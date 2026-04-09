// SPDX-License-Identifier: MIT OR Apache-2.0

//! BIP-325 Signet block validation.
//!
//! Reference: <https://github.com/bitcoin/bips/blob/master/bip-0325.mediawiki>
//! Reference impl: <https://github.com/bitcoin/bitcoin/blob/master/src/signet.cpp>

#![cfg(feature = "bitcoinconsensus")]

extern crate alloc;

use alloc::borrow::ToOwned;
use alloc::vec;
use alloc::vec::Vec;

use bitcoin::absolute::LockTime;
use bitcoin::block::Header as BlockHeader;
use bitcoin::blockdata::opcodes::all as opcodes;
use bitcoin::blockdata::script::Builder;
use bitcoin::blockdata::script::Script;
use bitcoin::blockdata::script::ScriptBuf;
use bitcoin::blockdata::transaction::OutPoint;
use bitcoin::blockdata::transaction::Transaction;
use bitcoin::blockdata::transaction::TxIn;
use bitcoin::blockdata::transaction::TxOut;
use bitcoin::blockdata::transaction::Version;
use bitcoin::blockdata::witness::Witness;
use bitcoin::hashes::Hash;
use bitcoin::merkle_tree;
use bitcoin::Block;
use bitcoin::Sequence;
use bitcoin::TxMerkleNode;
use bitcoin::Txid;

/// The 4-byte magic prefix that identifies a signet solution push.
/// 0xecc7daa2 in little-endian byte order.
const SIGNET_HEADER: [u8; 4] = [0xa2, 0xda, 0xc7, 0xec];

/// BIP141 witness commitment prefix:
/// OP_RETURN (0x6a) OP_PUSH_36 (0x24) 0xaa21a9ed
const WITNESS_COMMITMENT_PREFIX: [u8; 6] = [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed];

/// Signet validation errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignetError {
    MissingCommitment,
    MissingCoinbase,
    InvalidSolutionFormat,
    ScriptVerificationFailed,
    InvalidScriptSig,
    InvalidWitness,
    CompactSizeOverflow,
}

impl core::fmt::Display for SignetError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SignetError::MissingCommitment => write!(f, "Missing signet commitment in coinbase"),
            SignetError::MissingCoinbase => write!(f, "Coinbase transaction missing"),
            SignetError::InvalidSolutionFormat => write!(f, "Invalid signet solution format"),
            SignetError::ScriptVerificationFailed => write!(f, "Script verification failed"),
            SignetError::InvalidScriptSig => write!(f, "Invalid scriptSig"),
            SignetError::InvalidWitness => write!(f, "Invalid witness stack"),
            SignetError::CompactSizeOverflow => write!(f, "CompactSize value overflows usize"),
        }
    }
}

/// Parsed signet solution extracted from the coinbase witness commitment.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SignetSolution {
    /// The scriptSig portion of the solution.
    pub script_sig: Vec<u8>,
    /// The scriptWitness stack (BIP141 serialized).
    pub script_witness: Vec<Vec<u8>>,
}

/// Top-level entry point: validate that `block` satisfies the signet challenge.
pub fn validate_signet_block(block: &Block, challenge: &Script) -> Result<(), SignetError> {
    let coinbase = block.txdata.first().ok_or(SignetError::MissingCoinbase)?;

    // Special case: if challenge is OP_TRUE, absence of a commitment is acceptable.
    if challenge.as_bytes() == [0x51] {
        return Ok(());
    }

    let solution = extract_signet_solution(coinbase)?;
    let signet_merkle_root = compute_signet_merkle_root(block)?;
    let to_spend = build_to_spend_tx(&block.header, signet_merkle_root, challenge);
    let to_sign = build_to_sign_tx(to_spend.compute_txid(), &solution);

    verify_signet_spend(&to_sign, &to_spend)
}

pub fn extract_signet_solution(coinbase: &Transaction) -> Result<SignetSolution, SignetError> {
    for output in &coinbase.output {
        let script = output.script_pubkey.as_bytes();

        if script.len() < 38 || !script.starts_with(&WITNESS_COMMITMENT_PREFIX) {
            continue;
        }

        let solution_bytes = &script[38..];
        if let Some(sol) = find_signet_push_after_commitment(solution_bytes)? {
            return Ok(sol);
        }
    }

    Err(SignetError::MissingCommitment)
}

fn find_signet_push_after_commitment(data: &[u8]) -> Result<Option<SignetSolution>, SignetError> {
    let mut i = 0;

    while i < data.len() {
        match parse_push_op(&data[i..])? {
            Some((push_data, consumed)) => {
                i += consumed;
                if push_data.starts_with(&SIGNET_HEADER) {
                    return Ok(Some(parse_solution_bytes(&push_data[4..])?));
                }
            }
            None => i += 1,
        }
    }

    Ok(None)
}

fn parse_push_op(script: &[u8]) -> Result<Option<(&[u8], usize)>, SignetError> {
    if script.is_empty() {
        return Ok(None);
    }

    let opcode = script[0];
    match opcode {
        0x00 => Ok(Some((&[], 1))),
        0x01..=0x4b => {
            let len = opcode as usize;
            if script.len() < 1 + len {
                return Err(SignetError::InvalidSolutionFormat);
            }
            Ok(Some((&script[1..1 + len], 1 + len)))
        }
        0x4c => {
            if script.len() < 2 {
                return Err(SignetError::InvalidSolutionFormat);
            }
            let len = script[1] as usize;
            if script.len() < 2 + len {
                return Err(SignetError::InvalidSolutionFormat);
            }
            Ok(Some((&script[2..2 + len], 2 + len)))
        }
        0x4d => {
            if script.len() < 3 {
                return Err(SignetError::InvalidSolutionFormat);
            }
            let len = u16::from_le_bytes([script[1], script[2]]) as usize;
            if script.len() < 3 + len {
                return Err(SignetError::InvalidSolutionFormat);
            }
            Ok(Some((&script[3..3 + len], 3 + len)))
        }
        0x4e => {
            if script.len() < 5 {
                return Err(SignetError::InvalidSolutionFormat);
            }
            let len = u32::from_le_bytes([script[1], script[2], script[3], script[4]]) as usize;
            if script.len() < 5 + len {
                return Err(SignetError::InvalidSolutionFormat);
            }
            Ok(Some((&script[5..5 + len], 5 + len)))
        }
        _ => Ok(None),
    }
}

fn parse_solution_bytes(data: &[u8]) -> Result<SignetSolution, SignetError> {
    if data.is_empty() {
        return Ok(SignetSolution::default());
    }

    let (script_sig_len, cs_bytes) = read_compact_size(data)?;
    if cs_bytes > data.len() {
        return Err(SignetError::InvalidSolutionFormat);
    }

    let after_cs = &data[cs_bytes..];
    if script_sig_len > after_cs.len() {
        return Err(SignetError::InvalidScriptSig);
    }

    let script_sig = after_cs[..script_sig_len].to_vec();
    let script_witness = parse_witness_stack(&after_cs[script_sig_len..])?;

    Ok(SignetSolution {
        script_sig,
        script_witness,
    })
}

/// Reads a Bitcoin CompactSize integer. Returns `(value, bytes_consumed)`.
fn read_compact_size(data: &[u8]) -> Result<(usize, usize), SignetError> {
    if data.is_empty() {
        return Err(SignetError::InvalidSolutionFormat);
    }

    match data[0] {
        0xfd => {
            if data.len() < 3 {
                return Err(SignetError::InvalidSolutionFormat);
            }
            let v = u16::from_le_bytes([data[1], data[2]]) as usize;
            Ok((v, 3))
        }
        0xfe => {
            if data.len() < 5 {
                return Err(SignetError::InvalidSolutionFormat);
            }
            let v = u32::from_le_bytes([data[1], data[2], data[3], data[4]]) as usize;
            Ok((v, 5))
        }
        0xff => {
            if data.len() < 9 {
                return Err(SignetError::InvalidSolutionFormat);
            }
            let v = u64::from_le_bytes([
                data[1], data[2], data[3], data[4], data[5], data[6], data[7], data[8],
            ]);

            let v = usize::try_from(v).map_err(|_| SignetError::CompactSizeOverflow)?;
            Ok((v, 9))
        }
        n => Ok((n as usize, 1)),
    }
}

/// Parses a BIP141 witness stack from raw bytes.
/// Format: CompactSize(item_count), then CompactSize-prefixed items.
fn parse_witness_stack(data: &[u8]) -> Result<Vec<Vec<u8>>, SignetError> {
    if data.is_empty() {
        return Ok(vec![]);
    }

    let (num_items, mut i) = read_compact_size(data)?;
    let mut items = Vec::with_capacity(num_items);

    for _ in 0..num_items {
        if i >= data.len() {
            return Err(SignetError::InvalidWitness);
        }

        let (len, cs) = read_compact_size(&data[i..])?;
        i += cs;

        if i + len > data.len() {
            return Err(SignetError::InvalidWitness);
        }

        items.push(data[i..i + len].to_vec());
        i += len;
    }

    Ok(items)
}

pub fn compute_signet_merkle_root(block: &Block) -> Result<TxMerkleNode, SignetError> {
    let mut txdata = block.txdata.clone();
    let coinbase = txdata.first_mut().ok_or(SignetError::MissingCoinbase)?;
    strip_signet_solution_from_coinbase(coinbase)?;

    let txids: Vec<TxMerkleNode> = txdata
        .iter()
        .map(|tx| TxMerkleNode::from_raw_hash(tx.compute_txid().to_raw_hash()))
        .collect();

    merkle_tree::calculate_root(txids.into_iter()).ok_or(SignetError::InvalidSolutionFormat)
}

fn strip_signet_solution_from_coinbase(coinbase: &mut Transaction) -> Result<(), SignetError> {
    for output in &mut coinbase.output {
        let script = output.script_pubkey.as_bytes();

        if script.len() < 38 || !script.starts_with(&WITNESS_COMMITMENT_PREFIX) {
            continue;
        }

        // Keep only the commitment prefix + 32-byte commitment hash.
        output.script_pubkey = ScriptBuf::from(script[..38].to_vec());
        return Ok(());
    }

    Err(SignetError::MissingCommitment)
}

pub fn build_to_spend_tx(
    header: &BlockHeader,
    signet_merkle_root: TxMerkleNode,
    challenge: &Script,
) -> Transaction {
    let mut block_data = Vec::with_capacity(72);
    block_data.extend_from_slice(&header.version.to_consensus().to_le_bytes());
    block_data.extend_from_slice(header.prev_blockhash.as_byte_array());
    block_data.extend_from_slice(signet_merkle_root.as_byte_array());
    block_data.extend_from_slice(&header.time.to_le_bytes());

    debug_assert_eq!(block_data.len(), 72);

    // scriptSig = OP_0 + push 72 bytes.
    let mut script_bytes = vec![0x00, 72];
    script_bytes.extend_from_slice(&block_data);
    let script_sig = ScriptBuf::from(script_bytes);

    Transaction {
        version: Version(0),
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint {
                txid: Txid::all_zeros(),
                vout: 0xFFFF_FFFF,
            },
            script_sig,
            sequence: Sequence::ZERO,
            witness: Witness::new(),
        }],
        output: vec![TxOut {
            value: bitcoin::Amount::ZERO,
            script_pubkey: challenge.to_owned(),
        }],
    }
}

pub fn build_to_sign_tx(to_spend_txid: Txid, solution: &SignetSolution) -> Transaction {
    let mut witness = Witness::new();
    for item in &solution.script_witness {
        witness.push(item);
    }

    Transaction {
        version: Version(0),
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint {
                txid: to_spend_txid,
                vout: 0,
            },
            script_sig: ScriptBuf::from(solution.script_sig.clone()),
            sequence: Sequence::ZERO,
            witness,
        }],
        output: vec![TxOut {
            value: bitcoin::Amount::ZERO,
            script_pubkey: Builder::new().push_opcode(opcodes::OP_RETURN).into_script(),
        }],
    }
}

fn verify_signet_spend(to_sign: &Transaction, to_spend: &Transaction) -> Result<(), SignetError> {
    use bitcoin::consensus::encode::serialize;

    let serialized_to_sign = serialize(to_sign);
    let challenge_bytes = to_spend.output[0].script_pubkey.as_bytes();
    let amount_sat = to_spend.output[0].value.to_sat();

    // NOTE: the exact bitcoinconsensus API signature can vary by crate version.
    // If your version differs, adjust only this line.
    bitcoinconsensus::verify(challenge_bytes, amount_sat, &serialized_to_sign, None, 0)
        .map_err(|_| SignetError::ScriptVerificationFailed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_solution_parse() {
        let sol = parse_solution_bytes(&[]).unwrap();
        assert!(sol.script_sig.is_empty());
        assert!(sol.script_witness.is_empty());
    }

    #[test]
    fn test_compact_size() {
        assert_eq!(read_compact_size(&[0x10]).unwrap(), (16, 1));
        assert_eq!(read_compact_size(&[0xfd, 0x00, 0x01]).unwrap(), (256, 3));
        assert_eq!(read_compact_size(&[0x00]).unwrap(), (0, 1));
        assert!(read_compact_size(&[0xff]).is_err());

        let data = [0xff, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        assert_eq!(read_compact_size(&data).unwrap(), (1, 9));
    }

    #[test]
    fn test_signet_header_constant() {
        assert_eq!(SIGNET_HEADER, [0xa2, 0xda, 0xc7, 0xec]);
    }

    #[test]
    fn test_parse_push_op_empty() {
        let data = &[];
        assert_eq!(parse_push_op(data).unwrap(), None);
    }

    #[test]
    fn test_parse_push_op_op_0() {
        let data = &[0x00];
        let (push_data, consumed) = parse_push_op(data).unwrap().unwrap();
        assert!(push_data.is_empty());
        assert_eq!(consumed, 1);
    }

    #[test]
    fn test_parse_push_op_direct_push() {
        let data = &[0x03, 0xaa, 0xbb, 0xcc];
        let (push_data, consumed) = parse_push_op(data).unwrap().unwrap();
        assert_eq!(push_data, &[0xaa, 0xbb, 0xcc]);
        assert_eq!(consumed, 4);
    }

    #[test]
    fn test_contains_signet_push_path() {
        let mut script = WITNESS_COMMITMENT_PREFIX.to_vec();
        script.extend_from_slice(&[0x12; 32]);
        script.push(4);
        script.extend_from_slice(&SIGNET_HEADER);
        assert!(find_signet_push_after_commitment(&script[38..])
            .unwrap()
            .is_some());
    }

    #[test]
    fn test_strip_signet_solution_from_coinbase() {
        use bitcoin::blockdata::transaction::TxOut;
        use bitcoin::Amount;

        let mut script = WITNESS_COMMITMENT_PREFIX.to_vec();
        script.extend_from_slice(&[0x12; 32]);
        script.push(4);
        script.extend_from_slice(&SIGNET_HEADER);

        let mut tx = Transaction {
            version: Version(0),
            lock_time: LockTime::ZERO,
            input: vec![],
            output: vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::from(script),
            }],
        };

        strip_signet_solution_from_coinbase(&mut tx).unwrap();
        assert_eq!(tx.output[0].script_pubkey.as_bytes().len(), 38);
    }

    #[test]
    fn test_signature_error_display() {
        assert_eq!(
            SignetError::MissingCommitment.to_string(),
            "Missing signet commitment in coinbase"
        );
        assert_eq!(
            SignetError::MissingCoinbase.to_string(),
            "Coinbase transaction missing"
        );
    }

    #[test]
    fn test_solution_with_witness() {
        let mut data = vec![];
        data.push(0x02);
        data.extend_from_slice(&[0xaa, 0xbb]);
        data.push(0x01);
        data.push(0x03);
        data.extend_from_slice(&[0xcc, 0xdd, 0xee]);

        let sol = parse_solution_bytes(&data).unwrap();
        assert_eq!(sol.script_sig, vec![0xaa, 0xbb]);
        assert_eq!(sol.script_witness.len(), 1);
        assert_eq!(sol.script_witness[0], vec![0xcc, 0xdd, 0xee]);
    }

    #[test]
    fn test_witness_stack_parsing() {
        let mut data = vec![];
        data.push(0x02);
        data.push(0x02);
        data.extend_from_slice(&[0xaa, 0xbb]);
        data.push(0x01);
        data.push(0xcc);

        let stack = parse_witness_stack(&data).unwrap();
        assert_eq!(stack.len(), 2);
        assert_eq!(stack[0], vec![0xaa, 0xbb]);
        assert_eq!(stack[1], vec![0xcc]);
    }
}
