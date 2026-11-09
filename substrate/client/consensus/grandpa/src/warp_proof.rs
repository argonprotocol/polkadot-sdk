// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Substrate.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <https://www.gnu.org/licenses/>.

//! Utilities for generating and verifying GRANDPA warp sync proofs.

use codec::{Decode, DecodeAll, Encode};

use crate::{
	best_justification, find_scheduled_change, AuthoritySetChanges, AuthoritySetHardFork,
	BlockNumberOps, GrandpaJustification, SharedAuthoritySet,
};
use sc_client_api::Backend as ClientBackend;
use sc_network_sync::strategy::warp::{
	EncodedProof, VerificationResult, Verifier, WarpSyncProvider,
};
use sp_blockchain::{Backend as BlockchainBackend, HeaderBackend};
use sp_consensus_grandpa::{AuthorityList, SetId, GRANDPA_ENGINE_ID};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor, One},
	Justifications,
};

use std::{collections::HashMap, sync::Arc};

/// Warp proof processing error.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Decoding error.
	#[error("Failed to decode block hash: {0}.")]
	DecodeScale(#[from] codec::Error),
	/// Client backend error.
	#[error("{0}")]
	Client(#[from] sp_blockchain::Error),
	/// Invalid request data.
	#[error("{0}")]
	InvalidRequest(String),
	/// Invalid warp proof.
	#[error("{0}")]
	InvalidProof(String),
	/// Missing header or authority set change data.
	#[error("Missing required data to be able to answer request.")]
	MissingData,
}

/// The maximum size in bytes of the `WarpSyncProof`.
pub(super) const MAX_WARP_SYNC_PROOF_SIZE: usize = 8 * 1024 * 1024;

/// A proof of an authority set change.
#[derive(Decode, Encode, Debug)]
pub struct WarpSyncFragment<Block: BlockT> {
	/// The last block that the given authority set finalized. This block should contain a digest
	/// signaling an authority set change from which we can fetch the next authority set.
	pub header: Block::Header,
	/// A justification for the header above which proves its finality. In order to validate it the
	/// verifier must be aware of the authorities and set id for which the justification refers to.
	pub justification: GrandpaJustification<Block>,
}

/// An accumulated proof of multiple authority set changes.
#[derive(Decode, Encode)]
pub struct WarpSyncProof<Block: BlockT> {
	proofs: Vec<WarpSyncFragment<Block>>,
	is_finished: bool,
}

impl<Block: BlockT> WarpSyncProof<Block> {
	/// Generates a warp sync proof starting at the given block. It will generate authority set
	/// change proofs for all changes that happened from `begin` until the current authority set
	/// (capped by MAX_WARP_SYNC_PROOF_SIZE).
	fn generate<Backend>(
		backend: &Backend,
		begin: Block::Hash,
		set_changes: &AuthoritySetChanges<NumberFor<Block>>,
	) -> Result<WarpSyncProof<Block>, Error>
	where
		Backend: ClientBackend<Block>,
	{
		// TODO: cache best response (i.e. the one with lowest begin_number)
		let blockchain = backend.blockchain();

		let begin_number = blockchain
			.block_number_from_id(&BlockId::Hash(begin))?
			.ok_or_else(|| Error::InvalidRequest("Missing start block".to_string()))?;

		if begin_number > blockchain.info().finalized_number {
			return Err(Error::InvalidRequest("Start block is not finalized".to_string()));
		}

		let canon_hash = blockchain.hash(begin_number)?.expect(
			"begin number is lower than finalized number; \
			 all blocks below finalized number must have been imported; \
			 qed.",
		);

		if canon_hash != begin {
			return Err(Error::InvalidRequest(
				"Start block is not in the finalized chain".to_string(),
			));
		}

		let mut proofs = Vec::new();
		let mut proofs_encoded_len = 0;
		let mut proof_limit_reached = false;

		let set_changes = set_changes.iter_from(begin_number).ok_or(Error::MissingData)?;

		for (_, last_block) in set_changes {
			let hash = blockchain.block_hash_from_id(&BlockId::Number(*last_block))?
				.expect("header number comes from previously applied set changes; corresponding hash must exist in db; qed.");

			let header = blockchain
				.header(hash)?
				.expect("header hash obtained from header number exists in db; corresponding header must exist in db too; qed.");

			// the last block in a set is the one that triggers a change to the next set,
			// therefore the block must have a digest that signals the authority set change
			if find_scheduled_change::<Block>(&header).is_none() {
				// if it doesn't contain a signal for standard change then the set must have changed
				// through a forced changed, in which case we stop collecting proofs as the chain of
				// trust in authority handoffs was broken.
				break;
			}

			let justification = blockchain
				.justifications(header.hash())?
				.and_then(|just| just.into_justification(GRANDPA_ENGINE_ID))
				.ok_or_else(|| Error::MissingData)?;

			let justification = GrandpaJustification::<Block>::decode_all(&mut &justification[..])?;

			let proof = WarpSyncFragment { header: header.clone(), justification };
			let proof_size = proof.encoded_size();

			// Check for the limit. We remove some bytes from the maximum size, because we're only
			// counting the size of the `WarpSyncFragment`s. The extra margin is here to leave
			// room for rest of the data (the size of the `Vec` and the boolean).
			if proofs_encoded_len + proof_size >= MAX_WARP_SYNC_PROOF_SIZE - 50 {
				proof_limit_reached = true;
				break;
			}

			proofs_encoded_len += proof_size;
			proofs.push(proof);
		}

		let is_finished = if proof_limit_reached {
			false
		} else {
			let latest_justification = best_justification(backend)?.filter(|justification| {
				// the existing best justification must be for a block higher than the
				// last authority set change. if we didn't prove any authority set
				// change then we fallback to make sure it's higher or equal to the
				// initial warp sync block.
				let limit = proofs
					.last()
					.map(|proof| proof.justification.target().0 + One::one())
					.unwrap_or(begin_number);

				justification.target().0 >= limit
			});

			if let Some(latest_justification) = latest_justification {
				let header = blockchain.header(latest_justification.target().1)?
					.expect("header hash corresponds to a justification in db; must exist in db as well; qed.");

				let proof = WarpSyncFragment { header, justification: latest_justification };

				// Check for the limit. We remove some bytes from the maximum size, because we're
				// only counting the size of the `WarpSyncFragment`s. The extra margin is here
				// to leave room for rest of the data (the size of the `Vec` and the boolean).
				if proofs_encoded_len + proof.encoded_size() >= MAX_WARP_SYNC_PROOF_SIZE - 50 {
					false
				} else {
					proofs.push(proof);
					true
				}
			} else {
				true
			}
		};

		let final_outcome = WarpSyncProof { proofs, is_finished };
		debug_assert!(final_outcome.encoded_size() <= MAX_WARP_SYNC_PROOF_SIZE);
		Ok(final_outcome)
	}

	/// Verifies the warp sync proof starting at the given set id and with the given authorities.
	/// Verification stops when either the proof is exhausted or finality for the target header can
	/// be proven. If the proof is valid the new set id and authorities is returned.
	fn verify(
		&self,
		set_id: SetId,
		authorities: AuthorityList,
		hard_forks: &HashMap<(Block::Hash, NumberFor<Block>), (SetId, AuthorityList)>,
	) -> Result<(SetId, AuthorityList), Error>
	where
		NumberFor<Block>: BlockNumberOps,
	{
		let mut current_set_id = set_id;
		let mut current_authorities = authorities;

		for (fragment_num, proof) in self.proofs.iter().enumerate() {
			let hash = proof.header.hash();
			let number = *proof.header.number();

			if let Some((set_id, list)) = hard_forks.get(&(hash, number)) {
				current_set_id = *set_id;
				current_authorities = list.clone();
			} else {
				proof
					.justification
					.verify(current_set_id, &current_authorities)
					.map_err(|err| Error::InvalidProof(err.to_string()))?;

				if proof.justification.target().1 != hash {
					return Err(Error::InvalidProof(
						"Mismatch between header and justification".to_owned(),
					));
				}

				if let Some(scheduled_change) = find_scheduled_change::<Block>(&proof.header) {
					current_authorities = scheduled_change.next_authorities;
					current_set_id += 1;
				} else if fragment_num != self.proofs.len() - 1 || !self.is_finished {
					// Only the last fragment of the last proof message is allowed to be missing the
					// authority set change.
					return Err(Error::InvalidProof(
						"Header is missing authority set change digest".to_string(),
					));
				}
			}
		}
		Ok((current_set_id, current_authorities))
	}
}

/// Implements network API for warp sync.
pub struct NetworkProvider<Block: BlockT, Backend: ClientBackend<Block>>
where
	NumberFor<Block>: BlockNumberOps,
{
	backend: Arc<Backend>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	hard_forks: HashMap<(Block::Hash, NumberFor<Block>), (SetId, AuthorityList)>,
}

impl<Block: BlockT, Backend: ClientBackend<Block>> NetworkProvider<Block, Backend>
where
	NumberFor<Block>: BlockNumberOps,
{
	/// Create a new instance for a given backend and authority set.
	pub fn new(
		backend: Arc<Backend>,
		authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
		hard_forks: Vec<AuthoritySetHardFork<Block>>,
	) -> Self {
		NetworkProvider {
			backend,
			authority_set,
			hard_forks: hard_forks
				.into_iter()
				.map(|fork| (fork.block, (fork.set_id, fork.authorities)))
				.collect(),
		}
	}
}

/// Verifier state for GRANDPA warp sync.
struct VerifierState<Block: BlockT> {
	set_id: SetId,
	authorities: AuthorityList,
	next_proof_context: Block::Hash,
}

/// Verifier implementation for GRANDPA warp sync.
struct GrandpaVerifier<Block: BlockT> {
	state: VerifierState<Block>,
	hard_forks: HashMap<(Block::Hash, NumberFor<Block>), (SetId, AuthorityList)>,
	eras_synced: u64,
}

impl<Block: BlockT> Verifier<Block> for GrandpaVerifier<Block>
where
	NumberFor<Block>: BlockNumberOps,
{
	fn verify(
		&mut self,
		proof: &EncodedProof,
	) -> Result<VerificationResult<Block>, Box<dyn std::error::Error + Send + Sync>> {
		let EncodedProof(proof) = proof;
		let proof = WarpSyncProof::<Block>::decode_all(&mut proof.as_slice())
			.map_err(|e| format!("Proof decoding error: {:?}", e))?;
		let last_header = proof
			.proofs
			.last()
			.map(|p| p.header.clone())
			.ok_or_else(|| "Empty proof".to_string())?;

		let (current_set_id, current_authorities) =
			(self.state.set_id, self.state.authorities.clone());

		let (next_set_id, next_authorities) = proof
			.verify(current_set_id, current_authorities, &self.hard_forks)
			.map_err(Box::new)?;

		self.state = VerifierState {
			set_id: next_set_id,
			authorities: next_authorities,
			next_proof_context: last_header.hash(),
		};

		// Track eras synced
		self.eras_synced += proof.proofs.len() as u64;

		let justifications = proof
			.proofs
			.into_iter()
			.map(|p| {
				let justifications =
					Justifications::new(vec![(GRANDPA_ENGINE_ID, p.justification.encode())]);
				(p.header, justifications)
			})
			.collect::<Vec<_>>();

		if proof.is_finished {
			Ok(VerificationResult::Complete(last_header, justifications))
		} else {
			Ok(VerificationResult::Partial(justifications))
		}
	}

	fn next_proof_context(&self) -> Block::Hash {
		self.state.next_proof_context
	}

	fn status(&self) -> Option<String> {
		Some(format!("{} eras synced", self.eras_synced))
	}
}

impl<Block: BlockT, Backend: ClientBackend<Block>> WarpSyncProvider<Block>
	for NetworkProvider<Block, Backend>
where
	NumberFor<Block>: BlockNumberOps,
{
	fn generate(
		&self,
		start: Block::Hash,
	) -> Result<EncodedProof, Box<dyn std::error::Error + Send + Sync>> {
		let proof = WarpSyncProof::<Block>::generate(
			&*self.backend,
			start,
			&self.authority_set.authority_set_changes(),
		)
		.map_err(Box::new)?;
		Ok(EncodedProof(proof.encode()))
	}

	fn create_verifier(&self) -> Box<dyn Verifier<Block>> {
		let authority_set = self.authority_set.inner();
		let genesis_hash = self.backend.blockchain().info().genesis_hash;
		Box::new(GrandpaVerifier {
			state: VerifierState {
				set_id: authority_set.set_id,
				authorities: authority_set.current_authorities.clone(),
				next_proof_context: genesis_hash,
			},
			hard_forks: self.hard_forks.clone(),
			eras_synced: 0,
		})
	}
}

#[cfg(test)]
mod tests {
	use super::WarpSyncProof;
	use crate::{AuthoritySetChanges, GrandpaJustification};
	use codec::Encode;
	use rand::prelude::*;
	use sc_block_builder::BlockBuilderBuilder;
	use sp_blockchain::HeaderBackend;
	use sp_consensus::BlockOrigin;
	use sp_consensus_grandpa::GRANDPA_ENGINE_ID;
	use sp_keyring::Ed25519Keyring;
	use std::sync::Arc;
	use substrate_test_runtime_client::{
		BlockBuilderExt, ClientBlockImportExt, ClientExt, DefaultTestClientBuilderExt,
		TestClientBuilder, TestClientBuilderExt,
	};

	#[test]
	fn verified_warp_checkpoint_imports_with_its_sparse_parent() {
		use sc_client_api::{apply_aux, BlockBackend, LockImportRun};
		use sc_client_db::{Backend, BlocksPruning, DatabaseSettings, DatabaseSource, PruningMode};
		use sc_consensus::{
			BlockImport, BlockImportParams, ForkChoiceStrategy, ImportResult, ImportedState,
			StateAction, StorageChanges,
		};
		use sc_network_sync::strategy::warp::{EncodedProof, VerificationResult, Verifier};
		use sp_runtime::traits::{Block as _, Hash as _, Header as _};
		use sp_state_machine::Backend as _;
		use substrate_test_runtime_client::runtime::{GRANDPA_AUTHORITIES_KEY, GRANDPA_SET_ID_KEY};

		let genesis_authorities = vec![(Ed25519Keyring::Alice.public().into(), 1)];
		let next_authorities = vec![(Ed25519Keyring::Bob.public().into(), 1)];
		let builder = TestClientBuilder::new()
			.add_extra_storage(GRANDPA_AUTHORITIES_KEY, genesis_authorities.encode());
		let backend = builder.backend();
		let source = Arc::new(builder.build());
		let mut blocks = Vec::new();

		// G -> 1 -> 2 (authority change) -> 3 (state checkpoint).
		for number in 1..=3 {
			let mut builder = BlockBuilderBuilder::new(&*source)
				.on_parent_block(source.info().best_hash)
				.with_parent_block_number(number - 1)
				.build()
				.unwrap();
			if number == 2 {
				builder
					.push_deposit_log_digest_item(sp_runtime::DigestItem::Consensus(
						GRANDPA_ENGINE_ID,
						sp_consensus_grandpa::ConsensusLog::ScheduledChange(
							sp_consensus_grandpa::ScheduledChange {
								delay: 0u64,
								next_authorities: next_authorities.clone(),
							},
						)
						.encode(),
					))
					.unwrap();
				builder
					.push_storage_change(
						GRANDPA_AUTHORITIES_KEY.to_vec(),
						Some(next_authorities.encode()),
					)
					.unwrap();
				builder
					.push_storage_change(GRANDPA_SET_ID_KEY.to_vec(), Some(1u64.encode()))
					.unwrap();
			}
			let block = builder.build().unwrap().block;
			futures::executor::block_on(source.import(BlockOrigin::Own, block.clone())).unwrap();
			blocks.push(block);
		}

		// The old set finalizes the handoff; the new set finalizes the checkpoint.
		for (index, signer, set_id) in [(1, Ed25519Keyring::Alice, 0), (2, Ed25519Keyring::Bob, 1)]
		{
			let target_hash = blocks[index].hash();
			let target_number = *blocks[index].header.number();
			let precommit = finality_grandpa::Precommit { target_hash, target_number };
			let payload = sp_consensus_grandpa::localized_payload(
				42,
				set_id,
				&finality_grandpa::Message::Precommit(precommit.clone()),
			);
			let commit = finality_grandpa::Commit {
				target_hash,
				target_number,
				precommits: vec![finality_grandpa::SignedPrecommit {
					precommit,
					signature: signer.sign(&payload).into(),
					id: signer.public().into(),
				}],
			};
			let justification = GrandpaJustification::from_commit(&source, 42, commit).unwrap();
			source
				.finalize_block(target_hash, Some((GRANDPA_ENGINE_ID, justification.encode())))
				.unwrap();
			if index == 2 {
				source
					.lock_import_and_run(|import_op| {
						crate::aux_schema::update_best_justification(&justification, |insert| {
							apply_aux(import_op, insert, &[])
						})
					})
					.unwrap();
			}
		}
		let proof = WarpSyncProof::generate(
			&*backend,
			source.info().genesis_hash,
			&AuthoritySetChanges::from(vec![(0, 2)]),
		)
		.unwrap();
		let mut verifier: super::GrandpaVerifier<substrate_test_runtime_client::runtime::Block> =
			super::GrandpaVerifier {
				state: super::VerifierState {
					set_id: 0,
					authorities: genesis_authorities.clone(),
					next_proof_context: source.info().genesis_hash,
				},
				hard_forks: Default::default(),
				eras_synced: 0,
			};
		let VerificationResult::Complete(checkpoint, headers) =
			verifier.verify(&EncodedProof(proof.encode())).unwrap()
		else {
			panic!("expected a complete verified proof")
		};
		assert_eq!(headers.iter().map(|(h, _)| *h.number()).collect::<Vec<_>>(), vec![2, 3]);
		let checkpoint_state = source.state_at(checkpoint.hash()).unwrap();
		let pairs = checkpoint_state
			.pairs(Default::default())
			.unwrap()
			.collect::<Result<Vec<_>, _>>()
			.unwrap();
		let state = ImportedState {
			block: checkpoint.hash(),
			state: sp_state_machine::KeyValueStates(vec![sp_state_machine::KeyValueStorageLevel {
				state_root: Vec::new(),
				parent_storage_keys: Vec::new(),
				key_values: pairs,
			}]),
		};
		let root = sp_runtime::traits::BlakeTwo256::trie_root(
			state.state.0[0].key_values.clone(),
			sp_runtime::StateVersion::V1,
		);
		assert_eq!(root, *checkpoint.state_root(), "snapshot export must match the checkpoint");
		let next_block = BlockBuilderBuilder::new(&*source)
			.on_parent_block(checkpoint.hash())
			.with_parent_block_number(3)
			.build()
			.unwrap()
			.build()
			.unwrap()
			.block;

		// The no-parent control must work before testing the proof's sparse parent.
		for retain_parent in [false, true] {
			let directory = tempfile::tempdir().unwrap();
			let open_backend = || {
				Arc::new(
					Backend::new(
						DatabaseSettings {
							trie_cache_maximum_size: Some(1 << 20),
							state_pruning: Some(PruningMode::blocks_pruning(256)),
							blocks_pruning: BlocksPruning::KeepAll,
							pruning_filters: Vec::new(),
							source: DatabaseSource::ParityDb { path: directory.path().into() },
							metrics_registry: None,
						},
						0,
					)
					.unwrap(),
				)
			};
			let builder = TestClientBuilder::with_backend(open_backend())
				.add_extra_storage(GRANDPA_AUTHORITIES_KEY, genesis_authorities.encode())
				.set_no_genesis();
			let backend = builder.backend();
			let client = Arc::new(builder.build());
			let genesis = source.header(source.info().genesis_hash).unwrap().unwrap();
			let mut import = BlockImportParams::new(BlockOrigin::WarpSync, genesis);
			import.state_action = StateAction::Skip;
			import.fork_choice = Some(ForkChoiceStrategy::Custom(false));
			futures::executor::block_on((&*client).import_block(import)).unwrap();
			let (grandpa_import, link) = crate::block_import(
				client.clone(),
				512,
				&source,
				sc_consensus::LongestChain::new(backend),
				None,
			)
			.unwrap();
			if retain_parent {
				let (parent, _) = headers[0].clone();
				let mut import = BlockImportParams::new(BlockOrigin::WarpSync, parent);
				import.state_action = StateAction::Skip;
				import.fork_choice = Some(ForkChoiceStrategy::Custom(false));
				futures::executor::block_on(grandpa_import.import_block(import)).unwrap();
			}
			assert!(client.header(blocks[0].hash()).unwrap().is_none());
			let mut import =
				BlockImportParams::new(BlockOrigin::NetworkInitialSync, checkpoint.clone());
			import.body = Some(blocks[2].extrinsics.clone());
			import.state_action = StateAction::ApplyChanges(StorageChanges::Import(state.clone()));
			import.import_existing = true;
			import.fork_choice = Some(ForkChoiceStrategy::Custom(true));
			let result = futures::executor::block_on(grandpa_import.import_block(import));
			assert!(
				matches!(result, Ok(ImportResult::Imported(_))),
				"retain_parent={retain_parent}: {result:?}"
			);
			assert_eq!(client.info().finalized_hash, checkpoint.hash());
			assert!(client.state_at(checkpoint.hash()).is_ok());
			assert_eq!(link.shared_authority_set().set_id(), 1);
			assert_eq!(
				link.shared_authority_set().clone_inner().current_authorities,
				next_authorities
			);
			let gap = client.info().block_gap.unwrap();
			assert_eq!((gap.start, gap.end), (1, 2));
			assert_eq!(gap.gap_type, sp_blockchain::BlockGapType::MissingHeaderAndBody);

			// Reopen before executing descendants or backfilling the sparse proof history.
			drop(link);
			drop(grandpa_import);
			drop(client);
			let builder = TestClientBuilder::with_backend(open_backend())
				.add_extra_storage(GRANDPA_AUTHORITIES_KEY, genesis_authorities.encode())
				.set_no_genesis();
			let backend = builder.backend();
			let client = Arc::new(builder.build());
			assert_eq!(client.info().best_hash, checkpoint.hash());
			assert_eq!(client.info().finalized_hash, checkpoint.hash());
			assert_eq!(client.info().finalized_state, Some((checkpoint.hash(), 3)));
			assert_eq!(client.info().block_gap, Some(gap));
			assert!(client.code_at(checkpoint.hash()).is_ok());
			let (grandpa_import, link) = crate::block_import(
				client.clone(),
				512,
				&source,
				sc_consensus::LongestChain::new(backend),
				None,
			)
			.unwrap();
			assert_eq!(link.shared_authority_set().set_id(), 1);
			assert_eq!(
				link.shared_authority_set().clone_inner().current_authorities,
				next_authorities
			);

			let mut import =
				BlockImportParams::new(BlockOrigin::NetworkBroadcast, next_block.header.clone());
			import.body = Some(next_block.extrinsics.clone());
			import.fork_choice = Some(ForkChoiceStrategy::Custom(true));
			assert!(matches!(
				futures::executor::block_on(grandpa_import.import_block(import)).unwrap(),
				ImportResult::Imported(_)
			));
			assert_eq!(client.info().best_hash, next_block.hash());
			assert!(client.state_at(next_block.hash()).is_ok());

			// Gap sync must also fill the body of an already-retained proof header.
			for block in &blocks[..2] {
				let mut import = BlockImportParams::new(BlockOrigin::GapSync, block.header.clone());
				import.body = Some(block.extrinsics.clone());
				import.justifications = source.justifications(block.hash()).unwrap();
				import.state_action = StateAction::Skip;
				import.import_existing = true;
				import.fork_choice = Some(ForkChoiceStrategy::Custom(false));
				assert!(matches!(
					futures::executor::block_on(grandpa_import.import_block(import)).unwrap(),
					ImportResult::Imported(_)
				));
			}
			assert!(client.info().block_gap.is_none());
			assert_eq!(client.info().finalized_hash, checkpoint.hash());
			assert_eq!(client.info().best_hash, next_block.hash());
		}
	}

	#[test]
	fn warp_sync_proof_generate_verify() {
		let mut rng = rand::rngs::StdRng::from_seed([0; 32]);
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let client = Arc::new(builder.build());

		let available_authorities = Ed25519Keyring::iter().collect::<Vec<_>>();
		let genesis_authorities = vec![(Ed25519Keyring::Alice.public().into(), 1)];

		let mut current_authorities = vec![Ed25519Keyring::Alice];
		let mut current_set_id = 0;
		let mut authority_set_changes = Vec::new();

		for n in 1..=100 {
			let mut builder = BlockBuilderBuilder::new(&*client)
				.on_parent_block(client.chain_info().best_hash)
				.with_parent_block_number(client.chain_info().best_number)
				.build()
				.unwrap();
			let mut new_authorities = None;

			// we will trigger an authority set change every 10 blocks
			if n != 0 && n % 10 == 0 {
				// pick next authorities and add digest for the set change
				let n_authorities = rng.gen_range(1..available_authorities.len());
				let next_authorities = available_authorities
					.choose_multiple(&mut rng, n_authorities)
					.cloned()
					.collect::<Vec<_>>();

				new_authorities = Some(next_authorities.clone());

				let next_authorities = next_authorities
					.iter()
					.map(|keyring| (keyring.public().into(), 1))
					.collect::<Vec<_>>();

				let digest = sp_runtime::generic::DigestItem::Consensus(
					sp_consensus_grandpa::GRANDPA_ENGINE_ID,
					sp_consensus_grandpa::ConsensusLog::ScheduledChange(
						sp_consensus_grandpa::ScheduledChange { delay: 0u64, next_authorities },
					)
					.encode(),
				);

				builder.push_deposit_log_digest_item(digest).unwrap();
			}

			let block = builder.build().unwrap().block;

			futures::executor::block_on(client.import(BlockOrigin::Own, block)).unwrap();

			if let Some(new_authorities) = new_authorities {
				// generate a justification for this block, finalize it and note the authority set
				// change
				let (target_hash, target_number) = {
					let info = client.info();
					(info.best_hash, info.best_number)
				};

				let mut precommits = Vec::new();
				for keyring in &current_authorities {
					let precommit = finality_grandpa::Precommit { target_hash, target_number };

					let msg = finality_grandpa::Message::Precommit(precommit.clone());
					let encoded = sp_consensus_grandpa::localized_payload(42, current_set_id, &msg);
					let signature = keyring.sign(&encoded[..]).into();

					let precommit = finality_grandpa::SignedPrecommit {
						precommit,
						signature,
						id: keyring.public().into(),
					};

					precommits.push(precommit);
				}

				let commit = finality_grandpa::Commit { target_hash, target_number, precommits };

				let justification = GrandpaJustification::from_commit(&client, 42, commit).unwrap();

				client
					.finalize_block(target_hash, Some((GRANDPA_ENGINE_ID, justification.encode())))
					.unwrap();

				authority_set_changes.push((current_set_id, n));

				current_set_id += 1;
				current_authorities = new_authorities;
			}
		}

		let authority_set_changes = AuthoritySetChanges::from(authority_set_changes);

		// generate a warp sync proof
		let genesis_hash = client.hash(0).unwrap().unwrap();

		let warp_sync_proof =
			WarpSyncProof::generate(&*backend, genesis_hash, &authority_set_changes).unwrap();

		// verifying the proof should yield the last set id and authorities
		let (new_set_id, new_authorities) =
			warp_sync_proof.verify(0, genesis_authorities, &Default::default()).unwrap();

		let expected_authorities = current_authorities
			.iter()
			.map(|keyring| (keyring.public().into(), 1))
			.collect::<Vec<_>>();

		assert_eq!(new_set_id, current_set_id);
		assert_eq!(new_authorities, expected_authorities);
	}
}
