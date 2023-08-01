# ⚡ Madara: Starknet Sequencer with ticking functionality 👉👈

## Madara

For Madara docs look at [Madara Readme](./README-MADARA.md)

## Madara with ticker

Ticking Madara is a modified version of the Madara sequencer for Starknet which
implements a ticking functionality, a transaction which is invoked by the
protocol at the start of each new block. If you're looking for the original
Madara project, please visit their
[GitHub page](https://github.com/keep-starknet-strange/madara/ "Madara Sequencer").

## Table of contents

- [Why ticking functionality?](#why-ticking-functionality)
- [Tick contract](#tick-contract)
- [Madara modification](#madara-modification)
- [Running Ticking Madara](#running-ticking-madara)

## Why ticking functionality?

Ticking Madara was inspired by
[Ticking Optimism](https://github.com/therealbytes/ticking-optimism/ "Ticking Optimism"),
a similar project which achieved the same end result for the Optimism rollup
chain. The benefit of ticking functionality is the ability to integrate it into
an app chain and invoke the app logic completely on-chain. This logic can be
expanded as needed, and as long as the dedicated sender address has enough funds
to cover the fees for invoking the `tick` function, it will be processed as the
first tx in every block.

## Tick contract

As this is mainly a Proof-of-concept, the contract itself is fairly simple. In
order to prove invoking of the contract occurs on each new block, the `tick`
function increments a storage variable by one. The contract was written in both
versions of Cairo, the smart contract language for Starknet, as Madara has not
fully migrated to Cairo version 1, and still uses version 0. However, when the
migration to Cairo version 1 is complete, we will update the sequencer to invoke
Cairo v1 contract instead.

Tick contract code in cairo version 0 is as follows:

```python
// SPDX-License-Identifier: MIT

%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.uint256 import Uint256

@storage_var
    func my_value_storage() -> (res: felt) {
}

@view
func get_my_stored_value{
    syscall_ptr: felt*,
    pedersen_ptr: HashBuiltin*,
    range_check_ptr,
}() -> (
    res: felt
) {
    let (res) = my_value_storage.read();
    return (res = res);
}

@external
func tick{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() {
    let (res) = my_value_storage.read();
    my_value_storage.write(res + 1);
    return();
}
```

The same contract in Cairo v1 looks like this:

```rust
#[contract]
mod TickingStarknetContract {
    struct Storage {
        balance: felt252,
    }

    // Increases the balance by one.
    #[external]
    fn tick() {
        balance::write(balance::read() + 1);
    }

    // Returns the current balance.
    #[view]
    fn get_balance() -> felt252 {
        balance::read()
    }
}
```

Note: Cairo language syntax and contract structure is still evolving and
continuously changing. The reason for choosing this specific version is because
it is the latest version of v1 syntax supported by
[Protostar](https://docs.swmansion.com/protostar/ "Protostar"), a toolchain for
Starknet development utilized in this project.

## Madara modification

First, we added compiled tick contract to the genesis state of the sequencer, in
the `crates/node/src/chain_spec.rs` file.

```rust
let test_contract_class = get_contract_class(&read_file_to_string("../../cairo-contracts/build/tick.json"), 0);
```

In the `crates/node/src/constants.rs` we added constant values for the contract
address and the contract class hash.

```rust
pub const TEST_CONTRACT_ADDRESS: &str = "0x1111";
pub const TEST_CONTRACT_CLASS_HASH: &str = "0x0000d08ad5cd621607f319e1f460d63268a9efb087c47b8066e6f82f2acc1e36";
```

Main changes were made in the Starknet pallet. We've added constant values here
as well in order to be able to use them throughout the pallet. Here we also
added the selector for the tick function entrypoint in the smart contract.

```rust
pub const TEST_SENDER_ADDRESS: &str = "0x0000000000000000000000000000000000000000000000000000000000000001";
pub const TEST_CONTRACT_ADDRESS: &str = "0x1111";
pub const TEST_CONTRACT_CLASS_HASH: &str = "0x0000d08ad5cd621607f319e1f460d63268a9efb087c47b8066e6f82f2acc1e36";
pub const TEST_TICK_SELECTOR: &str = "0x02141a67791ccd46711281bdb998cf05330a94bd912f4ab44bfca6f08f79cbf1";
```

Most of the changes are in the `crates/pallets/starknet/src/lib.rs` file, which
is the core file of the sequencer logic. Here we simplified the invoke function
to log any execution of the transaction, and moved the rest of the code to a
separate `execute_tx` function.

```rust
/// The invoke transaction is the main transaction type used to invoke contract functions in
/// Starknet.
/// See `https://docs.starknet.io/documentation/architecture_and_concepts/Blocks/transactions/#invoke_transaction`.
/// # Arguments
///
/// * `origin` - The origin of the transaction.
/// * `transaction` - The Starknet transaction.
///
///  # Returns
///
/// * `DispatchResult` - The result of the transaction.
#[pallet::call_index(1)]
#[pallet::weight({0})]
pub fn invoke(origin: OriginFor<T>, transaction: InvokeTransaction) -> DispatchResult {
    // This ensures that the function can only be called via unsigned transaction.
    ensure_none(origin)?;
    // Check if contract is deployed
    ensure!(ContractClassHashes::<T>::contains_key(transaction.sender_address), Error::<T>::AccountNotDeployed);
    let (transaction, receipt) = match Self::execute_tx(transaction) {
        Ok((transaction, receipt)) => {
            log!(info, "Successfully execute tx");
            (transaction, receipt)
        },
        Err(err) => {
            log!(error, "Failed to execute tx {:?}", err);
            return Err(Error::<T>::TransactionExecutionFailed.into());
        }
    };
    // Append the transaction to the pending transactions.
    Pending::<T>::try_append((transaction, receipt)).map_err(|_| Error::<T>::TooManyPendingTransactions)?;
    Ok(())
}
```

We have also modified Starknet hook `on_initialize`. This function is invoked
each time a new block is being created, and we have added separate logs to
display the successful invokation of the `invoke_tick` function.

```rust
fn on_initialize(_: T::BlockNumber) -> Weight {
    match Self::invoke_tick() {
        Ok(_) => log!(info, "Successfully invoke tick and intialize block"),
        Err(err) => match err {
            _ => log!(error, "Failed to invoke tick {:?}", err),
        }
    }
    Weight::zero()
}
```

The `invoke_tick` function is the one invoking the ticking contract. First, the
tx struct is created in the `set_tick_tx` function, then checks are performed in
order to ensure the sender account exists on Madara.

```rust
fn invoke_tick() -> Result<(), DispatchError> {
    log!(info, "INVOKE TICK");
    let tick_invoke_tx = Self::set_tick_tx();

    ensure!(ContractClassHashes::<T>::contains_key(tick_invoke_tx.sender_address), Error::<T>::AccountNotDeployed);

    let (transaction, receipt) = match Self::execute_tx(tick_invoke_tx) {
        Ok((transaction, receipt)) => {
            log!(info, "Successfully execute tick tx");
            (transaction, receipt)
        },
        Err(err) => {
            log!(error, "Failed to execute tick tx {:?}", err);
            return Err(Error::<T>::TransactionExecutionFailed.into());
        }
    };

    Pending::<T>::try_append((transaction, receipt)).map_err(|_| Error::<T>::TooManyPendingTransactions)?;

    Ok(())
}
```

The `set_tick_tx` function creates and returns the `InvokeTransaction` struct by
signing it and adding the `tick` smart contract invocation to the calldata
vector.

```rust
fn set_tick_tx() -> InvokeTransaction {
    let contract_nonce = Self::nonce(Felt252Wrapper::from_hex_be(constants::TEST_SENDER_ADDRESS).unwrap());
    log!(info,"CURRECT NONCE TICK {:?}", contract_nonce);

    let mut signature = Vec::new();
    signature.push(Felt252Wrapper::from_hex_be("0x0").unwrap());
    signature.push(Felt252Wrapper::from_hex_be("0x0").unwrap());

    let sender_address = Felt252Wrapper::from_hex_be(constants::TEST_SENDER_ADDRESS).unwrap();
    let nonce = contract_nonce;
    let mut calldata = Vec::new();
    calldata.push(Felt252Wrapper::from_hex_be(constants::TEST_CONTRACT_ADDRESS).unwrap());
    calldata.push(Felt252Wrapper::from_hex_be(constants::TEST_TICK_SELECTOR).unwrap());
    calldata.push(Felt252Wrapper::from_hex_be("0x0").unwrap());

    InvokeTransaction {
        version: 1,
        sender_address,
        calldata: BoundedVec::try_from(calldata).unwrap_or_default(),
        nonce,
        signature: BoundedVec::try_from(signature).unwrap_or_default(),
        max_fee: Felt252Wrapper::from(u128::MAX),
        is_query: false,
    }
}
```

The code in the `execute_tx` performs smart contract function invokations on
Starknet. This logic used to be in the `init` function, but this separation is
what allows us to call `tick` on each new block.

```rust
fn execute_tx(invoke_transaction: InvokeTransaction) -> Result<(Transaction, TransactionReceiptWrapper), DispatchError> {
    let block_context = Self::get_block_context();
    let chain_id = Self::chain_id();
    let transaction: Transaction = invoke_transaction.from_invoke(chain_id);
    let call_info =
        transaction.execute(&mut BlockifierStateAdapter::<T>::default(), &block_context, TxType::Invoke, None);
    let receipt = match call_info {
        Ok(TransactionExecutionInfoWrapper {
            validate_call_info: _validate_call_info,
            execute_call_info,
            fee_transfer_call_info,
            actual_fee,
            actual_resources: _actual_resources,
        }) => {
            log!(info, "Invoke Tick Transaction executed successfully: {:?}", execute_call_info);

            let events = Self::emit_events_for_calls(execute_call_info, fee_transfer_call_info)?;

            TransactionReceiptWrapper {
                events: BoundedVec::try_from(events).map_err(|_| Error::<T>::ReachedBoundedVecLimit)?,
                transaction_hash: transaction.hash,
                tx_type: TxType::Invoke,
                actual_fee: actual_fee.0.into(),
            }
        }
        Err(e) => {
            log!(error, "Invoke Transaction execution failed: {:?}", e);
            return Err(Error::<T>::TransactionExecutionFailed.into());
        }
    };

    Ok((transaction, receipt))
}
```

## Running Ticking Madara

Ticking Madara is available via
[Docker image on Docker hub](https://hub.docker.com/r/fixmvp/ticking-madara "Ticking Madara Docker image").
To pull and run the image, simply run the following command:

```bash
docker run fixmvp/ticking-madara
```

If you'd like to play around with the sequencer yourself, you can clone our
[GitHub repository](https://github.com/MVPWorkshop/madara "Ticking Madara GitHub repository").
The command to run the sequencer from the source code is

```bash
cargo run --release - --dev --tmp --rpc-external --execution native --pool-limit=100000 --pool-kbytes=500000 --rpc-methods=unsafe --rpc-cors=all --in-peers=0 --out-peers=1 --no-telemetry
```

Just make sure you have
[Rust installed](https://www.rust-lang.org/tools/install "Rust installation").
