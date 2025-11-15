# Specification of WiredTiger Storage API

This is a formal specification of the WiredTiger key-value storage API, defined in [`Storage.tla`](Storage.tla). It models a core subset of the main transactional API operations supported by WiredTiger. You can conveniently explore the current specification interactively [here](https://will62794.github.io/spectacle/#!/home?specpath=https://raw.githubusercontent.com/mongodb-labs/wt-spec/refs/heads/main/Storage.tla&constants%5BWC%5D=%22majority%22&constants%5BMaxTimestamp%5D=3&constants%5BRC%5D=%22snapshot%22&constants%5BKeys%5D=%7B0%2C1%7D&constants%5BNoValue%5D=%22NoValue%22&constants%5BTxnId%5D=%7BtxnA%2CtxnB%7D&constants%5BNil%5D=%22Nil%22&constants%5BNode%5D=%7Bn%7D&constants%5BTimestamps%5D=%7B1%2C2%2C3%7D).

## Model-Based Testing

We have experimented with an automated, model-based test case generation workflow for checking that the WiredTiger implementation conforms to the model defined in the [`Storage.tla`](Storage.tla) specification. Essentially, we generate WiredTiger unit test cases by computing path coverings of the reachable state space of the `Storage` model. We then use these test cases to check that the WiredTiger implementation conforms to the `Storage` model. A similar "lightweight verification" approach was also explored previously in WiredTiger using a C++ based model definition and randomized workload simulator. You can, for example, see the operation types from the C++ lightweight model-based verification harness [here](https://github.com/wiredtiger/wiredtiger/blob/7baa2123eea89c1854d7434ce7bf26dc8fd2a92d/test/model/src/include/model/driver/kv_workload.h#L1117-L1120).


The basic workflow to generate test cases from our TLA+ specification of the storage layer is implemented in the [`testgen.py`](testgen.py) script e.g. to run a small model with 2 transactions and 2 keys, you can execute the following:

```bash
python3 testgen.py --parallel_test_split 4 --compact --constants TxnId "{t1,t2}" Keys "{k1,k2}" Timestamps "{1,2,3}" --coverage_pct 1.0
```
this will generate WiredTiger unit tests files in `tests/test_txn_model_traces_*.py` files, which can be directly run against a WiredTiger build.

There is also a `testrun.sh` script that executes the above test generation script, copies over the test files to a sibling `wiredtiger` build directory, and then executes all of these generated tests. For example, you can execute 
```bash
./testrun.sh 0.5
```
to generate a set of unit test cases that aim to achieve 50% state coverage of the `Storage` model, and will then run these tests against a current WiredTiger build.

Note that this code also makes use of a modified build of TLC whose code lives on [this branch](https://github.com/will62794/tlaplus/tree/multi-inv-checking-et-al).