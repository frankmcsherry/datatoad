#!/bin/bash
#
# Benchmark battery for datatoad.
#
# Usage:
#   ./scripts/bench.sh                          # single machine, 1 worker
#   ./scripts/bench.sh -w 4                     # single machine, 4 workers
#   ./scripts/bench.sh -n 4 -p 0                # distributed, this is process 0
#   ./scripts/bench.sh distributed              # launch on all 4 minis via ssh
#   ./scripts/bench.sh distributed -w 4         # launch on all 4 minis, 4 workers each
#
# The "distributed" mode SSHes into mini-{00..03} and runs the battery on each,
# collecting output. All other arguments are passed through to datatoad.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BINARY="${SCRIPT_DIR}/../target/release/datatoad"
SCRIPTS=(
    galen.dt
    tc-10k.dt
    cspa.dt
    cvc5.dt
    dyck.dt
    csda.dt
    andersen.dt
    z3.dt
)

# Distributed mode: launch on all minis and wait.
if [[ "${1:-}" == "distributed" ]]; then
    shift
    EXTRA_ARGS="$*"

    # Deploy binary to all minis first.
    echo "Deploying binary to minis..."
    for host in mini-00 mini-01 mini-02 mini-03; do
        scp -q "$BINARY" "$host":~/Projects/datatoad/target/release/datatoad &
    done
    wait
    echo "Binary deployed."
    echo

    # Deploy scripts to all minis.
    for host in mini-00 mini-01 mini-02 mini-03; do
        for script in "${SCRIPTS[@]}"; do
            scp -q "${SCRIPT_DIR}/${script}" "$host":~/Projects/datatoad/scripts/ &
        done
    done
    wait

    # Run on all minis in parallel.
    for host in mini-00 mini-01 mini-02 mini-03; do
        IDX=${host##mini-0}
        ssh "$host" "~/Projects/datatoad/scripts/bench.sh -h ~/hostfile.txt -n 4 -p $IDX $EXTRA_ARGS" 2>&1 | sed "s/^/[$host] /" &
    done
    wait
    exit 0
fi

# Local/single-process mode.
echo "datatoad benchmark battery"
echo "args: $*"
echo "---"
echo

TOTAL_START=$SECONDS
for script in "${SCRIPTS[@]}"; do
    echo "=== ${script} ==="
    "$BINARY" "$@" "${SCRIPT_DIR}/${script}"
    echo
done

ELAPSED=$((SECONDS - TOTAL_START))
echo "---"
echo "total: ${ELAPSED}s"
