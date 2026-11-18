#!/bin/bash
# Emit, build, and add case splits for omega failures until the closure files build.
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")"
for round in 1 2; do
  python3 emit_lean.py > /dev/null
  (cd ../.. && lake build Cgt.RowA2Odd.CloseFFTT Cgt.RowA2Odd.CloseFTFT Cgt.RowA2Odd.CloseFTTF Cgt.RowA2Odd.CloseTFFT Cgt.RowA2Odd.CloseTTFF Cgt.RowA2Odd.CloseTFTF) > build.log 2>&1
  n=$(grep -c "^error" build.log)
  echo "round $round: $n errors"
  if [ "$n" = "0" ]; then exit 0; fi
  python3 fix_leaves.py build.log
done
