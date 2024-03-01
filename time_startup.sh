#!/bin/bash

# Step 1: Create the directory if it doesn't exist and write the file
mkdir -p test
echo 'import Lean.Meta.Basic
open Lean.Meta

#eval show MetaM _ from
  IO.FS.writeFile "test/write_file.out" ""' > test/write_file.lean

# Step 2: Delete test/write_file.out if it exists
rm -f test/write_file.out

# Step 3: Start a timer with higher precision
start_time=$(python3 -c 'import time; print(time.time())')

# Step 4: Run `code test/write_file.lean`
code test/write_file.lean &

# Step 5: Wait until `test/write_file.out` exists with 0.1s checks
while [ ! -f test/write_file.out ]
do
  sleep 0.1
done

# Step 6: Stop the timer with the same high precision
end_time=$(python3 -c 'import time; print(time.time())')

# Step 7: Kill all Electron processes (ouch!)
pkill Electron

# Step 8: Calculate and print the elapsed time
elapsed_time=$(python3 -c "print(f'{float($end_time) - float($start_time):.1f}')")
echo "Elapsed time: $elapsed_time seconds"
