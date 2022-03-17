import Mathlib.Util.MemoFix

def fibLength : List Nat → Nat :=
  memoFix fun fib xs =>
    dbg_trace xs
    match xs with
    | [] => 0
    | [x] => 1
    | _ :: xs@(_ :: ys) => fib xs + fib ys

-- visits every sublist only once
#eval fibLength [1,2,3,4,5,6,7,8]
