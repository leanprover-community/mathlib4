import Mathlib.Data.Nat.Notation

-- 1.5. Datatypes and Patterns
inductive Bool' where
  | false' : Bool'
  | true' : Bool'

-- 1.5.1. Pattern Matching

def isZero (n : ℕ) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero 0

#eval isZero 5

def pred (n : ℕ) : ℕ :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 0

#eval pred 5

#eval pred 839

-- 1.5.2. Recursive Functions

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

