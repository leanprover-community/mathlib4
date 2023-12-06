import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin
-- import LeanSage.ForMathlib

/-- Call `sage` -/
def sageOutput (args : Array String) : IO String := do
  IO.Process.run { cmd := "sage", args := args }

/-- Parse a string containing a list of integers. Should be a proper parser! -/
def String.parseNatList (l : String) : List ℕ :=
  (((l.drop 1).dropRight 2).split (. = ' ')).map
    (fun s => s.stripSuffix ",") |> .map String.toNat!

/-- An "unsafe" function that calls `sage` to find the prime factors of a number. -/
unsafe def sagePrimeFactorsUnsafe (n : ℕ) : List ℕ :=
  let args := #["-c", s!"print(prime_factors({n}))"] ;
  match unsafeBaseIO (sageOutput args).toBaseIO with
  | .ok l => l.parseNatList
  | .error _ => []

/--
An "opaque" wrapper around the unsafe function.

This prevents the `unsafe` label propagating to definitions that use it,
but also prevent Lean from knowing anything about the implementation.
-/
@[implemented_by sagePrimeFactorsUnsafe]
opaque sagePrimeFactors (n : ℕ) : List ℕ

/-- An axiom specifying the behaviour of `sagePrimeFactors`. -/
@[simp] axiom mem_sagePrimeFactors_iff {p n : ℕ} :
    p ∈ sagePrimeFactors n ↔ p ∈ Nat.primeFactors n

-- Check that it works!
#eval sagePrimeFactors 102343422330000000000002    -- prints [2, 229, 2399, 46573]
-- #eval Nat.primeFactors 102343422330000000000002

/--
Now define our new algorithm.

Note this is an algorithm: it return a `Bool` not a `Prop`, and is computable:
-/
def sageIsPrimitiveRoot (a : ℕ) (p : ℕ) : Bool :=
  (a : ZMod p) != 0 && (sagePrimeFactors (p - 1)).all fun q => ((a : ZMod p) ^ ((p - 1) / q) : ZMod p) != 1

-- TODO run an example
#eval sageIsPrimitiveRoot 2 7927
#eval sageIsPrimitiveRoot 3 7927

/--
Now we verify that that this algorithm has the expected behaviour by relating it
to existing formalized notions in Mathlib.

Here `IsPrimitiveRoot x k` asserts that `a` is a primitive root of unity of order `k`
in some commutative monoid.
-/
-- theorem IsPrimitiveRoot_iff_sageIsPrimitiveRoot {p : ℕ} [Fact (p.Prime)] (a : ZMod p) :
--     IsPrimitiveRoot a (p - 1) ↔ sageIsPrimitiveRoot a.val p := by
--   -- This proof relies on a theorem in another file that right now has some `sorry`s
--   -- but we know how to resolve them, and these theorems properly belong in Mathlib (soon!).
--   simp [IsPrimitiveRoot_iff', sageIsPrimitiveRoot]


-- a ^ k (mod p)
def repeatedSquare (p : ℕ) (a : ℕ) : ℕ → ℕ
| 0 => 1
| (k + 1) =>
  if k % 2 = 0 then
    have : k / 2 < k + 1 := calc
      k / 2 ≤ (k + 1) / 2 := Nat.div_le_div_right (Nat.le_add_right k 1)
      _ < k + 1 := Nat.div_lt_self' k 0
    (a * (repeatedSquare p a (k/2))^2) % p
    else
    have : (k+1) / 2 < k + 1 := Nat.div_lt_self' k 0
    ((repeatedSquare p a ((k+1)/2))^2) % p
termination_by repeatedSquare p a k => k

#check ZMod

nonrec def ZMod.repeatedSquare {p : ℕ} (a : ZMod p) (k : ℕ) : ZMod p :=
  repeatedSquare p a.val k

#check @ZMod.npowImpl

def ZMod.repeatedSquare' (n : ℕ) (k : ℕ) (a : ZMod (n + 1)) : ZMod (n + 1) :=
  a.repeatedSquare k

@[csimp]
theorem square_equiv : ZMod.npowImpl = ZMod.repeatedSquare' :=
  sorry

#eval repeatedSquare 107 2 106
#eval 2^106 % 107
#eval (2 : ZMod 107)^106

#eval ZMod.npowImpl _ 106 (2 : ZMod 107)
#eval ZMod.repeatedSquare' _ 106 (2 : ZMod 107)

#eval repeatedSquare 49999 3 49998
#eval 3^49998 % 49999
-- #eval (3 : ZMod 49999)^49998

#synth Pow (ZMod 10) ℕ


#eval ZMod.npowImpl _ 49998 (3 : ZMod 49999)
#eval ZMod.repeatedSquare' _ 49998 (3 : ZMod 49999)

/-
def p := 104743
#eval sagePrimeFactors (p-1)
-- #eval [2].all fun q => (3 : ZMod p) ^ ((p - 1) / q) != 1
-- #eval [2, 3, 11, 23].all fun q => (3 : ZMod p) ^ ((p - 1) / q) != 1
-- #eval sageIsPrimitiveRoot 3 104743


#eval sageIsPrimitiveRoot 3 11


-/
