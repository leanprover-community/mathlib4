import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.Positivity

/-! Tests for the `Nat.fib` `norm_num` extension and its companion simproc. -/

-- via the `norm_num` extension
example : Nat.fib 12 = 144 := by norm_num
example : Nat.fib 0 = 0 := by norm_num
example : Nat.fib 1 = 1 := by norm_num
example : Nat.fib 70 = 190392490709135 := by norm_num

-- via the generated simproc: these need `simp`/`grind`, which could not do them before
example : Nat.fib 12 = 144 := by simp
example : Nat.fib 12 = 144 := by grind
example : Nat.fib (10 + 2) = 144 := by simp

/-- The extension must keep normalising its own operands, because `NormNum.derive` does no
traversal of its own. Consumers that call `derive` directly (`ring`, `positivity`, ...) rely
on this; a simproc-only implementation would silently fail here. -/
example : 0 < Nat.fib (Nat.sqrt 144) := by positivity
example : Nat.fib (Nat.sqrt 144) = 144 := by norm_num
example : Nat.fib 12 + 6 = 150 := by norm_num

section phases
open Qq Mathlib.Meta.NormNum

/-- An extension may opt out of `simp`'s post phase; the companion simproc then never fires,
while `norm_num` still runs the extension in its own pre phase. -/
local norm_num_simproc [simp] evalFibNoPost (Nat.fib _) where
  post := false
  eval {_ _} e := do
    let .app _ (x : Q(ℕ)) ← Lean.Meta.whnfR e | failure
    let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
    let ⟨ex, p⟩ ← deriveNat x sℕ
    let ⟨ey, pf⟩ := proveNatFib ex
    let pf' : Q(IsNat (Nat.fib $x) $ey) := q(isNat_fib $p $pf)
    return .isNat sℕ ey pf'

example : Nat.fib 12 = 144 := by
  fail_if_success simp only [evalFibNoPost]
  norm_num

end phases
