import Mathlib.Tactic.Linter.FindDefEqAbuse

set_option diagnostics true
set_option diagnostics.threshold 100000000

find_defeq_abuse X.Y
namespace X

def Y := Option Nat

--attribute [irreducible] Y

/-- warning: 'f' relies on the definition of 'X.Y' -/
#guard_msgs in
def f : Y := some 0

/-- warning: 'g' relies on the definition of 'X.Y' -/
#guard_msgs in
def g : Y := some 0

theorem f_eq_g : f = g := rfl

/-- warning: 'd' relies on the definition of 'X.Y' -/
#guard_msgs in
theorem d : f = g := by
  unfold f g
  rfl

end X

find_defeq_abuse ENat
section Z

def WithTop (α : Type) := Option α

axiom WithTop.lt {α : Type} : WithTop α → WithTop α → Prop

instance : LT (WithTop α) := ⟨WithTop.lt⟩

def WithTop.coe (v : α) : WithTop α := some v

axiom WithTop.coe_lt_coe {α : Type} [LT α] {a b : α} : coe a < coe b ↔ a < b

def ENat := WithTop Nat

/-- warning: 'instLTENat' relies on the definition of 'ENat' -/
#guard_msgs in
instance : LT ENat := inferInstanceAs (LT (WithTop Nat))

/-- warning: 'instNatCastENat' relies on the definition of 'ENat' -/
#guard_msgs in
instance : NatCast ENat where
  natCast n := .coe n

/-- warning: 'test' relies on the definition of 'instNatCastENat' -/
#guard_msgs in
theorem test (k : Nat) : (k : ENat) < ((k + 1 : Nat) : ENat) := WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)

end Z
