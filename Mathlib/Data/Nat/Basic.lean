import Std.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Nontrivial

namespace Nat

instance : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

attribute [simp] succ_ne_zero lt_succ_self

protected def case_strong_rec_on {p : ℕ → Sort u} (a : ℕ)
  (hz : p 0) (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
Nat.strong_rec_on a fun | 0, _ => hz | n+1, ih => hi n (λ m w => ih m (lt_succ_of_le w))

/- Up -/

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def Up (ub a i : ℕ) := i < a ∧ i < ub

lemma Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩

lemma Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := (measure (ub - .)).wf) fun ⟨ia, iu⟩ => Nat.sub_lt_sub_left iu ia

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def upRel (ub : ℕ) : WellFoundedRelation Nat := ⟨Up ub, Up.WF ub⟩
