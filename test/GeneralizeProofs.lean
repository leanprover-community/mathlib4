import Mathlib.Algebra.Ring.Nat
import Mathlib.Tactic.GeneralizeProofs

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true
noncomputable def List.nthLe (l : List α) (n) (_h : n < l.length) : α := test_sorry

-- For debugging `generalize_proofs`
-- set_option trace.Tactic.generalize_proofs true

example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  generalize_proofs h
  guard_hyp h :ₛ 1 < List.length [1, 2]
  guard_target =ₛ [1, 2].nthLe 1 h = 2
  exact test_sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2 := by
  generalize_proofs a
  guard_hyp a :ₛ ∃ x, x < 2
  guard_target =ₛ Classical.choose a < 2
  exact Classical.choose_spec a

example (x : ℕ) (h : x < 2) :
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2) = Classical.choose (⟨x, h⟩ : ∃ x, x < 2) := by
  generalize_proofs a
  guard_hyp a :ₛ ∃ x, x < 2
  guard_target =ₛ Classical.choose a = Classical.choose a
  rfl

example (x : ℕ) (h : x < 2) (h' : x < 1) :
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2)
      = Classical.choose (⟨x, (by clear h; omega)⟩ : ∃ x, x < 2) := by
  generalize_proofs a
  guard_hyp a :ₛ ∃ x, x < 2
  guard_target =ₛ Classical.choose a = Classical.choose a
  rfl

example (x : ℕ) (h h' : x < 2) :
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2) = Classical.choose (⟨x, h'⟩ : ∃ x, x < 2) := by
  change _ at h'
  fail_if_success guard_target =ₛ
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2) = Classical.choose (⟨x, h⟩ : ∃ x, x < 2)
  generalize_proofs at h'
  fail_if_success change _ at h'
  guard_target =ₛ Classical.choose (⟨x, h⟩ : ∃ x, x < 2) = Classical.choose (⟨x, h⟩ : ∃ x, x < 2)
  generalize_proofs a
  guard_target =ₛ Classical.choose a = Classical.choose a
  rfl

example (x : ℕ) (h : x < 2) :
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2)
      = Classical.choose (⟨x, Nat.lt_succ_of_lt h⟩ : ∃ x, x < 3) := by
  generalize_proofs a a'
  guard_hyp a :ₛ ∃ x, x < 2
  guard_hyp a' :ₛ ∃ x, x < 3
  guard_target =ₛ Classical.choose a = Classical.choose a'
  exact test_sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) =
  Classical.choose (⟨x, Nat.lt_succ_of_lt h⟩ : ∃ x, x < 3) := by
  generalize_proofs
  guard_target = Classical.choose _ = Classical.choose _
  exact test_sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) =
  Classical.choose (⟨x, Nat.lt_succ_of_lt h⟩ : ∃ x, x < 3) := by
  generalize_proofs _ a
  guard_hyp a : ∃ x, x < 3
  guard_target = Classical.choose _ = Classical.choose a
  exact test_sorry

example (a : ∃ x, x < 2) : Classical.choose a < 2 := by
  generalize_proofs
  guard_target =ₛ Classical.choose a < 2
  exact Classical.choose_spec a

example (a : ∃ x, x < 2) : Classical.choose a < 2 := by
  generalize_proofs t
  guard_target =ₛ Classical.choose a < 2
  exact Classical.choose_spec a

example (x : ℕ) (h : x < 2) (H : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2) :
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2 := by
  generalize_proofs a at H ⊢
  guard_hyp a :ₛ ∃ x, x < 2
  guard_hyp H :ₛ Classical.choose a < 2
  guard_target =ₛ Classical.choose a < 2
  exact H

example (H : ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y) :
    ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y := by
  generalize_proofs (config := { abstract := false })
  guard_target =ₛ ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y
  generalize_proofs a at H ⊢
  guard_hyp a :ₛ ∀ (y w : ℕ), w < y → ∃ x, x < y
  guard_hyp H :ₛ ∀ (y : ℕ), ∃ x h, Classical.choose (a y x h) < y
  guard_target =ₛ ∀ (y : ℕ), ∃ x h, Classical.choose (a y x h) < y
  exact H

example (H : ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y) :
    ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y := by
  generalize_proofs a at *
  guard_hyp a :ₛ ∀ (y w : ℕ), w < y → ∃ x, x < y
  guard_hyp H :ₛ ∀ (y : ℕ), ∃ x h, Classical.choose (a y x h) < y
  guard_target =ₛ ∀ (y : ℕ), ∃ x h, Classical.choose (a y x h) < y
  exact H

namespace zulip1
/-!
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60generalize_proofs.60.20sometimes.20silently.20has.20no.20effect/near/407162574
-/

theorem t (x : Option Unit) : x.isSome = true := test_sorry
def p : Unit → Prop := test_sorry

theorem good (x : Option Unit) : p (Option.get x test_sorry) → x.isSome = true := by
  generalize_proofs h
  exact fun _ => h

theorem was_bad (x : Option Unit) : p (Option.get x (t x)) → x.isSome = true := by
  generalize_proofs h
  exact fun _ => h

end zulip1

section

attribute [local instance] Classical.propDecidable

example (H : ∀ x, x = 1) : (if h : ∃ (k : ℕ), k = 1 then Classical.choose h else 0) = 1 := by
  rw [dif_pos ?hc]
  case hc => exact ⟨1, rfl⟩
  generalize_proofs h
  guard_hyp h :ₛ ∃ x, x = 1
  guard_target =ₛ Classical.choose h = 1
  apply H

end
