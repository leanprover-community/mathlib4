import Mathlib.Data.Finset.Basic
/-!
Tests that `List.choose` and friends all reduce appropriately.

Previously this was blocked by reducibility issues with `And.rec`
(https://leanprover.zulipchat.com/#narrow/stream/236446-Type-theory/topic/And.2Erec/near/398483665).
-/

namespace List

lemma foo : ∃ x, x ∈ ([0,3] : List (Fin 5)) ∧ x = 3 := by
  use 3
  simp

example : choose _ _ foo = 3 := by rfl
example : choose _ _ foo = 3 := rfl
example : choose _ _ foo = 3 := by eq_refl
example : choose _ _ foo = 3 := by exact rfl
example : choose _ _ foo = 3 := by decide

end List

namespace Multiset

lemma foo : ∃! x, x ∈ ({0,3} : Multiset (Fin 5)) ∧ x = 3 := by
  use 3
  simp

example : choose _ _ foo = 3 := by rfl
example : choose _ _ foo = 3 := rfl
example : choose _ _ foo = 3 := by eq_refl
example : choose _ _ foo = 3 := by exact rfl
example : choose _ _ foo = 3 := by decide

end Multiset

namespace Finset

lemma foo : ∃! x, x ∈ ({0,3} : Finset (Fin 5)) ∧ x = 3 := by
  use 3
  simp

example : choose _ _ foo = 3 := by rfl
example : choose _ _ foo = 3 := rfl
example : choose _ _ foo = 3 := by eq_refl
example : choose _ _ foo = 3 := by exact rfl
example : choose _ _ foo = 3 := by decide

end Finset
