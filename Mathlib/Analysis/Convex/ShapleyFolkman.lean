import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped Pointwise BigOperators
open Set Finset

variable {ι : Type*}
variable {E : Type*}

section SetSums

variable [AddCommMonoid E]

#check Set.mem_add
#check Set.mem_zero
#check Finset.sum_insert
#check Finset.sum_eq_zero
#check Finset.induction_on

example (A B : Set E) (x y : E) (hx : x ∈ A) (hy : y ∈ B) :
    x + y ∈ A + B := by
  exact ⟨x, hx, y, hy, rfl⟩

example (A B : Set E) (z : E) (hz : z ∈ A + B) :
    ∃ x ∈ A, ∃ y ∈ B, x + y = z := by
  simpa [Set.mem_add] using hz

lemma mem_finset_sum_sets_of_forall
    (s : Finset ι) (A : ι → Set E) (x : ι → E)
    (hx : ∀ i ∈ s, x i ∈ A i) :
    (∑ i ∈ s, x i) ∈ (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      rw [Finset.sum_insert has]
      exact ⟨x a, hx a (by simp), ∑ i ∈ s, x i,
        ih (fun i hi => hx i (by simp [hi])), rfl⟩

lemma mem_finset_sum_sets_exists
    (s : Finset ι) (A : ι → Set E) (z : E)
    (hz : z ∈ (∑ i ∈ s, A i)) :
    ∃ x : ι → E,
      (∀ i ∈ s, x i ∈ A i) ∧
      ∑ i ∈ s, x i = z := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i hi
        simp at hi
      · simpa using hz.symm

  | insert a s has ih =>
      rw [Finset.sum_insert has] at hz
      rcases hz with ⟨xa, hxa, ys, hys, hsum⟩
      rcases ih ys hys with ⟨x, hx, hxsum⟩

      refine ⟨Function.update x a xa, ?_, ?_⟩

      · intro i hi
        by_cases hia : i = a
        · subst hia
          simp [Function.update, hxa]
        · have his : i ∈ s := by
            simpa [hia] using hi
          simp [Function.update, hia, hx i his]

      · rw [Finset.sum_insert has]

        have hsum_update :
            ∑ i ∈ s, Function.update x a xa i = ∑ i ∈ s, x i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hia : i ≠ a := by
            intro h
            exact has (h ▸ hi)
          simp [Function.update, hia]

        calc
          Function.update x a xa a + ∑ i ∈ s, Function.update x a xa i
              = xa + ∑ i ∈ s, x i := by
                  rw [hsum_update]
                  simp [Function.update]
          _ = xa + ys := by
                  rw [hxsum]
          _ = z := by
                  simpa using hsum

end SetSums
