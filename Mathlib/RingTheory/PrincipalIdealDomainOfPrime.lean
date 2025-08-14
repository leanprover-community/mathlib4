/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.Ideal.Oka
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal ideal domains and prime ideals

## Main results

- `IsPrincipalIdealRing.of_prime`: a ring where all prime ideals are principal is a principal ideal
  ring.
-/

variable {R : Type*} [CommSemiring R]

namespace Ideal

/-- If a commutative (semi)ring has a non-principal ideal, then it has an ideal which is maximal for
not being principal. -/
lemma exists_maximal_not_principal (h : ∃ I : Ideal R, ¬I.IsPrincipal) :
    ∃ I : Ideal R, Maximal (¬·.IsPrincipal) I := by
  refine zorn_le₀ { I : Ideal R | ¬I.IsPrincipal } (fun C hC hC₂ ↦ ?_)
  by_cases H : C.Nonempty
  · refine ⟨sSup C, ?_, fun _ ↦ le_sSup⟩
    intro ⟨x, hx⟩
    have : x ∈ sSup C := hx ▸ mem_span_singleton_self x
    obtain ⟨I, I_mem_C, x_mem_I⟩ := Submodule.mem_sSup_of_directed H hC₂.directedOn |>.1 this
    have I_eq_sSup : I = sSup C := le_antisymm (le_sSup I_mem_C)
      (hx ▸ (span_singleton_le_iff_mem I |>.2 x_mem_I))
    exact (I_eq_sSup ▸ hC I_mem_C) ⟨x, hx⟩
  · obtain ⟨I, hI⟩ := h
    exact ⟨I, hI, by simp [Set.not_nonempty_iff_eq_empty.1 H]⟩

/-- `Submodule.IsPrincipal` is an Oka predicate. -/
theorem isOka_isPrincipal : IsOka (Submodule.IsPrincipal (R := R)) where
  top := top_isPrincipal
  oka {I a} := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, le_antisymm ?_ ?_⟩ <;> rw [submodule_span_eq] at *
    · intro i hi
      have hisup : i ∈ I ⊔ span {a} := mem_sup_left hi
      have hasup : a ∈ I ⊔ span {a} := mem_sup_right (mem_span_singleton_self a)
      rw [hx, mem_span_singleton'] at hisup hasup
      obtain ⟨u, rfl⟩ := hisup
      obtain ⟨v, rfl⟩ := hasup
      obtain ⟨z, rfl⟩ : ∃ z, z * y = u := by
        rw [← mem_span_singleton', ← hy, mem_colon_singleton, mul_comm v, ← mul_assoc]
        exact mul_mem_right _ _ hi
      exact mem_span_singleton'.2 ⟨z, by rw [mul_assoc, mul_comm y]⟩
    · rw [← span_singleton_mul_span_singleton, ← hx, Ideal.sup_mul, sup_le_iff,
        span_singleton_mul_span_singleton, mul_comm a, span_singleton_le_iff_mem]
      exact ⟨mul_le_right, mem_colon_singleton.1 <| hy ▸ mem_span_singleton_self y⟩

end Ideal

open Ideal

/-- If all prime ideals in a commutative ring are principal, so are all other ideals. -/
theorem IsPrincipalIdealRing.of_prime (H : ∀ P : Ideal R, P.IsPrime → P.IsPrincipal) :
    IsPrincipalIdealRing R :=
  ⟨isOka_isPrincipal.forall_of_forall_prime_isOka exists_maximal_not_principal H⟩
