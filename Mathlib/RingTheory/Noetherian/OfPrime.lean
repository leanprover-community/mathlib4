/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
import Mathlib.RingTheory.Ideal.Oka
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Noetherian rings and prime ideals

## Main results

- `IsNoetherianRing.of_prime`: a ring where all prime ideals are principal is a principal ideal ring

## References

- [cohen1950]: *Commutative rings with restricted minimum condition*, I. S. Cohen, Theorem 2
-/

variable {R : Type*}

namespace Ideal

/-- If a commutative (semi)ring has a infinitely generated ideal, then it has an ideal which is
maximal for being infinitely generated. -/
theorem exists_maximal_not_fg [CommSemiring R] (h : ∃ I : Ideal R, ¬I.FG) :
    ∃ I : Ideal R, Maximal (¬·.FG) I := by
  refine zorn_le₀ _ (fun C hC hC₂ ↦ ?_)
  by_cases H : C.Nonempty
  · refine ⟨sSup C, ?_, fun _ ↦ le_sSup⟩
    intro ⟨G, hG⟩
    obtain ⟨I, I_mem_C, G_subset_I⟩ : ∃ I ∈ C, G.toSet ⊆ I := by
      refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion H (fun _ hx ↦ ?_)
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
      exact (Submodule.mem_sSup_of_directed H hC₂.directedOn).1 <| hG ▸ subset_span hx
    have I_eq_sSup : I = sSup C := le_antisymm (le_sSup I_mem_C) (hG ▸ Ideal.span_le.2 G_subset_I)
    exact hC I_mem_C ⟨G, I_eq_sSup ▸ hG⟩
  · obtain ⟨I, hI⟩ := h
    exact ⟨I, hI, by simp [Set.not_nonempty_iff_eq_empty.1 H]⟩

-- TODO: Mettre dans RingTheory/Ideal/Span.lean
lemma mem_span_range_self [Semiring R] {α : Type*} {f : α → R} : ∀ {x}, f x ∈ span (Set.range f) :=
  (subset_span <| Set.mem_range_self _)

open Set Finset

/-- `Ideal.FG` is an Oka predicate. -/
theorem isOka_fg [CommRing R] : IsOka (FG (R := R)) where
  top := ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    classical
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H k : ∃ r : R, ∃ p ∈ I, r * a + p = f k := by
      apply mem_span_singleton_sup.1
      rw [sup_comm, ← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ ∪ image (a • i) univ, le_antisymm ?_ (fun y hy ↦ ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun _ ↦ mul_comm a _ ▸ mem_colon_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 (hf ▸ Ideal.mem_sup_left hy)
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib, ← sum_mul, add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ ↦ mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm, ← smul_eq_mul, range_smul, ← submodule_span_eq, Submodule.span_smul, hi]
      exact smul_mem_smul_set <| mem_colon_singleton.2 <|
        (I.add_mem_iff_right <| I.sum_mem (fun _ _ ↦ mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)

end Ideal

open Ideal

theorem IsNoetherianRing.of_prime [CommRing R] (H : ∀ I : Ideal R, I.IsPrime → I.FG) :
    IsNoetherianRing R :=
  ⟨isOka_fg.forall_of_forall_prime_isOka exists_maximal_not_fg H⟩
