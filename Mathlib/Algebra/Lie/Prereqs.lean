/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Batteries.Tactic.ShowUnused

-- move this
section

variable (R L M : Type*)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

instance instCanLiftSubmoduleLieSubmodule : CanLift (Submodule R M) (LieSubmodule R L M) (·)
    (fun N ↦ ∀ {x : L} {m : M}, m ∈ N → ⁅x, m⁆ ∈ N) where
  prf N hN := ⟨⟨N, hN⟩, rfl⟩

end

-- move this
section

open LieAlgebra

class LieTower (L₁ L₂ M : Type*) [Add M] [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] where
    leibniz_lie : ∀ (x : L₁) (y : L₂) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

lemma leibniz_lie' {L₁ L₂ M : Type*}
    [Add M] [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [LieTower L₁ L₂ M]
    (x : L₁) (y : L₂) (m : M) :
    ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := LieTower.leibniz_lie x y m

lemma lie_swap_lie {L₁ L₂ M : Type*} [AddCommGroup M]
    [Bracket L₁ L₂] [Bracket L₂ L₁] [Bracket L₁ M] [Bracket L₂ M]
    [LieTower L₁ L₂ M] [LieTower L₂ L₁ M]
    (x : L₁) (y : L₂) (m : M) :
    ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆ := by
  have h1 := leibniz_lie' x y m
  have h2 := leibniz_lie' y x m
  convert congr($h1.symm - $h2) using 1 <;> abel

instance {L : Type*} (M : Type*) [LieRing L] [AddCommGroup M] [LieRingModule L M] :
    LieTower L L M where
  leibniz_lie x y m := leibniz_lie x y m

instance {R L : Type*} (M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [LieRingModule L M] (A : LieSubalgebra R L) :
    LieTower A L M where
  leibniz_lie x y m := leibniz_lie x.val y m

instance {R L : Type*} (M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [LieRingModule L M] (A : LieIdeal R L) :
    LieTower A L M where
  leibniz_lie x y m := leibniz_lie x.val y m

instance {R L : Type*} (M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [LieRingModule L M] (A : LieIdeal R L) :
    LieTower L A M where
  leibniz_lie x y m := leibniz_lie x y.val m

end

-- move this
open LieAlgebra in
instance (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  (A : LieIdeal R L) [IsSolvable R L] : IsSolvable R A :=
  A.incl_injective.lieAlgebra_isSolvable

-- move this
lemma IsCoatom.lt_top {α : Type*} [PartialOrder α] [OrderTop α] {a : α} (h : IsCoatom a) : a < ⊤ :=
  h.lt_iff.mpr rfl

-- move this
lemma Submodule.disjoint_span_of_not_mem
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (A : Submodule k V) (x : V) (hx : x ∉ A) :
    Disjoint A (k ∙ x) := by
  rw [disjoint_iff_inf_le]
  rintro y ⟨(hyA : y ∈ A), (hyx : y ∈ k ∙ x)⟩
  obtain ⟨c, rfl⟩ : ∃ c, c • x = y := by rwa [Submodule.mem_span_singleton] at hyx
  apply A.smul_mem c⁻¹ at hyA
  rcases eq_or_ne c 0 with (rfl | hc) <;> simp_all

-- move this
lemma Submodule.isCompl_span_of_iscoatom_of_not_mem
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (A : Submodule k V) (x : V) (hA : IsCoatom A) (hx : x ∉ A) :
    IsCompl A (k ∙ x) := by
  refine ⟨disjoint_span_of_not_mem A x hx, ?_⟩ 
  rw [codisjoint_iff_le_sup]
  apply (hA.2 _ _).ge
  rw [left_lt_sup]
  contrapose! hx
  exact hx <| Submodule.mem_span_singleton_self x

-- move this
@[simp]
lemma LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    (x : M) (h : x ≠ 0) (y) :
    (toSpanNonzeroSingleton R M x h).symm y • x = y := by
  set e := toSpanNonzeroSingleton R M x h
  show (e (e.symm y) : M) = y
  simp

