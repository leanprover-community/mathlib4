/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov

! This file was ported from Lean 3 source module linear_algebra.isomorphisms
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Quotient

/-!
# Isomorphism theorems for modules.

* The Noether's first, second, and third isomorphism theorems for modules are proved as
  `linear_map.quot_ker_equiv_range`, `linear_map.quotient_inf_equiv_sup_quotient` and
  `submodule.quotient_quotient_equiv_quotient`.

-/


universe u v

variable {R M M₂ M₃ : Type _}

variable [Ring R] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f : M →ₗ[R] M₂)

/-! The first and second isomorphism theorems for modules. -/


namespace LinearMap

open Submodule

section IsomorphismLaws

/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`. -/
noncomputable def quotKerEquivRange : (M ⧸ f.ker) ≃ₗ[R] f.range :=
  (LinearEquiv.ofInjective (f.ker.liftQ f <| le_rfl) <|
        ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ (le_refl f.ker)).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftQ _ _ _)
#align linear_map.quot_ker_equiv_range LinearMap.quotKerEquivRange

/-- The first isomorphism theorem for surjective linear maps. -/
noncomputable def quotKerEquivOfSurjective (f : M →ₗ[R] M₂) (hf : Function.Surjective f) :
    (M ⧸ f.ker) ≃ₗ[R] M₂ :=
  f.quotKerEquivRange.trans (LinearEquiv.ofTop f.range (LinearMap.range_eq_top.2 hf))
#align linear_map.quot_ker_equiv_of_surjective LinearMap.quotKerEquivOfSurjective

@[simp]
theorem quotKerEquivRange_apply_mk (x : M) :
    (f.quotKerEquivRange (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl
#align linear_map.quot_ker_equiv_range_apply_mk LinearMap.quotKerEquivRange_apply_mk

@[simp]
theorem quotKerEquivRange_symm_apply_image (x : M) (h : f x ∈ f.range) :
    f.quotKerEquivRange.symm ⟨f x, h⟩ = f.ker.mkQ x :=
  f.quotKerEquivRange.symm_apply_apply (f.ker.mkQ x)
#align linear_map.quot_ker_equiv_range_symm_apply_image LinearMap.quotKerEquivRange_symm_apply_image

/-- Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotientInfToSupQuotient (p p' : Submodule R M) :
    p ⧸ comap p.Subtype (p ⊓ p') →ₗ[R] _ ⧸ comap (p ⊔ p').Subtype p' :=
  (comap p.subtype (p ⊓ p')).liftQ ((comap (p ⊔ p').Subtype p').mkQ.comp (of_le le_sup_left))
    (by
      rw [ker_comp, of_le, comap_cod_restrict, ker_mkq, map_comap_subtype]
      exact comap_mono (inf_le_inf_right _ le_sup_left))
#align linear_map.quotient_inf_to_sup_quotient LinearMap.quotientInfToSupQuotient

/--
Second Isomorphism Law : the canonical map from `p/(p ∩ p')` to `(p+p')/p'` as a linear isomorphism.
-/
noncomputable def quotientInfEquivSupQuotient (p p' : Submodule R M) :
    (p ⧸ comap p.Subtype (p ⊓ p')) ≃ₗ[R] _ ⧸ comap (p ⊔ p').Subtype p' :=
  LinearEquiv.ofBijective (quotient_inf_to_sup_quotient p p')
    ⟨by
      rw [← ker_eq_bot, quotient_inf_to_sup_quotient, ker_liftq_eq_bot]
      rw [ker_comp, ker_mkq]
      exact fun ⟨x, hx1⟩ hx2 => ⟨hx1, hx2⟩,
      by
      rw [← range_eq_top, quotient_inf_to_sup_quotient, range_liftq, eq_top_iff']
      rintro ⟨x, hx⟩; rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
      use ⟨y, hy⟩; apply (Submodule.Quotient.eq _).2
      change y - (y + z) ∈ p'
      rwa [sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff]⟩
#align linear_map.quotient_inf_equiv_sup_quotient LinearMap.quotientInfEquivSupQuotient

@[simp]
theorem coe_quotientInfToSupQuotient (p p' : Submodule R M) :
    ⇑(quotientInfToSupQuotient p p') = quotientInfEquivSupQuotient p p' :=
  rfl
#align linear_map.coe_quotient_inf_to_sup_quotient LinearMap.coe_quotientInfToSupQuotient

@[simp]
theorem quotientInfEquivSupQuotient_apply_mk (p p' : Submodule R M) (x : p) :
    quotientInfEquivSupQuotient p p' (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ofLe (le_sup_left : p ≤ p ⊔ p') x) :=
  rfl
#align linear_map.quotient_inf_equiv_sup_quotient_apply_mk LinearMap.quotientInfEquivSupQuotient_apply_mk

theorem quotientInfEquivSupQuotient_symm_apply_left (p p' : Submodule R M) (x : p ⊔ p')
    (hx : (x : M) ∈ p) :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨x, hx⟩ :=
  (LinearEquiv.symm_apply_eq _).2 <| by simp [of_le_apply]
#align linear_map.quotient_inf_equiv_sup_quotient_symm_apply_left LinearMap.quotientInfEquivSupQuotient_symm_apply_left

@[simp]
theorem quotientInfEquivSupQuotient_symm_apply_eq_zero_iff {p p' : Submodule R M} {x : p ⊔ p'} :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = 0 ↔ (x : M) ∈ p' :=
  (LinearEquiv.symm_apply_eq _).trans <| by simp [of_le_apply]
#align linear_map.quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff LinearMap.quotientInfEquivSupQuotient_symm_apply_eq_zero_iff

theorem quotientInfEquivSupQuotient_symm_apply_right (p p' : Submodule R M) {x : p ⊔ p'}
    (hx : (x : M) ∈ p') : (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = 0 :=
  quotientInfEquivSupQuotient_symm_apply_eq_zero_iff.2 hx
#align linear_map.quotient_inf_equiv_sup_quotient_symm_apply_right LinearMap.quotientInfEquivSupQuotient_symm_apply_right

end IsomorphismLaws

end LinearMap

/-! The third isomorphism theorem for modules. -/


namespace Submodule

variable (S T : Submodule R M) (h : S ≤ T)

/-- The map from the third isomorphism theorem for modules: `(M / S) / (T / S) → M / T`. -/
def quotientQuotientEquivQuotientAux (h : S ≤ T) : (M ⧸ S) ⧸ T.map S.mkQ →ₗ[R] M ⧸ T :=
  liftq _ (mapq S T LinearMap.id h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker, mkq_apply, mapq_apply]
      exact (quotient.mk_eq_zero _).mpr hx)
#align submodule.quotient_quotient_equiv_quotient_aux Submodule.quotientQuotientEquivQuotientAux

@[simp]
theorem quotientQuotientEquivQuotientAux_mk (x : M ⧸ S) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk x) = mapQ S T LinearMap.id h x :=
  liftQ_apply _ _ _
#align submodule.quotient_quotient_equiv_quotient_aux_mk Submodule.quotientQuotientEquivQuotientAux_mk

@[simp]
theorem quotientQuotientEquivQuotientAux_mk_mk (x : M) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk (Quotient.mk x)) = Quotient.mk x := by
  rw [quotient_quotient_equiv_quotient_aux_mk, mapq_apply, LinearMap.id_apply]
#align submodule.quotient_quotient_equiv_quotient_aux_mk_mk Submodule.quotientQuotientEquivQuotientAux_mk_mk

/-- **Noether's third isomorphism theorem** for modules: `(M / S) / (T / S) ≃ M / T`. -/
def quotientQuotientEquivQuotient : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T :=
  {
    quotientQuotientEquivQuotientAux S T
      h with
    toFun := quotientQuotientEquivQuotientAux S T h
    invFun := mapQ _ _ (mkQ S) (le_comap_map _ _)
    left_inv := fun x => Quotient.inductionOn' x fun x => Quotient.inductionOn' x fun x => by simp
    right_inv := fun x => Quotient.inductionOn' x fun x => by simp }
#align submodule.quotient_quotient_equiv_quotient Submodule.quotientQuotientEquivQuotient

/-- Corollary of the third isomorphism theorem: `[S : T] [M : S] = [M : T]` -/
theorem card_quotient_mul_card_quotient (S T : Submodule R M) (hST : T ≤ S)
    [DecidablePred fun x => x ∈ S.map T.mkQ] [Fintype (M ⧸ S)] [Fintype (M ⧸ T)] :
    Fintype.card (S.map T.mkQ) * Fintype.card (M ⧸ S) = Fintype.card (M ⧸ T) := by
  rw [Submodule.card_eq_card_quotient_mul_card (map T.mkq S),
    fintype.card_eq.mpr ⟨(quotient_quotient_equiv_quotient T S hST).toEquiv⟩]
#align submodule.card_quotient_mul_card_quotient Submodule.card_quotient_mul_card_quotient

end Submodule

