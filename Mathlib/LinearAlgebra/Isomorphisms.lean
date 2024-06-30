/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Quotient

#align_import linear_algebra.isomorphisms from "leanprover-community/mathlib"@"2738d2ca56cbc63be80c3bd48e9ed90ad94e947d"

/-!
# Isomorphism theorems for modules.

* The Noether's first, second, and third isomorphism theorems for modules are proved as
  `LinearMap.quotKerEquivRange`, `LinearMap.quotientInfEquivSupQuotient` and
  `Submodule.quotientQuotientEquivQuotient`.

-/

universe u v

variable {R M M₂ M₃ : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable (f : M →ₗ[R] M₂)

/-! The first and second isomorphism theorems for modules. -/

namespace LinearMap

open Submodule

section IsomorphismLaws

/-- The **first isomorphism law for modules**. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`. -/
noncomputable def quotKerEquivRange : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  (LinearEquiv.ofInjective (f.ker.liftQ f <| le_rfl) <|
        ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (LinearMap.ker f))).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftQ _ _ _)
#align linear_map.quot_ker_equiv_range LinearMap.quotKerEquivRange

/-- The **first isomorphism theorem for surjective linear maps**. -/
noncomputable def quotKerEquivOfSurjective (f : M →ₗ[R] M₂) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] M₂ :=
  f.quotKerEquivRange.trans (LinearEquiv.ofTop (LinearMap.range f) (LinearMap.range_eq_top.2 hf))
#align linear_map.quot_ker_equiv_of_surjective LinearMap.quotKerEquivOfSurjective

@[simp]
theorem quotKerEquivRange_apply_mk (x : M) :
    (f.quotKerEquivRange (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl
#align linear_map.quot_ker_equiv_range_apply_mk LinearMap.quotKerEquivRange_apply_mk

@[simp]
theorem quotKerEquivRange_symm_apply_image (x : M) (h : f x ∈ LinearMap.range f) :
    f.quotKerEquivRange.symm ⟨f x, h⟩ = f.ker.mkQ x :=
  f.quotKerEquivRange.symm_apply_apply (f.ker.mkQ x)
#align linear_map.quot_ker_equiv_range_symm_apply_image LinearMap.quotKerEquivRange_symm_apply_image

-- Porting note: breaking up original definition of quotientInfToSupQuotient to avoid timing out
/-- Linear map from `p` to `p+p'/p'` where `p p'` are submodules of `R` -/
abbrev subToSupQuotient (p p' : Submodule R M) :
    { x // x ∈ p } →ₗ[R] { x // x ∈ p ⊔ p' } ⧸ comap (Submodule.subtype (p ⊔ p')) p' :=
  (comap (p ⊔ p').subtype p').mkQ.comp (Submodule.inclusion le_sup_left)

-- Porting note: breaking up original definition of quotientInfToSupQuotient to avoid timing out
theorem comap_leq_ker_subToSupQuotient (p p' : Submodule R M) :
    comap (Submodule.subtype p) (p ⊓ p') ≤ ker (subToSupQuotient p p') := by
  rw [LinearMap.ker_comp, Submodule.inclusion, comap_codRestrict, ker_mkQ, map_comap_subtype]
  exact comap_mono (inf_le_inf_right _ le_sup_left)

/-- Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotientInfToSupQuotient (p p' : Submodule R M) :
    (↥p) ⧸ (comap p.subtype (p ⊓ p')) →ₗ[R] (↥(p ⊔ p')) ⧸ (comap (p ⊔ p').subtype p') :=
   (comap p.subtype (p ⊓ p')).liftQ (subToSupQuotient p p') (comap_leq_ker_subToSupQuotient p p')
#align linear_map.quotient_inf_to_sup_quotient LinearMap.quotientInfToSupQuotient

-- Porting note: breaking up original definition of quotientInfEquivSupQuotient to avoid timing out
theorem quotientInfEquivSupQuotient_injective (p p' : Submodule R M) :
    Function.Injective (quotientInfToSupQuotient p p') := by
  rw [← ker_eq_bot, quotientInfToSupQuotient, ker_liftQ_eq_bot]
  rw [ker_comp, ker_mkQ]
  exact fun ⟨x, hx1⟩ hx2 => ⟨hx1, hx2⟩

-- Porting note: breaking up original definition of quotientInfEquivSupQuotient to avoid timing out
theorem quotientInfEquivSupQuotient_surjective (p p' : Submodule R M) :
    Function.Surjective (quotientInfToSupQuotient p p') := by
  rw [← range_eq_top, quotientInfToSupQuotient, range_liftQ, eq_top_iff']
  rintro ⟨x, hx⟩; rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
  use ⟨y, hy⟩; apply (Submodule.Quotient.eq _).2
  simp only [mem_comap, map_sub, coeSubtype, coe_inclusion, sub_add_cancel_left, neg_mem_iff, hz]

/--
Second Isomorphism Law : the canonical map from `p/(p ∩ p')` to `(p+p')/p'` as a linear isomorphism.
-/
noncomputable def quotientInfEquivSupQuotient (p p' : Submodule R M) :
    (p ⧸ comap p.subtype (p ⊓ p')) ≃ₗ[R] _ ⧸ comap (p ⊔ p').subtype p' :=
  LinearEquiv.ofBijective (quotientInfToSupQuotient p p')
    ⟨quotientInfEquivSupQuotient_injective p p', quotientInfEquivSupQuotient_surjective p p'⟩
#align linear_map.quotient_inf_equiv_sup_quotient LinearMap.quotientInfEquivSupQuotient

-- @[simp]
-- Porting note: `simp` affects the type arguments of `DFunLike.coe`, so this theorem can't be
--               a simp theorem anymore, even if it has high priority.
theorem coe_quotientInfToSupQuotient (p p' : Submodule R M) :
    ⇑(quotientInfToSupQuotient p p') = quotientInfEquivSupQuotient p p' :=
  rfl
#align linear_map.coe_quotient_inf_to_sup_quotient LinearMap.coe_quotientInfToSupQuotient

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem quotientInfEquivSupQuotient_apply_mk (p p' : Submodule R M) (x : p) :
    let map := inclusion (le_sup_left : p ≤ p ⊔ p')
    quotientInfEquivSupQuotient p p' (Submodule.Quotient.mk x) =
      @Submodule.Quotient.mk R (p ⊔ p' : Submodule R M) _ _ _ (comap (p ⊔ p').subtype p') (map x) :=
  rfl
#align linear_map.quotient_inf_equiv_sup_quotient_apply_mk LinearMap.quotientInfEquivSupQuotient_apply_mk

theorem quotientInfEquivSupQuotient_symm_apply_left (p p' : Submodule R M) (x : ↥(p ⊔ p'))
    (hx : (x : M) ∈ p) :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨x, hx⟩ :=
  (LinearEquiv.symm_apply_eq _).2 <| by
    -- porting note (#10745): was `simp`.
    rw [quotientInfEquivSupQuotient_apply_mk, inclusion_apply]
#align linear_map.quotient_inf_equiv_sup_quotient_symm_apply_left LinearMap.quotientInfEquivSupQuotient_symm_apply_left


-- @[simp] -- Porting note (#10618): simp can prove this
theorem quotientInfEquivSupQuotient_symm_apply_eq_zero_iff {p p' : Submodule R M} {x : ↥(p ⊔ p')} :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = 0 ↔ (x : M) ∈ p' :=
  (LinearEquiv.symm_apply_eq _).trans <| by
    -- porting note (#10745): was `simp`.
    rw [_root_.map_zero, Quotient.mk_eq_zero, mem_comap, Submodule.coeSubtype]
#align linear_map.quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff LinearMap.quotientInfEquivSupQuotient_symm_apply_eq_zero_iff

theorem quotientInfEquivSupQuotient_symm_apply_right (p p' : Submodule R M) {x : ↥(p ⊔ p')}
    (hx : (x : M) ∈ p') : (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x)
    = 0 :=
  quotientInfEquivSupQuotient_symm_apply_eq_zero_iff.2 hx
#align linear_map.quotient_inf_equiv_sup_quotient_symm_apply_right LinearMap.quotientInfEquivSupQuotient_symm_apply_right

end IsomorphismLaws

end LinearMap

/-! The third isomorphism theorem for modules. -/

namespace Submodule

variable (S T : Submodule R M) (h : S ≤ T)

/-- The map from the third isomorphism theorem for modules: `(M / S) / (T / S) → M / T`. -/
def quotientQuotientEquivQuotientAux (h : S ≤ T) : (M ⧸ S) ⧸ T.map S.mkQ →ₗ[R] M ⧸ T :=
  liftQ _ (mapQ S T LinearMap.id h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker, mkQ_apply, mapQ_apply]
      exact (Quotient.mk_eq_zero _).mpr hx)
#align submodule.quotient_quotient_equiv_quotient_aux Submodule.quotientQuotientEquivQuotientAux

@[simp]
theorem quotientQuotientEquivQuotientAux_mk (x : M ⧸ S) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk x) = mapQ S T LinearMap.id h x :=
  liftQ_apply _ _ _
#align submodule.quotient_quotient_equiv_quotient_aux_mk Submodule.quotientQuotientEquivQuotientAux_mk

-- @[simp] -- Porting note (#10618): simp can prove this
theorem quotientQuotientEquivQuotientAux_mk_mk (x : M) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk (Quotient.mk x)) = Quotient.mk x := by simp
#align submodule.quotient_quotient_equiv_quotient_aux_mk_mk Submodule.quotientQuotientEquivQuotientAux_mk_mk

/-- **Noether's third isomorphism theorem** for modules: `(M / S) / (T / S) ≃ M / T`. -/
def quotientQuotientEquivQuotient : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T :=
  { quotientQuotientEquivQuotientAux S T h with
    toFun := quotientQuotientEquivQuotientAux S T h
    invFun := mapQ _ _ (mkQ S) (le_comap_map _ _)
    left_inv := fun x => Quotient.inductionOn' x fun x => Quotient.inductionOn' x fun x => by simp
    right_inv := fun x => Quotient.inductionOn' x fun x => by simp }
#align submodule.quotient_quotient_equiv_quotient Submodule.quotientQuotientEquivQuotient

/-- Essentially the same equivalence as in the third isomorphism theorem,
except restated in terms of suprema/addition of submodules instead of `≤`. -/
def quotientQuotientEquivQuotientSup : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ S ⊔ T :=
  quotEquivOfEq _ _ (by rw [map_sup, mkQ_map_self, bot_sup_eq]) ≪≫ₗ
    quotientQuotientEquivQuotient S (S ⊔ T) le_sup_left

/-- Corollary of the third isomorphism theorem: `[S : T] [M : S] = [M : T]` -/
theorem card_quotient_mul_card_quotient (S T : Submodule R M) (hST : T ≤ S)
    [DecidablePred fun x => x ∈ S.map T.mkQ] [Fintype (M ⧸ S)] [Fintype (M ⧸ T)] :
    Fintype.card (S.map T.mkQ) * Fintype.card (M ⧸ S) = Fintype.card (M ⧸ T) := by
  rw [Submodule.card_eq_card_quotient_mul_card (map T.mkQ S),
    Fintype.card_eq.mpr ⟨(quotientQuotientEquivQuotient T S hST).toEquiv⟩]
#align submodule.card_quotient_mul_card_quotient Submodule.card_quotient_mul_card_quotient

end Submodule
