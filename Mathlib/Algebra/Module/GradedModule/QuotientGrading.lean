/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.Algebra.Module.GradedModule.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient of Graded Module by a Homogeneous Submodule

-/

open SetLike DirectSum

variable {ιA ιM σA σM A M : Type*}

variable [Ring A] [AddCommGroup M] [Module A M]

variable {𝒜 : ιA → σA} {ℳ : ιM → σM}
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubgroupClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubgroupClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

namespace HomogeneousSubmodule

variable (p : HomogeneousSubmodule 𝒜 ℳ)

/--
The addive group homomorphism from `Mᵢ ⧸ p ∩ Mᵢ` to `M ⧸ p`
-/
@[simps!]
def quotientGradingEmb (i : ιM) :
    (ℳ i : AddSubgroup M) ⧸ (AddSubgroup.addSubgroupOf p.toAddSubgroup _) →+
    M ⧸ p.toSubmodule :=
  QuotientAddGroup.map _ _ (ℳ i : AddSubgroup M).subtype <| le_refl _

/--
`M ⧸ p` is a graded module over `A` whose `i`-th degree part is `Mᵢ ⧸ p ∩ Mᵢ`
-/
def quotientGrading (i : ιM) : AddSubgroup (M ⧸ p.toSubmodule) :=
  (p.quotientGradingEmb i).range

/--
`M ⧸ p ≃ ⨁ᵢ Mᵢ ⧸ Mᵢ ∩ p` is given by `[x] ↦ i ↦ [xᵢ]`. This is well-defined because `p` is
homogeneous.
-/
def quotientGrading.decomposeAux : M →+ ⨁ i, p.quotientGrading i :=
AddMonoidHom.comp
  (DFinsupp.liftAddHom fun i ↦
    { toFun := fun m ↦ .of _ i
        ⟨p.toSubmodule.mkQ m.1, ⟨QuotientAddGroup.mk' _ m, by erw [QuotientAddGroup.map_mk']⟩⟩
      map_zero' := DFinsupp.ext fun j ↦ by
        simp only [ZeroMemClass.coe_zero, map_zero, zero_apply]
        ext
        by_cases h : i = j
        · subst h
          simp only [of_eq_same, ZeroMemClass.coe_zero]
        · rw [of_eq_of_ne]; exact h
      map_add' := by
        rintro a b
        simp only [AddSubgroup.coe_add, map_add, Submodule.mkQ_apply]
        refine DFinsupp.ext fun j ↦ ?_
        ext
        by_cases h : i = j
        · subst h
          simp only [of_eq_same, add_apply, AddSubmonoid.mk_add_mk]
          rfl
        · rw [of_eq_of_ne, DirectSum.add_apply, of_eq_of_ne, of_eq_of_ne, add_zero] <;> exact h
         })
  (DirectSum.decomposeAddEquiv ℳ).toAddMonoidHom

lemma quotientGrading.le_decomposeAux_ker :
    p.toSubmodule.toAddSubgroup ≤ (quotientGrading.decomposeAux p).ker := fun x hx ↦
  show DFinsupp.sumAddHom _ (decompose ℳ x) = 0 by
  classical
  rw [show decompose ℳ x =
      ∑ i in (decompose ℳ x).support,
        (DFinsupp.single i ⟨decompose ℳ x i, SetLike.coe_mem _⟩) from
      DFinsupp.ext fun i ↦ by aesop, map_sum]
  simp_rw [DFinsupp.sumAddHom_single]
  refine Finset.sum_eq_zero fun i _ ↦ DFinsupp.ext fun j ↦ Subtype.ext <| show _ = 0 from ?_
  by_cases h : i = j
  · subst h; simpa [of_eq_same, Submodule.Quotient.mk_eq_zero, mem_iff] using p.2 _ hx
  · simp [of_eq_of_ne (h := h)]

/--
`M ⧸ p ≃ ⨁ᵢ Mᵢ ⧸ Mᵢ ∩ p` is given by `[x] ↦ i ↦ [xᵢ]`. This is well-defined because `p` is
homogeneous.
-/
def quotientGradingDecompose : M ⧸ p.toSubmodule →+ ⨁ i, p.quotientGrading i :=
QuotientAddGroup.lift _ (quotientGrading.decomposeAux p) (quotientGrading.le_decomposeAux_ker p)

lemma quotientGradingDecompose_apply_mkQ_of_mem (i : ιM) (m : M) (hm : m ∈ ℳ i) :
    p.quotientGradingDecompose (p.toSubmodule.mkQ m) i =
    p.toSubmodule.mkQ m := by
  classical
  simp only [quotientGradingDecompose, Submodule.mkQ_apply]
  erw [QuotientAddGroup.lift_mk']
  simp only [quotientGrading.decomposeAux, Submodule.mkQ_apply, DFinsupp.liftAddHom_apply,
    AddMonoidHom.coe_comp, Function.comp_apply]
  erw [show decompose ℳ m =
      ∑ i in (decompose ℳ m).support,
        (DFinsupp.single i ⟨decompose ℳ m i, SetLike.coe_mem _⟩) from
      DFinsupp.ext fun i ↦ by aesop, map_sum]

  simp only [Subtype.coe_eta, DFinsupp.sumAddHom_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [DFinsupp.finset_sum_apply]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℳ m]
  change (p.quotientGrading i).subtype _ = p.toSubmodule.mkQ _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  simp only [AddSubgroup.coeSubtype, Submodule.mkQ_apply]
  by_cases h : i = j
  · subst h; simp only [of_eq_same]
  · rw [of_eq_of_ne (h := Ne.symm h), decompose_of_mem_ne (hx := hm) (hij := h),
      ZeroMemClass.coe_zero]; rfl

lemma quotientGradingDecompose_apply_mkQ_of_ne (i j : ιM) (m : M) (hm : m ∈ ℳ i) (h : i ≠ j) :
    p.quotientGradingDecompose (p.toSubmodule.mkQ m) j = 0 := by
  classical
  simp only [quotientGradingDecompose, Submodule.mkQ_apply]
  erw [QuotientAddGroup.lift_mk']
  simp only [quotientGrading.decomposeAux, Submodule.mkQ_apply, DFinsupp.liftAddHom_apply,
    AddMonoidHom.coe_comp, Function.comp_apply]
  erw [show decompose ℳ m =
      ∑ i in (decompose ℳ m).support,
        (DFinsupp.single i ⟨decompose ℳ m i, SetLike.coe_mem _⟩) from
      DFinsupp.ext fun i ↦ by aesop, map_sum]
  simp only [Subtype.coe_eta, DFinsupp.sumAddHom_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [DFinsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  ext
  by_cases h : j = k
  · subst h
    simp only [of_eq_same, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero, mem_iff]
    rw [decompose_of_mem_ne (hx := hm) (hij := h)]
    exact p.toSubmodule.zero_mem
  · rw [of_eq_of_ne]; exact Ne.symm h

lemma quotientGradingDecompose_leftInverse :
    Function.LeftInverse (DirectSum.coeAddMonoidHom p.quotientGrading)
      p.quotientGradingDecompose := by
  classical
  intro x
  induction x using Quotient.inductionOn' with | h x => ?_
  simp only [quotientGradingDecompose, quotientGrading.decomposeAux, Submodule.mkQ_apply,
    DFinsupp.liftAddHom_apply]
  erw [QuotientAddGroup.lift_mk']
  change DirectSum.coeAddMonoidHom _ (DFinsupp.sumAddHom _ (decompose ℳ x)) = _
  erw [show decompose ℳ x =
      ∑ i in (decompose ℳ x).support,
        (DFinsupp.single i ⟨decompose ℳ x i, SetLike.coe_mem _⟩) from
      DFinsupp.ext fun i ↦ by aesop, map_sum]
  simp_rw [DFinsupp.sumAddHom_single]
  rw [map_sum]
  simp only [Subtype.coe_eta, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeAddMonoidHom_of,
    Submodule.Quotient.mk''_eq_mk]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℳ x]
  change _ = p.toSubmodule.mkQ _
  rw [map_sum]
  rfl

lemma quotientGradingDecompose_rightInverse :
    Function.RightInverse (DirectSum.coeAddMonoidHom p.quotientGrading)
      p.quotientGradingDecompose :=
  fun x ↦ DFinsupp.ext fun i ↦ by
  induction x using DirectSum.induction_on with
  | H_zero => simp
  | H_basic j x =>
    rcases x with ⟨x, hx⟩
    induction x using Quotient.inductionOn' with | h x =>
    obtain ⟨y, hy⟩ := hx
    induction y using Quotient.inductionOn' with | h y =>
    erw [quotientGradingEmb, QuotientAddGroup.map_mk'] at hy
    rcases y with ⟨y, hy'⟩
    simp only [AddSubgroup.coeSubtype] at hy
    simp_rw [← hy]
    simp only [coeAddMonoidHom_of]
    by_cases h : i = j
    · ext
      subst h
      simp only [of_eq_same]
      exact quotientGradingDecompose_apply_mkQ_of_mem p i y hy'
    · ext
      rw [of_eq_of_ne (h := Ne.symm h), ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero]
      exact quotientGradingDecompose_apply_mkQ_of_ne p j i y hy' (Ne.symm h)
  | H_plus _ _ h h' => simp [h, h']

instance quotientDecomposition : DirectSum.Decomposition p.quotientGrading where
  decompose' := p.quotientGradingDecompose
  left_inv := p.quotientGradingDecompose_leftInverse
  right_inv := p.quotientGradingDecompose_rightInverse

instance quotientGradedSMul : SetLike.GradedSMul 𝒜 p.quotientGrading where
  smul_mem := by
    intro i j a m ha hm
    obtain ⟨x, rfl⟩ := hm
    induction x using Quotient.inductionOn' with | h x => ?_
    rcases x with ⟨x, hx⟩
    exact ⟨Quotient.mk'' ⟨a • x, (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem ha hx⟩, rfl⟩

end HomogeneousSubmodule
