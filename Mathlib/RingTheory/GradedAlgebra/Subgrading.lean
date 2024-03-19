/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!
# Grading structure for sub-structures

Let `A` be a graded ring and `M` a graded module over `A`.

- If `R` is a homogeneous subring of `A`, then `R` is also a grade ring with `i`-th grading being
  `Rᵢ ∩ Aᵢ`
- If `N` is a homogeneous submodule of `M`, then `N` is also a graded module over `A` with `i`-th
  grading being `Nᵢ ∩ Mᵢ`
- If `N` is a homogeneous submodule of `M`, then `M ⧸ N` is also a graded module over `A` with
  `i`-th grading being `Mᵢ ⧸ (Nᵢ ∩ Mᵢ)`
-/

open DirectSum
open BigOperators

variable {ιA ιM σA σM R A M : Type*}
variable [SetLike σA A] [SetLike σM M]
variable [DecidableEq ιA] [DecidableEq ιM]
variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [AddCommGroup M] [AddSubgroupClass σM M] [Decomposition ℳ]
variable [Ring A] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [DecidableEq ιA] [AddMonoid ιA] [GradedRing 𝒜]

namespace HomogeneousSubring

variable {𝒜}
variable (A' : HomogeneousSubring 𝒜)

/--
If `A` is a graded ring and `A'` a homogeneous subring, then `A'` is also graded whose degree `i`
part is `Aᵢ ∩ A'`.
-/
def grading (i : ιA) : AddSubgroup A' where
  carrier := { a | (a : A) ∈ 𝒜 i }
  add_mem' := AddMemClass.add_mem
  zero_mem' := ZeroMemClass.zero_mem _
  neg_mem' := NegMemClass.neg_mem

variable [(i : ιA) → (x : 𝒜 i) → Decidable (x ≠ 0)] [∀ a : A, Decidable (a ∈ A')]

/--
Then `A' ≃ ⨁ᵢ Aᵢ ∩ A` by `a ↦ i ↦ aᵢ`. This is well-defined because `A'` is a homogeneoeus subring.
-/
protected def grading.decompose (a : A') : ⨁ i, A'.grading i :=
∑ i in (decompose 𝒜 a).support,
  .of _ (i : ιA) ⟨⟨decompose 𝒜 a i, A'.2 i a.2⟩, SetLike.coe_mem _⟩

lemma grading.decompose_zero : grading.decompose A' 0 = 0 := by
  delta grading.decompose
  convert Finset.sum_empty
  rw [ZeroMemClass.coe_zero, DirectSum.decompose_zero, DFinsupp.support_zero]

lemma grading.decompose_apply (a : A') (j : ιA) :
    (grading.decompose A' a j : A) = decompose 𝒜 a j := by
  delta grading.decompose
  simp only
  erw [DFinsupp.finset_sum_apply,  AddSubmonoidClass.coe_finset_sum,
        AddSubmonoidClass.coe_finset_sum]
  simp_rw [DirectSum.coe_of_apply]
  calc _
    _ = ∑ i in (decompose 𝒜 (a : A)).support,
          (if (i : ιA) = j then decompose 𝒜 (a : A) i else 0 : A) :=
        Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> rfl
  simp only [Finset.sum_ite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_eq_left_iff, not_not]
  aesop

lemma grading.decompose_add (a b : A') :
    grading.decompose A' (a + b) = grading.decompose A' a + grading.decompose A' b := by
  refine DFinsupp.ext fun i ↦ ?_
  ext
  simp only [decompose_apply, Subsemiring.coe_add, Subring.coe_toSubsemiring,
    DirectSum.decompose_add, add_apply, AddMemClass.coe_add, AddSubmonoid.coe_add]

lemma grading.decompose_leftInverse :
    Function.LeftInverse (DirectSum.coeAddMonoidHom A'.grading) (grading.decompose A') := by
  rintro ⟨a, ha⟩
  ext
  change A'.subtype _ = _
  simp only [grading.decompose, map_sum, coeAddMonoidHom_of, Subsemiring.coe_subtype]
  conv_rhs => rw [← sum_support_decompose 𝒜 a]

lemma grading.decompose_rightInverse :
    Function.RightInverse (DirectSum.coeAddMonoidHom A'.grading) (grading.decompose A') := by
  intro a
  refine DFinsupp.ext fun i ↦ ?_
  ext
  rw [grading.decompose_apply]
  induction' a using DirectSum.induction_on with j x x y hx hy
  · simp only [map_zero, ZeroMemClass.coe_zero, DirectSum.decompose_zero, zero_apply]
  · simp only [coeAddMonoidHom_of]
    erw [DirectSum.decompose_coe (ℳ := 𝒜) (i := j) ⟨x.1.1, x.2⟩]
    by_cases h : i = j
    · subst h; simp only [of_eq_same]
    · rw [of_eq_of_ne, of_eq_of_ne] <;> aesop
  · simp [map_add, DirectSum.add_apply, hx, hy]

instance : SetLike.GradedMonoid A'.grading where
  one_mem := (inferInstance : SetLike.GradedMonoid 𝒜).one_mem
  mul_mem _ _ _ _ h h' := (inferInstance : SetLike.GradedMonoid 𝒜).mul_mem h h'

instance : Decomposition A'.grading where
  decompose' := grading.decompose A'
  left_inv := grading.decompose_leftInverse A'
  right_inv := grading.decompose_rightInverse A'

instance gradedRing : GradedRing A'.grading where
  __ := inferInstanceAs <| SetLike.GradedMonoid A'.grading
  __ := inferInstanceAs <| Decomposition A'.grading

lemma grading.decompose_def (x : A') :
    DirectSum.decompose A'.grading x = HomogeneousSubring.grading.decompose A' x := rfl

section irrelevant_ideal

variable {ιA σA A : Type*} [SetLike σA A] [DecidableEq ιA]
variable {𝒜 : ιA → σA} [Ring A]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [DecidableEq ιA] [CanonicallyOrderedAddCommMonoid ιA] [GradedRing 𝒜]
variable [(i : ιA) → (x : 𝒜 i) → Decidable (x ≠ 0)]
variable (R : HomogeneousSubring 𝒜) [(a : A) → Decidable (a ∈ R)]

lemma irrelevant_eq  :
    (HomogeneousIdeal.irrelevant R.grading).toIdeal =
    Ideal.comap (R.toSubring.subtype : R →+* A) (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  classical
  ext x
  erw [HomogeneousIdeal.mem_irrelevant_iff, Ideal.mem_comap, HomogeneousIdeal.mem_irrelevant_iff,
    GradedRing.proj_apply, GradedRing.proj_apply, HomogeneousSubring.grading.decompose_def,
    Subtype.ext_iff, grading.decompose_apply]
  rfl

end irrelevant_ideal

end HomogeneousSubring

namespace HomogeneousSubmodule

instance : AddSubgroupClass (HomogeneousSubmodule A ℳ) M where
  add_mem {x} := x.toSubmodule.add_mem
  zero_mem {x} := x.toSubmodule.zero_mem
  neg_mem {x} := x.toSubmodule.neg_mem

variable {𝒜 ℳ}
variable (p : HomogeneousSubmodule A ℳ)

section submodule_grading

/--
If `A` is a graded ring and `M` a graded module over `A`. Let `p` a homogeneous submodule of `M`,
then `p` is a graded module over `A` as well whose degree `i` part is `Mᵢ ∩ p`.
-/
def grading (i : ιM) : AddSubgroup p where
  carrier := { x | (x : M) ∈ ℳ i }
  add_mem' := AddMemClass.add_mem
  zero_mem' := ZeroMemClass.zero_mem _
  neg_mem' := NegMemClass.neg_mem

variable [(i : ιM) → (x : ℳ i) → Decidable (x ≠ 0)] [∀ a : M, Decidable (a ∈ p)]


/--
`p ≃ ⨁ᵢ p ∩ Mᵢ` is defined by `x ↦ i ↦ xᵢ`. This is well-defined because `p` is homogeneous.
-/
protected def grading.decompose (a : p) : ⨁ i, p.grading i :=
∑ i in ((decompose ℳ a).support.filter fun i ↦ (decompose ℳ a i : M) ∈ p).attach,
  .of _ (i : ιM) ⟨⟨decompose ℳ a i, Finset.mem_filter.mp i.2 |>.2⟩, SetLike.coe_mem _⟩

lemma grading.decompose_zero : grading.decompose p 0 = 0 := by
  delta grading.decompose
  convert Finset.sum_empty
  ext ⟨i, hi⟩
  rw [Finset.mem_filter, DFinsupp.mem_support_iff, Submodule.coe_zero, DirectSum.decompose_zero,
    DirectSum.zero_apply] at hi
  exact hi.1 rfl |>.elim

lemma grading.decompose_apply (a : p) (j : ιM) :
    (grading.decompose p a j : M) = decompose ℳ a j := by
  delta grading.decompose
  simp only
  erw [DFinsupp.finset_sum_apply,  AddSubmonoidClass.coe_finset_sum,
        AddSubmonoidClass.coe_finset_sum]
  simp_rw [DirectSum.coe_of_apply]
  calc _
    _ = (∑ i in ((decompose ℳ (a : M)).support.filter
          fun i ↦ (decompose ℳ (a : M) i : M) ∈ p).attach,
          if (i : ιM) = j then decompose ℳ (a : M) i else 0 : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> rfl
  rw [← Finset.sum_filter]
  set S := _; change ∑ i in S, _ = _
  by_cases hj : (decompose ℳ (a : M) j : M) = 0
  · rw [hj]
    convert Finset.sum_empty
    ext ⟨i, hi⟩
    simp only [Finset.filter_congr_decidable, Finset.mem_filter, DFinsupp.mem_support_toFun, ne_eq,
      Finset.mem_attach, true_and, Finset.not_mem_empty, iff_false] at hi ⊢
    intro h
    exact hi.1 (Subtype.ext <| h.symm ▸ hj)
  have eq : S = {⟨j, by
    simp only [Finset.filter_congr_decidable, Finset.mem_filter, DFinsupp.mem_support_toFun, ne_eq]
    exact ⟨by contrapose! hj; exact Subtype.ext_iff.mp hj, p.is_homogeneous' _ a.2⟩⟩} := by aesop
  rw [eq, Finset.sum_singleton]

lemma grading.decompose_add (a b : p) :
    grading.decompose p (a + b) = grading.decompose p a + grading.decompose p b := by
  refine DFinsupp.ext fun i ↦ ?_
  ext
  simp only [decompose_apply, Subsemiring.coe_add, Subring.coe_toSubsemiring,
    DirectSum.decompose_add, add_apply, AddMemClass.coe_add, AddSubmonoid.coe_add]

lemma grading.decompose_leftInverse :
    Function.LeftInverse (DirectSum.coeAddMonoidHom p.grading) (grading.decompose p) := by
  rintro ⟨a, ha⟩
  ext
  change p.subtype _ = _
  simp only [grading.decompose, map_sum, coeAddMonoidHom_of, Subsemiring.coe_subtype]
  conv_rhs => rw [← sum_support_decompose ℳ a]
  apply Finset.sum_bij (i := fun i _ ↦ i.1)
  · rintro ⟨i, hi⟩ -
    simp only [Finset.mem_filter, DFinsupp.mem_support_toFun, ne_eq] at hi ⊢
    exact hi.1
  · rintro ⟨i₁, hi₁⟩ - ⟨i₂, hi₂⟩ - (h : i₁ = i₂)
    subst h
    simp only [Finset.mem_filter, DFinsupp.mem_support_toFun, ne_eq] at hi₁ ⊢
  · intro i hi
    refine ⟨⟨i, ?_⟩, by simp, rfl⟩
    simp only [Finset.mem_filter, DFinsupp.mem_support_toFun, ne_eq] at hi ⊢
    exact ⟨hi, p.is_homogeneous' _ ha⟩
  · rintro ⟨i, hi⟩ -
    simp only [Finset.mem_filter, DFinsupp.mem_support_toFun, ne_eq, Submodule.coeSubtype] at hi ⊢

lemma grading.decompose_rightInverse :
    Function.RightInverse (DirectSum.coeAddMonoidHom p.grading) (grading.decompose p) := by
  intro a
  refine DFinsupp.ext fun i ↦ ?_
  ext
  rw [grading.decompose_apply]
  induction' a using DirectSum.induction_on with j x x y hx hy
  · simp only [map_zero, ZeroMemClass.coe_zero, DirectSum.decompose_zero, zero_apply]
  · simp only [coeAddMonoidHom_of]
    erw [DirectSum.decompose_coe (ℳ := ℳ) (i := j) ⟨x.1.1, x.2⟩]
    by_cases h : i = j
    · subst h; simp only [of_eq_same]
    · rw [of_eq_of_ne, of_eq_of_ne] <;> aesop
  · simp [map_add, DirectSum.add_apply, hx, hy]

instance decomposition : Decomposition p.grading where
  decompose' := grading.decompose p
  left_inv := grading.decompose_leftInverse p
  right_inv := grading.decompose_rightInverse p

variable [VAdd ιA ιM] [SetLike.GradedSMul 𝒜 ℳ]
instance gradedSMul : SetLike.GradedSMul 𝒜 p.grading where
  smul_mem _ _ _ _ ha hm := (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem ha hm

end submodule_grading

section quotient_grading

variable {ℳ : ιM → AddSubgroup M} [Decomposition ℳ] [VAdd ιA ιM] [SetLike.GradedSMul 𝒜 ℳ]
variable (p : HomogeneousSubmodule A ℳ)

open Classical

/--
The addive group homomorphism from `Mᵢ ⧸ p ∩ Mᵢ` to `M ⧸ p`
-/
@[simps!]
def quotientGradingEmb (i : ιM) :
    ℳ i ⧸ (AddSubgroup.addSubgroupOf p.toAddSubgroup _) →+
    M ⧸ p.toSubmodule :=
  QuotientAddGroup.map _ _ (ℳ i).subtype <| le_refl _

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
    { toFun := fun m ↦ .of _ i ⟨p.toSubmodule.mkQ m.1, ⟨Quotient.mk'' m, by
        rw [quotientGradingEmb]
        erw [QuotientAddGroup.map_mk']⟩⟩
      map_zero' := DFinsupp.ext fun j ↦ by
        simp only [ZeroMemClass.coe_zero, map_zero, zero_apply]
        ext
        by_cases h : i = j
        · subst h
          simp only [of_eq_same, ZeroMemClass.coe_zero]
        · rw [of_eq_of_ne]; exact h
      map_add' := by
        rintro a b
        simp only [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, map_add,
          Submodule.mkQ_apply]
        refine DFinsupp.ext fun j ↦ ?_
        ext
        by_cases h : i = j
        · subst h
          simp only [of_eq_same, add_apply, AddSubmonoid.mk_add_mk]
        · rw [of_eq_of_ne, DirectSum.add_apply, of_eq_of_ne, of_eq_of_ne, add_zero] <;> exact h
         })
  (DirectSum.decomposeAddEquiv ℳ).toAddMonoidHom

lemma quotientGrading.le_decomposeAux_ker :
    p.toSubmodule.toAddSubgroup ≤ (quotientGrading.decomposeAux p).ker := fun x hx ↦
  show DFinsupp.sumAddHom _ (decompose ℳ x) = 0 by
  have eq0 :
      decompose ℳ x =
      ∑ i in (decompose ℳ x).support,
        (DFinsupp.single i ⟨decompose ℳ x i, SetLike.coe_mem _⟩) := by
    refine DFinsupp.ext fun i ↦ ?_
    ext
    simp only [Subtype.coe_eta, DFinsupp.finset_sum_apply, DFinsupp.single_apply,
      Finset.sum_dite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not, SetLike.coe_eq_coe]
    split_ifs with h
    · exact h
    · rfl
  rw [eq0, map_sum]
  simp_rw [DFinsupp.sumAddHom_single]
  apply Finset.sum_eq_zero
  intros i _
  simp only [Submodule.mkQ_apply, Subtype.coe_eta, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  refine DFinsupp.ext fun j ↦ Subtype.ext <| show _ = 0 from ?_
  by_cases h : i = j
  · subst h; simp only [of_eq_same, Submodule.Quotient.mk_eq_zero, mem_iff]; exact p.2 _ hx
  · rw [of_eq_of_ne, ZeroMemClass.coe_zero]; exact h

/--
`M ⧸ p ≃ ⨁ᵢ Mᵢ ⧸ Mᵢ ∩ p` is given by `[x] ↦ i ↦ [xᵢ]`. This is well-defined because `p` is
homogeneous.
-/
protected def quotientGrading.decompose : M ⧸ p.toSubmodule →+ ⨁ i, p.quotientGrading i :=
QuotientAddGroup.lift _ (quotientGrading.decomposeAux p) (quotientGrading.le_decomposeAux_ker p)

lemma quotientGrading.decompose_apply_mkQ_of_mem (i : ιM) (m : M) (hm : m ∈ ℳ i) :
    (quotientGrading.decompose p (p.toSubmodule.mkQ m) i : M ⧸ p.toSubmodule) =
    p.toSubmodule.mkQ m := by
  simp only [quotientGrading.decompose, Submodule.mkQ_apply]
  erw [QuotientAddGroup.lift_mk']
  simp only [decomposeAux, Submodule.mkQ_apply, DFinsupp.liftAddHom_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  have eq0 :
      decompose ℳ m =
      ∑ i in (decompose ℳ m).support,
        (DFinsupp.single i ⟨decompose ℳ m i, SetLike.coe_mem _⟩) := by
    refine DFinsupp.ext fun i ↦ ?_
    ext
    simp only [Subtype.coe_eta, DFinsupp.finset_sum_apply, DFinsupp.single_apply,
      Finset.sum_dite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not, SetLike.coe_eq_coe]
    split_ifs with h
    · exact h
    · rfl
  erw [eq0, map_sum]
  simp only [Subtype.coe_eta, DFinsupp.sumAddHom_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [DFinsupp.finset_sum_apply]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℳ m]
  change (p.quotientGrading i).subtype _ = p.toSubmodule.mkQ _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intros j hj
  simp only [AddSubgroup.coeSubtype, Submodule.mkQ_apply]
  by_cases h : i = j
  · subst h
    simp only [of_eq_same]
  · rw [of_eq_of_ne, decompose_of_mem_ne (hx := hm) (hij := h)]
    · rfl
    · exact Ne.symm h

lemma quotientGrading.decompose_apply_mkQ_of_ne (i j : ιM) (m : M) (hm : m ∈ ℳ i) (h : i ≠ j) :
    (quotientGrading.decompose p (p.toSubmodule.mkQ m) j : M ⧸ p.toSubmodule) =
    0 := by
  simp only [quotientGrading.decompose, Submodule.mkQ_apply]
  erw [QuotientAddGroup.lift_mk']
  simp only [decomposeAux, Submodule.mkQ_apply, DFinsupp.liftAddHom_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  have eq0 :
      decompose ℳ m =
      ∑ i in (decompose ℳ m).support,
        (DFinsupp.single i ⟨decompose ℳ m i, SetLike.coe_mem _⟩) := by
    refine DFinsupp.ext fun i ↦ ?_
    ext
    simp only [Subtype.coe_eta, DFinsupp.finset_sum_apply, DFinsupp.single_apply,
      Finset.sum_dite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not, SetLike.coe_eq_coe]
    split_ifs with h
    · exact h
    · rfl
  erw [eq0, map_sum]
  simp only [Subtype.coe_eta, DFinsupp.sumAddHom_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [DFinsupp.finset_sum_apply]
  norm_cast
  apply Finset.sum_eq_zero
  intro k hk
  ext
  by_cases h : j = k
  · subst h
    simp only [of_eq_same, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero, mem_iff]
    rw [decompose_of_mem_ne (hx := hm) (hij := h)]
    exact p.toSubmodule.zero_mem
  · rw [of_eq_of_ne]; exact Ne.symm h

lemma quotientGrading.decompose_leftInverse :
    Function.LeftInverse (DirectSum.coeAddMonoidHom p.quotientGrading)
      (quotientGrading.decompose p) := by
  intro x
  induction' x using Quotient.inductionOn' with x
  simp only [quotientGrading.decompose, decomposeAux, Submodule.mkQ_apply,
    DFinsupp.liftAddHom_apply]
  erw [QuotientAddGroup.lift_mk']
  change DirectSum.coeAddMonoidHom _ (DFinsupp.sumAddHom _ (decompose ℳ x)) = _
  have eq0 :
      decompose ℳ x =
      ∑ i in (decompose ℳ x).support,
        (DFinsupp.single i ⟨decompose ℳ x i, SetLike.coe_mem _⟩) := by
    refine DFinsupp.ext fun i ↦ ?_
    ext
    simp only [Subtype.coe_eta, DFinsupp.finset_sum_apply, DFinsupp.single_apply,
      Finset.sum_dite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not, SetLike.coe_eq_coe]
    split_ifs with h
    · exact h
    · rfl
  rw [eq0, map_sum]
  simp_rw [DFinsupp.sumAddHom_single]
  rw [map_sum]
  simp only [Subtype.coe_eta, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeAddMonoidHom_of,
    Submodule.Quotient.mk''_eq_mk]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℳ x]
  change _ = p.toSubmodule.mkQ _
  rw [map_sum]
  rfl

lemma quotientGrading.decompose_rightInverse :
    Function.RightInverse (DirectSum.coeAddMonoidHom p.quotientGrading)
      (quotientGrading.decompose p) := by
  intro x
  refine DFinsupp.ext fun i ↦ ?_
  induction' x using DirectSum.induction_on with j x x y hx hy
  · simp  only [map_zero, zero_apply]
  · rcases x with ⟨x, hx⟩
    induction' x using Quotient.inductionOn' with x
    obtain ⟨y, hy⟩ := hx
    induction' y using Quotient.inductionOn' with y
    erw [quotientGradingEmb, QuotientAddGroup.map_mk'] at hy
    cases' y with y hy'
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hy
    simp_rw [← hy]
    simp only [coeAddMonoidHom_of]
    by_cases h : i = j
    · ext
      subst h
      simp only [of_eq_same]
      exact quotientGrading.decompose_apply_mkQ_of_mem p i y hy'
    · ext
      rw [of_eq_of_ne, ZeroMemClass.coe_zero]
      swap
      · exact Ne.symm h
      exact quotientGrading.decompose_apply_mkQ_of_ne p j i y hy' (Ne.symm h)
  · simp [hx, hy]

instance quotientDecomposition : DirectSum.Decomposition p.quotientGrading where
  decompose' := quotientGrading.decompose p
  left_inv := quotientGrading.decompose_leftInverse p
  right_inv := quotientGrading.decompose_rightInverse p

instance quotientGradedSMul : SetLike.GradedSMul 𝒜 p.quotientGrading where
  smul_mem := by
    intro i j a m ha hm
    obtain ⟨x, rfl⟩ := hm
    induction' x using Quotient.inductionOn' with x
    cases' x with x hx
    erw [quotientGradingEmb, QuotientAddGroup.map_mk', AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      quotientGrading]
    refine ⟨Quotient.mk'' ⟨a • x, (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem ha hx⟩, ?_⟩
    erw [quotientGradingEmb, QuotientAddGroup.map_mk', AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rfl

end quotient_grading

end HomogeneousSubmodule
