/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Localization

/-!
# Ramification index

-/

@[expose] public section

section temp

open TensorProduct

-- PRed
theorem Submodule.baseChange_mono {R M : Type*} (A : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    {N N' : Submodule R M} (h : N ≤ N') :
    N.baseChange A ≤ N'.baseChange A := by
  rw [Submodule.baseChange, LinearMap.baseChange, ← Submodule.subtype_comp_inclusion N N' h,
    ← LinearMap.id_comp LinearMap.id, TensorProduct.AlgebraTensorModule.map_comp]
  apply LinearMap.range_comp_le_range

-- PRed
@[simp]
theorem Submodule.baseChange_le_iff {R M A : Type*} [CommRing R]
    [Ring A] [Algebra R A] [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} :
    N.baseChange A ≤ N'.baseChange A ↔ N ≤ N' := by
  refine ⟨fun h ↦ ?_, Submodule.baseChange_mono A⟩
  rwa [← N'.ker_mkQ, LinearMap.le_ker_iff_comp_subtype_eq_zero,
    Module.FaithfullyFlat.zero_iff_lTensor_zero R A (N'.mkQ.comp N.subtype),
    LinearMap.lTensor_comp, ← LinearMap.range_le_ker_iff, lTensor_mkQ, ← restrictScalars_le R]

-- PRed
theorem Submodule.baseChange_inj {R M A : Type*} [CommRing R]
    [Ring A] [Algebra R A] [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} :
    N.baseChange A = N'.baseChange A ↔ N = N' := by
  simp [le_antisymm_iff]

-- PRed
theorem Submodule.baseChange_injective {R M A : Type*} [CommRing R]
    [Ring A] [Algebra R A] [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} (h : N.baseChange A = N'.baseChange A) :
    N = N' :=
  Submodule.baseChange_inj.mp h

variable (R M S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  [AddCommGroup M] [Module R M]

-- PRed
/-- `Submodule.baseChange` as an order embedding. -/
def Submodule.baseChangeOrderEmbedding [Module.FaithfullyFlat R S] :
    Submodule R M ↪o Submodule S (S ⊗[R] M) where
  toFun := Submodule.baseChange S
  inj' _ _ := Submodule.baseChange_injective
  map_rel_iff' := Submodule.baseChange_le_iff

variable {R M S}

-- PRed
theorem IsNoetherian.ofFaithfullyFlat (h : IsNoetherian S (S ⊗[R] M)) : IsNoetherian R M := by
  rw [isNoetherian_iff'] at h ⊢
  exact OrderEmbedding.wellFoundedGT (Submodule.baseChangeOrderEmbedding R M S)

-- PRed
theorem IsArtinian.ofFaithfullyFlat (h : IsArtinian S (S ⊗[R] M)) : IsArtinian R M := by
  rw [isArtinian_iff] at h ⊢
  exact OrderEmbedding.wellFounded (Submodule.baseChangeOrderEmbedding R M S) h

end temp

section flatBaseChange

open TensorProduct

-- PRed
theorem Submodule.toBaseChange_injective {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module.Flat R A] (p : Submodule R M) :
    Function.Injective (p.toBaseChange A) := by
  refine (LinearMap.injective_rangeRestrict_iff (LinearMap.baseChange A p.subtype)).mpr ?_
  rw [LinearMap.baseChange_eq_ltensor]
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact injective_subtype p

-- PRed
@[simps!]
noncomputable def Submodule.toBaseChangeEquiv
    {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module.Flat R A] (p : Submodule R M) :
    A ⊗[R] ↥p ≃ₗ[A] baseChange A p :=
  LinearEquiv.ofBijective (p.toBaseChange A)
    ⟨p.toBaseChange_injective A, p.toBaseChange_surjective A⟩

-- PRed
theorem IsLocalRing.map_maximalIdeal_le {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (IsLocalRing.maximalIdeal A).map f ≤ IsLocalRing.maximalIdeal B := by
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]

-- PRed
theorem Ideal.IsMaximal.lt_top {R : Type*} [CommRing R] {I : Ideal R} (hI : IsMaximal I) :
    I < ⊤ :=
  lt_top_iff_ne_top.mpr hI.ne_top

-- PRed
theorem IsLocalRing.map_maximalIdeal_lt_top
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (IsLocalRing.maximalIdeal A).map f < ⊤ :=
  (IsLocalRing.map_maximalIdeal_le f).trans_lt (IsLocalRing.maximalIdeal.isMaximal B).lt_top

-- PRed
theorem length_of_isScalarTower_of_surjective {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : Function.Surjective (algebraMap A B))
    (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] :
    Module.length A M = Module.length B M := by
  have : RingHomSurjective (algebraMap A B) := ⟨h⟩
  let f : M →ₛₗ[algebraMap A B] M :=
  { __ := AddMonoidHom.id M
    map_smul' := by simp }
  let e := Submodule.orderIsoMapComapOfBijective f Function.bijective_id
  rw [Module.length, Module.length, WithBot.unbot_eq_iff, WithBot.coe_unbot] -- better lemma
  exact Order.krullDim_eq_of_orderIso e

variable {A B M : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] [AddCommGroup M] [Module A M]

variable (B) in
open IsLocalRing LinearMap Module Submodule TensorProduct.AlgebraTensorModule in
theorem CovBy.length_baseChange {p q : Submodule A M} (h : p ⋖ q) :
    length B (q.baseChange B) =
      length B (p.baseChange B) + length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
  rw [← (p.toBaseChangeEquiv B).length_eq, ← (q.toBaseChangeEquiv B).length_eq]
  let f : p →ₗ[A] q := inclusion h.le
  have key : IsSimpleModule A (q ⧸ f.range) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  rw [eq_maximalIdeal hm] at e
  let g := e.comp f.range.mkQ
  have : Function.Injective f := inclusion_injective _
  have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
  have : Function.Exact f g := exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
  rw [length_eq_add_of_exact (lTensor B B f) (lTensor B B g) (by simpa) (by simpa) (by simpa),
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toLinearEquiv.length_eq]

variable (A B M) in
open IsLocalRing Module Submodule in
theorem length_baseChange :
    length B (B ⊗[A] M) = length A M * length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
  by_cases h : IsFiniteLength A M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, length B ((s k).baseChange B) =
        k * length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top, baseChange_top, length_top]
    intro k
    induction k using Fin.induction
    case pos.zero => rw [← RelSeries.head, hs_bot, baseChange_bot]; simp
    case pos.succ i hi => simpa [hi, add_one_mul] using (s.step i).length_baseChange B
  · have : ¬ IsFiniteLength B (B ⊗[A] M) := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp IsNoetherian.ofFaithfullyFlat IsArtinian.ofFaithfullyFlat
    rw [← length_ne_top_iff, not_ne_iff] at h this
    rw [h, this, ENat.top_mul]
    rw [← pos_iff_ne_zero, length_pos_iff, Quotient.nontrivial_iff]
    exact (map_maximalIdeal_lt_top (algebraMap A B)).ne

variable [Module B M] [IsScalarTower A B M]

set_option backward.isDefEq.respectTransparency false in
variable (A) in
open IsLocalRing LinearMap Module Submodule TensorProduct.AlgebraTensorModule in
theorem CovBy.length_restrictScalars {p q : Submodule B M} (h : p ⋖ q) :
    length A q = Module.length A p + (Module.rank (ResidueField A) (ResidueField B)).toENat := by
  have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
  let f : p →ₗ[B] q := inclusion h.le
  have key : IsSimpleModule B (q ⧸ f.range) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  rw [eq_maximalIdeal hm] at e
  let g : q →ₗ[B] ResidueField B := e.comp f.range.mkQ
  have : Function.Injective f := inclusion_injective _
  have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
  have : Function.Exact f g := exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
  rw [length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A)
    (by simpa) (by simpa) (by simpa), length_of_isScalarTower_of_surjective (A := A)
    (B := ResidueField A) (M := ResidueField B) residue_surjective, Module.length_eq_rank]

variable (A B M) in
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing Module Submodule in
theorem length_restrictScalars :
    length A M = length B M * (Module.rank (ResidueField A) (ResidueField B)).toENat := by
  have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
  by_cases h : IsFiniteLength B M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, length A (s k) = k * (Module.rank (ResidueField A) (ResidueField B)).toENat by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact length_top.symm
    intro k
    induction k using Fin.induction
    case pos.zero => rw [← RelSeries.head, hs_bot]; simp
    case pos.succ i hi => simpa [hi, add_one_mul] using (s.step i).length_restrictScalars A
  · have : ¬ IsFiniteLength A M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
    rw [← length_ne_top_iff, not_ne_iff] at h this
    rw [h, this, ENat.top_mul]
    rw [← pos_iff_ne_zero, pos_iff_ne_zero, ne_eq, Cardinal.toENat_eq_zero]
    exact Module.rank_pos_of_free.ne'

end flatBaseChange

namespace Ideal

open Classical in
noncomputable def ramificationIdx {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat
  else 0

noncomputable def ramificationIdx_def {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    p.ramificationIdx q = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat :=
  dif_pos _

noncomputable def ramificationIdx_eq_zero {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) (hq : ¬ q.IsPrime) :
    p.ramificationIdx q = 0 :=
  dif_neg hq

theorem ramificationIdx_tower {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime] [r.LiesOver q]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    p.ramificationIdx r = p.ramificationIdx q * q.ramificationIdx r := by
  simp_rw [ramificationIdx_def, ← ENat.toNat_mul]
  congr
  set Sq := Localization.AtPrime q
  set Tr := Localization.AtPrime r
  have := length_baseChange (A := Sq) (B := Tr) (M := Sq ⧸ p.map (algebraMap R Sq))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map,
    ← IsScalarTower.algebraMap_eq] at this
  convert this
  let f := (Ideal.quotientEquivAlgOfEq Tr (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Tr (p.map (algebraMap R Sq)))
  exact f.toLinearEquiv.length_eq

theorem ramificationIdx_tower' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T) [r.LiesOver q] [Module.Flat S T] :
    p.ramificationIdx r = p.ramificationIdx q * q.ramificationIdx r := by
  by_cases hr : r.IsPrime
  · rw [Ideal.over_def r q]
    apply ramificationIdx_tower
  · rw [ramificationIdx_eq_zero p r hr, ramificationIdx_eq_zero q r hr, mul_zero]

open Module TensorProduct in
theorem sum_ramification_inertia
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] : False := by
  let F := S ⊗[R] p.ResidueField
  let q : Ideal S := sorry
  have : q.IsPrime := sorry
  have : q.LiesOver p := sorry
  let Sq := Localization.AtPrime q
  let A := Sq ⧸ p.map (algebraMap R Sq)
  let e := (length Sq A).toNat
  have := length_restrictScalars (Localization.AtPrime p) (Localization.AtPrime q) A -- e * f
  sorry

end Ideal
