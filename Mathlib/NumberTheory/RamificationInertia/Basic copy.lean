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

theorem IsFiniteLength.ofFaithfullyFlat (h : IsFiniteLength S (S ⊗[R] M)) : IsFiniteLength R M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  exact h.imp IsNoetherian.ofFaithfullyFlat IsArtinian.ofFaithfullyFlat

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

variable {A B M : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] [AddCommGroup M] [Module A M]

theorem foo : (Module.length B (B ⊗[A] M)) =
    (Module.length A M) *
      (Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B))) := by
  set mA := IsLocalRing.maximalIdeal A
  set mB := mA.map (algebraMap A B)
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  by_cases h : IsFiniteLength A M; swap
  · have : ¬ IsFiniteLength B (B ⊗[A] M) := mt IsFiniteLength.ofFaithfullyFlat h
    rw [← Module.length_ne_top_iff, not_ne_iff] at h this
    rw [h, this, ENat.top_mul]
    rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff]
    exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    have key : ∀ k : Fin s.length.succ, (Order.height ((s k).baseChange B)) =
      k * (Module.length B (B ⧸ mB)) := by
      intro k
      induction k using Fin.induction
      case zero =>
        rw [Fin.val_zero, Nat.cast_zero, zero_mul, ← RelSeries.head, hs_bot,
          Submodule.baseChange_bot, Order.height_bot]
      case succ i hi =>
        have : (i.succ : ℕ) = (i.castSucc : ℕ).succ := rfl
        rw [this, Nat.cast_succ, add_one_mul, ← hi,
          ← Module.length_submodule, ← Module.length_submodule]
        let p := s i.castSucc
        let q := s i.succ
        let f : p →ₗ[A] q := Submodule.inclusion (s.lt_succ i).le
        have key : IsSimpleModule A (q ⧸ f.range) := by
          rw [Submodule.range_inclusion, ← covBy_iff_quot_is_simple (s.lt_succ i).le]
          exact s.step i
        obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
        rw [IsLocalRing.eq_maximalIdeal hm] at e
        let g := e.comp f.range.mkQ
        have hf : Function.Injective f := Submodule.inclusion_injective _
        have hg : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
        have hfg : Function.Exact f g := by
          refine (LinearMap.exact_iff (f := f) (g := g)).mpr ?_
          simp [g]
        let f' := TensorProduct.AlgebraTensorModule.lTensor B B f
        let g' := TensorProduct.AlgebraTensorModule.lTensor B B g
        have hf' : Function.Injective f' := by simpa [f'] using hf
        have hg' : Function.Surjective g' := by simpa [g'] using hg
        have hfg' : Function.Exact f' g' := by simpa [f', g'] using hfg
        have key := Module.length_eq_add_of_exact f' g' hf' hg' hfg'
        have h1 := p.toBaseChangeEquiv B
        have h2 := q.toBaseChangeEquiv B
        rw [← h1.length_eq, ← h2.length_eq]
        rw [key]
        congr
        have := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B mA
        exact this.toLinearEquiv.length_eq.symm
    specialize key (Fin.last s.length)
    rw [← RelSeries.last, hs_top, Submodule.baseChange_top, Fin.val_last] at key
    rw [Module.length_eq_height, key]

end flatBaseChange

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime]

noncomputable def ramificationIdx : ℕ :=
  letI Sq := Localization.AtPrime q
  (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat

theorem ramificationIdx_tower [r.LiesOver q]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    p.ramificationIdx r = p.ramificationIdx q * q.ramificationIdx r := by
  simp_rw [ramificationIdx, ← ENat.toNat_mul]
  congr
  set Sq := Localization.AtPrime q
  set Tr := Localization.AtPrime r
  have := foo (A := Sq) (B := Tr) (M := Sq ⧸ p.map (algebraMap R Sq))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map,
    ← IsScalarTower.algebraMap_eq] at this
  convert this
  let f := (Ideal.quotientEquivAlgOfEq Tr (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Tr (p.map (algebraMap R Sq)))
  exact f.toLinearEquiv.length_eq

end Ideal
