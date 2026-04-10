/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
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
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.SurjectiveOnStalks
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Ramification index

-/

@[expose] public section

section artinian

open Submodule

-- PRed
theorem MaximalSpectrum.nilradical_pow_eq_iInf (R : Type*) [CommRing R] [IsArtinianRing R] (n : ℕ) :
    nilradical R ^ n = iInf fun I : MaximalSpectrum R ↦ I.1 ^ n := by
  haveI h0 {I J : MaximalSpectrum R} (h : I ≠ J) : IsCoprime I.1 J.1 :=
      Ideal.isCoprime_iff_sup_eq.mpr <| I.2.coprime_of_ne J.2 <| mt MaximalSpectrum.ext h
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  rw [← iInf_univ, ← Finset.coe_univ, PrimeSpectrum.nilradical_eq_iInf]
  simp only [Finset.mem_coe]
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime fun _ _ _ _ h ↦ .pow (h0 h),
    Finset.prod_pow, Ideal.prod_eq_iInf_of_pairwise_isCoprime fun _ _ _ _ ↦ h0]
  simp [Finset.mem_univ, iInf, IsArtinianRing.primeSpectrum_asIdeal_range_eq]

-- PRed
@[simps!]
noncomputable def IsArtinainRing.quotNilradicalPowEquivPi
    (R : Type*) [CommRing R] [IsArtinianRing R] (n : ℕ) :
    (R ⧸ nilradical R ^ n) ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal ^ n :=
  haveI h0 {I J : MaximalSpectrum R} (h : I ≠ J) : IsCoprime I.1 J.1 :=
      Ideal.isCoprime_iff_sup_eq.mpr <| I.2.coprime_of_ne J.2 <| mt MaximalSpectrum.ext h
  haveI h1 : nilradical R ^ n = ⨅ I : MaximalSpectrum R, I.1 ^ n := by
    exact MaximalSpectrum.nilradical_pow_eq_iInf R n
  (Ideal.quotientEquivAlgOfEq R h1).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I J h ↦ .pow (h0 h)
      commutes' _ := rfl}

theorem tada1 (R : Type*) [CommRing R] :
    Function.Injective (algebraMap R (∀ I : MaximalSpectrum R, Localization.AtPrime I.1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← Submodule.mem_bot R, ← SetLike.mem_coe, ← Set.singleton_subset_iff,
    ← Submodule.colon_eq_top_iff_subset, ← not_ne_iff, Ideal.ne_top_iff_exists_maximal]
  contrapose! hx
  obtain ⟨I, hI, hx⟩ := hx
  refine Function.ne_iff.mpr ⟨⟨I, hI⟩, ?_⟩
  simpa [IsLocalization.map_eq_zero_iff I.primeCompl, not_imp_not, SetLike.le_def] using hx

/-- A version of `IsArtinianRing.equivPiLocalization` with worse definitional equality. -/
noncomputable def IsArtinianRing.equivPiLocalizationAux
    (R : Type*) [CommRing R] [IsArtinianRing R] :
    R ≃ₐ[R] ∀ I : MaximalSpectrum R, Localization.AtPrime I.1 :=
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  let n : ℕ := Classical.choose (isNilpotent_nilradical (R := R))
  let hn : nilradical R ^ n = ⊥ := Classical.choose_spec isNilpotent_nilradical
  have hn : nilradical R ^ (n + 1) = ⊥ := by rw [pow_succ, hn, bot_mul]
  have (I : MaximalSpectrum R) : IsLocalization I.1.primeCompl (R ⧸ I.asIdeal ^ (n + 1)) := by
    classical
    rw [isLocalization_iff]
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun h ↦ ?_⟩
    · exact (Ideal.Quotient.isUnit_mk_pow_iff_notMem I.1 n.succ_ne_zero).mpr x.2
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨⟨y, 1⟩, by simp⟩
    · have key : IsCoprime ((∏ J ≠ I, J.1) ^ (n + 1)) (I.1 ^ (n + 1)) := by
        rw [IsCoprime.pow_iff n.succ_pos n.succ_pos, IsCoprime.prod_left_iff]
        intro J hJ
        rw [Ideal.isCoprime_iff_sup_eq]
        exact J.2.coprime_of_ne I.2 <| mt MaximalSpectrum.ext <| Finset.ne_of_mem_erase hJ
      obtain ⟨a, ha, b, hb, hab⟩ := key.exists
      refine ⟨⟨a, ?_⟩, ?_⟩
      · simpa [← hab, I.1.add_mem_iff_left, I.1.pow_le_self _ hb] using I.1.one_notMem
      · rw [← sub_eq_zero, ← mul_sub, ← Ideal.mem_bot, ← hn]
        rw [MaximalSpectrum.nilradical_pow_eq_iInf, iInf_split_single _ I, mul_comm]
        refine Ideal.mul_le_inf (Ideal.mul_mem_mul (Ideal.Quotient.eq.mp h) ?_)
        simp only [mem_iInf]
        refine fun J h ↦ Ideal.pow_right_mono ?_ (n + 1) ha
        refine Ideal.prod_le_inf.trans (Finset.inf_le ?_)
        exact Finset.mem_erase_of_ne_of_mem h (Finset.mem_univ J)
  ((AlgEquiv.piCongrRight fun I ↦ IsLocalization.algEquiv I.1.primeCompl _ _).trans
    ((IsArtinainRing.quotNilradicalPowEquivPi R (n + 1)).symm.trans
      ((Ideal.quotientEquivAlgOfEq R hn).trans (.quotientBot R R)))).symm

/-- An Artinian local ring is isomorphic to the product of its localizations. -/
noncomputable def IsArtinianRing.equivPiLocalization
    (R : Type*) [CommRing R] [IsArtinianRing R] :
    R ≃ₐ[R] ∀ I : MaximalSpectrum R, Localization.AtPrime I.1 :=
  letI ψ := IsArtinianRing.equivPiLocalizationAux R
  AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨tada1 R, fun x ↦
    ⟨ψ.symm x, (ψ.commutes (ψ.symm x)).symm.trans (ψ.apply_symm_apply x)⟩⟩

@[simp]
theorem IsArtinianRing.equivPiLocalization_apply (R : Type*) [CommRing R] [IsArtinianRing R]
    (x : R) : IsArtinianRing.equivPiLocalization R x = algebraMap R _ x :=
  rfl

@[simp]
theorem IsArtinianRing.equivPiLocalization_apply_apply (R : Type*) [CommRing R] [IsArtinianRing R]
    (x : R) (I : MaximalSpectrum R) : IsArtinianRing.equivPiLocalization R x I = algebraMap R _ x :=
  rfl

end artinian

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

variable {A B M : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] [AddCommGroup M] [Module A M]

-- PRed
variable (B) in
open IsLocalRing LinearMap Module Submodule TensorProduct.AlgebraTensorModule in
theorem CovBy.length_baseChange {p q : Submodule A M} (h : p ⋖ q) :
    length B (q.baseChange B) =
      length B (p.baseChange B) + length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
  rw [← (Submodule.toBaseChange.toLinearEquiv B p).length_eq,
    ← (Submodule.toBaseChange.toLinearEquiv B q).length_eq]
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

-- PRed
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

-- PRed
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
    (by simpa) (by simpa) (by simpa), Module.length_eq_of_surjective (M := ResidueField B)
      (residue_surjective (R := A)), Module.length_eq_rank]

-- PRed
variable (A B M) in
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

section

namespace Ideal

open Classical in
noncomputable def ramificationIdx
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx_def
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    p.ramificationIdx q = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat :=
  dif_pos _

theorem ramificationIdx_of_not_isPrime
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) (hq : ¬ q.IsPrime) :
    p.ramificationIdx q = 0 :=
  dif_neg hq

theorem ramificationIdx_of_not_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) (h : ¬ p.map (algebraMap R S) ≤ q) : p.ramificationIdx q = 0 := by
  by_cases hq : q.IsPrime
  · suffices map (algebraMap R (Localization.AtPrime q)) p = ⊤ by
      rw [← Submodule.Quotient.subsingleton_iff] at this
      rw [ramificationIdx_def, Module.length_eq_zero, ENat.toNat_zero]
    rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← map_map]
    contrapose! h
    rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint q.primeCompl] at h
    exact disjoint_compl_left_iff.mp h
  · rw [ramificationIdx_of_not_isPrime p q hq]

theorem ramificationIdx_of_ne
    {R : Type*} [CommRing R] (p q : Ideal R) (h : p ≠ q) [hp : p.IsPrime] :
      p.ramificationIdx q = 0 := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime p q hq]
  by_cases hpq : p ≤ q; swap
  · apply ramificationIdx_of_not_le
    rwa [Algebra.algebraMap_self, map_id]
  contrapose! h
  let Rp := R ⧸ p
  let qRp := q.map (algebraMap R Rp)
  have : qRp.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  let Rq := Localization.AtPrime q
  let pRq := p.map (algebraMap R Rq)
  let A := Rq ⧸ pRq
  have h1 : Module.length Rq A = Module.length A A := by
    apply Module.length_eq_of_surjective
    rw [Quotient.algebraMap_eq]
    exact Quotient.mk_surjective
  rw [ramificationIdx_def, h1] at h
  have : IsArtinianRing A := by
    rw [isArtinianRing_iff_isFiniteLength, ← Module.length_ne_top_iff]
    contrapose! h
    rw [ENat.toNat_eq_zero]
    right
    assumption
  have : IsDomain A := by
    apply IsLocalization.isDomain_of_le_nonZeroDivisors
      (M := Algebra.algebraMapSubmonoid Rp q.primeCompl) A
    rintro - ⟨x, hx, rfl⟩
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq]
    rw [Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem]
    exact mt (@hpq x) hx
  have : IsField A := IsArtinianRing.isField_of_isDomain A
  have : IsMaximal (p.map (algebraMap R Rq)) := by
    apply Quotient.maximal_of_isField
    assumption
  have := IsLocalRing.eq_maximalIdeal this
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at this
  replace this := congrArg (comap (algebraMap R Rq)) this
  rwa [IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl Rq hq disjoint_compl_left,
    IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl Rq hp] at this
  have : Disjoint (q.primeCompl : Set R) (q : Set R) := by
    apply disjoint_compl_left
  exact Set.disjoint_of_subset_right hpq disjoint_compl_left

/-- See `ramificationIdx_tower'` for a version that does not assume primality. -/
theorem ramificationIdx_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
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

theorem ramificationIdx_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T) [r.LiesOver q] [Module.Flat S T] :
    p.ramificationIdx r = p.ramificationIdx q * q.ramificationIdx r := by
  by_cases hr : r.IsPrime
  · rw [Ideal.over_def r q]
    apply ramificationIdx_tower
  · rw [ramificationIdx_of_not_isPrime p r hr, ramificationIdx_of_not_isPrime q r hr, mul_zero]

theorem ramificationIdx_of_not_liesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) (h : ¬ q.LiesOver p) : p.ramificationIdx q = 0 := by
  rw [ramificationIdx_tower' p (q.under R) q, ramificationIdx_of_ne p (q.under R), zero_mul]
  rwa [liesOver_iff] at h

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

noncomputable instance [Algebra.QuasiFinite R S] : Fintype (p.primesOver S) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

-- PRed
open TensorProduct in
noncomputable def _root_.Algebra.TensorProduct.quotientTensorEquiv
    {R : Type*} (S T A : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing T] [Algebra R T] [CommRing A] [Algebra R A]
    [Algebra S T] [IsScalarTower R S T] (I : Ideal T) :
    (T ⧸ I) ⊗[R] A ≃ₐ[S] (T ⊗[R] A) ⧸ I.map (algebraMap T (T ⊗[R] A)) :=
  { __ := (Algebra.TensorProduct.comm R (T ⧸ I) A).toRingEquiv.trans <|
      (Algebra.TensorProduct.tensorQuotientEquiv (R := R) R T A I).toRingEquiv.trans <|
      quotientEquiv _ _ (Algebra.TensorProduct.comm R A T).toRingEquiv <| by
        nth_rewrite 3 [← Ideal.map_coe]
        simp [map_map]
        rfl
    commutes' _ := rfl }

-- PRed
open TensorProduct in
noncomputable def _root_.Algebra.TensorProduct.quotientTensorEquiv_apply_tmul
    {R : Type*} (S T A : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing T] [Algebra R T] [CommRing A] [Algebra R A]
    [Algebra S T] [IsScalarTower R S T] (I : Ideal T) (x : T) (y : A) :
    Algebra.TensorProduct.quotientTensorEquiv S T A I (x ⊗ₜ y) =
      Ideal.Quotient.mk _ (x ⊗ₜ[R] y) :=
  rfl

-- PRed
open TensorProduct in
noncomputable def _root_.Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul
    {R : Type*} (S T A : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing T] [Algebra R T] [CommRing A] [Algebra R A]
    [Algebra S T] [IsScalarTower R S T] (I : Ideal T) (x : T) (y : A) :
    (Algebra.TensorProduct.quotientTensorEquiv S T A I).symm (Ideal.Quotient.mk _ (x ⊗ₜ[R] y)) =
      (Ideal.Quotient.mk _ x) ⊗ₜ[R] y :=
  rfl

-- PRed
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open Algebra Algebra.TensorProduct in
/-- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`. -/
noncomputable def Fiber.algEquivQuotient :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    p.Fiber S ≃ₐ[S] Sp ⧸ pSp :=
  letI Rp := Localization p.primeCompl
  letI pRp := IsLocalRing.maximalIdeal Rp
  letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI pSp := pRp.map (algebraMap Rp Sp)
  (commRight R S p.ResidueField).symm.trans <| (tensorQuotientEquiv S Rp S pRp).trans <|
    { __ := quotientEquiv _ _ (Localization.tensorLeftAlgEquiv p.primeCompl S) (by
        rw [← Ideal.map_coe includeRight, Ideal.map_map]
        congr
        ext
        simp [Localization.tensorLeftAlgEquiv_apply_one_tmul p.primeCompl])
      commutes' := by simp }

noncomputable instance [Algebra.QuasiFinite R S] : Fintype (MaximalSpectrum (p.Fiber S)) :=
  Fintype.ofFinite (MaximalSpectrum (p.Fiber S))

instance [Algebra.QuasiFinite R S] (q : MaximalSpectrum (p.Fiber S)) :
    Module.Finite p.ResidueField (Localization.AtPrime q.1) :=
  Module.Finite.of_quasiFinite

theorem foo1 [Algebra.QuasiFinite R S] : Module.finrank p.ResidueField (p.Fiber S) =
    ∑ q : MaximalSpectrum (p.Fiber S),
      Module.finrank p.ResidueField (Localization.AtPrime q.1) := by
  have key := (IsArtinianRing.equivPiLocalization (p.Fiber S)).restrictScalars p.ResidueField
  rw [key.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

set_option backward.isDefEq.respectTransparency false in
noncomputable def equiv [Algebra.QuasiFinite R S] : MaximalSpectrum (p.Fiber S) ≃ p.primesOver S :=
  .symm <| (PrimeSpectrum.primesOverOrderIsoFiber R S p).toEquiv.trans
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum

theorem equiv_apply [Algebra.QuasiFinite R S] (q : MaximalSpectrum (p.Fiber S)) :
    (equiv p) q = q.1.comap Algebra.TensorProduct.includeRight := by
  rfl

noncomputable def foo9 :
    letI Rp := Localization p.primeCompl
    letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    letI pS := p.map (algebraMap R S)
    letI pSp := pS.map (algebraMap S Sp)
    ∀ (q : Ideal (Sp ⧸ pSp)) (r : Ideal S) [q.IsPrime] [r.IsPrime] [q.LiesOver r] [r.LiesOver p],
      letI Sr := Localization.AtPrime r
      Localization.AtPrime q ≃ₐ[Rp] Sr ⧸ pS.map (algebraMap S Sr) := by
  intro q r hq hr hqr hrp
  let Rp := Localization p.primeCompl
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let pS := p.map (algebraMap R S)
  let pSp := pS.map (algebraMap S Sp)
  let Sr := Localization.AtPrime r
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
      (Localization.AtPrime q) := by
    suffices Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl = (q.under (S ⧸ pS)).primeCompl by
      convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid (S ⧸ pS) (Algebra.algebraMapSubmonoid S p.primeCompl))
            (Localization.AtPrime q) q
    ext x
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    rw [mem_primeCompl_iff, mem_comap, ← Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      ← mem_comap, ← under_def, ← hqr.over]
    refine ⟨fun ⟨y, hy, hx⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
    rw [← sub_eq_zero, ← map_sub, Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem] at hx
    contrapose! hy
    simpa [r.sub_mem_iff_left hy] using map_le_iff_le_comap.mpr hrp.over.le hx
  have := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Localization.AtPrime q)
  have := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Sr ⧸ map (algebraMap S Sr) pS)
  let e := (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
    (Localization.AtPrime q) ((Sr ⧸ pS.map (algebraMap S Sr)))).restrictScalars R
  exact
    { __ := e
      commutes' := by
        let f := e.toAlgHom.comp (IsScalarTower.toAlgHom R Rp (Localization.AtPrime q))
        let g := IsScalarTower.toAlgHom R Rp (Sr ⧸ pS.map (algebraMap S Sr))
        suffices f = g by rwa [DFunLike.ext_iff] at this
        apply Localization.algHom_ext
        suffices f.toRingHom.comp (algebraMap R Rp) = g.toRingHom.comp (algebraMap R Rp) by
          rwa [DFunLike.ext_iff] at this ⊢
        simp }

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable def foo8 (q : Ideal (p.Fiber S)) [q.IsPrime] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Sr ⧸ p.map (algebraMap R Sr) := by
  let Rp := Localization p.primeCompl
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let pS := p.map (algebraMap R S)
  let pSp := pS.map (algebraMap S Sp)
  let r := q.under S
  let Sr := Localization.AtPrime r
  change Localization.AtPrime q ≃ₐ[Rp] Sr ⧸ p.map (algebraMap R Sr)
  let eq : p.Fiber S ≃ₐ[S] (Sp ⧸ pSp) := by
    refine (Fiber.algEquivQuotient p).trans (quotientEquivAlgOfEq S ?_)
    rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map]
    dsimp only [pSp, pS]
    rw [map_map, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let q' : Ideal (Sp ⧸ pSp) := q.comap eq.symm
  have : Localization.AtPrime q' ≃ₐ[Rp] Localization.AtPrime q :=
    { __ := Localization.localAlgEquiv q' q eq.symm rfl
      commutes' := by
        let e1 := (Localization.localAlgEquiv q' q eq.symm rfl).toAlgHom.restrictScalars R
        let e2 := IsScalarTower.toAlgHom R Rp (Localization.AtPrime q')
        let f := e1.comp e2
        let g := IsScalarTower.toAlgHom R Rp (Localization.AtPrime q)
        suffices f = g by rwa [DFunLike.ext_iff] at this
        apply Localization.algHom_ext
        suffices f.toRingHom.comp (algebraMap R Rp) = g.toRingHom.comp (algebraMap R Rp) by
          rwa [DFunLike.ext_iff] at this ⊢
        simp }
  refine this.symm.trans <| (foo9 p q' r).trans <|
    quotientEquivAlgOfEq Rp <| by rw [map_map, ← IsScalarTower.algebraMap_eq]

theorem diamond {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    (Localization.AtPrime.instAlgebraOfLiesOver p q) = OreLocalization.instAlgebra := by
  apply Algebra.algebra_ext
  rw [← DFunLike.ext_iff]
  exact Localization.localRingHom_unique p q _ Ideal.LiesOver.over fun x ↦ rfl

theorem foo3 (q : Ideal (p.Fiber S)) [q.IsPrime] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Module.length (Localization.AtPrime p) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime p) (Sr ⧸ p.map (algebraMap R Sr)) := by
  apply LinearEquiv.length_eq
  convert (foo8 p q).toLinearEquiv
  rw [diamond]
  rfl

theorem foo2 [Algebra.QuasiFinite R S] [Module.Flat R S] (q : MaximalSpectrum (p.Fiber S)) :
    Module.finrank p.ResidueField (Localization.AtPrime q.1) =
      p.ramificationIdx (q.1.comap Algebra.TensorProduct.includeRight) *
        Module.finrank p.ResidueField
          (q.1.comap Algebra.TensorProduct.includeRight).ResidueField := by
  set r := q.1.comap Algebra.TensorProduct.includeRight
  set Sr := Localization.AtPrime r
  set A := Sr ⧸ p.map (algebraMap R Sr)
  have := length_restrictScalars (Localization.AtPrime p) (Localization.AtPrime r) A
  replace this := congrArg ENat.toNat this
  rw [ENat.toNat_mul, Cardinal.toNat_toENat] at this
  convert this
  · rw [← foo3, Module.length_eq_of_surjective
      (IsLocalRing.residue_surjective (R := Localization.AtPrime p)),
      Module.length_eq_finrank, ENat.toNat_coe]
  · rw [ramificationIdx_def]

theorem sum_ramification_inertia
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber S) =
      ∑ q : p.primesOver S, p.ramificationIdx q.1 *
        Module.finrank p.ResidueField q.1.ResidueField := by
  rw [foo1, ← (equiv p).sum_comp]
  apply Finset.sum_congr rfl
  intros
  apply foo2

-- PRed
lemma finrank_fiber_eq_rankAtStalk (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [hp : p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber S) = Module.rankAtStalk S ⟨p, hp⟩ :=
  (Module.rankAtStalk_eq ⟨p, hp⟩).symm

-- PRed
theorem primeCompl_bot (R : Type*) [Semiring R] [IsDomain R] :
    (⊥ : Ideal R).primeCompl = nonZeroDivisors R := by
  ext
  simp

instance isFractionRing_residueField_bot {R : Type*} [CommRing R] [IsDomain R] :
    IsFractionRing R (⊥ : Ideal R).ResidueField := by
  let R' := Localization.AtPrime (⊥ : Ideal R)
  have : IsFractionRing R R' := by
    convert Localization.isLocalization
    exact (Ideal.primeCompl_bot R).symm
  let : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
  change IsFractionRing R (R' ⧸ IsLocalRing.maximalIdeal R')
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R)
    (AlgEquiv.quotientBot R R').symm

set_option backward.isDefEq.respectTransparency false in
theorem IsField.of_finite (K L : Type*) [Field K] [CommRing L] [Algebra K L]
    [IsDomain L] [Module.Finite K L] :
    IsField L where
  exists_pair_ne := Nontrivial.exists_pair_ne
  mul_comm := CommSemiring.mul_comm
  mul_inv_cancel {x} hx :=
    (LinearMap.mulLeft K x).surjective_of_injective (mul_right_injective₀ hx) 1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance isFractionRing_fiber_bot
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] [IsDomain R] [IsDomain S] [Module.Finite R S] :
    IsFractionRing S ((⊥ : Ideal R).Fiber S) := by
  let κR := (⊥ : Ideal R).ResidueField
  let κS := (⊥ : Ideal R).Fiber S
  let R' := Localization.AtPrime (⊥ : Ideal R)
  have : IsFractionRing R R' := by
    convert Localization.isLocalization
    exact (Ideal.primeCompl_bot R).symm
  let : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
  let M₁ := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  let M₂ := nonZeroDivisors S
  have h : M₁ ≤ nonZeroDivisors S := by
    rintro - ⟨x, hx, rfl⟩
    exact map_mem_nonZeroDivisors (algebraMap R S) (FaithfulSMul.algebraMap_injective R S) hx
  have : IsDomain (Localization M₁) := IsLocalization.isDomain_localization h
  have : IsField (Localization M₁) := IsField.of_finite (FractionRing R) (Localization M₁)
  let f : Localization M₁ →ₐ[S] FractionRing S :=
    Localization.mapToFractionRing (FractionRing S) M₁ (Localization M₁) h

  -- subalgebra of fraction ring
  sorry

theorem sum_ramification_inertia'
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Projective R S]
    (p : Ideal R) [p.IsPrime] :
    Module.finrank R S =
      ∑ q : p.primesOver S, p.ramificationIdx q.1 *
        Module.finrank p.ResidueField q.1.ResidueField := by
  let κR := (⊥ : Ideal R).ResidueField
  let κS := (⊥ : Ideal R).Fiber S
  let : Algebra S κS := Algebra.TensorProduct.rightAlgebra
  have : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
  rw [← sum_ramification_inertia, ← Algebra.IsAlgebraic.finrank_of_isFractionRing R κR S κS,
    Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_rankAtStalk]
  apply (Module.isLocallyConstant_rankAtStalk).apply_eq_of_preconnectedSpace

theorem sum_ramification_inertia''
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G] [Finite G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] [Module.Flat R S] [FaithfulSMul R S] :
    Module.Projective R S := by
  have h1 : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  have h2 : (algebraMap R S).IsIntegral := algebraMap_isIntegral_iff.mpr h1
  have : Module.FaithfullyFlat R S := by
    apply Module.FaithfullyFlat.of_comap_surjective
    apply RingHom.IsIntegral.comap_surjective h2
    exact FaithfulSMul.algebraMap_injective R S
  -- finitely generated projective iff locally free
  have : ∀ p : PrimeSpectrum R, Module.Flat (Localization.AtPrime p.1) (LocalizedModule p.1.primeCompl S) := by
    intro m
    exact Module.Flat.localizedModule m.asIdeal.primeCompl
  have : ∀ p : PrimeSpectrum R, Module.Free (Localization.AtPrime p.1) (LocalizedModule p.1.primeCompl S) := by
    intro m
    sorry
    -- apply Module.free_of_flat_of_isLocalRing
    -- exact Module.Flat.localizedModule m.asIdeal.primeCompl
  have : Module.FinitePresentation R S := by
    sorry
  apply Module.projective_of_localization_maximal
  sorry

theorem sum_ramification_inertia'''
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G] [Finite G]
    [MulSemiringAction G S] [FaithfulSMul G S] [Module.Flat R S] -- finite type will give quasifinite
    [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsPrime] :
    letI : Module.Finite R S := sorry
    Nat.card G =
      ∑ q : p.primesOver S, p.ramificationIdx q.1 *
        Module.finrank p.ResidueField q.1.ResidueField := by

  have : Algebra.QuasiFinite R S := sorry
  have : Module.Flat R S := sorry
  rw [← sum_ramification_inertia]
  -- might need to also assume `[Domain R]` (to get connected base)?
  sorry

end Ideal
