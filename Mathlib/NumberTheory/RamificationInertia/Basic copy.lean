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
    (by simpa) (by simpa) (by simpa), Module.length_eq_of_surjective (M := ResidueField B)
      (residue_surjective (R := A)), Module.length_eq_rank]

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

section

open TensorProduct

variable {R : Type*} [CommRing R] (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ]
  (S : Type*) [CommRing S] [Algebra R S]

-- PRed
/-- The isomorphism `S ⊗[R] Rₘ ≃ₐ[S] Sₘ`. This is a specialization of `IsLocalization.algEquiv`,
but with additional properties since now `Sₘ` is automatically an `Rₘ`-algebra. -/
noncomputable def Localization.tensor_localization_algEquiv :
    (S ⊗[R] Localization M) ≃ₐ[S] Localization (Algebra.algebraMapSubmonoid S M) :=
  (Localization.algEquiv (Algebra.algebraMapSubmonoid S M) (S ⊗[R] Localization M)).symm

-- PRed
@[simp]
theorem Localization.tensor_localization_algEquiv_apply_tmul_one (x : S) :
    Localization.tensor_localization_algEquiv M S (x ⊗ₜ[R] 1) = algebraMap _ _ x :=
  (Localization.tensor_localization_algEquiv M S).commutes x

-- PRed
@[simp]
theorem Localization.tensor_localization_algEquiv_apply_one_tmul (x : Localization M) :
    Localization.tensor_localization_algEquiv M S (1 ⊗ₜ[R] x) = algebraMap _ _ x := by
  let Rₘ := Localization M
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq M x
  letI : Algebra Rₘ (S ⊗[R] Rₘ) := Algebra.TensorProduct.rightAlgebra
  have h1 : (1 : S) ⊗ₜ[R] IsLocalization.mk' Rₘ x y = algebraMap _ _ (IsLocalization.mk' Rₘ x y) :=
    rfl
  rw [h1, Localization.tensor_localization_algEquiv, Localization.algEquiv_symm_apply,
    IsLocalization.algebraMap_mk' S, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp_rw [RingHom.id_apply]
  have h x : algebraMap S Sₘ ((algebraMap R S) x) = algebraMap Rₘ Sₘ ((algebraMap R Rₘ) x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h, h, ← map_mul, IsLocalization.mk'_spec]

-- PRed
noncomputable def Localization.localization_tensor_algEquiv :
    (Localization M ⊗[R] S) ≃ₐ[Localization M] Localization (Algebra.algebraMapSubmonoid S M) :=
  { __ := (Algebra.TensorProduct.comm R (Localization M) S).toRingEquiv.trans
      (Localization.tensor_localization_algEquiv M S).toRingEquiv
    commutes' := Localization.tensor_localization_algEquiv_apply_one_tmul M S }

-- PRed
@[simp]
theorem Localization.localization_tensor_algEquiv_apply_tmul_one (x : Localization M) :
    Localization.localization_tensor_algEquiv M S (x ⊗ₜ[R] 1) = algebraMap _ _ x :=
  (Localization.localization_tensor_algEquiv M S).commutes x

-- PRed
@[simp]
theorem Localization.localization_tensor_algEquiv_apply_one_tmul (x : S) :
    Localization.localization_tensor_algEquiv M S (1 ⊗ₜ[R] x) = algebraMap _ _ x :=
  (Localization.tensor_localization_algEquiv M S).commutes x

end

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
    have : IsLocalization qRp.primeCompl A := by
      sorry
    exact IsLocalization.isDomain_of_atPrime A qRp
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

#exit

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] :
    Algebra (IsLocalRing.ResidueField R) (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
  inferInstanceAs (Algebra (R ⧸ IsLocalRing.maximalIdeal R)
    (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))

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
  (commRight R S p.ResidueField).symm.trans <|
    (tensorQuotientEquiv S Rp S pRp).trans <|
    { __ := quotientEquiv _ _ (Localization.tensor_localization_algEquiv p.primeCompl S) (by
        rw [← Ideal.map_coe includeRight, Ideal.map_map]
        congr
        ext
        simp [Localization.tensor_localization_algEquiv_apply_one_tmul p.primeCompl])
      commutes' x := by simp }

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open Algebra Algebra.TensorProduct in
/-- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`. -/
noncomputable def Fiber.ker_includeRight :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    RingHom.ker (includeRight : S →ₐ[R] p.Fiber S) = pSp.comap (algebraMap S Sp) := by
  let Rp := Localization p.primeCompl
  let pRp := IsLocalRing.maximalIdeal Rp
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let pSp := pRp.map (algebraMap Rp Sp)
  let e := Fiber.algEquivQuotient p (S := S)
  rw [← RingHom.ker_coe_toRingHom, ← algebraMap_eq_includeRight, ← e.symm.toAlgHom.comp_algebraMap]
  refine (RingHom.ker_equiv_comp _ _).trans ?_
  rw [IsScalarTower.algebraMap_eq S Sp, Ideal.Quotient.algebraMap_eq, RingHom.ker_eq_comap_bot,
    ← comap_comap, ← RingHom.ker_eq_comap_bot, mk_ker]









noncomputable instance [Algebra.QuasiFinite R S] : Fintype (p.primesOver S) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : Algebra p.ResidueField (p.Fiber S) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance [Algebra.QuasiFinite R S] : Fintype (MaximalSpectrum (p.Fiber S)) :=
  Fintype.ofFinite (MaximalSpectrum (p.Fiber S))

instance : IsArtinianRing p.ResidueField :=
  inferInstance

instance : IsLocalRing (Localization.AtPrime p) :=
  inferInstance

instance {R : Type*} [Semiring R] : Module R R :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance : CommRing (p.Fiber S) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (q : MaximalSpectrum (p.Fiber S)) :
    Algebra p.ResidueField (Localization.AtPrime q.1) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (q : MaximalSpectrum (p.Fiber S)) :
    Module p.ResidueField (Localization.AtPrime q.1) :=
  Algebra.toModule

-- PRed
instance {R : Type*} [CommSemiring R] : IsLocalHom (algebraMap R R) := by
  exact { map_nonunit := fun a a_1 ↦ a_1 }

instance foobar [CommRing R] : DistribMulAction R R :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance [Algebra.QuasiFinite R S] (q : MaximalSpectrum (p.Fiber S)) :
    Module.Finite p.ResidueField (Localization.AtPrime q.1) :=
  Module.Finite.of_quasiFinite

set_option backward.isDefEq.respectTransparency false in
theorem foo1 [Algebra.QuasiFinite R S] : Module.finrank p.ResidueField (p.Fiber S) =
    ∑ q : MaximalSpectrum (p.Fiber S),
      Module.finrank p.ResidueField (Localization.AtPrime q.1) := by
  have key := (IsArtinianRing.equivPiLocalization (p.Fiber S)).restrictScalars p.ResidueField
  rw [key.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

set_option backward.isDefEq.respectTransparency false in
noncomputable def equiv [Algebra.QuasiFinite R S] : p.primesOver S ≃ MaximalSpectrum (p.Fiber S) :=
  (PrimeSpectrum.primesOverOrderIsoFiber R S p).toEquiv.trans
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum

theorem equiv_symm_apply [Algebra.QuasiFinite R S] (q : MaximalSpectrum (p.Fiber S)) :
    (equiv p).symm q = q.1.comap Algebra.TensorProduct.includeRight := by
  rfl

open TensorProduct

set_option backward.isDefEq.respectTransparency false in
theorem diamond1 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    (Localization.AtPrime.instAlgebraOfLiesOver p q) = OreLocalization.instAlgebra := by
  apply Algebra.algebra_ext
  rw [← DFunLike.ext_iff]
  apply Localization.localRingHom_unique _
  · exact Ideal.LiesOver.over
  · intro x
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem diamond2 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    (Localization.AtPrime.instAlgebraOfLiesOver p q).toModule = OreLocalization.instModuleOfIsScalarTower := by
  rw [diamond1]
  rfl

theorem ker_localRingHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (f : R →+* S) (h : I = comap f J) :
    RingHom.ker (Localization.localRingHom I J f h) =
      ((RingHom.ker (algebraMap S (Localization.AtPrime J))).comap f).map
        (algebraMap R (Localization.AtPrime I)) := by
  apply le_antisymm; swap
  · rw [map_le_iff_le_comap]
    intro
    simp
  · intro x hx
    obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq I.primeCompl x
    rw [IsLocalization.mem_map_algebraMap_iff I.primeCompl]
    refine ⟨⟨⟨x, ?_⟩, y⟩, IsLocalization.mk'_spec (Localization.AtPrime I) x y⟩
    rwa [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff,
      ← IsLocalization.mk'_eq_zero_iff (f x) 1 (S := Localization.AtPrime J),
      IsLocalization.mk'_one] at hx

section

open Algebra.TensorProduct

variable {p}

noncomputable def foo5 (q : MaximalSpectrum (p.Fiber S)) :
    Localization.AtPrime (q.1.comap includeRight) →ₐ[R] Localization.AtPrime q.1 :=
  Localization.localAlgHom _ _ includeRight rfl

theorem foo6 (q : MaximalSpectrum (p.Fiber S)) :
    Function.Surjective (foo5 q) := by
  intro x
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq q.1.primeCompl x
  obtain ⟨a, ha, b, hb⟩ := Fiber.exists_smul_eq_one_tmul p x
  obtain ⟨c, hc, d, hd⟩ := Fiber.exists_smul_eq_one_tmul p y.1
  dsimp only [foo5]
  refine ⟨IsLocalization.mk' (M := (q.1.comap includeRight).primeCompl) _ (c • b) ⟨a • d, ?_⟩, ?_⟩
  · rw [mem_primeCompl_iff, mem_comap, map_smul, includeRight_apply, ← hd, ← smul_assoc,
      smul_eq_mul, Algebra.smul_def, q.2.isPrime.mul_mem_right_iff y.2, ← mem_comap,
      ← under_def, ← LiesOver.over (p := p) (P := q.1)]
    exact IsPrime.mul_notMem ‹_› ha hc
  · rw [Localization.localAlgHom_apply, Localization.localRingHom_mk',
      IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul]
    rw [← smul_eq_mul, mul_comm, ← smul_eq_mul, smul_comm, ← smul_assoc, hd,
      smul_comm, ← smul_assoc, hb]
    simp [mul_comm]

theorem foo7 (q : MaximalSpectrum (p.Fiber S)) :
    RingHom.ker (foo5 q) = p.map (algebraMap R _) := by
  let g : S →ₐ[R] p.Fiber S := includeRight
  apply le_antisymm
  · dsimp only [foo5]
    intro x hx
    obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq (q.1.comap includeRight).primeCompl x
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    apply Ideal.mul_mem_right
    rw [RingHom.mem_ker, Localization.localAlgHom_apply, Localization.localRingHom_mk',
      IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨a, ha, b, hb⟩ := Fiber.exists_smul_eq_one_tmul p z.1
    have hz' := congr(a • $hz)
    rw [← includeRight_apply] at hb
    rw [← smul_eq_mul, ← smul_assoc, hb, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smul_eq_mul,
      ← map_mul, smul_zero, ← RingHom.mem_ker, Fiber.ker_includeRight, mem_comap] at hz'
    clear hz
    let Q := q.1.comap includeRight
    let SQ := Localization.AtPrime Q
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    let Rp := Localization p.primeCompl
    let pRp := IsLocalRing.maximalIdeal (Localization p.primeCompl)
    let pSp := pRp.map (algebraMap Rp Sp)
    have : Q.LiesOver p := comap_liesOver q.asIdeal p includeRight
    -- Sp is contained in SQ
    change algebraMap S SQ x ∈ p.map (algebraMap R SQ)
    change algebraMap S Sp (b * x) ∈ pSp at hz'
    have : b ∉ Q := by
      rwa [mem_comap, ← hb, Algebra.smul_def, Ideal.IsPrime.mul_mem_right_iff z.2,
        ← mem_comap, ← under_def, ← LiesOver.over (p := p) (P := q.1)]
    dsimp only [pSp, pRp] at hz'
    rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R S Sp, ← map_map] at hz'
    rw [IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S p.primeCompl)] at hz'
    obtain ⟨⟨u, -, v, hv, rfl⟩, h⟩ := hz'
    simp only at h
    rw [← map_mul, mul_assoc, mul_comm x, ← mul_assoc] at h
    have hv' : algebraMap R S v ∉ Q := by
      rwa [← mem_comap, ← under_def, ← LiesOver.over (p := p) (P := Q)]
    have hbc : b * algebraMap R S v ∉ Q := by
      rwa [Ideal.IsPrime.mul_mem_left_iff this]
    rw [← sub_eq_zero, ← map_sub,
      ← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid S p.primeCompl),
      IsLocalization.mk'_eq_zero_iff] at h
    obtain ⟨⟨-, m, hm, rfl⟩, h⟩ := h
    simp only at h
    replace h := congrArg (algebraMap S SQ) h
    rw [map_zero, map_mul] at h
    have : algebraMap R S m ∉ Q := by
      rwa [← mem_comap, ← under_def, ← LiesOver.over (p := p) (P := Q)]
    rw [IsUnit.mul_right_eq_zero] at h
    · rw [map_sub, sub_eq_zero, map_mul] at h
      have h1 : IsUnit ((algebraMap S SQ) (b * (algebraMap R S) v)) := by
        exact IsLocalization.map_units SQ (⟨b * (algebraMap R S) v, hbc⟩ : Q.primeCompl)
      have : (algebraMap S SQ) ↑u ∈ p.map (algebraMap R SQ) := by
        rw [IsScalarTower.algebraMap_eq R S SQ, ← map_map]
        apply Ideal.mem_map_of_mem
        exact u.2
      rwa [← h, Ideal.unit_mul_mem_iff_mem] at this
      exact h1
    · exact IsLocalization.map_units SQ (⟨algebraMap R S m, this⟩ : Q.primeCompl)
  · rw [map_le_iff_le_comap]
    intro x hx
    rw [← algebraMap_residueField_eq_zero] at hx
    rw [mem_comap, RingHom.mem_ker, (p.foo5 q).commutes,
      IsScalarTower.algebraMap_apply R p.ResidueField, hx, map_zero]

end

set_option backward.isDefEq.respectTransparency false in
noncomputable def foo4 (q : MaximalSpectrum (p.Fiber S)) :
    letI r := q.1.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Localization.AtPrime q.1 ≃ₐ[Localization.AtPrime p] (Sr ⧸ p.map (algebraMap R Sr)) := by
  let r := q.1.comap Algebra.TensorProduct.includeRight
  let Sr := Localization.AtPrime r
  let f : Sr →ₐ[Localization.AtPrime p] Localization.AtPrime q.1 :=
  { __ := foo5 q
    commutes' x := by
      change (Localization.localRingHom r q.1 Algebra.TensorProduct.includeRight.toRingHom rfl
        (Localization.localRingHom p r (algebraMap R S) LiesOver.over x)) =
          (Localization.localRingHom p q.1 (algebraMap R (p.Fiber S)) LiesOver.over x)
      rw [← RingHom.comp_apply, ← Localization.localRingHom_comp]
      congr
      exact Algebra.TensorProduct.includeRight.comp_algebraMap }
  have hf : Function.Surjective f := foo6 q
  have hf' : RingHom.ker f = p.map (algebraMap R Sr) := foo7 q
  exact (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
    (Ideal.quotientEquivAlgOfEq (Localization.AtPrime p) hf')

set_option backward.isDefEq.respectTransparency false in
theorem foo3 (q : MaximalSpectrum (p.Fiber S)) :
    letI r := q.1.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Module.length (Localization.AtPrime p) (Localization.AtPrime q.1) =
      Module.length (Localization.AtPrime p) (Sr ⧸ p.map (algebraMap R Sr)) := by
  let Rp := Localization.AtPrime p
  let r := q.1.comap (Algebra.TensorProduct.includeRight)
  let Sr := Localization.AtPrime r
  apply LinearEquiv.length_eq
  convert (foo4 p q).toLinearEquiv
  symm
  apply diamond2

set_option backward.isDefEq.respectTransparency false in
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
  rw [foo1, ← (equiv p).symm.sum_comp]
  apply Finset.sum_congr rfl
  intros
  apply foo2

set_option backward.isDefEq.respectTransparency false in
theorem sum_ramification_inertia'
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank R S =
      ∑ q : p.primesOver S, p.ramificationIdx q.1 *
        Module.finrank p.ResidueField q.1.ResidueField := by
  rw [← sum_ramification_inertia]
  -- might need to also assume `[Domain R]` (to get connected base)?
  sorry

set_option backward.isDefEq.respectTransparency false in
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
    apply Module.free_of_flat_of_isLocalRing
    exact Module.Flat.localizedModule m.asIdeal.primeCompl
  have : Module.FinitePresentation R S := by
    sorry
  apply Module.projective_of_localization_maximal


set_option backward.isDefEq.respectTransparency false in
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
