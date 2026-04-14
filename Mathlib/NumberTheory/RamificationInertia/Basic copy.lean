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
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Ramification index

-/

@[expose] public section

section artinian

open Submodule

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
        rw [IsArtinianRing.nilradical_pow_eq_iInf, iInf_split_single _ I, mul_comm]
        refine Ideal.mul_le_inf (Ideal.mul_mem_mul (Ideal.Quotient.eq.mp h) ?_)
        simp only [mem_iInf]
        refine fun J h ↦ Ideal.pow_right_mono ?_ (n + 1) ha
        refine Ideal.prod_le_inf.trans (Finset.inf_le ?_)
        exact Finset.mem_erase_of_ne_of_mem h (Finset.mem_univ J)
  ((AlgEquiv.piCongrRight fun I ↦ IsLocalization.algEquiv I.1.primeCompl _ _).trans
    ((IsArtinianRing.quotNilradicalPowEquivPi R (n + 1)).symm.trans
      ((Ideal.quotientEquivAlgOfEq R hn).trans (.quotientBot R R)))).symm

/-- An Artinian local ring is isomorphic to the product of its localizations. -/
noncomputable def IsArtinianRing.equivPiLocalizationMaximal
    (R : Type*) [CommRing R] [IsArtinianRing R] :
    R ≃ₐ[R] ∀ I : MaximalSpectrum R, Localization.AtPrime I.1 :=
  letI ψ := IsArtinianRing.equivPiLocalizationAux R
  AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨tada1 R, fun x ↦
    ⟨ψ.symm x, (ψ.commutes (ψ.symm x)).symm.trans (ψ.apply_symm_apply x)⟩⟩

@[simp]
theorem IsArtinianRing.equivPiLocalizationMaximal_apply
    (R : Type*) [CommRing R] [IsArtinianRing R] (x : R) :
    IsArtinianRing.equivPiLocalizationMaximal R x = algebraMap R _ x :=
  rfl

@[simp]
theorem IsArtinianRing.equivPiLocalizationMaximal_apply_apply
    (R : Type*) [CommRing R] [IsArtinianRing R] (x : R) (I : MaximalSpectrum R) :
    IsArtinianRing.equivPiLocalizationMaximal R x I = algebraMap R _ x :=
  rfl

/-- An Artinian local ring is isomorphic to the product of its localizations. -/
noncomputable def IsArtinianRing.equivPiLocalizationPrime
    (R : Type*) [CommRing R] [IsArtinianRing R] :
    R ≃ₐ[R] ∀ I : PrimeSpectrum R, Localization.AtPrime I.1 :=
  (IsArtinianRing.equivPiLocalizationMaximal R).trans
    (AlgEquiv.piCongrLeft R (fun I : PrimeSpectrum R ↦ Localization.AtPrime I.1)
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm)

@[simp]
theorem IsArtinianRing.equivPiLocalizationPrime_apply
    (R : Type*) [CommRing R] [IsArtinianRing R] (x : R) :
    IsArtinianRing.equivPiLocalizationPrime R x = algebraMap R _ x :=
  rfl

@[simp]
theorem IsArtinianRing.equivPiLocalizationPrime_apply_apply
    (R : Type*) [CommRing R] [IsArtinianRing R] (x : R) (I : PrimeSpectrum R) :
    IsArtinianRing.equivPiLocalizationPrime R x I = algebraMap R _ x :=
  rfl

end artinian

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
      exact h.imp IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
        IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
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

section ramification_inertia

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

section ramificationIdx

open Classical in
/-- An alternate definition of ramification index. -/
noncomputable def ramificationIdx' : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx'_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

theorem ramificationIdx'_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx' R = 0 :=
  dif_neg hq

theorem ramificationIdx'_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [h : q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx'_def, h.over]

/-- See `ramificationIdx'_tower'` for a version that does not assume primality. -/
theorem ramificationIdx'_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime] [r.LiesOver q]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  rw [ramificationIdx'_def, ramificationIdx'_eq (r.under R), ramificationIdx'_eq q,
    ← ENat.toNat_mul]
  congr
  set Sq := Localization.AtPrime q
  set Tr := Localization.AtPrime r
  have := length_baseChange (A := Sq) (B := Tr) (M := Sq ⧸ (r.under R).map (algebraMap R Sq))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq] at this
  convert this
  let f := (Ideal.quotientEquivAlgOfEq Tr (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Tr ((r.under R).map (algebraMap R Sq)))
  exact f.toLinearEquiv.length_eq

theorem ramificationIdx'_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [h : r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := by rw [h.over]; exact IsPrime.under S r -- should be lemma
    apply ramificationIdx'_tower
  · rw [ramificationIdx'_of_not_isPrime r R hr, ramificationIdx'_of_not_isPrime r S hr, mul_zero]

end ramificationIdx

section inertiaDeg

open Classical in
/-- An alternate definition of inertia degree. -/
noncomputable def inertiaDeg' : ℕ :=
  if _ : q.IsPrime then Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg'_def [q.IsPrime] :
    q.inertiaDeg' R = Module.finrank (q.under R).ResidueField q.ResidueField :=
  dif_pos _

theorem inertiaDeg'_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg' R = 0 :=
  dif_neg hq

theorem inertiaDeg'_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [h : q.LiesOver p] [q.IsPrime] [p.IsPrime] :
    q.inertiaDeg' R = Module.finrank p.ResidueField q.ResidueField := by
  rw [inertiaDeg'_def]
  convert rfl <;> exact LiesOver.over

theorem inertiaDeg'_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [h : r.LiesOver q] [Module.Flat S T] :
    r.inertiaDeg' R = q.inertiaDeg' R * r.inertiaDeg' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := by rw [h.over]; exact IsPrime.under S r -- should be lemma
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    rw [inertiaDeg'_eq (r.under R), inertiaDeg'_eq (r.under R), inertiaDeg'_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg'_of_not_isPrime r R hr, inertiaDeg'_of_not_isPrime r S hr, mul_zero]

end inertiaDeg

end ramification_inertia

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

noncomputable instance [Algebra.QuasiFinite R S] : Fintype (p.primesOver S) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

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
/-- _ -/
noncomputable def equiv [Algebra.QuasiFinite R S] : MaximalSpectrum (p.Fiber S) ≃ p.primesOver S :=
  .symm <| (PrimeSpectrum.primesOverOrderIsoFiber R S p).toEquiv.trans
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum

theorem equiv_apply [Algebra.QuasiFinite R S] (q : MaximalSpectrum (p.Fiber S)) :
    (equiv p) q = q.1.comap Algebra.TensorProduct.includeRight := by
  rfl

/-- _ -/
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
/-- _ -/
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
      (q.1.comap Algebra.TensorProduct.includeRight).ramificationIdx' R *
          (q.1.comap Algebra.TensorProduct.includeRight).inertiaDeg' R := by
  set r := q.1.comap Algebra.TensorProduct.includeRight
  set Sr := Localization.AtPrime r
  set A := Sr ⧸ p.map (algebraMap R Sr)
  have := length_restrictScalars (Localization.AtPrime p) (Localization.AtPrime r) A
  replace this := congrArg ENat.toNat this
  rw [ENat.toNat_mul, Cardinal.toNat_toENat] at this
  rw [ramificationIdx'_eq p, inertiaDeg'_eq p]
  convert this -- todo: can we remove this convert?
  rw [← foo3, Module.length_eq_of_surjective
    (IsLocalRing.residue_surjective (R := Localization.AtPrime p)),
    Module.length_eq_finrank, ENat.toNat_coe]

theorem sum_ramification_inertia
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber S) =
      ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R := by
  rw [foo1, ← (equiv p).sum_comp]
  apply Finset.sum_congr rfl
  intros
  apply foo2

-- PRed
lemma finrank_fiber_eq_rankAtStalk (R S : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [hp : p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] S) = Module.rankAtStalk S ⟨p, hp⟩ :=
  (Module.rankAtStalk_eq ⟨p, hp⟩).symm

theorem foo17 (R S K : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [CommRing K] [NoZeroDivisors K] [Algebra R K] [FaithfulSMul R K] :
    Module.finrank R S = Module.finrank K (K ⊗[R] S) := by
  symm
  let h : S →ₗ[R] K ⊗[R] S :=
  { toFun := tmul _ 1
    map_add' := tmul_add 1
    map_smul' x := tmul_smul x 1 }
  apply IsBaseChange.finrank_eq (g := h)
  have := IsBaseChange.of_equiv (f := h) (LinearEquiv.refl (R := K) (M := K ⊗[R] S))
  apply this
  intro x
  rfl

/-- _ -/
noncomputable def foo18 (R S K : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [CommRing K] [Algebra R K] (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [IsScalarTower R (Localization.AtPrime p) K] :
    letI Rp := Localization.AtPrime p
    letI Sp := LocalizedModule.AtPrime p S
    (K ⊗[Rp] Sp) ≃ₗ[K] K ⊗[R] S :=
  letI Rp := Localization.AtPrime p
  letI Sp := LocalizedModule.AtPrime p S
  ((LinearEquiv.baseChange Rp K Sp (Rp ⊗[R] S)
    (LocalizedModule.equivTensorProduct p.primeCompl S)).trans
      (AlgebraTensorModule.cancelBaseChange R Rp K K S))

theorem finrank_fiber_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [AddCommGroup S] [Module R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] S) = Module.finrank R S := by
  rw [finrank_fiber_eq_rankAtStalk]
  let Rp := Localization.AtPrime p
  let Sp := LocalizedModule.AtPrime p S
  have : Module.Free Rp Sp := Module.free_of_flat_of_isLocalRing
  transitivity Module.finrank Rp Sp
  · simp only [Module.rankAtStalk_eq]
    transitivity Module.finrank p.ResidueField (p.ResidueField ⊗[Rp] Sp)
    · exact (foo18 R S p.ResidueField p).finrank_eq.symm
    · exact Module.finrank_baseChange
  · let K := FractionRing R
    have : FaithfulSMul Rp K := IsFractionRing.instFaithfulSMul Rp K
    rw [foo17 R S K, foo17 Rp Sp K]
    exact (foo18 R S K p).finrank_eq

theorem sum_ramification_inertia'
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    Module.finrank R S =
      ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R := by
  rw [← sum_ramification_inertia, finrank_fiber_eq_finrank]

theorem sum_ramification_inertia''
    {R S G : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [Module.Flat R S] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    Nat.card G =
      ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R := by
  let := FractionRing.mulSemiringAction_of_isGaloisGroup G R S
  let := FractionRing.liftAlgebra R (FractionRing S)
  rw [← sum_ramification_inertia', (IsGaloisGroup.toFractionRing G R S).card_eq_finrank,
    Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) S (FractionRing S)]

open NumberField in
example {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L] :
    Module.Flat (𝓞 K) (𝓞 L) :=
  inferInstance

end Ideal
