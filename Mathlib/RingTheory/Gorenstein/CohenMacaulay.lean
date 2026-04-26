/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.CohenMacaulay.Catenary
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Gorenstein.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Regular.InjectiveDimension
public import Mathlib.RingTheory.Regular.ProjectiveDimension
public import Mathlib.RingTheory.RingHom.Flat

/-!

# Gorenstein Local Ring is Cohen Macaulay

-/

@[expose] public section

universe v u

variable {R : Type u} [CommRing R]

lemma Ideal.ofList_reverse (rs : List R) : Ideal.ofList rs.reverse = Ideal.ofList rs := by
  simp [Ideal.ofList]

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

section

section

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The linear map `M⧸xM → N⧸xN` induced by `M → N`. -/
def quotSMulTopLinearMap (x : R) (f : M →ₗ[R] N) : QuotSMulTop x M →ₗ[R] QuotSMulTop x N :=
  Submodule.mapQ _ _ f (fun m hm ↦ by
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm with ⟨m', _, hm'⟩
    simpa [← hm'] using Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)

/-- The linear equivalence `M⧸xM ≃ N⧸xN` induced by `M ≃ N`. -/
def quotSMulTopLinearEquiv (x : R) (e : M ≃ₗ[R] N) : (QuotSMulTop x M) ≃ₗ[R] (QuotSMulTop x N) where
  __ := quotSMulTopLinearMap x e.toLinearMap
  invFun := quotSMulTopLinearMap x e.symm.toLinearMap
  left_inv y := by
    induction y using Submodule.Quotient.induction_on
    simp [quotSMulTopLinearMap]
  right_inv y := by
    induction y using Submodule.Quotient.induction_on
    simp [quotSMulTopLinearMap]

variable (M) in
/-- The linear equivalence `M⧸(r1. ... rk, a)M ≃ M ⧸ (r1. ... rk)M ⧸ a • ⊤`. -/
def Submodule.quotOfListSMulTopEquivQuotSMulTopOuter {rs rs' : List R} {a : R}
    (eq : rs = rs' ++ [a]) : (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≃ₗ[R]
    QuotSMulTop a (M ⧸ Ideal.ofList rs' • (⊤ : Submodule R M)) :=
  ((Submodule.quotEquivOfEq _ _ (by simp [eq, sup_comm, Ideal.ofList_reverse])).trans
    (Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M a rs'.reverse)).trans
    (quotSMulTopLinearEquiv a (Submodule.quotEquivOfEq _ _ (by simp [Ideal.ofList_reverse])))

/-- The linear equivalence `R⧸(r1. ... rk, a) ≃ R ⧸ (r1. ... rk) ⧸ a • ⊤`. -/
def Ideal.quotOfListSMulTopEquivQuotSMulTopOuter {rs rs' : List R} {a : R}
    (eq : rs = rs' ++ [a]) : (R ⧸ Ideal.ofList rs) ≃ₗ[R]
    QuotSMulTop a (R ⧸ Ideal.ofList rs') :=
    ((Submodule.quotEquivOfEq _ _ (by simp)).trans
    (Submodule.quotOfListSMulTopEquivQuotSMulTopOuter R eq)).trans
    (quotSMulTopLinearEquiv a (Submodule.quotEquivOfEq _ _ (by simp)))

end

variable [Small.{v} R]

open Pointwise

set_option backward.isDefEq.respectTransparency false in
/-- If `M` has projective dimension not exceeding `n`, for an `M`-regular element `a`,
the linear equivalence `Ext M N n ⧸ a • ⊤ ≃ Ext M⧸xM N (n + 1)` induced by the long exact sequence
`Ext M N n → Ext M N n → Ext M⧸xM N (n + 1) → 0` with first morphism scalar multiple by `a`. -/
noncomputable def quotSMulTop_ext_equiv_ext_quotSMulTop (M : ModuleCat.{v} R) (n : ℕ)
    [HasProjectiveDimensionLE M n] (a : R) (reg : IsSMulRegular M a) (N : ModuleCat.{v} R) :
    QuotSMulTop a (Ext M N n) ≃ₗ[R] Ext (ModuleCat.of R (QuotSMulTop a M)) N (n + 1) := by
  let S := M.smulShortComplex a
  have S_exact : S.ShortExact := reg.smulShortComplex_shortExact
  let f : Ext M N n →ₗ[R] Ext (ModuleCat.of R (QuotSMulTop a M)) N (n + 1) := {
    toFun := S_exact.extClass.precomp N (add_comm 1 n)
    map_add' := by simp
    map_smul' := by simp } --here need set false
  have surj : Function.Surjective f := by
    have exac := Ext.contravariant_sequence_exact₃' S_exact N n (n + 1) (add_comm 1 n)
    have : Subsingleton (Ext M N (n + 1)) :=
      HasProjectiveDimensionLT.subsingleton M (n + 1) (n + 1) (le_refl _) N
    exact (AddCommGrpCat.epi_iff_surjective _).mp
      (exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ this).eq_zero_of_tgt _))
  have ker : LinearMap.ker f = a • (⊤ : Submodule R _) := by
    have exac := Ext.contravariant_sequence_exact₁' S_exact N n (n + 1) (add_comm 1 n)
    have exac' : Function.Exact (a • LinearMap.id (R := R) (M := (Ext M N n))) f := by
      convert (ShortComplex.ab_exact_iff_function_exact _).mp exac
      ext x
      simp only [S, M.smulShortComplex_f_eq_smul_id]
      simp [ModuleCat.smulShortComplex, Ext.mk₀_smul]
    rw [LinearMap.exact_iff.mp exac']
    ext y
    simp [Submodule.mem_smul_pointwise_iff_exists]
  exact (Submodule.quotEquivOfEq _ _ ker.symm).trans (f.quotKerEquivOfSurjective surj)

set_option backward.isDefEq.respectTransparency false in
/-- The linear equivalence `Ext (R⧸(r1, ... rk)) M k ≃ M⧸(r1, ... rk)M` for `R`-regular sequence
`(r1, ... rk)`, this is a special case of a more general result for Koszul complex. -/
noncomputable def ext_quotient_regular_sequence_length [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsRegular R rs) :
    (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M rs.length) ≃ₗ[R]
    M ⧸ Ideal.ofList rs • (⊤ : Submodule R M) := by
  generalize len : rs.length = n
  induction n generalizing rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    let e₀ := (Shrink.linearEquiv R (R ⧸ (⊥ : Ideal R))).trans
      (AlgEquiv.quotientBot R R).toLinearEquiv
    exact ((Ext.linearEquiv₀.trans (ModuleCat.homLinearEquiv.trans (e₀.congrLeft M R))).trans
      (LinearMap.ringLmapEquivSelf R R M)).trans (Submodule.quotEquivOfEqBot ⊥ rfl).symm
  · rename_i n hn
    let a := rs[n]
    let rs' := rs.take n
    have mem_max : ∀ x ∈ rs, x ∈ maximalIdeal R := by
      intro x hx
      apply IsLocalRing.le_maximalIdeal reg.2.symm
      simpa using (Ideal.mem_span x).mpr fun p a ↦ a hx
    have mem_max' : ∀ x ∈ rs', x ∈ maximalIdeal R := fun x hx ↦ mem_max x (List.mem_of_mem_take hx)
    have rs'reg : RingTheory.Sequence.IsRegular R rs' := by
      refine ⟨⟨fun i hi ↦ ?_⟩, ?_⟩
      · simp only [List.length_take, len, le_add_iff_nonneg_right, zero_le, inf_of_le_left,
          List.getElem_take, rs'] at hi ⊢
        rw [List.take_take, min_eq_left_of_lt hi]
        exact reg.1.1 i (lt_of_lt_of_eq (Nat.lt_add_right 1 hi) len.symm)
      · simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr mem_max')).symm
    have eqapp : rs = rs' ++ [a] := by simp [rs', a, len]
    have reg' : IsSMulRegular (R ⧸ Ideal.ofList rs' • (⊤ : Submodule R R)) a :=
      reg.1.1 n (lt_of_lt_of_eq (lt_add_one n) len.symm)
    have reg'' : IsSMulRegular (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) a := by
      rw [(Shrink.linearEquiv R _).isSMulRegular_congr, ← Ideal.mul_top (Ideal.ofList rs')]
      simpa using reg'
    let e1' : QuotSMulTop a (Shrink.{v} (R ⧸ Ideal.ofList rs')) ≃ₗ[R]
      (Shrink.{v} (R ⧸ Ideal.ofList rs)) :=
      ((quotSMulTopLinearEquiv a (Shrink.linearEquiv R (R ⧸ Ideal.ofList rs'))).trans
      (Ideal.quotOfListSMulTopEquivQuotSMulTopOuter eqapp).symm).trans (Shrink.linearEquiv R _).symm
    let e1 : Ext (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M (n + 1) ≃ₗ[R]
      Ext (ModuleCat.of R (QuotSMulTop a (Shrink.{v} (R ⧸ Ideal.ofList rs')))) M (n + 1) := {
      __ := (((extFunctor (n + 1)).mapIso e1'.toModuleIso.op).app M).addCommGroupIsoToAddEquiv
      map_smul' r x := by simp [Iso.addCommGroupIsoToAddEquiv] }
    let _ : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) n :=
      have : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) = n := by
        simp [ModuleCat.projectiveDimension_quotient_eq_length rs' rs'reg, rs', len]
      (projectiveDimension_le_iff _ n).mp (le_of_eq this)
    let e2 : QuotSMulTop a (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) M n) ≃ₗ[R]
      Ext (ModuleCat.of R (QuotSMulTop a (Shrink.{v} (R ⧸ Ideal.ofList rs')))) M (n + 1) :=
      quotSMulTop_ext_equiv_ext_quotSMulTop (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs')))
        n a reg'' M
    exact ((e1.trans e2.symm).trans
      (quotSMulTopLinearEquiv a (hn rs' rs'reg (by simp [rs', len])))).trans
      (Submodule.quotOfListSMulTopEquivQuotSMulTopOuter M eqapp).symm

end

section injdim

lemma nontrivial_of_islocalizedModule {S : Submonoid R} {M MS : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup MS] [Module R MS] {f : M →ₗ[R] MS} (isl : IsLocalizedModule S f)
    (h : Nontrivial MS) : Nontrivial M := by
  by_contra!
  absurd h
  exact not_nontrivial_iff_subsingleton.mpr
    (IsLocalizedModule.linearEquiv S f (LocalizedModule.mkLinearMap S M)).subsingleton

section

/-- For `p` a prime ideal disjoint with multiplicative set `S`, the map `S⁻¹M → Mₚ`. -/
noncomputable def isLocalizedModule_map_of_disjoint_map (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (p : Ideal A) [p.IsPrime] {M : Type*} [AddCommGroup M]
    [Module R M] {MS : Type*} [AddCommGroup MS] [Module R MS] (f : M →ₗ[R] MS)
    [IsLocalizedModule S f] [Module A MS] [IsScalarTower R A MS] {Mp : Type*} [AddCommGroup Mp]
    [Module R Mp] (g : M →ₗ[R] Mp) [IsLocalizedModule.AtPrime (p.comap (algebraMap R A)) g]
    [Module A Mp] [IsScalarTower R A Mp] : MS →ₗ[A] Mp :=
  have (s : S) : IsUnit ((algebraMap R (Module.End R Mp)) s.1) :=
    have : s.1 ∈ (p.comap (algebraMap R A)).primeCompl :=
      ((IsLocalization.disjoint_comap_iff S A p).mpr Ideal.IsPrime.ne_top').le_compl_right s.2
    IsLocalizedModule.map_units g ⟨s.1, this⟩
  (IsLocalizedModule.lift S f g this).extendScalarsOfIsLocalization S A

lemma isLocalizedModule_map_of_disjoint (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization S A] (p : Ideal A) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    {MS : Type*} [AddCommGroup MS] [Module R MS] (f : M →ₗ[R] MS) [IsLocalizedModule S f]
    [Module A MS] [IsScalarTower R A MS] {Mp : Type*} [AddCommGroup Mp] [Module R Mp]
    (g : M →ₗ[R] Mp) [IsLocalizedModule.AtPrime (p.comap (algebraMap R A)) g]
    [Module A Mp] [IsScalarTower R A Mp] :
    IsLocalizedModule.AtPrime p (isLocalizedModule_map_of_disjoint_map S A p f g) where
  map_units x := by
    rcases IsLocalization.exists_mk'_eq S x.1 with ⟨r, s, hrs⟩
    rw [← hrs, IsLocalization.mk'_eq_mul_mk'_one, map_mul, ← IsScalarTower.algebraMap_apply]
    apply IsUnit.mul _ ((isUnit_of_invertible (IsLocalization.mk' A 1 s)).map _)
    have nmem : r ∈ (p.comap (algebraMap R A)).primeCompl := by
      by_contra mem
      simp only [Ideal.mem_primeCompl_iff, Ideal.mem_comap, not_not,
        ← IsLocalization.mk'_mem_iff (y := s), hrs] at mem
      exact x.2 mem
    rcases (IsLocalizedModule.map_units g ⟨r, nmem⟩).exists_right_inv with ⟨r', hr'⟩
    rw [isUnit_iff_exists]
    use r'.extendScalarsOfIsLocalization S A
    constructor
    · ext y
      simpa using LinearMap.congr_fun hr' y
    · ext y
      simpa using LinearMap.congr_fun hr' y
  surj y := by
    rcases IsLocalizedModule.surj (p.comap (algebraMap R A)).primeCompl g y with ⟨⟨m, r⟩, hmr⟩
    have mem : (algebraMap R A) r ∈ p.primeCompl := by
      simpa [← Ideal.mem_comap] using Ideal.mem_primeCompl_iff.mp r.2
    use ⟨f m, ⟨(algebraMap R A) r, mem⟩⟩
    simpa [isLocalizedModule_map_of_disjoint_map] using hmr
  exists_of_eq {z1 z2} eq := by
    rcases IsLocalizedModule.surj S f z1 with ⟨⟨m1, r1⟩, hmr1⟩
    rcases IsLocalizedModule.surj S f z2 with ⟨⟨m2, r2⟩, hmr2⟩
    have eq' : (isLocalizedModule_map_of_disjoint_map S A p f g) (r2 • r1 • z1) =
      (isLocalizedModule_map_of_disjoint_map S A p f g) (r1 • r2 • z2) := by
      simp [smul_smul, mul_comm r1 r2, eq]
    simp only [isLocalizedModule_map_of_disjoint_map, hmr1, LinearMap.map_smul_of_tower,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.lift_apply, hmr2] at eq'
    rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower] at eq'
    rcases IsLocalizedModule.exists_of_eq (S := (p.comap (algebraMap R A)).primeCompl) eq' with
      ⟨r3, hr3⟩
    have : (algebraMap R A) (r3 * (r2 * r1).1) ∈ p.primeCompl := by
      rw [map_mul]
      apply mul_mem
      · simpa [← Ideal.mem_comap] using Ideal.mem_primeCompl_iff.mp r3.2
      · simp only [Ideal.mem_primeCompl_iff]
        by_contra mem
        absurd Ideal.eq_top_of_isUnit_mem _ mem (IsLocalization.map_units A (r2 * r1))
        exact Ideal.IsPrime.ne_top'
    use ⟨(algebraMap R A) (r3 * (r2 * r1)), this⟩
    simp only [map_mul, Submonoid.mk_smul]
    nth_rw 2 [mul_comm ((algebraMap R A) r2)]
    simp only [← smul_smul, algebraMap_smul]
    change r3.1 • r2.1 • r1 • z1 = r3.1 • r1.1 • r2 • z2
    rw [hmr1, hmr2, ← map_smul, ← map_smul, ← map_smul, ← map_smul]
    exact LinearMap.congr_arg hr3

variable [Small.{v} R]

instance (S : Submonoid R) : Small.{v} (Localization S) :=
  small_of_surjective Localization.mkHom_surjective

instance (p : Ideal R) [p.IsPrime] : Small.{v} p.ResidueField :=
  small_of_surjective Ideal.Quotient.mk_surjective

private instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

lemma ext_succ_nontrivial_of_eq_of_le [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M]
    {p q : PrimeSpectrum R} (lt : p < q) (eq_of_le : ∀ r : PrimeSpectrum R, p < r → r ≤ q → r = q)
    (i : ℕ) (ntr : Nontrivial (Ext (ModuleCat.of (Localization p.1.primeCompl)
      (Shrink.{v} p.1.ResidueField)) (M.localizedModule p.1.primeCompl) i)) :
    Nontrivial (Ext (ModuleCat.of (Localization q.1.primeCompl)
      (Shrink.{v} q.1.ResidueField)) (M.localizedModule q.1.primeCompl) (i + 1)) := by
  by_contra! sub
  have : Module.Finite (Localization q.1.primeCompl) (M.localizedModule q.1.primeCompl) :=
    Module.Finite.equiv (Shrink.linearEquiv (Localization q.1.primeCompl) _).symm
  let f := (algebraMap R (Localization q.1.primeCompl))
  let Rq := (Localization q.1.primeCompl)
  let Rp := (Localization p.1.primeCompl)
  have disj : Disjoint (q.1.primeCompl : Set R) p.asIdeal := by
    rw [← le_compl_iff_disjoint_left]
    intro r hr
    simpa using le_of_lt lt hr
  let _ : (p.1.map f).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.1.primeCompl _ _ p.2 disj
  have ne : p.1.map f ≠ maximalIdeal (Localization q.1.primeCompl) := by
    by_contra eq
    absurd ne_of_lt lt
    rw [PrimeSpectrum.ext_iff, ← IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq
      p.2 disj, eq, Localization.AtPrime.comap_maximalIdeal]
  have sub' : Subsingleton (Ext (ModuleCat.of (Localization q.1.primeCompl) (Shrink.{v}
    (Localization q.1.primeCompl ⧸ (p.1.map f)))) (M.localizedModule q.1.primeCompl) i) := by
    apply ext_subsingleton_of_all_gt (M.localizedModule q.1.primeCompl) i (p.1.map f) ne
    intro r rgt hr
    have cgt : r.comap f > p.1 := by
      rw [← IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl
        (Localization q.1.primeCompl) p.2 disj]
      apply lt_of_le_of_ne (Ideal.comap_mono (le_of_lt rgt))
      apply ne_of_apply_ne (Ideal.map f)
      rw [IsLocalization.map_comap q.1.primeCompl, IsLocalization.map_comap q.1.primeCompl]
      exact ne_of_lt rgt
    have cle : r.comap f ≤ q.1 := le_of_le_of_eq (Ideal.comap_mono (le_maximalIdeal_of_isPrime r))
        (IsLocalization.AtPrime.comap_maximalIdeal (Localization q.1.primeCompl) q.1)
    have ceq : r.comap f = q.1 := by simp [← eq_of_le ⟨r.comap f, r.comap_isPrime f⟩ cgt cle]
    rw [← IsLocalization.map_comap q.1.primeCompl _ r, ceq,
      Localization.AtPrime.map_eq_maximalIdeal]
    exact sub
  have le' : q.1.primeCompl ≤ p.1.primeCompl := by simpa [Ideal.primeCompl] using le_of_lt lt
  let _ : Algebra Rq Rp := IsLocalization.localizationAlgebraOfSubmonoidLe Rq Rp _ _ le'
  let _ := IsLocalization.localization_isScalarTower_of_submonoid_le Rq Rp _ _ le'
  have isl0 : IsLocalization.AtPrime Rp (p.1.map f) := by
    have : IsLocalization.AtPrime (Localization.AtPrime (p.1.map f)) p.1 := by
      convert IsLocalization.isLocalization_atPrime_localization_atPrime q.1.primeCompl (p.1.map f)
      rw [IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq p.2 disj]
    let e := IsLocalization.algEquiv p.1.primeCompl Rp (Localization.AtPrime (p.1.map f))
    exact IsLocalization.isLocalization_of_algEquiv (p.1.map f).primeCompl (AlgEquiv.ofLinearEquiv
      (e.toLinearEquiv.extendScalarsOfIsLocalization q.1.primeCompl Rq) (by simp) (by simp)).symm
  have : IsLocalizedModule.AtPrime (p.1.map f) (Algebra.linearMap Rq Rp) :=
    (isLocalizedModule_iff_isLocalization' _ _).mpr isl0
  have : IsScalarTower Rq Rp (Shrink.{v, u} p.asIdeal.ResidueField) :=
    Equiv.isScalarTower Rq Rp (equivShrink p.asIdeal.ResidueField).symm
  let f1' := Submodule.toLocalizedQuotient' Rp (p.1.map f).primeCompl (Algebra.linearMap Rq Rp)
    (p.1.map f)
  have eqm : Submodule.localized' Rp (p.1.map f).primeCompl (Algebra.linearMap Rq Rp)
    (p.1.map f) = maximalIdeal Rp := by
    rw [Ideal.localized'_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Localization.AtPrime.map_eq_maximalIdeal]
  let e := ((Submodule.quotEquivOfEq _ _ eqm).restrictScalars Rq).trans
    (Shrink.linearEquiv.{v} Rq _).symm
  let f1 : (ModuleCat.of Rq (Shrink.{v} (Rq ⧸ p.1.map f))) →ₗ[Rq]
      (ModuleCat.of Rp (Shrink.{v} p.1.ResidueField)) :=
      e.toLinearMap.comp (f1'.comp (Shrink.linearEquiv.{v} Rq _).toLinearMap)
  have isl1 : IsLocalizedModule (p.1.map f).primeCompl f1 :=
    have := IsLocalizedModule.of_linearEquiv_right (p.1.map f).primeCompl f1'
      (Shrink.linearEquiv.{v} Rq _)
    IsLocalizedModule.of_linearEquiv (p.1.map f).primeCompl
      (f1'.comp (Shrink.linearEquiv.{v} Rq _).toLinearMap) e
  let : Module Rq (M.localizedModule p.1.primeCompl) :=
    ModuleCat.Algebra.instModuleCarrier
  have : IsScalarTower Rq Rp (M.localizedModule p.asIdeal.primeCompl) :=
    ModuleCat.Algebra.instIsScalarTowerCarrier
  have : IsLocalizedModule.AtPrime ((p.1.map f).comap f)
    (M.localizedModuleMkLinearMap p.1.primeCompl) := by
    convert M.localizedModule_isLocalizedModule p.1.primeCompl
    exact IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq p.2 disj
  have : IsScalarTower R Rq (M.localizedModule p.1.primeCompl) := {
    smul_assoc r s z := by
      nth_rw 2 [← algebraMap_smul Rp r]
      rw [← algebraMap_smul Rp s, smul_smul, Algebra.smul_def, ← algebraMap_smul Rp, map_mul,
        ← IsScalarTower.algebraMap_apply] }
  let f2 : (M.localizedModule q.1.primeCompl) →ₗ[Rq] (M.localizedModule p.asIdeal.primeCompl) :=
    isLocalizedModule_map_of_disjoint_map q.1.primeCompl Rq (p.1.map f)
    (M.localizedModuleMkLinearMap q.1.primeCompl) (M.localizedModuleMkLinearMap p.1.primeCompl)
  have isl2 : IsLocalizedModule (p.1.map f).primeCompl f2 :=
    isLocalizedModule_map_of_disjoint q.1.primeCompl Rq (p.1.map f)
    (M.localizedModuleMkLinearMap q.1.primeCompl) (M.localizedModuleMkLinearMap p.1.primeCompl)
  have isl := Ext.isLocalizedModule' (p.1.map f).primeCompl Rp f1 isl1 f2 isl2 i
  absurd nontrivial_of_islocalizedModule isl ntr
  exact not_nontrivial_iff_subsingleton.mpr sub'

end

variable [Small.{v} R]

section

set_option backward.isDefEq.respectTransparency false in
open associatedPrimes in
lemma supportDim_le_injectiveDimension [IsLocalRing R] [IsNoetherianRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] : supportDim R M ≤ injectiveDimension M := by
  obtain ⟨q, hq⟩ : ∃ q : LTSeries (Module.support R M), q.length = supportDim R M := by
    have : Nonempty (support R M) := Set.Nonempty.to_subtype nonempty_support_of_nontrivial
    have (n : ℕ) : (n : WithBot ℕ∞) = (n : ℕ∞) := rfl
    simp only [this, supportDim, Order.krullDim_eq_iSup_length, WithBot.coe_inj]
    apply ENat.exists_eq_iSup_of_lt_top
    rw [← WithBot.coe_lt_coe, ← Order.krullDim_eq_iSup_length, WithBot.coe_top, lt_top_iff_ne_top]
    apply ne_top_of_le_ne_top ringKrullDim_ne_top (Module.supportDim_le_ringKrullDim R M)
  have eq_of_le (i : Fin q.length) :
    ∀ r : PrimeSpectrum R, q i.castSucc < r → r ≤ q i.succ → r = q i.succ := by
    intro r ltr rle
    by_contra ne
    let q' := q.insertNth i ⟨r, Module.mem_support_mono (le_of_lt ltr) (q i.castSucc).2⟩ ltr
      (lt_of_le_of_ne rle ne)
    have : q'.length > q.length := by simp [q']
    absurd this
    simp only [gt_iff_lt, not_lt, ← Nat.cast_le (α := WithBot ℕ∞),
      hq, supportDim, Order.krullDim]
    exact le_iSup_iff.mpr fun b a ↦ a q'
  have tail_eq : (q ⟨q.length, lt_add_one q.length⟩).1.1 = maximalIdeal R := by
    by_contra! ne
    have := (q ⟨q.length, lt_add_one q.length⟩).1.2
    have lt := ne.lt_of_le (IsLocalRing.le_maximalIdeal_of_isPrime _)
    let q' := q.snoc ⟨IsLocalRing.closedPoint R, closedPoint_mem_support R M⟩ lt
    have : q'.length > q.length := by simp [q']
    absurd this
    simp only [gt_iff_lt, not_lt, ← Nat.cast_le (α := WithBot ℕ∞),
      hq, supportDim, Order.krullDim]
    exact le_iSup_iff.mpr fun b a ↦ a q'
  have head_min : (q 0).1.1 ∈ (Module.annihilator R M).minimalPrimes := by
    rcases Ideal.exists_minimalPrimes_le (annihilator_le_of_mem_support (q 0).2) with ⟨p, min, ple⟩
    rcases lt_or_eq_of_le ple with lt|eq
    · have pp : p.IsPrime := Ideal.minimalPrimes_isPrime min
      have : ⟨p, pp⟩ ∈ Module.support R M := by
        simpa [Module.mem_support_iff_of_finite] using min.1.2
      let q' := q.cons ⟨⟨p, pp⟩, this⟩ lt
      have : q'.length > q.length := by simp [q']
      absurd this
      simp only [gt_iff_lt, not_lt, ← Nat.cast_le (α := WithBot ℕ∞),
        hq, supportDim, Order.krullDim]
      exact le_iSup_iff.mpr fun b a ↦ a q'
    · simpa [← eq] using min
  have lem' (i : ℕ) (h : i ≤ q.length) : Nontrivial (Ext.{v}
    (ModuleCat.of (Localization (q.toFun ⟨i, Nat.lt_succ_iff.mpr h⟩).1.1.primeCompl)
      (Shrink.{v, u} (q.toFun ⟨i, Nat.lt_succ_iff.mpr h⟩).1.1.ResidueField))
    (M.localizedModule (q.toFun ⟨i, Nat.lt_succ_iff.mpr h⟩).1.1.primeCompl) i) := by
    induction i
    · simp only [Fin.zero_eta, Ext.homEquiv₀.nontrivial_congr, ModuleCat.localizedModule]
      rw [ModuleCat.homAddEquiv.nontrivial_congr, ((Shrink.linearEquiv.{v} _ _).congrLeft _
        (Localization (q 0).1.1.primeCompl)).nontrivial_congr,
        (Shrink.linearEquiv.{v} _ _).congrRight.nontrivial_congr]
      have ass := minimalPrimes_annihilator_subset_associatedPrimes R M head_min
      simp only [AssociatedPrimes.mem_iff] at ass
      have := mem_associatedPrimes_atPrime_of_mem_associatedPrimes ass
      simp only [AssociatedPrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at this
      rcases this with ⟨_, f, hf⟩
      exact nontrivial_of_ne f 0  (LinearMap.ne_zero_of_injective hf)
    · rename_i i ih
      exact ext_succ_nontrivial_of_eq_of_le M (q.step ⟨i, h⟩) (eq_of_le ⟨i, h⟩) i
        (ih (Nat.le_of_succ_le h))
  have ntr : Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R))) M
    q.length) := by
    let qq := q ⟨q.length, Nat.lt_succ_iff.mpr (le_refl q.length)⟩
    have qqeq : qq.1.1 = maximalIdeal R := tail_eq
    have ntr' : Nontrivial (Ext.{v} (ModuleCat.of (Localization qq.1.1.primeCompl)
      (Shrink.{v} qq.1.1.ResidueField)) (M.localizedModule qq.1.1.primeCompl) q.length) :=
      lem' q.length (le_refl _)
    have : IsScalarTower R (Localization qq.1.1.primeCompl) (Shrink.{v} qq.1.1.ResidueField) :=
      Equiv.isScalarTower R (Localization qq.1.1.primeCompl) (equivShrink qq.1.1.ResidueField).symm
    have : IsLocalization qq.1.1.primeCompl R :=
      IsLocalization.of_le_isUnit (fun x hx ↦ by simpa [qqeq] using hx)
    have surj : Function.Surjective (algebraMap R (Localization qq.1.1.primeCompl)) :=
      (IsLocalization.bijective qq.1.1.primeCompl
        (algebraMap R (Localization qq.1.1.primeCompl)) rfl).2
    have : IsLocalHom (algebraMap R (Localization qq.1.1.primeCompl)) :=
      IsLocalHom.of_surjective _ surj
    let e' : (R ⧸ maximalIdeal R) →ₗ[R] qq.1.1.ResidueField :=
      { __ := ResidueField.map (algebraMap R (Localization qq.1.1.primeCompl))
        map_smul' r x := by
          simp only [RingHom.toMonoidHom_eq_coe, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
            OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, map_mul,
            RingHom.id_apply, mul_eq_mul_right_iff, map_eq_zero]
          left
          rw [IsScalarTower.algebraMap_eq R (Localization qq.1.1.primeCompl) qq.1.1.ResidueField,
            ResidueField.algebraMap_eq, ← ResidueField.map_comp_residue]
          rfl }
    have bij : Function.Bijective e' :=
      ResidueField.map_bijective_of_surjective _ surj
    let e : (R ⧸ maximalIdeal R) ≃ₗ[R] qq.1.1.ResidueField :=
      LinearEquiv.ofBijective e' bij
    let f : ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R)) ≃ₗ[R]
      (ModuleCat.of (Localization qq.1.1.primeCompl) (Shrink.{v, u} qq.1.1.ResidueField)) :=
      ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).trans e).trans
        (Shrink.linearEquiv R qq.1.1.ResidueField).symm
    have isl1 : IsLocalizedModule qq.1.1.primeCompl f.toLinearMap := by
      have := isLocalizedModule_id qq.1.1.primeCompl (Shrink.{v} (R ⧸ maximalIdeal R)) R
      exact IsLocalizedModule.of_linearEquiv qq.1.1.primeCompl LinearMap.id f
    have isl := Ext.isLocalizedModule' qq.1.1.primeCompl
      (Localization qq.1.1.primeCompl) f.toLinearMap isl1
      (M.localizedModuleMkLinearMap qq.1.1.primeCompl)
      (M.localizedModule_isLocalizedModule qq.1.1.primeCompl) q.length
    exact nontrivial_of_islocalizedModule isl ntr'
  simp only [← hq, injectiveDimension_eq_sInf_of_finite.{v} M, le_sInf_iff, Set.mem_setOf_eq]
  intro b hb
  by_contra! lt
  exact (not_subsingleton_iff_nontrivial.mpr ntr) (hb q.length lt)

end

open Limits in
lemma injectiveDimension_eq_depth [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) (h : injectiveDimension M ≠ ⊤) [Module.Finite R M] [Nontrivial M] :
    injectiveDimension M = IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by
  let := Module.Finite.equiv (Shrink.linearEquiv R R).symm
  have lttop := depth_ne_top (ModuleCat.of R (Shrink.{v} R))
  rw [IsLocalRing.depth_eq_sSup_length_regular (ModuleCat.of R (Shrink.{v} R))] at lttop ⊢
  obtain ⟨rs, reg', mem, len⟩ := @ENat.sSup_mem_of_nonempty_of_lt_top _ (by
    use 0, []
    simpa using IsRegular.nil _ _) lttop.symm.lt_top'
  rw [← len]
  have reg : IsRegular R rs := ((Shrink.linearEquiv.{v} R R).isRegular_congr rs).mp reg'
  apply le_antisymm
  · obtain ⟨r, hr⟩ : ∃ n : ℕ, injectiveDimension M = n := by
      generalize hd : injectiveDimension M = d
      induction d with
      | bot =>
        absurd not_nontrivial_iff_subsingleton.mpr
          (ModuleCat.isZero_iff_subsingleton.mp ((injectiveDimension_eq_bot_iff M).mp hd))
        assumption
      | coe d =>
        induction d with
        | top => simp [hd] at h
        | coe d =>
          use d
          rfl
    rw [hr]
    apply Nat.cast_le.mpr
    have projdim : projectiveDimension (ModuleCat.of R
      ((Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)))) = rs.length := by
      simp [ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
        (ModuleCat.of R (Shrink.{v} R)) rs reg'.1 mem,
        ModuleCat.projectiveDimension_eq_zero_of_projective]
    have ntr : Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M r) := by
      by_contra! sub
      have (i : ℕ) (lt : r < i) :
        Subsingleton (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i) :=
        ((injectiveDimension_le_iff _ r).mp (le_of_eq hr)).subsingleton M (r + 1) i lt _
      have injle := (injectiveDimension_le_iff _ r).mp (le_of_eq hr)
      match r with
      | 0 =>
        have : injectiveDimension M ≤ ⊥ := by
          rw [injectiveDimension_eq_sInf_of_finite.{v} M]
          apply sInf_le
          intro i _
          match i with
          | 0 => exact sub
          | i + 1 => exact this (i + 1) (Nat.zero_lt_succ i)
        simp [hr] at this
      | s + 1 =>
        have : injectiveDimension M ≤ s := by
          rw [injectiveDimension_eq_sInf_of_finite.{v} M]
          apply sInf_le
          intro i hi
          have le : s + 1 ≤ i := Nat.cast_lt.mp hi
          rcases eq_or_lt_of_le le with eq|lt
          · simpa [← eq] using sub
          · exact this i lt
        rw [hr, Nat.cast_le] at this
        simp at this
    by_contra! lt
    have := projectiveDimension_lt_iff.mp (lt_of_eq_of_lt projdim (Nat.cast_lt.mpr lt))
    have sub := HasProjectiveDimensionLT.subsingleton.{v} (ModuleCat.of R
      ((Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)))) r r (le_refl r) M
    absurd not_nontrivial_iff_subsingleton.mpr sub
    have depth_zero : IsLocalRing.depth (ModuleCat.of R
      ((Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)))) = 0 := by
      have := depth_quotient_regular_sequence_add_length_eq_depth (ModuleCat.of R (Shrink.{v} R))
        rs reg'
      rw [IsLocalRing.depth_eq_sSup_length_regular (ModuleCat.of R (Shrink.{v} R)), ← len] at this
      nth_rw 2 [← zero_add (rs.length : ℕ∞)] at this
      exact (WithTop.add_right_inj (ENat.coe_ne_top rs.length)).mp this
    have := (moduleDepth_eq_zero_of_hom_nontrivial _ _).mp depth_zero
    rcases (nontrivial_iff_exists_ne 0).mp this with ⟨f, hf⟩
    have injf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      by_contra ne
      absurd hf
      ext y
      let e := Shrink.algEquiv R (R ⧸ maximalIdeal R)
      let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
      calc
      _ = f (e.symm (e y * (e x)⁻¹ * (e x))) := by
        simp [AddEquivClass.map_ne_zero_iff.mpr ne]
      _ = _ := by
        rcases Ideal.Quotient.mk_surjective (e y * (e x)⁻¹) with ⟨r, hr⟩
        rw [← hr, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]
        simp [LinearMap.mem_ker.mp hx]
    let g : ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)) ⟶
      ModuleCat.of R (Shrink.{v} R ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R))) :=
      ModuleCat.ofHom f
    let S := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_cokernel g
      mono_f := (ModuleCat.mono_iff_injective g).mpr injf }
    have exac := Ext.contravariant_sequence_exact₁'.{v} S_exact M r (r + 1) (add_comm 1 r)
    have : IsZero (AddCommGrpCat.of (Ext.{v} S.X₃ M (r + 1))) := by
      apply @AddCommGrpCat.isZero_of_subsingleton _ ?_
      have := (injectiveDimension_le_iff M r).mp (le_of_eq hr)
      exact HasInjectiveDimensionLT.subsingleton M (r + 1) (r + 1) (le_refl _) _
    have surj : Function.Surjective ((Ext.mk₀.{v} S.f).precomp M (zero_add r)) :=
      (AddCommGrpCat.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
    exact surj.nontrivial
  · simp only [injectiveDimension, le_sInf_iff, Set.mem_setOf_eq]
    intro b hb
    by_contra! lt
    have := hb rs.length lt
    absurd HasInjectiveDimensionLT.subsingleton.{v} M rs.length rs.length (le_refl _)
      (ModuleCat.of R (Shrink.{v, u} (R ⧸ Ideal.ofList rs)))
    apply not_subsingleton_iff_nontrivial.mpr
    rw [(ext_quotient_regular_sequence_length M rs reg).nontrivial_congr]
    apply Submodule.Quotient.nontrivial_iff.mpr
    apply (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator _).symm
    exact le_trans (Ideal.span_le.mpr mem) (maximalIdeal_le_jacobson _)

end injdim

section

variable (R) [IsLocalRing R] [IsNoetherianRing R]

theorem isCohenMacaulayLocalRing_of_isGorensteinLocalRing [IsGorensteinLocalRing R] :
    IsCohenMacaulayLocalRing R := by
  have := (isGorensteinLocalRing_def R).mp ‹_›
  have eq := injectiveDimension_eq_depth (ModuleCat.of R R) this
  have le := supportDim_le_injectiveDimension (ModuleCat.of R R)
  rw [Module.supportDim_self_eq_ringKrullDim, eq] at le
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth R (le_of_le_of_eq le _)
  simp [IsLocalRing.depth_eq_of_iso (Shrink.linearEquiv.{u} R R).toModuleIso]

theorem injectiveDimension_eq_ringKrullDim_of_isGorensteinLocalRing [IsGorensteinLocalRing R] :
    injectiveDimension (ModuleCat.of R R) = ringKrullDim R := by
  have gor := (isGorensteinLocalRing_def R).mp ‹_›
  have le := supportDim_le_injectiveDimension (ModuleCat.of R R)
  rw [Module.supportDim_self_eq_ringKrullDim] at le
  have le' := depth_le_ringKrullDim (ModuleCat.of R R)
  rw [← IsLocalRing.depth_eq_of_iso (Shrink.linearEquiv.{u} R R).toModuleIso,
    ← injectiveDimension_eq_depth (ModuleCat.of R R) gor] at le'
  exact le_antisymm le' le

lemma add_one_eq_top_iff (a : WithBot ℕ∞) : a + 1 = ⊤ ↔ a = ⊤ := by
  induction a with
  | bot => rfl
  | coe n =>
    induction n with
    | top => rfl
    | coe n =>
      simpa [- ENat.WithBot.coe_eq_natCast] using WithBot.coe_inj.not.mpr (ENat.coe_ne_top (n + 1))

set_option backward.isDefEq.respectTransparency false in
lemma injectiveDimension_quotient_span_regular
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    injectiveDimension (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) + 1 =
    injectiveDimension (ModuleCat.of R R) := by
  let e : (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x R)) ≅
    (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) :=
    { __ := Submodule.quotEquivOfEq _ (Ideal.span {x}) (by
        simp [← Submodule.ideal_span_singleton_smul])
      map_smul' r y := by
        rcases Ideal.Quotient.mk_surjective r with ⟨s, rfl⟩
        exact map_smul (Submodule.quotEquivOfEq _ _ _) s y }.toModuleIso
  rw [← injectiveDimension_quotSMulTop_succ_eq_injectiveDimension reg reg mem,
    injectiveDimension_eq_of_iso e]

open Pointwise in
lemma quotient_span_regular_isGorenstein_iff_isGorenstein
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    IsGorensteinLocalRing R ↔ IsGorensteinLocalRing (R ⧸ Ideal.span {x}) := by
  have : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  rw [isGorensteinLocalRing_def, isGorensteinLocalRing_def,
    ← injectiveDimension_quotient_span_regular R x reg mem]
  exact (add_one_eq_top_iff _).not

set_option backward.isDefEq.respectTransparency false in
open Ideal in
lemma quotient_regular_isGorenstein_iff_isGorenstein (rs : List R) (reg : IsRegular R rs) :
    IsGorensteinLocalRing R ↔ IsGorensteinLocalRing (R ⧸ Ideal.ofList rs) := by
  generalize h : rs.length = n
  induction n generalizing R rs with
  | zero =>
    rw [List.length_eq_zero_iff.mp h, Ideal.ofList_nil]
    exact ⟨fun h ↦ IsGorensteinLocalRing.of_ringEquiv (RingEquiv.quotientBot R).symm,
      fun h ↦ IsGorensteinLocalRing.of_ringEquiv (RingEquiv.quotientBot R)⟩
  | succ n ih =>
    match rs with
    | [] => simp at h
    | a :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have mem : a ∈ maximalIdeal R := by
        simp only [mem_maximalIdeal, mem_nonunits_iff]
        by_contra uni
        have := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton_self a) uni
        absurd reg.2.symm
        simp [this]
      let e : QuotSMulTop a R ≃ₗ[R ⧸ Ideal.span {a}] R ⧸ Ideal.span {a} :=
        (Submodule.quotEquivOfEq _ (Ideal.span {a})
          (by simp [← Submodule.ideal_span_singleton_smul])).extendScalarsOfSurjective
            Ideal.Quotient.mk_surjective
      simp only [isRegular_cons_iff', e.isRegular_congr] at reg
      have : Nontrivial (R ⧸ Ideal.span {a}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by simpa using mem)
      have : IsLocalRing (R ⧸ Ideal.span {a}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {a})) Ideal.Quotient.mk_surjective
      rw [quotient_span_regular_isGorenstein_iff_isGorenstein R a reg.1 mem,
        ih (R ⧸ Ideal.span {a}) _ reg.2 (by simp [h]), ← Ideal.map_ofList, Ideal.ofList_cons]
      let e' := DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.ofList rs')
      exact ⟨fun h ↦ IsGorensteinLocalRing.of_ringEquiv e',
        fun h ↦ IsGorensteinLocalRing.of_ringEquiv e'.symm⟩

end

section

variable [IsLocalRing R] [IsNoetherianRing R]

lemma exists_isPrime_no_insert (p : Ideal R) [p.IsPrime] (lt : p < maximalIdeal R) :
    ∃ q, q.IsPrime ∧ p ≤ q ∧ q < maximalIdeal R ∧
      (∀ r, r.IsPrime → q < r → r = maximalIdeal R) := by
  let S : Set (Ideal R) := {q | q.IsPrime ∧ p ≤ q ∧ q < maximalIdeal R}
  rcases set_has_maximal_iff_noetherian.mpr ‹_› S ⟨p, by simpa [S] using ⟨‹_›, lt⟩⟩ with ⟨q, hq⟩
  use q
  refine ⟨hq.1.1, hq.1.2.1, hq.1.2.2, fun r rp qlt ↦ ?_⟩
  by_contra ne
  absurd qlt
  exact hq.2 r ⟨rp, hq.1.2.1.trans qlt.le, lt_of_le_of_ne (le_maximalIdeal_of_isPrime r) ne⟩

lemma residueField_ext_subsingleton_of_no_insert (p : Ideal R) [p.IsPrime] (lt : p < maximalIdeal R)
    (h : ∀ q, q.IsPrime → p < q → q = maximalIdeal R) (k l : ℕ) (eq : l = k + 1)
    (sub : Subsingleton (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) l)) :
    Subsingleton (Ext (ModuleCat.of (Localization.AtPrime p) p.ResidueField)
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) k) := by
  have : Subsingleton (Ext (ModuleCat.of R (R ⧸ p)) (ModuleCat.of R R) k) := by
    let e (I : Ideal R) : (ModuleCat.of R (Shrink.{u, u} (R ⧸ I))) ≅ ModuleCat.of R (R ⧸ I) :=
      (Shrink.linearEquiv _ _).toModuleIso
    apply (((extFunctor k).mapIso (e p).op).app
        (ModuleCat.of R R)).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
    apply ext_subsingleton_of_all_gt (ModuleCat.of R R) k p lt.ne
    intro q qgt qp
    rw [h q qp qgt, ← eq]
    exact (((extFunctor l).mapIso (e (maximalIdeal R)).op).app
      (ModuleCat.of R R)).addCommGroupIsoToAddEquiv.subsingleton_congr.mp sub
  let Rp := Localization.AtPrime p
  let f := Submodule.toLocalizedQuotient' Rp p.primeCompl (Algebra.linearMap R Rp) p
  have eqm : Submodule.localized' Rp p.primeCompl (Algebra.linearMap R Rp) p = maximalIdeal Rp := by
    rw [Ideal.localized'_eq_map, Localization.AtPrime.map_eq_maximalIdeal]
  let g : (ModuleCat.of R (R ⧸ p)) →ₗ[R] (ModuleCat.of Rp p.ResidueField) :=
    ((Submodule.quotEquivOfEq _ _ eqm).restrictScalars R).comp f
  have : IsLocalizedModule.AtPrime p g :=
    IsLocalizedModule.of_linearEquiv p.primeCompl f _
  let h : (ModuleCat.of R R) →ₗ[R] (ModuleCat.of Rp Rp) := Algebra.linearMap R Rp
  have isl := Ext.isLocalizedModule' p.primeCompl (Localization.AtPrime p) g
    (IsLocalizedModule.of_linearEquiv p.primeCompl f _) h inferInstance k
  exact isl.subsingleton_of_subsingleton

lemma Module.length_ne_top_of_support_subset (M : Type*) [AddCommGroup M] [Module R M]
    [fin : Module.Finite R M] (h : support R M ⊆ {closedPoint R}) : Module.length R M ≠ ⊤ := by
  induction fin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime with
  | subsingleton N => simp
  | quotient N p e =>
    simp only [e.support_eq, support_eq_zeroLocus, Ideal.annihilator_quotient,
      Set.subset_singleton_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h
    have : IsSimpleModule R (R ⧸ p.1) := isSimpleModule_iff_isCoatom.mpr (by
      simpa [p.ext_iff.mp (h p (le_refl _)), closedPoint] using (maximalIdeal.isMaximal R).out)
    simp [e.length_eq]
  | exact N₁ N₂ N₃ f g inj surj exac ih1 ih3 =>
    simp only [Module.support_of_exact exac inj surj, Set.union_subset_iff] at h
    rw [Module.length_eq_add_of_exact f g inj surj exac, ← ENat.coe_toNat_eq_self.mpr (ih1 h.1),
      ← ENat.coe_toNat_eq_self.mpr (ih3 h.2), ← Nat.cast_add]
    exact ENat.coe_ne_top _

omit [IsLocalRing R] in
lemma LinearMap.surjective_of_injective_of_length_ne_top (M : Type*) [AddCommGroup M] [Module R M]
    [fin : Module.Finite R M] (ne : Module.length R M ≠ ⊤)
    (f : M →ₗ[R] M) (inj : Function.Injective f) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  by_contra netop
  have : IsFiniteLength R M := length_ne_top_iff.mp ne
  have : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp ‹_›).2
  absurd not_le.mpr (Submodule.length_lt netop)
  exact Module.length_le_of_injective f.rangeRestrict ((injective_rangeRestrict_iff f).mpr inj)

set_option backward.isDefEq.respectTransparency false in
lemma isGorensteinLocalRing_of_exists (k : ℕ) (gt : ringKrullDim R < k)
    (h : Subsingleton (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) k)) :
    IsGorensteinLocalRing R := by
  obtain ⟨n, hn⟩ := exist_nat_eq' R
  let e (I : Ideal R) : (ModuleCat.of R (Shrink.{u, u} (R ⧸ I))) ≅
    ModuleCat.of R (R ⧸ I) := (Shrink.linearEquiv _ _).toModuleIso
  induction n using Nat.case_strong_induction_on generalizing R k with
  | hz =>
    have : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hn
    have injlt : HasInjectiveDimensionLT (ModuleCat.of R R) k := by
      apply ModuleCat.hasInjectiveDimensionLT_of_quotients _ _ (fun I ↦ ?_)
      apply ext_subsingleton_of_support_subset _ _ k (fun p hp ↦ ?_)
      rw [Set.mem_setOf_eq, Ring.KrullDimLE.eq_maximalIdeal_of_isPrime p.1]
      exact (((extFunctor k).mapIso (e (maximalIdeal R)).op).app
        (ModuleCat.of R R)).addCommGroupIsoToAddEquiv.subsingleton_congr.mp h
    exact (isGorensteinLocalRing_def R).mpr (ne_top_of_lt (injectiveDimension_lt_iff.mpr injlt))
  | hi n ih =>
    have supp_le (M : ModuleCat.{u} R) [Module.Finite R M] :
      Module.support R (Ext M (ModuleCat.of R R) k) ⊆ {closedPoint R} := by
      intro p hp
      by_contra ne
      have ltm : p.1 < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal_of_isPrime p.1) (by
        simpa [PrimeSpectrum.ext_iff, closedPoint] using ne)
      rcases exists_isPrime_no_insert p.1 ltm with ⟨q, qp, ple, qlt, hq⟩
      let Rq := Localization.AtPrime q
      obtain ⟨m, hm⟩ := exist_nat_eq' Rq
      have mle : m ≤ n := by
        rw [← Order.lt_add_one_iff, ← Nat.cast_lt (α := WithBot ℕ∞), ← hm, ← hn,
          IsLocalization.AtPrime.ringKrullDim_eq_height q, Ideal.height_eq_primeHeight,
          ← maximalIdeal_primeHeight_eq_ringKrullDim, WithBot.coe_lt_coe]
        exact Ideal.primeHeight_strict_mono qlt
      simp only [hn, Nat.cast_lt] at gt
      have mlt : m < k - 1 := by omega
      have isg : IsGorensteinLocalRing Rq := by
        apply ih m mle (k - 1) (lt_of_eq_of_lt hm (Nat.cast_lt.mpr mlt)) _ hm
        exact residueField_ext_subsingleton_of_no_insert q qlt hq (k - 1) k (by omega) h
      have injlt : HasInjectiveDimensionLT (ModuleCat.of Rq Rq) k := by
        rw [← injectiveDimension_lt_iff,
          injectiveDimension_eq_ringKrullDim_of_isGorensteinLocalRing, hm, Nat.cast_lt]
        omega
      have qmem : ⟨q, qp⟩ ∈ support R (Ext M (ModuleCat.of R R) k) :=
        Module.mem_support_iff_of_finite.mpr ((Module.mem_support_iff_of_finite.mp hp).trans ple)
      let Mq := ModuleCat.of Rq (LocalizedModule.AtPrime q M)
      let g : M →ₗ[R] Mq := LocalizedModule.mkLinearMap q.primeCompl M
      let h : (ModuleCat.of R R) →ₗ[R] (ModuleCat.of Rq Rq) := Algebra.linearMap R Rq
      have isl := Ext.isLocalizedModule' q.primeCompl Rq g inferInstance h inferInstance k
      have : Subsingleton (Ext Mq (ModuleCat.of Rq Rq) k) := injlt.subsingleton _ k k (le_refl _) Mq
      absurd qmem
      simp only [notMem_support_iff]
      exact (@IsLocalizedModule.linearEquiv R _ q.primeCompl _ _ _ _ _ _ _ _ _
        (LocalizedModule.mkLinearMap q.primeCompl _) _ _ isl).subsingleton
    let S := {p : Ideal R | p.IsPrime ∧
      Nontrivial (Ext (ModuleCat.of R (R ⧸ p)) (ModuleCat.of R R) k)}
    have empty (nept : S.Nonempty) : False := by
      rcases set_has_maximal_iff_noetherian.mpr ‹_› S nept with ⟨p, ⟨_, ntr⟩, hp⟩
      have pne : p ≠ maximalIdeal R := by
        by_contra eq
        rw [eq, ← not_subsingleton_iff_nontrivial] at ntr
        exact ntr h
      have plt : p < maximalIdeal R :=  lt_of_le_of_ne (le_maximalIdeal_of_isPrime p) pne
      obtain ⟨x, hx, nmem⟩ : ∃ x ∈ maximalIdeal R, x ∉ p := Set.exists_of_ssubset plt
      have reg : IsSMulRegular (R ⧸ p) x := by
        refine isSMulRegular_iff_right_eq_zero_of_smul.mpr (fun r hr ↦ ?_)
        simpa [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, nmem] using hr
      have : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x (R ⧸ p))) (ModuleCat.of R R) k) := by
        apply ext_subsingleton_of_support_subset
        intro q hq
        have qnin : q.1 ∉ S := by
          apply (hp q.1).mt
          simp only [support_quotSMulTop, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
            Set.singleton_subset_iff, SetLike.mem_coe, Module.mem_support_iff_of_finite] at hq
          apply not_not.mpr (lt_of_le_of_ne _ (ne_of_mem_of_not_mem' hq.2 nmem).symm)
          exact le_of_eq_of_le Ideal.annihilator_quotient.symm hq.1
        simp only [Set.mem_setOf_eq, q.2, true_and, not_nontrivial_iff_subsingleton, S] at qnin
        exact (((extFunctor k).mapIso (e q.1).op).app
          (ModuleCat.of R R)).addCommGroupIsoToAddEquiv.subsingleton_congr.mp qnin
      let S := (ModuleCat.of R (R ⧸ p)).smulShortComplex x
      have S_exact : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact reg
      have exac := Ext.contravariant_sequence_exact₂' S_exact (ModuleCat.of R R) k
      have mono := exac.mono_g ((@AddCommGrpCat.isZero_of_subsingleton _ this).eq_zero_of_src _)
      have : S.f = x • 𝟙 (ModuleCat.of R (R ⧸ p)) := rfl
      simp only [S, this, AddCommGrpCat.mono_iff_injective, AddCommGrpCat.hom_ofHom] at mono
      simp only [ModuleCat.smulShortComplex] at mono
      have surjx : Function.Surjective
        (x • LinearMap.id (R := R) (M := Ext (ModuleCat.of R (R ⧸ p)) (ModuleCat.of R R) k)) := by
        apply LinearMap.surjective_of_injective_of_length_ne_top _
          (Module.length_ne_top_of_support_subset _ (supp_le _))
        convert mono
        ext y
        simp [Ext.mk₀_smul]
      have : x ∈ (Module.annihilator R (Ext (ModuleCat.of R (R ⧸ p))
        (ModuleCat.of R R) k)).jacobson := maximalIdeal_le_jacobson _ hx
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases surjx y with ⟨z, hz⟩
      simpa [← hz] using Submodule.smul_mem_pointwise_smul z x _ hy
    have ext_zero (p : Ideal R) [p.IsPrime] :
      Subsingleton (Ext (ModuleCat.of R (R ⧸ p)) (ModuleCat.of R R) k) := by
      by_contra! ntr
      exact empty ⟨p, ⟨‹_›, ntr⟩⟩
    have injlt : HasInjectiveDimensionLT (ModuleCat.of R R) k := by
      apply ModuleCat.hasInjectiveDimensionLT_of_quotients _ _ (fun I ↦ ?_)
      apply ext_subsingleton_of_support_subset _ _ k (fun p hp ↦ ?_)
      apply (((extFunctor k).mapIso (e p.1).op).app
        (ModuleCat.of R R)).addCommGroupIsoToAddEquiv.subsingleton_congr.mp (ext_zero p.1)
    exact (isGorensteinLocalRing_def R).mpr (injectiveDimension_lt_iff.mpr injlt).ne_top

end

section

--`Ext` iso quotient regular sequence

variable [Small.{v} R]

lemma extClass_postcomp_surjective (M N : ModuleCat.{v} R) (x : R) (reg : IsSMulRegular M x)
    (mem : x ∈ Module.annihilator R N) {a b : ℕ} (h : a + 1 = b) :
    Function.Surjective (reg.smulShortComplex_shortExact.extClass.postcomp N h) := by
  have epi := (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact a b h).epi_f
    (Ext.smul_id_postcomp_eq_zero_of_mem_annihilator mem b)
  exact (AddCommGrpCat.epi_iff_surjective _).mp epi

lemma ext_subsingleton_of_regualr_sequence (M N : ModuleCat.{v} R) {rs : List R}
    (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ Module.annihilator R N)
    (n : ℕ) (hn : n < rs.length) : Subsingleton (Ext N M n) := by
  induction n generalizing M rs
  · match rs with
    | [] => simp at hn
    | a :: rs' =>
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      rw [Ext.homEquiv₀.subsingleton_congr, ModuleCat.homEquiv.subsingleton_congr]
      exact IsSMulRegular.linearMap_subsingleton_of_mem_annihilator
        ((isWeaklyRegular_cons_iff _ _ _).mp reg).1 mem.1
  · rename_i n ih
    match rs with
    | [] => simp at hn
    | a :: rs' =>
      simp only [List.length_cons, add_lt_add_iff_right] at hn
      have reg' := (isWeaklyRegular_cons_iff _ _ _).mp reg
      have mem' := mem
      simp only [List.mem_cons, forall_eq_or_imp] at mem'
      let _ : Subsingleton (Ext N (M.smulShortComplex a).X₃ n) :=
        ih (ModuleCat.of R (QuotSMulTop a M)) reg'.2 mem'.2 hn
      exact (extClass_postcomp_surjective M N a reg'.1 mem'.1 (rfl : n + 1 = n + 1)).subsingleton

lemma extClass_postcomp_bijective_of_lt (M N : ModuleCat.{v} R) (x : R) (reg : IsSMulRegular M x)
    (mem : x ∈ Module.annihilator R N) {a b : ℕ} (h : a + 1 = b)
    {rs : List R} (reg' : IsWeaklyRegular M rs) (mem' : ∀ r ∈ rs, r ∈ Module.annihilator R N)
    (ltlen : a < rs.length) :
    Function.Bijective (reg.smulShortComplex_shortExact.extClass.postcomp N h) := by
  refine ⟨?_, extClass_postcomp_surjective M N x reg mem h⟩
  let _ : Subsingleton (Ext N (M.smulShortComplex x).X₂ a) :=
    ext_subsingleton_of_regualr_sequence M N reg' mem' a ltlen
  have mono := (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact a b h).mono_g
    (Limits.IsZero.eq_zero_of_src (AddCommGrpCat.isZero_of_subsingleton _) _)
  exact (AddCommGrpCat.mono_iff_injective _).mp mono

/-- For `(r1, ... rk)` an `M`-regular contained in `Ann(N)`, the linear map from
`N →ₗ[R] M⧸(r1, ... rk)` to `Ext N M k` defined by compostion of connection maps in
long exact sequence of `Ext`. -/
noncomputable def QuotientRegularSequenceToExt (M N : ModuleCat.{v} R) {rs : List R}
    (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    (N →ₗ[R] M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) →ₗ[R] Ext N M rs.length :=
  match rs with
  | [] => List.length_nil ▸
    ((Submodule.quotEquivOfEqBot (Ideal.ofList [] • ⊤ : Submodule R M) (by simp)).congrRight.trans
      (ModuleCat.homLinearEquiv.symm.trans Ext.linearEquiv₀.symm)).toLinearMap
  | a :: rs' =>
    (((isWeaklyRegular_cons_iff _ a rs').mp
      reg).1.smulShortComplex_shortExact.extClass.postcompOfLinear R N
      (rs'.length_cons.symm)).comp
      ((QuotientRegularSequenceToExt (ModuleCat.of R (QuotSMulTop a M)) N
      ((isWeaklyRegular_cons_iff _ a rs').mp reg).2
      (fun r hr ↦ mem r (List.mem_cons_of_mem a hr))).comp
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a rs').congrRight.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
lemma quotientRegularSequenceToExt_bijective (M N : ModuleCat.{v} R) {rs : List R}
    (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    Function.Bijective (QuotientRegularSequenceToExt M N reg mem) := by
  match rs with
  | [] =>
    exact LinearEquiv.bijective _
  | a :: rs' =>
    simp only [List.length_cons, QuotientRegularSequenceToExt, ModuleCat.smulShortComplex,
      LinearMap.coe_comp]
    have reg' := (isWeaklyRegular_cons_iff _ _ _).mp reg
    have mem' := mem
    simp only [List.mem_cons, forall_eq_or_imp] at mem'
    apply Function.Bijective.comp _
    · apply Function.Bijective.comp _ (LinearEquiv.bijective _)
      exact quotientRegularSequenceToExt_bijective
        (ModuleCat.of R (QuotSMulTop a M)) N reg'.2 mem'.2
    · exact extClass_postcomp_bijective_of_lt M N a reg'.1 mem'.1
        (rs'.length_cons (a := a)).symm reg mem (by simp)

/-- The linear equivalence obtained from the bijectivity of `QuotientRegularSequenceToExt`. -/
noncomputable def ExtEquivQuotientRegularSequence (M N : ModuleCat.{v} R) {rs : List R}
    (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    Ext N M rs.length ≃ₗ[R] (N →ₗ[R] M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) :=
  (LinearEquiv.ofBijective (QuotientRegularSequenceToExt M N reg mem)
    (quotientRegularSequenceToExt_bijective M N reg mem)).symm

end

section

/-- An ideal `I` is irreducible if intersection of two ideals equals `I`
implies one of them exactly being `I`. -/
class Ideal.isIrreducible (I : Ideal R) : Prop where
  irr : ∀ {J₁ J₂ : Ideal R}, J₁ ⊓ J₂ = I → (J₁ = I ∨ J₂ = I)

lemma Ideal.irreducible_iff_bot_irreducible (J : Ideal R) :
    J.isIrreducible ↔ (⊥ : Ideal (R ⧸ J)).isIrreducible := by
  refine ⟨fun h ↦ ⟨fun {I₁ I₂} eq ↦ ?_⟩, fun h ↦ ⟨fun {I₁ I₂} eq ↦ ?_⟩⟩
  · have : I₁.comap (Ideal.Quotient.mk J) ⊓ I₂.comap (Ideal.Quotient.mk J) = J := by
      rw [← Ideal.comap_inf, eq, ← RingHom.ker_eq_comap_bot, mk_ker]
    rcases h.irr this with eq1|eq2
    · left
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective I₁,
        eq1, map_quotient_self]
    · right
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective I₂,
        eq2, map_quotient_self]
  · have : I₁.map (Ideal.Quotient.mk J) ⊓ I₂.map (Ideal.Quotient.mk J) = ⊥ := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      rw [Ideal.comap_inf, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        mk_ker]
      simp [← eq]
    rcases h.irr this with eq'|eq'
    <;> simp only [map_eq_bot_iff_le_ker, mk_ker] at eq'
    <;> simp [le_antisymm eq' (by simp [← eq])]

variable [IsLocalRing R]

variable (R) in
lemma quotient_maximal_hom_nontrivial [IsArtinianRing R] :
    Nontrivial (R ⧸ maximalIdeal R →ₗ[R] R) := by
  have : maximalIdeal R ∈ associatedPrimes R R := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [annihilator_eq_bot.mpr inferInstance]
    exact (maximalIdeal R).mem_minimalPrimes_of_krullDimLE_zero
  rcases (isAssociatedPrime_iff_exists_injective_linearMap _ _).mp this with ⟨_, f, hf⟩
  exact nontrivial_of_ne f 0 (LinearMap.ne_zero_of_injective hf)

set_option backward.isDefEq.respectTransparency false in
lemma exist_linearMap_range_le_of_ne_bot [IsArtinianRing R] {I : Ideal R} (ne : I ≠ ⊥) :
    ∃ (f : (R ⧸ maximalIdeal R →ₗ[R] R)), Function.Injective f ∧ LinearMap.range f ≤ I := by
  have : maximalIdeal R ∈ associatedPrimes R I := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    apply Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime.mpr (IsLocalRing.le_maximalIdeal ?_)
    simp [Module.annihilator_eq_top_iff, Submodule.subsingleton_iff_eq_bot, ne]
  rcases (isAssociatedPrime_iff_exists_injective_linearMap _ _).mp this with ⟨_, f, hf⟩
  use I.subtype.comp f
  simpa [hf] using (le_of_le_of_eq (LinearMap.range_comp_le_range _ _) I.range_subtype)

set_option backward.isDefEq.respectTransparency false in
lemma Ideal.bot_isIrreducible_iff_isPrincipal [IsArtinianRing R] :
    (⊥ : Ideal R).isIrreducible ↔ (⊤ : Submodule R (R ⧸ maximalIdeal R →ₗ[R] R)).IsPrincipal := by
  let _ := quotient_maximal_hom_nontrivial R
  let _ : Field (R ⧸ maximalIdeal R) := Quotient.field (maximalIdeal R)
  refine ⟨fun irr ↦ ?_, fun ⟨f, hf⟩ ↦ ⟨fun {I₁ I₂} infI ↦ ?_⟩⟩
  · obtain ⟨f, fne0⟩ : ∃ (f : (R ⧸ maximalIdeal R →ₗ[R] R)), f ≠ 0 := exists_ne 0
    use f
    apply le_antisymm _ le_top
    intro g _
    rw [Submodule.mem_span_singleton]
    by_cases geq0 : g = 0
    · use 0
      simp [geq0]
    · obtain ⟨x, hx, xne0⟩ : ∃ x ∈ LinearMap.range f ⊓ LinearMap.range g, x ≠ 0 := by
        apply Submodule.exists_mem_ne_zero_of_ne_bot (irr.irr.mt ?_)
        simp [LinearMap.range_eq_bot, fne0, geq0]
      rcases Submodule.mem_inf.mp hx with ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
      have zne0 : z ≠ 0 := by
        by_contra eq0
        absurd xne0
        simp [← hz, eq0]
      rcases Ideal.Quotient.mk_surjective y  with ⟨y', hy'⟩
      rcases Ideal.Quotient.mk_surjective z⁻¹ with ⟨z', hz'⟩
      use z' * y'
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Quotient.mk_eq_mk,
        map_one, LinearMap.smul_apply, ← smul_smul]
      rw [← map_smul, Algebra.smul_def y', Ideal.Quotient.algebraMap_eq, hy', mul_one, hy, ← hz,
        ← map_smul, Algebra.smul_def z', Ideal.Quotient.algebraMap_eq, hz', inv_mul_cancel₀ zne0]
  · by_contra! nebot
    rcases exist_linearMap_range_le_of_ne_bot nebot.1 with ⟨f₁, inj1, hf₁⟩
    rcases exist_linearMap_range_le_of_ne_bot nebot.2 with ⟨f₂, inj2, hf₂⟩
    have mem1 : f₁ ∈ Submodule.span R {f} := by simp [← hf]
    have mem2 : f₂ ∈ Submodule.span R {f} := by simp [← hf]
    rcases Submodule.mem_span_singleton.mp mem1 with ⟨a₁, ha₁⟩
    have ne01 : (Quotient.mk (maximalIdeal R)) a₁ ≠ 0 := by
      by_contra eq0
      absurd LinearMap.ne_zero_of_injective inj1
      apply LinearMap.ext (fun z ↦ ?_)
      rw [← ha₁, LinearMap.smul_apply, ← map_smul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, eq0, zero_mul, map_zero, LinearMap.zero_apply]
    rcases Submodule.mem_span_singleton.mp mem2 with ⟨a₂, ha₂⟩
    have ne02 : (Quotient.mk (maximalIdeal R)) a₂ ≠ 0 := by
      by_contra eq0
      absurd LinearMap.ne_zero_of_injective inj2
      apply LinearMap.ext (fun z ↦ ?_)
      rw [← ha₂, LinearMap.smul_apply, ← map_smul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, eq0, zero_mul, map_zero, LinearMap.zero_apply]
    have le1 : LinearMap.range f ≤ I₁ := by
      apply le_trans (fun x hx ↦ ?_) hf₁
      rcases hx with ⟨y, hy⟩
      have : x = f₁ ((Ideal.Quotient.mk (maximalIdeal R) a₁)⁻¹ * y) := by
        rw [← ha₁, LinearMap.smul_apply, ← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        simp [ne01, hy]
      simp [this]
    have le2 : LinearMap.range f ≤ I₂ := by
      apply le_trans (fun x hx ↦ ?_) hf₂
      rcases hx with ⟨y, hy⟩
      have : x = f₂ ((Ideal.Quotient.mk (maximalIdeal R) a₂)⁻¹ * y) := by
        rw [← ha₂, LinearMap.smul_apply, ← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        simp [ne02, hy]
      simp [this]
    have := le_of_le_of_eq (le_inf le1 le2) infI
    simp only [le_bot_iff, LinearMap.range_eq_bot] at this
    absurd hf
    simp [this]

end

lemma generators_toList_isRegular_of_spanFinrank_eq [IsNoetherianRing R]
    [IsCohenMacaulayLocalRing R] (J : Ideal R) (h : maximalIdeal R ∈ J.minimalPrimes)
    (rank : J.spanFinrank = ringKrullDim R) :
    ∃ (rs : List R), rs.length = ringKrullDim R ∧ Ideal.ofList rs = J ∧ IsRegular R rs := by
  have fg : J.FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› J
  let _ : Fintype J.generators := (Submodule.FG.finite_generators fg).fintype
  use J.generators.toFinset.toList
  have len : J.generators.toFinset.toList.length = ringKrullDim R := by
    simp [Finset.length_toList, ← rank, ← Submodule.FG.generators_ncard fg,
      Set.ncard_eq_toFinset_card']
  have gen : Ideal.ofList J.generators.toFinset.toList = J := by
    simpa [Ideal.ofList] using Submodule.span_generators J
  rw [← gen] at h
  exact ⟨len, gen, isRegular_of_maximalIdeal_mem_ofList_minimalPrimes _ h len⟩

lemma ext_isPrincipal_iff [IsLocalRing R] (rs : List R) (reg : IsRegular R rs)
    (mem : ∀ x ∈ rs, x ∈ maximalIdeal R) :
    (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      rs.length)).IsPrincipal ↔
    (⊤ : Submodule R ((R ⧸ maximalIdeal R) →ₗ[R] R ⧸ Ideal.ofList rs)).IsPrincipal := by
  let e' := (ExtEquivQuotientRegularSequence (ModuleCat.of R R)
    (ModuleCat.of R (R ⧸ maximalIdeal R)) reg.1 (by simpa [Ideal.annihilator_quotient] using mem))
  let e := e'.trans
    (Submodule.quotEquivOfEq _ (Ideal.ofList rs) (by rw [smul_eq_mul, Ideal.mul_top])).congrRight
  exact ⟨fun h ↦ @Submodule.IsPrincipal.of_comap _ _ _ _ _ _ _ _ e.toLinearMap e.surjective ⊤
    (by simpa using h), fun h ↦ @Submodule.IsPrincipal.of_comap _ _ _ _ _ _ _ _
    e.symm.toLinearMap e.symm.surjective ⊤ (by simpa using h)⟩

variable [IsLocalRing R]

lemma hom_isPrincipal_of_injectiveDimension_eq_ringKrullDim_eq_zero [IsNoetherianRing R]
    (h1 : injectiveDimension (ModuleCat.of R R) = 0) (h2 : ringKrullDim R = 0) :
    (⊤ : Submodule R ((R ⧸ maximalIdeal R) →ₗ[R] R)).IsPrincipal := by
  have inj : Module.Injective R R := by
    rw [Module.injective_iff_injective_object, injective_iff_hasInjectiveDimensionLT_one]
    exact (injectiveDimension_le_iff _ 0).mp (le_of_eq h1)
  have maxass : maximalIdeal R ∈ associatedPrimes R R := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [annihilator_eq_bot.mpr inferInstance]
    let _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h2
    exact Ideal.mem_minimalPrimes_of_krullDimLE_zero (maximalIdeal R)
  rcases (isAssociatedPrime_iff_exists_injective_linearMap _ _).mp maxass with ⟨_, f, hf⟩
  use f
  apply ((Submodule.span_singleton_eq_top_iff _ _).mpr fun g ↦ ?_).symm
  rcases inj.out f hf g with ⟨h, hh⟩
  use h 1
  ext
  simp [hh]

set_option backward.isDefEq.respectTransparency false in
lemma linearMap_isPrincipal_iff (J : Ideal R) (hJ : J ≠ ⊤) :
    letI : IsLocalRing (R ⧸ J) :=
      have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
      have : IsLocalHom (Ideal.Quotient.mk J) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (⊤ : Submodule R (R ⧸ maximalIdeal R →ₗ[R] R ⧸ J)).IsPrincipal ↔
    (⊤ : Submodule (R ⧸ J) ((R ⧸ J) ⧸ maximalIdeal (R ⧸ J) →ₗ[R ⧸ J] R ⧸ J)).IsPrincipal := by
  let _ : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let _ : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let e : (R ⧸ maximalIdeal R) ≃ₗ[R] (R ⧸ J) ⧸ maximalIdeal (R ⧸ J) :=
    LinearEquiv.ofBijective
    { __ := ResidueField.map (Ideal.Quotient.mk J)
      map_smul' r x := by
        simp [Algebra.smul_def, IsLocalRing.ResidueField.map_residue,
          IsScalarTower.algebraMap_eq R (R ⧸ J) (ResidueField (R ⧸ J))] }
    (ResidueField.map_bijective_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective)
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · use (f.comp e.symm.toLinearMap).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    apply ((Submodule.span_singleton_eq_top_iff _ _).mpr fun g ↦ ?_).symm
    have : (g.restrictScalars R).comp e.toLinearMap ∈ Submodule.span R {f} := by simp [← hf]
    rcases Submodule.mem_span_singleton.mp this with ⟨r, hr⟩
    use Ideal.Quotient.mk J r
    apply LinearMap.ext (fun x ↦ ?_)
    change (r • f) (e.symm x) = _
    simp [hr]
  · use (f.restrictScalars R).comp e.toLinearMap
    apply ((Submodule.span_singleton_eq_top_iff _ _).mpr fun g ↦ ?_).symm
    have : (g.comp e.symm.toLinearMap).extendScalarsOfSurjective (S := R ⧸ J)
      Ideal.Quotient.mk_surjective ∈ Submodule.span (R ⧸ J) {f} := by simp [← hf]
    rcases Submodule.mem_span_singleton.mp this with ⟨r, hr⟩
    rcases Ideal.Quotient.mk_surjective r with ⟨r', hr'⟩
    use r'
    apply LinearMap.ext (fun x ↦ ?_)
    change ((Ideal.Quotient.mk J) r' • f) (e x) = _
    simp [hr', hr]

--set_option backward.isDefEq.respectTransparency false in
lemma ext_isPrincipal_of_injectiveDimension_eq_ringKrullDim [IsNoetherianRing R] (n : ℕ)
    (h1 : injectiveDimension (ModuleCat.of R R) = n) (h2 : ringKrullDim R = n) :
    (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R))
      (ModuleCat.of R R) n)).IsPrincipal := by
  have : IsGorensteinLocalRing R := by
    rw [isGorensteinLocalRing_def, h1]
    exact WithBot.coe_inj.not.mpr (ENat.coe_ne_top _)
  have : IsCohenMacaulayLocalRing R := isCohenMacaulayLocalRing_of_isGorensteinLocalRing R
  have deptheq : IsLocalRing.depth (ModuleCat.of R R) = n := by
    rw [← WithBot.coe_inj, ← (isCohenMacaulayLocalRing_def R).mp ‹_›, h2]
    rfl
  rw [IsLocalRing.depth_eq_sSup_length_regular] at deptheq
  rcases Set.mem_of_eq_of_mem deptheq.symm (@ENat.sSup_mem_of_nonempty_of_lt_top _
    (by use 0, []; simpa using IsRegular.nil _ _)
    (lt_of_eq_of_lt deptheq (ENat.coe_lt_top n))) with ⟨rs, reg, mem, len⟩
  have := (quotient_regular_isGorenstein_iff_isGorenstein R rs reg).mp ‹_›
  have netop : Ideal.ofList rs ≠ ⊤ :=
    (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top') (Ideal.span_le.mpr mem))
  rw [← Nat.cast_inj.mp len, ext_isPrincipal_iff rs reg mem, linearMap_isPrincipal_iff _ netop]
  have h2' : ringKrullDim (R ⧸ Ideal.ofList rs) = 0 := by
    rw [← ENat.WithBot.add_natCast_cancel (c := rs.length), zero_add,
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs reg, Nat.cast_inj.mp len, h2]
  exact hom_isPrincipal_of_injectiveDimension_eq_ringKrullDim_eq_zero
    ((injectiveDimension_eq_ringKrullDim_of_isGorensteinLocalRing _).trans h2') h2'

set_option backward.isDefEq.respectTransparency false in
variable (R) in
lemma injective_of_isPrincipal [IsArtinianRing R]
    (h : (⊤ : Submodule R (R ⧸ maximalIdeal R →ₗ[R] R)).IsPrincipal) :
    Injective (ModuleCat.of R R) := by
  have leneq1' : Module.length R (R ⧸ maximalIdeal R) = 1 :=
    length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr Ideal.IsMaximal.out)
  have leneq1 : Module.length R (R ⧸ maximalIdeal R →ₗ[R] R) = 1 := by
    rcases h with ⟨f, hf⟩
    have surj' : Function.Surjective (LinearMap.toSpanSingleton R _ f) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, ← hf]
    let e := LinearMap.quotKerEquivOfSurjective _ surj'
    have Ker : LinearMap.ker (LinearMap.toSpanSingleton R _ f) = maximalIdeal R := by
      apply le_antisymm
      · apply IsLocalRing.le_maximalIdeal
        simp only [ne_eq, LinearMap.ker_eq_top]
        by_contra eq0
        have : f = 0 := by
          rw [← LinearMap.toSpanSingleton_apply_one R _ f, eq0, LinearMap.zero_apply]
        let _ := quotient_maximal_hom_nontrivial R
        absurd hf
        simp [this]
      · intro x hx
        simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        apply LinearMap.ext (fun y ↦ ?_)
        rw [LinearMap.smul_apply, ← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          LinearMap.zero_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_mul, map_zero]
    rw [← e.length_eq, Ker, leneq1']
  have lenle (M : Type u) [AddCommGroup M] [Module R M] [fin : Module.Finite R M] :
    Module.length R (M →ₗ[R] R) ≤ Module.length R M := by
    induction fin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    · rename_i N _ _ _ sub
      simp
    · rename_i N _ _ _ p e
      rw [Ring.KrullDimLE.eq_maximalIdeal_of_isPrime p.1] at e
      rw [(e.congrLeft R R).length_eq, e.length_eq, leneq1, leneq1']
    · rename_i N1 _ _ _ N2 _ _ _ N3 _ _ _ f g inj surj exac len1 len3
      rw [Module.length_eq_add_of_exact f g inj surj exac]
      apply le_trans _ (add_le_add len1 len3)
      let f' := (f.lcomp R R).rangeRestrict
      let g' := g.lcomp R R
      have : Function.Exact g' f' := by
        simp only [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, f', g']
        rw [← LinearMap.exact_iff]
        exact LinearMap.exact_lcomp_of_exact_of_surjective R exac surj
      rw [Module.length_eq_add_of_exact g' f' (LinearMap.lcomp_injective_of_surjective _ surj)
        (LinearMap.surjective_rangeRestrict _) this, add_comm (Module.length R (N3 →ₗ[R] R))]
      exact add_le_add_left (Module.length_le_of_injective _ (Submodule.subtype_injective _)) _
  have exac := (LinearMap.exact_subtype_mkQ (maximalIdeal R))
  have surj : Function.Surjective ((maximalIdeal R).subtype.lcomp R R) := by
    rw [← LinearMap.range_eq_top]
    by_contra ne
    let f := (maximalIdeal R).mkQ.lcomp R R
    let g := ((maximalIdeal R).subtype.lcomp R R).rangeRestrict
    have : Function.Exact f g := by
      simp only [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, f, g]
      rw [← LinearMap.exact_iff]
      exact LinearMap.exact_lcomp_of_exact_of_surjective R exac (Submodule.mkQ_surjective _)
    have leneq := Module.length_eq_add_of_exact f g (LinearMap.lcomp_injective_of_surjective _
      (Submodule.mkQ_surjective _)) (LinearMap.surjective_rangeRestrict _) this
    rw [(LinearMap.ringLmapEquivSelf R R R).length_eq, Module.length_eq_add_of_exact _ _
      (maximalIdeal R).subtype_injective (maximalIdeal R).mkQ_surjective exac,
      leneq1, leneq1', add_comm 1, WithTop.add_right_inj WithTop.one_ne_top] at leneq
    exact (lt_of_lt_of_le (Submodule.length_lt ne) (lenle (maximalIdeal R))).ne leneq.symm
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom (maximalIdeal R).subtype)
      (ModuleCat.ofHom (maximalIdeal R).mkQ) (by
      rw [← ModuleCat.ofHom_comp, exac.linearMap_comp_eq_zero]
      rfl )
  have S_exact : S.ShortExact := {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr exac
    mono_f := (ModuleCat.mono_iff_injective S.f).mpr (maximalIdeal R).subtype_injective
    epi_g := (ModuleCat.epi_iff_surjective S.g).mpr (maximalIdeal R).mkQ_surjective }
  have exac1 := Ext.contravariant_sequence_exact₁' S_exact (ModuleCat.of R R) 0 1 (add_zero 1)
  have exac2 := Ext.contravariant_sequence_exact₃' S_exact (ModuleCat.of R R) 0 1 (add_zero 1)
  have inj : Function.Injective ((Ext.mk₀ S.g).precomp (ModuleCat.of R R) (zero_add 1)) := by
    apply (AddCommGrpCat.mono_iff_injective _).mp (exac2.mono_g (exac1.epi_f_iff.mp ?_))
    simp only [AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom, S]
    intro e
    rcases (Ext.mk₀_bijective _ _).2 e with ⟨e', he'⟩
    rcases surj e'.hom with ⟨f', hf'⟩
    rw [LinearMap.lcomp_apply'] at hf'
    use Ext.mk₀ (ModuleCat.ofHom f')
    simp [← he', ← ModuleCat.ofHom_comp, hf']
  apply ModuleCat.injective_of_subsingleton_ext_quotient_one _ (fun I ↦ ?_)
  apply ext_subsingleton_of_support_subset
  intro p _
  rw [Set.mem_setOf_eq, Ring.KrullDimLE.eq_maximalIdeal_of_isPrime p.1]
  apply (((extFunctor _).mapIso (Shrink.linearEquiv.{u} R (R ⧸ maximalIdeal R)).toModuleIso.op).app
    (ModuleCat.of R R)).symm.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
  let _ : Subsingleton (Ext.{u} (ModuleCat.of R R) (ModuleCat.of R R) 1) :=
    HasProjectiveDimensionLT.subsingleton (ModuleCat.of R R) 1 1 (le_refl 1) (ModuleCat.of R R)
  exact inj.subsingleton

lemma isGorensteinLocalRing_iff_exists [IsNoetherianRing R] :
    IsGorensteinLocalRing R ↔ ∃ n, ∀ i ≥ n, Subsingleton
    (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i) := by
  have (a : WithBot ℕ∞) : a ≠ ⊤ ↔ ∃ (n : ℕ), a < n := by
    induction a with
    | bot => simp
    | coe a =>
      induction a with
      | top => simp
      | coe a => simpa [- ENat.WithBot.coe_eq_natCast] using ⟨a + 1, Nat.cast_lt.mpr (lt_add_one a)⟩
  simp only [isGorensteinLocalRing_def, this, ge_iff_le]
  apply exists_congr (fun n ↦ ?_)
  rw [injectiveDimension_lt_iff_of_finite (ModuleCat.of R R) n]
  congr! 2
  exact (((extFunctor _).mapIso (Shrink.linearEquiv.{u} R (R ⧸ maximalIdeal R)).toModuleIso.op).app
    (ModuleCat.of R R)).symm.addCommGroupIsoToAddEquiv.subsingleton_congr

set_option backward.isDefEq.respectTransparency false in
theorem isGroensteinLocalRing_tfae [IsNoetherianRing R] (n : ℕ) (h : ringKrullDim R = n) :
    [IsGorensteinLocalRing R, injectiveDimension (ModuleCat.of R R) = n,
     (∀ i ≠ n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal,
     ∃ i > n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i),
     (∀ i < n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal,
     IsCohenMacaulayLocalRing R ∧ (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R))
      (ModuleCat.of R R) n)).IsPrincipal,
     IsCohenMacaulayLocalRing R ∧ ∀ {J : Ideal R}, maximalIdeal R ∈ J.minimalPrimes →
      J.spanFinrank = n → J.isIrreducible,
     IsCohenMacaulayLocalRing R ∧ ∃ J : Ideal R, maximalIdeal R ∈ J.minimalPrimes ∧
      J.spanFinrank = n ∧ J.isIrreducible
     ].TFAE := by
  tfae_have 1 → 2 := by
    intro
    rw [← h]
    apply injectiveDimension_eq_ringKrullDim_of_isGorensteinLocalRing
  tfae_have 2 → 3 := by
    intro injdim
    let _ : IsGorensteinLocalRing R := by
      rw [isGorensteinLocalRing_def, injdim]
      exact WithBot.coe_inj.not.mpr (ENat.coe_ne_top n)
    let _ : IsCohenMacaulayLocalRing R := isCohenMacaulayLocalRing_of_isGorensteinLocalRing R
    refine ⟨fun i hi ↦ ?_, ext_isPrincipal_of_injectiveDimension_eq_ringKrullDim n injdim h⟩
    rcases hi.lt_or_gt with lt|gt
    · have lt' : i < IsLocalRing.depth (ModuleCat.of R R) := by
        apply lt_of_lt_of_eq (ENat.coe_lt_coe.mpr lt)  (WithBot.coe_inj.mp _)
        exact h.symm.trans ((isCohenMacaulayLocalRing_def R).mp ‹_›)
      apply (((extFunctor _).mapIso
        (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).toModuleIso.op).app
        (ModuleCat.of R R)).symm.addCommGroupIsoToAddEquiv.subsingleton_congr.mp
      exact ext_subsingleton_of_lt_moduleDepth lt'
    · have : HasInjectiveDimensionLE (ModuleCat.of R R) n := by
        simp [← injectiveDimension_le_iff, injdim]
      exact HasInjectiveDimensionLT.subsingleton (ModuleCat.of R R) (n + 1) i gt _
  tfae_have 3 → 4 := fun ⟨h, _⟩ ↦ ⟨n + 1, ⟨lt_add_one n, h _ (Nat.succ_ne_self n)⟩⟩
  tfae_have 4 → 1 := by
    rintro ⟨k, kgt, hk⟩
    exact isGorensteinLocalRing_of_exists k (by simpa [h] using kgt) hk
  tfae_have 3 → 5 := fun ⟨nesub, prin⟩ ↦ ⟨fun i hi ↦ nesub i hi.ne, prin⟩
  tfae_have 5 → 6 := by
    refine fun ⟨ltsub, prin⟩ ↦ ⟨?_, prin⟩
    apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth
    rw [h]
    apply WithBot.coe_le_coe.mpr (le_sSup ?_)
    intro i hi
    apply (((extFunctor _).mapIso (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).toModuleIso.op).app
      (ModuleCat.of R R)).symm.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
    exact ltsub i (Nat.cast_lt.mp hi)
  tfae_have 6 → 7 := by
    refine fun ⟨CM, prin⟩ ↦ ⟨CM, fun {J} maxmin spanrank ↦ ?_⟩
    have : Nontrivial (R ⧸ J) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top') maxmin.1.2)
    have : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    have : IsArtinianRing (R ⧸ J) := quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J maxmin
    rcases generators_toList_isRegular_of_spanFinrank_eq J maxmin (by simp [spanrank, h]) with
      ⟨rs, len, gen, reg⟩
    have len' : rs.length = n := Nat.cast_inj.mp (len.trans h)
    have mem : ∀ x ∈ rs, x ∈ maximalIdeal R := fun x hx ↦
      le_of_eq_of_le gen maxmin.1.2 ((Ideal.mem_span x).mpr fun p a ↦ a hx)
    rw [← len', ext_isPrincipal_iff rs reg mem, gen,
      linearMap_isPrincipal_iff J (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top') maxmin.1.2)] at prin
    rw [Ideal.irreducible_iff_bot_irreducible, Ideal.bot_isIrreducible_iff_isPrincipal]
    exact prin
  tfae_have 7 → 8 := by
    refine fun ⟨CM, irr⟩ ↦ ⟨CM, ?_⟩
    --existence of parameter ideal
    rcases Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R) with ⟨S, min, hS⟩
    have : (Ideal.span (S : Set R)).spanFinrank = n := by
      have hteq : (maximalIdeal R).height = n := by
        rw [← WithBot.coe_inj, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]
        rfl
      apply le_antisymm
      · apply le_of_le_of_eq (Submodule.spanFinrank_span_le_ncard_of_finite S.finite_toSet)
        simpa [← ENat.coe_inj, hS] using hteq
      · rw [← ENat.coe_le_coe, ← hteq]
        apply le_of_le_of_eq (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ min)
        simpa [Submodule.fg_iff_spanRank_eq_spanFinrank] using
          (isNoetherianRing_iff_ideal_fg R).mp ‹_› _
    use Ideal.span (S : Set R)
    exact ⟨min, this, irr min this⟩
  tfae_have 8 → 1 := by
    refine fun ⟨CM, ⟨J, maxmin, spanrank, irr⟩⟩ ↦ ?_
    have : Nontrivial (R ⧸ J) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top') maxmin.1.2)
    have : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    have : IsArtinianRing (R ⧸ J) := quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J maxmin
    rcases generators_toList_isRegular_of_spanFinrank_eq J maxmin (by simp [spanrank, h]) with
      ⟨rs, len, gen, reg⟩
    rw [Ideal.irreducible_iff_bot_irreducible, Ideal.bot_isIrreducible_iff_isPrincipal] at irr
    have inj := injective_of_isPrincipal (R ⧸ J) irr
    rw [quotient_regular_isGorenstein_iff_isGorenstein R rs reg, gen, isGorensteinLocalRing_def]
    apply ne_top_of_le_ne_top (WithBot.coe_inj.not.mpr (ENat.coe_ne_top 0))
    exact (injectiveDimension_le_iff _ _).mpr inferInstance
  tfae_finish
