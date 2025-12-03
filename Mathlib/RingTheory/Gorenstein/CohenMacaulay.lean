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
public import Mathlib.RingTheory.CohenMacaulay.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Gorenstein.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
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

variable (R : Type u) [CommRing R]

variable {R} in
lemma Ideal.ofList_reverse (rs : List R) : Ideal.ofList rs.reverse = Ideal.ofList rs := by
  simp [Ideal.ofList]

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

variable {R} [IsLocalRing R] [IsNoetherianRing R]

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

universe w

variable [Small.{v} R] [UnivLE.{v, w}]

open Pointwise

/-- If `M` has projective dimension not exceeding `n`, for an `M`-regular element `a`,
the linear equivalence `Ext M N n ⧸ a • ⊤ ≃ Ext M⧸xM N (n + 1)` induced by the long exact sequence
`Ext M N n → Ext M N n → Ext M⧸xM N (n + 1) → 0` with first morphism scalar multiple by `a`. -/
noncomputable def quotSMulTop_ext_equiv_ext_quotSMulTop (M : ModuleCat.{v} R) (n : ℕ)
    [HasProjectiveDimensionLE M n] (a : R) (reg : IsSMulRegular M a) (N : ModuleCat.{v} R) :
    QuotSMulTop a (Ext.{w} M N n) ≃ₗ[R] Ext (ModuleCat.of R (QuotSMulTop a M)) N (n + 1) := by
  let S := M.smulShortComplex a
  have S_exact : S.ShortExact := reg.smulShortComplex_shortExact
  let f : Ext M N n →ₗ[R] Ext (ModuleCat.of R (QuotSMulTop a M)) N (n + 1) := {
    toFun := S_exact.extClass.precomp N (add_comm 1 n)
    map_add' := by simp
    map_smul' := by simp }
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
      have : S.f = a • 𝟙 _ := by
        ext
        simp [S]
      ext x
      simp [this, Ext.mk₀_smul]
    rw [LinearMap.exact_iff.mp exac']
    ext y
    simp [Submodule.mem_smul_pointwise_iff_exists]
  exact (Submodule.quotEquivOfEq _ _ ker.symm).trans (f.quotKerEquivOfSurjective surj)

/-- The linear equivalence `Ext (R⧸(r1, ... rk)) M k ≃ M⧸(r1, ... rk)M` for `R`-regular sequence
`(r1, ... rk)`, this is a special case of a more general result for Koszul complex. -/
noncomputable def ext_quotient_regular_sequence_length (M : ModuleCat.{v} R) (rs : List R)
    (reg : IsRegular R rs) :
    (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M rs.length) ≃ₗ[R]
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
      __ := (((extFunctor.{w} (n + 1)).mapIso e1'.toModuleIso.op).app M).addCommGroupIsoToAddEquiv
      map_smul' r x := by simp [Iso.addCommGroupIsoToAddEquiv] }
    let _ : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) n :=
      have : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) = n := by
        simp [projectiveDimension_quotient_eq_length rs' rs'reg, rs', len]
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

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma nontrivial_of_islocalizedModule {S : Submonoid R} {M MS : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup MS] [Module R MS] {f : M →ₗ[R] MS} (isl : IsLocalizedModule S f)
    (h : Nontrivial MS) : Nontrivial M := by
  by_contra!
  absurd h
  exact not_nontrivial_iff_subsingleton.mpr
    (IsLocalizedModule.linearEquiv S f (LocalizedModule.mkLinearMap S M)).subsingleton

section

omit [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- For `p` a prime ideal disjoint with multiplicative set `S`, the map `S⁻¹M → Mₚ`. -/
noncomputable def isLocalizaedModule_map_of_disjoint_map (S : Submonoid R) (A : Type*) [CommRing A]
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

omit [IsNoetherianRing R] in
lemma isLocalizaedModule_map_of_disjoint (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization S A] (p : Ideal A) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    {MS : Type*} [AddCommGroup MS] [Module R MS] (f : M →ₗ[R] MS) [IsLocalizedModule S f]
    [Module A MS] [IsScalarTower R A MS] {Mp : Type*} [AddCommGroup Mp] [Module R Mp]
    (g : M →ₗ[R] Mp) [IsLocalizedModule.AtPrime (p.comap (algebraMap R A)) g]
    [Module A Mp] [IsScalarTower R A Mp] :
    IsLocalizedModule.AtPrime p (isLocalizaedModule_map_of_disjoint_map S A p f g) where
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
    simpa [isLocalizaedModule_map_of_disjoint_map] using hmr
  exists_of_eq {z1 z2} eq := by
    rcases IsLocalizedModule.surj S f z1 with ⟨⟨m1, r1⟩, hmr1⟩
    rcases IsLocalizedModule.surj S f z2 with ⟨⟨m2, r2⟩, hmr2⟩
    have eq' : (isLocalizaedModule_map_of_disjoint_map S A p f g) (r2 • r1 • z1) =
      (isLocalizaedModule_map_of_disjoint_map S A p f g) (r1 • r2 • z2) := by
      simp [smul_smul, mul_comm r1 r2, eq]
    simp only [isLocalizaedModule_map_of_disjoint_map, hmr1, LinearMap.map_smul_of_tower,
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

universe w

variable [Small.{v} R] [UnivLE.{v, w}]

instance (S : Submonoid R) : Small.{v} (Localization S) :=
  small_of_surjective Localization.mkHom_surjective

instance (p : Ideal R) [p.IsPrime] : Small.{v} p.ResidueField :=
  small_of_surjective Ideal.Quotient.mk_surjective

private instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

lemma ext_succ_nontrivial_of_eq_of_le (M : ModuleCat.{v} R) [Module.Finite R M]
    {p q : PrimeSpectrum R} (lt : p < q) (eq_of_le : ∀ r : PrimeSpectrum R, p < r → r ≤ q → r = q)
    (i : ℕ) (ntr : Nontrivial (Ext.{w} (ModuleCat.of (Localization p.1.primeCompl)
      (Shrink.{v} p.1.ResidueField)) (M.localizedModule p.1.primeCompl) i)) :
    Nontrivial (Ext.{w} (ModuleCat.of (Localization q.1.primeCompl)
      (Shrink.{v} q.1.ResidueField)) (M.localizedModule q.1.primeCompl) (i + 1)) := by
  by_contra! sub
  let _ : Module.Finite (Localization q.1.primeCompl) (M.localizedModule q.1.primeCompl) :=
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
      p.1 p.2 disj, eq, Localization.AtPrime.comap_maximalIdeal]
  have sub' : Subsingleton (Ext (ModuleCat.of (Localization q.1.primeCompl) (Shrink.{v}
    (Localization q.1.primeCompl ⧸ (p.1.map f)))) (M.localizedModule q.1.primeCompl) i) := by
    apply ext_subsingleton_of_all_gt (M.localizedModule q.1.primeCompl) i (p.1.map f) ne
    intro r rgt hr
    have cgt : r.comap f > p.1 := by
      rw [← IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl
        (Localization q.1.primeCompl) p.1 p.2 disj]
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
      rw [IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq p.1 p.2 disj]
    let e := IsLocalization.algEquiv p.1.primeCompl Rp (Localization.AtPrime (p.1.map f))
    exact IsLocalization.isLocalization_of_algEquiv (p.1.map f).primeCompl (AlgEquiv.ofLinearEquiv
      (e.toLinearEquiv.extendScalarsOfIsLocalization q.1.primeCompl Rq) (by simp) (by simp)).symm
  let _ : IsLocalizedModule.AtPrime (p.1.map f) (Algebra.linearMap Rq Rp) :=
    (isLocalizedModule_iff_isLocalization' _ _).mpr isl0
  let _ : IsScalarTower Rq Rp (Shrink.{v, u} p.asIdeal.ResidueField) :=
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
    let _ := IsLocalizedModule.of_linearEquiv_right (p.1.map f).primeCompl f1'
      (Shrink.linearEquiv.{v} Rq _)
    IsLocalizedModule.of_linearEquiv (p.1.map f).primeCompl
      (f1'.comp (Shrink.linearEquiv.{v} Rq _).toLinearMap) e
  let _ : Module Rq (M.localizedModule p.1.primeCompl) :=
    ModuleCat.Algebra.instModuleCarrier
  let _ : IsScalarTower Rq Rp (M.localizedModule p.asIdeal.primeCompl) :=
    ModuleCat.Algebra.instIsScalarTowerCarrier
  let _ : IsLocalizedModule.AtPrime ((p.1.map f).comap f)
    (M.localizedModule_mkLinearMap p.1.primeCompl) := by
    convert M.localizedModule_isLocalizedModule p.1.primeCompl
    exact IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq p.1 p.2 disj
  let _ : IsScalarTower R Rq (M.localizedModule p.1.primeCompl) := {
    smul_assoc r s z := by
      nth_rw 2 [← algebraMap_smul Rp r]
      rw [← algebraMap_smul Rp s, smul_smul, Algebra.smul_def, ← algebraMap_smul Rp, map_mul,
        ← IsScalarTower.algebraMap_apply] }
  let f2 : (M.localizedModule q.1.primeCompl) →ₗ[Rq] (M.localizedModule p.asIdeal.primeCompl) :=
    isLocalizaedModule_map_of_disjoint_map q.1.primeCompl Rq (p.1.map f)
    (M.localizedModule_mkLinearMap q.1.primeCompl) (M.localizedModule_mkLinearMap p.1.primeCompl)
  have isl2 : IsLocalizedModule (p.1.map f).primeCompl f2 :=
    isLocalizaedModule_map_of_disjoint q.1.primeCompl Rq (p.1.map f)
    (M.localizedModule_mkLinearMap q.1.primeCompl) (M.localizedModule_mkLinearMap p.1.primeCompl)
  let _ : Module.Finite Rq (Shrink.{v} (Rq ⧸ Ideal.map f p.asIdeal)) :=
    Module.Finite.equiv (Shrink.linearEquiv Rq _).symm
  have isl := Ext.isLocalizedModule'.{v, v, u, u, w, w} (p.1.map f).primeCompl Rp f1 isl1 f2 isl2 i
  absurd nontrivial_of_islocalizedModule isl ntr
  exact not_nontrivial_iff_subsingleton.mpr sub'

end

variable [Small.{v} R]

section

open ModuleCat.Algebra

open associatedPrimes in
lemma supportDim_le_injectiveDimension (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    supportDim R M ≤ injectiveDimension M := by
  obtain ⟨q, hq⟩ : ∃ q : LTSeries (Module.support R M), q.length = supportDim R M := by
    let _ : Nonempty (support R M) := Set.Nonempty.to_subtype nonempty_support_of_nontrivial
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
    let _ := (q ⟨q.length, lt_add_one q.length⟩).1.2
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
      simp only [AssociatePrimes.mem_iff] at ass
      have := mem_associatedPrimes_atPrime_of_mem_associatedPrimes ass
      simp only [AssociatePrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at this
      rcases this with ⟨_, f, hf⟩
      exact nontrivial_of_ne f 0  (LinearMap.ne_zero_of_injective hf)
    · rename_i i ih
      exact ext_succ_nontrivial_of_eq_of_le.{v, u, v} M (q.step ⟨i, h⟩) (eq_of_le ⟨i, h⟩) i
        (ih (Nat.le_of_succ_le h))
  have ntr : Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R))) M
    q.length) := by
    let qq := q ⟨q.length, Nat.lt_succ_iff.mpr (le_refl q.length)⟩
    have qqeq : qq.1.1 = maximalIdeal R := tail_eq
    have ntr' : Nontrivial (Ext.{v} (ModuleCat.of (Localization qq.1.1.primeCompl)
      (Shrink.{v, u} qq.1.1.ResidueField)) (M.localizedModule qq.1.1.primeCompl) q.length) :=
      lem' q.length (le_refl _)
    let _ : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
      Module.Finite.equiv (Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R)).symm
    let _ : IsScalarTower R (Localization qq.1.1.primeCompl) (Shrink.{v} qq.1.1.ResidueField) :=
      Equiv.isScalarTower R (Localization qq.1.1.primeCompl) (equivShrink qq.1.1.ResidueField).symm
    let _ : IsLocalization qq.1.1.primeCompl R :=
      IsLocalization.at_units _ (fun x hx ↦ by simpa [qqeq] using hx)
    have surj : Function.Surjective (algebraMap R (Localization qq.1.1.primeCompl)) :=
      (IsLocalization.bijective qq.1.1.primeCompl
        (algebraMap R (Localization qq.1.1.primeCompl)) rfl).2
    let _ : IsLocalHom (algebraMap R (Localization qq.1.1.primeCompl)) :=
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
      let _ := isLocalizedModule_id qq.1.1.primeCompl (Shrink.{v, u} (R ⧸ maximalIdeal R)) R
      exact IsLocalizedModule.of_linearEquiv qq.1.1.primeCompl LinearMap.id f
    have isl := Ext.isLocalizedModule'.{v, v, u, u, v, v} qq.1.1.primeCompl
      (Localization qq.1.1.primeCompl) f.toLinearMap isl1
      (M.localizedModule_mkLinearMap qq.1.1.primeCompl)
      (M.localizedModule_isLocalizedModule qq.1.1.primeCompl) q.length
    exact nontrivial_of_islocalizedModule isl ntr'
  simp only [← hq, injectiveDimension_eq_sInf_of_finite.{v} M, le_sInf_iff, Set.mem_setOf_eq]
  intro b hb
  by_contra! lt
  exact (not_subsingleton_iff_nontrivial.mpr ntr) (hb q.length lt)

end

open Limits in
lemma injectiveDimension_eq_depth
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
      let _ : Module.Free R (Shrink.{v} R) := Module.Free.of_equiv (Shrink.linearEquiv R R).symm
      have : projectiveDimension (ModuleCat.of R (Shrink.{v} R)) = 0 := by
        apply le_antisymm
        · apply (projectiveDimension_le_iff _ 0).mpr
          simpa [HasProjectiveDimensionLE, ← projective_iff_hasProjectiveDimensionLT_one]
            using ModuleCat.projective_of_categoryTheory_projective _
        · have : projectiveDimension (ModuleCat.of R (Shrink.{v, u} R)) ≠ ⊥ := by
            simpa [projectiveDimension_eq_bot_iff] using not_subsingleton (Shrink.{v, u} R)
          rw [← WithBot.coe_unbot _ this, ← WithBot.coe_zero, WithBot.coe_le_coe]
          exact zero_le _
      simp [projectiveDimension_quotient_regular_sequence (ModuleCat.of R (Shrink.{v} R)) rs
        reg'.1 mem, this]
    have ntr : Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M r) := by
      by_contra! sub
      have (i : ℕ) (lt : r < i) :
        Subsingleton (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i) := by
        let _ := (injectiveDimension_le_iff _ r).mp (le_of_eq hr)
        exact HasInjectiveDimensionLT.subsingleton M (r + 1) i lt _
      let _ := (injectiveDimension_le_iff _ r).mp (le_of_eq hr)
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
    let _ := projectiveDimension_lt_iff.mp (lt_of_eq_of_lt projdim (Nat.cast_lt.mpr lt))
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
      let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
      calc
      _ = f (e.symm (e y * (e x)⁻¹ * (e x))) := by
        simp [AddEquivClass.map_ne_zero_iff.mpr ne]
      _ = _ := by
        rcases Ideal.Quotient.mk_surjective (e y * (e x)⁻¹) with ⟨r, hr⟩
        rw [← hr, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]
        simp [LinearMap.mem_ker.mp hx]
    let g : ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R)) ⟶
      ModuleCat.of R (Shrink.{v, u} R ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R))) :=
      ModuleCat.ofHom f
    let S := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_cokernel g
      mono_f := (ModuleCat.mono_iff_injective g).mpr injf
      epi_g := coequalizer.π_epi}
    have exac := Ext.contravariant_sequence_exact₁'.{v} S_exact M r (r + 1) (add_comm 1 r)
    have : IsZero (AddCommGrpCat.of (Ext.{v} S.X₃ M (r + 1))) := by
      apply @AddCommGrpCat.isZero_of_subsingleton _ ?_
      let _ := (injectiveDimension_le_iff M r).mp (le_of_eq hr)
      exact HasInjectiveDimensionLT.subsingleton M (r + 1) (r + 1) (le_refl _) _
    have surj : Function.Surjective ((Ext.mk₀.{v} S.f).precomp M (zero_add r)) :=
      (AddCommGrpCat.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
    exact surj.nontrivial
  · simp only [injectiveDimension, le_sInf_iff, Set.mem_setOf_eq]
    intro b hb
    by_contra! lt
    let _ := hb rs.length lt
    absurd HasInjectiveDimensionLT.subsingleton.{v} M rs.length rs.length (le_refl _)
      (ModuleCat.of R (Shrink.{v, u} (R ⧸ Ideal.ofList rs)))
    apply not_subsingleton_iff_nontrivial.mpr
    rw [(ext_quotient_regular_sequence_length.{v, u, v} M rs reg).nontrivial_congr]
    apply Submodule.Quotient.nontrivial_iff.mpr
    apply (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator _).symm
    exact le_trans (Ideal.span_le.mpr mem) (maximalIdeal_le_jacobson _)

end injdim

variable (R)

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
    | coe n => simpa using WithBot.coe_inj.not.mpr (ENat.coe_ne_top (n + 1))

lemma injectiveDimension_quotient_span_regular
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    injectiveDimension (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) + 1 =
    injectiveDimension (ModuleCat.of R R) := by
  let e : (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x R)) ≅
    (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) :=
    { __ := Submodule.quotEquivOfEq _ (Ideal.span {x}) (by
        simp [← Submodule.ideal_span_singleton_smul])
      map_smul' r y := by
        rcases Ideal.Quotient.mk_surjective r with ⟨s, hs⟩
        simp only [← hs, IsTorsionBySet.mk_smul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          map_smul, LinearEquiv.coe_coe, RingHomCompTriple.comp_apply, smul_eq_mul]
        rfl }.toModuleIso
  rw [← injectiveDimension_quotSMulTop_succ_eq_injectiveDimension reg reg mem,
    injectiveDimension_eq_of_iso e]

open Pointwise in
lemma quotient_span_regular_isGorenstein_iff_isGorenstein
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    IsGorensteinLocalRing R ↔ IsGorensteinLocalRing (R ⧸ Ideal.span {x}) := by
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  rw [isGorensteinLocalRing_def, isGorensteinLocalRing_def,
    ← injectiveDimension_quotient_span_regular R x reg mem]
  exact (add_one_eq_top_iff _).not

open Ideal in
lemma quotient_regular_isGorenstein_iff_isGorenstein
    (rs : List R) (reg : IsRegular R rs) :
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
        have : Ideal.span {a} = ⊤ :=
          Ideal.eq_top_of_isUnit_mem  _ (Ideal.mem_span_singleton_self a) uni
        absurd reg.2.symm
        simp [this]
      let e : QuotSMulTop a R ≃ₗ[R ⧸ Ideal.span {a}] R ⧸ Ideal.span {a} :=
        (Submodule.quotEquivOfEq _ (Ideal.span {a})
          (by simp [← Submodule.ideal_span_singleton_smul])).extendScalarsOfSurjective
            Ideal.Quotient.mk_surjective
      simp only [isRegular_cons_iff', e.isRegular_congr] at reg
      let _ : Nontrivial (R ⧸ Ideal.span {a}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by simpa using mem)
      let _ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let _ : IsLocalRing (R ⧸ Ideal.span {a}) :=
        IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {a})) Ideal.Quotient.mk_surjective
      rw [quotient_span_regular_isGorenstein_iff_isGorenstein R a reg.1 mem,
        ih (R ⧸ Ideal.span {a}) _ reg.2 (by simp [h])]
      rw [← Ideal.map_ofList, Ideal.ofList_cons]
      let e' := DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.ofList rs')
      exact ⟨fun h ↦ IsGorensteinLocalRing.of_ringEquiv e',
        fun h ↦ IsGorensteinLocalRing.of_ringEquiv e'.symm⟩
