/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Gorenstein.Defs
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Regular.InjectiveDimension

/-!

# Polynomial over Gorenstein Ring is Gorenstein

-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian Limits IsLocalRing Polynomial Ideal

/-- The base change map `R ⧸ I → S ⧸ IS ` -/
def quotientIsBaseChangeMap (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R) :
    R ⧸ I →ₗ[R] S ⧸ I.map (algebraMap R S) :=
  Submodule.liftQ I ((Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).toLinearMap.comp
    (Algebra.linearMap R S)) (fun x hx ↦ by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, AlgHom.coe_toLinearMap, Quotient.mkₐ_eq_mk,
        Function.comp_apply, Algebra.linearMap_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact mem_map_of_mem (algebraMap R S) hx)

lemma quotientIsBaseChangeMap_isBaseChange (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R) :
    IsBaseChange S (quotientIsBaseChangeMap R S I) := by
  apply IsBaseChange.of_equiv (Ideal.qoutMapEquivTensorQout S).symm
  intro x
  induction x using Submodule.Quotient.induction_on
  rename_i y
  simp only [quotientIsBaseChangeMap, Submodule.liftQ_apply]
  simp [qoutMapEquivTensorQout, Algebra.smul_def]

lemma isGorensteinLocalRing_iff_exists [IsLocalRing R] [IsNoetherianRing R] :
    IsGorensteinLocalRing R ↔ ∃ n, ∀ i ≥ n, Subsingleton
    (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i) := by
  have (a : WithBot ℕ∞) : a ≠ ⊤ ↔ ∃ (n : ℕ), a < n := by
    induction a with
    | bot => simp
    | coe a =>
      induction a with
      | top => simp
      | coe a => simpa using ⟨a + 1, Nat.cast_lt.mpr (lt_add_one a)⟩
  simp only [isGorensteinLocalRing_def, this, ge_iff_le]
  apply exists_congr (fun n ↦ ?_)
  rw [injectiveDimension_lt_iff_of_finite (ModuleCat.of R R) n]
  congr! 2
  exact (((extFunctor _).mapIso (Shrink.linearEquiv.{u} R (R ⧸ maximalIdeal R)).toModuleIso.op).app
    (ModuleCat.of R R)).symm.addCommGroupIsoToAddEquiv.subsingleton_congr

variable {R} in
lemma quotientSMulShortComplex_exact (I : Ideal R) (x : R) :
    Function.Exact (x • (LinearMap.id (R := R) (M := R ⧸ I)))
    (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {x})) := by
  intro y
  rcases Ideal.Quotient.mk_surjective y with ⟨z, hz⟩
  have : I ⊔ Ideal.span {x} = (Ideal.span {Ideal.Quotient.mk I x}).comap (Ideal.Quotient.mk I) := by
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective' _
      Ideal.Quotient.mk_surjective, mk_ker, sup_comm]
  simp only [← hz, Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Quotient.factor_mk,
    Quotient.eq_zero_iff_mem, this, mem_comap, mem_span_singleton', Algebra.smul_def, Set.mem_range,
    Module.End.mul_apply, LinearMap.id_coe, id_eq, Module.algebraMap_end_apply,
    Quotient.algebraMap_eq, mul_comm]

variable {R} in
/-- The short complex `R ⧸ I → R ⧸ I → R ⧸ I ⊔ span {x}`,
with the first map scalar multilple by `x`. -/
def quotientSMulShortComplex (I : Ideal R) (x : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (x • (LinearMap.id (R := R) (M := R ⧸ I))))
  (ModuleCat.ofHom (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {x}))) (by
    rw [← ModuleCat.ofHom_comp, (quotientSMulShortComplex_exact I x).linearMap_comp_eq_zero]
    rfl )

lemma quotientSMulShortComplex_shortExact_of_isSMulRegular (I : Ideal R) {x : R}
    (reg : IsSMulRegular (R ⧸ I) x) : (quotientSMulShortComplex I x).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (quotientSMulShortComplex I x)).mpr (quotientSMulShortComplex_exact I x)
  mono_f := (ModuleCat.mono_iff_injective (quotientSMulShortComplex I x).f).mpr reg
  epi_g := (ModuleCat.epi_iff_surjective (quotientSMulShortComplex I x).g).mpr
    (Submodule.factor_surjective le_sup_left)

lemma Polynomial.localization_at_comap_maximal_isGorenstein_of_isGorenstein [IsNoetherianRing R]
    [IsGorensteinLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsGorensteinLocalRing (Localization.AtPrime p) := by
  let _ : Module.Free R R[X] :=
    let _ : Module.Free R (AddMonoidAlgebra R ℕ) := Module.Free.finsupp R R ℕ
    Module.Free.of_equiv (Polynomial.toFinsuppIsoLinear R).symm
  let _ : Module.Flat R (Localization.AtPrime p) := Module.Flat.trans R R[X] _
  let f : ModuleCat.of R (R ⧸ maximalIdeal R) →ₗ[R] ModuleCat.of (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ (maximalIdeal R).map (algebraMap R (Localization.AtPrime p))) :=
    quotientIsBaseChangeMap R (Localization.AtPrime p) (maximalIdeal R)
  have isb1 : IsBaseChange (Localization.AtPrime p) f :=
    quotientIsBaseChangeMap_isBaseChange R (Localization.AtPrime p) (maximalIdeal R)
  let g : ModuleCat.of R R →ₗ[R] ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p) :=
    Algebra.linearMap R (Localization.AtPrime p)
  rcases (isGorensteinLocalRing_iff_exists R).mp ‹_› with ⟨n, hn⟩
  have subsing (i : ℕ) (hi : i ≥ n) : Subsingleton (Ext (ModuleCat.of (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ (maximalIdeal R).map (algebraMap R (Localization.AtPrime p))))
    (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) i) := by
    let _ := hn i hi
    apply (Ext.isBaseChange' (Localization.AtPrime p)
      _ _ f isb1 g (IsBaseChange.linearMap R (Localization.AtPrime p)) i).equiv.symm.subsingleton
  have lep : (maximalIdeal R).map C ≤ p := by simpa [← max] using map_comap_le
  have Ker : RingHom.ker (Polynomial.mapRingHom (residue R)) = (maximalIdeal R).map C := by
    simp [ker_mapRingHom, ker_residue]
  by_cases eq0 : p.map (Polynomial.mapRingHom (residue R)) = ⊥
  · have peq : p = (maximalIdeal R).map C := le_antisymm
      (by simpa [← Ker, ← Ideal.map_eq_bot_iff_le_ker]) lep
    have maxeq : maximalIdeal (Localization.AtPrime p) =
      (maximalIdeal R).map (algebraMap R (Localization.AtPrime p)) := by
      rw [IsScalarTower.algebraMap_eq R R[X], ← Ideal.map_map]
      simp [← peq, IsLocalization.AtPrime.map_eq_maximalIdeal]
    apply (isGorensteinLocalRing_iff_exists _).mpr
    use n
    intro i hi
    rw [maxeq]
    exact subsing i hi
  · let RXp := Localization.AtPrime p
    have isp := (Ideal.isPrime_map_C_of_isPrime (IsMaximal.isPrime' (maximalIdeal R)))
    have disj : Disjoint (p.primeCompl : Set R[X]) _ := disjoint_compl_left_iff.mpr lep
    let _ : (Ideal.map (algebraMap R RXp) (maximalIdeal R)).IsPrime := by
      rw [IsScalarTower.algebraMap_eq R R[X], ← Ideal.map_map, algebraMap_eq]
      exact IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl RXp _ isp disj
    let _ : IsPrincipalIdealRing (IsLocalRing.ResidueField R)[X] := inferInstance
    rcases IsPrincipalIdealRing.principal (Ideal.map (mapRingHom (residue R)) p) with ⟨z, hz⟩
    rcases map_surjective (residue R) residue_surjective z with ⟨y, hy⟩
    have peq : p = (maximalIdeal R).map C ⊔ Ideal.span {y} := by
      calc
      p = p ⊔ RingHom.ker (mapRingHom (residue R)) := by simpa [Ker] using lep
      _ = comap (mapRingHom (residue R)) ((Ideal.span {y}).map (mapRingHom (residue R))) := by
        simp [← Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), hz, Ideal.map_span, hy]
      _ = _ := by simp only [Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), sup_comm, Ker]
    have maxeq : maximalIdeal RXp = (maximalIdeal R).map (algebraMap R RXp) ⊔
      Ideal.span {(algebraMap R[X] RXp) y} := by
      simp [RXp, ← IsLocalization.AtPrime.map_eq_maximalIdeal p, peq, Ideal.map_sup, Ideal.map_span,
        ← Polynomial.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    let S := quotientSMulShortComplex ((maximalIdeal R).map (algebraMap R RXp))
      ((algebraMap R[X] RXp) y)
    have S_exact : S.ShortExact := by
      apply quotientSMulShortComplex_shortExact_of_isSMulRegular
      apply IsSMulRegular.of_right_eq_zero_of_smul (fun a ha ↦ ?_)
      simp only [Algebra.smul_def, Quotient.algebraMap_eq] at ha
      apply (mul_eq_zero_iff_left ?_).mp ha
      simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      rw [IsScalarTower.algebraMap_eq R R[X], ← Ideal.map_map, algebraMap_eq, ← Ideal.mem_comap,
        IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl RXp _ isp disj, ← Ker]
      simp only [RingHom.mem_ker, coe_mapRingHom, hy]
      by_contra zeq0
      absurd eq0
      simp [hz, zeq0]
    apply (isGorensteinLocalRing_iff_exists _).mpr
    use n + 1
    intro i hi
    have : 1 + (i - 1) = i := by omega
    rw [maxeq]
    apply AddCommGrpCat.subsingleton_of_isZero <| (Ext.contravariant_sequence_exact₃' S_exact
      (ModuleCat.of RXp RXp) (i - 1) i this).isZero_of_both_zeros
      (IsZero.eq_zero_of_src ?_ _) (IsZero.eq_zero_of_tgt ?_ _)
    · exact @AddCommGrpCat.isZero_of_subsingleton _ (subsing (i - 1) (Nat.le_sub_one_of_lt hi))
    · exact @AddCommGrpCat.isZero_of_subsingleton _ (subsing i (Nat.le_of_succ_le hi))

theorem Polynomial.isCM_of_isCM [IsNoetherianRing R] [IsGorensteinRing R] :
    IsGorensteinRing R[X] := by
  apply (isGorensteinRing_def _).mpr (fun p hp ↦ ?_)
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let _ : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have _ : IsLocalization pc S := {
    map_units x := by
      rcases x.2 with ⟨y, mem, eq⟩
      apply IsUnit.of_mul_eq_one (C (Localization.mk 1 ⟨y, mem⟩))
      simp [← eq, S, ← map_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    surj z := by
      induction z using Polynomial.induction_on'
      · rename_i f g hf hg
        rcases hf with ⟨⟨x1, y1⟩, h1⟩
        rcases hg with ⟨⟨x2, y2⟩, h2⟩
        use (x2 * y1.1 + x1 * y2.1, y1 * y2)
        simp only [Submonoid.coe_mul, map_mul, add_mul, map_add]
        nth_rw 4 [mul_comm]
        simp [← mul_assoc, h1, h2, add_comm]
      · rename_i n a
        rcases Localization.mkHom_surjective a with ⟨⟨x, y⟩, h⟩
        have : y.1 ∉ q := y.2
        use ((monomial n) x, ⟨C y.1, by simpa [pc]⟩)
        simp only [← h, Localization.mkHom_apply, algebraMap_def, coe_mapRingHom, map_C, ←
          Localization.mk_one_eq_algebraMap, monomial_mul_C, map_monomial, S, Localization.mk_mul]
        congr 1
        apply Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
        simp [mul_comm]
    exists_of_eq {x y} eq := by
      have eq' (n : ℕ) : (algebraMap R (Localization.AtPrime q)) (Polynomial.coeff x n) =
        (algebraMap R (Localization.AtPrime q)) (Polynomial.coeff y n) := by
        simp only [algebraMap_def, coe_mapRingHom, S] at eq
        rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, eq]
        --simp `failed to synthesize FaithfulSMul R (Localization.AtPrime q)`
      let g : ℕ → q.primeCompl := fun n ↦ Classical.choose (IsLocalization.exists_of_eq (eq' n))
      have g_spec (n : ℕ) := Classical.choose_spec
        (IsLocalization.exists_of_eq (M := q.primeCompl) (eq' n))
      let s := ∏ n ∈ x.1.1 ∪ y.1.1, g n
      have : s.1 ∉ q := s.2
      use ⟨C s.1, by simpa [pc]⟩
      ext n
      simp only [coeff_C_mul, s]
      by_cases mem : n ∈ x.1.1 ∪ y.1.1
      · rcases Finset.dvd_prod_of_mem g mem with ⟨t, ht⟩
        simp only [ht, Submonoid.coe_mul, mul_comm _ t.1, mul_assoc]
        rw [g_spec n]
      · simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq, not_or, not_not] at mem
        simp [← Polynomial.toFinsupp_apply, mem] }
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime :=  IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.comap_map_of_isPrime_disjoint pc _ _ ‹_› disj).symm
  let _ := (isGorensteinRing_def R).mp ‹_› q (comap_isPrime C p)
  have : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_comap q.primeCompl _ (comap C pS),
      ← IsLocalization.map_comap q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      IsLocalization.comap_map_of_isPrime_disjoint pc _ _ ‹_› disj,
      IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q) q]
    rfl
  let _ := localization_at_comap_maximal_isGorenstein_of_isGorenstein
    (Localization.AtPrime q) pS this
  exact IsGorensteinLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
