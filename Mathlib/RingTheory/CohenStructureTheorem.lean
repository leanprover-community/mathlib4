/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.MixedCharZero
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Extension
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Smooth.Quotient

/-!

# Cohen Structure Theorem

-/

@[expose] public section

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R]

section

lemma IsBaseChange.of_eq_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (J : Ideal S) (eq : J = I.map (algebraMap R S)) :
    letI := (Ideal.quotientMap (I := I) J (algebraMap R S)
      (by simp [← Ideal.map_le_iff_le_comap, eq])).toAlgebra
    letI : IsScalarTower R (R ⧸ I) (S ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
    IsBaseChange (R ⧸ I) (Ideal.Quotient.mkₐ R J).toLinearMap := by
  let _ := (Ideal.quotientMap (I := I) J (algebraMap R S)
    (by simp [← Ideal.map_le_iff_le_comap, eq])).toAlgebra
  let _ : IsScalarTower R (R ⧸ I) (S ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  let e : TensorProduct R (R ⧸ I) S ≃ₗ[R] S ⧸ J :=
    (TensorProduct.quotTensorEquivQuotSMul S I).trans (Submodule.quotEquivOfEq _ _ (by simp [eq])
    ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R J)
  apply IsBaseChange.of_equiv (e.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I)))
  intro s
  simp only [LinearEquiv.extendScalarsOfSurjective_apply, LinearEquiv.trans_apply, e]
  rw [← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp

end

section IsCohenRing

/-- A Cohen ring is a complete DVR with characteristic of residue field being an uniformizer. -/
class IsCohenRing [IsDomain R] extends IsDiscreteValuationRing R, IsAdicComplete (maximalIdeal R) R
    where
  span : maximalIdeal R = Ideal.span {(ringChar (ResidueField R) : R)}

set_option backward.isDefEq.respectTransparency false in
lemma exists_isCohenRing_of_not_charZero (k : Type u) [Field k] (charpos : ¬ CharZero k) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsCohenRing R),
      Nonempty (ResidueField R ≃+* k) := by
  have char := CharP.exists' k
  simp only [charpos, false_or] at char
  rcases char with ⟨p, _, char⟩
  let _ := ZMod.algebra k p
  let _ : Algebra (ResidueField (PadicInt p)) k :=
    ((algebraMap (ZMod p) k).comp PadicInt.residueField.toRingHom).toAlgebra
  rcases exists_isLocalHom_flat (PadicInt p) k with ⟨R, _, _, _, _, flat, maxeq, ⟨iso⟩⟩
  simp only [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
    map_natCast] at maxeq
  have maxfg : (maximalIdeal R).FG := by
    use {(p : R)}
    simp [maxeq]
  let R' := AdicCompletion (maximalIdeal R) R
  let _ : IsLocalRing R' := AdicCompletion.isLocalRing_of_fg maxfg
  have maxeq' : maximalIdeal R' = Ideal.span {(p : R')} := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg maxfg]
    simp [maxeq, Ideal.map_span]
  have reg : (p : R) ∈ nonZeroDivisors R := by
    refine mem_nonZeroDivisors_iff_right.mpr (fun x hx ↦ ?_)
    have regaux : IsSMulRegular R (p : R) := by
      simpa using IsSMulRegular.of_flat (IsSMulRegular.of_ne_zero PadicInt.irreducible_p.ne_zero)
    apply isSMulRegular_iff_right_eq_zero_of_smul.mp regaux x
    simp [← hx, mul_comm]
  have mem_of_mem_succ {n : ℕ} {r : R} (mem : p • r ∈ (maximalIdeal R) ^ (n + 1)) :
    r ∈ (maximalIdeal R) ^ n := by
    simp only [maxeq, Ideal.span_singleton_pow] at mem ⊢
    rcases Ideal.mem_span_singleton'.mp mem with ⟨s, hs⟩
    simp only [pow_succ, ← mul_assoc, nsmul_eq_mul, mul_comm _ r,
      mul_cancel_right_mem_nonZeroDivisors reg] at hs
    rw [← hs, Ideal.mem_span_singleton']
    use s
  have reg' : (p : R') ∈ nonZeroDivisors R' := by
    refine mem_nonZeroDivisors_iff_right.mpr (fun x hx ↦ ?_)
    have eq0 : p • x = 0 := by simp [← hx, mul_comm]
    ext n
    have : p • AdicCompletion.eval _ _ (n + 1) x = 0 := by
      simp [← LinearMap.map_smul_of_tower, eq0]
    rcases Submodule.Quotient.mk_surjective _ (x.1 (n + 1)) with ⟨y, hy⟩
    simp only [AdicCompletion.eval, LinearMap.coe_mk, AddHom.coe_mk, ← hy,
      ← Submodule.mkQ_apply, ← LinearMap.map_smul_of_tower] at this
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top] at this
    simpa [← x.2 (Nat.le_succ n), ← hy, AdicCompletion.transitionMap, Submodule.factorPow,
      Ideal.Quotient.eq_zero_iff_mem] using mem_of_mem_succ this
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  let _ : IsNoetherianRing R' := AdicCompletion.isNoetherianRing_of_fg _ maxfg
  have spanle : (maximalIdeal R').spanFinrank ≤ 1 := by
    rw [maxeq']
    exact le_of_le_of_eq (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _))
      (Set.ncard_singleton _)
  have dimge : 1 ≤ ringKrullDim R' := by
    apply (WithBot.one_le_iff_pos _).mpr
    by_contra! le
    let _ : Ring.KrullDimLE 0 R' := Ring.krullDimLE_iff.mpr le
    have disj := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes
      (Ideal.mem_minimalPrimes_of_krullDimLE_zero (maximalIdeal R'))
    absurd Disjoint.notMem_of_mem_right disj reg'
    simpa [maxeq'] using Ideal.subset_span (Set.mem_singleton _)
  have dimle := ringKrullDim_le_spanFinrank_maximalIdeal R'
  let _ : IsRegularLocalRing R' :=
    (isRegularLocalRing_def _).mpr (le_antisymm ((Nat.cast_le.mpr spanle).trans dimge) dimle)
  let _ : IsDiscreteValuationRing R' :=
    IsDiscreteValuationRing.of_isRegularLocalRing_of_ringKrullDim_eq_one _
      (le_antisymm (dimle.trans (Nat.cast_le.mpr spanle)) dimge)
  let _ : IsAdicComplete (maximalIdeal R') R' := AdicCompletion.isAdicComplete_of_fg maxfg
  use R', inferInstance, inferInstance
  let e : k ≃+* ResidueField R' := iso.toRingEquiv.trans
    (RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective_of_fg maxfg))
  refine ⟨⟨?_⟩, ⟨e.symm⟩⟩
  let _ := e.toRingHom.toAlgebra
  rw [← Algebra.ringChar_eq k, ringChar.eq k p, maxeq']

/-- A variant of `PadicInt.toZModPow`. -/
noncomputable def padicIntToIntQuotient (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    PadicInt p →+* ℤ ⧸ (Ideal.span {(p ^ n : ℤ)}) :=
  (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom.comp (PadicInt.toZModPow n)

set_option backward.isDefEq.respectTransparency false in
lemma padicIntToIntQuotient_surjective (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    Function.Surjective (padicIntToIntQuotient p n) := by
  simpa [padicIntToIntQuotient] using ZMod.ringHom_surjective _

lemma padicIntToIntQuotient_ker (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    RingHom.ker (padicIntToIntQuotient p n) = Ideal.span {(p ^ n : ℤ_[p])} := by
  simpa [← PadicInt.ker_toZModPow, padicIntToIntQuotient] using RingHom.ker_equiv_comp _ _

set_option backward.isDefEq.respectTransparency false in
lemma padicInt_to_int_quotient_comm (p : ℕ) [Fact (Nat.Prime p)] {m n : ℕ} (hle : m ≤ n) :
    padicIntToIntQuotient p m = (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (p : ℤ) hle))).comp
    (padicIntToIntQuotient p n) := by
  simp only [padicIntToIntQuotient, RingEquiv.toRingHom_eq_coe]
  ext x
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    ← PadicInt.cast_toZModPow m n hle]
  rcases ZMod.natCast_zmod_surjective ((PadicInt.toZModPow n) x) with ⟨y, hy⟩
  simpa [← hy, ZMod.cast_natCast (Nat.pow_dvd_pow p hle) y] using map_natCast _ _

set_option backward.isDefEq.respectTransparency false in
/-- For complete local ring `R` with residue field of characteristic `p`, the canonical map
`ℤ_[p] →+* R`. -/
noncomputable def padicIntOfCharP [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (p : ℕ)
    [Fact (Nat.Prime p)] (char : CharP (ResidueField R) p) : PadicInt p →+* R :=
  have mem (n : ℕ) : (p ^ n : R) ∈ (maximalIdeal R) ^ n:= by
    apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsLocalRing.residue_def, map_natCast, char.cast_eq_zero]
  let f (n : ℕ) : PadicInt p →+* (R ⧸ (maximalIdeal R) ^  n) :=
    (Ideal.Quotient.lift _ (Int.castRingHom _) ((Ideal.span_singleton_le_iff_mem
      (RingHom.ker (Int.castRingHom (R ⧸ maximalIdeal R ^ n)))).mpr (by
        simp [← Ideal.Quotient.eq_zero_iff_mem.mpr (mem n)]))).comp (padicIntToIntQuotient p n)
  IsAdicComplete.liftRingHom (maximalIdeal R) f (fun {m n} hle ↦ by
    simp only [padicInt_to_int_quotient_comm p hle, f]
    congr)

lemma padicIntOfCharP_flat_of_isCohenRing [IsLocalRing R] [IsDomain R] [IsCohenRing R]
    (p : ℕ) [Fact (Nat.Prime p)] (char : CharP (ResidueField R) p) :
    (padicIntOfCharP R p char).Flat := by
  let _ := (padicIntOfCharP R p char).toAlgebra
  have inj : Function.Injective (padicIntOfCharP R p char) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra ne
    rcases PadicInt.ideal_eq_span_pow_p ne with ⟨n, hn⟩
    have : (p : ℤ_[p]) ^ n ∈ RingHom.ker (padicIntOfCharP R p char) := by
      simpa [hn] using Ideal.subset_span (Set.mem_singleton_of_eq rfl)
    have ne : (p : R) ≠ 0 := by
      by_contra eq0
      absurd IsCohenRing.span (R := R)
      simpa [ringChar.eq (ResidueField R) p, eq0] using IsDiscreteValuationRing.not_a_field R
    simp [ne] at this
  let _ : Module.IsTorsionFree ℤ_[p] R := {
    isSMulRegular x hx := (isLeftRegular_iff_isRegular.mpr
      (IsRegular.of_ne_zero ((map_ne_zero_iff _ inj).mpr hx.ne_zero))).isSMulRegular}
  dsimp only [RingHom.Flat]
  infer_instance

lemma quotient_power_char_formallySmooth [IsDomain R] [IsCohenRing R] (p : ℕ) (prime : Nat.Prime p)
    (char : CharP (ResidueField R) p) (n : ℕ) (ne0 : n ≠ 0) : (Ideal.quotientMap
      (I := Ideal.span {(p ^ n : ℤ)}) (Ideal.span {(p ^ n : R)}) (Int.castRingHom R)
      (by simp [← Ideal.map_le_iff_le_comap, Ideal.map_span])).FormallySmooth := by
  let _ : Fact (Nat.Prime p) := ⟨prime⟩
  induction n with
  | zero => simp at ne0
  | succ n ih =>
    by_cases eq0 : n = 0
    · rw [eq0, zero_add]
      --should be able to obtain by extension is separable
      sorry
    · have le : Ideal.span {(p ^ (n + 1) : ℤ)} ≤ Ideal.span {(p ^ n : ℤ)} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ n))
      have le' : Ideal.span {(p ^ (n + 1) : R)} ≤ Ideal.span {(p ^ n : R)} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ n))
      apply RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero _ _
        (Ideal.Quotient.factor le) (Ideal.Quotient.factor le')
        _ (Ideal.Quotient.factor_surjective le) (Ideal.Quotient.factor_surjective le')
        _ _ _ (ih eq0)
      · let _ := (padicIntOfCharP R p char).toAlgebra
        let I := Ideal.span {(p ^ (n + 1) : ℤ_[p])}
        let J := Ideal.span {(p ^ (n + 1) : R)}
        let f : (ℤ_[p] ⧸ I) →+* (R ⧸ J) := (Ideal.quotientMap J (algebraMap ℤ_[p] R)
          (by simp [I, J, ← Ideal.map_le_iff_le_comap, Ideal.map_span]))
        let _ : Algebra (ℤ_[p] ⧸ I) (R ⧸ J) := f.toAlgebra
        let _ : IsScalarTower ℤ_[p] (ℤ_[p] ⧸ I) (R ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
        let isb := IsBaseChange.of_eq_map I J (by simp [I, J, Ideal.map_span])
        let _ : Module.Flat ℤ_[p] R := padicIntOfCharP_flat_of_isCohenRing R p char
        have : f.Flat := Module.Flat.isBaseChange _ _ _ _ isb
        let e : ℤ_[p] ⧸ I ≃+* ℤ ⧸ Ideal.span {(p ^ (n + 1) : ℤ)} :=
          (Ideal.quotEquivOfEq (padicIntToIntQuotient_ker p (n + 1)).symm).trans
            (RingHom.quotientKerEquivOfSurjective (padicIntToIntQuotient_surjective p (n + 1)))
        convert (RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective).comp this
        ext
        simp
      · ext
        simp
      · simp only [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.span_singleton_pow,
          Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul,
          Ideal.span_singleton_le_span_singleton]
        exact pow_dvd_pow _ (by omega)
      · simp [Ideal.Quotient.factor_ker, Ideal.map_span]

end IsCohenRing

section

variable {R} [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in
lemma exists_section_of_charZero [IsAdicComplete (maximalIdeal R) R]
    (char : CharZero (ResidueField R)) :
    ∃ (f : ResidueField R →+* R), (IsLocalRing.residue R).comp f = RingHom.id _ := by
  let _ : Algebra ℚ (ResidueField R) := DivisionRing.toRatAlgebra
  let _ : Algebra.FormallySmooth ℚ (ResidueField R) :=
    --should be able to obtain by extension is separable
    sorry
  let _ : Algebra ℚ R := EqualCharZero.algebraRat (fun I ne ↦
    let tores : (R ⧸ I) →+* (ResidueField R) := Ideal.Quotient.factor (le_maximalIdeal ne)
    tores.charZero)
  have exists_lift (n : ℕ) (f : ResidueField R →+* (R ⧸ (maximalIdeal R) ^ (n + 1))) :
    ∃ g : ResidueField R →+* (R ⧸ (maximalIdeal R) ^ (n + 1 + 1)),
      (Ideal.Quotient.factorPowSucc _ (n + 1)).comp g = f := by
    let h := Ideal.Quotient.factorPowSucc (maximalIdeal R) (n + 1)
    have le := (maximalIdeal R).pow_le_pow_right (Nat.le_succ (n + 1))
    have nil : IsNilpotent (RingHom.ker h) := by
      use 2
      simpa [h, Ideal.Quotient.factor_ker , ← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
        using Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
    let g := (Algebra.FormallySmooth.liftOfSurjective f.toRatAlgHom
      h.toRatAlgHom (Ideal.Quotient.factor_surjective le) nil)
    use g.toRingHom
    have : h.toRatAlgHom.comp g = f.toRatAlgHom := Algebra.FormallySmooth.comp_liftOfSurjective
      f.toRatAlgHom h.toRatAlgHom (Ideal.Quotient.factor_surjective le) nil
    ext x
    change (h.toRatAlgHom.comp g) x = _
    simp [this]
  let f_series (n : ℕ) : (ResidueField R →+* (R ⧸ (maximalIdeal R) ^ n)) := by
    induction n with
    | zero =>
      exact Ideal.Quotient.factor (by simp)
    | succ n ih =>
      induction n with
      | zero =>
        exact Ideal.Quotient.factor (by simp)
      | succ n ih =>
        exact Classical.choose (exists_lift n ih)
  have f_series1 : f_series 1 = Ideal.Quotient.factor (le_of_eq (pow_one _).symm) := rfl
  have f_series_spec {n m : ℕ} (h : m = n + 1) : (Ideal.Quotient.factorPow _
    (Nat.le.intro h.symm)).comp (f_series m) = f_series n := by
    subst h
    match n with
    | 0 => exact Ideal.Quotient.factor_comp _ _
    | n + 1 => exact Classical.choose_spec (exists_lift n _)
  have f_series_spec' {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (f_series n) = f_series m := by
    obtain ⟨l, hl⟩ := Nat.le.dest hle
    subst hl
    induction l with
    | zero => simp
    | succ l ih =>
      have : m + (l + 1) = (m + l) + 1 := add_assoc m l 1
      rw [← ih (Nat.le_add_right m l), ← f_series_spec this, ← RingHom.comp_assoc,
        Ideal.Quotient.factor_comp]
  let f := IsAdicComplete.liftRingHom (maximalIdeal R) f_series f_series_spec'
  use f
  have (x : R) : (residue R) x = (Ideal.Quotient.factor (by simp))
    ((Ideal.Quotient.mk ((maximalIdeal R) ^ 1)) x) := rfl
  ext x
  rw [RingHom.comp_apply, this, IsAdicComplete.mk_liftRingHom, f_series1]
  simp [ResidueField]

set_option backward.isDefEq.respectTransparency false in
lemma exists_isCohenRing_residueField_map_bijective [IsAdicComplete (maximalIdeal R) R]
    (charpos : ¬ CharZero (ResidueField R)) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsCohenRing S) (f : S →+* R)
    (_ : IsLocalHom f), Function.Bijective (ResidueField.map f) := by
  rcases exists_isCohenRing_of_not_charZero (ResidueField R) charpos with ⟨S, _, _, cohen, ⟨e⟩⟩
  use S, inferInstance, inferInstance, inferInstance
  have char := CharP.exists' (ResidueField R)
  simp only [charpos, false_or] at char
  rcases char with ⟨p, prime, char⟩
  have char' : CharP (ResidueField S) p := CharP.of_ringHom_of_ne_zero
    e.symm.toRingHom p (NeZero.ne' p).symm
  have eqspan : maximalIdeal S = Ideal.span {(p : S)} := by
    rw [IsCohenRing.span, ringChar.eq (ResidueField S) p]
  have exists_lift (n : ℕ)
    (f : (S ⧸ (maximalIdeal S) ^ (n + 1)) →+* (R ⧸ (maximalIdeal R) ^ (n + 1))) :
    ∃ g : (S ⧸ (maximalIdeal S) ^ (n + 1 + 1)) →+* (R ⧸ (maximalIdeal R) ^ (n + 1 + 1)),
      (Ideal.Quotient.factorPowSucc (maximalIdeal R) (n + 1)).comp g =
      f.comp (Ideal.Quotient.factorPowSucc (maximalIdeal S) (n + 1)) := by
    let H := Ideal.Quotient.factorPowSucc (maximalIdeal R) (n + 1)
    have le := (maximalIdeal R).pow_le_pow_right (Nat.le_succ (n + 1))
    have nil : IsNilpotent (RingHom.ker H) := by
      use 2
      simpa [H, Ideal.Quotient.factor_ker, ← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
        using Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
    let F := (Ideal.quotientMap (I := Ideal.span {(p ^ (n + 1 + 1) : ℤ)})
      (Ideal.span {(p ^ (n + 1 + 1) : S)}) (Int.castRingHom S)
      (by simp [← Ideal.map_le_iff_le_comap, Ideal.map_span]))
    let E : S ⧸ Ideal.span {(p ^ (n + 1 + 1) : S)} ≃+* S ⧸ (maximalIdeal S) ^ (n + 1 + 1) :=
      Ideal.quotEquivOfEq (by simp [cohen.span, ringChar.eq, Ideal.span_singleton_pow])
    let _ := (E.toRingHom.comp F).toAlgebra
    let _ : Algebra.FormallySmooth (ℤ ⧸ Ideal.span {(p ^ (n + 1 + 1) : ℤ)})
      (S ⧸ maximalIdeal S ^ (n + 1 + 1)) :=
      (quotient_power_char_formallySmooth S p prime.out char' (n + 1 + 1) (by omega)).comp
      (RingHom.FormallySmooth.of_bijective E.bijective)
    let G : ℤ ⧸ Ideal.span {(p ^ (n + 1 + 1) : ℤ)} →+* R ⧸ (maximalIdeal R) ^ (n + 1 + 1) :=
      Ideal.quotientMap _ (Int.castRingHom R) (by
        simp only [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, eq_intCast, Int.cast_pow]
        apply Ideal.pow_mem_pow
        simp [← Ideal.Quotient.eq_zero_iff_mem, char.cast_eq_zero])
    let _ := G.toAlgebra
    let _ := (H.comp G).toAlgebra
    let H' : R ⧸ maximalIdeal R ^ (n + 1 + 1) →ₐ[ℤ ⧸ Ideal.span {(p ^ (n + 1 + 1) : ℤ)}]
      R ⧸ maximalIdeal R ^ (n + 1) := {
      __ := H
      commutes' k := by simp [RingHom.algebraMap_toAlgebra] }
    let f' : (S ⧸ (maximalIdeal S) ^ (n + 1 + 1)) →ₐ[ℤ ⧸ Ideal.span {(p ^ (n + 1 + 1) : ℤ)}]
      (R ⧸ (maximalIdeal R) ^ (n + 1)) := {
      __ := f.comp (Ideal.Quotient.factorPowSucc (maximalIdeal S) (n + 1))
      commutes' k := by
        rcases Ideal.Quotient.mk_surjective k with ⟨l, hl⟩
        simp [← hl] }
    let g := Algebra.FormallySmooth.liftOfSurjective f' H' (Ideal.Quotient.factor_surjective le) nil
    use g.toRingHom
    have : H'.comp g = f' := Algebra.FormallySmooth.comp_liftOfSurjective f' H'
      (Ideal.Quotient.factor_surjective le) nil
    ext x
    change H'.comp g x = _
    simp [this, f']
  let _ : Unique (S ⧸ maximalIdeal S ^ 0) :=
    @uniqueOfSubsingleton _ (Ideal.Quotient.subsingleton_iff.mpr (by simp)) 0
  let _ : Unique (R ⧸ maximalIdeal R ^ 0) :=
    @uniqueOfSubsingleton _ (Ideal.Quotient.subsingleton_iff.mpr (by simp)) 0
  let f0 : S ⧸ maximalIdeal S ^ 0 ≃+* R ⧸ maximalIdeal R ^ 0 := RingEquiv.ofUnique
  let f1 : S ⧸ maximalIdeal S ^ 1 ≃+* R ⧸ maximalIdeal R ^ 1 :=
    ((Ideal.quotEquivOfEq (pow_one _)).trans e).trans (Ideal.quotEquivOfEq (pow_one _).symm)
  let f_series (n : ℕ) : (S ⧸ (maximalIdeal S) ^ n →+* (R ⧸ (maximalIdeal R) ^ n)) := by
    induction n with
    | zero => exact f0.toRingHom
    | succ n ih =>
      induction n with
      | zero => exact f1.toRingHom
      | succ n ih => exact Classical.choose (exists_lift n ih)
  have f_series1 : f_series 1 = f1.toRingHom := rfl
  have f_series_spec {n m : ℕ} (h : m = n + 1) :
    (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le.intro h.symm)).comp (f_series m) =
    (f_series n).comp (Ideal.Quotient.factorPow (maximalIdeal S) (Nat.le.intro h.symm)) := by
    subst h
    match n with
    | 0 =>
      ext
      exact Subsingleton.elim _ _
    | n + 1 => exact Classical.choose_spec (exists_lift n _)
  have f_series_spec' {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (f_series n) =
    (f_series m).comp (Ideal.Quotient.factorPow (maximalIdeal S) hle) := by
    obtain ⟨l, hl⟩ := Nat.le.dest hle
    subst hl
    induction l with
    | zero => simp
    | succ l ih =>
      have : m + (l + 1) = (m + l) + 1 := add_assoc m l 1
      have eq : Ideal.Quotient.factorPow (maximalIdeal R) hle =
        (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_add_right m l)).comp
        (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le.intro this.symm)) := by simp
      rw [eq, RingHom.comp_assoc, f_series_spec this, ← RingHom.comp_assoc,
        ih (Nat.le_add_right m l), RingHom.comp_assoc, Ideal.Quotient.factor_comp]
  let f' : AdicCompletion (maximalIdeal S) S →+* AdicCompletion (maximalIdeal R) R := {
    toFun := fun x ↦ ⟨fun n ↦ (Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _).symm))
      (f_series n ((Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _))) (x.1 n))),
      fun {m n} hle ↦ by
        simp only [smul_eq_mul, AdicCompletion.transitionMap, Submodule.factorPow,
          Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.factor_comp_apply]
        have : Ideal.Quotient.factor _ = (Ideal.Quotient.factor
          (le_of_eq (Ideal.mul_top _).symm)).comp (Ideal.Quotient.factorPow (maximalIdeal R) hle) :=
          (Ideal.Quotient.factor_comp _ _).symm
        rw [this, RingHom.comp_apply, ← RingHom.comp_apply _ (f_series n), f_series_spec' hle]
        simp [← x.2 hle, AdicCompletion.transitionMap, Submodule.factorPow]⟩
    map_one' := by ext; simp
    map_mul' x y := by ext; simp
    map_zero' := by ext; simp
    map_add' x y := by ext; simp }
  let f := ((AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toRingHom.comp f').comp
    (AdicCompletion.ofAlgEquiv (maximalIdeal S)).toRingHom
  have eqe : (residue R).comp f = e.toRingHom.comp (residue S) := by
    have res : residue R = (Ideal.Quotient.factor _).comp
      (Ideal.Quotient.mk (maximalIdeal R ^ 1 • ⊤)) :=
      (Ideal.Quotient.factor_comp_mk (le_of_eq ((Ideal.mul_top _).trans (pow_one _)))).symm
    ext x
    rw [res]
    change (Ideal.Quotient.factor (le_of_eq ((Ideal.mul_top _).trans (pow_one _))))
      ((Ideal.Quotient.mk (maximalIdeal R ^ 1 • ⊤))
      ((AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm
      (f' ((AdicCompletion.ofAlgEquiv (maximalIdeal S)) x)))) = _
    rw [AdicCompletion.mk_smul_top_ofAlgEquiv_symm, AdicCompletion.eval_apply]
    simp [f', f_series1, f1, Ideal.quotEquivOfEq_eq_factor, ResidueField, residue]
  have : RingHom.ker ((residue R).comp f) = maximalIdeal S := by
    simp [eqe, ← RingHom.comap_ker, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  rw [← RingHom.comap_ker, IsLocalRing.ker_residue] at this
  let _ : IsLocalHom f := ((IsLocalRing.local_hom_TFAE f).out 0 4).mpr this
  use f, ‹_›
  rw [(RingHom.cancel_right residue_surjective).mp ((ResidueField.map_comp_residue f).trans eqe)]
  exact e.bijective

end
