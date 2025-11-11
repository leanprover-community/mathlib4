/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Differential Fields

This file defines the logarithmic derivative `Differential.logDeriv` and proves properties of it.
This is defined algebraically, compared to `logDeriv` which is analytical.
-/

namespace Differential

open algebraMap Polynomial IntermediateField

variable {R : Type*} [Field R] [Differential R] (a b : R)

/--
The logarithmic derivative of a is a′ / a.
-/
def logDeriv : R := a′ / a

@[simp]
lemma logDeriv_zero : logDeriv (0 : R) = 0 := by
  simp [logDeriv]

@[simp]
lemma logDeriv_one : logDeriv (1 : R) = 0 := by
  simp [logDeriv]

lemma logDeriv_mul (ha : a ≠ 0) (hb : b ≠ 0) : logDeriv (a * b) = logDeriv a + logDeriv b := by
  unfold logDeriv
  simp [field]
  ring

lemma logDeriv_div (ha : a ≠ 0) (hb : b ≠ 0) : logDeriv (a / b) = logDeriv a - logDeriv b := by
  unfold logDeriv
  simp [field, Derivation.leibniz_div]

@[simp]
lemma logDeriv_pow (n : ℕ) (a : R) : logDeriv (a ^ n) = n * logDeriv a := by
  induction n with
  | zero => simp
  | succ n h2 =>
    obtain rfl | hb := eq_or_ne a 0
    · simp
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
      simp [hb]

lemma logDeriv_eq_zero : logDeriv a = 0 ↔ a′ = 0 :=
  ⟨fun h ↦ by simp only [logDeriv, _root_.div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h ↦ by unfold logDeriv at *; simp [h]⟩

lemma logDeriv_multisetProd {ι : Type*} (s : Multiset ι) {f : ι → R} (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (s.map f).prod = (s.map fun x ↦ logDeriv (f x)).sum := by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [← h₂]
    · apply logDeriv_mul
      · simp [h]
      · simp_all
    · simp_all

lemma logDeriv_prod (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := logDeriv_multisetProd _ h

lemma logDeriv_prod_of_eq_zero (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x = 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := by
  unfold logDeriv
  simp_all

lemma logDeriv_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv (algebraMap F K a) = algebraMap F K (logDeriv a) := by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]
lemma _root_.algebraMap.coe_logDeriv {F K : Type*} [Field F] [Field K] [Differential F]
    [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv a = logDeriv (a : K) := (logDeriv_algebraMap a).symm

variable {F : Type*} [Field F] [Differential F] [CharZero F]

noncomputable instance (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] :
    Differential (AdjoinRoot p) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk p).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      - (aeval (AdjoinRoot.root p) (mapCoeffs p)) / (aeval (AdjoinRoot.root p) (derivative p))) (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [ AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      simp only [ne_eq, AdjoinRoot.mk_eq_zero]
      have : 0 < p.natDegree := Irreducible.natDegree_pos (Fact.out)
      apply not_dvd_of_natDegree_lt
      · intro nh
        simp [natDegree_eq_zero_of_derivative_eq_zero nh] at this
      apply natDegree_derivative_lt
      exact Nat.ne_zero_of_lt this)

instance (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] :
    DifferentialAlgebra F (AdjoinRoot p) where
  deriv_algebraMap a := by
    change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk p).toIntAlgHom (C a)) = _
    rw [Derivation.liftOfSurjective_apply, implicitDeriv_C]
    rfl

variable {K : Type*} [Field K] [Algebra F K]

variable (F K) in
/--
If `K` is a finite field extension of `F` then we can define a differential algebra on `K`, by
choosing a primitive element of `K`, `k` and then using the equivalence to `AdjoinRoot (minpoly k)`.
-/
@[reducible]
noncomputable def differentialFiniteDimensional [FiniteDimensional F K] : Differential K :=
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  Differential.equiv (IntermediateField.adjoinRootEquivAdjoin F
    (IsAlgebraic.of_finite F k).isIntegral |>.trans (IntermediateField.equivOfEq h) |>.trans
    IntermediateField.topEquiv).symm.toRingEquiv

lemma differentialAlgebraFiniteDimensional [FiniteDimensional F K] :
    letI := differentialFiniteDimensional F K
    DifferentialAlgebra F K := by
  let k := (Field.exists_primitive_element F K).choose
  haveI h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  haveI : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  haveI : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  apply DifferentialAlgebra.equiv

/--
A finite extension of a differential field has a unique derivation which agrees with the one on the
base field.
-/
noncomputable def uniqueDifferentialAlgebraFiniteDimensional [FiniteDimensional F K] :
    Unique {_a : Differential K // DifferentialAlgebra F K} := by
  let default : {_a : Differential K // DifferentialAlgebra F K} :=
      ⟨differentialFiniteDimensional F K, differentialAlgebraFiniteDimensional⟩
  refine ⟨⟨default⟩, fun ⟨a, ha⟩ ↦ ?_⟩
  ext x
  apply_fun (aeval x (mapCoeffs (minpoly F x)) + aeval x (derivative (minpoly F x)) * ·)
  · conv_lhs => apply (deriv_aeval_eq ..).symm
    conv_rhs => apply (@deriv_aeval_eq _ _ _ _ _ default.1 _ default.2 _ _).symm
    simp
  · apply (add_right_injective _).comp
    apply mul_right_injective₀
    rw [ne_eq, ← minpoly.dvd_iff]
    have : 0 < (minpoly F x).natDegree := Irreducible.natDegree_pos
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
    apply not_dvd_of_natDegree_lt
    · intro nh
      simp [natDegree_eq_zero_of_derivative_eq_zero nh] at this
    apply natDegree_derivative_lt
    exact Nat.ne_zero_of_lt this

noncomputable instance (B : IntermediateField F K) [FiniteDimensional F B] : Differential B :=
  differentialFiniteDimensional F B

instance (B : IntermediateField F K) [FiniteDimensional F B] :
    DifferentialAlgebra F B := differentialAlgebraFiniteDimensional

instance [Differential K] [DifferentialAlgebra F K] (B : IntermediateField F K)
    [FiniteDimensional F B] : DifferentialAlgebra B K where
  deriv_algebraMap a := by
    change (B.val a)′ = B.val a′
    rw [algHom_deriv']
    exact Subtype.val_injective

end Differential
