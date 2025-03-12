/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
import Mathlib.RingTheory.Trace.Basic

/-!

# Normalized trace

This file defines *normalized trace* map, that is, an `F`-linear map from the algebraic closure
of `F` to `F` defined as the trace of an element from its adjoin extension divided by its degree.

To avoid heavy imports, we define it here as a map from an arbitrary algebraic (equivalently
integral) extension of `F`.

## Main definitions

- `normalizedTrace`: the trace of an element from the simple adjoin divided by the degree;
  it is a non-trivial `F`-linear map from an arbitrary algebraic extension `K` to `F`.

## Main results

- `normalizedTrace_intermediateField`: for a tower `K / E / F` of algebraic extensions,
  `normalizedTrace F E` agrees with `normalizedTrace F K` on `E`.
- `normalizedTrace_trans`: for a tower `K / E / F` of algebraic extensions, the normalized trace
  from `K to `E` composed with the normalized trace from `E` to `F` equals the normalized trace
  from `K` to `F`.
- `normalizedTrace_self`: `normalizedTrace F F` is the identity map.

-/

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open IntermediateField

/- The normalized trace function from an extension `K` to the base field `F`.
Note: this definition does not require the extension `K / F` to be integral (algebraic)
nor the fields to be of characteristic zero. -/
private noncomputable def normalizedTraceAux (a : K) : F :=
  (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)

private theorem normalizedTraceAux_def (a : K) : normalizedTraceAux F K a =
  (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a) := rfl

private theorem normalizedTraceAux_map {E : Type*} [Field E] [Algebra F E] (f : E →ₐ[F] K) (a : E) :
    normalizedTraceAux F K (f a) = normalizedTraceAux F E a := by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTraceAux, ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
  exact trace_eq_of_algEquiv e <| AdjoinSimple.gen F a

private theorem normalizedTraceAux_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTraceAux F K a = normalizedTraceAux F E a :=
  normalizedTraceAux_map F K E.val a

variable [CharZero F]

variable {K} in
private theorem normalizedTraceAux_eq_of_fininteDimensional [FiniteDimensional F K] (a : K) :
    normalizedTraceAux F K a = (Module.finrank F K : F)⁻¹ • trace F K a := by
  have h := (Nat.cast_ne_zero (R := F)).mpr <|
    Nat.pos_iff_ne_zero.mp <| Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [smul_eq_mul, mul_comm, ← div_eq_mul_inv, trace_eq_trace_adjoin F a,
    ← Module.finrank_mul_finrank F F⟮a⟯ K, nsmul_eq_mul, Nat.cast_mul, mul_comm,
    mul_div_mul_right _ _ h, div_eq_mul_inv, mul_comm, ← smul_eq_mul, normalizedTraceAux_def]

variable [Algebra.IsIntegral F K]

/-- The normalized trace map from an algebraic extension `K` to the base field `F`. -/
noncomputable def normalizedTrace : K →ₗ[F] F where
  toFun := normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
    have ha : a ∈ E := (le_sup_left : F⟮a⟯ ≤ E) <| mem_adjoin_simple_self F a
    have hb : b ∈ E := (le_sup_right : F⟮b⟯ ≤ E) <| mem_adjoin_simple_self F b
    have hab : a + b ∈ E := IntermediateField.add_mem E ha hb
    let a' : E := ⟨a, ha⟩
    let b' : E := ⟨b, hb⟩
    let ab' : E := ⟨a + b, hab⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K b',
      normalizedTraceAux_intermediateField F K ab',
      normalizedTraceAux_eq_of_fininteDimensional F a',
      normalizedTraceAux_eq_of_fininteDimensional F b',
      normalizedTraceAux_eq_of_fininteDimensional F ab',
      ← smul_add, ← map_add, AddMemClass.mk_add_mk]
  map_smul' m a := by
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    let E := F⟮a⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have ha : a ∈ E := mem_adjoin_simple_self F a
    have hma : m • a ∈ E := smul_mem E ha
    let a' : E := ⟨a, ha⟩
    let ma' : E := ⟨m • a, hma⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K ma',
      normalizedTraceAux_eq_of_fininteDimensional F a',
      normalizedTraceAux_eq_of_fininteDimensional F ma',
      smul_comm, ← map_smul _ m, SetLike.mk_smul_mk]

theorem normalizedTrace_def (a : K) : normalizedTrace F K a =
    (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a) :=
  rfl

variable {K} in
/-- Normalized trace defined purely in terms of the degree and the next coefficient of the minimal
polynomial. Could be an alternative definition but it is harder to work with linearity. -/
theorem normalizedTrace_minpoly (a : K) :
    normalizedTrace F K a = ((minpoly F a).natDegree : F)⁻¹ • -(minpoly F a).nextCoeff :=
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a

variable {F} in
theorem normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a := by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_fininteDimensional F a, Module.finrank_self F,
    Nat.cast_one, inv_one, one_smul, trace_self_apply]

@[simp]
theorem normalizedTrace_self : normalizedTrace F F = LinearMap.id :=
  LinearMap.ext normalizedTrace_self_apply

variable {K} in
theorem normalizedTrace_eq_of_fininteDimensional_apply [FiniteDimensional F K] (a : K) :
    normalizedTrace F K a = (Module.finrank F K : F)⁻¹ • trace F K a :=
  normalizedTraceAux_eq_of_fininteDimensional F a

theorem normalizedTrace_eq_of_fininteDimensional [FiniteDimensional F K] :
    normalizedTrace F K = (Module.finrank F K : F)⁻¹ • trace F K :=
  LinearMap.ext <| normalizedTrace_eq_of_fininteDimensional_apply F

/-- The normalized trace transfers via (injective) maps. -/
@[simp]
theorem normalizedTrace_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) (a : E) : normalizedTrace F K (f a) = normalizedTrace F E a :=
  normalizedTraceAux_map F K f a

/-- The normalized trace transfers via restriction to a subextension. -/
theorem normalizedTrace_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTrace F K a = normalizedTrace F E a :=
  normalizedTraceAux_intermediateField F K a

section IsScalarTower

variable (F E K : Type*) [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [Algebra.IsIntegral F E] [Algebra.IsIntegral F K]
variable [CharZero F]

@[simp]
theorem normalizedTrace_algebraMap_apply (a : E) :
    normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a :=
  normalizedTrace_map F K (IsScalarTower.toAlgHom F E K) a

@[simp]
theorem normalizedTrace_algebraMap :
    normalizedTrace F K ∘ₗ Algebra.linearMap E K = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_algebraMap_apply F E K

omit [Algebra.IsIntegral F E] in
/-- If all the coefficients of `minpoly E a` are in `F`, then the normalized trace of `a` from `K`
to `E` equals the normalized trace of `a` from `K` to `F`. -/
theorem normalizedTrace_algebraMap_of_lifts [CharZero E] [Algebra.IsIntegral E K] (a : K)
    (h : minpoly E a ∈ Polynomial.lifts (algebraMap F E)) :
    algebraMap F E (normalizedTrace F K a) = normalizedTrace E K a := by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  simp [normalizedTrace_minpoly F a, normalizedTrace_minpoly E a,
    ← minpoly.map_algebraMap ha h,
    (minpoly F a).natDegree_map,
    (minpoly F a).nextCoeff_map (algebraMap F E).injective,
    map_mul, map_neg]

/- An auxiliary result to prove `normalizedTrace_trans_apply`. It differs from
`normalizedTrace_trans_apply` only by the extra assumption about finiteness of `E` over `F`. -/
private theorem normalizedTrace_trans_apply_aux [FiniteDimensional F E] [Algebra.IsIntegral E K]
    [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a := by
  have : FiniteDimensional E E⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.isIntegral a)
  rw [normalizedTrace_def E K, inv_natCast_smul_eq (R := E) (S := F), map_smul,
    normalizedTrace_eq_of_fininteDimensional F E, LinearMap.smul_apply, ← smul_assoc,
    smul_eq_mul (a := _⁻¹), ← mul_inv, trace_trace, mul_comm,
    ← Nat.cast_mul, Module.finrank_mul_finrank, eq_comm]
  let E' := E⟮a⟯.restrictScalars F
  have : FiniteDimensional F E' := Module.Finite.trans E E⟮a⟯
  have h_finrank_eq : Module.finrank F E⟮a⟯ = Module.finrank F E' := rfl
  have h_trace_eq : trace F E⟮a⟯ (AdjoinSimple.gen E a) = trace F E' (AdjoinSimple.gen E a : E') :=
    rfl
  let a' : E' := AdjoinSimple.gen E a
  rw [h_finrank_eq, h_trace_eq, ← normalizedTrace_eq_of_fininteDimensional_apply F,
    ← normalizedTrace_intermediateField F K a']
  congr

/-- For a tower `K / E / F` of algebraic extensions, the normalized trace from `K` to `E` composed
with the normalized trace from `E` to `F` equals the normalized trace from `K` to `F`. -/
theorem normalizedTrace_trans_apply [Algebra.IsIntegral E K] [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a :=
  let S : Set E := (minpoly E a).coeffs
  let E₀ := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral E₀ E := IsIntegral.tower_top F
  have : Algebra.IsIntegral E₀ K := IsIntegral.trans E
  have hsub : S ⊆ (algebraMap E₀ E).range :=
    Subalgebra.range_algebraMap E₀.toSubalgebra ▸ IntermediateField.subset_adjoin F S
  have hlifts := (Polynomial.lifts_iff_coeffs_subset_range _).mpr hsub
  (normalizedTrace_trans_apply_aux F E₀ K _ ▸
    normalizedTrace_algebraMap_apply F E₀ E _ ▸
    congrArg (normalizedTrace F E) (normalizedTrace_algebraMap_of_lifts E₀ E K a hlifts)).symm

@[simp]
theorem normalizedTrace_trans [Algebra.IsIntegral E K] [CharZero E] :
    normalizedTrace F E ∘ₗ normalizedTrace E K = normalizedTrace F K :=
  LinearMap.ext <| normalizedTrace_trans_apply F E K

end IsScalarTower

theorem normalizedTrace_algebraMap_apply_eq_self (a : F) :
    normalizedTrace F K (algebraMap F K a) = a := by simp

/-- The normalized trace map is a left inverse of the algebra map. -/
theorem normalizedTrace_algebraMap_eq_id :
    normalizedTrace F K ∘ₗ Algebra.linearMap F K = LinearMap.id :=
  LinearMap.ext <| normalizedTrace_algebraMap_apply_eq_self F K

/-- The normalized trace commutes with (injective) maps. -/
@[simp]
theorem normalizedTrace_comp_algHom {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) : normalizedTrace F K ∘ₗ f = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_map F K f

theorem normalizedTrace_surjective : Function.Surjective (normalizedTrace F K) :=
  fun a ↦ ⟨algebraMap F K a, normalizedTrace_algebraMap_apply_eq_self F K a⟩

/-- The normalized trace map is non-trivial. -/
theorem normalizedTrace_ne_zero : normalizedTrace F K ≠ 0 :=
  let ⟨a, ha⟩ := normalizedTrace_surjective F K 1
  DFunLike.ne_iff.mpr <| ⟨a, ha ▸ one_ne_zero⟩

end Algebra
