/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
import Mathlib.RingTheory.Trace.Basic

/-!

# Normalized trace

This file defines *normalized trace* map, that is, an `F`-linear map from the algebraic closure
of `F` to `F` defined as the trace of an element divided by it's degree.

## Main definitions

- `normalizedTrace`: a non-trivial `F`-linear map from an arbitrary algebraic extension `K` to `F`.

## Main results

- `normalizedTrace_intermediateField`: for a tower `K / E / F`, `normalizedTrace F E` agrees with
  `normalizedTrace F K` on `E`.
- `normalizedTrace_self`: `normalizedTrace F F` is the identity map.

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open IntermediateField

/-- The normalized trace function from an extension `K` to the base field `F`.
Note: this definition does not require the extension `K / F` to be integral (algebraic)
nor the fields to be of characteristic zero. -/
noncomputable def normalizedTrace' (a : K) : F :=
  Algebra.trace F F⟮a⟯ (AdjoinSimple.gen F a) / Module.finrank F F⟮a⟯

theorem normalizedTrace'_map {E : Type*} [Field E] [Algebra F E] (f : E →ₐ[F] K) (a : E) :
    normalizedTrace' F K (f a) = normalizedTrace' F E a := by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTrace', ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
  exact Algebra.trace_eq_of_algEquiv e <| AdjoinSimple.gen F a

theorem normalizedTrace'_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTrace' F K a = normalizedTrace' F E a :=
  normalizedTrace'_map F K E.val a

variable [CharZero F]

variable {K} in
theorem normalizedTrace'_eq_of_fininteDimensional [FiniteDimensional F K] (a : K) :
    normalizedTrace' F K a = Algebra.trace F K a / Module.finrank F K := by
  have h := (Nat.cast_ne_zero (R := F)).mpr <|
    Nat.pos_iff_ne_zero.mp <| Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [trace_eq_trace_adjoin F a, ← Module.finrank_mul_finrank F F⟮a⟯ K,
    nsmul_eq_mul, Nat.cast_mul,
    mul_comm, mul_div_mul_right _ _ h]
  rfl

variable [Algebra.IsIntegral F K]

/-- The normalized trace map from an algebraic extension `K` to the base field `F`. -/
noncomputable def normalizedTrace : K →ₗ[F] F where
  toFun := normalizedTrace' F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    haveI : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
    haveI : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral b)
    haveI : FiniteDimensional F E := finiteDimensional_sup F⟮a⟯ F⟮b⟯
    have ha : a ∈ E := (le_sup_left : F⟮a⟯ ≤ E) <| mem_adjoin_simple_self F a
    have hb : b ∈ E := (le_sup_right : F⟮b⟯ ≤ E) <| mem_adjoin_simple_self F b
    have hab : a + b ∈ E := IntermediateField.add_mem E ha hb
    let a' : E := ⟨a, ha⟩
    let b' : E := ⟨b, hb⟩
    let ab' : E := ⟨a + b, hab⟩
    rw [normalizedTrace'_intermediateField F K a',
      normalizedTrace'_intermediateField F K b',
      normalizedTrace'_intermediateField F K ab',
      normalizedTrace'_eq_of_fininteDimensional F a',
      normalizedTrace'_eq_of_fininteDimensional F b',
      normalizedTrace'_eq_of_fininteDimensional F ab',
      ← add_div, ← map_add]
    rfl
  map_smul' m a := by
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    let E := F⟮a⟯
    haveI : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
    have ha : a ∈ E := mem_adjoin_simple_self F a
    have hma : m • a ∈ E := smul_mem E ha
    let a' : E := ⟨a, ha⟩
    let ma' : E := ⟨m • a, hma⟩
    rw [normalizedTrace'_intermediateField F K a',
      normalizedTrace'_intermediateField F K ma',
      normalizedTrace'_eq_of_fininteDimensional F a',
      normalizedTrace'_eq_of_fininteDimensional F ma',
      ← smul_div_assoc, ← map_smul]
    rfl

variable {F} in
/-- The normalized trace map `normalizedTrace' F F` is identity. -/
theorem normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a := by
  dsimp [normalizedTrace]
  rw [normalizedTrace'_eq_of_fininteDimensional F a, Module.finrank_self F,
    Nat.cast_one, div_one, Algebra.trace_self_apply]

/-- The normalized trace map `normalizedTrace' F F` is identity. -/
@[simp]
theorem normalizedTrace_self : normalizedTrace F F = LinearMap.id :=
  LinearMap.ext normalizedTrace_self_apply

@[simp]
theorem normalizedTrace_algebraMap_apply (a : F) : normalizedTrace F K (algebraMap F K a) = a :=
  (Algebra.ofId_apply K a ▸
    normalizedTrace'_map F K (Algebra.ofId F K) a).trans (normalizedTrace_self_apply a)

/-- The normalized trace map is a left inverse of the algebra map. -/
@[simp]
theorem normalizedTrace_algebraMap : normalizedTrace F K ∘ algebraMap F K = id :=
  funext <| normalizedTrace_algebraMap_apply F K

/-- The normalized trace transfers via (injective) maps. -/
@[simp]
theorem normalizedTrace_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) (a : E) : normalizedTrace F K (f a) = normalizedTrace F E a :=
  normalizedTrace'_map F K f a

/-- The normalized trace commutes with (injective) maps. -/
@[simp]
theorem normalizedTrace_comp {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) : normalizedTrace F K ∘ₗ f = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_map F K f

/-- The normalized trace transfers via restriction to a subextension. -/
theorem normalizedTrace_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTrace F K a = normalizedTrace F E a :=
  normalizedTrace'_intermediateField F K a

theorem normalizedTrace_eq_of_fininteDimensional [FiniteDimensional F K] :
    normalizedTrace F K = (Module.finrank F K : F)⁻¹ • Algebra.trace F K := by
  ext x
  rw [LinearMap.smul_apply, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  apply normalizedTrace'_eq_of_fininteDimensional

/-- The normalized trace map is non-trivial. -/
theorem nontrivial_normalizedTrace : normalizedTrace F K ≠ 0 :=
  DFunLike.ne_iff.mpr
    ⟨1, (map_one (algebraMap F K) ▸ normalizedTrace_algebraMap_apply F K 1) ▸ one_ne_zero⟩
