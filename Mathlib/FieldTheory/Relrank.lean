/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!

# Relative rank of subfields and intermediate fields

This file contains basics about the relative rank of subfields and intermediate fields.

## Main definitions

- `Subfield.relrank A B`, `IntermediateField.relrank A B`:
  defined to be `[B : A ⊓ B]` as a `Cardinal`.
  In particular, when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
  This is similar to `Subgroup.relindex` but it is `Cardinal` valued.

- `Subfield.relfinrank A B`, `IntermediateField.relfinrank A B`:
  the `Nat` version of `Subfield.relrank A B` and `IntermediateField.relrank A B`, respectively.
  If `B / A ⊓ B` is an infinite extension, then it is zero.
  This is similar to `Subgroup.relindex`.

-/

open Module Cardinal

universe u v w

namespace Subfield

variable {E : Type v} [Field E] {L : Type w} [Field L]

variable (A B C : Subfield E)

/-- `Subfield.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relindex` but it is `Cardinal` valued. -/
noncomputable def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

/-- The `Nat` version of `Subfield.relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero. -/
noncomputable def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

theorem relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B) := rfl

variable {A B C}

theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C := by
  simp_rw [relrank]
  congr!

theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

/-- If `A ≤ B`, then `Subfield.relrank A B` is `[B : A]`. -/
theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) := by
  rw [relrank]
  have := inf_of_le_left h
  congr!

/-- If `A ≤ B`, then `Subfield.relfinrank A B` is `[B : A]`. -/
theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)

theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)

theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))

theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]

theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

@[simp]
theorem relrank_self : relrank A A = 1 := by
  rw [relrank_eq_rank_of_le (le_refl A), extendScalars_self, IntermediateField.rank_bot]

@[simp]
theorem relfinrank_self : relfinrank A A = 1 := by
  simp [relfinrank_eq_toNat_relrank]

variable {A B} in
theorem relrank_eq_one_of_le (h : B ≤ A) : relrank A B = 1 := by
  rw [← inf_relrank_right, inf_eq_right.2 h, relrank_self]

variable {A B} in
theorem relfinrank_eq_one_of_le (h : B ≤ A) : relfinrank A B = 1 := by
  simp [relfinrank_eq_toNat_relrank, relrank_eq_one_of_le h]

variable {A B} in
theorem relrank_mul_rank_top (h : A ≤ B) : relrank A B * Module.rank B E = Module.rank A E := by
  rw [relrank_eq_rank_of_le h]
  letI : Algebra A B := (inclusion h).toAlgebra
  haveI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E

variable {A B} in
theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using congr(toNat $(relrank_mul_rank_top h))

@[simp]
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := relfinrank_eq_one_of_le le_top

@[simp]
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  let _ : AddCommMonoid (⊤ : IntermediateField A E) := inferInstance
  rw [relrank_eq_rank_of_le (show A ≤ ⊤ from le_top), extendScalars_top,
    IntermediateField.topEquiv.toLinearEquiv.rank_eq]

@[simp]
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_eq_toNat_relrank, finrank]

theorem lift_relrank_map_map (f : E →+* L) :
    lift.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B) :=
  -- typeclass inference is slow
  .symm <| Algebra.lift_rank_eq_of_equiv_equiv (((A ⊓ B).equivMapOfInjective f f.injective).trans
    <| .subringCongr <| by rw [← map_inf]; rfl) (B.equivMapOfInjective f f.injective) rfl

theorem relrank_map_map {L : Type v} [Field L] (f : E →+* L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_map_map A B f

theorem lift_relrank_comap (f : L →+* E) (B : Subfield L) :
    lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f)) :=
  (lift_relrank_map_map _ _ f).symm.trans <| congr_arg lift <| relrank_eq_of_inf_eq <| by
    rw [map_comap_eq, f.fieldRange_eq_map, inf_assoc, ← map_inf, top_inf_eq]

theorem relrank_comap {L : Type v} [Field L] (f : L →+* E)
    (B : Subfield L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [lift_id] using A.lift_relrank_comap f B

theorem relfinrank_comap (f : L →+* E) (B : Subfield L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using congr(toNat $(lift_relrank_comap A f B))

theorem lift_rank_comap (f : L →+* E) :
    lift.{v} (Module.rank (A.comap f) L) = lift.{w} (relrank A f.fieldRange) := by
  simpa only [relrank_top_right, ← RingHom.fieldRange_eq_map] using lift_relrank_comap A f ⊤

theorem rank_comap {L : Type v} [Field L] (f : L →+* E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [lift_id] using A.lift_rank_comap f

theorem finrank_comap (f : L →+* E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using congr(toNat $(lift_rank_comap A f))

theorem relfinrank_map_map (f : E →+* L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using congr(toNat $(lift_relrank_map_map A B f))

theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L →+* E) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A (B ⊓ f.fieldRange)) := by
  conv_lhs => rw [← lift_relrank_map_map _ _ f, map_comap_eq, map_comap_eq]
  congr 1
  apply relrank_eq_of_inf_eq
  rw [inf_assoc, inf_left_comm _ B, inf_of_le_left (le_refl _)]

theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] (f : L →+* E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L →+* E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L →+* E) (h : B ≤ f.fieldRange) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] (f : L →+* E) (h : B ≤ f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L →+* E) (h : B ≤ f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L →+* E) (h : Function.Surjective f) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ ↦ h x

theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] (f : L →+* E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L →+* E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
theorem relrank_dvd_rank_top_of_le (h : A ≤ B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

variable {A B} in
theorem relfinrank_dvd_finrank_top_of_le (h : A ≤ B) : relfinrank A B ∣ finrank A E :=
  dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

variable {A B C} in
theorem relrank_mul_relrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relrank A B * relrank B C = relrank A C := by
  have h3 := h1.trans h2
  rw [relrank_eq_rank_of_le h1, relrank_eq_rank_of_le h2, relrank_eq_rank_of_le h3]
  letI : Algebra A B := (inclusion h1).toAlgebra
  letI : Algebra B C := (inclusion h2).toAlgebra
  letI : Algebra A C := (inclusion h3).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B C

variable {A B C} in
theorem relfinrank_mul_relfinrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relfinrank A B * relfinrank B C = relfinrank A C := by
  simpa using congr(toNat $(relrank_mul_relrank h1 h2))

theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C := by
  rw [← inf_relrank_right A (B ⊓ C), ← inf_relrank_right B C, ← inf_relrank_right (A ⊓ B) C,
    inf_assoc, relrank_mul_relrank inf_le_right inf_le_right]

theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using congr(toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
theorem relrank_mul_relrank_eq_inf_relrank (h : B ≤ C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B ≤ C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
theorem relrank_inf_mul_relrank_of_le (h : A ≤ B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
theorem relfinrank_inf_mul_relfinrank_of_le (h : A ≤ B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using congr(toNat $(relrank_inf_mul_relrank_of_le C h))

variable {A B} in
theorem relrank_dvd_of_le_left (h : A ≤ B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

variable {A B} in
theorem relfinrank_dvd_of_le_left (h : A ≤ B) : B.relfinrank C ∣ A.relfinrank C :=
  dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

end Subfield

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable {L : Type w} [Field L] [Algebra F L]

variable (A B C : IntermediateField F E)

/-- `IntermediateField.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relindex` but it is `Cardinal` valued. -/
noncomputable def relrank := A.toSubfield.relrank B.toSubfield

/-- The `Nat` version of `IntermediateField.relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero. -/
noncomputable def relfinrank := A.toSubfield.relfinrank B.toSubfield

theorem relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B) := rfl

variable {A B C}

theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C :=
  Subfield.relrank_eq_of_inf_eq congr(toSubfield $h)

theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

/-- If `A ≤ B`, then `IntermediateField.relrank A B` is `[B : A]` -/
theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) :=
  Subfield.relrank_eq_rank_of_le h

/-- If `A ≤ B`, then `IntermediateField.relrank A B` is `[B : A]` -/
theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)

theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)

theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))

theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]

theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

@[simp]
theorem relrank_self : relrank A A = 1 := A.toSubfield.relrank_self

@[simp]
theorem relfinrank_self : relfinrank A A = 1 := A.toSubfield.relfinrank_self

variable {A B} in
theorem relrank_eq_one_of_le (h : B ≤ A) : relrank A B = 1 := by
  rw [← inf_relrank_right, inf_eq_right.2 h, relrank_self]

variable {A B} in
theorem relfinrank_eq_one_of_le (h : B ≤ A) : relfinrank A B = 1 := by
  simp [relfinrank_eq_toNat_relrank, relrank_eq_one_of_le h]

theorem lift_rank_comap (f : L →ₐ[F] E) :
    Cardinal.lift.{v} (Module.rank (A.comap f) L) = Cardinal.lift.{w} (relrank A f.fieldRange) :=
  A.toSubfield.lift_rank_comap f.toRingHom

theorem rank_comap {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [lift_id] using A.lift_rank_comap f

theorem finrank_comap (f : L →ₐ[F] E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using congr(toNat $(lift_rank_comap A f))

theorem lift_relrank_comap (f : L →ₐ[F] E) (B : IntermediateField F L) :
    Cardinal.lift.{v} (relrank (A.comap f) B) = Cardinal.lift.{w} (relrank A (B.map f)) :=
  A.toSubfield.lift_relrank_comap f.toRingHom B.toSubfield

theorem relrank_comap {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E)
    (B : IntermediateField F L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [lift_id] using A.lift_relrank_comap f B

theorem relfinrank_comap (f : L →ₐ[F] E) (B : IntermediateField F L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using congr(toNat $(lift_relrank_comap A f B))

theorem lift_relrank_map_map (f : E →ₐ[F] L) :
    Cardinal.lift.{v} (relrank (A.map f) (B.map f)) = Cardinal.lift.{w} (relrank A B) := by
  rw [← lift_relrank_comap, comap_map]

theorem relrank_map_map {L : Type v} [Field L] [Algebra F L] (f : E →ₐ[F] L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_map_map A B f

theorem relfinrank_map_map (f : E →ₐ[F] L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using congr(toNat $(lift_relrank_map_map A B f))

theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L →ₐ[F] E) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) =
    Cardinal.lift.{w} (relrank A (B ⊓ f.fieldRange)) :=
  A.toSubfield.lift_relrank_comap_comap_eq_lift_relrank_inf B.toSubfield f.toRingHom

theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L →ₐ[F] E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L →ₐ[F] E) (h : Function.Surjective f) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ ↦ h x

theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L →ₐ[F] E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
theorem relrank_mul_rank_top (h : A ≤ B) : relrank A B * Module.rank B E = Module.rank A E :=
  Subfield.relrank_mul_rank_top h

variable {A B} in
theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using congr(toNat $(relrank_mul_rank_top h))

variable {A B} in
theorem rank_bot_mul_relrank (h : A ≤ B) : Module.rank F A * relrank A B = Module.rank F B := by
  rw [relrank_eq_rank_of_le h]
  letI : Algebra A B := (inclusion h).toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank F A B

variable {A B} in
theorem finrank_bot_mul_relfinrank (h : A ≤ B) : finrank F A * relfinrank A B = finrank F B := by
  simpa using congr(toNat $(rank_bot_mul_relrank h))

variable {A B} in
theorem relrank_dvd_rank_top_of_le (h : A ≤ B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

variable {A B} in
theorem relfinrank_dvd_finrank_top_of_le (h : A ≤ B) : relfinrank A B ∣ finrank A E :=
  dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

theorem relrank_dvd_rank_bot : relrank A B ∣ Module.rank F B :=
  inf_relrank_right A B ▸ dvd_of_mul_left_eq _ (rank_bot_mul_relrank inf_le_right)

theorem relfinrank_dvd_finrank_bot : relfinrank A B ∣ finrank F B :=
  inf_relfinrank_right A B ▸ dvd_of_mul_left_eq _ (finrank_bot_mul_relfinrank inf_le_right)

variable {A B C} in
theorem relrank_mul_relrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relrank A B * relrank B C = relrank A C :=
  Subfield.relrank_mul_relrank h1 h2

variable {A B C} in
theorem relfinrank_mul_relfinrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relfinrank A B * relfinrank B C = relfinrank A C := by
  simpa using congr(toNat $(relrank_mul_relrank h1 h2))

theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C :=
  Subfield.relrank_inf_mul_relrank A.toSubfield B.toSubfield C.toSubfield

theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using congr(toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
theorem relrank_mul_relrank_eq_inf_relrank (h : B ≤ C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B ≤ C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
theorem relrank_inf_mul_relrank_of_le (h : A ≤ B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
theorem relfinrank_inf_mul_relfinrank_of_le (h : A ≤ B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using congr(toNat $(relrank_inf_mul_relrank_of_le C h))

@[simp]
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := relfinrank_eq_one_of_le le_top

@[simp]
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [← relrank_mul_rank_top (show A ≤ ⊤ from le_top), IntermediateField.rank_top, mul_one]

@[simp]
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]
theorem relrank_bot_left : relrank ⊥ A = Module.rank F A := by
  rw [← rank_bot_mul_relrank (show ⊥ ≤ A from bot_le), IntermediateField.rank_bot, one_mul]

@[simp]
theorem relfinrank_bot_left : relfinrank ⊥ A = finrank F A := by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]
theorem relrank_bot_right : relrank A ⊥ = 1 := relrank_eq_one_of_le bot_le

@[simp]
theorem relfinrank_bot_right : relfinrank A ⊥ = 1 := relfinrank_eq_one_of_le bot_le

variable {A B} in
theorem relrank_dvd_of_le_left (h : A ≤ B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

variable {A B} in
theorem relfinrank_dvd_of_le_left (h : A ≤ B) : B.relfinrank C ∣ A.relfinrank C :=
  dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

end IntermediateField
