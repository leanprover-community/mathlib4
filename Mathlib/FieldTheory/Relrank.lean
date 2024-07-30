/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin

/-!

# Relative rank of intermediate fields

This file contains basics about the relative rank of intermediate fields.

## Main definitions

- `IntermediateField.relrank A B`: defined to be `[B : A ⊓ B]` as a `Cardinal`.
  In particular, when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
  This is similar to `Subgroup.relindex` but it is `Cardinal` valued.

- `IntermediateField.relfinrank A B`: the `Nat` version of `IntermediateField.relrank A B`.
  If `B / A ⊓ B` is an infinite extension, then it is zero.
  This is similar to `Subgroup.relindex`.

-/

open IntermediateField FiniteDimensional

noncomputable section

--------

-- #15193

section Adhoc

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

theorem _root_.IntermediateField.map_comap_eq (f : L →ₐ[K] L') (S : IntermediateField K L') :
    (S.comap f).map f = S ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

theorem _root_.IntermediateField.map_comap_eq_self
    {f : L →ₐ[K] L'} {S : IntermediateField K L'} (h : S ≤ f.fieldRange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using IntermediateField.map_comap_eq f S

theorem _root_.IntermediateField.map_comap_eq_self_of_surjective
    {f : L →ₐ[K] L'} (hf : Function.Surjective f) (S : IntermediateField K L') :
    (S.comap f).map f = S :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)

theorem _root_.IntermediateField.comap_map
    (f : L →ₐ[K] L') (S : IntermediateField K L) :
    (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end Adhoc

--------

universe u v w

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable {L : Type w} [Field L] [Algebra F L]

variable (A B C : IntermediateField F E)

namespace IntermediateField

/-- `A.relrank B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relindex` but it is `Cardinal` valued. -/
def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

/-- The `Nat` version of `relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero. -/
def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

theorem relfinrank_def' : relfinrank A B = Cardinal.toNat (relrank A B) := rfl

variable {A B C}

theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C := by
  simp_rw [relrank]
  congr!

theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(Cardinal.toNat $(relrank_eq_of_inf_eq h))

/-- If `A ≤ B`, then `A.relrank B` is `[B : A]` -/
theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) := by
  rw [relrank]
  have := inf_of_le_left h
  congr!

/-- If `A ≤ B`, then `A.relfinrank B` is `[B : A]` -/
theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(Cardinal.toNat $(relrank_eq_rank_of_le h))

variable (A B C)

theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)

theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(Cardinal.toNat $(inf_relrank_right A B))

theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]

theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(Cardinal.toNat $(inf_relrank_left A B))

@[simp]
theorem relrank_self : relrank A A = 1 := by
  rw [relrank_eq_rank_of_le (le_refl A)]
  have : extendScalars (le_refl A) = ⊥ := restrictScalars_injective F (by simp)
  convert IntermediateField.rank_bot (F := A) (E := E)

@[simp]
theorem relfinrank_self : relfinrank A A = 1 := by
  simp [relfinrank_def']

variable {A B} in
theorem relrank_eq_one_of_le (h : B ≤ A) : relrank A B = 1 := by
  rw [← inf_relrank_right, inf_eq_right.2 h, relrank_self]

variable {A B} in
theorem relfinrank_eq_one_of_le (h : B ≤ A) : relfinrank A B = 1 := by
  simp [relfinrank_def', relrank_eq_one_of_le h]

theorem lift_rank_comap (f : L →ₐ[F] E) :
    Cardinal.lift.{v} (Module.rank (A.comap f) L) = Cardinal.lift.{w} (relrank A f.fieldRange) := by
  let j := f.restrictDomain (A.comap f)
  have hj : j.fieldRange = A ⊓ f.fieldRange := by
    ext x
    simp_rw [AlgHom.mem_fieldRange, Subtype.exists, mem_inf]
    constructor
    · rintro ⟨a, h, rfl⟩
      exact ⟨(A.toSubalgebra.mem_comap f a).1 h, a, rfl⟩
    · rintro ⟨h, ⟨a, rfl⟩⟩
      exact ⟨a, (A.toSubalgebra.mem_comap f a).2 h, rfl⟩
  exact Algebra.lift_rank_eq_of_equiv_equiv ((AlgEquiv.ofInjectiveField j).trans (equivOfEq hj))
    (AlgEquiv.ofInjectiveField f).toRingEquiv rfl

theorem rank_comap {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [Cardinal.lift_id] using A.lift_rank_comap f

theorem finrank_comap (f : L →ₐ[F] E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using congr(Cardinal.toNat $(lift_rank_comap A f))

theorem lift_relrank_comap (f : L →ₐ[F] E) (B : IntermediateField F L) :
    Cardinal.lift.{v} (relrank (A.comap f) B) = Cardinal.lift.{w} (relrank A (B.map f)) := by
  let j := f.restrictDomain ↥(A.comap f ⊓ B)
  have hj : j.fieldRange = A ⊓ B.map f := by
    ext x
    simp_rw [AlgHom.mem_fieldRange, Subtype.exists, mem_inf]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      exact ⟨(A.toSubalgebra.mem_comap f a).1 h1, a, h2, rfl⟩
    · rintro ⟨h1, a, h2, rfl⟩
      exact ⟨a, ⟨(A.toSubalgebra.mem_comap f a).2 h1, h2⟩, rfl⟩
  exact Algebra.lift_rank_eq_of_equiv_equiv ((AlgEquiv.ofInjectiveField j).trans (equivOfEq hj))
    (equivMap B f).toRingEquiv rfl

theorem relrank_comap {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E)
    (B : IntermediateField F L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [Cardinal.lift_id] using A.lift_relrank_comap f B

theorem relfinrank_comap (f : L →ₐ[F] E) (B : IntermediateField F L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using congr(Cardinal.toNat $(lift_relrank_comap A f B))

theorem lift_relrank_map_map (f : E →ₐ[F] L) :
    Cardinal.lift.{v} (relrank (A.map f) (B.map f)) = Cardinal.lift.{w} (relrank A B) := by
  rw [← lift_relrank_comap, comap_map]

theorem relrank_map_map {L : Type v} [Field L] [Algebra F L] (f : E →ₐ[F] L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [Cardinal.lift_id] using lift_relrank_map_map A B f

theorem relfinrank_map_map (f : E →ₐ[F] L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using congr(Cardinal.toNat $(lift_relrank_map_map A B f))

theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L →ₐ[F] E) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) =
    Cardinal.lift.{w} (relrank A (B ⊓ f.fieldRange)) := by
  conv_lhs => rw [← lift_relrank_map_map _ _ f, map_comap_eq, map_comap_eq]
  congr 1
  apply relrank_eq_of_inf_eq
  rw [inf_assoc, inf_left_comm _ B, inf_of_le_left (le_refl _)]

theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [Cardinal.lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L →ₐ[F] E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using congr(Cardinal.toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) =
    Cardinal.lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [Cardinal.lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using congr(Cardinal.toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L →ₐ[F] E) (h : Function.Surjective f) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) =
    Cardinal.lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ ↦ h x

theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L →ₐ[F] E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using congr(Cardinal.toNat
    $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
theorem relrank_mul_rank_top (h : A ≤ B) : relrank A B * Module.rank B E = Module.rank A E := by
  rw [relrank_eq_rank_of_le h]
  letI : Algebra A B := (inclusion h).toAlgebra
  haveI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E

variable {A B} in
theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using congr(Cardinal.toNat $(relrank_mul_rank_top h))

variable {A B} in
theorem rank_bot_mul_relrank (h : A ≤ B) : Module.rank F A * relrank A B = Module.rank F B := by
  rw [relrank_eq_rank_of_le h]
  letI : Algebra A B := (inclusion h).toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank F A B

variable {A B} in
theorem finrank_bot_mul_relfinrank (h : A ≤ B) : finrank F A * relfinrank A B = finrank F B := by
  simpa using congr(Cardinal.toNat $(rank_bot_mul_relrank h))

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
  simpa using congr(Cardinal.toNat $(relrank_mul_relrank h1 h2))

theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C := by
  rw [← inf_relrank_right A (B ⊓ C), ← inf_relrank_right B C, ← inf_relrank_right (A ⊓ B) C,
    inf_assoc, relrank_mul_relrank inf_le_right inf_le_right]

theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using congr(Cardinal.toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
theorem relrank_mul_relrank_eq_inf_relrank (h : B ≤ C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B ≤ C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using congr(Cardinal.toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
theorem relrank_inf_mul_relrank_of_le (h : A ≤ B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
theorem relfinrank_inf_mul_relfinrank_of_le (h : A ≤ B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using congr(Cardinal.toNat $(relrank_inf_mul_relrank_of_le C h))

@[simp]
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := by
  simp [relfinrank_def']

@[simp]
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [← relrank_mul_rank_top (show A ≤ ⊤ from le_top), IntermediateField.rank_top, mul_one]

@[simp]
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_def', finrank]

@[simp]
theorem relrank_bot_left : relrank ⊥ A = Module.rank F A := by
  rw [← rank_bot_mul_relrank (show ⊥ ≤ A from bot_le), IntermediateField.rank_bot, one_mul]

@[simp]
theorem relfinrank_bot_left : relfinrank ⊥ A = finrank F A := by
  simp [relfinrank_def', finrank]

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
