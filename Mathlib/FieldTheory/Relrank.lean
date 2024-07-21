/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Normal

/-!

# Relative rank of intermediate fields

In this file we define `IntermediateField.relrank A B`,
which is `[B : A ⊓ B]`, in particular, when `A ≤ B` it is `[B : A]`,
the degree of the field extension `B / A`. This is similar to `Subgroup.relindex`.

-/

open IntermediateField

noncomputable section

universe u v w

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable {L : Type w} [Field L] [Algebra F L]

variable (A B C : IntermediateField F E)

namespace IntermediateField

/-- `A.relrank B` is defined to be `[B : A ⊓ B]`, in particular, when `A ≤ B` it is `[B : A]`,
the degree of the field extension `B / A`. This is similar to `Subgroup.relindex`. -/
def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

variable {A B} in
theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) := by
  rw [relrank]
  have := inf_of_le_left h
  congr!

theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)

theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]

@[simp]
theorem relrank_self : relrank A A = 1 := by
  rw [relrank_eq_rank_of_le (le_refl A)]
  have : extendScalars (le_refl A) = ⊥ := restrictScalars_injective F (by simp)
  convert IntermediateField.rank_bot (F := A) (E := E)

variable {A B} in
theorem relrank_eq_one_of_le (h : B ≤ A) : relrank A B = 1 := by
  rw [← inf_relrank_right, inf_eq_right.2 h, relrank_self]

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

variable {A B} in
theorem relrank_mul_rank_top (h : A ≤ B) : relrank A B * Module.rank B E = Module.rank A E := by
  rw [relrank_eq_rank_of_le h]
  letI : Algebra A B := (inclusion h).toAlgebra
  haveI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E

variable {A B} in
theorem rank_bot_mul_relrank (h : A ≤ B) : Module.rank F A * relrank A B = Module.rank F B := by
  rw [relrank_eq_rank_of_le h]
  letI : Algebra A B := (inclusion h).toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank F A B

variable {A B} in
theorem relrank_dvd_rank_top_of_le (h : A ≤ B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

theorem relrank_dvd_rank_bot : relrank A B ∣ Module.rank F B :=
  inf_relrank_right A B ▸ dvd_of_mul_left_eq _ (rank_bot_mul_relrank inf_le_right)

-- Subgroup.relindex_subgroupOf ???

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

theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C := by
  rw [← inf_relrank_right A (B ⊓ C), ← inf_relrank_right B C, ← inf_relrank_right (A ⊓ B) C,
    inf_assoc, relrank_mul_relrank inf_le_right inf_le_right]

variable {B C} in
theorem relrank_mul_relrank_eq_inf_relrank (h : B ≤ C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
theorem relrank_inf_mul_relrank_of_le (h : A ≤ B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

@[simp]
theorem relrank_sup_right [Normal F B] : B.relrank (A ⊔ B) = B.relrank A := by
  sorry

@[simp]
theorem relrank_sup_left [Normal F B] : B.relrank (B ⊔ A) = B.relrank A := by
  rw [sup_comm, relrank_sup_right]

theorem relrank_dvd_rank_top_of_normal [Normal F A] : A.relrank B ∣ Module.rank A E :=
  relrank_sup_right B A ▸ relrank_dvd_rank_top_of_le le_sup_right

variable {A B} in
theorem relrank_dvd_of_le_left (h : A ≤ B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

-- this is incorrect !!! e.g. A B are two deg 3 ext / Q, C is deg 6 ext / Q
-- need normal condition
variable {B C} in
theorem relrank_dvd_of_le_right (h : B ≤ C) : A.relrank B ∣ A.relrank C :=
  have := dvd_of_mul_right_eq _ (relrank_mul_relrank_eq_inf_relrank A h)
  sorry

-- Subgroup.relindex_inf_le
-- Subgroup.index_inf_le

@[simp]
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [← relrank_mul_rank_top (show A ≤ ⊤ from le_top), IntermediateField.rank_top, mul_one]

@[simp]
theorem relrank_bot_left : relrank ⊥ A = Module.rank F A := by
  rw [← rank_bot_mul_relrank (show ⊥ ≤ A from bot_le), IntermediateField.rank_bot, one_mul]

@[simp]
theorem relrank_bot_right : relrank A ⊥ = 1 := relrank_eq_one_of_le bot_le

end IntermediateField
