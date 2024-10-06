/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Results on finite dimensionality and algebraicity of intermediate fields.
-/

open FiniteDimensional

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  {S : IntermediateField K L}

namespace IntermediateField

section FiniteDimensional

variable (F E : IntermediateField K L)

instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F :=
  left K F L

instance finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L :=
  right K F L

@[simp]
theorem rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl

@[simp]
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl

variable {F} {E}

@[simp]
theorem toSubalgebra_eq_iff : F.toSubalgebra = E.toSubalgebra ↔ F = E := by
  rw [SetLike.ext_iff, SetLike.ext'_iff, Set.ext_iff]
  rfl

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[E : K] ≤ [F : K]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_le [hfin : FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  haveI : Module.Finite K E.toSubalgebra := hfin
  toSubalgebra_injective <| Subalgebra.eq_of_le_of_finrank_le h_le h_finrank

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[F : K] = [E : K]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_eq [FiniteDimensional K E] (h_le : F ≤ E)
    (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

-- If `F ≤ E` are two intermediate fields of a finite extension `L / K` such that
-- `[L : F] ≤ [L : E]`, then `F = E`. Marked as private since it's a direct corollary of
-- `eq_of_le_of_finrank_le'` (the `FiniteDimensional K L` implies `FiniteDimensional F L`
-- automatically by typeclass resolution).
private theorem eq_of_le_of_finrank_le'' [FiniteDimensional K L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  apply eq_of_le_of_finrank_le h_le
  have h1 := finrank_mul_finrank K F L
  have h2 := finrank_mul_finrank K E L
  have h3 : 0 < finrank E L := finrank_pos
  nlinarith

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] ≤ [L : E]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_le' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L ≤ finrank E L) : F = E := by
  refine le_antisymm h_le (fun l hl ↦ ?_)
  rwa [← mem_extendScalars (le_refl F), eq_of_le_of_finrank_le''
    ((extendScalars_le_extendScalars_iff (le_refl F) h_le).2 h_le) h_finrank, mem_extendScalars]

/-- If `F ≤ E` are two intermediate fields of `L / K` such that `[L : F] = [L : E]` are finite,
then `F = E`. -/
theorem eq_of_le_of_finrank_eq' [FiniteDimensional F L] (h_le : F ≤ E)
    (h_finrank : finrank F L = finrank E L) : F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le

end FiniteDimensional

theorem isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L) :=
  (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm

theorem isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L) := by
  rw [← isAlgebraic_iff_isIntegral, isAlgebraic_iff, isAlgebraic_iff_isIntegral]

theorem minpoly_eq (x : S) : minpoly K x = minpoly K (x : L) :=
  (minpoly.algebraMap_eq (algebraMap S L).injective x).symm

end IntermediateField

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields. -/
def subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] :
    Subalgebra K L ≃o IntermediateField K L where
  toFun S := S.toIntermediateField fun x hx => S.inv_mem_of_algebraic
    (Algebra.IsAlgebraic.isAlgebraic ((⟨x, hx⟩ : S) : L))
  invFun S := S.toSubalgebra
  left_inv _ := toSubalgebra_toIntermediateField _ _
  right_inv := toIntermediateField_toSubalgebra
  map_rel_iff' := Iff.rfl

@[simp]
theorem mem_subalgebraEquivIntermediateField [Algebra.IsAlgebraic K L] {S : Subalgebra K L}
    {x : L} : x ∈ subalgebraEquivIntermediateField S ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_subalgebraEquivIntermediateField_symm [Algebra.IsAlgebraic K L]
    {S : IntermediateField K L} {x : L} :
    x ∈ subalgebraEquivIntermediateField.symm S ↔ x ∈ S :=
  Iff.rfl
