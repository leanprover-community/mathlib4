/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Tower
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Results on finite dimensionality and algebraicity of intermediate fields.
-/

open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {S : IntermediateField K L}

theorem IntermediateField.coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
    [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

/-- Turn an algebraic subalgebra into an intermediate field, `Subalgebra.IsAlgebraic` version. -/
def Subalgebra.IsAlgebraic.toIntermediateField {S : Subalgebra K L} (hS : S.IsAlgebraic) :
    IntermediateField K L where
  toSubalgebra := S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin

/-- Turn an algebraic subalgebra into an intermediate field, `Algebra.IsAlgebraic` version. -/
abbrev Algebra.IsAlgebraic.toIntermediateField (S : Subalgebra K L) [Algebra.IsAlgebraic K S] :
    IntermediateField K L := (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

namespace IntermediateField

instance isAlgebraic_tower_bot [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic K S :=
  Algebra.IsAlgebraic.of_injective S.val S.val.injective

instance isAlgebraic_tower_top [Algebra.IsAlgebraic K L] : Algebra.IsAlgebraic S L :=
  Algebra.IsAlgebraic.tower_top (K := K) S

section FiniteDimensional

variable (F E : IntermediateField K L)

instance finiteDimensional_left [FiniteDimensional K L] : FiniteDimensional K F := .left K F L
instance finiteDimensional_right [FiniteDimensional K L] : FiniteDimensional F L := .right K F L

@[simp]
theorem rank_eq_rank_subalgebra : Module.rank K F.toSubalgebra = Module.rank K F :=
  rfl

@[simp]
theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
  rfl

variable {F} {E}

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

theorem finrank_dvd_of_le_left (h : F ≤ E) : finrank E L ∣ finrank F L := by
  let _ := (inclusion h).toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  exact Dvd.intro_left (finrank F E) (finrank_mul_finrank F E L)

theorem finrank_dvd_of_le_right (h : F ≤ E) : finrank K F ∣ finrank K E := by
  let _ := (inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  exact Dvd.intro (finrank F E) (finrank_mul_finrank K F E)

theorem finrank_le_of_le_left [FiniteDimensional F L] (h : F ≤ E) : finrank E L ≤ finrank F L :=
  Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_left h)

theorem finrank_le_of_le_right [FiniteDimensional K E] (h : F ≤ E) : finrank K F ≤ finrank K E :=
  Nat.le_of_dvd Module.finrank_pos (finrank_dvd_of_le_right h)

/-- Mapping a finite dimensional intermediate field along an algebra equivalence gives
a finite-dimensional intermediate field. -/
instance finiteDimensional_map (f : L →ₐ[K] L) [FiniteDimensional K E] :
    FiniteDimensional K (E.map f) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap E f).toLinearEquiv

@[deprecated (since := "2025-05-02")]
alias _root_.im_finiteDimensional := IntermediateField.finiteDimensional_map

end FiniteDimensional

theorem isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L) :=
  (isAlgebraic_algebraMap_iff (algebraMap S L).injective).symm

theorem isIntegral_iff {x : S} : IsIntegral K x ↔ IsIntegral K (x : L) :=
  (isIntegral_algHom_iff S.val S.val.injective).symm

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
