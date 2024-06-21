/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.Algebra.Group.Ext
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

#align_import category_theory.preadditive.schur from "leanprover-community/mathlib"@"58a272265b5e05f258161260dd2c5d247213cbd3"

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category C]
variable [Preadditive C]

-- See also `epi_of_nonzero_to_simple`, which does not require `Preadditive C`.
theorem mono_of_nonzero_from_simple [HasKernels C] {X Y : C} [Simple X] {f : X ⟶ Y} (w : f ≠ 0) :
    Mono f :=
  Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)
#align category_theory.mono_of_nonzero_from_simple CategoryTheory.mono_of_nonzero_from_simple

/-- The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
theorem isIso_of_hom_simple
    [HasKernels C] {X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : IsIso f :=
  haveI := mono_of_nonzero_from_simple w
  isIso_of_mono_of_nonzero w
#align category_theory.is_iso_of_hom_simple CategoryTheory.isIso_of_hom_simple

/-- As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
theorem isIso_iff_nonzero [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X ⟶ Y) :
    IsIso f ↔ f ≠ 0 :=
  ⟨fun I => by
    intro h
    apply id_nonzero X
    simp only [← IsIso.hom_inv_id f, h, zero_comp],
   fun w => isIso_of_hom_simple w⟩
#align category_theory.is_iso_iff_nonzero CategoryTheory.isIso_iff_nonzero

open scoped Classical in
/-- In any preadditive category with kernels,
the endomorphisms of a simple object form a division ring. -/
noncomputable instance [HasKernels C] {X : C} [Simple X] : DivisionRing (End X) where
  inv f := if h : f = 0 then 0 else haveI := isIso_of_hom_simple h; inv f
  exists_pair_ne := ⟨𝟙 X, 0, id_nonzero _⟩
  inv_zero := dif_pos rfl
  mul_inv_cancel f hf := by
    dsimp
    rw [dif_neg hf]
    haveI := isIso_of_hom_simple hf
    exact IsIso.inv_hom_id f
  nnqsmul := _
  qsmul := _

open FiniteDimensional

section

variable (𝕜 : Type*) [DivisionRing 𝕜]

/-- Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
theorem finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear 𝕜 C] {X Y : C}
    [Simple X] [Simple Y] (h : (X ≅ Y) → False) : finrank 𝕜 (X ⟶ Y) = 0 :=
  haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (isIso_iff_nonzero f)
      simp only [Classical.not_not, Ne] at p
      exact p.mp fun _ => h (asIso f)
  finrank_zero_of_subsingleton
#align category_theory.finrank_hom_simple_simple_eq_zero_of_not_iso CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso

end

variable (𝕜 : Type*) [Field 𝕜]
variable [IsAlgClosed 𝕜] [Linear 𝕜 C]

-- Porting note: the defeq issue in lean3 described below is no longer a problem in Lean4.
-- In the proof below we have some difficulty using `I : FiniteDimensional 𝕜 (X ⟶ X)`
-- where we need a `FiniteDimensional 𝕜 (End X)`.
-- These are definitionally equal, but without eta reduction Lean can't see this.
-- To get around this, we use `convert I`,
-- then check the various instances agree field-by-field,
-- We prove this with the explicit `isIso_iff_nonzero` assumption,
-- rather than just `[Simple X]`, as this form is useful for
-- Müger's formulation of semisimplicity.
/-- An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
theorem finrank_endomorphism_eq_one {X : C} (isIso_iff_nonzero : ∀ f : X ⟶ X, IsIso f ↔ f ≠ 0)
    [I : FiniteDimensional 𝕜 (X ⟶ X)] : finrank 𝕜 (X ⟶ X) = 1 := by
  have id_nonzero := (isIso_iff_nonzero (𝟙 X)).mp (by infer_instance)
  refine finrank_eq_one (𝟙 X) id_nonzero ?_
  intro f
  have : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
  have : FiniteDimensional 𝕜 (End X) := I
  obtain ⟨c, nu⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional 𝕜 (End.of f)
  use c
  rw [spectrum.mem_iff, IsUnit.sub_iff, isUnit_iff_isIso, isIso_iff_nonzero, Ne,
    Classical.not_not, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at nu
  exact nu.symm
#align category_theory.finrank_endomorphism_eq_one CategoryTheory.finrank_endomorphism_eq_one

variable [HasKernels C]

/-- **Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] :
    finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_eq_one 𝕜 isIso_iff_nonzero
#align category_theory.finrank_endomorphism_simple_eq_one CategoryTheory.finrank_endomorphism_simple_eq_one

theorem endomorphism_simple_eq_smul_id {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)]
    (f : X ⟶ X) : ∃ c : 𝕜, c • 𝟙 X = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X)
    f
#align category_theory.endomorphism_simple_eq_smul_id CategoryTheory.endomorphism_simple_eq_smul_id

/-- Endomorphisms of a simple object form a field if they are finite dimensional.
This can't be an instance as `𝕜` would be undetermined.
-/
noncomputable def fieldEndOfFiniteDimensional (X : C) [Simple X] [I : FiniteDimensional 𝕜 (X ⟶ X)] :
    Field (End X) := by
  classical exact
    { (inferInstance : DivisionRing (End X)) with
      mul_comm := fun f g => by
        obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 f
        obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 g
        simp [← mul_smul, mul_comm c d] }
#align category_theory.field_End_of_finite_dimensional CategoryTheory.fieldEndOfFiniteDimensional

-- There is a symmetric argument that uses `[FiniteDimensional 𝕜 (Y ⟶ Y)]` instead,
-- but we don't bother proving that here.
/-- **Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
theorem finrank_hom_simple_simple_le_one (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)] [Simple X]
    [Simple Y] : finrank 𝕜 (X ⟶ Y) ≤ 1 := by
  obtain (h|h) := subsingleton_or_nontrivial (X ⟶ Y)
  · rw [finrank_zero_of_subsingleton]
    exact zero_le_one
  · obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h
    haveI fi := (isIso_iff_nonzero f).mpr nz
    refine finrank_le_one f ?_
    intro g
    obtain ⟨c, w⟩ := endomorphism_simple_eq_smul_id 𝕜 (g ≫ inv f)
    exact ⟨c, by simpa using w =≫ f⟩
#align category_theory.finrank_hom_simple_simple_le_one CategoryTheory.finrank_hom_simple_simple_le_one

theorem finrank_hom_simple_simple_eq_one_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
    [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = 1 ↔ Nonempty (X ≅ Y) := by
  fconstructor
  · intro h
    rw [finrank_eq_one_iff'] at h
    obtain ⟨f, nz, -⟩ := h
    rw [← isIso_iff_nonzero] at nz
    exact ⟨asIso f⟩
  · rintro ⟨f⟩
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (isIso_iff_nonzero f.hom).mp inferInstance⟩
    omega
#align category_theory.finrank_hom_simple_simple_eq_one_iff CategoryTheory.finrank_hom_simple_simple_eq_one_iff

theorem finrank_hom_simple_simple_eq_zero_iff (X Y : C) [FiniteDimensional 𝕜 (X ⟶ X)]
    [FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] :
    finrank 𝕜 (X ⟶ Y) = 0 ↔ IsEmpty (X ≅ Y) := by
  rw [← not_nonempty_iff, ← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)]
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  have := finrank_hom_simple_simple_le_one 𝕜 X Y
  interval_cases finrank 𝕜 (X ⟶ Y)
  · rfl
  · exact False.elim (h rfl)
#align category_theory.finrank_hom_simple_simple_eq_zero_iff CategoryTheory.finrank_hom_simple_simple_eq_zero_iff

open scoped Classical

theorem finrank_hom_simple_simple (X Y : C) [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X]
    [Simple Y] : finrank 𝕜 (X ⟶ Y) = if Nonempty (X ≅ Y) then 1 else 0 := by
  split_ifs with h
  · exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h
  · exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h)
#align category_theory.finrank_hom_simple_simple CategoryTheory.finrank_hom_simple_simple

end CategoryTheory
