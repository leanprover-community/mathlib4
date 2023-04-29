/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.preadditive.hom_orthogonal
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Linear.Basic
import Mathbin.CategoryTheory.Preadditive.Biproducts
import Mathbin.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
# Hom orthogonal families.

A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.

We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.

When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.

If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
lemma hom_orthogonal.equiv_of_iso (o : hom_orthogonal s) {f : α → ι} {g : β → ι}
  (i : ⨁ (λ a, s (f a)) ≅ ⨁ (λ b, s (g b))) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/


open Classical Matrix

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A family of objects is "hom orthogonal" if
there is at most one morphism between distinct objects.

(In a category with zero morphisms, that must be the zero morphism.) -/
def HomOrthogonal {ι : Type _} (s : ι → C) : Prop :=
  ∀ i j, i ≠ j → Subsingleton (s i ⟶ s j)
#align category_theory.hom_orthogonal CategoryTheory.HomOrthogonal

namespace HomOrthogonal

variable {ι : Type _} {s : ι → C}

theorem eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) :
    f = 0 := by
  haveI := o i j w
  apply Subsingleton.elim
#align category_theory.hom_orthogonal.eq_zero CategoryTheory.HomOrthogonal.eq_zero

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`. -/
@[simps]
noncomputable def matrixDecomposition (o : HomOrthogonal s) {α β : Type} [Fintype α] [Fintype β]
    {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i))
    where
  toFun z i j k :=
    eqToHom
        (by
          rcases k with ⟨k, ⟨⟩⟩
          simp) ≫
      biproduct.components z k j ≫
        eqToHom
          (by
            rcases j with ⟨j, ⟨⟩⟩
            simp)
  invFun z :=
    biproduct.matrix fun j k =>
      if h : f j = g k then z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫ eqToHom (by simp [h]) else 0
  left_inv z := by
    ext (j k)
    simp only [category.assoc, biproduct.lift_π, biproduct.ι_matrix]
    split_ifs
    · simp
      rfl
    · symm
      apply o.eq_zero h
  right_inv z := by
    ext (i⟨j, w⟩⟨k, ⟨⟩⟩)
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    simp [w.symm]; rfl
#align category_theory.hom_orthogonal.matrix_decomposition CategoryTheory.HomOrthogonal.matrixDecomposition

end

section

variable [Preadditive C] [HasFiniteBiproducts C]

/-- `hom_orthogonal.matrix_decomposition` as an additive equivalence. -/
@[simps]
noncomputable def matrixDecompositionAddEquiv (o : HomOrthogonal s) {α β : Type} [Fintype α]
    [Fintype β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃+
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }
#align category_theory.hom_orthogonal.matrix_decomposition_add_equiv CategoryTheory.HomOrthogonal.matrixDecompositionAddEquiv

@[simp]
theorem matrixDecomposition_id (o : HomOrthogonal s) {α : Type} [Fintype α] {f : α → ι} (i : ι) :
    o.matrixDecomposition (𝟙 (⨁ fun a => s (f a))) i = 1 :=
  by
  ext (⟨b, ⟨⟩⟩⟨a⟩)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [category.comp_id, category.id_comp, category.assoc, End.one_def, eq_to_hom_refl,
    Matrix.one_apply, hom_orthogonal.matrix_decomposition_apply, biproduct.components]
  split_ifs with h
  · cases h
    simp
  · convert comp_zero
    simpa using biproduct.ι_π_ne _ (Ne.symm h)
#align category_theory.hom_orthogonal.matrix_decomposition_id CategoryTheory.HomOrthogonal.matrixDecomposition_id

theorem matrixDecomposition_comp (o : HomOrthogonal s) {α β γ : Type} [Fintype α] [Fintype β]
    [Fintype γ] {f : α → ι} {g : β → ι} {h : γ → ι} (z : (⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b))
    (w : (⨁ fun b => s (g b)) ⟶ ⨁ fun c => s (h c)) (i : ι) :
    o.matrixDecomposition (z ≫ w) i = o.matrixDecomposition w i ⬝ o.matrixDecomposition z i :=
  by
  ext (⟨c, ⟨⟩⟩⟨a⟩)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Matrix.mul_apply, limits.biproduct.components,
    hom_orthogonal.matrix_decomposition_apply, category.comp_id, category.id_comp, category.assoc,
    End.mul_def, eq_to_hom_refl, eq_to_hom_trans_assoc, Finset.sum_congr]
  conv_lhs => rw [← category.id_comp w, ← biproduct.total]
  simp only [preadditive.sum_comp, preadditive.comp_sum]
  apply Finset.sum_congr_set
  · intros
    simp
    rfl
  · intro b nm
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at nm
    simp only [category.assoc]
    convert comp_zero
    convert comp_zero
    convert comp_zero
    convert comp_zero
    apply o.eq_zero nm
#align category_theory.hom_orthogonal.matrix_decomposition_comp CategoryTheory.HomOrthogonal.matrixDecomposition_comp

section

variable {R : Type _} [Semiring R] [Linear R C]

/-- `hom_orthogonal.matrix_decomposition` as an `R`-linear equivalence. -/
@[simps]
noncomputable def matrixDecompositionLinearEquiv (o : HomOrthogonal s) {α β : Type} [Fintype α]
    [Fintype β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃ₗ[R]
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }
#align category_theory.hom_orthogonal.matrix_decomposition_linear_equiv CategoryTheory.HomOrthogonal.matrixDecompositionLinearEquiv

end

/-!
The hypothesis that `End (s i)` has invariant basis number is automatically satisfied
if `s i` is simple (as then `End (s i)` is a division ring).
-/


variable [∀ i, InvariantBasisNumber (End (s i))]

/-- Given a hom orthogonal family `s : ι → C`
for which each `End (s i)` is a ring with invariant basis number (e.g. if each `s i` is simple),
if two direct sums over `s` are isomorphic, then they have the same multiplicities.
-/
theorem equiv_of_iso (o : HomOrthogonal s) {α β : Type} [Fintype α] [Fintype β] {f : α → ι}
    {g : β → ι} (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : ∃ e : α ≃ β, ∀ a, g (e a) = f a :=
  by
  refine' ⟨Equiv.ofPreimageEquiv _, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  intro c
  apply Nonempty.some
  apply Cardinal.eq.1
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  exact
    Matrix.square_of_invertible (o.matrix_decomposition i.inv c) (o.matrix_decomposition i.hom c)
      (by
        rw [← o.matrix_decomposition_comp]
        simp)
      (by
        rw [← o.matrix_decomposition_comp]
        simp)
#align category_theory.hom_orthogonal.equiv_of_iso CategoryTheory.HomOrthogonal.equiv_of_iso

end

end HomOrthogonal

end CategoryTheory

