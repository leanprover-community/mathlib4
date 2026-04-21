/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Data.Set.Subsingleton

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
theorem HomOrthogonal.equiv_of_iso (o : HomOrthogonal s) {f : α → ι} {g : β → ι}
    (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Matrix CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A family of objects is "hom orthogonal" if
there is at most one morphism between distinct objects.

(In a category with zero morphisms, that must be the zero morphism.) -/
def HomOrthogonal {ι : Type*} (s : ι → C) : Prop :=
  Pairwise fun i j => Subsingleton (s i ⟶ s j)

namespace HomOrthogonal

variable {ι : Type*} {s : ι → C}

theorem eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) :
    f = 0 :=
  (o w).elim _ _

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

open scoped Classical in
/-- Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`. -/
@[simps]
noncomputable def matrixDecomposition (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β]
    {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) where
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
    ext j k
    simp only [biproduct.matrix_π, biproduct.ι_desc]
    split_ifs with h
    · simp
      rfl
    · symm
      apply o.eq_zero h
  right_inv z := by
    ext i ⟨j, w⟩ ⟨k, ⟨⟩⟩
    simp only [eqToHom_refl, biproduct.matrix_components, Category.id_comp]
    split_ifs with h
    · simp
    · exfalso
      exact h w.symm

end

section

variable [Preadditive C] [HasFiniteBiproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- `HomOrthogonal.matrixDecomposition` as an additive equivalence. -/
@[simps!]
noncomputable def matrixDecompositionAddEquiv (o : HomOrthogonal s) {α β : Type} [Finite α]
    [Finite β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃+
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
@[simp]
theorem matrixDecomposition_id (o : HomOrthogonal s) {α : Type} [Finite α] {f : α → ι} (i : ι) :
    o.matrixDecomposition (𝟙 (⨁ fun a => s (f a))) i = 1 := by
  ext ⟨b, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Category.comp_id, Category.id_comp, End.one_def, eqToHom_refl,
    Matrix.one_apply, HomOrthogonal.matrixDecomposition_apply, biproduct.components]
  split_ifs with h
  · cases h
    simp
  · simp only [Subtype.mk.injEq] at h
    convert comp_zero
    simpa using biproduct.ι_π_ne _ (Ne.symm h)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
theorem matrixDecomposition_comp (o : HomOrthogonal s) {α β γ : Type} [Finite α] [Fintype β]
    [Finite γ] {f : α → ι} {g : β → ι} {h : γ → ι} (z : (⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b))
    (w : (⨁ fun b => s (g b)) ⟶ ⨁ fun c => s (h c)) (i : ι) :
    o.matrixDecomposition (z ≫ w) i = o.matrixDecomposition w i * o.matrixDecomposition z i := by
  ext ⟨c, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Matrix.mul_apply, Limits.biproduct.components,
    HomOrthogonal.matrixDecomposition_apply, Category.comp_id, Category.id_comp, Category.assoc,
    End.mul_def, eqToHom_refl, eqToHom_trans_assoc]
  conv_lhs => rw [← Category.id_comp w, ← biproduct.total]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr_set
  · simp
  · intro b nm
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at nm
    simp only [Category.assoc]
    convert comp_zero
    convert comp_zero
    convert comp_zero
    convert comp_zero
    simp only [o.eq_zero nm]

section

variable {R : Type*} [Semiring R] [Linear R C]

set_option backward.isDefEq.respectTransparency false in
/-- `HomOrthogonal.MatrixDecomposition` as an `R`-linear equivalence. -/
@[simps]
noncomputable def matrixDecompositionLinearEquiv (o : HomOrthogonal s) {α β : Type} [Finite α]
    [Finite β] {f : α → ι} {g : β → ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃ₗ[R]
      ∀ i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

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
theorem equiv_of_iso (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β] {f : α → ι}
    {g : β → ι} (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  refine ⟨Equiv.ofPreimageEquiv ?_, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  intro c
  apply Nonempty.some
  apply Cardinal.eq.1
  cases nonempty_fintype α; cases nonempty_fintype β
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  exact
    Matrix.square_of_invertible (o.matrixDecomposition i.inv c) (o.matrixDecomposition i.hom c)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)

end

end HomOrthogonal

end CategoryTheory
