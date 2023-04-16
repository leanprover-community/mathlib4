/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_topology.Moore_complex
! leanprover-community/mathlib commit 0bd2ea37bcba5769e14866170f251c9bc64e35d7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.AlgebraicTopology.SimplicialObject
import Mathbin.CategoryTheory.Abelian.Basic

/-!
## Moore complex

We construct the normalized Moore complex, as a functor
`simplicial_object C ⥤ chain_complex C ℕ`,
for any abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.

This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### References

* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex
-/


universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open Opposite

namespace AlgebraicTopology

variable {C : Type _} [Category C] [Abelian C]

attribute [local instance] abelian.has_pullbacks

/-! The definitions in this namespace are all auxiliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/


namespace NormalizedMooreComplex

open CategoryTheory.Subobject

variable (X : SimplicialObject C)

/-- The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
@[simp]
def objX : ∀ n : ℕ, Subobject (X.obj (op (SimplexCategory.mk n)))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)
#align algebraic_topology.normalized_Moore_complex.obj_X AlgebraicTopology.NormalizedMooreComplex.objX

/-- The differentials in the normalized Moore complex.
-/
@[simp]
def objD : ∀ n : ℕ, (objX X (n + 1) : C) ⟶ (objX X n : C)
  | 0 => Subobject.arrow _ ≫ X.δ (0 : Fin 2) ≫ inv (⊤ : Subobject _).arrow
  | n + 1 =>
    by
    -- The differential is `subobject.arrow _ ≫ X.δ (0 : fin (n+3))`,
    -- factored through the intersection of the kernels.
    refine' factor_thru _ (arrow _ ≫ X.δ (0 : Fin (n + 3))) _
    -- We now need to show that it factors!
    -- A morphism factors through an intersection of subobjects if it factors through each.
    refine' (finset_inf_factors _).mpr fun i m => _
    -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
    apply kernel_subobject_factors
    -- Use a simplicial identity
    dsimp [obj_X]
    erw [category.assoc, ← X.δ_comp_δ (Fin.zero_le i.succ), ← category.assoc]
    -- It's the first two factors which are zero.
    convert zero_comp
    -- We can rewrite the arrow out of the intersection of all the kernels as a composition
    -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
    rw [← factor_thru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i.succ (by simp))]
    -- It's the second two factors which are zero.
    rw [category.assoc]
    convert comp_zero
    exact kernel_subobject_arrow_comp _
#align algebraic_topology.normalized_Moore_complex.obj_d AlgebraicTopology.NormalizedMooreComplex.objD

theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 :=
  by
  -- It's a pity we need to do a case split here;
    -- after the first simp the proofs are almost identical
    cases n <;>
    dsimp
  · simp only [subobject.factor_thru_arrow_assoc]
    slice_lhs 2 3 => erw [← X.δ_comp_δ (Fin.zero_le (0 : Fin (0 + 2)))]
    rw [← factor_thru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin 2) (by simp))]
    slice_lhs 2 3 => rw [kernel_subobject_arrow_comp]
    simp
  · simp [factor_thru_right]
    slice_lhs 2 3 => erw [← X.δ_comp_δ (Fin.zero_le (0 : Fin (n.succ + 2)))]
    rw [←
      factor_thru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin (n + 3)) (by simp))]
    slice_lhs 2 3 => rw [kernel_subobject_arrow_comp]
    simp
#align algebraic_topology.normalized_Moore_complex.d_squared AlgebraicTopology.NormalizedMooreComplex.d_squared

/-- The normalized Moore complex functor, on objects.
-/
@[simps]
def obj (X : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD
      X)
    (d_squared X)
#align algebraic_topology.normalized_Moore_complex.obj AlgebraicTopology.NormalizedMooreComplex.obj

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

/-- The normalized Moore complex functor, on morphisms.
-/
@[simps]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => by
      refine' factor_thru _ (arrow _ ≫ f.app (op (SimplexCategory.mk n))) _
      cases n <;> dsimp
      · apply top_factors
      · refine' (finset_inf_factors _).mpr fun i m => _
        apply kernel_subobject_factors
        slice_lhs 2 3 => erw [← f.naturality]
        rw [← factor_thru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i (by simp))]
        slice_lhs 2 3 => erw [kernel_subobject_arrow_comp]
        simp)
    fun n => by
    cases n <;> dsimp
    · ext
      simp
    · ext
      simp
#align algebraic_topology.normalized_Moore_complex.map AlgebraicTopology.NormalizedMooreComplex.map

end NormalizedMooreComplex

open NormalizedMooreComplex

variable (C)

/-- The (normalized) Moore complex of a simplicial object `X` in an abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
@[simps]
def normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C ℕ
    where
  obj := obj
  map X Y f := map f
  map_id' X := by
    ext n
    cases n <;>
      · dsimp
        simp
  map_comp' X Y Z f g := by
    ext n
    cases n <;> simp
#align algebraic_topology.normalized_Moore_complex AlgebraicTopology.normalizedMooreComplex

variable {C}

@[simp]
theorem normalizedMooreComplex_objD (X : SimplicialObject C) (n : ℕ) :
    ((normalizedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n := by
  apply ChainComplex.of_d
#align algebraic_topology.normalized_Moore_complex_obj_d AlgebraicTopology.normalizedMooreComplex_objD

end AlgebraicTopology

