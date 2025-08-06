/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.Basic

/-!
## Moore complex

We construct the normalized Moore complex, as a functor
`SimplicialObject C ⥤ ChainComplex C ℕ`,
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

open scoped Simplicial

namespace AlgebraicTopology

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] Abelian.hasPullbacks

/-! The definitions in this namespace are all auxiliary definitions for `NormalizedMooreComplex`
and should usually only be accessed via that. -/


namespace NormalizedMooreComplex

open CategoryTheory.Subobject

variable (X : SimplicialObject C)

/-- The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
def objX : ∀ n : ℕ, Subobject (X.obj (op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)

@[simp] theorem objX_zero : objX X 0 = ⊤ :=
  rfl

@[simp] theorem objX_add_one (n) :
    objX X (n + 1) = Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ) :=
  rfl

/-- The differentials in the normalized Moore complex.
-/
@[simp]
def objD : ∀ n : ℕ, (objX X (n + 1) : C) ⟶ (objX X n : C)
  | 0 => Subobject.arrow _ ≫ X.δ (0 : Fin 2) ≫ inv (⊤ : Subobject _).arrow
  | n + 1 => by
    -- The differential is `Subobject.arrow _ ≫ X.δ (0 : Fin (n+3))`,
    -- factored through the intersection of the kernels.
    refine factorThru _ (arrow _ ≫ X.δ (0 : Fin (n + 3))) ?_
    -- We now need to show that it factors!
    -- A morphism factors through an intersection of subobjects if it factors through each.
    refine (finset_inf_factors _).mpr fun i _ => ?_
    -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
    apply kernelSubobject_factors
    dsimp [objX]
    -- Use a simplicial identity
    rw [Category.assoc, ← Fin.castSucc_zero, ← X.δ_comp_δ (Fin.zero_le i.succ)]
    -- We can rewrite the arrow out of the intersection of all the kernels as a composition
    -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
    rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i.succ (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  -- It's a pity we need to do a case split here;
    -- after the first rw the proofs are almost identical
  rcases n with _ | n <;> dsimp [objD]
  · rw [Subobject.factorThru_arrow_assoc, Category.assoc, ← Fin.castSucc_zero,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin 2) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
  · rw [factorThru_right, factorThru_eq_zero, factorThru_arrow_assoc, Category.assoc,
      ← Fin.castSucc_zero,
      ← X.δ_comp_δ (Fin.zero_le (0 : Fin (n + 3))),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin (n + 3)) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

/-- The normalized Moore complex functor, on objects.
-/
@[simps!]
def obj (X : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD X) (d_squared X)

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

/-- The normalized Moore complex functor, on morphisms.
-/
@[simps!]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => factorThru _ (arrow _ ≫ f.app (op ⦋n⦌)) (by
      cases n <;> dsimp
      · apply top_factors
      · refine (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
        rw [Category.assoc, SimplicialObject.δ, ← f.naturality,
          ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i (by simp)),
          Category.assoc]
        erw [kernelSubobject_arrow_comp_assoc]
        rw [zero_comp, comp_zero]))
    fun n => by
    cases n <;> dsimp [objD, objX] <;> cat_disch

end NormalizedMooreComplex

open NormalizedMooreComplex

variable (C) in
/-- The (normalized) Moore complex of a simplicial object `X` in an abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
@[simps]
def normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := obj
  map f := map f

-- Porting note: removed @[simp] as it is not in normal form
theorem normalizedMooreComplex_objD (X : SimplicialObject C) (n : ℕ) :
    ((normalizedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n :=
  ChainComplex.of_d _ _ (d_squared X) n

end AlgebraicTopology
