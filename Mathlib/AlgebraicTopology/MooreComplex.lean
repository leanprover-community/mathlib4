/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Abelian.Basic

#align_import algebraic_topology.Moore_complex from "leanprover-community/mathlib"@"0bd2ea37bcba5769e14866170f251c9bc64e35d7"

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
def objX : ∀ n : ℕ, Subobject (X.obj (op (SimplexCategory.mk n)))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)
set_option linter.uppercaseLean3 false in
#align algebraic_topology.normalized_Moore_complex.obj_X AlgebraicTopology.NormalizedMooreComplex.objX

theorem objX_zero : objX X 0 = ⊤ :=
  rfl

theorem objX_add_one (n) :
    objX X (n + 1) = Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ) :=
  rfl

attribute [eqns objX_zero objX_add_one] objX
attribute [simp] objX

/-- The differentials in the normalized Moore complex.
-/
@[simp]
def objD : ∀ n : ℕ, (objX X (n + 1) : C) ⟶ (objX X n : C)
  | 0 => Subobject.arrow _ ≫ X.δ (0 : Fin 2) ≫ inv (⊤ : Subobject _).arrow
  | n + 1 => by
    -- The differential is `Subobject.arrow _ ≫ X.δ (0 : Fin (n+3))`,
    -- factored through the intersection of the kernels.
    refine' factorThru _ (arrow _ ≫ X.δ (0 : Fin (n + 3))) _
    -- ⊢ Factors (objX X (n + 1)) (arrow (objX X (n + 1 + 1)) ≫ SimplicialObject.δ X 0)
    -- We now need to show that it factors!
    -- A morphism factors through an intersection of subobjects if it factors through each.
    refine' (finset_inf_factors _).mpr fun i _ => _
    -- ⊢ Factors (kernelSubobject (SimplicialObject.δ X (Fin.succ i))) (arrow (objX X …
    -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
    apply kernelSubobject_factors
    -- ⊢ (arrow (objX X (n + 1 + 1)) ≫ SimplicialObject.δ X 0) ≫ SimplicialObject.δ X …
    dsimp [objX]
    -- ⊢ (arrow (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObject.δ  …
    -- Use a simplicial identity
    erw [Category.assoc, ← X.δ_comp_δ (Fin.zero_le i.succ)]
    -- ⊢ arrow (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObject.δ X …
    -- We can rewrite the arrow out of the intersection of all the kernels as a composition
    -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
    rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i.succ (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.normalized_Moore_complex.obj_d AlgebraicTopology.NormalizedMooreComplex.objD

theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  -- It's a pity we need to do a case split here;
    -- after the first erw the proofs are almost identical
  rcases n with _ | n <;> dsimp [objD]
  -- ⊢ objD X (Nat.zero + 1) ≫ objD X Nat.zero = 0
                          -- ⊢ factorThru (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObjec …
                          -- ⊢ factorThru (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObjec …
  · erw [Subobject.factorThru_arrow_assoc, Category.assoc,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin 2) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
  · erw [factorThru_right, factorThru_eq_zero, factorThru_arrow_assoc, Category.assoc,
      ← X.δ_comp_δ (Fin.zero_le (0 : Fin (n + 3))),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin (n + 3)) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.normalized_Moore_complex.d_squared AlgebraicTopology.NormalizedMooreComplex.d_squared

/-- The normalized Moore complex functor, on objects.
-/
@[simps!]
def obj (X : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD X) (d_squared X)
set_option linter.uppercaseLean3 false in
#align algebraic_topology.normalized_Moore_complex.obj AlgebraicTopology.NormalizedMooreComplex.obj

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

/-- The normalized Moore complex functor, on morphisms.
-/
@[simps!]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => factorThru _ (arrow _ ≫ f.app (op (SimplexCategory.mk n))) (by
      cases n <;> dsimp
      -- ⊢ Factors (objX Y Nat.zero) (arrow (objX X Nat.zero) ≫ NatTrans.app f (op (Sim …
                  -- ⊢ Factors ⊤ (arrow ⊤ ≫ NatTrans.app f (op (SimplexCategory.mk 0)))
                  -- ⊢ Factors (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObject.δ …
      · apply top_factors
        -- 🎉 no goals
      · refine' (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ _
        -- ⊢ (arrow (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObject.δ  …
        erw [Category.assoc, ← f.naturality,
          ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i (by simp)),
          Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]))
    fun n => by
    cases n <;> dsimp [objD, objX] <;> aesop_cat
    -- ⊢ (fun n => factorThru (objX Y n) (arrow (objX X n) ≫ NatTrans.app f (op (Simp …
                -- ⊢ factorThru (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObjec …
                -- ⊢ factorThru (Finset.inf Finset.univ fun k => kernelSubobject (SimplicialObjec …
                                       -- 🎉 no goals
                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
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
def normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := obj
  map f := map f
  -- Porting note: Why `aesop_cat` can't do `dsimp` steps?
  map_id X := by ext (_ | _) <;> dsimp <;> aesop_cat
                 -- ⊢ HomologicalComplex.Hom.f ({ obj := obj, map := fun {X Y} f => map f }.map (𝟙 …
                                 -- ⊢ Subobject.factorThru ⊤ (Subobject.arrow ⊤ ≫ 𝟙 (X.obj (op (SimplexCategory.mk …
                                 -- ⊢ Subobject.factorThru (Finset.inf Finset.univ fun k => kernelSubobject (Simpl …
                                           -- 🎉 no goals
                                           -- 🎉 no goals
  map_comp f g := by ext (_ | _) <;> apply Subobject.eq_of_comp_arrow_eq <;> dsimp <;> aesop_cat
                     -- ⊢ HomologicalComplex.Hom.f ({ obj := obj, map := fun {X Y} f => map f }.map (f …
                                     -- ⊢ HomologicalComplex.Hom.f ({ obj := obj, map := fun {X Y} f => map f }.map (f …
                                     -- ⊢ HomologicalComplex.Hom.f ({ obj := obj, map := fun {X Y} f => map f }.map (f …
                                                                             -- ⊢ Subobject.factorThru ⊤ (Subobject.arrow ⊤ ≫ NatTrans.app f (op (SimplexCateg …
                                                                             -- ⊢ Subobject.factorThru (Finset.inf Finset.univ fun k => kernelSubobject (Simpl …
                                                                                       -- 🎉 no goals
                                                                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.normalized_Moore_complex AlgebraicTopology.normalizedMooreComplex

variable {C}

-- porting note: removed @[simp] as it is not in normal form
theorem normalizedMooreComplex_objD (X : SimplicialObject C) (n : ℕ) :
    ((normalizedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n :=
-- porting note: in mathlib, `apply ChainComplex.of_d` was enough
  ChainComplex.of_d _ _ (d_squared X) n
set_option linter.uppercaseLean3 false in
#align algebraic_topology.normalized_Moore_complex_obj_d AlgebraicTopology.normalizedMooreComplex_objD

end AlgebraicTopology
