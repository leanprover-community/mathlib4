/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Relative cell complexes

In this file, we define a structure `RelativeCellComplex` which expresses
that a morphism `f : X ⟶ Y` is a transfinite composition of morphisms,
all of which consist in attaching cells. Here, we allow a different
family of authorized cells at each step. For example, (relative)
CW-complexes are defined in the file `Mathlib/Topology/CWComplex/Abstract/Basic.lean`
by requiring that at the `n`th step, we attach `n`-disks along their
boundaries.

This structure `RelativeCellComplex` is also used in the
formalization of the small object argument,
see the file `Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean`.

## References
* https://ncatlab.org/nlab/show/small+object+argument

-/

universe w w' t v u

open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C}
  (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i) {X Y : C} (f : X ⟶ Y)

/-- Let `J` be a well-ordered type. Assume that for each `j : J`, we
have a family `basicCell j` of morphisms. A relative cell complex
is a morphism `f : X ⟶ Y` which is a transfinite composition of morphisms
in such a way that at the step `j : J`, we attach cells in the family `basicCell j`. -/
structure RelativeCellComplex
    extends TransfiniteCompositionOfShape J f where
  /-- If `j` is not the maximum element, `F.obj (Order.succ j)` is obtained
  from `F.obj j` by attaching cells in the family of morphisms `basicCell j`. -/
  attachCells (j : J) (hj : ¬ IsMax j) :
    AttachCells.{w} (basicCell j) (F.map (homOfLE (Order.le_succ j)))

namespace RelativeCellComplex

variable {basicCell f} (c : RelativeCellComplex basicCell f)

/-- The index type of cells in a relative cell complex. -/
structure Cells where
  /-- the step where the cell is added -/
  j : J
  hj : ¬ IsMax j
  /-- the index of the cell -/
  k : (c.attachCells j hj).ι

variable {c} in
/-- Given a cell `γ` in a relative cell complex, this is the corresponding
index in the family of morphisms `basicCell γ.j`. -/
def Cells.i (γ : Cells c) : α γ.j := (c.attachCells γ.j γ.hj).π γ.k

variable {c} in
/-- The inclusion of a cell. -/
def Cells.ι (γ : Cells c) : B γ.j γ.i ⟶ Y :=
  (c.attachCells γ.j γ.hj).cell γ.k ≫ c.incl.app (Order.succ γ.j)

lemma hom_ext {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂)
    (h : ∀ (γ : Cells c), γ.ι ≫ φ₁ = γ.ι ≫ φ₂) :
    φ₁ = φ₂ := by
  refine c.isColimit.hom_ext (fun j ↦ ?_)
  dsimp
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa [← cancel_epi c.isoBot.inv] using h₀
  | succ j hj hj' =>
    apply (c.attachCells j hj).hom_ext
    · simpa using hj'
    · intro i
      simpa only [Category.assoc, Cells.ι] using h ({ hj := hj, k := i, .. })
  | isSuccLimit j hj hj' =>
    exact (c.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
      (fun ⟨k, hk⟩ ↦ by simpa using hj' k hk)

open MorphismProperty in
/-- If `f` is a relative cell complex with respect to a constant
family of morphisms `g`, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in the family `g`. -/
@[simps toTransfiniteCompositionOfShape]
def transfiniteCompositionOfShape
    {α : Type*} {A B : α → C} (g : (i : α) → (A i ⟶ B i))
    (c : RelativeCellComplex.{w} (fun (_ : J) ↦ g) f) :
    (coproducts.{w} (ofHoms g)).pushouts.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
  map_mem j hj := (c.attachCells j hj).pushouts_coproducts

end RelativeCellComplex

end HomotopicalAlgebra
