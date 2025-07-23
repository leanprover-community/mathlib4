/-
Copyright (c) 2025 Emily Riehl and Dominic Verity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dominic Verity
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Functor
/-!

# The homotopy category functor preserves finite products.

The functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is the left adjoint of a reflective subcategory
inclusion, whose right adjoint is the fully faithful `nerveFunctor : Cat ⥤ SSet`;
see `nerveAdjunction : hoFunctor ⊣ nerveFunctor`.

Both `Cat.{u, u}` and `SSet.{u}` are cartesian closed categories. This files proves that
`hoFunctor` preserves finite cartesian products; note it fails to preserve infinite products.

-/

section

open CategoryTheory Functor Limits

variable {C D J : Type*} [Category C] [Category D] [Category J]
variable (K : J ⥤ C) (L L' : C ⥤ D) (α : L ⟶ L') [IsIso (whiskerLeft K α)]
variable (c : Cocone K) (hc : IsColimit c) [PreservesColimit K L] [PreservesColimit K L']

include hc in
lemma foo : IsIso (α.app c.pt) := by
  obtain ⟨hc₁⟩ := PreservesColimit.preserves (F := L) hc
  obtain ⟨hc₂⟩ := PreservesColimit.preserves (F := L') hc
  let e := IsColimit.coconePointsIsoOfNatIso hc₁ hc₂ (asIso (whiskerLeft K α))
  convert inferInstanceAs (IsIso e.hom)
  apply hc₁.hom_ext fun j ↦ ?_
  simp only [Functor.comp_obj, Functor.mapCocone_pt, Functor.const_obj_obj, Functor.mapCocone_ι_app,
    NatTrans.naturality, IsColimit.coconePointsIsoOfNatIso_hom, asIso_hom, e]
  refine ((hc₁.ι_map (L'.mapCocone c) (whiskerLeft K α) j).trans ?_).symm
  simp

end

-- Where do these belong?
-- BM: `Mathlib.CategoryTheory.Category.Preorder`
namespace OrderHom

open CategoryTheory Functor SSet

-- BM: golfed this, at the cost of being a bit less explicit
def toFunctor {X Y} [Preorder X] [Preorder Y] (f : X →o Y) : X ⥤ Y := f.monotone.functor

def ofFunctor {X Y} [Preorder X] [Preorder Y] (F : X ⥤ Y) : (X →o Y) where
  toFun := F.obj
  monotone' := monotone F

def isoFunctor {X Y} [Preorder X] [Preorder Y] : (X →o Y) ≅ (X ⥤ Y) where
  hom := toFunctor
  inv := ofFunctor

end OrderHom

namespace CategoryTheory

universe u v

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve

def SimplexCategory.homEquivOrderHom {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) →o Fin (b.len + 1)) where
  toFun := Hom.toOrderHom
  invFun := Hom.mk
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

def OrderHom.uliftMapIso {α β : Type*} [Preorder α] [Preorder β] :
    (ULift α →o ULift β) ≃ (α →o β) where
  toFun f := ⟨fun x ↦ (f ⟨x⟩).down, fun _ _ h ↦ f.monotone (by simpa)⟩
  invFun := OrderHom.uliftMap
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

-- set_option pp.universes true

-- def SimplexCategory.homIsoOrderHomULift {a b : SimplexCategory} :
--     (a ⟶ b) ≅ (ULift.{u} (Fin (a.len + 1)) →o ULift (Fin (b.len + 1))) where
--   hom := _
--   inv := _


-- what's the policy on defining short-but-convenient compositions?
def SimplexCategory.homIsoFunctor {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ Fin (b.len + 1)) :=
  Equiv.trans SimplexCategory.homEquivOrderHom OrderHom.isoFunctor.toEquiv

def SimplexCategory.homIsoFunctor' {a b : SimplexCategory} :
    (a ⟶ b) ≃ (Fin (a.len + 1) ⥤ ULiftFin (b.len + 1)) :=
  Equiv.trans SimplexCategory.homIsoFunctor sorry

/-- Nerves of finite non-empty ordinals are representable functors. -/
def nerve.RepresentableBySimplex (n : ℕ) : (nerve (Fin (n + 1))).RepresentableBy ⦋n⦌ where
  homEquiv := SimplexCategory.homIsoFunctor
  homEquiv_comp {_ _} _ _ := rfl

-- /-- The Yoneda embedding from the `SimplexCategory` into simplicial sets is naturally
-- isomorphic to `SimplexCategory.toCat ⋙ nerveFunctor` with component isomorphisms
-- `Δ[n] ≅ nerve (Fin (n + 1))`. -/
-- -- def simplexIsNerve (n : ℕ) : Δ[n] ≅ nerve (Fin (n + 1)) := NatIso.ofComponents <| fun n ↦
-- --     Equiv.toIso stdSimplex.objEquiv ≪≫ SimplexCategory.homIsoFunctor

-- -- Alternate definition:
-- -- `:= SSet.stdSimplex.isoOfRepresentableBy <| nerve.RepresentableBySimplex n`
-- -- Though slightly shorter, this would essentially have us convert to an equiv then back to an iso.

-- set_option pp.universes true

def simplexIsNerve' (n : ℕ) : Δ[n] ≅ nerve (ULiftFin.{u} (n + 1)) :=
  NatIso.ofComponents
    (fun i ↦ Equiv.toIso (stdSimplex.objEquiv.trans SimplexCategory.homIsoFunctor'))
    sorry

/-- Via the whiskered counit (or unit) of `nerveAdjunction`, the triple composite
`nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor` is naturally isomorphic to `nerveFunctor`.
As `nerveFunctor` is a right adjoint, this functor preserves binary products.
Note Mathlib does not seem to recognize that `Cat.{v, u}` has binary products. -/
instance nerveHoNerve.binaryProductIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  sorry

-- This proof can probably be golfed.
instance hoFunctor.binaryProductNerveIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) := by
      have eq := prodComparison_comp
        nerveFunctor (hoFunctor ⋙ nerveFunctor) (A := Cat.of C) (B := Cat.of D)
      exact IsIso.of_isIso_fac_left eq.symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  apply isIso_of_fully_faithful nerveFunctor

/-- By `simplexIsNerve` this is isomorphic to a map of the form
`hoFunctor.binaryProductNerveIsIso`. -/
instance hoFunctor.binarySimplexProductIsIso (n m : ℕ) :
    IsIso (prodComparison hoFunctor Δ[n] Δ[m]) :=
  IsIso.of_isIso_fac_right
    (prodComparison_natural hoFunctor (simplexIsNerve' n).hom (simplexIsNerve' m).hom).symm

noncomputable
def CartesianMonoidalCategory.tensorLeftIsoProd
    {C : Type*} [Category C] [CartesianMonoidalCategory C] (X : C) :
    MonoidalCategory.tensorLeft X ≅ prod.functor.obj X :=
  NatIso.ofComponents fun Y ↦
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit _)

/-- Modulo composing with a symmetry on both ends, the natural transformation
`prodComparisonNatTrans hofunctor Δ[m]` is a natural transformation between cocontinuous
functors whose component at `X : SSet` is `prodComparison hoFunctor X Δ[m]`. This makes use
of cartesian closure of both `SSet.{u}` and `Cat.{u,u}` to establish cocontinuity of the
product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) X` this reduces to
the result proven in `hoFunctor.binarySimplexProductIsIso`.
-/
lemma hoFunctor.binaryProductWithSimplexIsIso (D X : SSet.{u})
    (H : ∀ m, IsIso (prodComparison hoFunctor D Δ[m])) :
    IsIso (prodComparison hoFunctor D X) := by
  letI Xcolim := CategoryTheory.Presheaf.colimitOfRepresentable X
  have : (prod.functor.obj D).IsLeftAdjoint := by
    have := (CategoryTheory.FunctorToTypes.adj D).isLeftAdjoint
    exact Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd _)
  have : (prod.functor.obj (hoFunctor.obj (D : SSet.{u}))).IsLeftAdjoint := by infer_instance
  have : (hoFunctor).IsLeftAdjoint := nerveAdjunction.isLeftAdjoint
  have : IsIso (whiskerLeft (CategoryTheory2.Presheaf.functorToRepresentables X)
      (prodComparisonNatTrans hoFunctor D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro x
    dsimp
    exact H (unop (unop x).fst).len
  exact foo
    (J := (Elements X)ᵒᵖ)
    (C := SSet.{u})
    (D := Cat.{u, u})
    (CategoryTheory2.Presheaf.functorToRepresentables X)
    (prod.functor.obj D ⋙ hoFunctor) (hoFunctor ⋙ prod.functor.obj (hoFunctor.obj D))
    (prodComparisonNatTrans ..) _ Xcolim

/-- The natural transformation `prodComparisonNatTrans hofunctor X` is a natural
transformation between cocontinuous functors whose component at `Y : SSet` is
`prodComparison hoFunctor X Y`. This makes use of cartesian closure of both `SSet.{u}`
and `Cat.{u,u}` to establish cocontinuity of the product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) Y` this reduces to
the result proven in `hoFunctor.binaryProductWithSimplexIsIso`.
-/
instance hoFunctor.binaryProductIsIso (X Y : SSet):
    IsIso (prodComparison hoFunctor X Y) := by
  apply hoFunctor.binaryProductWithSimplexIsIso
  intro m
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  apply hoFunctor.binaryProductWithSimplexIsIso
  exact fun _ ↦ hoFunctor.binarySimplexProductIsIso _ _

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of simplicial sets
`X` and `Y`. -/
instance hoFunctor.preservesBinaryProducts (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of functors
out of `Discrete Limits.WalkingPair`. -/
instance hoFunctor.preservesBinaryProducts' :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) hoFunctor where
  preservesLimit :=
    fun {F} ↦ preservesLimit_of_iso_diagram hoFunctor (id (diagramIsoPair F).symm)

instance hoFunctor.preservesFiniteProducts : PreservesFiniteProducts hoFunctor :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- A product preserving functor between cartesian closed categories is lax monoidal. -/
noncomputable instance hoFunctor.laxMonoidal : LaxMonoidal hoFunctor :=
  (Monoidal.ofChosenFiniteProducts hoFunctor).toLaxMonoidal


end CategoryTheory
