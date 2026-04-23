/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Properties of the geometric realization

In this file, we introduce some API in order to study the geometric
realization functor (and its right adjoint the singular simplicial set functor):
* `SimplexCategory.toTopHomeo`: the homeomorphism between the geometric
realization of `Δ[n]` and `stdSimplex ℝ (Fin (n + 1))`;
* `TopCat.toSSetObj₀Equiv : toSSet.obj X _⦋0⦌ ≃ X` for `X : TopCat`;
* `SSet.stdSimplex.toTopObjIsoI : |Δ[1]| ≅ TopCat.I`;
* `SSet.stdSimplex.toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`:
the morphism corresponding to `toTopObjIsoI.hom` by adjunction.

-/

@[expose] public section

universe u

noncomputable instance : TopCat.toSSet.{u}.Monoidal := .ofChosenFiniteProducts _

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SimplexCategory

open SSet

/-- The homeomorphism between the topological realization of a standard simplex
in `SSet` and the corresponding topological standard simplex. -/
noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.{u}.obj n| ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    toTopHomeo m ∘ SSet.toTop.{u}.map (SSet.stdSimplex.map f) =
    stdSimplex.map f ∘ n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (ConcreteCategory.congr_hom ((forget TopCat).congr_map
    (toTopSimplex.hom.naturality f)) x)

lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
      (_root_.stdSimplex.map f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.symm ∘ stdSimplex.map f =
      (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom ∘ n.toTopHomeo.symm := by
  ext x : 1
  exact ConcreteCategory.congr_hom ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    m.toTopHomeo.symm (stdSimplex.map f x) =
      SSet.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

instance : Unique (stdSimplex ℝ (Fin (⦋0⦌.len + 1))) :=
  inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))

noncomputable instance : Unique |(Δ[0] : SSet.{u})| := ⦋0⦌.toTopHomeo.unique

namespace TopCat

/-- Given `X : TopCat`, this is the bijection between `0`-simplices
of the singular simplicial set of `X` and `X`. -/
@[simps! -isSimp apply symm_apply]
noncomputable def toSSetObj₀Equiv {X : TopCat.{u}} :
    toSSet.obj X _⦋0⦌ ≃ X :=
  (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : _)
      invFun x := ⟨fun _ ↦ x, by continuity⟩
      left_inv _ := by
        ext x
        obtain rfl := Subsingleton.elim x default
        rfl
      right_inv _ := rfl }

@[simp]
lemma toSSet_map_const (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y) :
    toSSet.map (TopCat.const (X := X) y) =
      SSet.const (toSSetObj₀Equiv.symm y) :=
  rfl

end TopCat

lemma sSetTopAdj_homEquiv_stdSimplex_zero {X : TopCat.{u}}
    (f : |Δ[0]| ⟶ X) :
    sSetTopAdj.homEquiv Δ[0] X f =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (f default)) := by
  have : sSetTopAdj.unit.app Δ[0] =
      SSet.const (TopCat.toSSetObj₀Equiv.symm default) :=
    SSet.yonedaEquiv.injective (TopCat.toSSetObj₀Equiv.injective (by subsingleton))
  rw [Adjunction.homEquiv_unit, TopCat.toSSetObj₀Equiv_symm_apply, this]
  rfl

/-- The standard topological simplex of dimension `1` is homeomorphic to `TopCat.I`. -/
def TopCat.stdSimplexHomeomorphI :
    _root_.stdSimplex ℝ (Fin 2) ≃ₜ TopCat.I.{u} :=
  stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm

namespace SSet.stdSimplex

/-- The geometric realization of `Δ[1]` is isomorphic to `TopCat.I`. -/
noncomputable def toTopObjIsoI :
    |(Δ[1] : SSet.{u})| ≅ TopCat.I.{u} :=
  TopCat.isoOfHomeo ((SimplexCategory.toTopHomeo _).trans TopCat.stdSimplexHomeomorphI)

/-- The canonical morphism `Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`: by adjunction,
it corresponds to the isomorphism `toTopObjIsoI : |Δ[1]| ≅ TopCat.I`. -/
noncomputable def toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u} :=
  sSetTopAdj.homEquiv _ _ toTopObjIsoI.hom

@[simp]
lemma δ_one_toSSetObjI :
    stdSimplex.δ 1 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 0) := by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left, sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 1)).hom) default)) = 0 := by
    rw [← stdSimplexHomeomorphUnitInterval_zero]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0), stdSimplex.map_vertex]
    rfl
  exact congr_arg ULift.up.{u} this

@[simp]
lemma δ_zero_toSSetObjI :
    dsimp% stdSimplex.δ 0 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 1) := by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left, sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 0)).hom) default)) = 1 := by
    rw [← stdSimplexHomeomorphUnitInterval_one]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0), stdSimplex.map_vertex]
    rfl
  exact congr_arg ULift.up.{u} this

@[simp]
lemma toSSetObj_app_const_zero :
    toSSetObjI.app (op ⦋0⦌) (const _ 0 _) = TopCat.toSSetObj₀Equiv.symm 0 := by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 1 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_one_eq_const]
  · simp

@[simp]
lemma toSSetObj_app_const_one :
    toSSetObjI.app (op ⦋0⦌) (const _ 1 _) = TopCat.toSSetObj₀Equiv.symm 1 := by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 0 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_zero_eq_const]
  · simp

open Functor.Monoidal in
@[reassoc (attr := simp)]
lemma ι₀_whiskerLeft_toSSetObjI_μ (X : TopCat.{u}) :
    SSet.ι₀ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₀ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

open Functor.Monoidal in
@[reassoc (attr := simp)]
lemma ι₁_whiskerLeft_toSSetObjI_μ (X : TopCat.{u}) :
    SSet.ι₁ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₁ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

end SSet.stdSimplex
