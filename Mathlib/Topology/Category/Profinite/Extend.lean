/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.CategoryTheory.Filtered.Final
/-!

# Extending cones in `Profinite`

Let `(Sᵢ)_{i : I}` be a family of finite sets indexed by a cofiltered category `I` and let `S` be
its limit in `Profinite`. Let `G` be a functor from `Profinite` to a category `C` and suppose that
`G` preserves the limit described above. Suppose further that the projection maps `S ⟶ Sᵢ` are
epimorphic for all `i`. Then `G.obj S` is isomorphic to a limit indexed by
`StructuredArrow S toProfinite` (see `Profinite.Extend.isLimitCone`).

We also provide the dual result for a functor of the form `G : Profiniteᵒᵖ ⥤ C`.

We apply this to define `Profinite.diagram'`, `Profinite.asLimitCone'`, and `Profinite.asLimit'`,
analogues to their unprimed versions in `Mathlib.Topology.Category.Profinite.AsLimit`, in which the
indexing category is `StructuredArrow S toProfinite` instead of `DiscreteQuotient S`.
-/

universe u w

open CategoryTheory Limits FintypeCat Functor

attribute [local instance] ConcreteCategory.instFunLike

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone <| F ⋙ toProfinite)

/--
A continuous map from a profinite set to a finite set factors through one of the components of
the profinite set when written as a cofiltered limit of finite sets.
-/
lemma exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X) :
    ∃ (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g := by
  let _ : TopologicalSpace X := ⊥
  have : DiscreteTopology (toProfinite.obj X) := ⟨rfl⟩
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.continuous⟩
  obtain ⟨i, g, h⟩ := exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, (g : _ → _), ?_⟩
  ext x
  exact LocallyConstant.congr_fun h x

namespace Extend

/--
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofiltered category,
we obtain a functor from the indexing category to `StructuredArrow c.pt toProfinite`.
-/
@[simps]
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

-- We check that the original diagram factors through `Profinite.Extend.functor`.
example : functor c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

/--
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofiltered category,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
@[simps! obj map]
def functorOp : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩ :=
  (functor c).op ⋙ StructuredArrow.toCostructuredArrow _ _

-- We check that the opposite of the original diagram factors through `Profinite.Extend.functorOp`.
example : functorOp c ⋙ CostructuredArrow.proj toProfinite.op ⟨c.pt⟩ ≅ F.op := Iso.refl _

/--
If the projection maps in the cone are epimorphic and the cone is limiting, then
`Profinite.Extend.functor` is initial.

TODO: investigate how to weaken the assumption `∀ i, Epi (c.π.app i)` to
`∀ i, ∃ j (_ : j ⟶ i), Epi (c.π.app j)`.
-/
lemma functor_initial (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Initial (functor c) := by
  let e : I ≌ ULiftHom.{w} (ULift.{w} I) := ULiftHomULiftCategory.equiv _
  suffices (e.inverse ⋙ functor c).Initial from initial_of_equivalence_comp e.inverse (functor c)
  rw [initial_iff_of_isCofiltered (F := e.inverse ⋙ functor c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    obtain ⟨i, g, h⟩ := exists_hom c hc f
    refine ⟨⟨i⟩, ⟨StructuredArrow.homMk g h.symm⟩⟩
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩ ⟨i⟩ ⟨_, (s : F.obj i ⟶ X), (w : f = c.π.app i ≫ _)⟩
      ⟨_, (s' : F.obj i ⟶ X), (w' : f = c.π.app i ≫ _)⟩
    simp only [functor_obj, functor_map, StructuredArrow.hom_eq_iff, StructuredArrow.mk_right,
      StructuredArrow.comp_right, StructuredArrow.homMk_right]
    refine ⟨⟨i⟩, 𝟙 _, ?_⟩
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [w] at w'
    exact toProfinite.map_injective <| Epi.left_cancellation _ _ w'

/--
If the projection maps in the cone are epimorphic and the cone is limiting, then
`Profinite.Extend.functorOp` is final.
-/
lemma functorOp_final (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Final (functorOp c) := by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toProfinite c.pt)).IsEquivalence  :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence )
  exact Functor.final_comp (functor c).op _

section Limit

variable {C : Type*} [Category C] (G : Profinite ⥤ C)

/--
Given a functor `G` from `Profinite` and `S : Profinite`, we obtain a cone on
`(StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G)` with cone point `G.obj S`.

Whiskering this cone with `Profinite.Extend.functor c` gives `G.mapCone c` as we check in the
example below.
-/
@[simps]
def cone (S : Profinite) :
    Cone (StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G) where
  pt := G.obj S
  π := {
    app := fun i ↦ G.map i.hom
    naturality := fun _ _ f ↦ (by
      have := f.w
      simp only [const_obj_obj, StructuredArrow.left_eq_id, const_obj_map, Category.id_comp,
        StructuredArrow.w] at this
      simp only [const_obj_obj, comp_obj, StructuredArrow.proj_obj, const_obj_map, Category.id_comp,
        Functor.comp_map, StructuredArrow.proj_map, ← map_comp, StructuredArrow.w]) }

example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

/--
If `c` and `G.mapCone c` are limit cones and the projection maps in `c` are epimorphic,
then `cone G c.pt` is a limit cone.
-/
noncomputable
def isLimitCone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsLimit <| G.mapCone c) :
    IsLimit (cone G c.pt) := (functor_initial c hc).isLimitWhiskerEquiv _ hc'

end Limit

section Colimit

variable {C : Type*} [Category C] (G : Profiniteᵒᵖ ⥤ C)

/--
Given a functor `G` from `Profiniteᵒᵖ` and `S : Profinite`, we obtain a cocone on
`(CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G)` with cocone point `G.obj ⟨S⟩`.

Whiskering this cocone with `Profinite.Extend.functorOp c` gives `G.mapCocone c.op` as we check in
the example below.
-/
@[simps]
def cocone (S : Profinite) :
    Cocone (CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G) where
  pt := G.obj ⟨S⟩
  ι := {
    app := fun i ↦ G.map i.hom
    naturality := fun _ _ f ↦ (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp only [comp_obj, CostructuredArrow.proj_obj, op_obj, const_obj_obj, Functor.comp_map,
        CostructuredArrow.proj_map, op_map, ← map_comp, this, const_obj_map, Category.comp_id]) }

example : G.mapCocone c.op = (cocone G c.pt).whisker (functorOp c) := rfl

/--
If `c` is a limit cone, `G.mapCocone c.op` is a colimit cone and the projection maps in `c`
are epimorphic, then `cocone G c.pt` is a colimit cone.
-/
noncomputable
def isColimitCocone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op) :
    IsColimit (cocone G c.pt) := (functorOp_final c hc).isColimitWhiskerEquiv _ hc'

end Colimit

end Extend

open Extend

section ProfiniteAsLimit

variable (S : Profinite.{u})

/--
A functor `StructuredArrow S toProfinite ⥤ FintypeCat` whose limit in `Profinite` is isomorphic
to `S`.
-/
abbrev fintypeDiagram' : StructuredArrow S toProfinite ⥤ FintypeCat :=
  StructuredArrow.proj S toProfinite

/-- An abbreviation for `S.fintypeDiagram' ⋙ toProfinite`. -/
abbrev diagram' : StructuredArrow S toProfinite ⥤ Profinite :=
  S.fintypeDiagram' ⋙ toProfinite

/-- A cone over `S.diagram'` whose cone point is `S`. -/
abbrev asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S

instance (i : DiscreteQuotient S) : Epi (S.asLimitCone.π.app i) :=
  (epi_iff_surjective _).mpr i.proj_surjective

/-- `S.asLimitCone'` is a limit cone. -/
noncomputable def asLimit' : IsLimit S.asLimitCone' := isLimitCone _ (𝟭 _) S.asLimit S.asLimit

/-- A bundled version of `S.asLimitCone'` and `S.asLimit'`. -/
noncomputable def lim' : LimitCone S.diagram' := ⟨S.asLimitCone', S.asLimit'⟩

end ProfiniteAsLimit

end Profinite
