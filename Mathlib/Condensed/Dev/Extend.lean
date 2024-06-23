/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Filtered.Final
/-!

# Extending a functor from `FintypeCat` to `Profinite`
-/

universe u

open CategoryTheory Limits FintypeCat Functor

attribute [local instance] FintypeCat.discreteTopology ConcreteCategory.instFunLike

namespace CompHausLike

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}

variable {P : TopCat.{u} → Prop} [∀ (Y : TopCat) [Fintype Y], HasProp P Y]

instance (A : FintypeCat.{u}) :
    letI _ : TopologicalSpace A := ⊥
    HasProp P (TopCat.of A) :=
  letI _ : TopologicalSpace A := ⊥
  letI _ : Fintype (TopCat.of A) := inferInstanceAs (Fintype A)
  inferInstance

-- def _root_.FintypeCat.toCompHausLike : FintypeCat ⥤ CompHausLike P where
--   obj A :=
--     let _ : TopologicalSpace A := ⊥
--     have : HasProp P A := inferInstanceAs (HasProp P (TopCat.of A))
--     CompHausLike.of P A
--   map f := ⟨f, by continuity⟩

end CompHausLike

namespace Profinite

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
    (c : Cone <| F ⋙ toProfinite)

/--
A continuous map from a profinite set to a finite set factors through one of the components of
the profinite set when written as a cofiltered limit of finite sets.
-/
lemma exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X) :
    ∃ (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g := by
  let _ : TopologicalSpace X := ⊥
  have : DiscreteTopology (toProfinite.obj X) :=
    inferInstanceAs (DiscreteTopology X)
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.continuous⟩
  obtain ⟨i, g, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, g.toFun, ?_⟩
  ext x
  exact LocallyConstant.congr_fun h x

namespace Extend

@[simps]
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

def functorOp : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩ :=
  (functor c).op ⋙ StructuredArrow.toCostructuredArrow _ _

example : functor c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

example : functorOp c ⋙ CostructuredArrow.proj toProfinite.op ⟨c.pt⟩ ≅ F.op := Iso.refl _

theorem functor_initial (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Initial (functor c) := by
  rw [initial_iff_of_isCofiltered (F := functor c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    obtain ⟨i, g, h⟩ := Profinite.exists_hom c hc f
    refine ⟨i, ⟨StructuredArrow.homMk g h.symm⟩⟩
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩ i ⟨_, (s : F.obj i ⟶ X), (w : f = c.π.app i ≫ _)⟩
      ⟨_, (s' : F.obj i ⟶ X), (w' : f = c.π.app i ≫ _)⟩
    simp only [functor_obj, functor_map, StructuredArrow.hom_eq_iff, StructuredArrow.mk_right,
      StructuredArrow.comp_right, StructuredArrow.homMk_right]
    refine ⟨i, 𝟙 _, ?_⟩
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [w] at w'
    exact toProfinite.map_injective <| Epi.left_cancellation _ _ w'

theorem functorOp_final (hc : IsLimit c) [∀ i, Epi (c.π.app i)] : Final (functorOp c) := by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toProfinite c.pt)).IsEquivalence  :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence )
  exact Functor.final_comp (functor c).op _

section Limit

variable {C : Type*} [Category C] (G : Profinite ⥤ C)

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

noncomputable
def isLimitCone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsLimit <| G.mapCone c) :
    IsLimit (cone G c.pt) := (functor_initial c hc).isLimitWhiskerEquiv _ hc'

end Limit

section Colimit

variable {C : Type*} [Category C] (G : Profiniteᵒᵖ ⥤ C)

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

noncomputable
def isColimitCocone (hc : IsLimit c) [∀ i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op) :
    IsColimit (cocone G c.pt) := (functorOp_final c hc).isColimitWhiskerEquiv _ hc'

end Colimit

end Extend

open Extend

section ProfiniteAsLimit

variable (S : Profinite)

abbrev diagram' : StructuredArrow S toProfinite ⥤ Profinite :=
  StructuredArrow.proj S toProfinite ⋙ toProfinite

def asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S

instance (i : DiscreteQuotient S) : Epi (S.asLimitCone.π.app i) :=
  (epi_iff_surjective _).mpr i.proj_surjective

noncomputable def asLimit' : IsLimit S.asLimitCone' := isLimitCone _ (𝟭 _) S.asLimit S.asLimit

noncomputable def lim' : LimitCone S.diagram' := ⟨S.asLimitCone', S.asLimit'⟩

end ProfiniteAsLimit

end Profinite
