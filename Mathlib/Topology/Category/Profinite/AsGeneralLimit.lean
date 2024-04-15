import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.CategoryTheory.Limits.KanExtension
import Mathlib.CategoryTheory.Filtered.Final

universe u

open CategoryTheory Limits FintypeCat Functor

attribute [local instance] FintypeCat.discreteTopology

namespace Profinite

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
    (c : Cone <| F ⋙ toProfinite)

lemma exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X) :
    ∃ (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g := by
  have : DiscreteTopology (toProfinite.obj X) := by
    dsimp only [toProfinite, Profinite.of]
    infer_instance
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

def cone : Cone (F ⋙ toProfinite ⋙ G) := G.mapCone c

def cone' (S : Profinite) : Cone (Ran.diagram toProfinite (toProfinite ⋙ G) S) where
  pt := G.obj S
  π := {
    app := fun i ↦ G.map i.hom
    naturality := fun _ _ f ↦ (by
      have := f.w
      simp only [Functor.const_obj_obj, StructuredArrow.left_eq_id, Functor.const_obj_map,
        Category.id_comp] at this
      simp only [Functor.const_obj_obj, Functor.comp_obj, StructuredArrow.proj_obj,
        Functor.const_obj_map, this, Functor.map_comp, Category.id_comp, Functor.comp_map,
        StructuredArrow.proj_map]) }

-- instance (hc : IsLimit c) : HasLimit (F ⋙ toProfinite) := ⟨c, hc⟩

example : cone c G = (cone' G c.pt).whisker (functor c) := rfl

variable [HasLimit (F ⋙ toProfinite ⋙ G)]

noncomputable
def can : G.obj c.pt ⟶ limit (F ⋙ toProfinite ⋙ G) :=
  limit.lift (F ⋙ toProfinite ⋙ G) (G.mapCone c)

variable [HasLimit (Ran.diagram toProfinite (toProfinite ⋙ G) c.pt)]

noncomputable
def can' : G.obj c.pt ⟶ limit (Ran.diagram toProfinite (toProfinite ⋙ G) c.pt) :=
  limit.lift (Ran.diagram toProfinite (toProfinite ⋙ G) c.pt) (cone' G c.pt)

end Limit

section Colimit

end Colimit

end Profinite.Extend
