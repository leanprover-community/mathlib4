import Mathlib.Condensed.LocallyConstant
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Category.Profinite.CofilteredLimit

universe u

open CategoryTheory Functor Limits Condensed FintypeCat StructuredArrow

namespace Condensed

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (F : I ⥤ FintypeCat.{u})
    (c : Cone <| F ⋙ toProfinite) (hc : IsLimit c)

namespace ToStructuredArrow

@[simps]
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)
  map_id _ := by
    simp only [CategoryTheory.Functor.map_id, hom_eq_iff, mk_right, homMk_right, id_right]
  map_comp _ _ := by simp only [Functor.map_comp, hom_eq_iff, mk_right, homMk_right, comp_right]

def functorIso : functor F c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

attribute [local instance] FintypeCat.discreteTopology

-- TODO: PR
instance : Faithful toProfinite where
  map_injective h := funext fun _ ↦ (DFunLike.ext_iff.mp h) _

-- TODO: PR
instance : Full toProfinite where
  preimage f := fun x ↦ f x
  witness _ := rfl

instance [∀ i, Epi (c.π.app i)] : Initial (functor F c) := by
  rw [initial_iff_of_isCofiltered (F := functor F c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    have : DiscreteTopology (toProfinite.obj X) := by
      simp only [toProfinite, Profinite.of]
      infer_instance
    let f' : LocallyConstant c.pt (toProfinite.obj X) := ⟨f, by
      rw [IsLocallyConstant.iff_continuous]
      exact f.continuous⟩
    obtain ⟨i, g, h⟩ := Profinite.exists_locallyConstant.{_, u, u} c hc f'
    refine ⟨i, ⟨homMk g.toFun ?_⟩⟩
    ext x
    have := (LocallyConstant.congr_fun h x).symm
    erw [LocallyConstant.coe_comap_apply _ _ (c.π.app i).continuous] at this
    exact this
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩ i ⟨_, (s : F.obj i ⟶ X), (w : f = c.π.app i ≫ _)⟩
      ⟨_, (s' : F.obj i ⟶ X), (w' : f = c.π.app i ≫ _)⟩
    simp only [functor_obj, functor_map, hom_eq_iff, mk_right, comp_right, homMk_right]
    refine ⟨i, 𝟙 _, ?_⟩
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [w] at w'
    exact toProfinite.map_injective <| Epi.left_cancellation _ _ w'

end Condensed.ToStructuredArrow
