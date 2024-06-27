import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks


namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves is representable if for all diagrams
```
      yoneda(X)
        |
        |
        v
F --f--> G
```
The pullback `F ×_G yoneda.obj X` is representable. -/
def Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun _ G f ↦ ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), (pullback f g).Representable

-- TODO: prove this notion is stable under composition!
-- TODO: prove isomorphisms are representable (`RespectsIso`)
-- TODO: stable under base change

namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

noncomputable def pullback : C :=
  Functor.reprX (hF := hf g)

noncomputable def pullbackIso : yoneda.obj (hf.pullback g) ≅ Limits.pullback f g :=
  Functor.reprW (hF := hf g)

noncomputable def fst : hf'.pullback g ⟶ Y :=
  Yoneda.fullyFaithful.preimage ((hf'.pullbackIso g).hom ≫ Limits.pullback.fst)

noncomputable def snd : hf.pullback g ⟶ X :=
  Yoneda.fullyFaithful.preimage ((hf.pullbackIso g).hom ≫ Limits.pullback.snd)

@[simp, reassoc]
lemma yoneda_map_fst : yoneda.map (hf'.fst g) = (hf'.pullbackIso g).hom ≫ Limits.pullback.fst := by
  simp only [fst, Functor.FullyFaithful.map_preimage]

@[simp, reassoc]
lemma yoneda_map_snd : yoneda.map (hf.snd g) = (hf.pullbackIso g).hom ≫ Limits.pullback.snd := by
  simp only [snd, Functor.FullyFaithful.map_preimage]

@[reassoc]
lemma condition : yoneda.map (hf'.fst g) ≫ f' = yoneda.map (hf'.snd g) ≫ g := by
  simpa using Limits.pullback.condition

variable {g}

noncomputable def lift {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X)
    (hi : i ≫ f = yoneda.map h ≫ g) : Z ⟶ hf.pullback g :=
  Yoneda.fullyFaithful.preimage <| (Limits.pullback.lift _ _ hi) ≫ (hf.pullbackIso g).inv

noncomputable def lift' {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X)
    (hi : (yoneda.map i) ≫ f' = yoneda.map h ≫ g) : Z ⟶ hf'.pullback g :=
  hf'.lift _ _ hi

noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift (yoneda.map <| hf'.snd g) (hf'.fst g) (condition _ _).symm

end

def yoneda_representable [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    Presheaf.representable (yoneda.map f) := fun Z g ↦ by
  obtain ⟨g, rfl⟩ := yoneda.map_surjective g
  have : PreservesLimit (cospan f g) yoneda := sorry
  exact ⟨Limits.pullback f g, ⟨PreservesPullback.iso _ _ _⟩⟩

-- def pullback_yoneda {X : C} (g : yoneda.obj X ⟶ G) : yoneda.obj (pullback hf g) ⟶ F :=
--   Functor.reprY (hF := hf g)

end Presheaf.representable

namespace MorphismProperty

variable {F G : Cᵒᵖ ⥤ Type v} (P : MorphismProperty C)

def presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun _ G f ↦ ∃ (hf : Presheaf.representable f), ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), P (hf.snd g)

variable {P}

lemma presheaf.representable {f : F ⟶ G} (hf : P.presheaf f) : Presheaf.representable f :=
  hf.choose

lemma presheaf.representable_spec {f : F ⟶ G} (hf : P.presheaf f) {X : C} (g : yoneda.obj X ⟶ G) :
    P (hf.choose.snd g) :=
  hf.choose_spec g

-- if P is compatible w/ isos/comps/base change, then so is `presheaf P`
-- TODO: yoneda.map f satisfies P if f does

end MorphismProperty

end CategoryTheory
