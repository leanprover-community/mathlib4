/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import Mathlib.CategoryTheory.Subpresheaf.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The image of a subpresheaf

Given a morphism of presheaves of types `f : F' ⟶ F`, we define `imagePresheaf f`
as a subpresheaf of `F`.

## TODO (@joelriou)
* introduce `Subpresheaf.image` and `Subpresheaf.preimage`

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F F' F'' : Cᵒᵖ ⥤ Type w} {G : Subpresheaf F}

/-- If the image of a morphism falls in a subpresheaf, then the morphism factors through it. -/
@[simps!]
def Subpresheaf.lift (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) : F' ⟶ G.toPresheaf where
  app U x := ⟨f.app U x, hf U x⟩
  naturality := by
    have := elementwise_of% f.naturality
    intros
    refine funext fun x => Subtype.ext ?_
    simp only [toPresheaf_obj, types_comp_apply]
    exact this _ _

@[reassoc (attr := simp)]
theorem Subpresheaf.lift_ι (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) :
    G.lift f hf ≫ G.ι = f := by
  ext
  rfl

/-- The image presheaf of a morphism, whose components are the set-theoretic images. -/
@[simps]
def imagePresheaf (f : F' ⟶ F) : Subpresheaf F where
  obj U := Set.range (f.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    have := elementwise_of% f.naturality
    exact ⟨_, this i x⟩

@[simp]
theorem imagePresheaf_id : imagePresheaf (𝟙 F) = ⊤ := by
  ext
  simp

/-- A morphism factors through the image presheaf. -/
@[simps!]
def toImagePresheaf (f : F' ⟶ F) : F' ⟶ (imagePresheaf f).toPresheaf :=
  (imagePresheaf f).lift f fun _ _ => Set.mem_range_self _

@[reassoc (attr := simp)]
theorem toImagePresheaf_ι (f : F' ⟶ F) : toImagePresheaf f ≫ (imagePresheaf f).ι = f :=
  (imagePresheaf f).lift_ι _ _

theorem imagePresheaf_comp_le (f₁ : F ⟶ F') (f₂ : F' ⟶ F'') :
    imagePresheaf (f₁ ≫ f₂) ≤ imagePresheaf f₂ := fun U _ hx => ⟨f₁.app U hx.choose, hx.choose_spec⟩

instance isIso_toImagePresheaf {F F' : Cᵒᵖ ⥤ Type w} (f : F ⟶ F') [hf : Mono f] :
  IsIso (toImagePresheaf f) := by
  have : ∀ (X : Cᵒᵖ), IsIso ((toImagePresheaf f).app X) := by
    intro X
    rw [isIso_iff_bijective]
    constructor
    · intro x y e
      have := (NatTrans.mono_iff_mono_app f).mp hf X
      rw [mono_iff_injective] at this
      exact this (congr_arg Subtype.val e :)
    · rintro ⟨_, ⟨x, rfl⟩⟩
      exact ⟨x, rfl⟩
  apply NatIso.isIso_of_isIso_app

end CategoryTheory
