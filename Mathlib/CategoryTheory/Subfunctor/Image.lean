/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The image of a subfunctor

Given a morphism of type-valued functors `p : F' ⟶ F`, we define its range
`Subfunctor.range p`. More generally, if `G' : Subfunctor F'`, we
define `G'.image p : Subfunctor F` as the image of `G'` by `f`, and
if `G : Subfunctor F`, we define its preimage `G.preimage f : Subfunctor F'`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F F' F'' : C ⥤ Type w}

namespace Subfunctor

section range

/-- The range of a morphism of type-valued functors, as a subfunctor of the target. -/
@[simps]
def range (p : F' ⟶ F) : Subfunctor F where
  obj U := Set.range (p.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    exact ⟨_, FunctorToTypes.naturality  _ _ p i x⟩

variable (F) in
lemma range_id : range (𝟙 F) = ⊤ := by aesop

@[simp]
lemma range_ι (G : Subfunctor F) : range G.ι = G := by aesop

end range

section lift

variable (f : F' ⟶ F) {G : Subfunctor F} (hf : range f ≤ G)

/-- If the image of a morphism falls in a subfunctor, then the morphism factors through it. -/
@[simps!]
def lift : F' ⟶ G.toFunctor where
  app U x := ⟨f.app U x, hf U (by simp)⟩
  naturality _ _ g := by
    ext x
    simpa [Subtype.ext_iff] using FunctorToTypes.naturality _ _ f g x

@[reassoc (attr := simp)]
theorem lift_ι : lift f hf ≫ G.ι = f := rfl

end lift

section range

variable (p : F' ⟶ F)

/-- Given a morphism `p : F' ⟶ F` of type-valued functors, this is the morphism
from `F'` to its range. -/
def toRange :
    F' ⟶ (range p).toFunctor :=
  lift p (by rfl)

@[reassoc (attr := simp)]
lemma toRange_ι : toRange p ≫ (range p).ι = p := rfl

lemma toRange_app_val {i : C} (x : F'.obj i) :
    ((toRange p).app i x).val = p.app i x := by
  simp [toRange]

@[simp]
lemma range_toRange : range (toRange p) = ⊤ := by
  ext i ⟨x, hx⟩
  dsimp at hx ⊢
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  simp only [Set.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

lemma epi_iff_range_eq_top :
    Epi p ↔ range p = ⊤ := by
  simp [NatTrans.epi_iff_epi_app, epi_iff_surjective, Subfunctor.ext_iff, funext_iff,
    Set.range_eq_univ]

lemma range_eq_top [Epi p] : range p = ⊤ := by rwa [← epi_iff_range_eq_top]

instance : Epi (toRange p) := by simp [epi_iff_range_eq_top]

instance [Mono p] : IsIso (toRange p) := by
  have := mono_of_mono_fac (toRange_ι p)
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  constructor
  · rw [← mono_iff_injective]
    infer_instance
  · rw [← epi_iff_surjective]
    infer_instance

lemma range_comp_le (f : F ⟶ F') (g : F' ⟶ F'') :
    range (f ≫ g) ≤ range g := fun _ _ _ ↦ by aesop

end range

section image

variable (G : Subfunctor F) (f : F ⟶ F')

/-- The image of a subfunctor by a morphism of type-valued functors. -/
@[simps]
def image : Subfunctor F' where
  obj i := (f.app i) '' (G.obj i)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨F.map φ x, G.map φ hx, by apply FunctorToTypes.naturality⟩

lemma image_top : (⊤ : Subfunctor F).image f = range f := by aesop

@[simp]
lemma image_iSup {ι : Type*} (G : ι → Subfunctor F) (f : F ⟶ F') :
    (⨆ i, G i).image f = ⨆ i, (G i).image f := by aesop

lemma image_comp (g : F' ⟶ F'') :
    G.image (f ≫ g) = (G.image f).image g := by aesop

lemma range_comp (g : F' ⟶ F'') :
    range (f ≫ g) = (range f).image g := by aesop

end image

section preimage

/-- The preimage of a subfunctor by a morphism of type-valued functors. -/
@[simps]
def preimage (G : Subfunctor F) (p : F' ⟶ F) : Subfunctor F' where
  obj n := p.app n ⁻¹' (G.obj n)
  map f := (Set.preimage_mono (G.map f)).trans (by
    simp only [Set.preimage_preimage, FunctorToTypes.naturality _ _ p f]
    rfl)

@[simp]
lemma preimage_id (G : Subfunctor F) :
    G.preimage (𝟙 F) = G := by aesop

lemma preimage_comp (G : Subfunctor F) (f : F'' ⟶ F') (g : F' ⟶ F) :
    G.preimage (f ≫ g) = (G.preimage g).preimage f := by aesop

lemma image_le_iff (G : Subfunctor F) (f : F ⟶ F') (G' : Subfunctor F') :
    G.image f ≤ G' ↔ G ≤ G'.preimage f := by
  simp [Subfunctor.le_def]

/-- Given a morphism `p : F' ⟶ F` of type-valued functors and `G : Subfunctor F`,
this is the morphism from the preimage of `G` by `p` to `G`. -/
def fromPreimage (G : Subfunctor F) (p : F' ⟶ F) :
    (G.preimage p).toFunctor ⟶ G.toFunctor :=
  lift ((G.preimage p).ι ≫ p) (by
    rw [range_comp, range_ι, image_le_iff])

@[reassoc]
lemma fromPreimage_ι (G : Subfunctor F) (p : F' ⟶ F) :
    G.fromPreimage p ≫ G.ι = (G.preimage p).ι ≫ p := rfl

lemma preimage_eq_top_iff (G : Subfunctor F) (p : F' ⟶ F) :
    G.preimage p = ⊤ ↔ range p ≤ G := by
  rw [← image_top, image_le_iff]
  simp

@[simp]
lemma preimage_image_of_epi (G : Subfunctor F) (p : F' ⟶ F) [hp : Epi p] :
    (G.preimage p).image p = G := by
  apply le_antisymm
  · rw [image_le_iff]
  · intro i x hx
    simp only [NatTrans.epi_iff_epi_app, epi_iff_surjective] at hp
    obtain ⟨y, rfl⟩ := hp _ x
    exact ⟨y, hx, rfl⟩

end preimage

@[deprecated (since := "2025-12-11")] alias Subpresheaf.range := range
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_id := range_id
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_ι := range_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.lift := lift
@[deprecated (since := "2025-12-11")] alias Subpresheaf.lift_ι := lift_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.toRange := toRange
@[deprecated (since := "2025-12-11")] alias Subpresheaf.toRange_ι := toRange_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.toRange_app_val := toRange_app_val
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_toRange := range_toRange
@[deprecated (since := "2025-12-11")] alias Subpresheaf.epi_iff_range_eq_top := epi_iff_range_eq_top
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_eq_top := range_eq_top
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_comp_le := range_comp_le
@[deprecated (since := "2025-12-11")] alias Subpresheaf.image := image
@[deprecated (since := "2025-12-11")] alias Subpresheaf.image_top := image_top
@[deprecated (since := "2025-12-11")] alias Subpresheaf.image_iSup := image_iSup
@[deprecated (since := "2025-12-11")] alias Subpresheaf.image_comp := image_comp
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_comp := range_comp
@[deprecated (since := "2025-12-11")] alias Subpresheaf.preimage := preimage
@[deprecated (since := "2025-12-11")] alias Subpresheaf.preimage_id := preimage_id
@[deprecated (since := "2025-12-11")] alias Subpresheaf.preimage_comp := preimage_comp
@[deprecated (since := "2025-12-11")] alias Subpresheaf.image_le_iff := image_le_iff
@[deprecated (since := "2025-12-11")] alias Subpresheaf.fromPreimage := fromPreimage
@[deprecated (since := "2025-12-11")] alias Subpresheaf.fromPreimage_ι := fromPreimage_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.preimage_eq_top_iff := preimage_eq_top_iff
@[deprecated (since := "2025-12-11")] alias Subpresheaf.preimage_image_of_epi :=
  preimage_image_of_epi

end Subfunctor

end CategoryTheory
