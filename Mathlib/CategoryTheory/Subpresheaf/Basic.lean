/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Sites.IsSheafFor


/-!

# Subpresheaf of types

We define the subpresheaf of a type valued presheaf.

## Main results

- `CategoryTheory.Subpresheaf` :
  A subpresheaf of a presheaf of types.

-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A subpresheaf of a presheaf consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
structure Subpresheaf (F : Cᵒᵖ ⥤ Type w) where
  /-- If `G` is a sub-presheaf of `F`, then the sections of `G` on `U` forms a subset of sections of
    `F` on `U`. -/
  obj : ∀ U, Set (F.obj U)
  /-- If `G` is a sub-presheaf of `F` and `i : U ⟶ V`, then for each `G`-sections on `U` `x`,
    `F i x` is in `F(V)`. -/
  map : ∀ {U V : Cᵒᵖ} (i : U ⟶ V), obj U ⊆ F.map i ⁻¹' obj V

@[deprecated (since := "2025-01-08")] alias GrothendieckTopology.Subpresheaf := Subpresheaf

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subpresheaf F)

instance : PartialOrder (Subpresheaf F) :=
  PartialOrder.lift Subpresheaf.obj (fun _ _ => Subpresheaf.ext)

instance : Top (Subpresheaf F) :=
  ⟨⟨fun _ => ⊤, @fun U _ _ x _ => by simp⟩⟩

instance : Nonempty (Subpresheaf F) :=
  inferInstance

/-- The subpresheaf as a presheaf. -/
@[simps!]
def Subpresheaf.toPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := G.obj U
  map := @fun _ _ i x => ⟨F.map i x, G.map i x.prop⟩
  map_id X := by
    ext ⟨x, _⟩
    dsimp
    simp only [FunctorToTypes.map_id_apply]
  map_comp := @fun X Y Z i j => by
    ext ⟨x, _⟩
    dsimp
    simp only [FunctorToTypes.map_comp_apply]

instance {U} : CoeHead (G.toPresheaf.obj U) (F.obj U) where
  coe := Subtype.val

/-- The inclusion of a subpresheaf to the original presheaf. -/
@[simps]
def Subpresheaf.ι : G.toPresheaf ⟶ F where app _ x := x

instance : Mono G.ι :=
  ⟨@fun _ _ _ e =>
    NatTrans.ext <|
      funext fun U => funext fun x => Subtype.ext <| congr_fun (congr_app e U) x⟩

/-- The inclusion of a subpresheaf to a larger subpresheaf -/
@[simps]
def Subpresheaf.homOfLe {G G' : Subpresheaf F} (h : G ≤ G') : G.toPresheaf ⟶ G'.toPresheaf where
  app U x := ⟨x, h U x.prop⟩

instance {G G' : Subpresheaf F} (h : G ≤ G') : Mono (Subpresheaf.homOfLe h) :=
  ⟨fun _ _ e =>
    NatTrans.ext <|
      funext fun U =>
        funext fun x =>
          Subtype.ext <| (congr_arg Subtype.val <| (congr_fun (congr_app e U) x :) :)⟩

@[reassoc (attr := simp)]
theorem Subpresheaf.homOfLe_ι {G G' : Subpresheaf F} (h : G ≤ G') :
    Subpresheaf.homOfLe h ≫ G'.ι = G.ι := by
  ext
  rfl

instance : IsIso (Subpresheaf.ι (⊤ : Subpresheaf F)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

theorem Subpresheaf.eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι := by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2

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

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
def Subpresheaf.sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where
  arrows V f := F.map f.op s ∈ G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simp only [op_unop, op_comp, FunctorToTypes.map_comp_apply]
    exact G.map _ hi

/-- Given an `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
def Subpresheaf.familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toPresheaf := fun _ i hi => ⟨F.map i.op s, hi⟩

theorem Subpresheaf.family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine Subtype.ext ?_ -- Porting note: `ext1` does not work here
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, e]

theorem Subpresheaf.nat_trans_naturality (f : F' ⟶ G.toPresheaf) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congr_arg Subtype.val (FunctorToTypes.naturality _ _ f i x)

section Image

/-- The image presheaf of a morphism, whose components are the set-theoretic images. -/
@[simps]
def imagePresheaf (f : F' ⟶ F) : Subpresheaf F where
  obj U := Set.range (f.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    have := elementwise_of% f.naturality
    exact ⟨_, this i x⟩

@[simp]
theorem top_subpresheaf_obj (U) : (⊤ : Subpresheaf F).obj U = ⊤ :=
  rfl

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

end Image

end CategoryTheory
