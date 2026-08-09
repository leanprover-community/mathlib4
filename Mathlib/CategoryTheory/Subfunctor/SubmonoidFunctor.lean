/-
Copyright (c) 2026 John Rozmarynowycz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Rozmarynowycz
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Functors of submonoids

Given a functor `M : C ⥤ MonCat`, we define a functor of submonoids `S` to be a
family `Submonoid (M.obj U)` for all `U : C` that are compatible with the maps induced by `M`.

We provide the complete lattice structure and the basic functoriality properties.

## TODO

- Show the Galois connection between `SubmonoidFunctor.image` and `SubmonoidFunctor.comap`
  and provide the related API.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {M : C ⥤ MonCat.{w}}

variable (M) in
/-- A submonoid functor consists of a submonoid of `M.obj U` for every `U`,
compatible with the restriction maps `M.map i`. -/
@[ext]
structure SubmonoidFunctor where
  /-- A submonoid of `M.obj U` for all `U : C`. -/
  obj (U : C) : Submonoid (M.obj U)
  /-- For any `i : U ⟶ V`, `M.map i` maps the submonoid `obj U` into the submonoid `obj V`. -/
  map {U V : C} (i : U ⟶ V) : obj U ≤ (obj V).comap (M.map i).hom := by cat_disch

namespace SubmonoidFunctor

variable (S : SubmonoidFunctor M)

lemma map_le {U V : C} (f : U ⟶ V) : (S.obj U).map (M.map f).hom ≤ S.obj V := by
  grw [Submonoid.map_le_iff_le_comap, S.map f]

/-- The functor of monoids associated to a functor of submonoids. -/
@[simps obj map]
def toFunctor : C ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i :=
    MonCat.ofHom <| ((M.map i).hom.submonoidComap (S.obj _)).comp <| Submonoid.inclusion (S.map i)

/-- The subfunctor associated to a functor of submonoids. -/
@[simps obj]
def toSubfunctor : Subfunctor (M ⋙ forget MonCat) where
  obj _ := (S.obj _).carrier
  map := S.map

variable {M M' M'' : C ⥤ MonCat.{w}} (S : SubmonoidFunctor M) (S' : SubmonoidFunctor M')

instance {U : C} : CoeHead (S.toFunctor.obj U) (M.obj U) where
  coe := Subtype.val

instance : PartialOrder (SubmonoidFunctor M) :=
  PartialOrder.lift SubmonoidFunctor.obj fun _ _ => SubmonoidFunctor.ext

@[simps! top_obj bot_obj sup_obj inf_obj sInf_obj sSup_obj]
instance : CompleteLattice (SubmonoidFunctor M) where
  sup F G :=
    { obj _ := F.obj _ ⊔ G.obj _
      map i := by grw [F.map i, G.map i, (Submonoid.monotone_comap).le_map_sup] }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by simp [h₁ U, h₂ U]
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩ }
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj _ := ⨆ F ∈ S, F.obj _
      map {U V} f := by
        grw [← Submonoid.monotone_comap.le_map_iSup₂]
        exact iSup₂_mono fun F _ ↦ F.map f }
  isLUB_sSup _ := ⟨fun a ha U ↦ le_iSup₂_of_le a ha le_rfl, fun _ _ _ ↦ by aesop⟩
  sInf S :=
    { obj _ := ⨅ F ∈ S, F.obj _
      map f := by
        rw [(Submonoid.gc_map_comap (M.map f).hom).u_iInf₂]
        exact iInf₂_mono fun F _ ↦ F.map f }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot := { obj _ := ⊥ }
  bot_le _ _ := bot_le
  top := { obj _ := ⊤ }
  le_top _ _ := le_top

/-- The inclusion of a submonoid functor `S` to the original functor of monoids `M`. -/
@[simps]
def ι : S.toFunctor ⟶ M where
  app _ := MonCat.ofHom (Submonoid.subtype _)

instance : Mono S.ι := by
  suffices ∀ (X : C), Mono (S.ι.app X) from NatTrans.mono_of_mono_app _
  intro X
  exact ConcreteCategory.mono_of_injective _ Subtype.val_injective

section image

variable (p : M ⟶ M')

/-- The submonoid functor defined by the image along a morphism of functors of monoids. -/
@[simps]
def image (S : SubmonoidFunctor M) : SubmonoidFunctor M' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map i := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_map, ← MonCat.hom_comp, ← p.naturality,
      MonCat.hom_comp, ← Submonoid.map_map]
    grw [S.map_le]

variable (M) in
@[simp]
lemma image_id : image (𝟙 M) ⊤ = ⊤ := by aesop

@[simp]
lemma image_comp (p' : M' ⟶ M'') : S.image (p ≫ p') = (S.image p).image p' := by cat_disch

end image

section comap

variable (p : M ⟶ M') (S'' : SubmonoidFunctor M'')

/-- The submonoid functor defined by the preimage along a morphism of functors of monoids. -/
@[simps]
def comap (S' : SubmonoidFunctor M') : SubmonoidFunctor M where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

variable (M) in
@[simp]
lemma comap_id : comap (𝟙 M) ⊤ = ⊤ := rfl

@[simp]
lemma comap_comp (p' : M' ⟶ M'') : S''.comap (p ≫ p') = (S''.comap p').comap p := by rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma image_comap_ι : image S.ι (comap S.ι S) = S := by aesop

end comap

section lift

variable (p : M ⟶ M') (S : SubmonoidFunctor M) (S' : SubmonoidFunctor M')
  (hp : image p ⊤ ≤ S')

set_option backward.defeqAttrib.useBackward true in
/-- If the image of morphism `M' ⟶ M` lands in a submonoid functor `S`,
then the morphism factors through it. -/
@[simps! app]
def lift : M ⟶ S'.toFunctor where
  app U := MonCat.ofHom <| MonoidHom.codRestrict (p.app U).hom _ fun x ↦ hp _ (by simp)

@[reassoc (attr := simp)]
theorem lift_ι : lift p S' hp ≫ S'.ι = p := rfl

end lift

end SubmonoidFunctor

end CategoryTheory
