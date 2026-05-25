/-
Copyright (c) 2026 John Rozmarynowycz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Rozmarynowycz
-/
module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder

/-!

# Functors of submonoids

Given a functor `R : C ⥤ MonCat`, we define a functor of submonoids `S` to be a
family `Submonoid (R.obj U)` for all `U : C` that are compatible with the maps induced by `R`.

We provide the complete lattice structure and the basic functoriality properties.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {M : C ⥤ MonCat.{w}}

variable (R) in
/-- A submonoid functor consists of a submonoid of `R.obj U` for every `U`,
compatible with the restriction maps `R.map i`. -/
@[ext]
structure SubmonoidFunctor where
  /-- A submonoid of `R.obj U` for all `U : C`. -/
  obj (U : C) : Submonoid (R.obj U)
  /-- For any `i : U ⟶ V`, `R.map i` maps the submonoid `obj U` into the submonoid `obj V`. -/
  map {U V : C} (i : U ⟶ V) : obj U ≤ (obj V).comap (R.map i).hom

namespace SubmonoidFunctor

/-- The functor of monoids associated to a functor of submonoids. -/
@[simps obj map]
def toMonoidFunctor (S : SubmonoidFunctor R) : C ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i :=
    MonCat.ofHom <| ((R.map i).hom.submonoidComap (S.obj _)).comp <| Submonoid.inclusion (S.map i)

/-- The subfunctor associated to a functor of submonoids. -/
@[simps obj]
def toSubfunctor (S : SubmonoidFunctor R) : Subfunctor (R ⋙ forget MonCat) where
  obj _ := (S.obj _).carrier
  map := S.map

variable {R R' : C ⥤ MonCat.{w}} (S : SubmonoidFunctor R) (S' : SubmonoidFunctor R')

lemma map_le {U V : C} (f : U ⟶ V) : (S.obj U).map (R.map f).hom ≤ S.obj V := by
  grw [Submonoid.map_le_iff_le_comap, S.map f]

attribute [gcongr] Submonoid.monotone_map Submonoid.monotone_comap

instance {U : C} : CoeHead (S.toMonoidFunctor.obj U) (R.obj U) where
  coe := Subtype.val

instance : PartialOrder (SubmonoidFunctor R) :=
  PartialOrder.lift SubmonoidFunctor.obj fun _ _ => SubmonoidFunctor.ext

instance : CompleteLattice (SubmonoidFunctor R) where
  sup F G := {
    obj U := F.obj U ⊔ G.obj U
    map i := by grw [F.map i, G.map i, (Submonoid.monotone_comap).le_map_sup]
    }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by simp [h₁ U, h₂ U]
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := ⨆ F ∈ S, F.obj U
      map {U V} f := by
        grw [← Submonoid.monotone_comap.le_map_iSup₂]
        exact iSup₂_mono fun F _ ↦ F.map f }
  isLUB_sSup _ := ⟨fun a ha U ↦ le_iSup₂_of_le a ha le_rfl, fun _ _ _ ↦ by aesop⟩
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f := by
        rw [(Submonoid.gc_map_comap (R.map f).hom).u_iInf₂]
        exact iInf₂_mono fun F _ ↦ F.map f }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot := { obj _ := ⊥ }
  bot_le _ _ := bot_le
  top := { obj _ := ⊤ }
  le_top _ _ := le_top

/-- The inclusion of a submonoid functor `S` to the original functor of monoids `R`. -/
@[simps]
def ι : S.toMonoidFunctor ⟶ R where
  app _ := MonCat.ofHom (Submonoid.subtype _)

section image

/-- The submonoid functor defined by the image along a morphism of functors of monoids. -/
@[simps]
def image (S : SubmonoidFunctor R) (p : R ⟶ R') : SubmonoidFunctor R' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map i := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_map, ← MonCat.hom_comp, ← p.naturality,
      MonCat.hom_comp, ← Submonoid.map_map]
    grw [S.map_le]

variable (R) in
lemma image_id : image ⊤ (𝟙 R) = ⊤ := by aesop

end image

section comap

/-- The submonoid functor defined by the preimage along a morphism of functors of monoids. -/
@[simps]
def comap (S' : SubmonoidFunctor R') (p : R ⟶ R') : SubmonoidFunctor R where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

@[simp]
lemma image_comap_ι : image (comap S (S.ι)) (S.ι) = S := by aesop

end comap

section lift

variable (p' : R' ⟶ R) (S : SubmonoidFunctor R) (S' : SubmonoidFunctor R')
  (hp' : image S' p' ≤ S)

/-- If the image of a submonoid functor `S'` under a morphism of
functors of monoids falls in another submonoid functor `S`,
then the morphism factors through it. -/
@[simps! app]
def lift : S'.toMonoidFunctor ⟶ S.toMonoidFunctor where
  app U := MonCat.ofHom {
    toFun := (↾fun x => ⟨p'.app U x, hp' U (by aesop)⟩)
    map_one' := by aesop
    map_mul' := by aesop
  }
  naturality _ _ g := by
    ext x
    simp only [toMonoidFunctor_obj,toMonoidFunctor_map,
      TypeCat.Fun.coe_mk, MonCat.hom_comp, hom_ofHom, Subtype.ext_iff]
    simp only [SetLike.coe_eq_coe]
    erw [MonoidHom.comp_apply]
    simpa [Subtype.ext_iff, -NatTrans.naturality_apply] using NatTrans.naturality_apply p' g x

@[reassoc (attr := simp)]
theorem lift_ι : lift p' S S' hp' ≫ S.ι = S'.ι ≫ p' := rfl

end lift

end SubmonoidFunctor

end CategoryTheory
