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

Given a functor `R: C ⥤ MonCat`, we define a subfunctor of submonoids.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {R : C ⥤ MonCat.{w}}

variable (R) in
/-- A submonoid functor consists of a submonoid of `R.obj U` for every `U`,
compatible with the restriction maps `R.map i`. -/
@[ext]
structure SubmonoidFunctor where
  /-- A family of submonoids of `R.obj X` for all `X`. -/
  obj : ∀ U, Submonoid (R.obj U)
  /-- For any `i : U ⟶ V`, `R.map i` maps the submonoid `obj U` into the submonoid `obj V`. -/
  map : ∀ {U V : C} (i : U ⟶ V), obj U ≤ (obj V).comap (R.map i).hom

namespace SubmonoidFunctor

/-- The functor of monoids associated to a subfunctor of submonoids. -/
@[simps obj map]
def toMonoidFunctor (S : SubmonoidFunctor R) : C ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i :=
    MonCat.ofHom <| ((R.map i).hom.submonoidComap (S.obj _)).comp <| Submonoid.inclusion (S.map i)

variable {R R' : C ⥤ MonCat.{w}} (S : SubmonoidFunctor R) (S' : SubmonoidFunctor R')

instance {U : C} : CoeHead (S.toMonoidFunctor.obj U) (R.obj U) where
  coe := Subtype.val

instance : PartialOrder (SubmonoidFunctor R) :=
  PartialOrder.lift SubmonoidFunctor.obj (fun _ _ => SubmonoidFunctor.ext)

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
        nth_rw 2 [← sSup_image]
        refine le_trans ?_ Submonoid.monotone_comap.le_map_sSup
        rw [iSup_image]
        exact iSup₂_mono fun F _ ↦ F.map f }
  isLUB_sSup _ := ⟨fun _ _ _ _ ↦ by
    intro a
    simp only [sSup_image', Submonoid.mem_iSup];
    intro N i
    aesop, fun _ _ _ ↦ by aesop⟩
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨s, h, rfl⟩
        rw [Submonoid.mem_sInf] at hx
        simp_all only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
          Set.iInter_exists, Set.mem_iInter, SetLike.mem_coe]
        intro i a a_1
        subst a_1
        expose_names
        have : (i.obj U).carrier ⊆ ⇑(hom (R.map f)) ⁻¹' ↑(i.obj V).carrier := i.map f
        tauto  }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot :=
    { obj _ := ⊥
      map _ _ h := by simp_all only [Submonoid.mem_bot, one_mem]}
  bot_le _ _ := bot_le
  top :=
    { obj _ := ⊤
      map _ _ h:= Set.mem_preimage.mpr h }
  le_top _ _ := le_top

/-- The inclusion of a submonoid functor `S` to the original functor of monoids `R`. -/
@[simps]
def ι : S.toMonoidFunctor ⟶ R where
  app _ := MonCat.ofHom (Submonoid.subtype _)

section range

/-- The submonoid functor defined by the image along a morphism of functors of monoids. -/
@[simps]
def range (S : SubmonoidFunctor R) (p : R ⟶ R') : SubmonoidFunctor R' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map := by
    rintro U V i a h
    obtain ⟨x, h ⟩ := h
    use (hom (R.map i)) x
    have : x ∈ (hom (R.map i)) ⁻¹' (S.obj V).carrier := by
      exact (Set.mem_of_mem_of_subset h.1 (S.map i))
    cat_disch

variable (R) in
lemma range_id : range ⊤ (𝟙 R) = ⊤ := by aesop

end range

section comap

/-- The submonoid functor defined by the preimage along a morphism of functors of monoids. -/
@[simps]
def comap (S' : SubmonoidFunctor R') (p : R ⟶ R') : SubmonoidFunctor R where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

@[simp]
lemma range_comap_ι : range (comap S (S.ι)) (S.ι) = S := by aesop

end comap

section lift

variable (p' : R' ⟶ R) (S : SubmonoidFunctor R) (S' : SubmonoidFunctor R')
  (hp' : range S' p' ≤ S)

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

theorem lift_ι : lift p' S S' hp' ≫ S.ι = S'.ι ≫ p' := rfl

end lift

end SubmonoidFunctor

end CategoryTheory
