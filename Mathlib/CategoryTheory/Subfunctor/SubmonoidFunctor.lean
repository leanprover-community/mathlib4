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

## Submonoid Functor

Given a functor `R: C ⥤ MonCat`, we define a subfunctor of submonoids. We also define
a sheaf of submonoids when `R` is a sheaf.

-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {R : C ⥤ MonCat.{w}}

variable (R) in
@[ext]
structure SubmonoidFunctors where
  /-- a family of submonoids of `R.obj X` for all `X`. -/
  obj : ∀ U, Submonoid (R.obj U)
  /-- If `S` is a submonoid functor of `R` and `i : U ⟶ V`, then for each `S`-sections on `U`
  `x`, `R i x` is in `S(V)`. -/
  map : ∀ {U V : C} (i : U ⟶ V), obj U ≤ (obj V).comap (R.map i).hom

namespace SubmonoidFunctors

/-- The functor of monoids associated to a subfunctor of submonoids. -/
@[simps obj map]
def toMonoidFunctor (S : SubmonoidFunctors R) : C ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i:=
    MonCat.ofHom <| ((R.map i).hom.submonoidComap (S.obj _)).comp <| Submonoid.inclusion (S.map i)
  map_id _ := by cat_disch
  map_comp _ _ := by cat_disch

variable {R R' : C ⥤ MonCat.{w}} (S : SubmonoidFunctors R) (S' : SubmonoidFunctors R')

instance {U : C} : CoeHead (S.toMonoidFunctor.obj U) (R.obj U) where
  coe := Subtype.val

instance : PartialOrder (SubmonoidFunctors R) :=
  PartialOrder.lift SubmonoidFunctors.obj (fun _ _ => SubmonoidFunctors.ext)

instance : CompleteLattice (SubmonoidFunctors R) where
  sup F G := {
    obj U := F.obj U ⊔ G.obj U
    map i _ := by
      expose_names
      simp only [Submonoid.mem_comap, Submonoid.sup_eq_closure,
        Submonoid.mem_closure]
      intro h T hT
      have : (R.map i)⁻¹' (↑(F.obj V) ∪ ↑(G.obj V)) ⊆ (R.map i)⁻¹' T := by cat_disch
      have : ((F.obj U).carrier ∪ (G.obj U).carrier) ⊆ (R.map i)⁻¹' T := by
        simp_all only [Set.union_subset_iff, SetLike.coe_subset_coe, and_imp, Set.preimage_union]
        obtain ⟨left, right⟩ := hT
        obtain ⟨left_1, right_1⟩ := this
        apply And.intro
        · have : (F.obj U).carrier ⊆ ⇑(hom (R.map i)) ⁻¹' ↑(F.obj V).carrier :=  F.map i
          tauto
        · have : (G.obj U).carrier ⊆ ⇑(hom (R.map i)) ⁻¹' ↑(G.obj V).carrier :=  G.map i
          tauto
      exact h (Submonoid.comap (MonCat.Hom.hom (R.map i)) T) this
    }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    simp only [sup_le_iff]
    tauto
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj _ := sSup (Set.image (fun T ↦ T.obj _) S)
      map f x hx := by
        erw [sSup_image', Submonoid.mem_iSup]
        rw [sSup_image',Submonoid.mem_iSup ] at hx
        intro N hN
        expose_names
        have : ∀ (i : S), ⇑(hom (R.map f)) ⁻¹' ((@Subtype.val (SubmonoidFunctors R)
          (fun x ↦ x ∈ S) i).obj V) ≤ ⇑(hom (R.map f)) ⁻¹' N.carrier := by tauto
        have : ∀ (i : S), ((@Subtype.val (SubmonoidFunctors R) (fun x ↦ x ∈ S) i).obj U) ≤
          ⇑(hom (R.map f)) ⁻¹' N.carrier := by
          intro i
          simp_all only [Subtype.forall, Set.le_eq_subset]
          obtain ⟨val, property⟩ := i
          have : (val.obj U).carrier ⊆ ⇑(hom (R.map f)) ⁻¹' ↑(val.obj V).carrier := val.map f
          tauto
        apply hx (Submonoid.comap (MonCat.Hom.hom (R.map f)) N) this
        }
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
  app _ := MonCat.ofHom {
    toFun := fun x ↦ x
    map_one' := by simp only [OneMemClass.coe_one]
    map_mul' _ _  := by simp only [Submonoid.coe_mul]
    }
  naturality _ _ _ := by cat_disch

section range

/-- The submonoid functor defined by the image along a morphism of functors of monoids. -/
@[simps]
def range (S : SubmonoidFunctors R) (p : R ⟶ R') : SubmonoidFunctors R' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map := by
    rintro U V i a h
    obtain ⟨x, h ⟩ := h
    use (hom (R.map i)) x
    have : x ∈ (hom (R.map i)) ⁻¹' (S.obj V).carrier := by
      exact (Set.mem_of_mem_of_subset h.1 (S.map i))
    cat_disch

variable (R) in
lemma range_id : range ⊤ (𝟙 R) = ⊤  := by aesop

end range

section comap

/-- The submonoid functor defined by the preimage along a morphism of functors of monoids. -/
@[simps]
def comap (S' : SubmonoidFunctors R') (p : R ⟶ R') : SubmonoidFunctors R where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

@[simp]
lemma range_comap_ι : range (comap S (S.ι)) (S.ι) = S := by aesop

end comap

section lift

variable (p' : R' ⟶ R) (S : SubmonoidFunctors R) (S' : SubmonoidFunctors R')
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

end SubmonoidFunctors

end CategoryTheory
