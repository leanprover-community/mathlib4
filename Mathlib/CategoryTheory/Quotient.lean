/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module category_theory.quotient
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.CategoryTheory.EqToHom

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/


/-- A `hom_rel` on `C` consists of a relation on every hom-set. -/
def HomRel (C) [Quiver C] :=
  ∀ ⦃X Y : C⦄, (X ⟶ Y) → (X ⟶ Y) → Prop deriving Inhabited
#align hom_rel HomRel

namespace CategoryTheory

variable {C : Type _} [Category C] (r : HomRel C)

include r

/-- A `hom_rel` is a congruence when it's an equivalence on every hom-set, and it can be composed
from left and right. -/
class Congruence : Prop where
  IsEquiv : ∀ {X Y}, IsEquiv _ (@r X Y)
  compLeft : ∀ {X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z}, r g g' → r (f ≫ g) (f ≫ g')
  compRight : ∀ {X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z), r f f' → r (f ≫ g) (f' ≫ g)
#align category_theory.congruence CategoryTheory.Congruence

attribute [instance] congruence.is_equiv

/-- A type synonym for `C`, thought of as the objects of the quotient category. -/
@[ext]
structure Quotient where
  as : C
#align category_theory.quotient CategoryTheory.Quotient

instance [Inhabited C] : Inhabited (Quotient r) :=
  ⟨{ as := default }⟩

namespace Quotient

/-- Generates the closure of a family of relations w.r.t. composition from left and right. -/
inductive CompClosure ⦃s t : C⦄ : (s ⟶ t) → (s ⟶ t) → Prop
  |
  intro {a b} (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) :
    comp_closure (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)
#align category_theory.quotient.comp_closure CategoryTheory.Quotient.CompClosure

theorem CompClosure.of {a b} (m₁ m₂ : a ⟶ b) (h : r m₁ m₂) : CompClosure r m₁ m₂ := by
  simpa using comp_closure.intro (𝟙 _) m₁ m₂ (𝟙 _) h
#align category_theory.quotient.comp_closure.of CategoryTheory.Quotient.CompClosure.of

theorem comp_left {a b c : C} (f : a ⟶ b) :
    ∀ (g₁ g₂ : b ⟶ c) (h : CompClosure r g₁ g₂), CompClosure r (f ≫ g₁) (f ≫ g₂)
  | _, _, ⟨x, m₁, m₂, y, h⟩ => by simpa using comp_closure.intro (f ≫ x) m₁ m₂ y h
#align category_theory.quotient.comp_left CategoryTheory.Quotient.comp_left

theorem comp_right {a b c : C} (g : b ⟶ c) :
    ∀ (f₁ f₂ : a ⟶ b) (h : CompClosure r f₁ f₂), CompClosure r (f₁ ≫ g) (f₂ ≫ g)
  | _, _, ⟨x, m₁, m₂, y, h⟩ => by simpa using comp_closure.intro x m₁ m₂ (y ≫ g) h
#align category_theory.quotient.comp_right CategoryTheory.Quotient.comp_right

/-- Hom-sets of the quotient category. -/
def Hom (s t : Quotient r) :=
  Quot <| @CompClosure C _ r s.as t.as
#align category_theory.quotient.hom CategoryTheory.Quotient.Hom

instance (a : Quotient r) : Inhabited (Hom r a a) :=
  ⟨Quot.mk _ (𝟙 a.as)⟩

/-- Composition in the quotient category. -/
def comp ⦃a b c : Quotient r⦄ : Hom r a b → Hom r b c → Hom r a c := fun hf hg =>
  Quot.liftOn hf
    (fun f =>
      Quot.liftOn hg (fun g => Quot.mk _ (f ≫ g)) fun g₁ g₂ h =>
        Quot.sound <| comp_left r f g₁ g₂ h)
    fun f₁ f₂ h => Quot.inductionOn hg fun g => Quot.sound <| comp_right r g f₁ f₂ h
#align category_theory.quotient.comp CategoryTheory.Quotient.comp

@[simp]
theorem comp_mk {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    comp r (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g) :=
  rfl
#align category_theory.quotient.comp_mk CategoryTheory.Quotient.comp_mk

instance category : Category (Quotient r)
    where
  Hom := Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := comp r
#align category_theory.quotient.category CategoryTheory.Quotient.category

/-- The functor from a category to its quotient. -/
@[simps]
def functor : C ⥤ Quotient r where
  obj a := { as := a }
  map _ _ f := Quot.mk _ f
#align category_theory.quotient.functor CategoryTheory.Quotient.functor

noncomputable instance : Full (functor r) where preimage X Y f := Quot.out f

instance : EssSurj (functor r)
    where mem_essImage Y :=
    ⟨Y.as,
      ⟨eqToIso
          (by
            ext
            rfl)⟩⟩

protected theorem induction {P : ∀ {a b : Quotient r}, (a ⟶ b) → Prop}
    (h : ∀ {x y : C} (f : x ⟶ y), P ((functor r).map f)) : ∀ {a b : Quotient r} (f : a ⟶ b), P f :=
  by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  exact h f
#align category_theory.quotient.induction CategoryTheory.Quotient.induction

protected theorem sound {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂) :
    (functor r).map f₁ = (functor r).map f₂ := by
  simpa using Quot.sound (comp_closure.intro (𝟙 a) f₁ f₂ (𝟙 b) h)
#align category_theory.quotient.sound CategoryTheory.Quotient.sound

theorem functor_map_eq_iff [Congruence r] {X Y : C} (f f' : X ⟶ Y) :
    (functor r).map f = (functor r).map f' ↔ r f f' :=
  by
  constructor
  · erw [Quot.eq]
    intro h
    induction' h with m m' hm
    · cases hm
      apply congruence.comp_left
      apply congruence.comp_right
      assumption
    · apply refl
    · apply symm
      assumption
    · apply trans <;> assumption
  · apply Quotient.sound
#align category_theory.quotient.functor_map_eq_iff CategoryTheory.Quotient.functor_map_eq_iff

variable {D : Type _} [Category D] (F : C ⥤ D)
  (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

include H

/-- The induced functor on the quotient category. -/
@[simps]
def lift : Quotient r ⥤ D where
  obj a := F.obj a.as
  map a b hf :=
    Quot.liftOn hf (fun f => F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, h⟩
        simp [H _ _ _ _ h])
  map_id' a := F.map_id a.as
  map_comp' := by
    rintro a b c ⟨f⟩ ⟨g⟩
    exact F.map_comp f g
#align category_theory.quotient.lift CategoryTheory.Quotient.lift

theorem lift_spec : functor r ⋙ lift r F H = F :=
  by
  apply Functor.ext; rotate_left
  · rintro X
    rfl
  · rintro X Y f
    simp
#align category_theory.quotient.lift_spec CategoryTheory.Quotient.lift_spec

theorem lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H :=
  by
  subst_vars
  apply functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
    ext
    rfl
  · rintro X Y f
    dsimp [lift, Functor]
    apply Quot.inductionOn f
    rintro ff
    simp only [Quot.liftOn_mk, functor.comp_map]
    congr <;> ext <;> rfl
#align category_theory.quotient.lift_unique CategoryTheory.Quotient.lift_unique

/-- The original functor factors through the induced functor. -/
def lift.isLift : functor r ⋙ lift r F H ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align category_theory.quotient.lift.is_lift CategoryTheory.Quotient.lift.isLift

@[simp]
theorem lift.isLift_hom (X : C) : (lift.isLift r F H).Hom.app X = 𝟙 (F.obj X) :=
  rfl
#align category_theory.quotient.lift.is_lift_hom CategoryTheory.Quotient.lift.isLift_hom

@[simp]
theorem lift.isLift_inv (X : C) : (lift.isLift r F H).inv.app X = 𝟙 (F.obj X) :=
  rfl
#align category_theory.quotient.lift.is_lift_inv CategoryTheory.Quotient.lift.isLift_inv

theorem lift_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (lift r F H).map ((functor r).map f) = F.map f :=
  by
  rw [← nat_iso.naturality_1 (lift.is_lift r F H)]
  dsimp
  simp
#align category_theory.quotient.lift_map_functor_map CategoryTheory.Quotient.lift_map_functor_map

end Quotient

end CategoryTheory

