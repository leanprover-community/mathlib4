/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.EqToHom

#align_import category_theory.quotient from "leanprover-community/mathlib"@"740acc0e6f9adf4423f92a485d0456fc271482da"

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/


/-- A `HomRel` on `C` consists of a relation on every hom-set. -/
def HomRel (C) [Quiver C] :=
  ∀ ⦃X Y : C⦄, (X ⟶ Y) → (X ⟶ Y) → Prop
#align hom_rel HomRel

-- Porting Note: `deriving Inhabited` was not able to deduce this typeclass
instance (C) [Quiver C] : Inhabited (HomRel C) where
  default := fun _ _ _ _ ↦ PUnit

namespace CategoryTheory

variable {C : Type _} [Category C] (r : HomRel C)

/-- A `HomRel` is a congruence when it's an equivalence on every hom-set, and it can be composed
from left and right. -/
class Congruence : Prop where
  /-- `r` is an equivalence on every hom-set. -/
  isEquiv : ∀ {X Y}, IsEquiv _ (@r X Y)
  /-- Precomposition with an arrow respects `r`. -/
  compLeft : ∀ {X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z}, r g g' → r (f ≫ g) (f ≫ g')
  /-- Postcomposition with an arrow respects `r`. -/
  compRight : ∀ {X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z), r f f' → r (f ≫ g) (f' ≫ g)
#align category_theory.congruence CategoryTheory.Congruence

attribute [instance] Congruence.isEquiv

/-- A type synonym for `C`, thought of as the objects of the quotient category. -/
@[ext]
structure Quotient (r : HomRel C) where
  /-- The object of `C`. -/
  as : C
#align category_theory.quotient CategoryTheory.Quotient

instance [Inhabited C] : Inhabited (Quotient r) :=
  ⟨{ as := default }⟩

namespace Quotient

/-- Generates the closure of a family of relations w.r.t. composition from left and right. -/
inductive CompClosure (r : HomRel C) ⦃s t : C⦄ : (s ⟶ t) → (s ⟶ t) → Prop
  | intro {a b : C} (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) :
    CompClosure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)
#align category_theory.quotient.comp_closure CategoryTheory.Quotient.CompClosure

theorem CompClosure.of {a b : C} (m₁ m₂ : a ⟶ b) (h : r m₁ m₂) : CompClosure r m₁ m₂ := by
  simpa using CompClosure.intro (𝟙 _) m₁ m₂ (𝟙 _) h
  -- 🎉 no goals
#align category_theory.quotient.comp_closure.of CategoryTheory.Quotient.CompClosure.of

theorem comp_left {a b c : C} (f : a ⟶ b) :
    ∀ (g₁ g₂ : b ⟶ c) (_ : CompClosure r g₁ g₂), CompClosure r (f ≫ g₁) (f ≫ g₂)
  | _, _, ⟨x, m₁, m₂, y, h⟩ => by simpa using CompClosure.intro (f ≫ x) m₁ m₂ y h
                                  -- 🎉 no goals
#align category_theory.quotient.comp_left CategoryTheory.Quotient.comp_left

theorem comp_right {a b c : C} (g : b ⟶ c) :
    ∀ (f₁ f₂ : a ⟶ b) (_ : CompClosure r f₁ f₂), CompClosure r (f₁ ≫ g) (f₂ ≫ g)
  | _, _, ⟨x, m₁, m₂, y, h⟩ => by simpa using CompClosure.intro x m₁ m₂ (y ≫ g) h
                                  -- 🎉 no goals
#align category_theory.quotient.comp_right CategoryTheory.Quotient.comp_right

/-- Hom-sets of the quotient category. -/
def Hom (s t : Quotient r) :=
  Quot <| @CompClosure C _ r s.as t.as
#align category_theory.quotient.hom CategoryTheory.Quotient.Hom

instance (a : Quotient r) : Inhabited (Hom r a a) :=
  ⟨Quot.mk _ (𝟙 a.as)⟩

/-- Composition in the quotient category. -/
def comp ⦃a b c : Quotient r⦄ : Hom r a b → Hom r b c → Hom r a c := fun hf hg ↦
  Quot.liftOn hf
    (fun f ↦
      Quot.liftOn hg (fun g ↦ Quot.mk _ (f ≫ g)) fun g₁ g₂ h ↦
        Quot.sound <| comp_left r f g₁ g₂ h)
    fun f₁ f₂ h ↦ Quot.inductionOn hg fun g ↦ Quot.sound <| comp_right r g f₁ f₂ h
#align category_theory.quotient.comp CategoryTheory.Quotient.comp

@[simp]
theorem comp_mk {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    comp r (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g) :=
  rfl
#align category_theory.quotient.comp_mk CategoryTheory.Quotient.comp_mk

-- porting note: Had to manually add the proofs of `comp_id` `id_comp` and `assoc`
instance category : Category (Quotient r) where
  Hom := Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
  comp_id f := Quot.inductionOn f $ by simp
                                       -- 🎉 no goals
                                       -- 🎉 no goals
  id_comp f := Quot.inductionOn f $ by simp
  assoc f g h := Quot.inductionOn f $ Quot.inductionOn g $ Quot.inductionOn h $ by simp
                                                                                   -- 🎉 no goals
#align category_theory.quotient.category CategoryTheory.Quotient.category

/-- The functor from a category to its quotient. -/
@[simps]
def functor : C ⥤ Quotient r where
  obj a := { as := a }
  map := @fun _ _ f ↦ Quot.mk _ f
#align category_theory.quotient.functor CategoryTheory.Quotient.functor

noncomputable instance fullFunctor : Full (functor r) where preimage := @fun X Y f ↦ Quot.out f

instance : EssSurj (functor r)
    where mem_essImage Y :=
    ⟨Y.as, ⟨eqToIso (by
            ext
            -- ⊢ ((functor r).obj Y.as).as = Y.as
            rfl)⟩⟩
            -- 🎉 no goals

protected theorem induction {P : ∀ {a b : Quotient r}, (a ⟶ b) → Prop}
    (h : ∀ {x y : C} (f : x ⟶ y), P ((functor r).map f)) :
    ∀ {a b : Quotient r} (f : a ⟶ b), P f := by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  -- ⊢ P (Quot.mk (CompClosure r) f)
  exact h f
  -- 🎉 no goals
#align category_theory.quotient.induction CategoryTheory.Quotient.induction

protected theorem sound {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂) :
    (functor r).map f₁ = (functor r).map f₂ := by
  simpa using Quot.sound (CompClosure.intro (𝟙 a) f₁ f₂ (𝟙 b) h)
  -- 🎉 no goals
#align category_theory.quotient.sound CategoryTheory.Quotient.sound

theorem functor_map_eq_iff [h : Congruence r] {X Y : C} (f f' : X ⟶ Y) :
    (functor r).map f = (functor r).map f' ↔ r f f' := by
  constructor
  -- ⊢ (functor r).map f = (functor r).map f' → r f f'
  · erw [Quot.eq]
    -- ⊢ EqvGen (CompClosure r) f f' → r f f'
    intro h
    -- ⊢ r f f'
    induction' h with m m' hm
    · cases hm
      -- ⊢ r (f✝ ≫ m₁✝ ≫ g✝) (f✝ ≫ m₂✝ ≫ g✝)
      apply Congruence.compLeft
      -- ⊢ r (m₁✝ ≫ g✝) (m₂✝ ≫ g✝)
      apply Congruence.compRight
      -- ⊢ r m₁✝ m₂✝
      assumption
      -- 🎉 no goals
    · haveI := (h.isEquiv : IsEquiv _ (@r X Y))
      -- ⊢ r x✝ x✝
      -- porting note: had to add this line for `refl` (and name the `Congruence` argument)
      apply refl
      -- 🎉 no goals
    · apply symm
      -- ⊢ r x✝ y✝
      assumption
      -- 🎉 no goals
    · apply _root_.trans <;> assumption
                             -- 🎉 no goals
                             -- 🎉 no goals
  · apply Quotient.sound
    -- 🎉 no goals
#align category_theory.quotient.functor_map_eq_iff CategoryTheory.Quotient.functor_map_eq_iff

variable {D : Type _} [Category D] (F : C ⥤ D)
  (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

/-- The induced functor on the quotient category. -/
@[simps]
def lift : Quotient r ⥤ D where
  obj a := F.obj a.as
  map := @fun a b hf ↦
    Quot.liftOn hf (fun f ↦ F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, h⟩
        -- ⊢ (fun f => F.map f) (f✝ ≫ m₁✝ ≫ g✝) = (fun f => F.map f) (f✝ ≫ m₂✝ ≫ g✝)
        simp [H _ _ _ _ h])
        -- 🎉 no goals
  map_id a := F.map_id a.as
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    -- ⊢ { obj := fun a => F.obj a.as, map := fun a b hf => Quot.liftOn hf (fun f =>  …
    exact F.map_comp f g
    -- 🎉 no goals
#align category_theory.quotient.lift CategoryTheory.Quotient.lift

theorem lift_spec : functor r ⋙ lift r F H = F := by
  apply Functor.ext; rotate_left
  -- ⊢ autoParam (∀ (X Y : C) (f : X ⟶ Y), (functor r ⋙ lift r F H).map f = eqToHom …
                     -- ⊢ ∀ (X : C), (functor r ⋙ lift r F H).obj X = F.obj X
  · rintro X
    -- ⊢ (functor r ⋙ lift r F H).obj X = F.obj X
    rfl
    -- 🎉 no goals
  · rintro X Y f
    -- ⊢ (functor r ⋙ lift r F H).map f = eqToHom (_ : (functor r ⋙ lift r F H).obj X …
    simp
    -- 🎉 no goals
#align category_theory.quotient.lift_spec CategoryTheory.Quotient.lift_spec

theorem lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H := by
  subst_vars
  -- ⊢ Φ = lift r (functor r ⋙ Φ) H
  fapply Functor.hext
  -- ⊢ ∀ (X : Quotient r), Φ.obj X = (lift r (functor r ⋙ Φ) H).obj X
  · rintro X
    -- ⊢ Φ.obj X = (lift r (functor r ⋙ Φ) H).obj X
    dsimp [lift, Functor]
    -- ⊢ Φ.obj X = Φ.obj ((functor r).obj X.as)
    congr
    -- 🎉 no goals
  · rintro _ _ f
    -- ⊢ HEq (Φ.map f) ((lift r (functor r ⋙ Φ) H).map f)
    dsimp [lift, Functor]
    -- ⊢ HEq (Φ.map f) (Quot.liftOn f (fun f => Φ.map (Quot.mk (CompClosure r) f)) (_ …
    refine Quot.inductionOn f (fun _ ↦ ?_) -- porting note: this line was originally an `apply`
    -- ⊢ HEq (Φ.map (Quot.mk (CompClosure r) x✝)) (Quot.liftOn (Quot.mk (CompClosure  …
    simp only [Quot.liftOn_mk, Functor.comp_map]
    -- ⊢ HEq (Φ.map (Quot.mk (CompClosure r) x✝)) (Φ.map (Quot.mk (CompClosure r) x✝))
    congr
    -- 🎉 no goals
#align category_theory.quotient.lift_unique CategoryTheory.Quotient.lift_unique

/-- The original functor factors through the induced functor. -/
def lift.isLift : functor r ⋙ lift r F H ≅ F :=
  NatIso.ofComponents fun X ↦ Iso.refl _
#align category_theory.quotient.lift.is_lift CategoryTheory.Quotient.lift.isLift

@[simp]
theorem lift.isLift_hom (X : C) : (lift.isLift r F H).hom.app X = 𝟙 (F.obj X) :=
  rfl
#align category_theory.quotient.lift.is_lift_hom CategoryTheory.Quotient.lift.isLift_hom

@[simp]
theorem lift.isLift_inv (X : C) : (lift.isLift r F H).inv.app X = 𝟙 (F.obj X) :=
  rfl
#align category_theory.quotient.lift.is_lift_inv CategoryTheory.Quotient.lift.isLift_inv

theorem lift_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (lift r F H).map ((functor r).map f) = F.map f := by
  rw [← NatIso.naturality_1 (lift.isLift r F H)]
  -- ⊢ (lift r F H).map ((functor r).map f) = NatTrans.app (lift.isLift r F H).inv  …
  dsimp
  -- ⊢ Quot.liftOn (Quot.mk (CompClosure r) f) (fun f => F.map f) (_ : ∀ (a b : ((f …
  simp
  -- 🎉 no goals
#align category_theory.quotient.lift_map_functor_map CategoryTheory.Quotient.lift_map_functor_map

end Quotient

end CategoryTheory
