/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax

#align_import category_theory.bicategory.natural_transformation from "leanprover-community/mathlib"@"4ff75f5b8502275a4c2eb2d2f02bdf84d7fb8993"

/-!
# Oplax natural transformations

Just as there are natural transformations between functors, there are oplax natural transformations
between oplax functors. The equality in the naturality of natural transformations is replaced by a
specified 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` in the case of oplax natural
transformations.

## Main definitions

* `OplaxNatTrans F G` : oplax natural transformations between oplax functors `F` and `G`
* `OplaxNatTrans.vcomp η θ` : the vertical composition of oplax natural transformations `η`
  and `θ`
* `OplaxNatTrans.category F G` : the category structure on the oplax natural transformations
  between `F` and `G`
-/

namespace CategoryTheory

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is an oplax natural transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfies the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure OplaxNatTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id :
    ∀ a : B,
      naturality (𝟙 a) ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      naturality (f ≫ g) ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat
#align category_theory.oplax_nat_trans CategoryTheory.OplaxNatTrans
#align category_theory.oplax_nat_trans.app CategoryTheory.OplaxNatTrans.app
#align category_theory.oplax_nat_trans.naturality CategoryTheory.OplaxNatTrans.naturality
#align category_theory.oplax_nat_trans.naturality_naturality' CategoryTheory.OplaxNatTrans.naturality_naturality
#align category_theory.oplax_nat_trans.naturality_naturality CategoryTheory.OplaxNatTrans.naturality_naturality
#align category_theory.oplax_nat_trans.naturality_id' CategoryTheory.OplaxNatTrans.naturality_id
#align category_theory.oplax_nat_trans.naturality_id CategoryTheory.OplaxNatTrans.naturality_id
#align category_theory.oplax_nat_trans.naturality_comp' CategoryTheory.OplaxNatTrans.naturality_comp
#align category_theory.oplax_nat_trans.naturality_comp CategoryTheory.OplaxNatTrans.naturality_comp

attribute [nolint docBlame] CategoryTheory.OplaxNatTrans.app
  CategoryTheory.OplaxNatTrans.naturality
  CategoryTheory.OplaxNatTrans.naturality_naturality
  CategoryTheory.OplaxNatTrans.naturality_id
  CategoryTheory.OplaxNatTrans.naturality_comp

attribute [reassoc (attr := simp)] OplaxNatTrans.naturality_naturality OplaxNatTrans.naturality_id
  OplaxNatTrans.naturality_comp

namespace OplaxNatTrans

section

variable (F : OplaxFunctor B C)

/-- The identity oplax natural transformation. -/
@[simps]
def id : OplaxNatTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv
#align category_theory.oplax_nat_trans.id CategoryTheory.OplaxNatTrans.id

instance : Inhabited (OplaxNatTrans F F) :=
  ⟨id F⟩

variable {F} {G H : OplaxFunctor B C} (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h =
      f ◁ θ.naturality g ≫ f ◁ θ.app a ◁ H.map₂ β := by
  simp_rw [← whiskerLeft_comp, naturality_naturality]
#align category_theory.oplax_nat_trans.whisker_left_naturality_naturality CategoryTheory.OplaxNatTrans.whiskerLeft_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h =
      η.naturality f ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  rw [← comp_whiskerRight, naturality_naturality, comp_whiskerRight, whisker_assoc]
#align category_theory.oplax_nat_trans.whisker_right_naturality_naturality CategoryTheory.OplaxNatTrans.whiskerRight_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ θ.naturality h ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  simp_rw [← whiskerLeft_comp, naturality_comp]
#align category_theory.oplax_nat_trans.whisker_left_naturality_comp CategoryTheory.OplaxNatTrans.whiskerLeft_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ η.naturality g ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                  η.naturality f ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_comp]; simp
#align category_theory.oplax_nat_trans.whisker_right_naturality_comp CategoryTheory.OplaxNatTrans.whiskerRight_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  simp_rw [← whiskerLeft_comp, naturality_id]
#align category_theory.oplax_nat_trans.whisker_left_naturality_id CategoryTheory.OplaxNatTrans.whiskerLeft_naturality_id

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_id]; simp
#align category_theory.oplax_nat_trans.whisker_right_naturality_id CategoryTheory.OplaxNatTrans.whiskerRight_naturality_id

end

/-- Vertical composition of oplax natural transformations. -/
@[simps]
def vcomp (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H) : OplaxNatTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g := by
    calc
      _ =
          ?_ ≫
            F.mapComp f g ▷ η.app c ▷ θ.app c ≫
              ?_ ≫
                F.map f ◁ η.naturality g ▷ θ.app c ≫
                  ?_ ≫
                    (F.map f ≫ η.app b) ◁ θ.naturality g ≫
                      η.naturality f ▷ (θ.app b ≫ H.map g) ≫
                        ?_ ≫ η.app a ◁ θ.naturality f ▷ H.map g ≫ ?_ :=
        ?_
      _ = _ := ?_
    · exact (α_ _ _ _).inv
    · exact (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom
    · exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv
    · exact (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv
    · exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv
    · rw [whisker_exchange_assoc]
      simp
    · simp
#align category_theory.oplax_nat_trans.vcomp CategoryTheory.OplaxNatTrans.vcomp

variable (B C)

@[simps id comp]
instance : CategoryStruct (OplaxFunctor B C) where
  Hom := OplaxNatTrans
  id := OplaxNatTrans.id
  comp := OplaxNatTrans.vcomp

end

section

variable {F G : OplaxFunctor B C}

/-- A modification `Γ` between oplax natural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification (η θ : F ⟶ G) where
  app (a : B) : η.app a ⟶ θ.app a
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f := by
    aesop_cat
#align category_theory.oplax_nat_trans.modification CategoryTheory.OplaxNatTrans.Modification
#align category_theory.oplax_nat_trans.modification.app CategoryTheory.OplaxNatTrans.Modification
#align category_theory.oplax_nat_trans.modification.naturality' CategoryTheory.OplaxNatTrans.Modification.naturality
#align category_theory.oplax_nat_trans.modification.naturality CategoryTheory.OplaxNatTrans.Modification.naturality

attribute [nolint docBlame] CategoryTheory.OplaxNatTrans.Modification.app
  CategoryTheory.OplaxNatTrans.Modification.naturality

/- Porting note: removed primes from field names and removed `restate_axiom` since that is no longer
  needed in Lean 4 -/

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ ι : F ⟶ G}

namespace Modification

variable (η)

/-- The identity modification. -/
@[simps]
def id : Modification η η where app a := 𝟙 (η.app a)
#align category_theory.oplax_nat_trans.modification.id CategoryTheory.OplaxNatTrans.Modification.id

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

variable {η}

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ θ.naturality g = f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.map g := by
  simp_rw [← whiskerLeft_comp, naturality]
#align category_theory.oplax_nat_trans.modification.whisker_left_naturality CategoryTheory.OplaxNatTrans.Modification.whiskerLeft_naturality

@[reassoc (attr := simp)]
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ θ.naturality f ▷ g =
      (α_ _ _ _).inv ≫ η.naturality f ▷ g ≫ Γ.app a ▷ G.map f ▷ g := by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]
#align category_theory.oplax_nat_trans.modification.whisker_right_naturality CategoryTheory.OplaxNatTrans.Modification.whiskerRight_naturality

end

/-- Vertical composition of modifications. -/
@[simps]
def vcomp (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a
#align category_theory.oplax_nat_trans.modification.vcomp CategoryTheory.OplaxNatTrans.Modification.vcomp

end Modification

/-- Category structure on the oplax natural transformations between OplaxFunctors. -/
@[simps]
instance category (F G : OplaxFunctor B C) : Category (F ⟶ G) where
  Hom := Modification
  id := Modification.id
  comp := Modification.vcomp
#align category_theory.oplax_nat_trans.category CategoryTheory.OplaxNatTrans.category

-- Porting note: duplicating the `ext` lemma.
@[ext]
lemma ext {F G : OplaxFunctor B C} {α β : F ⟶ G} {m n : α ⟶ β} (w : ∀ b, m.app b = n.app b) :
    m = n := by
  apply Modification.ext
  ext
  apply w

@[simp]
lemma Modification.id_app' {X : B} {F G : OplaxFunctor B C} (α : F ⟶ G) :
    Modification.app (𝟙 α) X = 𝟙 (α.app X) := rfl

@[simp]
lemma Modification.comp_app' {X : B} {F G : OplaxFunctor B C} {α β γ : F ⟶ G}
    (m : α ⟶ β) (n : β ⟶ γ) : (m ≫ n).app X = m.app X ≫ n.app X :=
  rfl

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def ModificationIso.ofComponents (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        F.map f ◁ (app b).hom ≫ θ.naturality f = η.naturality f ≫ (app a).hom ▷ G.map f) :
    η ≅ θ where
  hom := { app := fun a => (app a).hom }
  inv :=
    { app := fun a => (app a).inv
      naturality := fun {a b} f => by
        simpa using congr_arg (fun f => _ ◁ (app b).inv ≫ f ≫ (app a).inv ▷ _) (naturality f).symm }
#align category_theory.oplax_nat_trans.modification_iso.of_components CategoryTheory.OplaxNatTrans.ModificationIso.ofComponents

end

end OplaxNatTrans

end CategoryTheory
