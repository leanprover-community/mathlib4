/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
import Mathlib.CategoryTheory.Equivalence

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We provide an induction principle `Sum.homInduction` to reason and work with morphisms in this
category.

The sum of two functors `F : A ⥤ C` and `G : B ⥤ C` is a functor `A ⊕ B ⥤ C`, written `F.sum' G`.
This construction should be preferred when defining functors out of a sum.

We provide natural isomorphisms `inlCompSum' : inl_ ⋙ F.sum' G ≅ F` and
`inrCompSum' : inl_ ⋙ F.sum' G ≅ G`.

Furthermore, we provide `Functor.sumIsoExt`, which
constructs a natural isomorphism of functors out of a sum out of natural isomorphism with
their precomposition with the inclusion. This construction sholud be preferred when trying
to construct isomorphisms between functors out of a sum.

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [category_theory universes].
open Sum

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/- Porting note: `aesop_cat` not firing on `assoc` where autotac in Lean 3 did -/

/-- `sum C D` gives the direct sum of two categories.
-/
instance sum : Category.{max v₁ v₂} (C ⊕ D) where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => ULift.{max v₁ v₂} (X ⟶ Y)
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => ULift.{max v₁ v₂} (X ⟶ Y)
  id X :=
    match X with
    | inl X => ULift.up (𝟙 X)
    | inr X => ULift.up (𝟙 X)
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl _, inl _, inl _, f, g => ULift.up <|f.down ≫ g.down
    | inr _, inr _, inr _, f, g => ULift.up <| f.down ≫ g.down
  assoc {W X Y Z} f g h :=
    match X, Y, Z, W with
    | inl _, inl _, inl _, inl _ => by simp
    | inr _, inr _, inr _, inr _ => by simp

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
theorem hom_inl_inr_false {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y) : False := by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
theorem hom_inr_inl_false {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y) : False := by
  cases f

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps! obj]
def inl_ : C ⥤ C ⊕ D where
  obj X := inl X
  map f := ULift.up f

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps! obj]
def inr_ : D ⥤ C ⊕ D where
  obj X := inr X
  map f := ULift.up f

variable {C D}

/-- An induction principle for morphisms in a sum of category: a morphism is either of the form
`(inl_ _ _).map _` or of the form `(inr_ _ _).map _)`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def homInduction {P : {x y : C ⊕ D} → (x ⟶ y) → Sort*}
    (inl : ∀ x y : C, (f : x ⟶ y) → P ((inl_ C D).map f))
    (inr : ∀ x y : D, (f : x ⟶ y) → P ((inr_ C D).map f))
    {x y : C ⊕ D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .inl x, .inl y, f => inl x y f.down
  | .inr x, .inr y, f => inr x y f.down

@[simp]
lemma homInduction_left {P : {x y : C ⊕ D} → (x ⟶ y) → Sort*}
    (inl : ∀ x y : C, (f : x ⟶ y) → P ((inl_ C D).map f))
    (inr : ∀ x y : D, (f : x ⟶ y) → P ((inr_ C D).map f))
    {x y : C} (f : x ⟶ y) : homInduction inl inr ((inl_ C D).map f) = inl x y f :=
  rfl

@[simp]
lemma homInduction_right {P : {x y : C ⊕ D} → (x ⟶ y) → Sort*}
    (inl : ∀ x y : C, (f : x ⟶ y) → P ((inl_ C D).map f))
    (inr : ∀ x y : D, (f : x ⟶ y) → P ((inr_ C D).map f))
    {x y : D} (f : x ⟶ y) : homInduction inl inr ((inr_ C D).map f) = inr x y f :=
  rfl

end Sum

namespace Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

section Sum'

variable (F : A ⥤ C) (G : B ⥤ C)

/-- The sum of two functors that land in a given category `C`. -/
def sum' : A ⊕ B ⥤ C where
  obj
  | inl X => F.obj X
  | inr X => G.obj X
  map {X Y} f := Sum.homInduction (inl := fun _ _ f ↦ F.map f) (inr := fun _ _ g ↦ G.map g) f
  map_comp {x y z} f g := by
    cases f <;> cases g <;> simp [← Functor.map_comp]
  map_id x := by
    cases x <;> (simp only [← map_id]; rfl)

/-- The sum `F.sum' G` precomposed with the left inclusion functor is isomorphic to `F` -/
@[simps!]
def inlCompSum' : Sum.inl_ A B ⋙ F.sum' G ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The sum `F.sum' G` precomposed with the right inclusion functor is isomorphic to `G` -/
@[simps!]
def inrCompSum' : Sum.inr_ A B ⋙ F.sum' G ≅ G :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
theorem sum'_obj_inl (a : A) : (F.sum' G).obj (inl a) = (F.obj a) :=
  rfl

@[simp]
theorem sum'_obj_inr (b : B) : (F.sum' G).obj (inr b) = (G.obj b) :=
  rfl

@[simp]
theorem sum'_map_inl {a a' : A} (f : a ⟶ a') :
    (F.sum' G).map ((Sum.inl_ _ _).map f) = F.map f :=
  rfl

@[simp]
theorem sum'_map_inr {b b' : B} (f : b ⟶ b') :
    (F.sum' G).map ((Sum.inr_ _ _).map f) = G.map f :=
  rfl

end Sum'

/-- The sum of two functors. -/
def sum (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D := (F ⋙ Sum.inl_ _ _).sum' (G ⋙ Sum.inr_ _ _)

@[simp]
theorem sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.sum G).obj (inl a) = inl (F.obj a) :=
  rfl

@[simp]
theorem sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.sum G).obj (inr c) = inr (G.obj c) :=
  rfl

@[simp]
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : a ⟶ a') :
    (F.sum G).map ((Sum.inl_ _ _).map f) = (Sum.inl_ _ _).map (F.map f) :=
  rfl

@[simp]
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : c ⟶ c') :
    (F.sum G).map ((Sum.inr_ _ _).map f) = (Sum.inr_ _ _).map (G.map f) :=
  rfl

section

variable {F G : A ⊕ B ⥤ C}
  (e₁ : Sum.inl_ A B ⋙ F ≅ Sum.inl_ A B ⋙ G)
  (e₂ : Sum.inr_ A B ⋙ F ≅ Sum.inr_ A B ⋙ G)

/-- A functor out of a sum is uniquely characterized by its precompositions with `inl_` and `inr_`.
-/
def sumIsoExt : F ≅ G :=
  NatIso.ofComponents (fun x ↦
    match x with
    | inl x => e₁.app x
    | inr x => e₂.app x)
    (fun {x y} f ↦ by
      cases f
      · simpa using e₁.hom.naturality _
      · simpa using e₂.hom.naturality _)

@[simp]
lemma sumIsoExt_hom_app_inl (a : A) : (sumIsoExt e₁ e₂).hom.app (inl a) = e₁.hom.app a := rfl

@[simp]
lemma sumIsoExt_hom_app_inr (b : B) : (sumIsoExt e₁ e₂).hom.app (inr b) = e₂.hom.app b := rfl

@[simp]
lemma sumIsoExt_inv_app_inl (a : A) : (sumIsoExt e₁ e₂).inv.app (inl a) = e₁.inv.app a := rfl

@[simp]
lemma sumIsoExt_inv_app_inr (b : B) : (sumIsoExt e₁ e₂).inv.app (inr b) = e₂.inv.app b := rfl

end

section

variable (F : A ⊕ B ⥤ C)

/-- Any functor out of a sum is the sum of its precomposition with the inclusions. -/
def isoSum : F ≅ (Sum.inl_ A B ⋙ F).sum' (Sum.inr_ A B ⋙ F) :=
  sumIsoExt (Iso.refl _) (Iso.refl _)

variable (a : A) (b : B)

@[simp]
lemma isoSum_hom_app_inl : (isoSum F).hom.app (inl a) = 𝟙 (F.obj (inl a)) := rfl

@[simp]
lemma isoSum_hom_app_inr : (isoSum F).hom.app (inr b) = 𝟙 (F.obj (inr b)) := rfl

@[simp]
lemma isoSum_inv_app_inl : (isoSum F).inv.app (inl a) = 𝟙 (F.obj (inl a)) := rfl

@[simp]
lemma isoSum_inv_app_inr : (isoSum F).inv.app (inr b) = 𝟙 (F.obj (inr b)) := rfl

end

end Functor

namespace NatTrans

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- The sum of two natural transformations, where all functors have the same target category. -/
def sum' {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) : F.sum' H ⟶ G.sum' I where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f := by
    cases f <;> simp

@[simp]
theorem sum'_app_inl {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum' α β).app (inl a) = α.app a :=
  rfl

@[simp]
theorem sum'_app_inr {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (b : B) :
    (sum' α β).app (inr b) = β.app b :=
  rfl

/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I where
  app X :=
    match X with
    | inl X => (Sum.inl_ B D).map (α.app X)
    | inr X => (Sum.inr_ B D).map (β.app X)
  naturality X Y f := by
    cases f <;> simp [← Functor.map_comp]

@[simp]
theorem sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum α β).app (inl a) = (Sum.inl_ _ _).map (α.app a) :=
  rfl

@[simp]
theorem sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
    (sum α β).app (inr c) = (Sum.inr_ _ _).map (β.app c) :=
  rfl

end NatTrans

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The functor exchanging two direct summand categories. -/
def swap : C ⊕ D ⥤ D ⊕ C := (inr_ D C).sum' (inl_ D C)

@[simp]
theorem swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X :=
  rfl

@[simp]
theorem swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X :=
  rfl

@[simp]
theorem swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f :=
  rfl

@[simp]
theorem swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f :=
  rfl

/-- Precomposing `swap` with the left inclusion gives the right inclusion. -/
@[simps! hom_app inv_app]
def swapCompInl : inl_ C D ⋙ swap C D ≅ inr_ D C := (Functor.inlCompSum' (inr_ _ _) (inl_ _ _)).symm

/-- Precomposing `swap` with the right inclusion gives the leftt inclusion. -/
@[simps! hom_app inv_app]
def swapCompInr : inr_ C D ⋙ swap C D ≅ inl_ D C := (Functor.inrCompSum' (inr_ _ _) (inl_ _ _)).symm

namespace Swap

/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
@[simps functor inverse]
def equivalence : C ⊕ D ≌ D ⊕ C where
  functor := swap C D
  inverse := swap D C
  unitIso := Functor.sumIsoExt (swapCompInr D C).symm (swapCompInl D C).symm
  counitIso := Functor.sumIsoExt (swapCompInr C D).symm (swapCompInl C D).symm

instance isEquivalence : (swap C D).IsEquivalence :=
  (by infer_instance : (equivalence C D).functor.IsEquivalence)

/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C ⊕ D) :=
  (equivalence C D).unitIso.symm

end Swap

end Sum

end CategoryTheory
