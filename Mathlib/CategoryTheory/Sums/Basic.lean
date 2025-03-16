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

The sum of two functors `F : A ⥤ C` and `G : B ⥤ C` is a functor `A ⊕ B ⥤ C`, written `F.sum' G`.
This construction should be preffered when defining functors out of a sum.

We provides natural isomorphisms `inlCompSum' : inl_ ⋙ F.sum' G ≅ F` and
`inrCompSum' : inl_ ⋙ F.sum' G ≅ G`.

Furthermore, we provide `Functor.sumIsoExt`, which
constructs a natural isomorphism of functors out of a sum out of natural isomorphism with
their precomposition with the inclusion. This construction sholud be preffered when trying
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

@[reassoc (attr := simp)]
theorem sum_comp_inl_down {P Q R : C} (f : (inl P : C ⊕ D) ⟶ inl Q) (g : (inl Q : C ⊕ D) ⟶ inl R) :
    (f ≫ g).down = f.down ≫ g.down :=
  rfl

@[reassoc (attr := simp)]
theorem sum_comp_inr_down {P Q R : D} (f : (inr P : C ⊕ D) ⟶ inr Q) (g : (inr Q : C ⊕ D) ⟶ inr R) :
    (f ≫ g).down = f.down ≫ g.down :=
  rfl

@[reassoc (attr := simp)]
theorem sum_comp_inl {P Q R : C} (f : (inl P : C ⊕ D) ⟶ inl Q) (g : (inl Q : C ⊕ D) ⟶ inl R) :
    (f ≫ g) = (ULift.up (f.down ≫ g.down) : inl P ⟶ inl R) :=
  rfl

@[reassoc (attr := simp)]
theorem sum_comp_inr {P Q R : D} (f : (inr P : C ⊕ D) ⟶ inr Q) (g : (inr Q : C ⊕ D) ⟶ inr R) :
    f ≫ g = (ULift.up (f.down ≫ g.down) : inr P ⟶ inr R) :=
  rfl

@[simp]
lemma id_down_left {P : C} : (𝟙 (inl P) : (_ : C ⊕ D) ⟶ _ ).down = 𝟙 P := rfl

@[simp]
lemma id_down_right {P : D} : (𝟙 (inr P) : (_ : C ⊕ D) ⟶ _ ).down = 𝟙 P := rfl

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps! obj]
def inl_ : C ⥤ C ⊕ D where
  obj X := inl X
  map {_ _} f := ULift.up f

@[simp]
lemma inl_map_down {c c' : C} (f : c ⟶ c') : ((inl_ C D).map f).down = f := rfl

@[simp]
lemma inl_map_down' {c c' : C} (f : (inl c : C ⊕ D) ⟶ inl c') : (inl_ C D).map f.down = f := rfl

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps! obj]
def inr_ : D ⥤ C ⊕ D where
  obj X := inr X
  map {_ _} f := ULift.up f

@[simp]
lemma inr_map_down {d d' : D} (f : d ⟶ d') : ((inr_ C D).map f).down = f := rfl

@[simp]
lemma inr_map_down' {d d' : D} (f : (inr d : C ⊕ D) ⟶ inr d') : (inr_ C D).map f.down = f := rfl

end Sum

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

namespace Functor

section Sum'

variable (F : A ⥤ C) (G : B ⥤ C)

/-- The sum of two functors that lands in a given category `C`. -/
def sum' : A ⊕ B ⥤ C where
  obj X :=
    match X with
    | inl X => F.obj X
    | inr X => G.obj X
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => F.map f.down
    | inr _, inr _, f => G.map f.down

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
theorem sum'_map_inl {a a' : A} (f : inl a ⟶ inl a') :
    (F.sum' G).map f = (F.map f.down) :=
  rfl

@[simp]
theorem sum'_map_inr {b b' : B} (f : inr b ⟶ inr b') :
    (F.sum' G).map f = (G.map f.down) :=
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
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : inl a ⟶ inl a') :
    (F.sum G).map f = (Sum.inl_ _ _).map (F.map f.down) :=
  rfl

@[simp]
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : inr c ⟶ inr c') :
    (F.sum G).map f = (Sum.inr_ _ _).map (G.map f.down) :=
  rfl

section

variable {F G: A ⊕ B ⥤ C}
  (e₁ : Sum.inl_ _ _ ⋙ F ≅ Sum.inl_ _ _ ⋙ G)
  (e₂ : Sum.inr_ _ _ ⋙ F ≅ Sum.inr_ _ _ ⋙ G)

/-- A functor out of a sum is uniquely characterized by its precompositions with `inl_` and `inr_`.
-/
def sumIsoExt : F ≅ G :=
  NatIso.ofComponents (fun x ↦
    match x with
    | inl x => e₁.app x
    | inr x => e₂.app x)
    (fun {x y} f ↦
      match x, y, f with
      | inl x, inl y, f => by simpa using e₁.hom.naturality f.down
      | inr x, inr y, f => by simpa using e₂.hom.naturality f.down)

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

variable (F : A ⊕ B ⥤ C) (a : A) (b : B)

/-- Any functor out of a sum is the sum of its precomposition with the inclusions. -/
def isoSum : F ≅ (Sum.inl_ _ _ ⋙ F).sum' (Sum.inr_ _ _ ⋙ F) :=
    sumIsoExt (Iso.refl _) (Iso.refl _)

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

/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I where
  app X :=
    match X with
    | inl X => (Sum.inl_ _ _).map (α.app X)
    | inr X => (Sum.inr_ _ _).map (β.app X)
  naturality X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => by simp [← Functor.map_comp]
    | inr X, inr Y, f => by simp [← Functor.map_comp]

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
def swap : C ⊕ D ⥤ D ⊕ C := (inr_ _ _).sum' (inl_ _ _)

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
@[simps!]
def swapCompInl : inl_ _ _ ⋙ swap C D ≅ inr_ _ _ := (Functor.inlCompSum' (inr_ _ _) (inl_ _ _)).symm

/-- Precomposing `swap` with the rightt inclusion gives the leftt inclusion. -/
@[simps!]
def swapCompInr : inr_ _ _ ⋙ swap C D ≅ inl_ _ _ := (Functor.inrCompSum' (inr_ _ _) (inl_ _ _)).symm

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
