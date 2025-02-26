/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Products.Basic

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/


namespace CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
open Sum

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

/- Porting note: `aesop_cat` not firing on `assoc` where autotac in Lean 3 did -/

/-- `sum C D` gives the direct sum of two categories.
-/
instance sum : Category.{v₁} (C ⊕ D) where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => X ⟶ Y
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => X ⟶ Y
  id X :=
    match X with
    | inl X => 𝟙 X
    | inr X => 𝟙 X
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl _, inl _, inl _, f, g => f ≫ g
    | inr _, inr _, inr _, f, g => f ≫ g
  assoc {W X Y Z} f g h :=
    match X, Y, Z, W with
    | inl _, inl _, inl _, inl _ => Category.assoc f g h
    | inr _, inr _, inr _, inr _ => Category.assoc f g h

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
theorem hom_inl_inr_false {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y) : False := by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
theorem hom_inr_inl_false {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y) : False := by
  cases f

theorem sum_comp_inl {P Q R : C} (f : (inl P : C ⊕ D) ⟶ inl Q) (g : (inl Q : C ⊕ D) ⟶ inl R) :
    @CategoryStruct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
      @CategoryStruct.comp _ _ (inl P) (inl Q) (inl R) (f : P ⟶ Q) (g : Q ⟶ R) :=
  rfl

theorem sum_comp_inr {P Q R : D} (f : (inr P : C ⊕ D) ⟶ inr Q) (g : (inr Q : C ⊕ D) ⟶ inr R) :
    @CategoryStruct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
      @CategoryStruct.comp _ _ (inr P) (inr Q) (inr R) (f : P ⟶ Q) (g : Q ⟶ R) :=
  rfl

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps]
def inl_ : C ⥤ C ⊕ D where
  obj X := inl X
  map {_ _} f := f

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps]
def inr_ : D ⥤ C ⊕ D where
  obj X := inr X
  map {_ _} f := f

/- Porting note: `aesop_cat` not firing on `map_comp` where autotac in Lean 3 did
but `map_id` was ok. -/

/-- The functor exchanging two direct summand categories. -/
def swap : C ⊕ D ⥤ D ⊕ C where
  obj X :=
    match X with
    | inl X => inr X
    | inr X => inl X
  map := @fun X Y f =>
    match X, Y, f with
    | inl _, inl _, f => f
    | inr _, inr _, f => f
  map_comp := fun {X} {Y} {Z} _ _ =>
    match X, Y, Z with
    | inl X, inl Y, inl Z => by rfl
    | inr X, inr Y, inr Z => by rfl

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

namespace Swap

/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
@[simps functor inverse]
def equivalence : C ⊕ D ≌ D ⊕ C where
  functor := swap C D
  inverse := swap D C
  unitIso := NatIso.ofComponents (by rintro (_|_) <;> exact Iso.refl _)
  counitIso := NatIso.ofComponents (by rintro (_|_) <;> exact Iso.refl _)

instance isEquivalence : (swap C D).IsEquivalence :=
  (by infer_instance : (equivalence C D).functor.IsEquivalence)

/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C ⊕ D) :=
  (equivalence C D).unitIso.symm

end Swap

end Sum

variable {A : Type u₁} [Category.{v₁} A] {A' : Type u₁} [Category.{v₁} A']
  {B : Type u₂} [Category.{v₂} B]
  {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- The sum of two functors. -/
def sum (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D where
  obj X :=
    match X with
    | inl X => inl (F.obj X)
    | inr X => inr (G.obj X)
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => F.map f
    | inr _, inr _, f => G.map f
  map_id {X} := by cases X <;> (erw [Functor.map_id]; rfl)
  map_comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g => by erw [F.map_comp]; rfl
    | inr X, inr Y, inr Z, f, g => by erw [G.map_comp]; rfl

/-- Similar to `sum`, but both functors land in the same category `C` -/
def sum' (F : A ⥤ B) (G : A' ⥤ B) : A ⊕ A' ⥤ B where
  obj X :=
    match X with
    | inl X => F.obj X
    | inr X => G.obj X
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => F.map f
    | inr _, inr _, f => G.map f
  map_id {X} := by cases X <;> erw [Functor.map_id]
  map_comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl _, inl _, inl _, f, g => by erw [F.map_comp]
    | inr _, inr _, inr _, f, g => by erw [G.map_comp]

/-- The sum `F.sum' G` precomposed with the left inclusion functor is isomorphic to `F` -/
@[simps!]
def inlCompSum' (F : A ⥤ B) (G : A' ⥤ B) : Sum.inl_ A A' ⋙ F.sum' G ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The sum `F.sum' G` precomposed with the right inclusion functor is isomorphic to `G` -/
@[simps!]
def inrCompSum' (F : A ⥤ B) (G : A' ⥤ B) : Sum.inr_ A A' ⋙ F.sum' G ≅ G :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
theorem sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.sum G).obj (inl a) = inl (F.obj a) :=
  rfl

@[simp]
theorem sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.sum G).obj (inr c) = inr (G.obj c) :=
  rfl

@[simp]
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : inl a ⟶ inl a') :
    (F.sum G).map f = F.map f :=
  rfl

@[simp]
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : inr c ⟶ inr c') :
    (F.sum G).map f = G.map f :=
  rfl

@[simp]
theorem sum'_obj_inl (F : A ⥤ B) (G : A' ⥤ B) (a : A) : (F.sum' G).obj (inl a) = (F.obj a) :=
  rfl

@[simp]
theorem sum'_obj_inr (F : A ⥤ B) (G : A' ⥤ B) (a' : A') : (F.sum' G).obj (inr a') = (G.obj a') :=
  rfl

@[simp]
theorem sum'_map_inl (F : A ⥤ B) (G : A' ⥤ B) {a a' : A} (f : inl a ⟶ inl a') :
    (F.sum' G).map f = F.map f :=
  rfl

@[simp]
theorem sum'_map_inr (F : A ⥤ B) (G : A' ⥤ B) {a a' : A'} (f : inr a ⟶ inr a') :
    (F.sum' G).map f = G.map f :=
  rfl

end Functor

namespace NatTrans

/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => by erw [α.naturality]; rfl
    | inr X, inr Y, f => by erw [β.naturality]; rfl

@[simp]
theorem sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum α β).app (inl a) = α.app a :=
  rfl

@[simp]
theorem sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
    (sum α β).app (inr c) = β.app c :=
  rfl

/-- The sum of two natural transformations, where all functors have the same target category. -/
def sum' {F G : A ⥤ B} {H I : A' ⥤ B} (α : F ⟶ G) (β : H ⟶ I) : F.sum' H ⟶ G.sum' I where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => by change F.map _ ≫ _ = _; rw [α.naturality]; rfl
    | inr X, inr Y, f => by change H.map _ ≫ _ = _; rw [β.naturality]; rfl

@[simp]
theorem sum'_app_inl {F G : A ⥤ B} {H I : A' ⥤ B} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum' α β).app (inl a) = α.app a :=
  rfl

@[simp]
theorem sum'_app_inr {F G : A ⥤ B} {H I : A' ⥤ B} (α : F ⟶ G) (β : H ⟶ I) (a' : A') :
    (sum' α β).app (inr a') = β.app a' :=
  rfl

end NatTrans

namespace Sum

variable (A A') (B)

/-- The equivalence between functors from a sum and the product of the
 functor categories. -/
@[simps! functor_obj functor_map]
def functorEquiv : A ⊕ A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where
  functor :=
    { obj F := ⟨inl_ _ _ ⋙ F , inr_ _ _ ⋙ F⟩
      map η := ⟨whiskerLeft _ η, whiskerLeft _ η⟩ }
  inverse :=
    { obj F := Functor.sum' F.1 F.2
      map η := NatTrans.sum' η.1 η.2
      map_id x := by
        ext x'
        cases x' <;> rfl }
  unitIso :=
    NatIso.ofComponents (fun x ↦
      NatIso.ofComponents (fun t ↦
        match t with
        | inl x => Iso.refl _
        | inr x => Iso.refl _ ))
  counitIso :=
    NatIso.ofComponents <| fun _ ↦
      Iso.prod (NatIso.ofComponents (fun _ ↦ Iso.refl _)) (NatIso.ofComponents (fun _ ↦ Iso.refl _))

-- generated simps lemma for `functorEquiv` include match arms in the statements, so we rather
-- state them separately for the two constructors of `A ⊕ A'`.

variable {A A'} {B}

@[simp]
lemma functorEquiv_inverse_obj_obj_inl (F : (A ⥤ B) × (A' ⥤ B)) (a : A) :
    ((functorEquiv A A' B).inverse.obj F).obj (inl a) = F.1.obj a :=
  rfl

@[simp]
lemma functorEquiv_inverse_obj_obj_inr (F : (A ⥤ B) × (A' ⥤ B)) (a' : A') :
    ((functorEquiv A A' B).inverse.obj F).obj (inr a') = F.2.obj a' :=
  rfl

@[simp]
lemma functorEquiv_inverse_obj_map_inl (F : (A ⥤ B) × (A' ⥤ B)) {a₀ a₁ : A} (f : a₀ ⟶ a₁) :
    ((functorEquiv A A' B).inverse.obj F).map (f : inl _ ⟶ inl _) = F.1.map f :=
  rfl

@[simp]
lemma functorEquiv_inverse_obj_map_inr (F : (A ⥤ B) × (A' ⥤ B)) {a'₀ a'₁ : A'} (f : a'₀ ⟶ a'₁) :
    ((functorEquiv A A' B).inverse.obj F).map (f : inr _ ⟶ inr _) = F.2.map f :=
  rfl

@[simp]
lemma functorEquiv_inverse_map_app_inl {X Y : (A ⥤ B) × (A' ⥤ B)} (η : X ⟶ Y) (a : A) :
    ((functorEquiv A A' B).inverse.map η).app (inl a) = η.1.app a :=
  rfl

@[simp]
lemma functorEquiv_inverse_map_app_inr {X Y : (A ⥤ B) × (A' ⥤ B)} (η : X ⟶ Y) (a' : A') :
    ((functorEquiv A A' B).inverse.map η).app (inr a') = η.2.app a' :=
  rfl

@[simp]
lemma functorEquiv_counitIso_hom_app (X : (A ⥤ B) × (A' ⥤ B)) :
    (functorEquiv A A' B).counitIso.hom.app X = 𝟙 X :=
  rfl

@[simp]
lemma functorEquiv_counit_hom_app (X : (A ⥤ B) × (A' ⥤ B)) :
    (functorEquiv A A' B).counit.app X = 𝟙 X :=
  rfl

@[simp]
lemma functorEquiv_counitIso_inv_app (X : (A ⥤ B) × (A' ⥤ B)) :
    (functorEquiv A A' B).counitIso.inv.app X = 𝟙 X :=
  rfl

@[simp]
lemma functorEquiv_unitIso_inv_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unitIso.inv.app X).app (inl a) = 𝟙 (X.obj (inl a)) :=
  rfl

@[simp]
lemma functorEquiv_unitIso_inv_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unitIso.inv.app X).app (inr a') = 𝟙 (X.obj (inr a')) :=
  rfl

@[simp]
lemma functorEquiv_unitIso_hom_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unitIso.hom.app X).app (inl a) = 𝟙 (X.obj (inl a)) :=
  rfl

@[simp]
lemma functorEquiv_unitIso_hom_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unitIso.hom.app X).app (inr a') = 𝟙 (X.obj (inr a')) :=
  rfl

@[simp]
lemma functorEquiv_unit_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unit.app X).app (inl a) = 𝟙 (X.obj (inl a)) :=
  rfl

@[simp]
lemma functorEquiv_unit_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unit.app X).app (inr a') = 𝟙 (X.obj (inr a')) :=
  rfl

/-- Composing the forward direction of `functorEquiv` with the first projection is the same as
  precomposition with `inl_ A A'`. -/
@[simps!]
def functorEquivFunctorCompFstIso :
    (functorEquiv _ _ _).functor ⋙ Prod.fst _ _ ≅ (whiskeringLeft _ _ C).obj (inl_ A A') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Composing the forward direction of `functorEquiv` with the second projection is the same as
  precomposition with `inr_ A A'`. -/
@[simps!]
def functorEquivFunctorCompSndIso :
    (functorEquiv _ _ _).functor ⋙ Prod.snd _ _ ≅ (whiskeringLeft _ _ C).obj (inr_ A A') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Composing the backward direction of `functorEquiv` with precomposition with `inl_ A A'`.
  is naturally isomorphic to the first projection. -/
@[simps!]
def functorEquivInverseCompWhiskeringLeftInLIso :
    (functorEquiv _ _ _).inverse ⋙ (whiskeringLeft _ _ C).obj (inl_ A A') ≅ Prod.fst _ _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Composing the backward direction of `functorEquiv` with the second projection is the same as
  precomposition with `inr_ A A'`. -/
@[simps!]
def functorEquivInverseCompWhiskeringLeftInRIso :
    (functorEquiv _ _ _).inverse ⋙ (whiskeringLeft _ _ C).obj (inr_ A A') ≅ Prod.snd _ _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- A restatement `functorEquiv` : we can construct a natural transformation of functors
`A ⊕ A' ⥤ B` from the data of natural transformations of their whiskering with `inl_` and `inr_`. -/
@[simps!]
def natTransOfNatTransWhiskerLeftInlInr {F G : A ⊕ A' ⥤ B}
    (η₁ : inl_ _ _ ⋙ F ⟶ inl_ _ _ ⋙ G) (η₂ : inr_ _ _ ⋙ F ⟶ inr_ _ _ ⋙ G) : F ⟶ G :=
  (functorEquiv _ _ _).unit.app _ ≫
    (functorEquiv _ _ _).inverse.map
      (⟨η₁, η₂⟩ : (functorEquiv _ _ _).functor.obj _ ⟶ (functorEquiv _ _ _).functor.obj _) ≫
      (functorEquiv _ _ _).unitInv.app _

@[simp]
lemma natTransOfNatTransWhiskerLeftInlInr_id {F : A ⊕ A' ⥤ B} :
    natTransOfNatTransWhiskerLeftInlInr (𝟙 (inl_ _ _ ⋙ F)) (𝟙 (inr_ _ _ ⋙ F)) = 𝟙 _ := by
  aesop_cat

@[simp]
lemma natTransOfNatTransWhiskerLeftInlInr_comp {F G H : A ⊕ A' ⥤ B}
    (η₁ : inl_ _ _ ⋙ F ⟶ inl_ _ _ ⋙ G) (η₂ : inr_ _ _ ⋙ F ⟶ inr_ _ _ ⋙ G)
    (ν₁ : inl_ _ _ ⋙ G ⟶ inl_ _ _ ⋙ H) (ν₂ : inr_ _ _ ⋙ G ⟶ inr_ _ _ ⋙ H) :
    natTransOfNatTransWhiskerLeftInlInr (η₁ ≫ ν₁) (η₂ ≫ ν₂) =
      natTransOfNatTransWhiskerLeftInlInr η₁ η₂ ≫
        natTransOfNatTransWhiskerLeftInlInr ν₁ ν₂ := by
  aesop_cat

/-- A restatement `functorEquiv` : we can construct a natural isomorphism of functors
`A ⊕ A' ⥤ B` from the data of natural isomorphisms of their whiskering with `inl_` and `inr_`. -/
@[simps!]
def natIsoOfNatIsoWhiskerLeftInlInr {F G : A ⊕ A' ⥤ B}
    (η₁ : inl_ _ _ ⋙ F ≅ inl_ _ _ ⋙ G) (η₂ : inr_ _ _ ⋙ F ≅ inr_ _ _ ⋙ G) : F ≅ G :=
  (functorEquiv _ _ _).unitIso.app _ ≪≫
    (functorEquiv _ _ _).inverse.mapIso (Iso.prod η₁ η₂) ≪≫
      (functorEquiv _ _ _).unitIso.symm.app _

@[simp]
lemma natIsoOfNatIsoWhiskerLeftInlInr_hom {F G : A ⊕ A' ⥤ B}
    (η₁ : inl_ _ _ ⋙ F ≅ inl_ _ _ ⋙ G) (η₂ : inr_ _ _ ⋙ F ≅ inr_ _ _ ⋙ G) :
    (natIsoOfNatIsoWhiskerLeftInlInr η₁ η₂).hom =
      natTransOfNatTransWhiskerLeftInlInr η₁.hom η₂.hom := by
  aesop_cat

@[simp]
lemma natIsoOfNatIsoWhiskerLeftInlInr_inv {F G : A ⊕ A' ⥤ B}
    (η₁ : inl_ _ _ ⋙ F ≅ inl_ _ _ ⋙ G) (η₂ : inr_ _ _ ⋙ F ≅ inr_ _ _ ⋙ G) :
    (natIsoOfNatIsoWhiskerLeftInlInr η₁ η₂).inv =
      natTransOfNatTransWhiskerLeftInlInr η₁.inv η₂.inv := by
  aesop_cat

end Sum

end CategoryTheory
