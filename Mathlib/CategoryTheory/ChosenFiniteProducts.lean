/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric

/-!
# Categories with chosen finite products

We introduce a class, `ChosenFiniteProducts`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

Given a category with such an instance, we also provide the associated
symmetric monoidal structure so that one can write `X ⊗ Y` for the explicit
binary product and `𝟙_ C` for the explicit terminal object.

# Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the tensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

/--
An instance of `ChosenFiniteProducts C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
class ChosenFiniteProducts (C : Type u) [Category.{v} C] where
  /-- A choice of a limit binary fan for any two objects of the category. -/
  product : (X Y : C) → Limits.LimitCone (Limits.pair X Y)
  /-- A choice of a terminal object. -/
  terminal : Limits.LimitCone (Functor.empty.{0} C)

/--
An instance of `ChosenFiniteCoproducts C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊕ₒ Y` for the product and `𝟘_ C` for
the initial object.
-/
class ChosenFiniteCoproducts (C : Type u) [Category.{v} C] where
  /-- A choice of a colimit binary cofan for any two objects of the category. -/
  coproduct : (X Y : C) → Limits.ColimitCocone (Limits.pair X Y)
  /-- A choice of an initial object. -/
  initial : Limits.ColimitCocone (Functor.empty.{0} C)

namespace ChosenFiniteProducts

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    MonoidalCategory C :=
  monoidalOfChosenFiniteProducts terminal product

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    SymmetricCategory C :=
  symmetricOfChosenFiniteProducts _ _

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

open MonoidalCategory

theorem braiding_eq_braiding (X Y : C) :
  (β_ X Y) = Limits.BinaryFan.braiding (product X Y).isLimit (product Y X).isLimit := rfl

/--
The unique map to the terminal object.
-/
def toUnit (X : C) : X ⟶ 𝟙_ C :=
  terminal.isLimit.lift <| .mk _ <| .mk (fun x => x.as.elim) fun x => x.as.elim

instance (X : C) : Unique (X ⟶ 𝟙_ C) where
  default := toUnit _
  uniq _ := terminal.isLimit.hom_ext fun ⟨j⟩ => j.elim

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
lemma toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g :=
  Subsingleton.elim _ _

@[reassoc (attr := simp)]
theorem comp_toUnit {X Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  toUnit_unique _ _

/--
Construct a morphism to the product given its two components.
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊗ Y :=
  (product X Y).isLimit.lift <| Limits.BinaryFan.mk f g

/--
The first projection from the product.
-/
def fst (X Y : C) : X ⊗ Y ⟶ X :=
  letI F : Limits.BinaryFan X Y := (product X Y).cone
  F.fst

/--
The second projection from the product.
-/
def snd (X Y : C) : X ⊗ Y ⟶ Y :=
  letI F : Limits.BinaryFan X Y := (product X Y).cone
  F.snd

@[reassoc (attr := simp)]
lemma lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f := by
  simp [lift, fst]

@[reassoc (attr := simp)]
lemma lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g := by
  simp [lift, snd]

instance mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_fst _ _

instance mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_snd _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : T ⟶ X ⊗ Y)
    (h_fst : f ≫ fst _ _ = g ≫ fst _ _)
    (h_snd : f ≫ snd _ _ = g ≫ snd _ _) :
    f = g :=
  (product X Y).isLimit.hom_ext fun ⟨j⟩ => j.recOn h_fst h_snd

-- Similarly to `CategoryTheory.Limits.prod.comp_lift`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
lemma comp_lift {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[simp]
lemma lift_fst_snd {X Y : C} : lift (fst X Y) (snd X Y) = 𝟙 (X ⊗ Y) := by ext <;> simp

@[simp]
lemma lift_comp_fst_snd {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    lift (f ≫ fst _ _) (f ≫ snd _ _) = f := by
  aesop_cat

@[reassoc (attr := simp)]
lemma tensorHom_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ g) ≫ fst _ _ = fst _ _ ≫ f := lift_fst _ _

@[reassoc (attr := simp)]
lemma tensorHom_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ g) ≫ snd _ _ = snd _ _ ≫ g := lift_snd _ _

@[reassoc]
lemma lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    lift f g ≫ (h ⊗ k) = lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[deprecated lift_map (since := "2025-03-04"), reassoc (attr := simp)]
lemma lift_tensorHom {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    lift f g ≫ (h ⊗ k) = lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
lemma lift_fst_comp_snd_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (fst _ _ ≫ g) (snd _ _ ≫ g') = g ⊗ g' := by ext <;> simp

@[reassoc (attr := simp)]
lemma whiskerLeft_fst (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (X ◁ g) ≫ fst _ _ = fst _ _ :=
  (tensorHom_fst _ _).trans (by simp)

@[reassoc (attr := simp)]
lemma whiskerLeft_snd (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (X ◁ g) ≫ snd _ _ = snd _ _ ≫ g :=
  tensorHom_snd _ _

@[reassoc (attr := simp)]
lemma whiskerRight_fst {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (f ▷ Y) ≫ fst _ _ = fst _ _ ≫ f :=
  tensorHom_fst _ _

@[reassoc (attr := simp)]
lemma whiskerRight_snd {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (f ▷ Y) ≫ snd _ _ = snd _ _ :=
  (tensorHom_snd _ _).trans (by simp)

@[reassoc (attr := simp)]
lemma lift_whiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) :
    lift f g ≫ (h ▷ Z) = lift (f ≫ h) g := by
  aesop_cat

@[reassoc (attr := simp)]
lemma lift_whiskerLeft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) :
    lift f g ≫ (Y ◁ h) = lift f (g ≫ h) := by
  aesop_cat

@[reassoc (attr := simp)]
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _ := lift_fst _ _

@[reassoc (attr := simp)]
lemma associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd _ _  := by
  erw [lift_snd_assoc]
  erw [lift_fst]
  rfl

@[reassoc (attr := simp)]
lemma associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _  := by
  erw [lift_snd_assoc]
  erw [lift_snd]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  erw [lift_fst_assoc]
  erw [lift_fst]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst _ _ := by
  erw [lift_fst_assoc]
  erw [lift_snd]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _ := lift_snd _ _

@[reassoc (attr := simp)]
lemma lift_lift_associator_hom {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift (lift f g) h ≫ (α_ Y Z W).hom = lift f (lift g h) := by
  aesop_cat

@[reassoc (attr := simp)]
lemma lift_lift_associator_inv {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift f (lift g h) ≫ (α_ Y Z W).inv = lift (lift f g) h := by
  aesop_cat

@[reassoc (attr := simp)]
lemma leftUnitor_inv_fst (X : C) :
    (λ_ X).inv ≫ fst _ _ = toUnit _ := toUnit_unique _ _

@[reassoc (attr := simp)]
lemma leftUnitor_inv_snd (X : C) :
    (λ_ X).inv ≫ snd _ _ = 𝟙 X := lift_snd _ _

@[reassoc (attr := simp)]
lemma rightUnitor_inv_fst (X : C) :
    (ρ_ X).inv ≫ fst _ _ = 𝟙 X := lift_fst _ _

@[reassoc (attr := simp)]
lemma rightUnitor_inv_snd (X : C) :
    (ρ_ X).inv ≫ snd _ _ = toUnit _ := toUnit_unique _ _

@[reassoc (attr := simp)]
lemma lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) :
    lift f g ≫ (λ_ Y).hom = g := by
  rw [← Iso.eq_comp_inv]
  aesop_cat

@[reassoc (attr := simp)]
lemma lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) :
    lift f g ≫ (ρ_ Y).hom = f := by
  rw [← Iso.eq_comp_inv]
  aesop_cat

@[reassoc (attr := simp)]
theorem braiding_hom_fst {X Y : C} : (β_ X Y).hom ≫ fst _ _ = snd _ _ := by
  simp [braiding_eq_braiding, fst, snd]

@[reassoc (attr := simp)]
theorem braiding_hom_snd {X Y : C} : (β_ X Y).hom ≫ snd _ _ = fst _ _ := by
  simp [braiding_eq_braiding, fst, snd]

@[reassoc (attr := simp)]
theorem braiding_inv_fst {X Y : C} : (β_ X Y).inv ≫ fst _ _ = snd _ _ := by
  simp [braiding_eq_braiding, fst, snd]

@[reassoc (attr := simp)]
theorem braiding_inv_snd {X Y : C} : (β_ X Y).inv ≫ snd _ _ = fst _ _ := by
  simp [braiding_eq_braiding, fst, snd]

theorem lift_snd_fst {X Y : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom := rfl

@[simp, reassoc]
lemma lift_snd_comp_fst_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (snd _ _ ≫ g') (fst _ _ ≫ g) = (β_ _ _).hom ≫ (g' ⊗ g) := by ext <;> simp

@[reassoc (attr := simp)]
lemma lift_braiding_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ X Y).hom = lift g f := by aesop

@[reassoc (attr := simp)]
lemma lift_braiding_inv {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ Y X).inv = lift g f := by aesop

/--
Construct an instance of `ChosenFiniteProducts C` given an instance of `HasFiniteProducts C`.
-/
noncomputable
def ofFiniteProducts
    (C : Type u) [Category.{v} C] [Limits.HasFiniteProducts C] :
    ChosenFiniteProducts C where
  product X Y := Limits.getLimitCone (Limits.pair X Y)
  terminal := Limits.getLimitCone (Functor.empty C)

instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : ∀ (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk <| ChosenFiniteProducts.product _ _
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ C)
  hasFiniteProducts_of_has_binary_and_terminal

section ChosenFiniteProductsComparison

variable {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D] (F : C ⥤ D)

section terminalComparison

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`terminalComparison F` is the unique map `F (𝟙_ C) ⟶ 𝟙_ D`. -/
abbrev terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D := toUnit _

@[reassoc]
lemma map_toUnit_comp_terminalCompariso (A : C) :
    F.map (toUnit A) ≫ terminalComparison F = toUnit _ := toUnit_unique _ _

open Limits

/-- If `terminalComparison F` is an Iso, then `F` preserves terminal objects. -/
lemma preservesLimit_empty_of_isIso_terminalComparison [IsIso (terminalComparison F)] :
    PreservesLimit (Functor.empty.{0} C) F := by
  apply preservesLimit_of_preserves_limit_cone terminal.isLimit
  apply isLimitChangeEmptyCone D terminal.isLimit
  exact asIso (terminalComparison F)|>.symm

/-- If `F` preserves terminal objects, then `terminalComparison F` is an isomorphism. -/
noncomputable def preservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] :
    F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (isLimitChangeEmptyCone D (isLimitOfPreserves _ terminal.isLimit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso terminal.isLimit

@[simp]
lemma preservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] :
    (preservesTerminalIso F).hom = terminalComparison F := toUnit_unique _ _

instance terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty.{0} C) F] :
    IsIso (terminalComparison F) := by
  rw [← preservesTerminalIso_hom]
  infer_instance

end terminalComparison

section prodComparison

variable (A B : C)

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`prodComparison F A B` is the canonical comparison morphism from `F (A ⊗ B)` to `F(A) ⊗ F(B)`. -/
def prodComparison (A B : C) : F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B :=
  lift (F.map (fst A B)) (F.map (snd A B))

@[reassoc (attr := simp)]
theorem prodComparison_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B) :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem prodComparison_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B) :=
  lift_snd _ _

@[reassoc (attr := simp)]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (fst _ _) = fst _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (snd _ _) = snd _ _ := by simp [IsIso.inv_comp_eq]

variable {A B} {A' B' : C}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (f ⊗ g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ (F.map f ⊗ F.map g) := by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_fst, tensorHom_fst, prodComparison_fst_assoc,
    prodComparison_snd, tensorHom_snd, prodComparison_snd_assoc, ← F.map_comp]

/-- Naturality of the `prodComparison` morphism in the right argument. -/
@[reassoc]
theorem prodComparison_natural_whiskerLeft (g : B ⟶ B') :
    F.map (A ◁ g) ≫ prodComparison F A B' =
      prodComparison F A B ≫ (F.obj A ◁ F.map g) := by
  rw [← id_tensorHom, prodComparison_natural, Functor.map_id]
  rfl

/-- Naturality of the `prodComparison` morphism in the left argument. -/
@[reassoc]
theorem prodComparison_natural_whiskerRight (f : A ⟶ A') :
    F.map (f ▷ B) ≫ prodComparison F A' B =
      prodComparison F A B ≫ (F.map f ▷ F.obj B) := by
  rw [← tensorHom_id, prodComparison_natural, Functor.map_id]
  rfl

section
variable [IsIso (prodComparison F A B)]

/-- If the product comparison morphism is an iso, its inverse is natural in both arguments. -/
@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (f ⊗ g) =
      (F.map f ⊗ F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

/-- If the product comparison morphism is an iso, its inverse is natural in the right argument. -/
@[reassoc]
theorem prodComparison_inv_natural_whiskerLeft (g : B ⟶ B') [IsIso (prodComparison F A B')] :
    inv (prodComparison F A B) ≫ F.map (A ◁ g) =
      (F.obj A ◁ F.map g) ≫ inv (prodComparison F A B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerLeft]

/-- If the product comparison morphism is an iso, its inverse is natural in the left argument. -/
@[reassoc]
theorem prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodComparison F A' B)] :
    inv (prodComparison F A B) ≫ F.map (f ▷ B) =
      (F.map f ▷ F.obj B) ≫ inv (prodComparison F A' B) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerRight]

end

theorem prodComparison_comp {E : Type u₂} [Category.{v₂} E] [ChosenFiniteProducts E] (G : D ⥤ E) :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]
lemma prodComparison_id :
    prodComparison (𝟭 C) A B = 𝟙 (A ⊗ B) := lift_fst_snd

/-- The product comparison morphism from `F(A ⊗ -)` to `FA ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonNatTrans (A : C) :
    (curriedTensor C).obj A ⋙ F ⟶ F ⋙ (curriedTensor D).obj (F.obj A) where
  app B := prodComparison F A B
  naturality x y f := by
    apply hom_ext <;>
    simp only [Functor.comp_obj, curriedTensor_obj_obj,
      Functor.comp_map, curriedTensor_obj_map, Category.assoc, prodComparison_fst, whiskerLeft_fst,
      prodComparison_snd, prodComparison_snd_assoc, whiskerLeft_snd, ← F.map_comp]

theorem prodComparisonNatTrans_comp {E : Type u₂} [Category.{v₂} E] [ChosenFiniteProducts E]
    (G : D ⥤ E) : prodComparisonNatTrans (F ⋙ G) A =
      whiskerRight (prodComparisonNatTrans F A) G ≫
        whiskerLeft F (prodComparisonNatTrans G (F.obj A)) := by ext; simp [prodComparison_comp]

@[simp]
lemma prodComparisonNatTrans_id :
    prodComparisonNatTrans (𝟭 C) A = 𝟙 _ := by ext; simp

/-- The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonBifunctorNatTrans :
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj F ⟶
      F ⋙ curriedTensor D ⋙ (whiskeringLeft _ _ _).obj F where
  app A := prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;> simp [← Functor.map_comp]

variable {E : Type u₂} [Category.{v₂} E]
    [ChosenFiniteProducts E] (G : D ⥤ E)

theorem prodComparisonBifunctorNatTrans_comp {E : Type u₂} [Category.{v₂} E]
    [ChosenFiniteProducts E] (G : D ⥤ E) : prodComparisonBifunctorNatTrans (F ⋙ G) =
      whiskerRight (prodComparisonBifunctorNatTrans F) ((whiskeringRight _ _ _).obj G) ≫
        whiskerLeft F (whiskerRight (prodComparisonBifunctorNatTrans G)
          ((whiskeringLeft _ _ _).obj F)) := by ext; simp [prodComparison_comp]

instance (A : C) [∀ B, IsIso (prodComparison F A B)] : IsIso (prodComparisonNatTrans F A) := by
  letI : ∀ X, IsIso ((prodComparisonNatTrans F A).app X) := by assumption
  apply NatIso.isIso_of_isIso_app

instance [∀ A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctorNatTrans F) := by
  letI : ∀ X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ ↦ by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

open Limits
section PreservesLimitPairs

section
variable (A B)
variable [PreservesLimit (pair A B) F]

/-- If `F` preserves the limit of the pair `(A, B)`, then the binary fan given by
`(F.map fst A B, F.map (snd A B))` is a limit cone. -/
noncomputable def isLimitChosenFiniteProductsOfPreservesLimits :
    IsLimit <| BinaryFan.mk (F.map (fst A B)) (F.map (snd A B)) :=
  mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _) <|
    (product A B).isLimit.ofIsoLimit <| isoBinaryFanMk (product A B).cone

/-- If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is an isomorphism.
-/
noncomputable def prodComparisonIso : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitChosenFiniteProductsOfPreservesLimits F A B)
    (product _ _).isLimit

@[simp]
lemma prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B := by
  rfl

instance isIso_prodComparison_of_preservesLimit_pair : IsIso (prodComparison F A B) := by
  rw [← prodComparisonIso_hom]
  infer_instance

end

/-- The natural isomorphism `F(A ⊗ -) ≅ FA ⊗ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes). -/
@[simps! hom inv]
noncomputable def prodComparisonNatIso (A : C) [∀ B, PreservesLimit (pair A B) F] :
    (curriedTensor C).obj A ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj A) :=
  asIso (prodComparisonNatTrans F A)

/-- The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism. -/
@[simps! hom inv]
noncomputable def prodComparisonBifunctorNatIso [∀ A B, PreservesLimit (pair A B) F] :
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj F ≅
      F ⋙ curriedTensor D ⋙ (whiskeringLeft _ _ _).obj F :=
  asIso (prodComparisonBifunctorNatTrans F)

end PreservesLimitPairs

section ProdComparisonIso

/-- If `prodComparison F A B` is an isomorphism, then `F` preserves the limit of `pair A B`. -/
lemma preservesLimit_pair_of_isIso_prodComparison (A B : C)
    [IsIso (prodComparison F A B)] :
    PreservesLimit (pair A B) F := by
 apply preservesLimit_of_preserves_limit_cone (product A B).isLimit
 refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((product (F.obj A) (F.obj B)).cone.extend (prodComparison F A B))
      (BinaryFan.ext (by exact Iso.refl _) ?_ ?_) |>.invFun
      (IsLimit.extendIso _ (product (F.obj A) (F.obj B)).isLimit)
 · dsimp only [BinaryFan.fst]
   simp [pairComp, prodComparison, lift, fst]
 · dsimp only [BinaryFan.snd]
   simp [pairComp, prodComparison, lift, snd]

/-- If `prodComparison F A B` is an isomorphism for all `A B` then `F` preserves limits of shape
`Discrete (WalkingPair)`. -/
lemma preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    [∀ A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

end ProdComparisonIso

end prodComparison

end ChosenFiniteProductsComparison

end ChosenFiniteProducts

namespace ChosenFiniteCoproducts

/-- The chosen initial object -/
abbrev initialObj (C : Type u) [Category.{v} C] [ChosenFiniteCoproducts C] : C := initial.cocone.pt

-- TODO: if `AddMonoidalCategory` is added, switch to use notation from there, analogously to how
-- `ChosenFiniteProducts` uses notation from `MonoidalCategory`

/-- Notation for the chosen initial object -/
scoped notation "𝟘_" => initialObj

variable {C : Type u} [Category.{v} C] [ChosenFiniteCoproducts C]

/-- The chosen coproduct of two objects -/
abbrev coprodObj (X Y : C) : C := (coproduct X Y).cocone.pt

/-- Notation for the chosen coproduct of two objects -/
scoped infixr:70 " ⊕ₒ " => coprodObj

/--
The unique map from the initial object.
-/
def fromZero (X : C) : 𝟘_ C ⟶ X :=
  initial.isColimit.desc <| .mk _ <| .mk (fun x => x.as.elim) fun x => x.as.elim

instance (X : C) : Unique (𝟘_ C ⟶ X) where
  default := fromZero _
  uniq _ := initial.isColimit.hom_ext fun ⟨j⟩ => j.elim

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply fromZero_unique` forcing
lean to do the necessary elaboration.
-/
lemma fromZero_unique {X : C} (f g : 𝟘_ _ ⟶ X) : f = g :=
  Subsingleton.elim _ _

/--
Construct a morphism from the coproduct given its two components.
-/
def desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : X ⊕ₒ Y ⟶ T :=
  (coproduct X Y).isColimit.desc <| Limits.BinaryCofan.mk f g

/--
The first injection into the coproduct
-/
def inl (X Y : C) : X ⟶ X ⊕ₒ Y :=
  letI F : Limits.BinaryCofan X Y := (coproduct X Y).cocone
  F.inl

/--
The second injection into the coproduct
-/
def inr (X Y : C) : Y ⟶ X ⊕ₒ Y :=
  letI F : Limits.BinaryCofan X Y := (coproduct X Y).cocone
  F.inr

@[reassoc (attr := simp)]
lemma inl_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inl X Y ≫ desc f g = f := by
  simp [inl, desc]

@[simp, reassoc]
lemma inr_desc {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T) : inr X Y ≫ desc f g = g := by
  simp [inr, desc]

instance epi_desc_of_epi_left {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T)
    [Epi f] : Epi (desc f g) :=
  epi_of_epi_fac <| inl_desc _ _

instance epi_desc_of_epi_right {T X Y : C} (f : X ⟶ T) (g : Y ⟶ T)
    [Epi g] : Epi (desc f g) :=
  epi_of_epi_fac <| inr_desc _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : X ⊕ₒ Y ⟶ T)
    (h_inl : inl X Y ≫ f = inl X Y ≫ g)
    (h_inr : inr X Y ≫ f = inr X Y ≫ g) :
    f = g :=
  (coproduct X Y).isColimit.hom_ext fun ⟨j⟩ => j.recOn h_inl h_inr

-- Similarly to `CategoryTheory.Limits.coprod.desc_comp`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
lemma desc_comp {V W X Y : C} (f : V ⟶ W) (g : X ⟶ V) (h : Y ⟶ V) :
    desc g h ≫ f = desc (g ≫ f) (h ≫ f) := by ext <;> simp [inl_desc_assoc, inr_desc_assoc]

@[simp]
lemma desc_inl_inr {X Y : C} : desc (inl X Y) (inr X Y) = 𝟙 (X ⊕ₒ Y) := by ext <;> simp

@[simp]
lemma desc_inl_comp_inr_comp {X Y Z : C} (f : Y ⊕ₒ Z ⟶ X) :
    desc (inl Y Z ≫ f) (inr Y Z ≫ f) = f := by ext <;> simp

-- TODO: if `AddMonoidalCategory` is added, switch to using `addHom` from there, analogously to how
-- `ChosenFiniteProducts` uses `tensorHom` from `MonoidalCategory`

/-- The coproduct of two morphisms -/
def addHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : X ⊕ₒ X' ⟶ Y ⊕ₒ Y' :=
  desc (f ≫ inl Y Y') (g ≫ inr Y Y')

/-- Notation for the chosen coproduct of two morphisms -/
scoped infixr:70 " ⊕ₕ " => addHom

@[reassoc]
lemma inl_addHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    inl X X' ≫ (f ⊕ₕ g) = f ≫ inl Y Y' := by simp [addHom]

@[reassoc]
lemma inr_addHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    inr X X' ≫ (f ⊕ₕ g) = g ≫ inr Y Y' := by simp [addHom]

@[reassoc]
lemma addHom_desc {S T U V W : C} (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    (h ⊕ₕ k) ≫ desc f g = desc (h ≫ f) (k ≫ g) := by simp [addHom]

@[simp]
lemma desc_comp_inl_inr {W X Y Z : C} (g : X ⟶ W) (g' : Z ⟶ Y) :
    desc (g ≫ inl _ _) (g' ≫ inr _ _) = g ⊕ₕ g' := rfl

/--
Construct an instance of `ChosenFiniteCoproducts C` given an instance of `HasFiniteCoproducts C`.
-/
noncomputable
def ofFiniteCoproducts
    (C : Type u) [Category.{v} C] [Limits.HasFiniteCoproducts C] :
    ChosenFiniteCoproducts C where
  coproduct X Y := Limits.getColimitCocone (Limits.pair X Y)
  initial := Limits.getColimitCocone (Functor.empty C)

instance (priority := 100) : Limits.HasFiniteCoproducts C :=
  letI : ∀ (X Y : C), Limits.HasColimit (Limits.pair X Y) := fun _ _ =>
    .mk <| ChosenFiniteCoproducts.coproduct _ _
  letI : Limits.HasBinaryCoproducts C := Limits.hasBinaryCoproducts_of_hasColimit_pair _
  letI : Limits.HasInitial C := Limits.hasInitial_of_unique (𝟘_ C)
  hasFiniteCoproducts_of_has_binary_and_initial

section ChosenFiniteCoproductsComparison

variable {D : Type u₁} [Category.{v₁} D] [ChosenFiniteCoproducts D] (F : C ⥤ D)

section initialComparison

/-- When `C` and `D` have chosen finite coproducts and `F : C ⥤ D` is any functor,
`initialComparison F` is the unique map `𝟘_ D ⟶ F (𝟘_ C)`. -/
abbrev initialComparison : 𝟘_ D ⟶ F.obj (𝟘_ C) := fromZero _

@[reassoc (attr := simp)]
lemma initialComparison_comp_map_fromZero (A : C) :
    initialComparison F ≫ F.map (fromZero A) = fromZero _ := fromZero_unique _ _

open Limits

/-- If `initialComparison F` is an Iso, then `F` preserves initial objects. -/
lemma preservesColimit_empty_of_isIso_initialComparison [IsIso (initialComparison F)] :
    PreservesColimit (Functor.empty.{0} C) F := by
  apply preservesColimit_of_preserves_colimit_cocone initial.isColimit
  apply isColimitChangeEmptyCocone D initial.isColimit
  exact asIso (initialComparison F)

/-- If `F` preserves initial objects, then `initialComparison F` is an isomorphism. -/
noncomputable def preservesInitialIso [h : PreservesColimit (Functor.empty.{0} C) F] :
    F.obj (𝟘_ C) ≅ 𝟘_ D :=
  (isColimitChangeEmptyCocone D (isColimitOfPreserves _ initial.isColimit)
    (asEmptyCocone (F.obj (𝟘_ C))) (Iso.refl _)).coconePointUniqueUpToIso initial.isColimit

@[simp]
lemma preservesInitialIso_inv [PreservesColimit (Functor.empty.{0} C) F] :
    (preservesInitialIso F).inv = initialComparison F := fromZero_unique _ _

instance initialComparison_isIso_of_preservesColimits [PreservesColimit (Functor.empty.{0} C) F] :
    IsIso (initialComparison F) := by
  rw [← preservesInitialIso_inv]
  infer_instance

end initialComparison

section coprodComparison

variable (A B : C)

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`coprodComparison F A B` is the canonical comparison morphism from `F(A) ⊕ₒ F(B)` to `F (A ⊕ₒ B)`.
-/
def coprodComparison (A B : C) : F.obj A ⊕ₒ F.obj B ⟶ F.obj (A ⊕ₒ B) :=
  desc (F.map (inl A B)) (F.map (inr A B))

@[reassoc (attr := simp)]
theorem inl_coprodComparison : inl _ _ ≫ coprodComparison F A B = F.map (inl A B) :=
  inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_coprodComparison : inr _ _ ≫ coprodComparison F A B = F.map (inr A B) :=
  inr_desc _ _

@[reassoc (attr := simp)]
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map (inl _ _) ≫ inv (coprodComparison F A B) = inl _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map (inr _ _) ≫ inv (coprodComparison F A B) = inr _ _ := by simp [IsIso.inv_comp_eq]

variable {A B} {A' B' : C}

/-- Naturality of the `coprodComparison` morphism in both arguments. -/
@[reassoc]
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (f ⊕ₕ g) =
      (F.map f ⊕ₕ F.map g) ≫ coprodComparison F A' B' := by
  apply hom_ext <;>
  simp only [Category.assoc, addHom, coprodComparison, inl_desc_assoc, inl_desc, inr_desc_assoc,
    inr_desc, ← F.map_comp]

section
variable [IsIso (coprodComparison F A B)]

/-- If the coproduct comparison morphism is an iso, its inverse is natural in both arguments. -/
@[reassoc]
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ (F.map f ⊕ₕ F.map g) =
      F.map (f ⊕ₕ g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, coprodComparison_natural]

end

theorem coprodComparison_comp {E : Type u₂} [Category.{v₂} E] [ChosenFiniteCoproducts E] (G : D ⥤ E) :
    coprodComparison (F ⋙ G) A B =
      coprodComparison G (F.obj A) (F.obj B) ≫ G.map (coprodComparison F A B) := by
  unfold coprodComparison
  ext <;> simp [← G.map_comp]

@[simp]
lemma coprodComparison_id :
    coprodComparison (𝟭 C) A B = 𝟙 (A ⊕ₒ B) := desc_inl_inr

end coprodComparison

end ChosenFiniteCoproductsComparison

end ChosenFiniteCoproducts

open MonoidalCategory ChosenFiniteProducts

namespace Functor

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D] (F : C ⥤ D)

open Functor.OplaxMonoidal

/- The definitions `oplaxMonoidalOfChosenFiniteProducts` and
`monoidalOfChosenFiniteProducts` are not made instances because it would
create a diamond for the (oplax) monoidal structure on a composition
`F ⋙ G` of functors between categories with chosen finite products. -/

/-- Any functor between categories with chosen finite products induces an oplax monoial functor. -/
def oplaxMonoidalOfChosenFiniteProducts : F.OplaxMonoidal where
  η' := terminalComparison F
  δ' X Y := prodComparison F X Y
  δ'_natural_left f X' := by simpa using (prodComparison_natural F f (𝟙 X')).symm
  δ'_natural_right X g := by simpa using (prodComparison_natural F (𝟙 X) g).symm
  oplax_associativity' _ _ _ := by
    apply hom_ext
    case' h_snd => apply hom_ext
    all_goals simp [← Functor.map_comp]
  oplax_left_unitality' _ := by
    apply hom_ext
    · exact toUnit_unique _ _
    · simp only [leftUnitor_inv_snd, Category.assoc, whiskerRight_snd,
        prodComparison_snd, ← F.map_comp, F.map_id]
  oplax_right_unitality' _ := by
    apply hom_ext
    · simp only [rightUnitor_inv_fst, Category.assoc, whiskerLeft_fst,
        prodComparison_fst, ← F.map_comp, F.map_id]
    · exact toUnit_unique _ _


attribute [local instance] oplaxMonoidalOfChosenFiniteProducts

lemma η_of_chosenFiniteProducts : η F = terminalComparison F := rfl

lemma δ_of_chosenFiniteProducts (X Y : C) : δ F X Y = prodComparison F X Y := rfl

open Limits

variable [PreservesFiniteProducts F]

instance : IsIso (η F) :=
  terminalComparison_isIso_of_preservesLimits F

instance (A B : C) : IsIso (δ F A B) :=
  isIso_prodComparison_of_preservesLimit_pair F A B

/-- If `F : C ⥤ D` is a functor between categories with chosen finite products
that preserves finite products, then it is a monoidal functor. -/
noncomputable def monoidalOfChosenFiniteProducts : F.Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal F

end Functor

namespace Functor.Monoidal

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D] (F : C ⥤ D)

section

attribute [local instance] oplaxMonoidalOfChosenFiniteProducts

@[reassoc (attr := simp)]
lemma δ_fst (X Y : C) : OplaxMonoidal.δ F X Y ≫ fst _ _ = F.map (fst _ _) := by
  simp [δ_of_chosenFiniteProducts]

@[reassoc (attr := simp)]
lemma δ_snd (X Y : C) : OplaxMonoidal.δ F X Y ≫ snd _ _ = F.map (snd _ _) := by
  simp [δ_of_chosenFiniteProducts]

@[reassoc (attr := simp)]
lemma lift_δ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    F.map (lift f g) ≫ OplaxMonoidal.δ F _ _ = lift (F.map f) (F.map g) := by
  apply hom_ext <;> simp [← F.map_comp]

end

section

open Limits

variable [PreservesFiniteProducts F]

attribute [local instance] monoidalOfChosenFiniteProducts

@[reassoc (attr := simp)]
lemma toUnit_ε {X : C} : toUnit (F.obj X) ≫ LaxMonoidal.ε F = F.map (toUnit X) :=
  (cancel_mono (εIso _).inv).1 (toUnit_unique _ _)

@[reassoc (attr := simp)]
lemma lift_μ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    lift (F.map f) (F.map g) ≫ LaxMonoidal.μ F _ _ = F.map (lift f g) :=
  (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_fst (X Y : C) : LaxMonoidal.μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_snd (X Y : C) : LaxMonoidal.μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

section

variable {F} {E : Type u₂} [Category.{v₂} E] [ChosenFiniteProducts E] {G : D ⥤ E}
  [PreservesFiniteProducts G]

attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
@[reassoc]
lemma μ_comp (X Y : C) :
    LaxMonoidal.μ (F ⋙ G) X Y = LaxMonoidal.μ G _ _ ≫ G.map (LaxMonoidal.μ F X Y) := by
  apply (cancel_mono (μIso _ _ _).inv).1
  apply ChosenFiniteProducts.hom_ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

end

end

end Functor.Monoidal

namespace Functor

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D] (F : C ⥤ D)

attribute [local instance] monoidalOfChosenFiniteProducts

/-- A finite-product-preserving functor between categories with chosen finite products is
braided. -/
noncomputable def braidedOfChosenFiniteProducts [Limits.PreservesFiniteProducts F] : F.Braided :=
  { monoidalOfChosenFiniteProducts F with
    braided X Y := by
      rw [← cancel_mono (Monoidal.μIso _ _ _).inv]
      apply ChosenFiniteProducts.hom_ext <;> simp [← Functor.map_comp] }

end Functor

namespace NatTrans

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D] (F G : C ⥤ D)
  [Limits.PreservesFiniteProducts F] [Limits.PreservesFiniteProducts G]

attribute [local instance] Functor.monoidalOfChosenFiniteProducts in
theorem monoidal_of_preservesFiniteProducts (α : F ⟶ G) :
    NatTrans.IsMonoidal α where
  unit := (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply ChosenFiniteProducts.hom_ext <;> simp

end NatTrans

end CategoryTheory
