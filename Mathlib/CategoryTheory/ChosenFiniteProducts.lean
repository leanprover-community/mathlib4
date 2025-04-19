/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
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

universe v v₁ v₂ v₃ u u₁ u₂ u₃

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

@[reassoc (attr := simp)]
lemma lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
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
lemma associator_inv_fst_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  erw [lift_fst_assoc]
  erw [lift_fst]
  rfl

@[deprecated (since := "2025-04-01")] alias associator_inv_fst := associator_inv_fst_fst
@[deprecated (since := "2025-04-01")] alias associator_inv_fst_assoc := associator_inv_fst_fst_assoc

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

lemma leftUnitor_hom (X : C) : (λ_ X).hom = snd _ _ := rfl
lemma rightUnitor_hom (X : C) : (ρ_ X).hom = fst _ _ := rfl

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

@[reassoc]
lemma whiskerLeft_toUnit_comp_rightUnitor_hom (X Y : C) : X ◁ toUnit Y ≫ (ρ_ X).hom = fst X Y := by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]
lemma whiskerRight_toUnit_comp_leftUnitor_hom (X Y : C) : toUnit X ▷ Y ≫ (λ_ Y).hom = snd X Y := by
  rw [← cancel_mono (λ_ Y).inv]; aesop

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
variable {E : Type u₂} [Category.{v₂} E] [ChosenFiniteProducts E] (G : D ⥤ E)

section terminalComparison

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`terminalComparison F` is the unique map `F (𝟙_ C) ⟶ 𝟙_ D`. -/
abbrev terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D := toUnit _

@[reassoc]
lemma map_toUnit_comp_terminalComparison (A : C) :
    F.map (toUnit A) ≫ terminalComparison F = toUnit _ := toUnit_unique _ _

@[deprecated (since := "2025-04-09")]
alias map_toUnit_comp_terminalCompariso := map_toUnit_comp_terminalComparison

@[deprecated (since := "2025-04-09")]
alias map_toUnit_comp_terminalCompariso_assoc := map_toUnit_comp_terminalComparison_assoc

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

@[simp]
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  ext; exact toUnit_unique ..

@[simp]
lemma preservesTerminalIso_comp [PreservesLimit (Functor.empty.{0} C) F]
    [PreservesLimit (Functor.empty.{0} D) G] [PreservesLimit (Functor.empty.{0} C) (F ⋙ G)]  :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  ext; exact toUnit_unique ..

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

/-- If the product comparison morphism is an iso, its inverse is natural in both argument. -/
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

@[simp] lemma prodComparisonIso_id  : prodComparisonIso (𝟭 C) A B = .refl _ := by ext <;> simp

@[simp]
lemma prodComparisonIso_comp [PreservesLimit (pair A B) (F ⋙ G)]
    [PreservesLimit (pair (F.obj A) (F.obj B)) G] :
    prodComparisonIso (F ⋙ G) A B =
      G.mapIso (prodComparisonIso F A B) ≪≫ prodComparisonIso G (F.obj A) (F.obj B) := by
  ext <;> simp [ChosenFiniteProducts.prodComparison, ← G.map_comp]

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

open Limits

variable {P : C → Prop}

-- TODO: Introduce `ClosedUnderFiniteProducts`?
/-- The restriction of a cartesian-monoidal category along an object property that's closed under
finite products is cartesian-monoidal. -/
noncomputable def fullSubcategory (hP₀ : ClosedUnderLimitsOfShape (Discrete PEmpty) P)
    (hP₂ : ClosedUnderLimitsOfShape (Discrete WalkingPair) P) :
    ChosenFiniteProducts (FullSubcategory P) where
  product X Y := {
    cone := BinaryFan.mk
      (P := ⟨X.1 ⊗ Y.1, hP₂ (product X.obj Y.obj).isLimit <| by rintro ⟨_ | _⟩ <;> simp [X.2, Y.2]⟩)
      (fst X.1 Y.1) (snd X.1 Y.1)
    isLimit := BinaryFan.IsLimit.mk _ (fun {T} f g ↦ lift (f : T.1 ⟶ X.1) g)
      (fun f g ↦ lift_fst _ _) (fun f g ↦ lift_snd _ _)
      (by rintro T f g m rfl rfl; symm; exact lift_comp_fst_snd _)
  }
  terminal.cone := asEmptyCone ⟨𝟙_ C, hP₀ terminal.isLimit <| by simp⟩
  terminal.isLimit := IsTerminal.isTerminalOfObj (fullSubcategoryInclusion _) _ <| .ofUnique (𝟙_ C)

end ChosenFiniteProducts

open MonoidalCategory ChosenFiniteProducts

variable
  {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
  {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]
  {E : Type u₃} [Category.{v₃} E] [ChosenFiniteProducts E]
  (F : C ⥤ D) (G : D ⥤ E) {X Y Z : C}

open Functor.LaxMonoidal Functor.OplaxMonoidal
open Limits (PreservesFiniteProducts)

namespace Functor.OplaxMonoidal
variable [F.OplaxMonoidal]

lemma η_of_chosenFiniteProducts : η F = terminalComparison F := toUnit_unique ..

lemma δ_of_chosenFiniteProducts (X Y : C) : δ F X Y = prodComparison F X Y := by
  ext
  · have eq₁ := δ_natural_right F X (toUnit Y) =≫ fst _ _
    have eq₂ := OplaxMonoidal.right_unitality_hom F X
    rw [Category.assoc, Category.assoc, whiskerLeft_fst] at eq₁
    rw [rightUnitor_hom, whiskerLeft_fst] at eq₂
    rw [eq₁, eq₂, prodComparison_fst, ← F.map_comp, rightUnitor_hom, whiskerLeft_fst]
  · have eq₁ := δ_natural_left F (toUnit X) Y =≫ snd _ _
    have eq₂ := OplaxMonoidal.left_unitality_hom F Y
    rw [Category.assoc, Category.assoc, whiskerRight_snd] at eq₁
    rw [leftUnitor_hom, whiskerRight_snd] at eq₂
    rw [eq₁, eq₂, prodComparison_snd, ← F.map_comp, leftUnitor_hom, whiskerRight_snd]

variable [PreservesFiniteProducts F]

instance : IsIso (η F) :=
  η_of_chosenFiniteProducts F ▸ terminalComparison_isIso_of_preservesLimits F

instance (X Y : C) : IsIso (δ F X Y) :=
  δ_of_chosenFiniteProducts F X Y ▸ isIso_prodComparison_of_preservesLimit_pair F X Y

omit [F.OplaxMonoidal] in
/-- Any functor between cartesian-monoidal categories is oplax monoidal.

This is not made an instance because it would create a diamond for the oplax monoidal structure on
the identity and composition of functors. -/
def ofChosenFiniteProducts : F.OplaxMonoidal where
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

omit [F.OplaxMonoidal] in
/-- Any functor between cartesian-monoidal categories is oplax monoidal in a unique way. -/
instance : Subsingleton F.OplaxMonoidal where
  allEq a b := by
    ext1
    · exact toUnit_unique _ _
    · ext1; ext1; rw [← δ, ← δ, δ_of_chosenFiniteProducts, δ_of_chosenFiniteProducts]

end OplaxMonoidal

namespace Monoidal
variable [F.Monoidal] [G.Monoidal]

@[reassoc (attr := simp)]
lemma toUnit_ε (X : C) : toUnit (F.obj X) ≫ ε F = F.map (toUnit X) := by
  rw [← cancel_mono (εIso F).inv]; exact toUnit_unique ..

@[reassoc (attr := simp)]
lemma δ_fst (X Y : C) : δ F X Y ≫ fst _ _ = F.map (fst _ _) := by
  rw [← whiskerLeft_toUnit_comp_rightUnitor_hom, ← whiskerLeft_toUnit_comp_rightUnitor_hom,
    LaxMonoidal.right_unitality, ← MonoidalCategory.whiskerLeft_comp_assoc, toUnit_ε,
    LaxMonoidal.μ_natural_right_assoc, δ_μ_assoc, map_comp]

@[reassoc (attr := simp)]
lemma δ_snd (X Y : C) : δ F X Y ≫ snd _ _ = F.map (snd _ _) := by
  rw [← whiskerRight_toUnit_comp_leftUnitor_hom, ← whiskerRight_toUnit_comp_leftUnitor_hom,
    LaxMonoidal.left_unitality, ← MonoidalCategory.comp_whiskerRight_assoc, toUnit_ε,
    LaxMonoidal.μ_natural_left_assoc, δ_μ_assoc, map_comp]

@[reassoc (attr := simp)]
lemma lift_δ (f : X ⟶ Y) (g : X ⟶ Z) : F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g) := by
  ext <;> simp [← map_comp]

@[reassoc (attr := simp)]
lemma lift_μ (f : X ⟶ Y) (g : X ⟶ Z) : lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g) :=
  (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_fst (X Y : C) : μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
lemma μ_snd (X Y : C) : μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
@[reassoc]
lemma μ_comp [(F ⋙ G).Monoidal] (X Y : C) : μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y) := by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

variable [PreservesFiniteProducts F]

lemma ε_of_chosenFiniteProducts : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext; simpa using η_of_chosenFiniteProducts F

lemma μ_of_chosenFiniteProducts (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_chosenFiniteProducts F X Y

attribute [local instance] OplaxMonoidal.ofChosenFiniteProducts in
omit [F.Monoidal] in
/-- A finite-product-preserving functor between cartesian monoidal categories is monoidal.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
noncomputable def ofChosenFiniteProducts : F.Monoidal := .ofOplaxMonoidal F

omit [F.Monoidal] in
instance : Subsingleton F.Monoidal := (toOplaxMonoidal_injective F).subsingleton

end Monoidal

namespace Braided
variable [PreservesFiniteProducts F]

attribute [local instance] Monoidal.ofChosenFiniteProducts in
/-- A finite-product-preserving functor between cartesian monoidal categories is braided.

This is not made an instance because it would create a diamond for the braided structure on
the identity and composition of functors. -/
noncomputable def ofChosenFiniteProducts : F.Braided where
  braided X Y := by rw [← cancel_mono (Monoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]

end Braided

namespace EssImageSubcategory
variable [F.Full] [F.Faithful] [PreservesFiniteProducts F] {T X Y Z : F.EssImageSubcategory}

@[simps!]
noncomputable instance instChosenFiniteProducts : ChosenFiniteProducts F.EssImageSubcategory :=
  .fullSubcategory (.essImage _) (.essImage _)

lemma tensor_obj (X Y : F.EssImageSubcategory) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

lemma fst_def (X Y : F.EssImageSubcategory) : fst X Y = fst X.obj Y.obj := rfl
lemma snd_def (X Y : F.EssImageSubcategory) : snd X Y = snd X.obj Y.obj := rfl
lemma lift_def (f : T ⟶ X) (g : T ⟶ Y) : lift f g = lift (T := T.1) f g := rfl

lemma whiskerLeft_def (X : F.EssImageSubcategory) (f : Y ⟶ Z) : X ◁ f = X.obj ◁ f := rfl
lemma whiskerRight_def (f : Y ⟶ Z) (X : F.EssImageSubcategory) :
    f ▷ X = MonoidalCategoryStruct.whiskerRight (C := D) f X.obj := rfl

lemma associator_hom_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := rfl

lemma associator_inv_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv := rfl

lemma toUnit_def (X : F.EssImageSubcategory) : toUnit X = toUnit X.obj := toUnit_unique ..

end Functor.EssImageSubcategory

namespace NatTrans
variable (F G : C ⥤ D) [F.Monoidal] [G.Monoidal]

instance isMonoidal_of_chosenFiniteProducts (α : F ⟶ G) : IsMonoidal α where
  unit := (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply ChosenFiniteProducts.hom_ext <;> simp

end NatTrans

end CategoryTheory
