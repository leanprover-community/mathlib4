/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

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

namespace ChosenFiniteProducts

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    MonoidalCategory C :=
  monoidalOfChosenFiniteProducts terminal product

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    SymmetricCategory C :=
  symmetricOfChosenFiniteProducts _ _

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

open MonoidalCategory

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
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _ := lift_fst _ _

@[reassoc (attr := simp)]
lemma associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd _ _  := by
  erw [lift_snd_assoc, lift_fst]
  rfl

@[reassoc (attr := simp)]
lemma associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _  := by
  erw [lift_snd_assoc, lift_snd]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  erw [lift_fst_assoc, lift_fst]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst _ _ := by
  erw [lift_fst_assoc, lift_snd]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _ := lift_snd _ _

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

@[simp]
lemma map_toUnit_comp_terminalCompariso (A : C) :
    F.map (toUnit A) ≫ terminalComparison F = toUnit _ := toUnit_unique _ _

open Limits

/-- If `terminalComparison F` is an Iso, then `F` preserves terminal objects. -/
noncomputable def preservesLimitEmptyOfIsIsoTerminalComparison [IsIso (terminalComparison F)] :
    PreservesLimit (Functor.empty.{0} C) F := by
  apply preservesLimitOfPreservesLimitCone terminal.isLimit
  apply isLimitChangeEmptyCone D terminal.isLimit
  exact asIso (terminalComparison F)|>.symm

/-- If `F` preserves terminal objects, then `terminalComparison F` is an isomorphism. -/
def PreservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] : F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (isLimitChangeEmptyCone D (h.preserves terminal.isLimit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso terminal.isLimit

@[simp]
lemma PreservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] :
    (PreservesTerminalIso F).hom = terminalComparison F := toUnit_unique _ _

instance terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty.{0} C) F] :
    IsIso (terminalComparison F) := by
  rw [← PreservesTerminalIso_hom]
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

@[reassoc]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (fst _ _) = fst _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc]
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

/-- The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
def prodComparisonBifunctorNatTrans :
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj F ⟶
      F ⋙ curriedTensor D ⋙ (whiskeringLeft _ _ _).obj F where
  app A := prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;>
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, curriedTensor_obj_obj,
      whiskeringLeft_obj_obj, Functor.comp_map, whiskeringRight_obj_map, NatTrans.comp_app,
      whiskerRight_app, curriedTensor_map_app, prodComparisonNatTrans_app, Category.assoc,
      prodComparison_fst, whiskeringLeft_obj_map, whiskerLeft_app, whiskerRight_fst,
      prodComparison_fst_assoc, prodComparison_snd, whiskerRight_snd, ← F.map_comp]

/-- The natural isomorphism `F(A ⊗ -) ≅ FA ⊗ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes). -/
@[simps]
noncomputable def prodComparisonNatIso (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    (curriedTensor C).obj A ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

/-- The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism. -/
@[simps]
noncomputable def prodComparisonBifunctorsNatIso
    [∀ A B, IsIso (prodComparison F A B)] :
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj F ≅
      F ⋙ curriedTensor D ⋙ (whiskeringLeft _ _ _).obj F := by
  refine { @asIso _ _ _ _ _ ?_ with hom := prodComparisonBifunctorNatTrans F }
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun A ↦ Iso.isIso_hom (prodComparisonNatIso F A))

theorem prodComparison_comp {E : Type u₂} [Category.{v₂} E] [ChosenFiniteProducts E] (G : D ⥤ E) :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp <;> rw [← G.map_comp] <;> simp

open Limits

section PreservesLimitPairs

variable (A B)
variable [PreservesLimit (pair A B) F]

/-- If `F` preserves the limit of the pair `(A, B)`, then the binary fan given by
`(F.map fst A B, F.map (snd A B))` is a limit cone. -/
def isLimitChosenFiniteProductsOfPreservesLimits :
    IsLimit <| BinaryFan.mk (F.map (fst A B)) (F.map (snd A B)) :=
  mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _) <|
    (product A B).isLimit.ofIsoLimit <| isoBinaryFanMk (product A B).cone

/-- If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is an isomorphism.
-/
def prodComparisonIso : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitChosenFiniteProductsOfPreservesLimits F A B)
    (product _ _).isLimit

@[simp]
lemma prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B := by
  rfl

instance isIso_prodComparison_of_preservesLimit_pair: IsIso (prodComparison F A B) := by
  rw [← prodComparisonIso_hom]
  infer_instance

end PreservesLimitPairs

section ProdComparisonIso

/-- If `prodComparison F A B` is an isomorphism, then `F` preserves the limit of `pair A B`. -/
noncomputable def preservesLimitPairOfIsIsoProdComparison (A B : C) [IsIso (prodComparison F A B)] :
    PreservesLimit (pair A B) F := by
  apply preservesLimitOfPreservesLimitCone (product A B).isLimit
  apply IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((product (F.obj A) (F.obj B)).cone.extend (prodComparison F A B)) _|>.invFun
  rotate_left
  · apply Cones.ext
    case φ => exact Iso.refl _
    rintro ⟨⟨j⟩⟩
    · simp only [Cones.postcompose_obj_pt, Functor.mapCone_pt, Functor.const_obj_obj,
      pair_obj_left, Cones.postcompose_obj_π, NatTrans.comp_app, Functor.comp_obj,
      Functor.mapCone_π_app, BinaryFan.π_app_left, Cone.extend_pt, Iso.refl_hom, Cone.extend_π,
      yoneda_obj_obj, Cone.extensions_app, Functor.op_obj, Functor.const_map_app, Category.id_comp]
      rw [← fst, ← fst, pairComp]
      simp
    · simp only [Cones.postcompose_obj_pt, Functor.mapCone_pt, Functor.const_obj_obj,
      pair_obj_right, Cones.postcompose_obj_π, NatTrans.comp_app, Functor.comp_obj,
      Functor.mapCone_π_app, BinaryFan.π_app_right, Cone.extend_pt, Iso.refl_hom, Cone.extend_π,
      yoneda_obj_obj, Cone.extensions_app, Functor.op_obj, Functor.const_map_app, Category.id_comp]
      rw [← snd, ← snd, pairComp]
      simp
  · exact IsLimit.extendIso _ (product (F.obj A) (F.obj B)).isLimit

/-- If `prodComparison F A B` is an isomorphism for all `A B` then `F` preserves limits of shape
`Discrete (WalkingPair)`. -/
noncomputable def preservesLimitsOfShapeDiscreteWalkingPairOfIsoProdComparison
    [∀ A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  constructor
  intro K
  refine @preservesLimitOfIsoDiagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimitPairOfIsIsoProdComparison

end ProdComparisonIso

end prodComparison

end ChosenFiniteProductsComparison

end ChosenFiniteProducts

end CategoryTheory
