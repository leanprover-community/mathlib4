/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Subterminal

/-!
# Exponential ideals

An exponential ideal of a Cartesian closed category `C` is a subcategory `D ⊆ C` such that for any
`B : D` and `A : C`, the exponential `A ⟹ B` is in `D`: resembling ring-theoretic ideals. We
define the notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories to
preserve the principle of equivalence.

We additionally show that if `C` is Cartesian closed and `i : D ⥤ C` is a reflective functor, the
following are equivalent.
* The left adjoint to `i` preserves binary (equivalently, finite) products.
* `i` is an exponential ideal.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category

open scoped CartesianClosed

section Ideal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D] {i : D ⥤ C}
variable (i) [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `A ⟹ B ∈ D` for all `A`.
-/
class ExponentialIdeal : Prop where
  exp_closed : ∀ {B}, i.essImage B → ∀ A, i.essImage (A ⟹ B)
attribute [nolint docBlame] ExponentialIdeal.exp_closed

/-- To show `i` is an exponential ideal it suffices to show that `A ⟹ iB` is "in" `D` for any `A` in
`C` and `B` in `D`.
-/
theorem ExponentialIdeal.mk' (h : ∀ (B : D) (A : C), i.essImage (A ⟹ i.obj B)) :
    ExponentialIdeal i :=
  ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((ihom A).mapIso iB') (h B' A)⟩

/-- The entire category viewed as a subcategory is an exponential ideal. -/
instance : ExponentialIdeal (𝟭 C) :=
  ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩

open MonoidalClosed

/-- The subcategory of subterminal objects is an exponential ideal. -/
instance : ExponentialIdeal (subterminalInclusion C) := by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (MonoidalClosed.uncurry g) (MonoidalClosed.uncurry h))

set_option backward.isDefEq.respectTransparency false in
/-- If `D` is a reflective subcategory, the property of being an exponential ideal is equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, that is:
`(A ⟹ iB) ≅ i L (A ⟹ iB)`, naturally in `B`.
The converse is given in `ExponentialIdeal.mk_of_iso`.
-/
def exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] :
    i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A := by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

/-- Given a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, we can show `i`
is an exponential ideal.
-/
theorem ExponentialIdeal.mk_of_iso [Reflective i]
    (h : ∀ A : C, i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A) : ExponentialIdeal i := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

end Ideal

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D]
variable (i : D ⥤ C)

/- This cannot be a local instance since it has free variables,
it can instead be used as a have when needed.
We assume HasFiniteProducts D as a hypothesis below, to avoid making this a local instance.
-/
theorem reflective_products [Limits.HasFiniteProducts C] [Reflective i] :
    Limits.HasFiniteProducts D := ⟨fun _ => hasLimitsOfShape_of_reflective i⟩

open MonoidalClosed MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
open Limits in
/-- Given a reflective subcategory `D` of a category with chosen finite products `C`, `D` admits
finite chosen products. -/
-- Note: This is not an instance as one might already have a (different) `CartesianMonoidalCategory`
-- instance on `D` (as for example with sheaves).
-- See note [reducible non-instances]
abbrev CartesianMonoidalCategory.ofReflective [CartesianMonoidalCategory C] [Reflective i] :
    CartesianMonoidalCategory D :=
  .ofChosenFiniteProducts
    ({ cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
       isLimit := by
         apply isLimitOfReflects i
         apply isLimitChangeEmptyCone _ isTerminalTensorUnit
         letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
           have := reflective_products i
           refine Functor.essImage.unit_isIso ⟨terminal D, ⟨PreservesTerminal.iso i |>.trans ?_⟩⟩
           exact IsLimit.conePointUniqueUpToIso (limit.isLimit _) isTerminalTensorUnit
         exact asIso ((reflectorAdjunction i).unit.app (𝟙_ C)) })
  fun X Y ↦
    { cone := BinaryFan.mk
        ((reflector i).map (fst (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
        ((reflector i).map (snd (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
      isLimit := by
        apply isLimitOfReflects i
        apply IsLimit.equivOfNatIsoOfIso (pairComp X Y _) _ _ _ |>.invFun
          (tensorProductIsBinaryProduct (i.obj X) (i.obj Y))
        fapply BinaryFan.ext
        · change (reflector i ⋙ i).obj (i.obj X ⊗ i.obj Y) ≅ (𝟭 C).obj (i.obj X ⊗ i.obj Y)
          letI : IsIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) := by
            apply Functor.essImage.unit_isIso
            haveI := reflective_products i
            use Limits.prod X Y
            constructor
            apply Limits.PreservesLimitPair.iso i _ _ |>.trans
            refine Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (i.obj X) (i.obj Y)))
              (tensorProductIsBinaryProduct _ _)
          exact asIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) |>.symm
        · simp only [BinaryFan.fst, Cones.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc]
        · simp only [BinaryFan.snd, Cones.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc] }

variable [CartesianMonoidalCategory C] [Reflective i] [MonoidalClosed C]
  [CartesianMonoidalCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- If the reflector preserves binary products, the subcategory is an exponential ideal.
This is the converse of `preservesBinaryProductsOfExponentialIdeal`.
-/
instance (priority := 10) exponentialIdeal_of_preservesBinaryProducts
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (reflector i)] :
    ExponentialIdeal i := by
  let ir := reflectorAdjunction i
  let L : C ⥤ D := reflector i
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit
  apply ExponentialIdeal.mk'
  intro B A
  let q : i.obj (L.obj (A ⟹ i.obj B)) ⟶ A ⟹ i.obj B := by
    apply MonoidalClosed.curry (ir.homEquiv _ _ _)
    apply _ ≫ (ir.homEquiv _ _).symm ((ihom.ev A).app (i.obj B))
    exact prodComparison L A _ ≫ (_ ◁ (ε.app _)) ≫ inv (prodComparison _ _ _)
  have : η.app (A ⟹ i.obj B) ≫ q = 𝟙 (A ⟹ i.obj B) := by
    dsimp
    rw [← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev, ← ir.homEquiv_naturality_left,
      ir.homEquiv_apply_eq, Category.assoc, Category.assoc,
      prodComparison_natural_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
      ir.left_triangle_components, whiskerLeft_id, Category.id_comp]
    apply IsIso.hom_inv_id_assoc
  haveI : IsSplitMono (η.app (A ⟹ i.obj B)) := IsSplitMono.mk' ⟨_, this⟩
  apply mem_essImage_of_unit_isSplitMono

variable [ExponentialIdeal i]

/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself Cartesian closed.

To allow for better control of definitional equality, this construction
takes in an explicit choice of lift of the essential image of `i` to `D`, in the form of a functor
`l : i.EssImageSubcategory ⥤ D` and natural isomorphism `φ : l ⋙ i ≅ i.essImage.ι`. When
`l ⋙ i` is defeq to `i.essImage.ι`, images of exponential objects in `D` under `i` will be defeq
to the respective exponential objects in `C`. -/
@[implicit_reducible]
def cartesianClosedOfReflective' (l : i.EssImageSubcategory ⥤ D) (φ : l ⋙ i ≅ i.essImage.ι) :
    MonoidalClosed D where
  closed := fun B =>
    { rightAdj := i.essImage.lift (i ⋙ ihom (i.obj B))
        (fun X ↦ ExponentialIdeal.exp_closed (i.obj_mem_essImage X) _) ⋙ l
      adj := by
        apply (ihom.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
          i.fullyFaithfulOfReflective
        · symm
          refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
          · haveI :=
              Adjunction.rightAdjoint_preservesLimits.{0, 0} (reflectorAdjunction i)
            apply asIso (prodComparison i B X)
          · dsimp [asIso]
            rw [prodComparison_natural_whiskerLeft]
        · exact (i.essImage.liftCompιIso _ _).symm.trans <|
            (Functor.isoWhiskerLeft _ φ.symm).trans (Functor.associator _ _ _).symm }

/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself Cartesian closed.

Unlike `cartesianClosedOfReflective'` this construction lifts exponential objects in `C` to
exponential objects in `D` by applying the reflector to them, even though they already lie in the
essential image of `i`; if you need better control over definitional equality, use
`cartesianClosedOfReflective'` instead. -/
@[implicit_reducible]
def cartesianClosedOfReflective : MonoidalClosed D :=
  cartesianClosedOfReflective' i (i.essImage.ι ⋙ reflector i)
    (NatIso.ofComponents (fun X ↦
      have := Functor.essImage.unit_isIso X.2
      (asIso ((reflectorAdjunction i).unit.app X.obj)).symm))

variable [BraidedCategory C]

/-- We construct a bijection between morphisms `L(A ⊗ B) ⟶ X` and morphisms `LA ⊗ LB ⟶ X`.
This bijection has two key properties:
* It is natural in `X`: See `bijection_natural`.
* When `X = LA ⨯ LB`, then the backwards direction sends the identity morphism to the product
  comparison morphism: See `bijection_symm_apply_id`.

Together these help show that `L` preserves binary products. This should be considered
*internal implementation* towards `preservesBinaryProductsOfExponentialIdeal`.
-/
noncomputable def bijection (A B : C) (X : D) :
    ((reflector i).obj (A ⊗ B) ⟶ X) ≃ ((reflector i).obj A ⊗ (reflector i).obj B ⟶ X) :=
  calc
    _ ≃ (A ⊗ B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B ⊗ A ⟶ i.obj X) := (β_ _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (B ⊗ i.obj ((reflector i).obj A) ⟶ i.obj X) := ((ihom.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A) ⊗ B ⟶ i.obj X) :=
      ((β_ _ _).homCongr (Iso.refl _))
    _ ≃ (B ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj B) ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (i.obj ((reflector i).obj A) ⊗ i.obj ((reflector i).obj B) ⟶ i.obj X) :=
      ((ihom.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A ⊗ (reflector i).obj B) ⟶ i.obj X) :=
      haveI : Limits.PreservesLimits i := (reflectorAdjunction i).rightAdjoint_preservesLimits
      haveI := Limits.preservesSmallestLimits_of_preservesLimits i
      Iso.homCongr (prodComparisonIso _ _ _).symm (Iso.refl (i.obj X))
    _ ≃ ((reflector i).obj A ⊗ (reflector i).obj B ⟶ X) :=
      i.fullyFaithfulOfReflective.homEquiv.symm

set_option backward.isDefEq.respectTransparency false in
theorem bijection_symm_apply_id (A B : C) :
    (bijection i A B _).symm (𝟙 _) = prodComparison _ _ _ := by
  simp only [bijection, Equiv.trans_def, curriedTensor_obj_obj, Equiv.symm_trans_apply,
    Equiv.symm_symm, Functor.FullyFaithful.homEquiv_apply, Functor.map_id, Iso.homCongr_symm,
    Iso.symm_symm_eq, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    unitCompPartialBijective_symm_apply, Functor.id_obj, Functor.comp_obj, Iso.symm_inv]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry,
    ← BraidedCategory.braiding_naturality_left_assoc, SymmetricCategory.symmetry_assoc,
    ← MonoidalCategory.whisker_exchange_assoc, ← tensorHom_def'_assoc,
    Adjunction.homEquiv_symm_apply, ← Adjunction.eq_unit_comp_map_iff, Iso.comp_inv_eq,
    Category.assoc, prodComparisonIso_hom i ((reflector i).obj A) ((reflector i).obj B)]
  apply hom_ext
  · rw [tensorHom_fst, Category.assoc, Category.assoc, prodComparison_fst, ← i.map_comp,
    prodComparison_fst]
    apply (reflectorAdjunction i).unit.naturality
  · rw [tensorHom_snd, Category.assoc, Category.assoc, prodComparison_snd, ← i.map_comp,
    prodComparison_snd]
    apply (reflectorAdjunction i).unit.naturality

set_option backward.isDefEq.respectTransparency false in
theorem bijection_natural (A B : C) (X X' : D) (f : (reflector i).obj (A ⊗ B) ⟶ X) (g : X ⟶ X') :
    bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g := by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage, i.map_comp,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Category.comp_id, Functor.map_comp, Functor.FullyFaithful.map_preimage, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, curry_natural_right _ (i.map g),
    unitCompPartialBijective_natural, uncurry_natural_right, ← Category.assoc, curry_natural_right,
    unitCompPartialBijective_natural, uncurry_natural_right, Category.assoc]

/--
The bijection allows us to show that `prodComparison L A B` is an isomorphism, where the inverse
is the forward map of the identity morphism.
-/
theorem prodComparison_iso (A B : C) : IsIso
    (prodComparison (reflector i) A B) :=
  ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff, bijection_natural, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply, Category.id_comp],
      by rw [← bijection_natural, Category.id_comp, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply]⟩⟩

attribute [local instance] prodComparison_iso

open Limits

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves binary products.
This is the converse of `exponentialIdeal_of_preserves_binary_products`.
-/
lemma preservesBinaryProducts_of_exponentialIdeal :
    PreservesLimitsOfShape (Discrete WalkingPair) (reflector i) where
  preservesLimit {K} :=
    letI := preservesLimit_pair_of_isIso_prodComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves finite products.
-/
lemma Limits.PreservesFiniteProducts.of_exponentialIdeal : PreservesFiniteProducts (reflector i) :=
  have := preservesBinaryProducts_of_exponentialIdeal i
  have : PreservesLimitsOfShape _ (reflector i) := leftAdjoint_preservesTerminal_of_reflective.{0} i
  .of_preserves_binary_and_terminal _

end

end CategoryTheory
