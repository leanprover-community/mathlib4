/-
Copyright (c) 2020 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Prod
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Monoidal adjunctions

Monoidal functors come in two types, lax and colax. Adjunctions between these
come in the form `colax ⊣ lax`. In fact we can automatically promote the left
adjoint of a lax functor to a colax functor and the right adjoint of a colax
functor to a lax functor. Since a (strong) monoidal functor is one which is
both lax and colax, this means an adjunction between two lax (colax) functor
automatically has its left (right) adjoint strong monoidal.

Note that a monoidal adjunction `colax ⊣ lax` is not just any adjunction of
the underlying functors; the structure maps of the monoidal functors must
correspond across the adjunction.

This can be fit into the general theory of doctrinal adjunction, which is about
adjunctions between colax and lax algebras of a 2-monad. It can also be fit
into the framework of double categories (as doctrinal adjunction can be).

References: Adjoint for double categories, Grandis and Pare
-/

open CategoryTheory

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]
         {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
         {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
         {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
         {M : Type u₄} [Category.{v₄} M] [MonoidalCategory.{v₄} M]
         {N : Type u₅} [Category.{v₅} N] [MonoidalCategory.{v₅} N]

structure MonoidalAdjunction (F : C ⥤⊗c D) (G : D ⥤⊗ℓ C) where
  adj : F.toFunctor ⊣ G.toFunctor
  ε_mate_η_components : adj.unit.app (𝟙_ C) ≫ G.toPrefunctor.map F.ε = G.η
  δ_mate_μ_components : ∀ (X Y : D),
    adj.unit.app (G.obj X ⊗ G.obj Y) ≫ G.map (F.δ (G.obj X) (G.obj Y)) ≫
      G.map (adj.counit.app X ⊗ adj.counit.app Y) = G.μ X Y

attribute [reassoc (attr := simp)] MonoidalAdjunction.ε_mate_η_components
attribute [reassoc (attr := simp)] MonoidalAdjunction.δ_mate_μ_components

/-- The notation `F ⊣⊗ G` stands for `MonoidalAdjunction F G`. -/
infixl:15 " ⊣⊗ " => MonoidalAdjunction

namespace MonoidalAdjunction

section

variable {F : C ⥤⊗c D} {G : D ⥤⊗ℓ C} (adj : F ⊣⊗ G)

@[reassoc (attr:=simp)]
lemma μ_mate_δ_components (X Y : C) :
    F.map (adj.adj.unit.app X ⊗ adj.adj.unit.app Y) ≫
      F.map (G.μ (F.obj X) (F.obj Y)) ≫
        adj.adj.counit.app (F.obj X ⊗ F.obj Y) = F.δ X Y := by
  simp [← adj.δ_mate_μ_components, ← @tensor_comp D,
        -δ_mate_μ_components, -tensor_comp]

@[reassoc (attr:=simp)]
lemma η_mate_ε_components :
    F.map G.η ≫ adj.adj.counit.app (𝟙_ D) = F.ε := by
  simp [← adj.ε_mate_η_components, -ε_mate_η_components]

lemma ε_mate_η : adj.adj.homEquiv (𝟙_ C) (𝟙_ D) F.ε = G.η := by
  simp

lemma η_mate_ε : (adj.adj.homEquiv (𝟙_ C) (𝟙_ D)).symm G.η = F.ε := by
  simp

lemma δ_μ_mates :
    transferNatTrans (adj.adj.prod adj.adj) adj.adj F.δNatTrans = G.μNatTrans := by
  aesop_cat

lemma μ_δ_mates :
    (transferNatTrans (adj.adj.prod adj.adj) adj.adj).symm G.μNatTrans = F.δNatTrans := by
  aesop_cat

@[simps]
def unit : MonoidalSq (.id C) F (.id C) G where
  constraint := (Functor.leftUnitor _).hom ≫ adj.adj.unit
  hexagon' := by simp [← adj.μ_mate_δ_components, -μ_mate_δ_components]

@[simps]
def counit : MonoidalSq G (.id D) F (.id D) where
  constraint := adj.adj.counit ≫ (Functor.leftUnitor _).inv
  hexagon' := by simp [← adj.δ_mate_μ_components, - δ_mate_μ_components]

-- The "right" triangle identity, as a square
lemma counit_hcomp_unit_app :
    adj.counit.hcomp adj.unit = LaxMonoidalNatTrans.equivHGlobularSquare _ _
      (G.rightUnitor.hom ≫ G.leftUnitor.inv) := by
  aesop_cat

-- The "left" triangle identity, as a square
lemma unit_vcomp_counit_app :
    adj.unit.vcomp adj.counit = ColaxMonoidalNatTrans.equivVGlobularSquare _ _
      (F.leftUnitor.hom ≫ F.rightUnitor.inv) := by
  aesop_cat

@[simps]
def mkOfConjuction (unit : MonoidalSq (.id C) F (.id C) G)
    (counit : MonoidalSq G (.id D) F (.id D))
    (left_triangle :
      unit.vcomp counit = ColaxMonoidalNatTrans.equivVGlobularSquare _ _
            (F.leftUnitor.hom ≫ F.rightUnitor.inv) := by aesop_cat)
    (right_triangle :
      counit.hcomp unit = LaxMonoidalNatTrans.equivHGlobularSquare _ _
        (G.rightUnitor.hom ≫ G.leftUnitor.inv) := by aesop_cat) : F ⊣⊗ G where
  adj := Adjunction.mkOfUnitCounit {
    unit := (Functor.leftUnitor _).inv ≫ unit.constraint
    counit := counit.constraint ≫ (Functor.leftUnitor _).inv
    left_triangle := by
      ext X
      simpa using congrArg (fun σ => σ.constraint.app X) left_triangle
    right_triangle := by
      ext X
      simpa using congrArg (fun σ => σ.constraint.app X) right_triangle
  }
  ε_mate_η_components := by simpa using unit.trapezoid
  -- TODO: clean this up, maybe after we have a better API for mates/pasting?
  δ_mate_μ_components := by
    intros X Y
    dsimp
    erw [assoc, unit.hexagon_components_assoc]
    have H1 := congrArg (fun σ => σ.constraint.app X) right_triangle
    have H2 := congrArg (fun σ => σ.constraint.app Y) right_triangle
    dsimp at H1 H2
    simp only [id_comp, comp_id] at H1 H2
    simp [← G.μ_natural, ← tensor_comp_assoc, H1, H2,
          -LaxMonoidalFunctor.μ_natural, -tensor_comp]

end

end MonoidalAdjunction

namespace LaxMonoidalFunctor

variable (F : C ⥤⊗ℓ D) [IsRightAdjoint F.toFunctor]
#check ColaxMonoidalFunctor.δNatTrans
open associativity_coherences in
@[simps ε δ toFunctor]
def leftAdjoint : D ⥤⊗c C :=
  let G := CategoryTheory.leftAdjoint F.toFunctor
  let h : G ⊣ F.toFunctor := Adjunction.ofRightAdjoint F.toFunctor
  let δ := (transferNatTrans (h.prod h) h).symm F.μNatTrans
  .ofTensorHom G ((h.homEquiv _ _).symm F.η) (fun X Y => δ.app (X, Y))
    (fun {X Y X' Y'} f g => δ.naturality (X := (X, X')) (Y := (Y, Y')) (f, g))
    (fun X Y Z => by
      have h1 := F.associativity_nat_trans
      have h2 := congrArg (transferNatTrans (h.prod (h.prod h)) h).symm h1
      have h3 := congrArg (NatTrans.app · (X, Y, Z)) h2
      -- erw [comp_id, id_comp, id_comp, id_comp, id_comp, id_comp] at h3
      -- simp only [comp_id] at h3
      -- dsimp [leftAssocTensor] at h3 ⊢
      dsimp only [coherence1, coherence2, coherence3,
        coherence4, coherence5, coherence6, Iso.refl_hom] at h3
      erw [comp_id, id_comp, id_comp, id_comp, id_comp, id_comp] at h3

      -- repeat erw [id_comp] at h3; erw [comp_id, id_comp] at h3
      admit)
    sorry
    sorry
  -- { G with
  --   ε := (h.homEquiv _ _).symm F.η
  --   δ := fun X Y => ((transferNatTrans (h.prod h) h).symm F.μNatTrans).app (X, Y)
  --   δ_natural_left := by
  --     intros X Y f X'
  --     admit
  --   δ_natural_right := by
  --     admit
  --   coassociativity := by
  --     admit
  --   left_counitality := by
  --     admit
  --   right_counitality := by
  --     admit }

end LaxMonoidalFunctor

/-

variable (F : C ⥤⊗s D)

section

variable [IsLeftAdjoint F.toFunctor]

-- TODO: Doctrinal adjunction, double category of (op)lax morphisms of an algebra
/-- If we have a right adjoint functor `G` to a monoidal functor `F`,
then `G` acquires a lax monoidal structure.
-/
@[simps η μ]
def rightAdjoint : D ⥤⊗ℓ C :=
  let h := Adjunction.ofLeftAdjoint F.toFunctor
  let G := CategoryTheory.rightAdjoint F.toFunctor
  { G with
    η := h.homEquiv _ _ F.ε
    μ := fun X Y => h.homEquiv _ _ <|
      F.δ (G.obj X) (G.obj Y) ≫ (h.counit.app X ⊗ h.counit.app Y)
    μ_natural_left := by
      intros
      erw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right,
        assoc, F.map_whiskerRight_assoc, F.μ_δ_id_assoc,
        ← tensor_comp, ← tensor_comp, id_comp, comp_id, h.counit_naturality]
    μ_natural_right := by
      intros
      erw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right,
        assoc, F.map_whiskerLeft_assoc, F.μ_δ_id_assoc,
        ← tensor_comp, ← tensor_comp, id_comp, comp_id, h.counit_naturality]
    associativity := by
      intro X Y Z
      dsimp only
      erw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left,
        ← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left, Equiv.apply_eq_iff_eq,
        ← (F.μIso (G.obj X ⊗ G.obj Y) (G.obj Z)).cancel_iso_hom_left,
        ← ((tensorRight _).mapIso (F.μIso (G.obj X) (G.obj Y))).cancel_iso_hom_left,
        mapIso_hom, tensorRight_map,
        F.associativity_assoc (G.obj X) (G.obj Y) (G.obj Z),
        ← F.μ_natural_assoc, assoc, F.μ_δ_id_assoc,
        ← F.μ_natural_assoc, F.μ_δ_id_assoc, ← tensor_comp,
        ← tensor_comp, id_comp, Functor.map_id, Functor.map_id, id_comp, ← tensor_comp_assoc,
        ← tensor_comp_assoc, id_comp, id_comp, h.homEquiv_unit, h.homEquiv_unit, Functor.map_comp,
        assoc, assoc, h.counit_naturality, h.left_triangle_components_assoc, Functor.map_comp,
        assoc, h.counit_naturality, h.left_triangle_components_assoc]
      simp
    left_unitality := by
      intro
      erw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
        h.homEquiv_counit, F.map_leftUnitor_hom, h.homEquiv_unit, assoc, assoc, assoc,
        F.map_tensor, assoc, assoc, F.μ_δ_id_assoc,
        ← tensor_comp_assoc, Functor.map_id, id_comp, Functor.map_comp, assoc,
        h.counit_naturality, h.left_triangle_components_assoc,
        ← leftUnitor_naturality, ← tensor_comp_assoc, id_comp, comp_id]
      rfl
    right_unitality := by
      intro
      erw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
        h.homEquiv_counit, F.map_rightUnitor_hom, assoc, assoc, ← rightUnitor_naturality,
        ← tensor_comp_assoc, comp_id, id_comp, h.homEquiv_unit, F.map_tensor, assoc, assoc, assoc,
        F.μ_δ_id_assoc, Functor.map_comp, Functor.map_id,
        ← tensor_comp_assoc, assoc, h.counit_naturality, h.left_triangle_components_assoc, id_comp]
      simp }
#align category_theory.monoidal_adjoint CategoryTheory.MonoidalFunctor.rightAdjoint

@[simp] lemma rightAdjoint_obj (X : D) :
    (rightAdjoint F).obj X = (CategoryTheory.rightAdjoint F.toFunctor).obj X := rfl

@[simp] lemma rightAdjoint_map {X Y} (f : X ⟶ Y) :
    (rightAdjoint F).map f = (CategoryTheory.rightAdjoint F.toFunctor).map f := rfl

end

section

variable [IsRightAdjoint F.toFunctor]

-- unfortunately we can't use simps here because the instance confuses
-- the tactic (even making it a local instance doesn't fix things)
/-- If we have a left adjoint functor `G` to a monoidal functor `F`,
then `G` acquires a colax monoidal structure.
-/
def leftAdjoint : D ⥤⊗c C :=
  letI : IsLeftAdjoint F.op.toLaxMonoidalFunctor.toFunctor :=
    inferInstanceAs (IsLeftAdjoint F.toFunctor.op)
  (rightAdjoint F.op).unop

@[simp] lemma leftAdjoint_obj (X : D) :
    (leftAdjoint F).obj X = (CategoryTheory.leftAdjoint F.toFunctor).obj X := rfl

@[simp] lemma leftAdjoint_map {X Y} (f : X ⟶ Y) :
    (leftAdjoint F).map f = (CategoryTheory.leftAdjoint F.toFunctor).map f := rfl

@[simp] lemma leftAdjoint_ε :
    (leftAdjoint F).ε = ((Adjunction.ofRightAdjoint F.toFunctor).homEquiv
                            (𝟙_ D) (𝟙_ C)).symm F.η := rfl

@[simp] lemma leftAdjoint_δ (X Y : D) :
    (leftAdjoint F).δ X Y =
    ((Adjunction.ofRightAdjoint F.toFunctor).homEquiv _ _).symm
      (((Adjunction.ofRightAdjoint F.toFunctor).unit.app X ⊗
        (Adjunction.ofRightAdjoint F.toFunctor).unit.app Y) ≫
        F.μ ((CategoryTheory.leftAdjoint F.toFunctor).obj X)
            ((CategoryTheory.leftAdjoint F.toFunctor).obj Y)) := rfl

end

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
def monoidalInverse [IsEquivalence F.toFunctor] : D ⥤⊗s C where
  η_ε_id := by
    erw [assoc, ← F.inv.map_comp_assoc, F.ε_η_id, map_id, id_comp,
      Iso.hom_inv_id_app]; rfl
  ε_η_id := by
    erw [assoc, Iso.inv_hom_id_app_assoc, ← F.inv.map_comp, F.η_ε_id, map_id]; rfl
  μ_δ_id X Y := by
    erw [assoc, ← F.inv.map_comp_assoc, assoc, ← tensor_comp_assoc,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app, tensor_id, id_comp,
      F.δ_μ_id, map_id, id_comp, Iso.hom_inv_id_app]; rfl
  δ_μ_id X Y := by
    erw [assoc, Iso.inv_hom_id_app_assoc, ← F.inv.map_comp, assoc,
      F.μ_δ_id_assoc, ← tensor_comp, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
      tensor_id, map_id]; rfl
  toFunctor := F.inv
  __ := leftAdjoint F
  __ := rightAdjoint F
#align category_theory.monoidal_inverse CategoryTheory.MonoidalFunctor.monoidalInverse

@[simp] lemma monoidalInverse_obj [IsEquivalence F.toFunctor] (X : D) :
    (monoidalInverse F).obj X = F.inv.obj X := rfl

@[simp] lemma monoidalInverse_map [IsEquivalence F.toFunctor] {X Y} (f : X ⟶ Y) :
    (monoidalInverse F).map f = F.inv.map f := rfl

@[simp] lemma monoidalInverse_η [IsEquivalence F.toFunctor] :
    (monoidalInverse F).η = F.asEquivalence.toAdjunction.homEquiv _ _ F.ε := rfl

@[simp] lemma monoidalInverse_ε [IsEquivalence F.toFunctor] :
    (monoidalInverse F).ε =
      (F.inv.asEquivalence.toAdjunction.homEquiv _ _).symm F.η := rfl

@[simp] lemma monoidalInverse_μ [IsEquivalence F.toFunctor] (X Y : D) :
    (monoidalInverse F).μ X Y =
      F.asEquivalence.toAdjunction.homEquiv _ _
        (F.δ (F.inv.obj X) (F.inv.obj Y) ≫
          (F.asEquivalence.counit.app X ⊗ F.asEquivalence.counit.app Y)) := rfl

instance (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    IsEquivalence (monoidalInverse F).toFunctor :=
  inferInstanceAs (IsEquivalence F.inv)


-/

/-

section

/-- The unit of a monoidal adjunction can be upgraded to a monoidal natural transformation. -/
def Adjunction.monoidalUnit (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    LaxMonoidalFunctor.id C ⟶ F.toLaxMonoidalFunctor ⊗⋙ F.rightAdjoint where
  toNatTrans := (ofLeftAdjoint F.toFunctor).unit
  unit := by simp [← (rightAdjoint F.toFunctor).map_comp, -map_comp]
  tensor X Y := ((ofLeftAdjoint F.toFunctor).homEquiv _ _).symm.injective <| by
    -- we shouldn't need to do this! maybe related to the diamond inheritance issue?
    have H := @ColaxMonoidalFunctor.δ_natural_assoc _ _ _ _ _ _
      F.toColaxMonoidalFunctor
    dsimp at H
    simp [← tensor_comp_assoc, H]

/-- The unit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps!] -- Porting note: have to manually specify the toNatTrans projection
def Equivalence.monoidalUnitIso (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    MonoidalFunctor.id C ≅ F ⊗⋙ F.monoidalInverse :=
  let η := Adjunction.monoidalUnit F
  (isoEquivOfFullyFaithful (MonoidalFunctor.toLax _ _)).symm <|
    LaxMonoidalNatIso.ofComponents (fun X => IsEquivalence.unitIso.app X)
      (fun f => η.naturality f) η.unit η.tensor

/-- The counit of a monoidal adjunction can be upgraded to a monoidal natural transformation. -/
@[simps toNatTrans]
def Adjunction.monoidalCounit (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    F.rightAdjoint ⊗⋙ F.toLaxMonoidalFunctor ⟶ LaxMonoidalFunctor.id D where
  toNatTrans := (ofLeftAdjoint F.toFunctor).counit

/-- The counit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps!] -- Porting note: have to manually specify the toNatTrans projection
def Equivalence.monoidalCounitIso (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    F.monoidalInverse ⊗⋙ F ≅ MonoidalFunctor.id D :=
  let η := Adjunction.monoidalCounit F
  (isoEquivOfFullyFaithful (MonoidalFunctor.toLax _ _)).symm <|
    LaxMonoidalNatIso.ofComponents (fun X => IsEquivalence.counitIso.app X)
      (fun f => η.naturality f) η.unit η.tensor

end
-/

end CategoryTheory
