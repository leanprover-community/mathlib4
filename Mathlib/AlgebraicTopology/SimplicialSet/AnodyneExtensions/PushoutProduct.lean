/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Anodyne extensions and pushout-products, fibrations and pullbacks

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial
  HomotopicalAlgebra Limits Opposite

namespace CategoryTheory

-- to be moved...
namespace Functor.PushoutObjObj

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
  {X₁ Y₁ X₂ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
  (sq : (curriedTensor C).PushoutObjObj f₁ f₂)

/-- In a braided monoidal category, from a `Functor.PushoutObjObj` structure for
the bifunctor `curriedTensor` and two morphism `f₁` and `f₂`, one may
obtain a similar structure for `f₂` and `f₁`. -/
@[simps!]
def flipTensor : (curriedTensor C).PushoutObjObj f₂ f₁ :=
  sq.flip.ofNatIso (BraidedCategory.curriedBraidingNatIso _).symm

@[simp]
lemma flipTensor_ι : dsimp% sq.flipTensor.ι = sq.ι ≫ (β_ _ _).inv := by
  simp [flipTensor]

end Functor.PushoutObjObj

end CategoryTheory

namespace SSet

open modelCategoryQuillen

namespace prodStdSimplex

-- this will be done in #39298
noncomputable def pairing {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).Pairing :=
  sorry

instance {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (pairing.{u} k n).IsRegular :=
  sorry

lemma strongAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    strongAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι :=
  (pairing k n).strongAnodyneExtensions

lemma anodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    anodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι :=
  (pairing k n).anodyneExtensions

end prodStdSimplex

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

lemma fibration_pullbackObjObjπ [Mono i] [Fibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    Fibration sq₁₃.π := by
  rw [fibration_iff]
  intro _ _ _ h
  simp only [J, MorphismProperty.iSup_iff] at h
  obtain ⟨m, ⟨k⟩⟩ := h
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[m + 1, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices anodyneExtensions sq₁₂.ι from
    this _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _))]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[m + 1, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff (Subcomplex.unionProd.pushoutObjObj _ _),
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact prodStdSimplex.anodyneExtensions_unionProd_ι _ _ _ hp

lemma anodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : anodyneExtensions j) :
    anodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← HomotopicalAlgebra.fibration_iff] at hp ⊢
  exact fibration_pullbackObjObjπ sq₁₃

lemma anodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : anodyneExtensions i) :
    anodyneExtensions sq₁₂.ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).1
    (anodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

lemma anodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using anodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

lemma anodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι := by
  simpa using anodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

lemma anodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : anodyneExtensions f) (Z : SSet.{u}) :
    anodyneExtensions (f ▷ Z) := by
  simpa using anodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

lemma anodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : anodyneExtensions f) (Z : SSet.{u}) :
    anodyneExtensions (Z ◁ f) := by
  simpa using anodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

instance {E B X : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration ((ihom X).map p) := by
  simpa using fibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

instance {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (X : SSet.{u}) [IsFibrant X] :
    Fibration ((MonoidalClosed.pre i).app X) := by
  simpa using fibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom i (terminal.from X) terminalIsTerminal)

instance (A : SSet.{u}) : IsFibrant ((ihom A).obj (⊤_ _)) := by
  have : IsIso (terminal.from ((ihom A).obj (⊤_ _))) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj _ _ terminalIsTerminal)
      terminalIsTerminal _
  rw [isFibrant_iff]
  infer_instance

instance {A X : SSet.{u}} [IsFibrant X] : IsFibrant ((ihom A).obj X) :=
  isFibrant_of_fibration ((ihom A).map (terminal.from X))

end SSet
