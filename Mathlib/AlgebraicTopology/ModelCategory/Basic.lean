/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Model categories

We introduce a typeclass `ModelCategory C` expressing that `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" and "weak equivalences"
which satisfy the axioms of (closed) model categories as they appear for example
in *Simplicial Homotopy Theory* by Goerss and Jardine. We also provide an
alternate constructor `ModelCategory.mk'` which uses a formulation of the axioms
using weak factorization systems.

As a given category `C` may have several model category structures, it is advisable
to define only local instances of `ModelCategory`, or to set these instances on type synonyms.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]
* https://ncatlab.org/nlab/show/model+category

-/

universe w v u

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C]

/-- A model category is a category equipped with classes of morphisms named cofibrations,
fibrations and weak equivalences which satisfy the axioms CM1/CM2/CM3/CM4/CM5
of (closed) model categories. -/
class ModelCategory where
  categoryWithFibrations : CategoryWithFibrations C := by infer_instance
  categoryWithCofibrations : CategoryWithCofibrations C := by infer_instance
  categoryWithWeakEquivalences : CategoryWithWeakEquivalences C := by infer_instance
  cm1a : HasFiniteLimits C := by infer_instance
  cm1b : HasFiniteColimits C := by infer_instance
  cm2 : (weakEquivalences C).HasTwoOutOfThreeProperty := by infer_instance
  cm3a : (weakEquivalences C).IsStableUnderRetracts := by infer_instance
  cm3b : (fibrations C).IsStableUnderRetracts := by infer_instance
  cm3c : (cofibrations C).IsStableUnderRetracts := by infer_instance
  cm4a {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm4b {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm5a : MorphismProperty.HasFactorization (trivialCofibrations C) (fibrations C) := by
    infer_instance
  cm5b : MorphismProperty.HasFactorization (cofibrations C) (trivialFibrations C) := by
    infer_instance

namespace ModelCategory

attribute [instance] categoryWithFibrations categoryWithCofibrations categoryWithWeakEquivalences
  cm1a cm1b cm2 cm3a cm3b cm3c cm4a cm4b cm5a cm5b

section

variable [ModelCategory C]

instance : MorphismProperty.IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp ↦ by
    obtain ⟨_, _⟩ := mem_trivialCofibrations_iff i|>.mp hi
    rw [← fibration_iff] at hp
    infer_instance)

instance : MorphismProperty.IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp ↦ by
    rw [mem_trivialFibrations_iff] at hp
    rw [← cofibration_iff] at hi
    have := hp.1
    have := hp.2
    infer_instance)

end

section mk'

open MorphismProperty

variable {C} in
private lemma mk'.cm3a_aux [CategoryWithFibrations C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] {A B X Y : C}
    {f : A ⟶ B} {w : X ⟶ Y} [Fibration f] [WeakEquivalence w]
    (h : RetractArrow f w) : WeakEquivalence f := by
  have hw := factorizationData (trivialCofibrations C) (fibrations C) w
  have : (trivialFibrations C).IsStableUnderRetracts := by
    rw [← cofibrations_rlp]
    infer_instance
  have sq : CommSq h.r.left hw.i f (hw.p ≫ h.r.right) := ⟨by simp⟩
  have hf : fibrations C f := by rwa [← fibration_iff]
  have : HasLiftingProperty hw.i f := hasLiftingProperty_of_wfs _ _ hw.hi hf
  have : RetractArrow f hw.p :=
    { i := Arrow.homMk (h.i.left ≫ hw.i) h.i.right
      r := Arrow.homMk sq.lift h.r.right }
  have h' : trivialFibrations C hw.p :=
    ⟨hw.hp, (weakEquivalence_iff _).1 (weakEquivalence_of_precomp_of_fac hw.fac)⟩
  simpa only [weakEquivalence_iff] using (of_retract this h').2

/-- Constructor for `ModelCategory C` which assumes a formulation of axioms
using weak factorization systems. -/
def mk' [CategoryWithFibrations C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] [HasFiniteLimits C] [HasFiniteColimits C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] :
    ModelCategory C where
  cm3a := ⟨fun {A B X Y f w h hw} ↦ by
    rw [← weakEquivalence_iff] at hw
    have hf := factorizationData (trivialCofibrations C) (fibrations C) f
    have : Cofibration hf.i := by
      simpa only [cofibration_iff] using hf.hi.1
    have : WeakEquivalence hf.i := by
      simpa only [weakEquivalence_iff] using hf.hi.2
    let φ : pushout hf.i h.i.left ⟶ Y :=
      pushout.desc (hf.p ≫ h.i.right) w (by simp)
    have : Fibration hf.p := by simpa only [fibration_iff] using hf.hp
    have : WeakEquivalence (pushout.inr _ _ ≫ φ) := by simpa [φ]
    have := weakEquivalence_of_precomp (pushout.inr _ _) φ
    have hp : RetractArrow hf.p φ :=
      { i := Arrow.homMk (pushout.inl _ _) h.i.right
        r := Arrow.homMk (pushout.desc (𝟙 _) (h.r.left ≫ hf.i) (by simp)) h.r.right }
    have := mk'.cm3a_aux hp
    rw [← weakEquivalence_iff, ← hf.fac]
    infer_instance⟩
  cm3b := by
    rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    infer_instance
  cm3c := by
    rw [← llp_eq_of_wfs (cofibrations C) (trivialFibrations C)]
    infer_instance
  cm4a i p _ _ _ := hasLiftingProperty_of_wfs i p (mem_trivialCofibrations i) (mem_fibrations p)
  cm4b i p _ _ _ := hasLiftingProperty_of_wfs i p (mem_cofibrations i) (mem_trivialFibrations p)

end mk'

end ModelCategory

end HomotopicalAlgebra
