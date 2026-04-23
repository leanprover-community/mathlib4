/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Cylinders

We introduce a notion of cylinder for an object `A : C` in a model category.
It consists of an object `I`, a weak equivalence `π : I ⟶ A` equipped with two sections
`i₀` and `i₁`. This notion shall be important in the definition of "left homotopies"
in model categories.

## Implementation notes

The most important definition in this file is `Cylinder A`. This structure
extends another structure `Precylinder A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of cylinders are stated as typeclasses `Cylinder.IsGood`
and `Cylinder.IsVeryGood`.

The existence of very good cylinder objects in model categories is stated
in the lemma `Cylinder.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/cylinder+object

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- A precylinder for `A : C` is the data of a morphism
`π : I ⟶ A` equipped with two sections. -/
structure Precylinder (A : C) where
  /-- the underlying object of a (pre)cylinder -/
  I : C
  /-- the first "inclusion" in the (pre)cylinder -/
  i₀ : A ⟶ I
  /-- the second "inclusion" in the (pre)cylinder -/
  i₁ : A ⟶ I
  /-- the codiagonal of the (pre)cylinder -/
  π : I ⟶ A
  i₀_π : i₀ ≫ π = 𝟙 A := by cat_disch
  i₁_π : i₁ ≫ π = 𝟙 A := by cat_disch

namespace Precylinder

attribute [reassoc (attr := simp)] i₀_π i₁_π

variable {A : C} (P : Precylinder A)

/-- The precylinder object obtained by switching the two inclusions. -/
@[simps]
def symm : Precylinder A where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two precylinders. -/
@[simps]
noncomputable def trans (P' : Precylinder A) [HasPushout P.i₁ P'.i₀] :
    Precylinder A where
  I := pushout P.i₁ P'.i₀
  i₀ := P.i₀ ≫ pushout.inl _ _
  i₁ := P'.i₁ ≫ pushout.inr _ _
  π := pushout.desc P.π P'.π (by simp)

section

variable [HasBinaryCoproduct A A]

/-- the map from the coproduct of two copies of `A` to `P.I`, when `P` is
a cylinder object for `A`. `P` shall be a *good* cylinder object
when this morphism is a cofibration. -/
noncomputable def i : A ⨿ A ⟶ P.I := coprod.desc P.i₀ P.i₁

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_i : coprod.inl ≫ P.i = P.i₀ := by simp [i]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_i : coprod.inr ≫ P.i = P.i₁ := by simp [i]

end

@[simp, reassoc]
lemma symm_i [HasBinaryCoproducts C] : P.symm.i = (coprod.braiding A A).hom ≫ P.i := by cat_disch

end Precylinder

/-- In a category with weak equivalences, a cylinder is the
data of a weak equivalence `π : I ⟶ A` equipped with two sections -/
structure Cylinder [CategoryWithWeakEquivalences C] (A : C) extends Precylinder A where
  weakEquivalence_π : WeakEquivalence π := by infer_instance

namespace Cylinder

attribute [instance] weakEquivalence_π

section

variable {A : C} [CategoryWithWeakEquivalences C] (P : Cylinder A)

/-- The cylinder object obtained by switching the two inclusions. -/
@[simps!]
def symm : Cylinder A where
  __ := P.toPrecylinder.symm
  weakEquivalence_π := by dsimp; infer_instance

@[simp, reassoc]
lemma symm_i [HasBinaryCoproducts C] :
    P.symm.i = (coprod.braiding A A).hom ≫ P.i :=
  P.toPrecylinder.symm_i

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

instance : WeakEquivalence P.i₀ :=
  weakEquivalence_of_postcomp_of_fac P.i₀_π

instance : WeakEquivalence P.i₁ :=
  weakEquivalence_of_postcomp_of_fac P.i₁_π

end

/-- A cylinder object `P` is good if the morphism
`P.i : A ⨿ A ⟶ P.I` is a cofibration. -/
class IsGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C] : Prop where
  cofibration_i : Cofibration P.i := by infer_instance

/-- A good cylinder object `P` is very good if `P.π` is a (trivial) fibration. -/
class IsVeryGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
    [CategoryWithFibrations C] : Prop extends P.IsGood where
  fibration_π : Fibration P.π := by infer_instance

attribute [instance] IsGood.cofibration_i IsVeryGood.fibration_π

section

variable [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  [HasInitial C] [(cofibrations C).IsStableUnderComposition]
  [(cofibrations C).IsStableUnderCobaseChange]
  [IsCofibrant A] [P.IsGood]

instance : Cofibration P.i₀ := by
  rw [← P.inl_i]
  infer_instance

instance : Cofibration P.i₁ := by
  rw [← P.inr_i]
  infer_instance

instance : IsCofibrant P.I :=
  isCofibrant_of_cofibration P.i₀

end

instance [HasBinaryCoproducts C] [CategoryWithCofibrations C] [P.IsGood]
    [(cofibrations C).RespectsIso] : P.symm.IsGood where
  cofibration_i := by
    have hi : cofibrations C P.i := by rw [← cofibration_iff]; infer_instance
    rw [P.symm_i, cofibration_iff]
    refine ((cofibrations C).arrow_mk_iso_iff ?_).2 hi
    exact Arrow.isoMk (coprod.braiding A A) (Iso.refl _)

section

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [(fibrations C).IsStableUnderComposition]

instance [HasBinaryCoproduct A A] [HasTerminal C] [IsFibrant A] [P.IsVeryGood] : IsFibrant P.I :=
  isFibrant_of_fibration P.π

instance [(cofibrations C).RespectsIso] [HasBinaryCoproducts C] [P.IsVeryGood] :
    P.symm.IsVeryGood where
  fibration_π := by dsimp; infer_instance

end

end

variable [ModelCategory C] {A : C} (P : Cylinder A)

section

variable (h : MorphismProperty.MapFactorizationData (cofibrations C) (trivialFibrations C)
    (codiag A))

set_option backward.isDefEq.respectTransparency false in
/-- A cylinder object for `A` can be obtained from a factorization of the obvious
map `A ⨿ A ⟶ A` as a cofibration followed by a trivial fibration. -/
@[simps]
noncomputable def ofFactorizationData : Cylinder A where
  I := h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  π := h.p

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ofFactorizationData_i : (ofFactorizationData h).i = h.i := by cat_disch

instance : (ofFactorizationData h).IsVeryGood where
  cofibration_i := by simpa using inferInstanceAs (Cofibration h.i)
  fibration_π := by dsimp; infer_instance

instance [HasTerminal C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
    IsFibrant (ofFactorizationData h).I :=
  isFibrant_of_fibration (ofFactorizationData h).π

end

variable (A) in
lemma exists_very_good :
    ∃ (P : Cylinder A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

instance : Nonempty (Cylinder A) := ⟨(exists_very_good A).choose⟩

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two good cylinders. -/
@[simps!]
noncomputable def trans [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood] :
    Cylinder A where
  __ := P.toPrecylinder.trans P'.toPrecylinder
  weakEquivalence_π := by
    have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
        pushout.desc P.π P'.π (by simp)) := by
      simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
        Precylinder.i₀_π]
      infer_instance
    dsimp
    apply weakEquivalence_of_precomp (P.i₀ ≫ pushout.inl _ _)

set_option backward.isDefEq.respectTransparency false in
instance [IsCofibrant A] (P P' : Cylinder A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  cofibration_i := by
    let ψ : P.I ⨿ A ⟶ (P.trans P').I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show (P.trans P').i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Precylinder.i, ψ]]
    have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = P'.i ≫ pushout.inr _ _ := by
      ext
      · simp [ψ, pushout.condition]
      · simp [ψ]
    have sq : IsPushout P.i₁ (coprod.inl ≫ P'.i) (coprod.inl ≫ ψ) (pushout.inr _ _) := by
      simpa [ψ] using IsPushout.of_hasPushout P.i₁ P'.i₀
    have : Cofibration ψ := by
      rw [cofibration_iff]
      exact (cofibrations C).of_isPushout
        (IsPushout.of_top sq fac (IsPushout.of_coprod_inl_with_id P.i₁ A).flip)
        (by rw [← cofibration_iff]; infer_instance)
    infer_instance

end Cylinder

end HomotopicalAlgebra
