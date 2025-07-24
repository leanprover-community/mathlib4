/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The lemma by K. S. Brown

In a model category, any morphism `f : X ⟶ Y` between
cofibrant objects can be factored as `i ≫ j`
with `i` a cofibration and `j` a trivial fibration
which has a section `s` that is a cofibration.
In order to state this, we introduce a structure
`CofibrantBrownFactorization f` with the data
of such morphisms `i`, `j` and `s` with the expected
properties, and show it is nonempty.
Moreover, if `f` is a weak equivalence, then all the
morphisms `i`, `j` and `s` are weak equivalences.
(We also obtain the dual results about morphisms
between fibrant objects.)

-/

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C]
  {X Y : C} (f : X ⟶ Y)

/-- Given a morphism `f : X ⟶ Y` in a model category,
this structure contains the data of a factorization `i ≫ j = f`
with `i` a cofibration, `j` a trivial fibration which
has a section `s` that is a cofibration.
That this structure is nonempty when `X`
and `Y` are cofibrant is Ken Brown's lemma. -/
structure CofibrantBrownFactorization where
  /-- the auxiliary object in the factorization -/
  obj : C
  /-- the cofibration -/
  i : X ⟶ obj
  /-- the trivial fibration -/
  j : obj ⟶ Y
  fac : i ≫ j = f := by aesop_cat
  /-- the section of `j` that is cofibration -/
  s : Y ⟶ obj
  s_j : s ≫ j = 𝟙 Y := by aesop_cat
  cofibration_i : Cofibration i := by infer_instance
  fibration_j : Fibration j := by infer_instance
  cofibration_s : Cofibration s := by infer_instance
  weakEquivalence_j : WeakEquivalence j := by infer_instance

namespace CofibrantBrownFactorization

attribute [reassoc (attr := simp)] fac s_j
attribute [instance] cofibration_i fibration_j cofibration_s
  weakEquivalence_j

section

variable (h : CofibrantBrownFactorization f)

instance [WeakEquivalence f] : WeakEquivalence h.i :=
  weakEquivalence_of_postcomp_of_fac h.fac

instance : WeakEquivalence h.s :=
  weakEquivalence_of_postcomp_of_fac h.s_j

end

/-- The term in `CofibrantBrownFactorization f` that is deduced from
a factorization of `coprod.desc f (𝟙 Y) : X ⨿ Y ⟶ Y`
as a cofibration followed by a trivial fibration. -/
@[simps]
noncomputable def mk' [IsCofibrant X] [IsCofibrant Y]
    (h : MapFactorizationData (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y))) :
    CofibrantBrownFactorization f where
  obj := h.Z
  i := coprod.inl ≫ h.i
  j := h.p
  s := coprod.inr ≫ h.i

instance [IsCofibrant X] [IsCofibrant Y] :
    Nonempty (CofibrantBrownFactorization f) :=
  ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

end CofibrantBrownFactorization

/-- Given a morphism `f : X ⟶ Y` in a model category,
this structure contains the data of a factorization `i ≫ j = f`
with `j` a fibration, `i` a trivial cofibration which
has a retraction `r` that is a fibration.
That this structure is nonempty when `X`
and `Y` are fibrant is Ken Brown's lemma. -/
structure FibrantBrownFactorization where
  /-- the auxiliary object in the factorization -/
  obj : C
  /-- the trivial cofibration -/
  i : X ⟶ obj
  /-- the fibration -/
  j : obj ⟶ Y
  fac : i ≫ j = f := by aesop_cat
  /-- the retraction of `i` that is fibration -/
  r : obj ⟶ X
  i_r : i ≫ r = 𝟙 X := by aesop_cat
  cofibration_i : Cofibration i := by infer_instance
  fibration_j : Fibration j := by infer_instance
  fibration_r : Fibration r := by infer_instance
  weakEquivalence_i : WeakEquivalence i := by infer_instance

namespace FibrantBrownFactorization

attribute [reassoc (attr := simp)] fac i_r
attribute [instance] cofibration_i fibration_j fibration_r
  weakEquivalence_i

section

variable (h : FibrantBrownFactorization f)

instance [WeakEquivalence f] : WeakEquivalence h.j :=
  weakEquivalence_of_precomp_of_fac h.fac

instance : WeakEquivalence h.r :=
  weakEquivalence_of_precomp_of_fac h.i_r

end

/-- The term in `CofibrantBrownFactorization f` that is deduced from
a factorization of `prod.lift f (𝟙 X) : X ⟶ Y ⨯ X`
as a cofibration followed by a trivial fibration. -/
@[simps]
noncomputable def mk' [IsFibrant X] [IsFibrant Y]
    (h : MapFactorizationData (trivialCofibrations C) (fibrations C) (prod.lift f (𝟙 X))) :
    FibrantBrownFactorization f where
  obj := h.Z
  i := h.i
  j := h.p ≫ prod.fst
  r := h.p ≫ prod.snd

instance [IsFibrant X] [IsFibrant Y] :
    Nonempty (FibrantBrownFactorization f) :=
  ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

end FibrantBrownFactorization

end HomotopicalAlgebra
