/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The factorization lemma by K. S. Brown

In a model category, any morphism `f : X ⟶ Y` between
cofibrant objects can be factored as `i ≫ p`
with `i` a cofibration and `p` a trivial fibration
which has a section `s` that is a cofibration.
In order to state this, we introduce a structure
`CofibrantBrownFactorization f` with the data
of such morphisms `i`, `p` and `s` with the expected
properties, and show it is nonempty.
Moreover, if `f` is a weak equivalence, then all the
morphisms `i`, `p` and `s` are weak equivalences.
(We also obtain the dual results about morphisms
between fibrant objects.)

## References
* [Brown, Kenneth S., *Abstract homotopy theory and generalized sheaf cohomology*, §I.1][brown-1973]

-/

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C]
  {X Y : C} (f : X ⟶ Y)

/-- Given a morphism `f : X ⟶ Y` in a model category,
this structure contains the data of a factorization `i ≫ p = f`
with `i` a cofibration, `p` a trivial fibration which
has a section `s` that is a cofibration.
That this structure is nonempty when `X`
and `Y` are cofibrant is Ken Brown's factorization lemma. -/
structure CofibrantBrownFactorization extends
    MapFactorizationData (cofibrations C) (trivialFibrations C) f where
  /-- a cofibration that is a section of `p` -/
  s : Y ⟶ Z
  s_p : s ≫ p = 𝟙 Y := by cat_disch
  cofibration_s : Cofibration s := by infer_instance

namespace CofibrantBrownFactorization

attribute [reassoc (attr := simp)] s_p
attribute [instance] cofibration_s

variable (h : CofibrantBrownFactorization f)

instance [WeakEquivalence f] : WeakEquivalence h.i :=
  weakEquivalence_of_postcomp_of_fac h.fac

instance : WeakEquivalence h.s :=
  weakEquivalence_of_postcomp_of_fac h.s_p

/-- The term in `CofibrantBrownFactorization f` that is deduced from
a factorization of `coprod.desc f (𝟙 Y) : X ⨿ Y ⟶ Y`
as a cofibration followed by a trivial fibration. -/
@[simps]
noncomputable def mk' [IsCofibrant X] [IsCofibrant Y]
    (h : MapFactorizationData (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y))) :
    CofibrantBrownFactorization f where
  Z := h.Z
  i := coprod.inl ≫ h.i
  p := h.p
  s := coprod.inr ≫ h.i
  hi := by rw [← cofibration_iff]; infer_instance
  hp := by rw [mem_trivialFibrations_iff]; constructor <;> infer_instance

variable (h : MapFactorizationData (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y)))

instance [IsCofibrant X] [IsCofibrant Y] :
    Nonempty (CofibrantBrownFactorization f) :=
  ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

end CofibrantBrownFactorization

/-- Given a morphism `f : X ⟶ Y` in a model category,
this structure contains the data of a factorization `i ≫ p = f`
with `p` a fibration, `i` a trivial cofibration which
has a retraction `r` that is a fibration.
That this structure is nonempty when `X`
and `Y` are fibrant is Ken Brown's factorization lemma. -/
structure FibrantBrownFactorization extends
    MapFactorizationData (trivialCofibrations C) (fibrations C) f where
  /-- a fibration that is a retraction of `i` -/
  r : Z ⟶ X
  i_r : i ≫ r = 𝟙 X := by cat_disch
  fibration_r : Fibration r := by infer_instance

namespace FibrantBrownFactorization

attribute [reassoc (attr := simp)] i_r
attribute [instance] fibration_r

variable (h : FibrantBrownFactorization f)

instance [WeakEquivalence f] : WeakEquivalence h.p :=
  weakEquivalence_of_precomp_of_fac h.fac

instance : WeakEquivalence h.r :=
  weakEquivalence_of_precomp_of_fac h.i_r

/-- The term in `CofibrantBrownFactorization f` that is deduced from
a factorization of `prod.lift f (𝟙 X) : X ⟶ Y ⨯ X`
as a cofibration followed by a trivial fibration. -/
@[simps]
noncomputable def mk' [IsFibrant X] [IsFibrant Y]
    (h : MapFactorizationData (trivialCofibrations C) (fibrations C) (prod.lift f (𝟙 X))) :
    FibrantBrownFactorization f where
  Z := h.Z
  i := h.i
  p := h.p ≫ prod.fst
  r := h.p ≫ prod.snd
  hi := by rw [mem_trivialCofibrations_iff]; constructor <;> infer_instance
  hp := by rw [← fibration_iff]; infer_instance

instance [IsFibrant X] [IsFibrant Y] :
    Nonempty (FibrantBrownFactorization f) :=
  ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

end FibrantBrownFactorization

end HomotopicalAlgebra
