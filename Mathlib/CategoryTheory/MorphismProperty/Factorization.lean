/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The factorization axiom

In this file, we introduce a type-class `HasFactorization W₁ W₂`, which, given
two classes of morphisms `W₁` and `W₂` in a category `C`, asserts that any morphism
in `C` can be factored as a morphism in `W₁` followed by a morphism in `W₂`. The data
of such factorizations can be packaged in the type `FactorizationData W₁ W₂`.

This shall be used in the formalization of model categories for which the CM5 axiom
asserts that any morphism can be factored as a cofibration followed by a trivial
fibration (or a trivial cofibration followed by a fibration).

We also provide a structure `FunctorialFactorizationData W₁ W₂` which contains
the data of a functorial factorization as above. With this design, when we
formalize certain constructions (e.g. cylinder objects in model categories),
we may first construct them using using `data : FactorizationData W₁ W₂`.
Without duplication of code, it shall be possible to show these cylinders
are functorial when a term `data : FunctorialFactorizationData W₁ W₂` is available,
the existence of which is asserted in the type-class `HasFunctorialFactorization W₁ W₂`.

-/

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C] (W₁ W₂ : MorphismProperty C)

/-- Given two classes of morphisms `W₁` and `W₂` on a category `C`, this is
the data of the factorization of a morphism `f : X ⟶ Y` as `i ≫ p` with
`W₁ i` and `W₂ p`. -/
structure MapFactorizationData {X Y : C} (f : X ⟶ Y) where
  /-- the intermediate object in the factorization -/
  Z : C
  /-- the first morphism in the factorization -/
  i : X ⟶ Z
  /-- the second morphism in the factorization -/
  p : Z ⟶ Y
  fac : i ≫ p = f := by aesop_cat
  hi : W₁ i
  hp : W₂ p

/-- The data of a term in `MapFactorizationData W₁ W₂ f` for any morphism `f`. -/
abbrev FactorizationData := ∀ {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f

/-- The factorization axiom for two classes of morphisms `W₁` and `W₂` in a category `C`. It
asserts that any morphism can be factored as a morphism in `W₁` followed by a morphism
in `W₂`. -/
class HasFactorization : Prop where
  nonempty_mapFactorizationData {X Y : C} (f : X ⟶ Y) : Nonempty (MapFactorizationData W₁ W₂ f)

/-- A chosen term in `FactorizationData W₁ W₂` when `HasFactorization W₁ W₂` holds. -/
noncomputable def factorizationData [HasFactorization W₁ W₂] : FactorizationData W₁ W₂ :=
  fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)

/-- The data of a functorial factorization of any morphism in `C` as a morphism in `W₁`
followed by a morphism in `W₂`. -/
structure FunctorialFactorizationData where
  /-- the intermediate objects in the factorizations -/
  Z : Arrow C ⥤ C
  /-- the first morphism in the factorizations -/
  i : Arrow.leftFunc ⟶ Z
  /-- the second morphism in the factorizations -/
  p : Z ⟶ Arrow.rightFunc
  fac : i ≫ p = Arrow.leftToRight := by aesop_cat
  hi (f : Arrow C) : W₁ (i.app f)
  hp (f : Arrow C) : W₂ (p.app f)

namespace FunctorialFactorizationData

variable {W₁ W₂}
variable (data : FunctorialFactorizationData W₁ W₂)

attribute [reassoc (attr := simp)] fac

@[reassoc (attr := simp)]
lemma fac_app {f : Arrow C} : data.i.app f ≫ data.p.app f = f.hom := by
  rw [← NatTrans.comp_app, fac,Arrow.leftToRight_app]

/-- The term in `FactorizationData W₁ W₂` that is deduced from a functorial factorization. -/
def factorizationData : FactorizationData W₁ W₂ := fun f =>
  { i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }

section

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g)

/-- When `data : FunctorialFactorizationData W₁ W₂`, this is the
morphism `(data.factorizationData f).Z ⟶ (data.factorizationData g).Z` expressing the
functoriality of the intermediate objects of the factorizations
for `φ : Arrow.mk f ⟶ Arrow.mk g`. -/
def mapZ : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z := data.Z.map φ

@[reassoc (attr := simp)]
lemma i_mapZ :
    (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.factorizationData g).i :=
  (data.i.naturality φ).symm

@[reassoc (attr := simp)]
lemma mapZ_p :
    data.mapZ φ ≫ (data.factorizationData g).p = (data.factorizationData f).p ≫ φ.right :=
  data.p.naturality φ

variable (f) in
@[simp]
lemma mapZ_id : data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _ :=
  data.Z.map_id _

@[reassoc, simp]
lemma mapZ_comp {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    data.mapZ (φ ≫ ψ) = data.mapZ φ ≫ data.mapZ ψ :=
  data.Z.map_comp _ _

end

end FunctorialFactorizationData

/-- The functorial factorization axiom for two classes of morphisms `W₁` and `W₂` in a
category `C`. It asserts that any morphism can be factored in a functorial manner
as a morphism in `W₁` followed by a morphism in `W₂`. -/
class HasFunctorialFactorization : Prop where
  nonempty_functorialFactorizationData : Nonempty (FunctorialFactorizationData W₁ W₂)

/-- A chosen term in `FunctorialFactorizationData W₁ W₂` when the functorial factorization
axiom `HasFunctorialFactorization W₁ W₂` holds. -/
noncomputable def functorialFactorizationData [HasFunctorialFactorization W₁ W₂] :
    FunctorialFactorizationData W₁ W₂ :=
  Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)

instance [HasFunctorialFactorization W₁ W₂] : HasFactorization W₁ W₂ where
  nonempty_mapFactorizationData f := ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩

end MorphismProperty

end CategoryTheory
