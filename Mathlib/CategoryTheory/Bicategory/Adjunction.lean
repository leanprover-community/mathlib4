/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Adjunctions in bicategories

For 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjunction between `f` and `g`
consists of a pair of 2-morphism `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategory.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.mkOfAdjointifyCounit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.

## Implementation notes

The computation of 2-morphisms in the proof is done using `calc` blocks. Typically,
the LHS and the RHS in each step of `calc` are related by simple rewriting up to associators
and unitors. So the proof for each step should be of the form `rw [...]; coherence`. In practice,
our proofs look like `rw [...]; simp [bicategoricalComp]; coherence`. The `simp` is not strictly
necessary, but it speeds up the proof and allow us to avoid increasing the `maxHeartbeats`.
The speedup is probably due to reducing the length of the expression e.g. by absorbing
identity maps or applying the pentagon relation. Such a hack may not be necessary if the
coherence tactic is improved. One possible way would be to perform such a simplification in the
preprocessing of the coherence tactic.

## Todo

* `Bicategory.mkOfAdjointifyUnit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.
-/

namespace CategoryTheory

namespace Bicategory

open Category

open scoped Bicategory

open Mathlib.Tactic.BicategoryCoherence (bicategoricalComp bicategoricalIsoComp)

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

/-- The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
def leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  η ▷ f ⊗≫ f ◁ ε

/-- The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
def rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η ⊗≫ ε ▷ g

/-- Adjunction between two 1-morphisms. -/
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  /-- The unit of an adjunction. -/
  unit : 𝟙 a ⟶ f ≫ g
  /-- The counit of an adjunction. -/
  counit : g ≫ f ⟶ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzag unit counit = (λ_ _).hom ≫ (ρ_ _).inv := by aesop_cat
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (λ_ _).inv := by aesop_cat

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

attribute [local simp] leftZigzag rightZigzag

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by dsimp; coherence
  right_triangle := by dsimp; coherence

instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

theorem left_adjoint_uniq_aux {f₁ f₂ : a ⟶ b} {g : b ⟶ a} (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) :
    (𝟙 f₁ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ f₂ ◁ adj₁.counit ⊗≫ 𝟙 f₂) ≫
        𝟙 f₂ ⊗≫ adj₁.unit ▷ f₂ ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁ =
      𝟙 f₁ := by
  calc
    _ = 𝟙 f₁ ⊗≫
          adj₂.unit ▷ f₁ ⊗≫
            (𝟙 a ◁ f₂ ◁ adj₁.counit ≫ adj₁.unit ▷ (f₂ ≫ 𝟙 b)) ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁ := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 f₁ ⊗≫
          (𝟙 a ◁ adj₂.unit ≫ adj₁.unit ▷ (f₂ ≫ g)) ▷ f₁ ⊗≫
            f₁ ◁ ((g ≫ f₂) ◁ adj₁.counit ≫ adj₂.counit ▷ 𝟙 b) ⊗≫ 𝟙 f₁ := by
      rw [whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = 𝟙 f₁ ⊗≫
          adj₁.unit ▷ f₁ ⊗≫
            f₁ ◁ (rightZigzag adj₂.unit adj₂.counit) ▷ f₁ ⊗≫ f₁ ◁ adj₁.counit ⊗≫ 𝟙 f₁ := by
      simp_rw [whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = 𝟙 f₁ ⊗≫ (leftZigzag adj₁.unit adj₁.counit) ⊗≫ 𝟙 f₁ := by
      rw [right_triangle]; simp [bicategoricalComp]; coherence
    _ = _ := by
      rw [left_triangle]; simp [bicategoricalComp]

theorem right_adjoint_uniq_aux {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) :
    (𝟙 g₁ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ adj₁.counit ▷ g₂ ⊗≫ 𝟙 g₂) ≫
        𝟙 g₂ ⊗≫ g₂ ◁ adj₁.unit ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁ =
      𝟙 g₁ := by
  calc
    _ = 𝟙 g₁ ⊗≫
          g₁ ◁ adj₂.unit ⊗≫
            (adj₁.counit ▷ (g₂ ≫ 𝟙 a) ≫ 𝟙 b ◁ g₂ ◁ adj₁.unit) ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁ := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 g₁ ⊗≫
          g₁ ◁ (adj₂.unit ▷ 𝟙 a ≫ (f ≫ g₂) ◁ adj₁.unit) ⊗≫
            (adj₁.counit ▷ (g₂ ≫ f) ≫ 𝟙 b ◁ adj₂.counit) ▷ g₁ ⊗≫ 𝟙 g₁ := by
      rw [← whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = 𝟙 g₁ ⊗≫
          g₁ ◁ adj₁.unit ⊗≫
            g₁ ◁ (leftZigzag adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ adj₁.counit ▷ g₁ ⊗≫ 𝟙 g₁ := by
      simp_rw [← whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = 𝟙 g₁ ⊗≫ (rightZigzag adj₁.unit adj₁.counit) ⊗≫ 𝟙 g₁ := by
      rw [left_triangle]; simp [bicategoricalComp]; coherence
    _ = _ := by
      rw [right_triangle]; coherence

/-- If `f₁` and `f₂` are both left adjoint to `g`, then they are isomorphic. -/
def leftAdjointUniq {f₁ f₂ : a ⟶ b} {g : b ⟶ a} (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) : f₁ ≅ f₂ where
  hom := 𝟙 f₁ ⊗≫ adj₂.unit ▷ f₁ ⊗≫ f₂ ◁ adj₁.counit ⊗≫ 𝟙 f₂
  inv := 𝟙 f₂ ⊗≫ adj₁.unit ▷ f₂ ⊗≫ f₁ ◁ adj₂.counit ⊗≫ 𝟙 f₁
  hom_inv_id := left_adjoint_uniq_aux adj₁ adj₂
  inv_hom_id := left_adjoint_uniq_aux adj₂ adj₁

/-- If `g₁` and `g₂` are both right adjoint to `f`, then they are isomorphic. -/
def rightAdjointUniq {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) : g₁ ≅ g₂ where
  hom := 𝟙 g₁ ⊗≫ g₁ ◁ adj₂.unit ⊗≫ adj₁.counit ▷ g₂ ⊗≫ 𝟙 g₂
  inv := 𝟙 g₂ ⊗≫ g₂ ◁ adj₁.unit ⊗≫ adj₂.counit ▷ g₁ ⊗≫ 𝟙 g₁
  hom_inv_id := right_adjoint_uniq_aux adj₁ adj₂
  inv_hom_id := right_adjoint_uniq_aux adj₂ adj₁

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

/-- The isomorphism version of `leftZigzag`. -/
def leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪⊗≫ whiskerLeftIso f ε

/-- The isomorphism version of `rightZigzag`. -/
def rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪⊗≫ whiskerRightIso ε g

attribute [local simp] leftZigzagIso rightZigzagIso leftZigzag rightZigzag

@[simp]
theorem leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom :=
  rfl

@[simp]
theorem rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom :=
  rfl

@[simp]
theorem leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm :=
  Iso.ext (leftZigzagIso_inv η ε)

@[simp]
theorem rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm :=
  Iso.ext (rightZigzagIso_inv η ε)

/-- An auxiliary definition for `mkOfAdjointifyCounit`. -/
def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso η (adjointifyCounit η ε) = λ_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; coherence
    _ = 𝟙 _ ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; simp [bicategoricalComp]
    _ = _ := by
      rw [Iso.inv_hom_id]; simp [bicategoricalComp]

/-- Adjoint equivalences between two objects. -/
structure Equivalence (a b : B) where
  /-- A 1-morphism in one direction. -/
  hom : a ⟶ b
  /-- A 1-morphism in the other direction. -/
  inv : b ⟶ a
  /-- The composition `hom ≫ inv` is isomorphic to the identity. -/
  unit : 𝟙 a ≅ hom ≫ inv
  /-- The composition `inv ≫ hom` is isomorphic to the identity. -/
  counit : inv ≫ hom ≅ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := by aesop_cat

@[inherit_doc] scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

/-- The identity 1-morphism is an equivalence. -/
def id (a : B) : a ≌ a := ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

instance : Inhabited (Equivalence a a) := ⟨id a⟩

/-- Construct an adjoint equivalence from 2-isomorphisms by upgrading `ε` to a counit. -/
def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

end Equivalence

end

end Bicategory

end CategoryTheory
