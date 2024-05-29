/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!

# Cartesian morphisms

This file defines cartesian resp. strongly cartesian morphisms in a based category.

## Main definitions
- `IsCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to `p`.
This structure extends `IsHomLift p f φ`.
- `IsStronglyCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to
`p`. This structure also extends `IsHomLift p f φ`.

## Implementation
The standard constructor of `IsStronglyCartesian` has both been renamed to `.mk'`, and we
have provided an alternate constructor `IsStronglyCartesian.mk`. The difference between the two
is that `IsStronglyCartesian.mk` peforms some substitutions of superfluous variables for the user.
It is recommended to use these instead to minimize the amount of equalities that needs to be carried
around in the construction.

## References
SGA 1
Stacks project
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The proposition that a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
is a cartesian arrow, see SGA 1, VI.5.1.
-/
class Functor.IsCartesian (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) extends
    IsHomLift p f φ : Prop where
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'

/-- The proposition that a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
is a strongly cartesian arrow, see STACKS PROJECT. -/
class Functor.IsStronglyCartesian (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    extends IsHomLift p f φ : Prop where mk' ::
  universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S)
    (_ : f' = g ≫ f) (φ' : a' ⟶ b) [IsHomLift p f' φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'

protected lemma IsStronglyCartesian.mk {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : b ⟶ a}
    [IsHomLift p f φ] (h : ∀ (a' : 𝒳) (g : p.obj a' ⟶ R) (φ' : a' ⟶ a), IsHomLift p (g ≫ f) φ' →
      ∃! χ : a' ⟶ b, IsHomLift p g χ ∧ χ ≫ φ = φ') : IsStronglyCartesian p f φ where
  universal_property := by
    intro R' a' g f' hf' φ' hφ'
    subst_hom_lift p f' φ'
    apply h a' g φ' (hf' ▸ inferInstance)

instance cartesian_of_stronglyCartesian (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] : p.IsCartesian f φ where
  universal_property := fun φ' =>
    IsStronglyCartesian.universal_property (φ:=φ) (f:=f) (𝟙 R) f (by simp) φ'


namespace IsCartesian

/-- Given an arrow `φ' : a' ⟶ b` and a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' ====== R --f--> S
```
such that `φ` is a cartesian arrow, then `inducedMap f φ φ'` is the map `a' ⟶ a`
obtained from the universal property of `φ`. -/
noncomputable def inducedMap (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ'

instance inducedMap_isHomLift (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      IsHomLift p (𝟙 R) (inducedMap p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.1

@[simp]
lemma inducedMap_comp (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      (inducedMap p f φ φ') ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.2

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' ====== R --f--> S
```
with `φ` a cartesian arrow. Then for any arrow `φ' : a' ⟶ b`, and `ψ : a' ⟶ a` such that
`g ≫ ψ = φ'`. Then `ψ` is the map induced by the universal property of `φ`. -/
lemma inducedMap_unique (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']
    (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = inducedMap p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').2
    ψ ⟨inferInstance, hψ⟩

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' ====== R --f--> S
```
with `φ` a cartesian arrow. Then for any arrow `φ' : a' ⟶ b`, any two arrows `ψ ψ' : a' ⟶ a` such
that `g ≫ ψ = φ' = g ≫ ψ'`. Then `ψ = ψ'`. -/
protected lemma uniqueness (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] {ψ ψ' : a' ⟶ a}
    [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ'] (hcomp : ψ ≫ φ = φ') (hcomp' : ψ' ≫ φ = φ') :
      ψ = ψ' := by
  rw [inducedMap_unique p f φ φ' ψ hcomp, inducedMap_unique p f φ φ' ψ' hcomp']

@[simp]
lemma inducedMap_self_eq_id (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] : inducedMap p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply inducedMap_unique
  simp only [id_comp]

/-- The canonical isomorphism between the domains of two cartesian arrows
lying over the same object. -/
@[simps]
noncomputable def naturalIso (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    (φ' : a' ⟶ b) [IsCartesian p f φ] [IsCartesian p f φ'] : a' ≅ a where
  hom := inducedMap p f φ φ'
  inv := inducedMap p f φ' φ
  -- TODO: simplify
  hom_inv_id := by
    have : p.IsHomLift (𝟙 R) (𝟙 a') := by apply IsHomLift.id (domain_eq p f φ')
    apply IsCartesian.uniqueness p f φ' φ' (by simp) (id_comp _)
  inv_hom_id := by
    have : p.IsHomLift (𝟙 R) (𝟙 a) := by apply IsHomLift.id (domain_eq p f φ)
    apply IsCartesian.uniqueness p f φ φ (by simp) (id_comp _)

end IsCartesian
