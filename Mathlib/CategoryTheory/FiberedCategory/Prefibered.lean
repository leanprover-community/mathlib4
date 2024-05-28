/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be fibered`.

## Main definitions

- `IsCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to `p`.
This structure extends `IsHomLift p f φ`.
- `IsFibered p` expresses that `p` gives `𝒳` the structure of a fibered category over `𝒮`, i.e.
that for every morphism `f : S ⟶ R` in `𝒮` and every object `b` in `𝒳` with `p(b)=R` there is a
cartesian arrow `φ : a ⟶ b`  of `f`.

## Implementation
The standard constructors of `IsCartesian` and `IsFibered` have both been renamed to `.mk'`. We have
provided alternate lemmas `IsCartesian.mk` and `IsFibered.mk` for constructing instances of these
structures, and it is recommended to use these instead to minimize the amount of equalities that
needs to be carried around in the construction.

The reason for this is the following:
Just like `IsHomLift p f φ`, we have phrased `IsCartesian p f φ` in a way to make its usage as
flexible  as possible with respect to non-definitional equalities of domains / codomains.
In particular, given a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
(by which we mean an object of `IsHomLift p f φ`). We say that it is cartesian if for all arrows
`g : R' ⟶ R`, and all lifts
```
  a' --φ'--> b
  -          -
  |          |
  v          v
  R' --f'--> S
```
such that `f' = g ≫ f`, there is a unique induced map `τ : a' ⟶ a` lifting `g` and such that
`τ ≫ φ = φ'`. This definition gives us some flexibility in that it allows us to take `f'` to be
non-definitionally equal to `g ≫ f`, and `p(a')` to be non-definitionally equal to `R'`.
`IsCartesian.mk` only requires us to check this condition for `f' = g ≫ f` and `R=p(a')`.

Similarly, `IsFibered p` is phrased as saying that for every `f : R ⟶ S`, and every `a` such that
`p(a)=S`, there is a cartesian arrow `φ` lying over `f`. The alternate constructor `IsFibered.mk`
only requires us to construct this arrow for every `a` and every `f : R ⟶ p(a)`.
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

/-- Definition of a prefibered category. SGA 1 VI.6.1. -/
class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where mk' ::
  has_pullbacks {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ

protected lemma IsPreFibered.mk (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
    ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ) : IsPreFibered p where
  has_pullbacks := @fun a R S ha f => by subst ha; apply h a R f

/-- Definition of a fibered category. SGA 1 VI.6.1. -/
class Functor.IsFibered (p : 𝒳 ⥤ 𝒮) extends IsPreFibered p : Prop where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ)

-- IsFibered.mk' in terms of strongly cartesian arrows?
-- protected lemma IsFibered.mk (p : 𝒳 ⥤ 𝒮) (h₁ : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
--     ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ) : IsPreFibered p where
--   has_pullbacks := @fun a R S ha f => by subst ha; apply h₁ a R f

end CategoryTheory
