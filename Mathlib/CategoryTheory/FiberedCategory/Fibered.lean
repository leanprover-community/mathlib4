/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be (pre)fibered.

## Main definitions

- `IsPreFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
This means that any morphism in the base `𝒮` can be lifted to a cartesian morphism in `𝒳`.

## Implementation

The standard constructor of `IsPreFibered` has been renamed to `.mk'`, and we have provided an
alternate constructor `IsPreFibered.mk`, which peforms substitutions of some superfluous variables.
It is recommended to use these instead to minimize the amount of equalities that needs to be carried
around in the construction.

There are different notions of fibered categories in the literature, and another common definition
is the existence of strongly cartesian morphisms lying over any given morphism in the base. We also
provide an alternate constructor for `IsFibered` in this sense, see `IsFibered.of_has_pullbacks'`.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)

-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Definition of a prefibered category. SGA 1 VI.6.1. -/
class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  has_pullbacks' {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ

protected lemma IsPreFibered.has_pullbacks (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ := by
  subst ha; exact IsPreFibered.has_pullbacks' f

namespace IsPreFibered

open IsCartesian

variable {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)

/-- Given a prefibered category `p : 𝒳 ⥤ 𝒫`, and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
`pullbackObj` is defined as the domain `R ×_S a` of some cartesian arrow lying over
`f`, which exists by the fibered category structure on `p`. -/
noncomputable def pullbackObj : 𝒳 :=
  Classical.choose (IsPreFibered.has_pullbacks p ha f)

/-- Given a fibered category `p : 𝒳 ⥤ 𝒫`, and a diagram
```
          a
          -
          |
          v
R --f--> S
```
we get a map `R ×_S b ⟶ a` -/
noncomputable def pullbackMap : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreFibered.has_pullbacks p ha f))

instance pullbackMap.IsCartesian : IsCartesian p f (pullbackMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreFibered.has_pullbacks p ha f))

lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)

end IsPreFibered

end CategoryTheory
