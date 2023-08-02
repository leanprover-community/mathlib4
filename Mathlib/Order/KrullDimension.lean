/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/

import Mathlib.Order.RelSeries
import Mathlib.Order.WithBot
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Module.LocalizedModule

/-!
# Krull dimension of a preordered set

If `α` is a preordered set, then `krullDim α` is defined to be `sup {n | a₀ < a₁ < ... < aₙ}`.
In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to
be positive infinity.

For `a : α`, its height is defined to be the krull dimension of the subset `(-∞, a]` while its
coheight is defined to be the krull dimension of `[a, +∞)`.

## Implementation notes
Krull dimensions are defined to take value in `WithBot (WithTop ℕ)` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.
-/

variable (α : Type _) [Preorder α]

/--
Krull dimension of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` order by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim : WithBot (WithTop ℕ) :=
  ⨆ (p : LTSeries α), p.length

/--
Height of an element `a` of a preordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
noncomputable def height (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
noncomputable def coheight (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Ici a)

noncomputable

section Preorder

variable {α β : Type _}

variable [Preorder α] [Preorder β]

lemma krullDim_le_of_StrictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β := by
  exact iSup_le $ λ p ↦ le_sSup ⟨Map p f hf, rfl⟩

end Preorder

noncomputable

/-
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
def ringKrullDim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ringKrullDim S ≤ ringKrullDim R`.
-/
theorem le_of_Surj (R S : Type _) [CommRing R] [CommRing S] (f : R →+* S)
  (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R := by
{ refine' krullDim_le_of_StrictMono (PrimeSpectrum.comap f)
    (Monotone.strictMono_of_injective ?_ (PrimeSpectrum.comap_injective_of_surjective f hf))
  . intro a b hab
    change ((PrimeSpectrum.comap f) a).asIdeal ≤ ((PrimeSpectrum.comap f) b).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono hab }

/--
If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringDrullDim R`.
-/
theorem le_of_Quot (R : Type _) [CommRing R] (I : PrimeSpectrum R) :
  ringKrullDim (R ⧸ I.asIdeal) ≤ ringKrullDim R :=
le_of_Surj _ _ (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`.
-/
theorem eq_of_RingEquiv (R S : Type _) [CommRing R] [CommRing S] (e : R ≃+* S) :
  ringKrullDim R = ringKrullDim S :=
le_antisymm (le_of_Surj S R (RingEquiv.symm e) (EquivLike.surjective (RingEquiv.symm e)))
  (le_of_Surj R S e (EquivLike.surjective e))

end ringKrullDim
