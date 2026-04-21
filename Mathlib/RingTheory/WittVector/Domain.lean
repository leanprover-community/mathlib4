/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.Identities

/-!

# Witt vectors over a domain

This file builds to the proof `WittVector.instIsDomain`,
an instance that says if `R` is an integral domain, then so is `𝕎 R`.
It depends on the API around iterated applications
of `WittVector.verschiebung` and `WittVector.frobenius`
found in `Identities.lean`.

The [proof sketch](https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723)
goes as follows:
any nonzero $x$ is an iterated application of $V$
to some vector $w_x$ whose 0th component is nonzero (`WittVector.verschiebung_nonzero`).
Known identities (`WittVector.iterate_verschiebung_mul`) allow us to transform
the product of two such $x$ and $y$
to the form $V^{m+n}\left(F^n(w_x) \cdot F^m(w_y)\right)$,
the 0th component of which must be nonzero.

## Main declarations

* `WittVector.iterate_verschiebung_mul_coeff` : an identity from [Haze09]
* `WittVector.instIsDomain`

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

namespace WittVector

open Function

variable {p : ℕ} {R : Type*}

local notation "𝕎" => WittVector p -- type as `\bbW`

/-!
## The `shift` operator
-/


/--
`WittVector.verschiebung` translates the entries of a Witt vector upward, inserting 0s in the gaps.
`WittVector.shift` does the opposite, removing the first entries.
This is mainly useful as an auxiliary construction for `WittVector.verschiebung_nonzero`.
-/
def shift (x : 𝕎 R) (n : ℕ) : 𝕎 R :=
  @mk' p R fun i => x.coeff (n + i)

theorem shift_coeff (x : 𝕎 R) (n k : ℕ) : (x.shift n).coeff k = x.coeff (n + k) :=
  rfl

variable [hp : Fact p.Prime] [CommRing R]

theorem verschiebung_shift (x : 𝕎 R) (k : ℕ) (h : ∀ i < k + 1, x.coeff i = 0) :
    verschiebung (x.shift k.succ) = x.shift k := by
  ext ⟨j⟩
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_self
  · simp only [verschiebung_coeff_succ, shift]
    congr 1
    rw [Nat.add_succ, add_comm, Nat.add_succ, add_comm]

theorem eq_iterate_verschiebung {x : 𝕎 R} {n : ℕ} (h : ∀ i < n, x.coeff i = 0) :
    x = verschiebung^[n] (x.shift n) := by
  induction n with
  | zero => cases x; simp [shift]
  | succ k ih =>
    dsimp; rw [verschiebung_shift]
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
    · exact h

theorem verschiebung_nonzero {x : 𝕎 R} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ x' : 𝕎 R, x'.coeff 0 ≠ 0 ∧ x = verschiebung^[n] x' := by
  classical
  have hex : ∃ k : ℕ, x.coeff k ≠ 0 := by
    by_contra! hall
    apply hx
    ext i
    simp only [hall, zero_coeff]
  let n := Nat.find hex
  use n, x.shift n
  refine ⟨Nat.find_spec hex, eq_iterate_verschiebung fun i hi => not_not.mp ?_⟩
  exact Nat.find_min hex hi

/-!
## Witt vectors over a domain

If `R` is an integral domain, then so is `𝕎 R`.
This argument is adapted from
<https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723>.
-/


instance [CharP R p] [NoZeroDivisors R] : NoZeroDivisors (𝕎 R) :=
  ⟨fun {x y} => by
    contrapose!
    rintro ⟨ha, hb⟩
    rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, rfl⟩
    rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, rfl⟩
    refine ne_of_apply_ne (fun x => x.coeff (na + nb)) ?_
    dsimp only
    rw [iterate_verschiebung_mul_coeff, zero_coeff]
    exact mul_ne_zero (pow_ne_zero _ hwa0) (pow_ne_zero _ hwb0)⟩

instance instIsDomain [CharP R p] [IsDomain R] : IsDomain (𝕎 R) :=
  NoZeroDivisors.to_isDomain _

end WittVector
