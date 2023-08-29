/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.RingTheory.WittVector.Identities

#align_import ring_theory.witt_vector.domain from "leanprover-community/mathlib"@"b1d911acd60ab198808e853292106ee352b648ea"

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


noncomputable section

open scoped Classical

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
#align witt_vector.shift WittVector.shift

theorem shift_coeff (x : 𝕎 R) (n k : ℕ) : (x.shift n).coeff k = x.coeff (n + k) :=
  rfl
#align witt_vector.shift_coeff WittVector.shift_coeff

variable [hp : Fact p.Prime] [CommRing R]

theorem verschiebung_shift (x : 𝕎 R) (k : ℕ) (h : ∀ i < k + 1, x.coeff i = 0) :
    verschiebung (x.shift k.succ) = x.shift k := by
  ext ⟨j⟩
  -- ⊢ coeff (↑verschiebung (shift x (Nat.succ k))) Nat.zero = coeff (shift x k) Na …
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    -- ⊢ k + Nat.zero < k + 1
    apply Nat.lt_succ_self
    -- 🎉 no goals
  · simp only [verschiebung_coeff_succ, shift]
    -- ⊢ coeff x (Nat.succ k + n✝) = coeff x (k + Nat.succ n✝)
    congr 1
    -- ⊢ Nat.succ k + n✝ = k + Nat.succ n✝
    rw [Nat.add_succ, add_comm, Nat.add_succ, add_comm]
    -- 🎉 no goals
#align witt_vector.verschiebung_shift WittVector.verschiebung_shift

theorem eq_iterate_verschiebung {x : 𝕎 R} {n : ℕ} (h : ∀ i < n, x.coeff i = 0) :
    x = verschiebung^[n] (x.shift n) := by
  induction' n with k ih
  -- ⊢ x = (↑verschiebung)^[Nat.zero] (shift x Nat.zero)
  · cases x; simp [shift]
    -- ⊢ { coeff := coeff✝ } = (↑verschiebung)^[Nat.zero] (shift { coeff := coeff✝ }  …
             -- 🎉 no goals
  · dsimp; rw [verschiebung_shift]
    -- ⊢ x = (↑verschiebung)^[k] (↑verschiebung (shift x (Nat.succ k)))
           -- ⊢ x = (↑verschiebung)^[k] (shift x k)
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
      -- 🎉 no goals
    · exact h
      -- 🎉 no goals
#align witt_vector.eq_iterate_verschiebung WittVector.eq_iterate_verschiebung

theorem verschiebung_nonzero {x : 𝕎 R} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ x' : 𝕎 R, x'.coeff 0 ≠ 0 ∧ x = verschiebung^[n] x' := by
  have hex : ∃ k : ℕ, x.coeff k ≠ 0 := by
    by_contra' hall
    apply hx
    ext i
    simp only [hall, zero_coeff]
  let n := Nat.find hex
  -- ⊢ ∃ n x', coeff x' 0 ≠ 0 ∧ x = (↑verschiebung)^[n] x'
  use n, x.shift n
  -- ⊢ coeff (shift x n) 0 ≠ 0 ∧ x = (↑verschiebung)^[n] (shift x n)
  refine' ⟨Nat.find_spec hex, eq_iterate_verschiebung fun i hi => not_not.mp _⟩
  -- ⊢ ¬¬coeff x i = 0
  exact Nat.find_min hex hi
  -- 🎉 no goals
#align witt_vector.verschiebung_nonzero WittVector.verschiebung_nonzero

/-!
## Witt vectors over a domain

If `R` is an integral domain, then so is `𝕎 R`.
This argument is adapted from
<https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723>.
-/


instance [CharP R p] [NoZeroDivisors R] : NoZeroDivisors (𝕎 R) :=
  ⟨fun {x y} => by
    contrapose!
    -- ⊢ x ≠ 0 ∧ y ≠ 0 → x * y ≠ 0
    rintro ⟨ha, hb⟩
    -- ⊢ x * y ≠ 0
    rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, rfl⟩
    -- ⊢ (↑verschiebung)^[na] wa * y ≠ 0
    rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, rfl⟩
    -- ⊢ (↑verschiebung)^[na] wa * (↑verschiebung)^[nb] wb ≠ 0
    refine' ne_of_apply_ne (fun x => x.coeff (na + nb)) _
    -- ⊢ (fun x => coeff x (na + nb)) ((↑verschiebung)^[na] wa * (↑verschiebung)^[nb] …
    dsimp only
    -- ⊢ coeff ((↑verschiebung)^[na] wa * (↑verschiebung)^[nb] wb) (na + nb) ≠ coeff  …
    rw [iterate_verschiebung_mul_coeff, zero_coeff]
    -- ⊢ coeff wa 0 ^ p ^ nb * coeff wb 0 ^ p ^ na ≠ 0
    exact mul_ne_zero (pow_ne_zero _ hwa0) (pow_ne_zero _ hwb0)⟩
    -- 🎉 no goals

instance instIsDomain [CharP R p] [IsDomain R] : IsDomain (𝕎 R) :=
  NoZeroDivisors.to_isDomain _

end WittVector
