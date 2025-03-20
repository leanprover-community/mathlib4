/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Extra lemmas about periodic points
-/

open Nat Set

namespace Function
variable {α : Type*} {f : α → α} {x y : α}

open Function (Commute)

theorem directed_ptsOfPeriod_pNat (f : α → α) : Directed (· ⊆ ·) fun n : ℕ+ => ptsOfPeriod f n :=
  fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

variable (f) in
theorem bijOn_periodicPts : BijOn f (periodicPts f) (periodicPts f) :=
  iUnion_pNat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pNat f) fun i => bijOn_ptsOfPeriod f i.pos

theorem minimalPeriod_eq_prime_iff {p : ℕ} [hp : Fact p.Prime] :
    minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt f x := by
  rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, Nat.dvd_prime hp.out,
    ← minimalPeriod_eq_one_iff_isFixedPt.not, or_and_right, and_not_self_iff, false_or,
    iff_self_and]
  exact fun h ↦ ne_of_eq_of_ne h hp.out.ne_one

/-- The backward direction of `minimalPeriod_eq_prime_iff`. -/
theorem minimalPeriod_eq_prime {p : ℕ} [hp : Fact p.Prime] (hper : IsPeriodicPt f p x)
    (hfix : ¬IsFixedPt f x) : minimalPeriod f x = p :=
  minimalPeriod_eq_prime_iff.mpr ⟨hper, hfix⟩

theorem minimalPeriod_eq_prime_pow {p k : ℕ} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x)
    (hk1 : IsPeriodicPt f (p ^ (k + 1)) x) : minimalPeriod f x = p ^ (k + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;>
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]

theorem Commute.minimalPeriod_of_comp_dvd_mul {g : α → α} (h : Commute f g) :
    minimalPeriod (f ∘ g) x ∣ minimalPeriod f x * minimalPeriod g x :=
  dvd_trans h.minimalPeriod_of_comp_dvd_lcm (lcm_dvd_mul _ _)

theorem Commute.minimalPeriod_of_comp_eq_mul_of_coprime {g : α → α} (h : Commute f g)
    (hco : Coprime (minimalPeriod f x) (minimalPeriod g x)) :
    minimalPeriod (f ∘ g) x = minimalPeriod f x * minimalPeriod g x := by
  apply h.minimalPeriod_of_comp_dvd_mul.antisymm
  suffices
    ∀ {f g : α → α},
      Commute f g →
        Coprime (minimalPeriod f x) (minimalPeriod g x) →
          minimalPeriod f x ∣ minimalPeriod (f ∘ g) x from
    hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  intro f g h hco
  refine hco.dvd_of_dvd_mul_left (IsPeriodicPt.left_of_comp h ?_ ?_).minimalPeriod_dvd
  · exact (isPeriodicPt_minimalPeriod _ _).const_mul _
  · exact (isPeriodicPt_minimalPeriod _ _).mul_const _

end Function

namespace Function

variable {α β : Type*} {f : α → α} {g : β → β} {x : α × β} {a : α} {b : β} {m n : ℕ}

theorem minimalPeriod_prod_map (f : α → α) (g : β → β) (x : α × β) :
    minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm (minimalPeriod g x.2) :=
  eq_of_forall_dvd <| by cases x; simp [← isPeriodicPt_iff_minimalPeriod_dvd, Nat.lcm_dvd_iff]

theorem minimalPeriod_fst_dvd : minimalPeriod f x.1 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prod_map]; exact Nat.dvd_lcm_left _ _

theorem minimalPeriod_snd_dvd : minimalPeriod g x.2 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prod_map]; exact Nat.dvd_lcm_right _ _

end Function
