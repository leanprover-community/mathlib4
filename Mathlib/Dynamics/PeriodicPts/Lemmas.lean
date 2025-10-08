/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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

theorem directed_ptsOfPeriod_pnat (f : α → α) : Directed (· ⊆ ·) fun n : ℕ+ => ptsOfPeriod f n :=
  fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

@[deprecated (since := "2025-04-27")]
alias directed_ptsOfPeriod_pNat := directed_ptsOfPeriod_pnat

variable (f) in
theorem bijOn_periodicPts : BijOn f (periodicPts f) (periodicPts f) :=
  iUnion_pnat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pnat f) fun i => bijOn_ptsOfPeriod f i.pos

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

section Fintype

open Fintype

theorem minimalPeriod_le_card [Fintype α] : minimalPeriod f x ≤ card α := by
  rw [← periodicOrbit_length]
  exact List.Nodup.length_le_card nodup_periodicOrbit

theorem isPeriodicPt_factorial_card_of_mem_periodicPts [Fintype α] (h : x ∈ periodicPts f) :
    IsPeriodicPt f (card α)! x :=
  isPeriodicPt_iff_minimalPeriod_dvd.mpr
    (Nat.dvd_factorial (minimalPeriod_pos_of_mem_periodicPts h) minimalPeriod_le_card)

theorem mem_periodicPts_iff_isPeriodicPt_factorial_card [Fintype α] :
    x ∈ periodicPts f ↔ IsPeriodicPt f (card α)! x where
  mp := isPeriodicPt_factorial_card_of_mem_periodicPts
  mpr h := minimalPeriod_pos_iff_mem_periodicPts.mp
    (IsPeriodicPt.minimalPeriod_pos (Nat.factorial_pos _) h)

theorem Injective.mem_periodicPts [Finite α] (h : Injective f) (x : α) : x ∈ periodicPts f := by
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, f^[m] x = f^[n] x ∧ m ≠ n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (by cutsat) (iterate_cancel h heq.symm)
  · exact mk_mem_periodicPts (by cutsat) (iterate_cancel h heq)

@[deprecated (since := "2025-04-27")]
alias mem_periodicPts_of_injective :=  Injective.mem_periodicPts

theorem injective_iff_periodicPts_eq_univ [Finite α] : Injective f ↔ periodicPts f = univ := by
  refine ⟨fun h ↦ eq_univ_iff_forall.mpr h.mem_periodicPts, fun h ↦ ?_⟩
  rw [Finite.injective_iff_surjective, ← range_eq_univ, ← univ_subset_iff, ← h]
  apply periodicPts_subset_range

@[deprecated (since := "2025-04-27")]
alias injective_iff_forall_mem_periodicPts := injective_iff_periodicPts_eq_univ

theorem injective_iff_iterate_factorial_card_eq_id [Fintype α] :
    Injective f ↔ f^[(card α)!] = id := by
  simp only [injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card,
    funext_iff, eq_univ_iff_forall, IsPeriodicPt, id, IsFixedPt]

end Fintype

end Function

namespace Function

variable {α β : Type*} {f : α → α} {g : β → β} {x : α × β} {a : α} {b : β} {m n : ℕ}

theorem minimalPeriod_prodMap (f : α → α) (g : β → β) (x : α × β) :
    minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm (minimalPeriod g x.2) :=
  eq_of_forall_dvd <| by simp [← isPeriodicPt_iff_minimalPeriod_dvd, Nat.lcm_dvd_iff]

@[deprecated (since := "2025-04-18")]
alias minimalPeriod_prod_map := minimalPeriod_prodMap

theorem minimalPeriod_fst_dvd : minimalPeriod f x.1 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_left _ _

theorem minimalPeriod_snd_dvd : minimalPeriod g x.2 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_right _ _

end Function
