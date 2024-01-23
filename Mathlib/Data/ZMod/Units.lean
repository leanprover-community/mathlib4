/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ashvni Narayanan, Michael Stoll
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Associated


/-!
# Lemmas about units in `ZMod`.
-/


namespace ZMod

variable {n m : ℕ}
/-- `unitsMap` is a group homomorphism that maps units of `ZMod m` to units of `ZMod n` when `n`
divides `m`. -/
def unitsMap (hm : n ∣ m) : (ZMod m)ˣ →* (ZMod n)ˣ := Units.map (castHom hm (ZMod n))

lemma unitsMap_def (hm : n ∣ m) : unitsMap hm = Units.map (castHom hm (ZMod n)) := rfl

lemma unitsMap_comp {d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd) := by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
  exact congr_arg Units.map <| congr_arg RingHom.toMonoidHom <| castHom_comp hm hd

@[simp]
lemma unitsMap_self (n : ℕ) : unitsMap (dvd_refl n) = MonoidHom.id _ := by
  simp [unitsMap, castHom_self]

lemma IsUnit_cast_of_dvd (hm : n ∣ m) (a : Units (ZMod m)) : IsUnit ((a : ZMod m) : ZMod n) :=
  Units.isUnit (unitsMap hm a)

theorem unitsMap_surjective [hm : NeZero m] (h : n ∣ m) :
    Function.Surjective (unitsMap h) := by
  suffices ∀ x : ℕ, x.Coprime n → ∃ k : ℕ, (x + k * n).Coprime m by
    intro x
    have ⟨k, hk⟩ := this x.val.val (val_coe_unit_coprime x)
    refine ⟨unitOfCoprime _ hk, Units.ext ?_⟩
    have : NeZero n := ⟨fun hn ↦ hm.out (eq_zero_of_zero_dvd (hn ▸ h))⟩
    simp [unitsMap_def]
  intro x hx
  let ps := m.primeFactors.filter (fun p ↦ ¬p ∣ x)
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub' hp hpx
    rw [add_comm, Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finset_prod_iff id).mp h
      rw [Finset.mem_filter, Nat.mem_primeFactors,
        ← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p ∈ ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hm.out⟩, hpx⟩
    have h := Nat.dvd_sub' hp ((Finset.dvd_prod_of_mem id pps).mul_right n)
    rw [Nat.add_sub_cancel] at h
    contradiction

end ZMod
