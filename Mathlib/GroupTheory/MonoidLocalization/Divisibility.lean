/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic

import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Divisibility.Units

/-!
# Divisibility in localizations of commutative monoids
-/

namespace Submonoid.LocalizationMap

variable {M N : Type*} [CommMonoid M] {S : Submonoid M} [CommMonoid N] (f : LocalizationMap S N)

public theorem map_isUnit_iff {m : M} : IsUnit (f m) ↔ ∃ s ∈ S, m ∣ s := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm, dvd⟩ ↦ isUnit_of_dvd_unit (map_dvd _ dvd) (f.map_units ⟨m, hm⟩)⟩
  have ⟨s, hxs⟩ := isUnit_iff_dvd_one.mp h
  have ⟨⟨r, s⟩, hrs⟩ := f.surj s
  replace hrs := congr(f m * $hrs)
  rw [← mul_assoc, ← hxs, one_mul, ← map_mul] at hrs
  have ⟨s', eq⟩ := f.eq_iff_exists.mp hrs
  exact ⟨s' * s, mul_mem s'.2 s.2, _, mul_left_comm _ m _ ▸ eq⟩

public theorem map_dvd_map {m₁ m₂ : M} : f m₁ ∣ f m₂ ↔ ∃ s ∈ S, m₁ ∣ s * m₂ where
  mp := fun ⟨n, eq⟩ ↦ by
    have ⟨⟨m, s⟩, hn⟩ := f.surj n
    replace hn := congr(f m₁ * $hn)
    rw [← mul_assoc, ← eq, ← map_mul, ← map_mul] at hn
    have ⟨s', hs'⟩ := f.eq_iff_exists.mp hn
    refine ⟨_, mul_mem s'.2 s.2, s' * m, ?_⟩
    rwa [mul_left_comm, mul_assoc, mul_comm s.1]
  mpr := fun ⟨s, hs, dvd⟩ ↦ (f.map_units ⟨s, hs⟩).dvd_mul_left.mp (map_mul f .. ▸ map_dvd f dvd)

end Submonoid.LocalizationMap
