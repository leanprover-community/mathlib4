/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# `Finset.lcm` lemmas

## Tags

finset, lcm, prod, coprime
-/

public section

namespace Finset

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_dvd_prod (s : Finset ι) (f : ι → α) : s.lcm f ∣ s.prod f :=
  lcm_dvd fun _ ↦ dvd_prod_of_mem _

theorem associated_lcm_prod {s : Finset ι} {f : ι → α} (h : Set.Pairwise s <| IsRelPrime.onFun f) :
    Associated (s.lcm f) (s.prod f) :=
  associated_of_dvd_dvd (s.lcm_dvd_prod f) (s.prod_dvd_of_isRelPrime h fun _ ↦ dvd_lcm)

theorem lcm_eq_prod {s : Finset ι} {f : ι → ℕ} (h : Set.Pairwise s <| Nat.Coprime.onFun f) :
    s.lcm f = s.prod f := by
  rw [show Nat.Coprime = IsRelPrime by ext; exact Nat.coprime_iff_isRelPrime] at h
  exact associated_lcm_prod h |>.eq_of_normalized (normalize_eq _) (normalize_eq _)

end Finset
