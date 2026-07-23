/-
Copyright (c) 2026 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
module

public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite sets in sigma types
-/

public section

open Finset

variable {ι α : Type*} {κ : ι → Type*}

namespace Set

variable {s : Set ι} {t : ∀ i, Set (κ i)}

/-- A finite sum of finite sets is finite -/
lemma Finite.sigma (hs : s.Finite) (ht : ∀ i ∈ s, (t i).Finite) :
    (s.sigma t).Finite := by
  lift s to Finset ι using hs
  classical
  apply Finite.ofFinset <| s.sigma fun i ↦ if h : i ∈ s then (ht i h).toFinset else ∅
  intro ⟨i, k⟩
  simp only [mem_sigma, mem_sigma_iff, SetLike.mem_coe, and_congr_right_iff]
  intro h
  simp [dif_pos h]

end Set
