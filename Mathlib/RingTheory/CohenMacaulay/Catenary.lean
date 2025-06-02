/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.CohenMacaulay.Basic

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

open RingTheory.Sequence IsLocalRing

lemma Ideal.ofList_height_eq_length_of_isRegular [IsCohenMacaulayLocalRing R] (rs : List R)
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (Ideal.ofList rs).height = rs.length := by
  sorry

lemma Ideal.maximalIdeal_mem_ofList_append_of_ofList_height_eq_length [IsLocalRing R] (rs : List R)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (ht : (Ideal.ofList rs).height = rs.length) :
    ∃ rs' : List R, maximalIdeal R ∈ (Ideal.ofList (rs ++ rs')).minimalPrimes ∧
    rs.length + rs'.length = ringKrullDim R := by
  sorry

lemma RingTheory.Sequence.isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
    [IsCohenMacaulayLocalRing R] (rs : List R)
    (mem : maximalIdeal R ∈ (Ideal.ofList rs).minimalPrimes) : IsWeaklyRegular R rs := by
  sorry
