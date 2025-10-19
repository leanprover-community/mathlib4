/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Nilpotent ideals in Noetherian rings


## Main results

* `IsNoetherianRing.isNilpotent_nilradical`
-/

open IsNoetherian

theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommSemiring R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) := by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩

lemma Ideal.FG.isNilpotent_iff_le_nilradical {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : I.FG) : IsNilpotent I ↔ I ≤ nilradical R :=
  ⟨fun ⟨n, hn⟩ _ hx ↦ ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
    fun h ↦ let ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI; ⟨n, le_bot_iff.mp hn⟩⟩
