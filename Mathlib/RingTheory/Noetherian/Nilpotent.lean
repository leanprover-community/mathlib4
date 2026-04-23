/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Nilpotent ideals in Noetherian rings


## Main results

* `IsNoetherianRing.isNilpotent_nilradical`
-/

public section

open IsNoetherian

theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommSemiring R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) := by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩

lemma Ideal.FG.isNilpotent_iff_le_nilradical {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : I.FG) : IsNilpotent I ↔ I ≤ nilradical R :=
  ⟨fun ⟨n, hn⟩ _ hx ↦ ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
    fun h ↦ let ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI; ⟨n, le_bot_iff.mp hn⟩⟩
