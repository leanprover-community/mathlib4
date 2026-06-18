/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Localization of a finitely generated submonoid

## TODO

If `Mathlib/GroupTheory/Finiteness.lean` wasn't so heavy, this could move earlier.
-/

public section

open Localization

variable {M : Type*} [CommMonoid M] {S : Submonoid M}

namespace WithOne

@[to_additive]
instance instFG [Monoid.FG M] : Monoid.FG <| WithOne M where
  fg_top := by
    have hM : (⊤ : Submonoid M).FG := Monoid.FG.fg_top
    rw [Submonoid.fg_iff] at hM ⊢
    obtain ⟨S, hS, hS'⟩ := hM
    refine ⟨insert ((1 : M) : WithOne M) (WithOne.coe '' S), ?_, (hS'.image WithOne.coe).insert _⟩
    rw [Submonoid.eq_top_iff']
    intro x
    induction x with
    | one => exact Submonoid.one_mem _
    | coe x =>
      induction x using Submonoid.dense_induction S hS
      · exact Submonoid.subset_closure (by grind)
      · exact Submonoid.subset_closure (by grind)
      · simp_all [Submonoid.mul_mem]

-- TODO: generalize to CommSemigroup, when IsMulTorsionFree uses `Nat.iterate`
@[to_additive]
instance instIsMulTorsionFree {M : Type*} [CommMonoid M] [IsMulTorsionFree M] :
    IsMulTorsionFree (WithOne M) where
  pow_left_injective n hn x y h := by
    induction x <;> induction y <;> dsimp only at h
    · rfl
    · rw [WithOne.coe_pnpow _ hn, one_pow] at h
      exact absurd h WithOne.one_ne_coe
    · rw [WithOne.coe_pnpow _ hn, one_pow] at h
      exact absurd h WithOne.one_ne_coe.symm
    · rw [WithOne.coe_pnpow _ hn, WithOne.coe_pnpow _ hn,
        iterate_mul_left_eq_pow, iterate_mul_left_eq_pow, Nat.sub_one_add_one hn, WithOne.coe_inj]
        at h
      rw [WithOne.coe_inj]
      exact pow_left_injective hn h

end WithOne

namespace Localization

/-- The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated. -/
@[to_additive /-- The localization of a finitely generated monoid at a finitely generated submonoid
is finitely generated. -/]
lemma fg [Monoid.FG M] (hS : S.FG) : Monoid.FG <| Localization S := by
  rw [← Monoid.fg_iff_submonoid_fg] at hS; exact Monoid.fg_of_surjective mkHom mkHom_surjective

end Localization

namespace Algebra.GrothendieckGroup

/-- The Grothendieck group of a finitely generated monoid is finitely generated. -/
@[to_additive /-- The Grothendieck group of a finitely generated monoid is finitely generated. -/]
instance instFG [Monoid.FG M] : Monoid.FG <| GrothendieckGroup M := fg Monoid.FG.fg_top

end Algebra.GrothendieckGroup
