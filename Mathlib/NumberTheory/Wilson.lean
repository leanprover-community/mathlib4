/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol
-/
import Mathlib.FieldTheory.Finite.Basic

#align_import number_theory.wilson from "leanprover-community/mathlib"@"c471da714c044131b90c133701e51b877c246677"

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Give `wilsons_lemma` a descriptive name.
-/


open Finset Nat FiniteField ZMod

open scoped BigOperators Nat

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp]
theorem wilsons_lemma : ((p - 1)! : ZMod p) = -1 := by
  refine'
    calc
      ((p - 1)! : ZMod p) = ∏ x in Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial, prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := _
      _ = -1 := by
        -- Porting note: `simp` is less powerful.
        -- simp_rw [← Units.coeHom_apply, ← (Units.coeHom (ZMod p)).map_prod,
        --   prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
        simp_rw [← Units.coeHom_apply]
        rw [← (Units.coeHom (ZMod p)).map_prod]
        simp_rw [prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  -- ⊢ ∏ x in Ico 1 (succ (p - 1)), ↑x = ∏ x : (ZMod p)ˣ, ↑x
  symm
  -- ⊢ ∏ x : (ZMod p)ˣ, ↑x = ∏ x in Ico 1 (succ (p - 1)), ↑x
  refine' prod_bij (fun a _ => (a : ZMod p).val) _ _ _ _
  · intro a ha
    -- ⊢ (fun a x => val ↑a) a ha ∈ Ico 1 (succ (p - 1))
    rw [mem_Ico, ← Nat.succ_sub hp, Nat.succ_sub_one]
    -- ⊢ 1 ≤ (fun a x => val ↑a) a ha ∧ (fun a x => val ↑a) a ha < p
    constructor
    -- ⊢ 1 ≤ (fun a x => val ↑a) a ha
    · apply Nat.pos_of_ne_zero; rw [← @val_zero p]
      -- ⊢ (fun a x => val ↑a) a ha ≠ 0
                                -- ⊢ (fun a x => val ↑a) a ha ≠ val 0
      intro h; apply Units.ne_zero a (val_injective p h)
      -- ⊢ False
               -- 🎉 no goals
    · exact val_lt _
      -- 🎉 no goals
  · rintro a -; simp only [cast_id, nat_cast_val]
    -- ⊢ ↑a = ↑((fun a x => val ↑a) a ha✝)
                -- 🎉 no goals
  · intro _ _ _ _ h; rw [Units.ext_iff]; exact val_injective p h
    -- ⊢ a₁✝ = a₂✝
                     -- ⊢ ↑a₁✝ = ↑a₂✝
                                         -- 🎉 no goals
  · intro b hb
    -- ⊢ ∃ a ha, b = (fun a x => val ↑a) a ha
    rw [mem_Ico, Nat.succ_le_iff, ← succ_sub hp, succ_sub_one, pos_iff_ne_zero] at hb
    -- ⊢ ∃ a ha, b = (fun a x => val ↑a) a ha
    refine' ⟨Units.mk0 b _, Finset.mem_univ _, _⟩
    -- ⊢ ↑b ≠ 0
    · intro h; apply hb.1; apply_fun val at h
      -- ⊢ False
               -- ⊢ b = 0
                           -- ⊢ b = 0
      simpa only [val_cast_of_lt hb.right, val_zero] using h
      -- 🎉 no goals
    · simp only [val_cast_of_lt hb.right, Units.val_mk0]
      -- 🎉 no goals
#align zmod.wilsons_lemma ZMod.wilsons_lemma

@[simp]
theorem prod_Ico_one_prime : ∏ x in Ico 1 p, (x : ZMod p) = -1 := by
  -- Porting note: was `conv in Ico 1 p =>`
  conv =>
    congr
    congr
    rw [← succ_sub_one p, succ_sub (Fact.out (p := p.Prime)).pos]
  rw [← prod_natCast, Finset.prod_Ico_id_eq_factorial, wilsons_lemma]
  -- 🎉 no goals
#align zmod.prod_Ico_one_prime ZMod.prod_Ico_one_prime

end ZMod

namespace Nat

variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
theorem prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n ≠ 1) : Prime n := by
  rcases eq_or_ne n 0 with (rfl | h0)
  -- ⊢ Prime 0
  · norm_num at h
    -- 🎉 no goals
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  -- ⊢ Prime n
  by_contra h2
  -- ⊢ False
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  -- ⊢ False
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  -- ⊢ False
  refine' hm2.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hm).mp (hm1.trans _)))
  -- ⊢ n ∣ (n - 1)! + 1
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd, cast_add, cast_one, h, add_left_neg]
  -- 🎉 no goals
#align nat.prime_of_fac_equiv_neg_one Nat.prime_of_fac_equiv_neg_one

/-- **Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. -/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Prime n ↔ ((n - 1)! : ZMod n) = -1 := by
  refine' ⟨fun h1 => _, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  -- ⊢ ↑(n - 1)! = -1
  haveI := Fact.mk h1
  -- ⊢ ↑(n - 1)! = -1
  exact ZMod.wilsons_lemma n
  -- 🎉 no goals
#align nat.prime_iff_fac_equiv_neg_one Nat.prime_iff_fac_equiv_neg_one

end Nat

assert_not_exists legendre_sym.quadratic_reciprocity
