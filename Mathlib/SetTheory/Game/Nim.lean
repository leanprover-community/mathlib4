/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Game.Birthday
import Mathlib.SetTheory.Game.Impartial

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `o`. In the game of `nim o₁` both players
may move to `nim o₂` for any `o₂ < o₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundyValue G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim o` to be `Set.Iio o`.
However, this definition does not work for us because it would make the type of nim
`Ordinal.{u} → SetTheory.PGame.{u + 1}`, which would make it impossible for us to state the
Sprague-Grundy theorem, since that requires the type of `nim` to be
`Ordinal.{u} → SetTheory.PGame.{u}`. For this reason, we
instead use `o.toType` for the possible moves. You can use `to_left_moves_nim` and
`to_right_moves_nim` to convert an ordinal less than `o` into a left or right move of `nim o`, and
vice versa.
-/


noncomputable section

universe u

namespace SetTheory

open scoped PGame
open Ordinal

namespace PGame

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
noncomputable def nim (o : Ordinal.{u}) : PGame.{u} :=
  ⟨o.toType, o.toType,
    fun x => nim ((enumIsoToType o).symm x).val,
    fun x => nim ((enumIsoToType o).symm x).val⟩
termination_by o
decreasing_by all_goals exact ((enumIsoToType o).symm x).prop

theorem nim_def (o : Ordinal) : nim o =
    ⟨o.toType, o.toType,
      fun x => nim ((enumIsoToType o).symm x).val,
      fun x => nim ((enumIsoToType o).symm x).val⟩ := by
  rw [nim]

theorem leftMoves_nim (o : Ordinal) : (nim o).LeftMoves = o.toType := by rw [nim_def]; rfl
theorem rightMoves_nim (o : Ordinal) : (nim o).RightMoves = o.toType := by rw [nim_def]; rfl

theorem moveLeft_nim_hEq (o : Ordinal) :
    HEq (nim o).moveLeft fun i : o.toType => nim ((enumIsoToType o).symm i) := by rw [nim_def]; rfl

theorem moveRight_nim_hEq (o : Ordinal) :
    HEq (nim o).moveRight fun i : o.toType => nim ((enumIsoToType o).symm i) := by rw [nim_def]; rfl

/-- Turns an ordinal less than `o` into a left move for `nim o` and vice versa. -/
noncomputable def toLeftMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).LeftMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (leftMoves_nim o).symm)

/-- Turns an ordinal less than `o` into a right move for `nim o` and vice versa. -/
noncomputable def toRightMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).RightMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (rightMoves_nim o).symm)

@[simp]
theorem toLeftMovesNim_symm_lt {o : Ordinal} (i : (nim o).LeftMoves) :
    toLeftMovesNim.symm i < o :=
  (toLeftMovesNim.symm i).prop

@[simp]
theorem toRightMovesNim_symm_lt {o : Ordinal} (i : (nim o).RightMoves) :
    toRightMovesNim.symm i < o :=
  (toRightMovesNim.symm i).prop

@[simp]
theorem moveLeft_nim' {o : Ordinal} (i) : (nim o).moveLeft i = nim (toLeftMovesNim.symm i).val :=
  (congr_heq (moveLeft_nim_hEq o).symm (cast_heq _ i)).symm

theorem moveLeft_nim {o : Ordinal} (i) : (nim o).moveLeft (toLeftMovesNim i) = nim i := by simp

@[simp]
theorem moveRight_nim' {o : Ordinal} (i) : (nim o).moveRight i = nim (toRightMovesNim.symm i).val :=
  (congr_heq (moveRight_nim_hEq o).symm (cast_heq _ i)).symm

theorem moveRight_nim {o : Ordinal} (i) : (nim o).moveRight (toRightMovesNim i) = nim i := by simp

/-- A recursion principle for left moves of a nim game. -/
@[elab_as_elim]
def leftMovesNimRecOn {o : Ordinal} {P : (nim o).LeftMoves → Sort*} (i : (nim o).LeftMoves)
    (H : ∀ a (H : a < o), P <| toLeftMovesNim ⟨a, H⟩) : P i := by
  rw [← toLeftMovesNim.apply_symm_apply i]; apply H

/-- A recursion principle for right moves of a nim game. -/
@[elab_as_elim]
def rightMovesNimRecOn {o : Ordinal} {P : (nim o).RightMoves → Sort*} (i : (nim o).RightMoves)
    (H : ∀ a (H : a < o), P <| toRightMovesNim ⟨a, H⟩) : P i := by
  rw [← toRightMovesNim.apply_symm_apply i]; apply H

instance isEmpty_nim_zero_leftMoves : IsEmpty (nim 0).LeftMoves := by
  rw [nim_def]
  exact isEmpty_toType_zero

instance isEmpty_nim_zero_rightMoves : IsEmpty (nim 0).RightMoves := by
  rw [nim_def]
  exact isEmpty_toType_zero

/-- `nim 0` has exactly the same moves as `0`. -/
def nimZeroRelabelling : nim 0 ≡r 0 :=
  Relabelling.isEmpty _

theorem nim_zero_equiv : nim 0 ≈ 0 :=
  Equiv.isEmpty _

noncomputable instance uniqueNimOneLeftMoves : Unique (nim 1).LeftMoves :=
  (Equiv.cast <| leftMoves_nim 1).unique

noncomputable instance uniqueNimOneRightMoves : Unique (nim 1).RightMoves :=
  (Equiv.cast <| rightMoves_nim 1).unique

@[simp]
theorem default_nim_one_leftMoves_eq :
    (default : (nim 1).LeftMoves) = @toLeftMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl

@[simp]
theorem default_nim_one_rightMoves_eq :
    (default : (nim 1).RightMoves) = @toRightMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl

@[simp]
theorem toLeftMovesNim_one_symm (i) :
    (@toLeftMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]

@[simp]
theorem toRightMovesNim_one_symm (i) :
    (@toRightMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]

theorem nim_one_moveLeft (x) : (nim 1).moveLeft x = nim 0 := by simp

theorem nim_one_moveRight (x) : (nim 1).moveRight x = nim 0 := by simp

/-- `nim 1` has exactly the same moves as `star`. -/
def nimOneRelabelling : nim 1 ≡r star := by
  rw [nim_def]
  refine ⟨?_, ?_, fun i => ?_, fun j => ?_⟩
  any_goals dsimp; apply Equiv.equivOfUnique
  all_goals simpa [enumIsoToType] using nimZeroRelabelling

theorem nim_one_equiv : nim 1 ≈ star :=
  nimOneRelabelling.equiv

@[simp]
theorem nim_birthday (o : Ordinal) : (nim o).birthday = o := by
  induction' o using Ordinal.induction with o IH
  rw [nim_def, birthday_def]
  dsimp
  rw [max_eq_right le_rfl]
  convert lsub_typein o with i
  exact IH _ (typein_lt_self i)

@[simp]
theorem neg_nim (o : Ordinal) : -nim o = nim o := by
  induction' o using Ordinal.induction with o IH
  rw [nim_def]; dsimp; congr <;> funext i <;> exact IH _ (Ordinal.typein_lt_self i)

instance nim_impartial (o : Ordinal) : Impartial (nim o) := by
  induction' o using Ordinal.induction with o IH
  rw [impartial_def, neg_nim]
  refine ⟨equiv_rfl, fun i => ?_, fun i => ?_⟩ <;> simpa using IH _ (typein_lt_self _)

theorem nim_fuzzy_zero_of_ne_zero {o : Ordinal} (ho : o ≠ 0) : nim o ‖ 0 := by
  rw [Impartial.fuzzy_zero_iff_lf, lf_zero_le]
  use toRightMovesNim ⟨0, Ordinal.pos_iff_ne_zero.2 ho⟩
  simp

@[simp]
theorem nim_add_equiv_zero_iff (o₁ o₂ : Ordinal) : (nim o₁ + nim o₂ ≈ 0) ↔ o₁ = o₂ := by
  constructor
  · refine not_imp_not.1 fun hne : _ ≠ _ => (Impartial.not_equiv_zero_iff (nim o₁ + nim o₂)).2 ?_
    wlog h : o₁ < o₂
    · exact (fuzzy_congr_left add_comm_equiv).1 (this _ _ hne.symm (hne.lt_or_lt.resolve_left h))
    rw [Impartial.fuzzy_zero_iff_gf, zero_lf_le]
    use toLeftMovesAdd (Sum.inr <| toLeftMovesNim ⟨_, h⟩)
    · simpa using (Impartial.add_self (nim o₁)).2
  · rintro rfl
    exact Impartial.add_self (nim o₁)

@[simp]
theorem nim_add_fuzzy_zero_iff {o₁ o₂ : Ordinal} : nim o₁ + nim o₂ ‖ 0 ↔ o₁ ≠ o₂ := by
  rw [iff_not_comm, Impartial.not_fuzzy_zero_iff, nim_add_equiv_zero_iff]

@[simp]
theorem nim_equiv_iff_eq {o₁ o₂ : Ordinal} : (nim o₁ ≈ nim o₂) ↔ o₁ = o₂ := by
  rw [Impartial.equiv_iff_add_equiv_zero, nim_add_equiv_zero_iff]

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundyValue : PGame.{u} → Ordinal.{u}
  | G => Ordinal.mex.{u, u} fun i => grundyValue (G.moveLeft i)
termination_by G => G

theorem grundyValue_eq_mex_left (G : PGame) :
    grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveLeft i) := by rw [grundyValue]

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundyValue : ∀ (G : PGame.{u}) [G.Impartial], G ≈ nim (grundyValue G)
  | G => by
    rw [Impartial.equiv_iff_add_equiv_zero, ← Impartial.forall_leftMoves_fuzzy_iff_equiv_zero]
    intro i
    apply leftMoves_add_cases i
    · intro i₁
      rw [add_moveLeft_inl]
      apply
        (fuzzy_congr_left (add_congr_left (Equiv.symm (equiv_nim_grundyValue (G.moveLeft i₁))))).1
      rw [nim_add_fuzzy_zero_iff]
      intro heq
      rw [eq_comm, grundyValue_eq_mex_left G] at heq
      -- Porting note: added universe annotation, argument
      have h := Ordinal.ne_mex.{u, u} (fun i ↦ grundyValue (moveLeft G i))
      rw [heq] at h
      exact (h i₁).irrefl
    · intro i₂
      rw [add_moveLeft_inr, ← Impartial.exists_left_move_equiv_iff_fuzzy_zero]
      revert i₂
      rw [nim_def]
      intro i₂
      have h' :
        ∃ i : G.LeftMoves,
          grundyValue (G.moveLeft i) = Ordinal.typein (α := toType (grundyValue G)) (· < ·) i₂ := by
        revert i₂
        rw [grundyValue_eq_mex_left]
        intro i₂
        have hnotin : _ ∉ _ := fun hin => not_le_of_lt (Ordinal.typein_lt_self i₂) (csInf_le' hin)
        simpa using hnotin
      cases' h' with i hi
      use toLeftMovesAdd (Sum.inl i)
      rw [add_moveLeft_inl, moveLeft_mk]
      apply Equiv.trans (add_congr_left (equiv_nim_grundyValue (G.moveLeft i)))
      simpa only [hi] using Impartial.add_self (nim (grundyValue (G.moveLeft i)))
termination_by G => G
decreasing_by all_goals pgame_wf_tac

theorem grundyValue_eq_iff_equiv_nim {G : PGame} [G.Impartial] {o : Ordinal} :
    grundyValue G = o ↔ (G ≈ nim o) :=
  ⟨by rintro rfl; exact equiv_nim_grundyValue G,
   by intro h; rw [← nim_equiv_iff_eq]; exact Equiv.trans (Equiv.symm (equiv_nim_grundyValue G)) h⟩

@[simp]
theorem nim_grundyValue (o : Ordinal.{u}) : grundyValue (nim o) = o :=
  grundyValue_eq_iff_equiv_nim.2 PGame.equiv_rfl

theorem grundyValue_eq_iff_equiv (G H : PGame) [G.Impartial] [H.Impartial] :
    grundyValue G = grundyValue H ↔ (G ≈ H) :=
  grundyValue_eq_iff_equiv_nim.trans (equiv_congr_left.1 (equiv_nim_grundyValue H) _).symm

@[simp]
theorem grundyValue_zero : grundyValue 0 = 0 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_zero_equiv)

theorem grundyValue_iff_equiv_zero (G : PGame) [G.Impartial] : grundyValue G = 0 ↔ (G ≈ 0) := by
  rw [← grundyValue_eq_iff_equiv, grundyValue_zero]

@[simp]
theorem grundyValue_star : grundyValue star = 1 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_one_equiv)

@[simp]
theorem grundyValue_neg (G : PGame) [G.Impartial] : grundyValue (-G) = grundyValue G := by
  rw [grundyValue_eq_iff_equiv_nim, neg_equiv_iff, neg_nim, ← grundyValue_eq_iff_equiv_nim]

theorem grundyValue_eq_mex_right :
    ∀ (G : PGame) [G.Impartial],
      grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveRight i)
   | ⟨l, r, L, R⟩, _ => by
    rw [← grundyValue_neg, grundyValue_eq_mex_left]
    congr
    ext i
    haveI : (R i).Impartial := @Impartial.moveRight_impartial ⟨l, r, L, R⟩ _ i
    apply grundyValue_neg

-- Todo: this actually generalizes to all ordinals, by defining `Ordinal.lxor` as the pairwise
-- `Nat.xor` of base `ω` Cantor normal forms.
/-- The Grundy value of the sum of two nim games with natural numbers of piles equals their bitwise
xor. -/
@[simp]
theorem grundyValue_nim_add_nim (n m : ℕ) :
    grundyValue (nim.{u} n + nim.{u} m) = n ^^^ m := by
  -- We do strong induction on both variables.
  induction' n using Nat.strong_induction_on with n hn generalizing m
  induction' m using Nat.strong_induction_on with m hm
  rw [grundyValue_eq_mex_left]
  refine (Ordinal.mex_le_of_ne.{u, u} fun i => ?_).antisymm
    (Ordinal.le_mex_of_forall fun ou hu => ?_)
  -- The Grundy value `n ^^^ m` can't be reached by left moves.
  · apply leftMoves_add_cases i <;>
      · -- A left move leaves us with a Grundy value of `k ^^^ m` for `k < n`, or
        -- `n ^^^ k` for `k < m`.
        refine fun a => leftMovesNimRecOn a fun ok hk => ?_
        obtain ⟨k, rfl⟩ := Ordinal.lt_omega.1 (hk.trans (Ordinal.nat_lt_omega _))
        simp only [add_moveLeft_inl, add_moveLeft_inr, moveLeft_nim', Equiv.symm_apply_apply]
        -- The inequality follows from injectivity.
        rw [natCast_lt] at hk
        first
        | rw [hn _ hk]
        | rw [hm _ hk]
        refine fun h => hk.ne ?_
        rw [Ordinal.natCast_inj] at h
        first
        | rwa [Nat.xor_left_inj] at h
        | rwa [Nat.xor_right_inj] at h
  -- Every other smaller Grundy value can be reached by left moves.
  · -- If `u < m ^^^ n`, then either `u ^^^ n < m` or `u ^^^ m < n`.
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (hu.trans (Ordinal.nat_lt_omega _))
    replace hu := Ordinal.natCast_lt.1 hu
    cases' Nat.lt_xor_cases hu with h h
    -- In the first case, reducing the `m` pile to `u ^^^ n` gives the desired Grundy value.
    · refine ⟨toLeftMovesAdd (Sum.inl <| toLeftMovesNim ⟨_, Ordinal.natCast_lt.2 h⟩), ?_⟩
      simp [Nat.xor_cancel_right, hn _ h]
    -- In the second case, reducing the `n` pile to `u ^^^ m` gives the desired Grundy value.
    · refine ⟨toLeftMovesAdd (Sum.inr <| toLeftMovesNim ⟨_, Ordinal.natCast_lt.2 h⟩), ?_⟩
      have : n ^^^ (u ^^^ n) = u := by rw [Nat.xor_comm u, Nat.xor_cancel_left]
      simpa [hm _ h] using this

theorem nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (n ^^^ m) := by
  rw [← grundyValue_eq_iff_equiv_nim, grundyValue_nim_add_nim]

theorem grundyValue_add (G H : PGame) [G.Impartial] [H.Impartial] {n m : ℕ} (hG : grundyValue G = n)
    (hH : grundyValue H = m) : grundyValue (G + H) = n ^^^ m := by
  rw [← nim_grundyValue (n ^^^ m), grundyValue_eq_iff_equiv]
  refine Equiv.trans ?_ nim_add_nim_equiv
  convert add_congr (equiv_nim_grundyValue G) (equiv_nim_grundyValue H) <;> simp only [hG, hH]

end PGame

end SetTheory
