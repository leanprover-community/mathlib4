/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Game.Birthday
import Mathlib.SetTheory.Game.Impartial

#align_import set_theory.game.nim from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

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
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `o.out.α` for the possible moves. You can use `to_left_moves_nim` and
`to_right_moves_nim` to convert an ordinal less than `o` into a left or right move of `nim o`, and
vice versa.
-/


noncomputable section

universe u

open scoped PGame

namespace PGame

-- Uses `noncomputable!` to avoid `rec_fn_macro only allowed in meta definitions` VM error
/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
noncomputable def nim : Ordinal.{u} → PGame.{u}
  | o₁ =>
    let f o₂ :=
      have _ : Ordinal.typein o₁.out.r o₂ < o₁ := Ordinal.typein_lt_self o₂
      nim (Ordinal.typein o₁.out.r o₂)
    ⟨o₁.out.α, o₁.out.α, f, f⟩
termination_by nim o => o
#align pgame.nim PGame.nim

open Ordinal

theorem nim_def (o : Ordinal) :
    have : IsWellOrder (Quotient.out o).α (· < ·) := inferInstance
    nim o =
      PGame.mk o.out.α o.out.α (fun o₂ => nim (Ordinal.typein (· < ·) o₂)) fun o₂ =>
        nim (Ordinal.typein (· < ·) o₂) := by
  rw [nim]; rfl
  -- ⊢ let_fun this := (_ : IsWellOrder (Quotient.out o).α fun x x_1 => x < x_1);
            -- 🎉 no goals
#align pgame.nim_def PGame.nim_def

theorem leftMoves_nim (o : Ordinal) : (nim o).LeftMoves = o.out.α := by rw [nim_def]; rfl
                                                                        -- ⊢ LeftMoves (mk (Quotient.out o).α (Quotient.out o).α (fun o₂ => nim (typein ( …
                                                                                      -- 🎉 no goals
#align pgame.left_moves_nim PGame.leftMoves_nim

theorem rightMoves_nim (o : Ordinal) : (nim o).RightMoves = o.out.α := by rw [nim_def]; rfl
                                                                          -- ⊢ RightMoves (mk (Quotient.out o).α (Quotient.out o).α (fun o₂ => nim (typein  …
                                                                                        -- 🎉 no goals
#align pgame.right_moves_nim PGame.rightMoves_nim

theorem moveLeft_nim_hEq (o : Ordinal) :
    have : IsWellOrder (Quotient.out o).α (· < ·) := inferInstance
    HEq (nim o).moveLeft fun i : o.out.α => nim (typein (· < ·) i) := by rw [nim_def]; rfl
                                                                         -- ⊢ let_fun this := (_ : IsWellOrder (Quotient.out o).α fun x x_1 => x < x_1);
                                                                                       -- 🎉 no goals
#align pgame.move_left_nim_heq PGame.moveLeft_nim_hEq

theorem moveRight_nim_hEq (o : Ordinal) :
    have : IsWellOrder (Quotient.out o).α (· < ·) := inferInstance
    HEq (nim o).moveRight fun i : o.out.α => nim (typein (· < ·) i) := by rw [nim_def]; rfl
                                                                          -- ⊢ let_fun this := (_ : IsWellOrder (Quotient.out o).α fun x x_1 => x < x_1);
                                                                                        -- 🎉 no goals
#align pgame.move_right_nim_heq PGame.moveRight_nim_hEq

/-- Turns an ordinal less than `o` into a left move for `nim o` and viceversa. -/
noncomputable def toLeftMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (leftMoves_nim o).symm)
#align pgame.to_left_moves_nim PGame.toLeftMovesNim

/-- Turns an ordinal less than `o` into a right move for `nim o` and viceversa. -/
noncomputable def toRightMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).RightMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (rightMoves_nim o).symm)
#align pgame.to_right_moves_nim PGame.toRightMovesNim

@[simp]
theorem toLeftMovesNim_symm_lt {o : Ordinal} (i : (nim o).LeftMoves) :
    ↑(toLeftMovesNim.symm i) < o :=
  (toLeftMovesNim.symm i).prop
#align pgame.to_left_moves_nim_symm_lt PGame.toLeftMovesNim_symm_lt

@[simp]
theorem toRightMovesNim_symm_lt {o : Ordinal} (i : (nim o).RightMoves) :
    ↑(toRightMovesNim.symm i) < o :=
  (toRightMovesNim.symm i).prop
#align pgame.to_right_moves_nim_symm_lt PGame.toRightMovesNim_symm_lt

@[simp]
theorem moveLeft_nim' {o : Ordinal.{u}} (i) :
    (nim o).moveLeft i = nim (toLeftMovesNim.symm i).val :=
  (congr_heq (moveLeft_nim_hEq o).symm (cast_heq _ i)).symm
#align pgame.move_left_nim' PGame.moveLeft_nim'

theorem moveLeft_nim {o : Ordinal} (i) : (nim o).moveLeft (toLeftMovesNim i) = nim i := by simp
                                                                                           -- 🎉 no goals
#align pgame.move_left_nim PGame.moveLeft_nim

@[simp]
theorem moveRight_nim' {o : Ordinal} (i) : (nim o).moveRight i = nim (toRightMovesNim.symm i).val :=
  (congr_heq (moveRight_nim_hEq o).symm (cast_heq _ i)).symm
#align pgame.move_right_nim' PGame.moveRight_nim'

theorem moveRight_nim {o : Ordinal} (i) : (nim o).moveRight (toRightMovesNim i) = nim i := by simp
                                                                                              -- 🎉 no goals
#align pgame.move_right_nim PGame.moveRight_nim

/-- A recursion principle for left moves of a nim game. -/
@[elab_as_elim]
def leftMovesNimRecOn {o : Ordinal} {P : (nim o).LeftMoves → Sort*} (i : (nim o).LeftMoves)
    (H : ∀ a (H : a < o), P <| toLeftMovesNim ⟨a, H⟩) : P i := by
  rw [← toLeftMovesNim.apply_symm_apply i]; apply H
  -- ⊢ P (↑toLeftMovesNim (↑toLeftMovesNim.symm i))
                                            -- 🎉 no goals
#align pgame.left_moves_nim_rec_on PGame.leftMovesNimRecOn

/-- A recursion principle for right moves of a nim game. -/
@[elab_as_elim]
def rightMovesNimRecOn {o : Ordinal} {P : (nim o).RightMoves → Sort*} (i : (nim o).RightMoves)
    (H : ∀ a (H : a < o), P <| toRightMovesNim ⟨a, H⟩) : P i := by
  rw [← toRightMovesNim.apply_symm_apply i]; apply H
  -- ⊢ P (↑toRightMovesNim (↑toRightMovesNim.symm i))
                                             -- 🎉 no goals
#align pgame.right_moves_nim_rec_on PGame.rightMovesNimRecOn

instance isEmpty_nim_zero_leftMoves : IsEmpty (nim 0).LeftMoves := by
  rw [nim_def]
  -- ⊢ IsEmpty (LeftMoves (mk (Quotient.out 0).α (Quotient.out 0).α (fun o₂ => nim  …
  exact Ordinal.isEmpty_out_zero
  -- 🎉 no goals
#align pgame.is_empty_nim_zero_left_moves PGame.isEmpty_nim_zero_leftMoves

instance isEmpty_nim_zero_rightMoves : IsEmpty (nim 0).RightMoves := by
  rw [nim_def]
  -- ⊢ IsEmpty (RightMoves (mk (Quotient.out 0).α (Quotient.out 0).α (fun o₂ => nim …
  exact Ordinal.isEmpty_out_zero
  -- 🎉 no goals
#align pgame.is_empty_nim_zero_right_moves PGame.isEmpty_nim_zero_rightMoves

/-- `nim 0` has exactly the same moves as `0`. -/
def nimZeroRelabelling : nim 0 ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.nim_zero_relabelling PGame.nimZeroRelabelling

theorem nim_zero_equiv : nim 0 ≈ 0 :=
  Equiv.isEmpty _
#align pgame.nim_zero_equiv PGame.nim_zero_equiv

noncomputable instance uniqueNimOneLeftMoves : Unique (nim 1).LeftMoves :=
  (Equiv.cast <| leftMoves_nim 1).unique
#align pgame.unique_nim_one_left_moves PGame.uniqueNimOneLeftMoves

noncomputable instance uniqueNimOneRightMoves : Unique (nim 1).RightMoves :=
  (Equiv.cast <| rightMoves_nim 1).unique
#align pgame.unique_nim_one_right_moves PGame.uniqueNimOneRightMoves

@[simp]
theorem default_nim_one_leftMoves_eq :
    (default : (nim 1).LeftMoves) = @toLeftMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl
#align pgame.default_nim_one_left_moves_eq PGame.default_nim_one_leftMoves_eq

@[simp]
theorem default_nim_one_rightMoves_eq :
    (default : (nim 1).RightMoves) = @toRightMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl
#align pgame.default_nim_one_right_moves_eq PGame.default_nim_one_rightMoves_eq

@[simp]
theorem toLeftMovesNim_one_symm (i) :
    (@toLeftMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by simp
                                                                        -- 🎉 no goals
#align pgame.to_left_moves_nim_one_symm PGame.toLeftMovesNim_one_symm

@[simp]
theorem toRightMovesNim_one_symm (i) :
    (@toRightMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by simp
                                                                         -- 🎉 no goals
#align pgame.to_right_moves_nim_one_symm PGame.toRightMovesNim_one_symm

theorem nim_one_moveLeft (x) : (nim 1).moveLeft x = nim 0 := by simp
                                                                -- 🎉 no goals
#align pgame.nim_one_move_left PGame.nim_one_moveLeft

theorem nim_one_moveRight (x) : (nim 1).moveRight x = nim 0 := by simp
                                                                  -- 🎉 no goals
#align pgame.nim_one_move_right PGame.nim_one_moveRight

/-- `nim 1` has exactly the same moves as `star`. -/
def nimOneRelabelling : nim 1 ≡r star := by
  rw [nim_def]
  -- ⊢ (mk (Quotient.out 1).α (Quotient.out 1).α (fun o₂ => nim (typein (fun x x_1  …
  refine' ⟨_, _, fun i => _, fun j => _⟩
  any_goals dsimp; apply Equiv.equivOfUnique
  -- ⊢ moveLeft (mk (Quotient.out 1).α (Quotient.out 1).α (fun o₂ => nim (typein (f …
  all_goals simp; exact nimZeroRelabelling
  -- 🎉 no goals
#align pgame.nim_one_relabelling PGame.nimOneRelabelling

theorem nim_one_equiv : nim 1 ≈ star :=
  nimOneRelabelling.equiv
#align pgame.nim_one_equiv PGame.nim_one_equiv

@[simp]
theorem nim_birthday (o : Ordinal) : (nim o).birthday = o := by
  induction' o using Ordinal.induction with o IH
  -- ⊢ birthday (nim o) = o
  rw [nim_def, birthday_def]
  -- ⊢ max (lsub fun i => birthday (moveLeft (mk (Quotient.out o).α (Quotient.out o …
  dsimp
  -- ⊢ max (lsub fun i => birthday (nim (typein (fun x x_1 => x < x_1) i))) (lsub f …
  rw [max_eq_right le_rfl]
  -- ⊢ (lsub fun i => birthday (nim (typein (fun x x_1 => x < x_1) i))) = o
  convert lsub_typein o with i
  -- ⊢ birthday (nim (typein (fun x x_1 => x < x_1) i)) = typein (fun x x_1 => x <  …
  exact IH _ (typein_lt_self i)
  -- 🎉 no goals
#align pgame.nim_birthday PGame.nim_birthday

@[simp]
theorem neg_nim (o : Ordinal) : -nim o = nim o := by
  induction' o using Ordinal.induction with o IH
  -- ⊢ -nim o = nim o
  rw [nim_def]; dsimp; congr <;> funext i <;> exact IH _ (Ordinal.typein_lt_self i)
  -- ⊢ (-mk (Quotient.out o).α (Quotient.out o).α (fun o₂ => nim (typein (fun x x_1 …
                -- ⊢ (mk (Quotient.out o).α (Quotient.out o).α (fun j => -nim (typein (fun x x_1  …
                       -- ⊢ (fun j => -nim (typein (fun x x_1 => x < x_1) j)) = fun o₂ => nim (typein (f …
                                 -- ⊢ -nim (typein (fun x x_1 => x < x_1) i) = nim (typein (fun x x_1 => x < x_1) i)
                                 -- ⊢ -nim (typein (fun x x_1 => x < x_1) i) = nim (typein (fun x x_1 => x < x_1) i)
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align pgame.neg_nim PGame.neg_nim

instance nim_impartial (o : Ordinal) : Impartial (nim o) := by
  induction' o using Ordinal.induction with o IH
  -- ⊢ Impartial (nim o)
  rw [impartial_def, neg_nim]
  -- ⊢ nim o ≈ nim o ∧ (∀ (i : LeftMoves (nim o)), Impartial (moveLeft (nim o) i))  …
  refine' ⟨equiv_rfl, fun i => _, fun i => _⟩ <;> simpa using IH _ (typein_lt_self _)
  -- ⊢ Impartial (moveLeft (nim o) i)
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align pgame.nim_impartial PGame.nim_impartial

theorem nim_fuzzy_zero_of_ne_zero {o : Ordinal} (ho : o ≠ 0) : nim o ‖ 0 := by
  rw [Impartial.fuzzy_zero_iff_lf, nim_def, lf_zero_le]
  -- ⊢ ∃ j, moveRight (mk (Quotient.out o).α (Quotient.out o).α (fun o₂ => nim (typ …
  rw [← Ordinal.pos_iff_ne_zero] at ho
  -- ⊢ ∃ j, moveRight (mk (Quotient.out o).α (Quotient.out o).α (fun o₂ => nim (typ …
  exact ⟨(Ordinal.principalSegOut ho).top, by simp⟩
  -- 🎉 no goals
#align pgame.nim_fuzzy_zero_of_ne_zero PGame.nim_fuzzy_zero_of_ne_zero

@[simp]
theorem nim_add_equiv_zero_iff (o₁ o₂ : Ordinal) : (nim o₁ + nim o₂ ≈ 0) ↔ o₁ = o₂ := by
  constructor
  -- ⊢ nim o₁ + nim o₂ ≈ 0 → o₁ = o₂
  · refine' not_imp_not.1 fun hne : _ ≠ _ => (Impartial.not_equiv_zero_iff (nim o₁ + nim o₂)).2 _
    -- ⊢ nim o₁ + nim o₂ ‖ 0
    wlog h : o₁ < o₂
    -- ⊢ nim o₁ + nim o₂ ‖ 0
    · exact (fuzzy_congr_left add_comm_equiv).1 (this _ _ hne.symm (hne.lt_or_lt.resolve_left h))
      -- 🎉 no goals
    rw [Impartial.fuzzy_zero_iff_gf, zero_lf_le, nim_def o₂]
    -- ⊢ ∃ i, 0 ≤ moveLeft (nim o₁ + mk (Quotient.out o₂).α (Quotient.out o₂).α (fun  …
    refine' ⟨toLeftMovesAdd (Sum.inr _), _⟩
    -- ⊢ LeftMoves (mk (Quotient.out o₂).α (Quotient.out o₂).α (fun o₂_1 => nim (type …
    · exact (Ordinal.principalSegOut h).top
      -- 🎉 no goals
    · -- Porting note: squeezed simp
      simpa only [Ordinal.typein_top, Ordinal.type_lt, PGame.add_moveLeft_inr, PGame.moveLeft_mk]
        using (Impartial.add_self (nim o₁)).2
  · rintro rfl
    -- ⊢ nim o₁ + nim o₁ ≈ 0
    exact Impartial.add_self (nim o₁)
    -- 🎉 no goals
#align pgame.nim_add_equiv_zero_iff PGame.nim_add_equiv_zero_iff

@[simp]
theorem nim_add_fuzzy_zero_iff {o₁ o₂ : Ordinal} : nim o₁ + nim o₂ ‖ 0 ↔ o₁ ≠ o₂ := by
  rw [iff_not_comm, Impartial.not_fuzzy_zero_iff, nim_add_equiv_zero_iff]
  -- 🎉 no goals
#align pgame.nim_add_fuzzy_zero_iff PGame.nim_add_fuzzy_zero_iff

@[simp]
theorem nim_equiv_iff_eq {o₁ o₂ : Ordinal} : (nim o₁ ≈ nim o₂) ↔ o₁ = o₂ := by
  rw [Impartial.equiv_iff_add_equiv_zero, nim_add_equiv_zero_iff]
  -- 🎉 no goals
#align pgame.nim_equiv_iff_eq PGame.nim_equiv_iff_eq

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundyValue : ∀ _ : PGame.{u}, Ordinal.{u}
  | G => Ordinal.mex.{u, u} fun i => grundyValue (G.moveLeft i)
termination_by grundyValue G => G
decreasing_by pgame_wf_tac
              -- 🎉 no goals
#align pgame.grundy_value PGame.grundyValue

theorem grundyValue_eq_mex_left (G : PGame) :
    grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveLeft i) := by rw [grundyValue]
                                                                                 -- 🎉 no goals
#align pgame.grundy_value_eq_mex_left PGame.grundyValue_eq_mex_left

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundyValue : ∀ (G : PGame.{u}) [G.Impartial], G ≈ nim (grundyValue G)
  | G => by
    rw [Impartial.equiv_iff_add_equiv_zero, ← Impartial.forall_leftMoves_fuzzy_iff_equiv_zero]
    -- ⊢ ∀ (i : LeftMoves (x✝ + nim (grundyValue x✝))), moveLeft (x✝ + nim (grundyVal …
    intro i
    -- ⊢ moveLeft (x✝ + nim (grundyValue x✝)) i ‖ 0
    apply leftMoves_add_cases i
    -- ⊢ ∀ (i : LeftMoves x✝), moveLeft (x✝ + nim (grundyValue x✝)) (↑toLeftMovesAdd  …
    · intro i₁
      -- ⊢ moveLeft (x✝ + nim (grundyValue x✝)) (↑toLeftMovesAdd (Sum.inl i₁)) ‖ 0
      rw [add_moveLeft_inl]
      -- ⊢ moveLeft x✝ i₁ + nim (grundyValue x✝) ‖ 0
      apply
        (fuzzy_congr_left (add_congr_left (Equiv.symm (equiv_nim_grundyValue (G.moveLeft i₁))))).1
      rw [nim_add_fuzzy_zero_iff]
      -- ⊢ grundyValue (moveLeft G i₁) ≠ grundyValue x✝
      intro heq
      -- ⊢ False
      rw [eq_comm, grundyValue_eq_mex_left G] at heq
      -- ⊢ False
      -- Porting note: added universe annotation, argument
      have h := Ordinal.ne_mex.{u, u} (fun i ↦ grundyValue (moveLeft G i))
      -- ⊢ False
      rw [heq] at h
      -- ⊢ False
      exact (h i₁).irrefl
      -- 🎉 no goals
    · intro i₂
      -- ⊢ moveLeft (x✝ + nim (grundyValue x✝)) (↑toLeftMovesAdd (Sum.inr i₂)) ‖ 0
      rw [add_moveLeft_inr, ← Impartial.exists_left_move_equiv_iff_fuzzy_zero]
      -- ⊢ ∃ i, moveLeft (x✝ + moveLeft (nim (grundyValue x✝)) i₂) i ≈ 0
      revert i₂
      -- ⊢ ∀ (i₂ : LeftMoves (nim (grundyValue x✝))), ∃ i, moveLeft (x✝ + moveLeft (nim …
      rw [nim_def]
      -- ⊢ ∀ (i₂ : LeftMoves (mk (Quotient.out (grundyValue x✝)).α (Quotient.out (grund …
      intro i₂
      -- ⊢ ∃ i, moveLeft (x✝ + moveLeft (mk (Quotient.out (grundyValue x✝)).α (Quotient …
      have h' :
        ∃ i : G.LeftMoves,
          grundyValue (G.moveLeft i) = Ordinal.typein (Quotient.out (grundyValue G)).r i₂ := by
        revert i₂
        rw [grundyValue_eq_mex_left]
        intro i₂
        have hnotin : _ ∉ _ := fun hin =>
          (le_not_le_of_lt (Ordinal.typein_lt_self i₂)).2 (csInf_le' hin)
        simpa using hnotin
      cases' h' with i hi
      -- ⊢ ∃ i, moveLeft (x✝ + moveLeft (mk (Quotient.out (grundyValue x✝)).α (Quotient …
      use toLeftMovesAdd (Sum.inl i)
      -- ⊢ moveLeft (x✝ + moveLeft (mk (Quotient.out (grundyValue x✝)).α (Quotient.out  …
      rw [add_moveLeft_inl, moveLeft_mk]
      -- ⊢ moveLeft x✝ i + nim (typein (fun x x_1 => x < x_1) i₂) ≈ 0
      apply Equiv.trans (add_congr_left (equiv_nim_grundyValue (G.moveLeft i)))
      -- ⊢ nim (grundyValue (moveLeft G i)) + nim (typein (fun x x_1 => x < x_1) i₂) ≈ 0
      simpa only [hi] using Impartial.add_self (nim (grundyValue (G.moveLeft i)))
      -- 🎉 no goals
termination_by equiv_nim_grundyValue G _ => G
decreasing_by pgame_wf_tac
              -- 🎉 no goals
              -- 🎉 no goals
#align pgame.equiv_nim_grundy_value PGame.equiv_nim_grundyValue

theorem grundyValue_eq_iff_equiv_nim {G : PGame} [G.Impartial] {o : Ordinal} :
    grundyValue G = o ↔ (G ≈ nim o) :=
  ⟨by rintro rfl; exact equiv_nim_grundyValue G,
      -- ⊢ G ≈ nim (grundyValue G)
                  -- 🎉 no goals
   by intro h; rw [← nim_equiv_iff_eq]; exact Equiv.trans (Equiv.symm (equiv_nim_grundyValue G)) h⟩
      -- ⊢ grundyValue G = o
               -- ⊢ nim (grundyValue G) ≈ nim o
                                        -- 🎉 no goals
#align pgame.grundy_value_eq_iff_equiv_nim PGame.grundyValue_eq_iff_equiv_nim

@[simp]
theorem nim_grundyValue (o : Ordinal.{u}) : grundyValue (nim o) = o :=
  grundyValue_eq_iff_equiv_nim.2 PGame.equiv_rfl
#align pgame.nim_grundy_value PGame.nim_grundyValue

theorem grundyValue_eq_iff_equiv (G H : PGame) [G.Impartial] [H.Impartial] :
    grundyValue G = grundyValue H ↔ (G ≈ H) :=
  grundyValue_eq_iff_equiv_nim.trans (equiv_congr_left.1 (equiv_nim_grundyValue H) _).symm
#align pgame.grundy_value_eq_iff_equiv PGame.grundyValue_eq_iff_equiv

@[simp]
theorem grundyValue_zero : grundyValue 0 = 0 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_zero_equiv)
#align pgame.grundy_value_zero PGame.grundyValue_zero

theorem grundyValue_iff_equiv_zero (G : PGame) [G.Impartial] : grundyValue G = 0 ↔ (G ≈ 0) := by
  rw [← grundyValue_eq_iff_equiv, grundyValue_zero]
  -- 🎉 no goals
#align pgame.grundy_value_iff_equiv_zero PGame.grundyValue_iff_equiv_zero

@[simp]
theorem grundyValue_star : grundyValue star = 1 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_one_equiv)
#align pgame.grundy_value_star PGame.grundyValue_star

@[simp]
theorem grundyValue_neg (G : PGame) [G.Impartial] : grundyValue (-G) = grundyValue G := by
  rw [grundyValue_eq_iff_equiv_nim, neg_equiv_iff, neg_nim, ← grundyValue_eq_iff_equiv_nim]
  -- 🎉 no goals
#align pgame.grundy_value_neg PGame.grundyValue_neg

theorem grundyValue_eq_mex_right :
    ∀ (G : PGame) [G.Impartial],
      grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveRight i)
   | ⟨l, r, L, R⟩, _ => by
    rw [← grundyValue_neg, grundyValue_eq_mex_left]
    -- ⊢ (mex fun i => grundyValue (moveLeft (-mk l r L R) i)) = mex fun i => grundyV …
    congr
    -- ⊢ (fun i => grundyValue (moveLeft (-mk l r L R) i)) = fun i => grundyValue (mo …
    ext i
    -- ⊢ grundyValue (moveLeft (-mk l r L R) i) = grundyValue (moveRight (mk l r L R) …
    haveI : (R i).Impartial := @Impartial.moveRight_impartial ⟨l, r, L, R⟩ _ i
    -- ⊢ grundyValue (moveLeft (-mk l r L R) i) = grundyValue (moveRight (mk l r L R) …
    apply grundyValue_neg
    -- 🎉 no goals
#align pgame.grundy_value_eq_mex_right PGame.grundyValue_eq_mex_right

-- Todo: this actually generalizes to all ordinals, by defining `Ordinal.lxor` as the pairwise
-- `Nat.lxor'` of base `ω` Cantor normal forms.
/-- The Grundy value of the sum of two nim games with natural numbers of piles equals their bitwise
xor. -/
@[simp]
theorem grundyValue_nim_add_nim (n m : ℕ) :
    grundyValue (nim.{u} n + nim.{u} m) = Nat.lxor' n m := by
  -- We do strong induction on both variables.
  induction' n using Nat.strong_induction_on with n hn generalizing m
  -- ⊢ grundyValue (nim ↑n + nim ↑m) = ↑(Nat.lxor' n m)
  induction' m using Nat.strong_induction_on with m hm
  -- ⊢ grundyValue (nim ↑n + nim ↑m) = ↑(Nat.lxor' n m)
  rw [grundyValue_eq_mex_left]
  -- ⊢ (mex fun i => grundyValue (moveLeft (nim ↑n + nim ↑m) i)) = ↑(Nat.lxor' n m)
  refine (Ordinal.mex_le_of_ne.{u, u} fun i => ?_).antisymm
    (Ordinal.le_mex_of_forall fun ou hu => ?_)
  -- The Grundy value `Nat.lxor' n m` can't be reached by left moves.
  · apply leftMoves_add_cases i <;>
    -- ⊢ ∀ (i : LeftMoves (nim ↑n)), grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeft …
      · -- A left move leaves us with a Grundy value of `Nat.lxor' k m` for `k < n`, or
        -- `Nat.lxor' n k` for `k < m`.
        refine' fun a => leftMovesNimRecOn a fun ok hk => _
        -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inl (↑toLeftMo …
        -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inr (↑toLeftMo …
        -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inl (↑toLeftMo …
        obtain ⟨k, rfl⟩ := Ordinal.lt_omega.1 (hk.trans (Ordinal.nat_lt_omega _))
        -- ⊢ grundyValue (nim ↑k + nim ↑m) ≠ ↑(Nat.lxor' n m)
        -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inr (↑toLeftMo …
        simp only [add_moveLeft_inl, add_moveLeft_inr, moveLeft_nim', Equiv.symm_apply_apply]
        -- ⊢ grundyValue (nim ↑k + nim ↑m) ≠ ↑(Nat.lxor' n m)
        -- ⊢ grundyValue (nim ↑n + nim ↑k) ≠ ↑(Nat.lxor' n m)
        -- The inequality follows from injectivity.
        rw [nat_cast_lt] at hk
        -- ⊢ grundyValue (nim ↑n + nim ↑k) ≠ ↑(Nat.lxor' n m)
        -- ⊢ k = n
        first
        -- ⊢ k = n
        | rw [hn _ hk]
        | rw [hm _ hk]
        refine' fun h => hk.ne _
        -- ⊢ k = m
        rw [Ordinal.nat_cast_inj] at h
        -- ⊢ k = m
        first
        | rwa [Nat.lxor'_left_inj] at h
        | rwa [Nat.lxor'_right_inj] at h
  -- Every other smaller Grundy value can be reached by left moves.
  · -- If `u < Nat.lxor' m n`, then either `Nat.lxor' u n < m` or `Nat.lxor' u m < n`.
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (hu.trans (Ordinal.nat_lt_omega _))
    -- ⊢ ∃ i, grundyValue (moveLeft (nim ↑n + nim ↑m) i) = ↑u
    replace hu := Ordinal.nat_cast_lt.1 hu
    -- ⊢ ∃ i, grundyValue (moveLeft (nim ↑n + nim ↑m) i) = ↑u
    cases' Nat.lt_lxor'_cases hu with h h
    -- ⊢ ∃ i, grundyValue (moveLeft (nim ↑n + nim ↑m) i) = ↑u
    -- In the first case, reducing the `m` pile to `Nat.lxor' u n` gives the desired Grundy value.
    · refine' ⟨toLeftMovesAdd (Sum.inl <| toLeftMovesNim ⟨_, Ordinal.nat_cast_lt.2 h⟩), _⟩
      -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inl (↑toLeftMo …
      simp [Nat.lxor_cancel_right, hn _ h]
      -- 🎉 no goals
    -- In the second case, reducing the `n` pile to `Nat.lxor' u m` gives the desired Grundy value.
    · refine' ⟨toLeftMovesAdd (Sum.inr <| toLeftMovesNim ⟨_, Ordinal.nat_cast_lt.2 h⟩), _⟩
      -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inr (↑toLeftMo …
      have : n.lxor' (u.lxor' n) = u; rw [Nat.lxor'_comm u, Nat.lxor'_cancel_left]
      -- ⊢ Nat.lxor' n (Nat.lxor' u n) = u
                                      -- ⊢ grundyValue (moveLeft (nim ↑n + nim ↑m) (↑toLeftMovesAdd (Sum.inr (↑toLeftMo …
      simpa [hm _ h] using this
      -- 🎉 no goals
#align pgame.grundy_value_nim_add_nim PGame.grundyValue_nim_add_nim

theorem nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (Nat.lxor' n m) := by
  rw [← grundyValue_eq_iff_equiv_nim, grundyValue_nim_add_nim]
  -- 🎉 no goals
#align pgame.nim_add_nim_equiv PGame.nim_add_nim_equiv

theorem grundyValue_add (G H : PGame) [G.Impartial] [H.Impartial] {n m : ℕ} (hG : grundyValue G = n)
    (hH : grundyValue H = m) : grundyValue (G + H) = Nat.lxor' n m := by
  rw [← nim_grundyValue (Nat.lxor' n m), grundyValue_eq_iff_equiv]
  -- ⊢ G + H ≈ nim ↑(Nat.lxor' n m)
  refine' Equiv.trans _ nim_add_nim_equiv
  -- ⊢ G + H ≈ nim ↑n + nim ↑m
  convert add_congr (equiv_nim_grundyValue G) (equiv_nim_grundyValue H) <;> simp only [hG, hH]
  -- ⊢ ↑n = grundyValue G
                                                                            -- 🎉 no goals
                                                                            -- 🎉 no goals
#align pgame.grundy_value_add PGame.grundyValue_add

end PGame
