/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module set_theory.game.short
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Game.Birthday

/-!
# Short games

A combinatorial game is `short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We prove that the order relations `≤` and `<`, and the equivalence relation `≈`, are decidable on
short games, although unfortunately in practice `dec_trivial` doesn't seem to be able to
prove anything using these instances.
-/


universe u

open scoped PGame

namespace PGame

/-- A short game is a game with a finite set of moves at every turn. -/
inductive Short : PGame.{u} → Type (u + 1)
  | mk :
    ∀ {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} (_ : ∀ i : α, Short (L i))
      (_ : ∀ j : β, Short (R j)) [Fintype α] [Fintype β], Short ⟨α, β, L, R⟩
#align pgame.short PGame.Short

instance subsingleton_short : ∀ x : PGame, Subsingleton (Short x)
  | mk xl xr xL xR =>
    ⟨fun a b => by
      cases a; cases b
      congr!
      · funext x
        apply @Subsingleton.elim _ (subsingleton_short (xL x))
      · funext x
        apply @Subsingleton.elim _ (subsingleton_short (xR x))⟩
termination_by subsingleton_short x => x
decreasing_by pgame_wf_tac
#align pgame.subsingleton_short PGame.subsingleton_short

/-- A synonym for `short.mk` that specifies the pgame in an implicit argument. -/
def Short.mk' {x : PGame} [Fintype x.LeftMoves] [Fintype x.RightMoves]
    (sL : ∀ i : x.LeftMoves, Short (x.moveLeft i))
    (sR : ∀ j : x.RightMoves, Short (x.moveRight j)) : Short x := by
  (cases x; dsimp at *) <;> exact Short.mk sL sR
#align pgame.short.mk' PGame.Short.mk'

attribute [class] Short

/-- Extracting the `fintype` instance for the indexing type for Left's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintypeLeft {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} [S : Short ⟨α, β, L, R⟩] :
    Fintype α := by cases' S with _ _ _ _ _ _ F _; exact F
#align pgame.fintype_left PGame.fintypeLeft

attribute [local instance] fintypeLeft

instance fintypeLeftMoves (x : PGame) [S : Short x] : Fintype x.LeftMoves := by
  cases x; dsimp; infer_instance
#align pgame.fintype_left_moves PGame.fintypeLeftMoves

/-- Extracting the `fintype` instance for the indexing type for Right's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintypeRight {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} [S : Short ⟨α, β, L, R⟩] :
    Fintype β := by cases' S with _ _ _ _ _ _ _ F; exact F
#align pgame.fintype_right PGame.fintypeRight

attribute [local instance] fintypeRight

instance fintypeRightMoves (x : PGame) [S : Short x] : Fintype x.RightMoves := by
  cases x; dsimp; infer_instance
#align pgame.fintype_right_moves PGame.fintypeRightMoves

instance moveLeftShort (x : PGame) [S : Short x] (i : x.LeftMoves) : Short (x.moveLeft i) := by
  cases' S with _ _ _ _ L _ _ _; apply L
#align pgame.move_left_short PGame.moveLeftShort

/-- Extracting the `short` instance for a move by Left.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def moveLeftShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (i : xl) : Short (xL i) := by
  cases' S with _ _ _ _ L _ _ _; apply L
#align pgame.move_left_short' PGame.moveLeftShort'

attribute [local instance] moveLeftShort'

instance moveRightShort (x : PGame) [S : Short x] (j : x.RightMoves) : Short (x.moveRight j) := by
  cases' S with _ _ _ _ _ R _ _; apply R
#align pgame.move_right_short PGame.moveRightShort

/-- Extracting the `short` instance for a move by Right.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def moveRightShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (j : xr) : Short (xR j) := by
  cases' S with _ _ _ _ _ R _ _; apply R
#align pgame.move_right_short' PGame.moveRightShort'

attribute [local instance] moveRightShort'

theorem short_birthday : ∀ (x : PGame.{u}) [Short x], x.birthday < Ordinal.omega
  | ⟨xl, xr, xL, xR⟩, hs => by
    haveI := hs
    rcases hs with ⟨sL, sR⟩
    rw [birthday, max_lt_iff]
    constructor;
    all_goals
      rw [← Cardinal.ord_aleph0]
      refine'
        Cardinal.lsub_lt_ord_of_isRegular.{u, u} Cardinal.isRegular_aleph0
          (Cardinal.lt_aleph0_of_finite _) fun i => _
      rw [Cardinal.ord_aleph0]
      apply short_birthday _
    · exact move_left_short' xL xR i
    · exact move_right_short' xL xR i
termination_by short_birthday x _ => x
#align pgame.short_birthday PGame.short_birthday

/-- This leads to infinite loops if made into an instance. -/
def Short.ofIsEmpty {l r xL xR} [IsEmpty l] [IsEmpty r] : Short (mk l r xL xR) :=
  Short.mk isEmptyElim isEmptyElim
#align pgame.short.of_is_empty PGame.Short.ofIsEmpty

instance short0 : Short 0 :=
  Short.ofIsEmpty
#align pgame.short_0 PGame.short0

instance short1 : Short 1 :=
  Short.mk (fun i => by cases i; infer_instance) fun j => by cases j
#align pgame.short_1 PGame.short1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Evidence that every `pgame` in a list is `short`. -/
inductive ListShort : List PGame.{u} → Type (u + 1)
  | nil : list_short []
  | cons : ∀ (hd : PGame.{u}) [Short hd] (tl : List PGame.{u}) [list_short tl], list_short (hd::tl)
#align pgame.list_short PGame.ListShort

attribute [class] list_short

attribute [instance] list_short.nil list_short.cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance listShortNthLe :
    ∀ (L : List PGame.{u}) [ListShort L] (i : Fin (List.length L)), Short (List.nthLe L i i.is_lt)
  | [], _, n => by exfalso; rcases n with ⟨_, ⟨⟩⟩
  | hd::tl, @list_short.cons _ S _ _, ⟨0, _⟩ => S
  | hd::tl, @list_short.cons _ _ _ S, ⟨n + 1, h⟩ =>
    @list_short_nth_le tl S ⟨n, (add_lt_add_iff_right 1).mp h⟩
#align pgame.list_short_nth_le PGame.listShortNthLe

instance shortOfLists : ∀ (L R : List PGame) [ListShort L] [ListShort R], Short (PGame.ofLists L R)
  | L, R, _, _ => by
    skip; apply short.mk
    · intros; infer_instance
    · intros; apply PGame.listShortNthLe
#align pgame.short_of_lists PGame.shortOfLists

-- where does the subtype.val come from?
/-- If `x` is a short game, and `y` is a relabelling of `x`, then `y` is also short. -/
def shortOfRelabelling : ∀ {x y : PGame.{u}} (R : Relabelling x y) (S : Short x), Short y
  | x, y, ⟨L, R, rL, rR⟩, S => by
    skip
    haveI := Fintype.ofEquiv _ L
    haveI := Fintype.ofEquiv _ R
    exact
      short.mk'
        (fun i => by rw [← L.right_inv i]; apply short_of_relabelling (rL (L.symm i)) inferInstance)
        fun j => by simpa using short_of_relabelling (rR (R.symm j)) inferInstance
#align pgame.short_of_relabelling PGame.shortOfRelabelling

instance shortNeg : ∀ (x : PGame.{u}) [Short x], Short (-x)
  | mk xl xr xL xR, _ => by skip; exact short.mk (fun i => short_neg _) fun i => short_neg _
decreasing_by pgame_wf_tac
#align pgame.short_neg PGame.shortNeg

instance shortAdd : ∀ (x y : PGame.{u}) [Short x] [Short y], Short (x + y)
  | mk xl xr xL xR, mk yl yr yL yR, _, _ => by
    skip
    apply short.mk;
    all_goals
      rintro ⟨i⟩
      · apply short_add
      · change short (mk xl xr xL xR + _); apply short_add
decreasing_by pgame_wf_tac
#align pgame.short_add PGame.shortAdd

instance shortNat : ∀ n : ℕ, Short n
  | 0 => PGame.short0
  | n + 1 => @PGame.shortAdd _ _ (short_nat n) PGame.short1
#align pgame.short_nat PGame.shortNat

instance shortBit0 (x : PGame.{u}) [Short x] : Short (bit0 x) := by dsimp [bit0]; infer_instance
#align pgame.short_bit0 PGame.shortBit0

instance shortBit1 (x : PGame.{u}) [Short x] : Short (bit1 x) := by dsimp [bit1]; infer_instance
#align pgame.short_bit1 PGame.shortBit1

/-- Auxiliary construction of decidability instances.
We build `decidable (x ≤ y)` and `decidable (x ⧏ y)` in a simultaneous induction.
Instances for the two projections separately are provided below.
-/
def leLfDecidable : ∀ (x y : PGame.{u}) [Short x] [Short y], Decidable (x ≤ y) × Decidable (x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR, shortx, shorty => by
    skip
    constructor
    · refine' @decidable_of_iff' _ _ mk_le_mk (id _)
      apply @And.decidable _ _ _ _
      · apply @Fintype.decidableForallFintype xl _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).2 <;> infer_instance
      · apply @Fintype.decidableForallFintype yr _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).2 <;> infer_instance
    · refine' @decidable_of_iff' _ _ mk_lf_mk (id _)
      apply @Or.decidable _ _ _ _
      · apply @Fintype.decidableExistsFintype yl _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).1 <;> infer_instance
      · apply @Fintype.decidableExistsFintype xr _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).1 <;> infer_instance
decreasing_by pgame_wf_tac
#align pgame.le_lf_decidable PGame.leLfDecidable

instance leDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ≤ y) :=
  (leLfDecidable x y).1
#align pgame.le_decidable PGame.leDecidable

instance lfDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ⧏ y) :=
  (leLfDecidable x y).2
#align pgame.lf_decidable PGame.lfDecidable

instance ltDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x < y) :=
  And.decidable
#align pgame.lt_decidable PGame.ltDecidable

instance equivDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ≈ y) :=
  And.decidable
#align pgame.equiv_decidable PGame.equivDecidable

example : Short 0 := by infer_instance

example : Short 1 := by infer_instance

example : Short 2 := by infer_instance

example : Short (-2) := by infer_instance

example : Short (ofLists [0] [1]) := by infer_instance

example : Short (ofLists [-2, -1] [1]) := by infer_instance

example : Short (0 + 0) := by infer_instance

example : Decidable ((1 : PGame) ≤ 1) := by infer_instance

-- No longer works since definitional reduction of well-founded definitions has been restricted.
-- example : (0 : pgame) ≤ 0 := dec_trivial
-- example : (1 : pgame) ≤ 1 := dec_trivial
end PGame
