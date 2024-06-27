/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Game.Birthday

#align_import set_theory.game.short from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Short games

A combinatorial game is `Short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We prove that the order relations `≤` and `<`, and the equivalence relation `≈`, are decidable on
short games, although unfortunately in practice `decide` doesn't seem to be able to
prove anything using these instances.
-/

-- Porting note: The local instances `moveLeftShort'` and `fintypeLeft` (and resp. `Right`)
-- trigger this error.
set_option synthInstance.checkSynthOrder false

universe u

namespace SetTheory

open scoped PGame

namespace PGame

/-- A short game is a game with a finite set of moves at every turn. -/
inductive Short : PGame.{u} → Type (u + 1)
  | mk :
    ∀ {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} (_ : ∀ i : α, Short (L i))
      (_ : ∀ j : β, Short (R j)) [Fintype α] [Fintype β], Short ⟨α, β, L, R⟩
#align pgame.short SetTheory.PGame.Short

-- Porting note: Added `simpNF` exception. It's unclear what puts `eq_iff_true_of_subsingleton` into
-- the simp set. A minimal reproduction of the simpNF error needs to import transitively at least
-- `Mathlib.Logic.Unique`.
--
-- The simplifier can already prove this using `eq_iff_true_of_subsingleton`
attribute [nolint simpNF] Short.mk.injEq

instance subsingleton_short (x : PGame) : Subsingleton (Short x) := by
  induction x with
  | mk xl xr xL xR =>
    constructor
    intro a b
    cases a; cases b
    congr!


-- Porting note: We use `induction` to prove `subsingleton_short` instead of recursion.
-- A proof using recursion generates a harder `decreasing_by` goal than in Lean 3 for some reason:
attribute [-instance] subsingleton_short in
theorem subsingleton_short_example : ∀ x : PGame, Subsingleton (Short x)
  | mk xl xr xL xR =>
    ⟨fun a b => by
      cases a; cases b
      congr!
      · funext x
        apply @Subsingleton.elim _ (subsingleton_short_example (xL x))
        -- Decreasing goal in Lean 4 is `Subsequent (xL x) (mk α β L R)`
        -- where `α`, `β`, `L`, and `R` are fresh hypotheses only propositionally
        -- equal to `xl`, `xr`, `xL`, and `xR`.
        -- (In Lean 3 it was `(mk xl xr xL xR)` instead.)
      · funext x
        apply @Subsingleton.elim _ (subsingleton_short_example (xR x))⟩
termination_by x => x
-- We need to unify a bunch of hypotheses before `pgame_wf_tac` can work.
decreasing_by all_goals {
  subst_vars
  simp only [mk.injEq, heq_eq_eq, true_and] at *
  casesm* _ ∧ _
  subst_vars
  pgame_wf_tac
}

#align pgame.subsingleton_short SetTheory.PGame.subsingleton_short

/-- A synonym for `Short.mk` that specifies the pgame in an implicit argument. -/
def Short.mk' {x : PGame} [Fintype x.LeftMoves] [Fintype x.RightMoves]
    (sL : ∀ i : x.LeftMoves, Short (x.moveLeft i))
    (sR : ∀ j : x.RightMoves, Short (x.moveRight j)) : Short x := by
  -- Porting note: Old proof relied on `unfreezingI`, which doesn't exist in Lean 4.
  convert Short.mk sL sR
  cases x
  dsimp
#align pgame.short.mk' SetTheory.PGame.Short.mk'

attribute [class] Short

/-- Extracting the `Fintype` instance for the indexing type for Left's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintypeLeft {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} [S : Short ⟨α, β, L, R⟩] :
    Fintype α := by cases' S with _ _ _ _ _ _ F _; exact F
#align pgame.fintype_left SetTheory.PGame.fintypeLeft

attribute [local instance] fintypeLeft

instance fintypeLeftMoves (x : PGame) [S : Short x] : Fintype x.LeftMoves := by
  cases S; assumption
#align pgame.fintype_left_moves SetTheory.PGame.fintypeLeftMoves

/-- Extracting the `Fintype` instance for the indexing type for Right's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintypeRight {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} [S : Short ⟨α, β, L, R⟩] :
    Fintype β := by cases' S with _ _ _ _ _ _ _ F; exact F
#align pgame.fintype_right SetTheory.PGame.fintypeRight

attribute [local instance] fintypeRight

instance fintypeRightMoves (x : PGame) [S : Short x] : Fintype x.RightMoves := by
  cases S; assumption
#align pgame.fintype_right_moves SetTheory.PGame.fintypeRightMoves

instance moveLeftShort (x : PGame) [S : Short x] (i : x.LeftMoves) : Short (x.moveLeft i) := by
  cases' S with _ _ _ _ L _ _ _; apply L
#align pgame.move_left_short SetTheory.PGame.moveLeftShort

/-- Extracting the `Short` instance for a move by Left.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def moveLeftShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (i : xl) : Short (xL i) := by
  cases' S with _ _ _ _ L _ _ _; apply L
#align pgame.move_left_short' SetTheory.PGame.moveLeftShort'

attribute [local instance] moveLeftShort'

instance moveRightShort (x : PGame) [S : Short x] (j : x.RightMoves) : Short (x.moveRight j) := by
  cases' S with _ _ _ _ _ R _ _; apply R
#align pgame.move_right_short SetTheory.PGame.moveRightShort

/-- Extracting the `Short` instance for a move by Right.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def moveRightShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (j : xr) : Short (xR j) := by
  cases' S with _ _ _ _ _ R _ _; apply R
#align pgame.move_right_short' SetTheory.PGame.moveRightShort'

attribute [local instance] moveRightShort'

theorem short_birthday (x : PGame.{u}) : [Short x] → x.birthday < Ordinal.omega := by
  -- Porting note: Again `induction` is used instead of `pgame_wf_tac`
  induction x with
  | mk xl xr xL xR ihl ihr =>
    intro hs
    rcases hs with ⟨sL, sR⟩
    rw [birthday, max_lt_iff]
    constructor
    all_goals
      rw [← Cardinal.ord_aleph0]
      refine
        Cardinal.lsub_lt_ord_of_isRegular.{u, u} Cardinal.isRegular_aleph0
          (Cardinal.lt_aleph0_of_finite _) fun i => ?_
      rw [Cardinal.ord_aleph0]
    · apply ihl
    · apply ihr
#align pgame.short_birthday SetTheory.PGame.short_birthday

/-- This leads to infinite loops if made into an instance. -/
def Short.ofIsEmpty {l r xL xR} [IsEmpty l] [IsEmpty r] : Short (PGame.mk l r xL xR) := by
  have : Fintype l := Fintype.ofIsEmpty
  have : Fintype r := Fintype.ofIsEmpty
  exact Short.mk isEmptyElim isEmptyElim
#align pgame.short.of_is_empty SetTheory.PGame.Short.ofIsEmpty

instance short0 : Short 0 :=
  Short.ofIsEmpty
#align pgame.short_0 SetTheory.PGame.short0

instance short1 : Short 1 :=
  Short.mk (fun i => by cases i; infer_instance) fun j => by cases j
#align pgame.short_1 SetTheory.PGame.short1

/-- Evidence that every `PGame` in a list is `Short`. -/
class inductive ListShort : List PGame.{u} → Type (u + 1)
  | nil : ListShort []
  -- Porting note: We introduce `cons` as a separate instance because attempting to use
  -- `[ListShort tl]` as a constructor argument errors saying that `ListShort tl` is not a class.
  -- Is this a bug in `class inductive`?
  | cons' {hd : PGame.{u}} {tl : List PGame.{u}} : Short hd → ListShort tl → ListShort (hd::tl)
#align pgame.list_short SetTheory.PGame.ListShort

attribute [instance] ListShort.nil

instance ListShort.cons (hd : PGame.{u}) [short_hd : Short hd]
                        (tl : List PGame.{u}) [short_tl : ListShort tl] :
    ListShort (hd::tl) :=
  cons' short_hd short_tl
#align pgame.list_short.cons SetTheory.PGame.ListShort.cons

instance listShortGet :
    ∀ (L : List PGame.{u}) [ListShort L] (i : Fin (List.length L)), Short (List.get L i)
  | [], _, n => by
    exfalso
    rcases n with ⟨_, ⟨⟩⟩;
  | _::_, ListShort.cons' S _, ⟨0, _⟩ => S
  | hd::tl, ListShort.cons' _ S, ⟨n + 1, h⟩ =>
    @listShortGet tl S ⟨n, (add_lt_add_iff_right 1).mp h⟩
#align pgame.list_short_nth_le SetTheory.PGame.listShortGet

instance shortOfLists : ∀ (L R : List PGame) [ListShort L] [ListShort R], Short (PGame.ofLists L R)
  | L, R, _, _ => by
    apply Short.mk
    · intros; infer_instance
    · intros; apply PGame.listShortGet
#align pgame.short_of_lists SetTheory.PGame.shortOfLists

/-- If `x` is a short game, and `y` is a relabelling of `x`, then `y` is also short. -/
def shortOfRelabelling : ∀ {x y : PGame.{u}}, Relabelling x y → Short x → Short y
  | x, y, ⟨L, R, rL, rR⟩, S => by
    haveI := Fintype.ofEquiv _ L
    haveI := Fintype.ofEquiv _ R
    exact
      Short.mk'
        (fun i => by rw [← L.right_inv i]; apply shortOfRelabelling (rL (L.symm i)) inferInstance)
        fun j => by simpa using shortOfRelabelling (rR (R.symm j)) inferInstance
#align pgame.short_of_relabelling SetTheory.PGame.shortOfRelabelling

instance shortNeg : ∀ (x : PGame.{u}) [Short x], Short (-x)
  | mk xl xr xL xR, _ => by
    exact Short.mk (fun i => shortNeg _) fun i => shortNeg _
#align pgame.short_neg SetTheory.PGame.shortNeg

instance shortAdd : ∀ (x y : PGame.{u}) [Short x] [Short y], Short (x + y)
  | mk xl xr xL xR, mk yl yr yL yR, _, _ => by
    apply Short.mk;
    all_goals
      rintro ⟨i⟩
      · apply shortAdd
      · change Short (mk xl xr xL xR + _); apply shortAdd
termination_by x y => (x, y)
#align pgame.short_add SetTheory.PGame.shortAdd

instance shortNat : ∀ n : ℕ, Short n
  | 0 => PGame.short0
  | n + 1 => @PGame.shortAdd _ _ (shortNat n) PGame.short1
#align pgame.short_nat SetTheory.PGame.shortNat

instance shortOfNat (n : ℕ) [Nat.AtLeastTwo n] : Short (no_index (OfNat.ofNat n)) := shortNat n

-- Porting note: `bit0` and `bit1` are deprecated so these instances can probably be removed.
set_option linter.deprecated false in
instance shortBit0 (x : PGame.{u}) [Short x] : Short (bit0 x) := by dsimp [bit0]; infer_instance
#align pgame.short_bit0 SetTheory.PGame.shortBit0

set_option linter.deprecated false in
instance shortBit1 (x : PGame.{u}) [Short x] : Short (bit1 x) := by dsimp [bit1]; infer_instance
#align pgame.short_bit1 SetTheory.PGame.shortBit1

/-- Auxiliary construction of decidability instances.
We build `Decidable (x ≤ y)` and `Decidable (x ⧏ y)` in a simultaneous induction.
Instances for the two projections separately are provided below.
-/
def leLFDecidable : ∀ (x y : PGame.{u}) [Short x] [Short y], Decidable (x ≤ y) × Decidable (x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR, shortx, shorty => by
    constructor
    · refine @decidable_of_iff' _ _ mk_le_mk (id ?_)
      apply @And.decidable _ _ ?_ ?_
      · apply @Fintype.decidableForallFintype xl _ ?_ _
        intro i
        apply (leLFDecidable _ _).2
      · apply @Fintype.decidableForallFintype yr _ ?_ _
        intro i
        apply (leLFDecidable _ _).2
    · refine @decidable_of_iff' _ _ mk_lf_mk (id ?_)
      apply @Or.decidable _ _ ?_ ?_
      · apply @Fintype.decidableExistsFintype yl _ ?_ _
        intro i
        apply (leLFDecidable _ _).1
      · apply @Fintype.decidableExistsFintype xr _ ?_ _
        intro i
        apply (leLFDecidable _ _).1
termination_by x y => (x, y)
#align pgame.le_lf_decidable SetTheory.PGame.leLFDecidable

instance leDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ≤ y) :=
  (leLFDecidable x y).1
#align pgame.le_decidable SetTheory.PGame.leDecidable

instance lfDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ⧏ y) :=
  (leLFDecidable x y).2
#align pgame.lf_decidable SetTheory.PGame.lfDecidable

instance ltDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x < y) :=
  And.decidable
#align pgame.lt_decidable SetTheory.PGame.ltDecidable

instance equivDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ≈ y) :=
  And.decidable
#align pgame.equiv_decidable SetTheory.PGame.equivDecidable

example : Short 0 := by infer_instance

example : Short 1 := by infer_instance

example : Short 2 := by infer_instance

example : Short (-2) := by infer_instance

example : Short (ofLists [0] [1]) := by infer_instance

example : Short (ofLists [-2, -1] [1]) := by infer_instance

example : Short (0 + 0) := by infer_instance

example : Decidable ((1 : PGame) ≤ 1) := by infer_instance

-- No longer works since definitional reduction of well-founded definitions has been restricted.
-- example : (0 : PGame.{u}) ≤ 0 := by decide
-- example : (1 : PGame.{u}) ≤ 1 := by decide
end PGame
