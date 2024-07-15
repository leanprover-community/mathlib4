/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade, Yuyang Zhao
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Ring.Int
import Mathlib.SetTheory.Game.PGame
import Mathlib.Tactic.Abel

#align_import set_theory.game.basic from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Combinatorial games.

In this file we construct an instance `OrderedAddCommGroup SetTheory.Game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/

-- Porting note: many definitions here are noncomputable as the compiler does not support PGame.rec
noncomputable section

namespace SetTheory

open Function PGame

universe u

-- Porting note: moved the setoid instance to PGame.lean

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `PGame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbrev Game :=
  Quotient PGame.setoid
#align game SetTheory.Game

namespace Game

-- Porting note (#11445): added this definition
/-- Negation of games. -/
instance : Neg Game where
  neg := Quot.map Neg.neg <| fun _ _ => (neg_equiv_neg_iff).2

instance : Zero Game where zero := ⟦0⟧
instance : Add Game where
  add := Quotient.map₂ HAdd.hAdd <| fun _ _ hx _ _ hy => PGame.add_congr hx hy

instance instAddCommGroupWithOneGame : AddCommGroupWithOne Game where
  zero := ⟦0⟧
  one := ⟦1⟧
  add_zero := by
    rintro ⟨x⟩
    exact Quot.sound (add_zero_equiv x)
  zero_add := by
    rintro ⟨x⟩
    exact Quot.sound (zero_add_equiv x)
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact Quot.sound add_assoc_equiv
  add_left_neg := Quotient.ind <| fun x => Quot.sound (add_left_neg_equiv x)
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    exact Quot.sound add_comm_equiv
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Inhabited Game :=
  ⟨0⟩

instance instPartialOrderGame : PartialOrder Game where
  le := Quotient.lift₂ (· ≤ ·) fun x₁ y₁ x₂ y₂ hx hy => propext (le_congr hx hy)
  le_refl := by
    rintro ⟨x⟩
    exact le_refl x
  le_trans := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact @le_trans _ _ x y z
  le_antisymm := by
    rintro ⟨x⟩ ⟨y⟩ h₁ h₂
    apply Quot.sound
    exact ⟨h₁, h₂⟩
  lt := Quotient.lift₂ (· < ·) fun x₁ y₁ x₂ y₂ hx hy => propext (lt_congr hx hy)
  lt_iff_le_not_le := by
    rintro ⟨x⟩ ⟨y⟩
    exact @lt_iff_le_not_le _ _ x y

/-- The less or fuzzy relation on games.

If `0 ⧏ x` (less or fuzzy with), then Left can win `x` as the first player. -/
def LF : Game → Game → Prop :=
  Quotient.lift₂ PGame.LF fun _ _ _ _ hx hy => propext (lf_congr hx hy)
#align game.lf SetTheory.Game.LF

local infixl:50 " ⧏ " => LF

/-- On `Game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem not_le : ∀ {x y : Game}, ¬x ≤ y ↔ y ⧏ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact PGame.not_le
#align game.not_le SetTheory.Game.not_le

/-- On `Game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem not_lf : ∀ {x y : Game}, ¬x ⧏ y ↔ y ≤ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact PGame.not_lf
#align game.not_lf SetTheory.Game.not_lf

-- Porting note: had to replace ⧏ with LF, otherwise cannot differentiate with the operator on PGame
instance : IsTrichotomous Game LF :=
  ⟨by
    rintro ⟨x⟩ ⟨y⟩
    change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _
    rw [Quotient.eq]
    apply lf_or_equiv_or_gf⟩

/-! It can be useful to use these lemmas to turn `PGame` inequalities into `Game` inequalities, as
the `AddCommGroup` structure on `Game` often simplifies many proofs. -/

-- Porting note: In a lot of places, I had to add explicitely that the quotient element was a Game.
-- In Lean4, quotients don't have the setoid as an instance argument,
-- but as an explicit argument, see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
theorem PGame.le_iff_game_le {x y : PGame} : x ≤ y ↔ (⟦x⟧ : Game) ≤ ⟦y⟧ :=
  Iff.rfl
#align game.pgame.le_iff_game_le SetTheory.Game.PGame.le_iff_game_le

theorem PGame.lf_iff_game_lf {x y : PGame} : PGame.LF x y ↔ ⟦x⟧ ⧏ ⟦y⟧ :=
  Iff.rfl
#align game.pgame.lf_iff_game_lf SetTheory.Game.PGame.lf_iff_game_lf

theorem PGame.lt_iff_game_lt {x y : PGame} : x < y ↔ (⟦x⟧ : Game) < ⟦y⟧ :=
  Iff.rfl
#align game.pgame.lt_iff_game_lt SetTheory.Game.PGame.lt_iff_game_lt

theorem PGame.equiv_iff_game_eq {x y : PGame} : x ≈ y ↔ (⟦x⟧ : Game) = ⟦y⟧ :=
  (@Quotient.eq' _ _ x y).symm
#align game.pgame.equiv_iff_game_eq SetTheory.Game.PGame.equiv_iff_game_eq

/-- The fuzzy, confused, or incomparable relation on games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy : Game → Game → Prop :=
  Quotient.lift₂ PGame.Fuzzy fun _ _ _ _ hx hy => propext (fuzzy_congr hx hy)
#align game.fuzzy SetTheory.Game.Fuzzy

local infixl:50 " ‖ " => Fuzzy

theorem PGame.fuzzy_iff_game_fuzzy {x y : PGame} : PGame.Fuzzy x y ↔ ⟦x⟧ ‖ ⟦y⟧ :=
  Iff.rfl
#align game.pgame.fuzzy_iff_game_fuzzy SetTheory.Game.PGame.fuzzy_iff_game_fuzzy

instance covariantClass_add_le : CovariantClass Game Game (· + ·) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_le SetTheory.Game.covariantClass_add_le

instance covariantClass_swap_add_le : CovariantClass Game Game (swap (· + ·)) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_le SetTheory.Game.covariantClass_swap_add_le

instance covariantClass_add_lt : CovariantClass Game Game (· + ·) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_lt SetTheory.Game.covariantClass_add_lt

instance covariantClass_swap_add_lt : CovariantClass Game Game (swap (· + ·)) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_lt SetTheory.Game.covariantClass_swap_add_lt

theorem add_lf_add_right : ∀ {b c : Game} (_ : b ⧏ c) (a), (b + a : Game) ⧏ c + a := by
  rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩
  apply PGame.add_lf_add_right h
#align game.add_lf_add_right SetTheory.Game.add_lf_add_right

theorem add_lf_add_left : ∀ {b c : Game} (_ : b ⧏ c) (a), (a + b : Game) ⧏ a + c := by
  rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩
  apply PGame.add_lf_add_left h
#align game.add_lf_add_left SetTheory.Game.add_lf_add_left

instance orderedAddCommGroup : OrderedAddCommGroup Game :=
  { Game.instAddCommGroupWithOneGame, Game.instPartialOrderGame with
    add_le_add_left := @add_le_add_left _ _ _ Game.covariantClass_add_le }
#align game.ordered_add_comm_group SetTheory.Game.orderedAddCommGroup

/-- A small family of games is bounded above. -/
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Game.{u}) :
    BddAbove (Set.range f) := by
  obtain ⟨x, hx⟩ := PGame.bddAbove_range_of_small (Quotient.out ∘ f)
  refine ⟨⟦x⟧, Set.forall_mem_range.2 fun i ↦ ?_⟩
  simpa [PGame.le_iff_game_le] using hx $ Set.mem_range_self i

/-- A small set of games is bounded above. -/
lemma bddAbove_of_small (s : Set Game.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → Game.{u})
#align game.bdd_above_of_small SetTheory.Game.bddAbove_of_small

/-- A small family of games is bounded below. -/
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Game.{u}) :
    BddBelow (Set.range f) := by
  obtain ⟨x, hx⟩ := PGame.bddBelow_range_of_small (Quotient.out ∘ f)
  refine ⟨⟦x⟧, Set.forall_mem_range.2 fun i ↦ ?_⟩
  simpa [PGame.le_iff_game_le] using hx $ Set.mem_range_self i

/-- A small set of games is bounded below. -/
lemma bddBelow_of_small (s : Set Game.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → Game.{u})
#align game.bdd_below_of_small SetTheory.Game.bddBelow_of_small

end Game

namespace PGame

@[simp]
theorem quot_neg (a : PGame) : (⟦-a⟧ : Game) = -⟦a⟧ :=
  rfl
#align pgame.quot_neg SetTheory.PGame.quot_neg

@[simp]
theorem quot_add (a b : PGame) : ⟦a + b⟧ = (⟦a⟧ : Game) + ⟦b⟧ :=
  rfl
#align pgame.quot_add SetTheory.PGame.quot_add

@[simp]
theorem quot_sub (a b : PGame) : ⟦a - b⟧ = (⟦a⟧ : Game) - ⟦b⟧ :=
  rfl
#align pgame.quot_sub SetTheory.PGame.quot_sub

theorem quot_eq_of_mk'_quot_eq {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, (⟦x.moveLeft i⟧ : Game) = ⟦y.moveLeft (L i)⟧)
    (hr : ∀ j, (⟦x.moveRight j⟧ : Game) = ⟦y.moveRight (R j)⟧) : (⟦x⟧ : Game) = ⟦y⟧ := by
  exact Quot.sound (.of_equiv L R (fun _ => Game.PGame.equiv_iff_game_eq.2 (hl _))
                                  (fun _ => Game.PGame.equiv_iff_game_eq.2 (hr _)))
#align pgame.quot_eq_of_mk_quot_eq SetTheory.PGame.quot_eq_of_mk'_quot_eq

theorem quot_mul_comm (x y : PGame.{u}) : (⟦x * y⟧ : Game) = ⟦y * x⟧ :=
  Quot.sound (x.mul_comm y).equiv
#align pgame.quot_mul_comm SetTheory.PGame.quot_mul_comm

@[simp]
theorem quot_mul_zero (x : PGame) : (⟦x * 0⟧ : Game) = ⟦0⟧ :=
  @Quotient.sound _ _ (x * 0) _ x.mul_zero_equiv
#align pgame.quot_mul_zero SetTheory.PGame.quot_mul_zero

@[simp]
theorem quot_zero_mul (x : PGame) : (⟦0 * x⟧ : Game) = ⟦0⟧ :=
  @Quotient.sound _ _ (0 * x) _ x.zero_mul_equiv
#align pgame.quot_zero_mul SetTheory.PGame.quot_zero_mul

@[simp]
theorem quot_neg_mul (x y : PGame) : (⟦-x * y⟧ : Game) = -⟦x * y⟧ :=
  Quot.sound (x.neg_mul y).equiv
#align pgame.quot_neg_mul SetTheory.PGame.quot_neg_mul

@[simp]
theorem quot_mul_neg (x y : PGame) : ⟦x * -y⟧ = (-⟦x * y⟧ : Game) :=
  Quot.sound (x.mul_neg y ▸ Setoid.refl _) -- Porting note: was `of_eq (x.mul_neg y)`
#align pgame.quot_mul_neg SetTheory.PGame.quot_mul_neg

theorem quot_neg_mul_neg (x y : PGame) : ⟦-x * -y⟧ = (⟦x * y⟧ : Game) := by simp

@[simp]
theorem quot_left_distrib (x y z : PGame) : (⟦x * (y + z)⟧ : Game) = ⟦x * y⟧ + ⟦x * z⟧ :=
  match x, y, z with
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine quot_eq_of_mk'_quot_eq ?_ ?_ ?_ ?_
    · fconstructor
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          -- Porting note: we've increased `maxDepth` here from `5` to `6`.
          -- Likely this sort of off-by-one error is just a change in the implementation
          -- of `solve_by_elim`.
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    · fconstructor
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { maxDepth := 6 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    -- Porting note: explicitly wrote out arguments to each recursive
    -- quot_left_distrib reference below, because otherwise the decreasing_by block
    -- failed. Previously, each branch ended with: `simp [quot_left_distrib]; abel`
    -- See https://github.com/leanprover/lean4/issues/2288
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧ =
            ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xL i) (yL j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧ =
            ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (zL k)]
        abel
      · change
          ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧ =
            ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xR i) (yR j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧ =
            ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (zR k)]
        abel
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧ =
            ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xL i) (yR j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧ =
            ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_left_distrib (xL i) (mk yl yr yL yR) (zR k)]
        abel
      · change
          ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧ =
            ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_left_distrib (xR i) (yL j) (mk zl zr zL zR)]
        abel
      · change
          ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧ =
            ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧
        simp only [quot_sub, quot_add]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_left_distrib (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_left_distrib (xR i) (mk yl yr yL yR) (zL k)]
        abel
  termination_by (x, y, z)
#align pgame.quot_left_distrib SetTheory.PGame.quot_left_distrib

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv (x y z : PGame) : x * (y + z) ≈ x * y + x * z :=
  Quotient.exact <| quot_left_distrib _ _ _
#align pgame.left_distrib_equiv SetTheory.PGame.left_distrib_equiv

@[simp]
theorem quot_left_distrib_sub (x y z : PGame) : (⟦x * (y - z)⟧ : Game) = ⟦x * y⟧ - ⟦x * z⟧ := by
  change (⟦x * (y + -z)⟧ : Game) = ⟦x * y⟧ + -⟦x * z⟧
  rw [quot_left_distrib, quot_mul_neg]
#align pgame.quot_left_distrib_sub SetTheory.PGame.quot_left_distrib_sub

@[simp]
theorem quot_right_distrib (x y z : PGame) : (⟦(x + y) * z⟧ : Game) = ⟦x * z⟧ + ⟦y * z⟧ := by
  simp only [quot_mul_comm, quot_left_distrib]
#align pgame.quot_right_distrib SetTheory.PGame.quot_right_distrib

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : PGame) : (x + y) * z ≈ x * z + y * z :=
  Quotient.exact <| quot_right_distrib _ _ _
#align pgame.right_distrib_equiv SetTheory.PGame.right_distrib_equiv

@[simp]
theorem quot_right_distrib_sub (x y z : PGame) : (⟦(y - z) * x⟧ : Game) = ⟦y * x⟧ - ⟦z * x⟧ := by
  change (⟦(y + -z) * x⟧ : Game) = ⟦y * x⟧ + -⟦z * x⟧
  rw [quot_right_distrib, quot_neg_mul]
#align pgame.quot_right_distrib_sub SetTheory.PGame.quot_right_distrib_sub

@[simp]
theorem quot_mul_one (x : PGame) : (⟦x * 1⟧ : Game) = ⟦x⟧ :=
  Quot.sound x.mul_one.equiv
#align pgame.quot_mul_one SetTheory.PGame.quot_mul_one

@[simp]
theorem quot_one_mul (x : PGame) : (⟦1 * x⟧ : Game) = ⟦x⟧ :=
  Quot.sound x.one_mul.equiv
#align pgame.quot_one_mul SetTheory.PGame.quot_one_mul

theorem quot_mul_assoc (x y z : PGame) : (⟦x * y * z⟧ : Game) = ⟦x * (y * z)⟧ :=
  match x, y, z with
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine quot_eq_of_mk'_quot_eq ?_ ?_ ?_ ?_
    · fconstructor
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          -- Porting note: as above, increased the `maxDepth` here by 1.
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    · fconstructor
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { maxDepth := 8 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    -- Porting note: explicitly wrote out arguments to each recursive
    -- quot_mul_assoc reference below, because otherwise the decreasing_by block
    -- failed. Each branch previously ended with: `simp [quot_mul_assoc]; abel`
    -- See https://github.com/leanprover/lean4/issues/2288
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zL k -
                (xL i * y + x * yL j - xL i * yL j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xL i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zL k)]
        rw [quot_mul_assoc (xL i) (yL j) (zL k)]
        abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zL k -
                (xR i * y + x * yR j - xR i * yR j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xR i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zL k)]
        rw [quot_mul_assoc (xR i) (yR j) (zL k)]
        abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zR k -
                (xL i * y + x * yR j - xL i * yR j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xL i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zR k)]
        rw [quot_mul_assoc (xL i) (yR j) (zR k)]
        abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zR k -
                (xR i * y + x * yL j - xR i * yL j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xR i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zR k)]
        rw [quot_mul_assoc (xR i) (yL j) (zR k)]
        abel
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zR k -
                (xL i * y + x * yL j - xL i * yL j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xL i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zR k)]
        rw [quot_mul_assoc (xL i) (yL j) (zR k)]
        abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zR k -
                (xR i * y + x * yR j - xR i * yR j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xR i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zR k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zR k)]
        rw [quot_mul_assoc (xR i) (yR j) (zR k)]
        abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zL k -
                (xL i * y + x * yR j - xL i * yR j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xL i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xL i) (yR j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xL i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yR j) (zL k)]
        rw [quot_mul_assoc (xL i) (yR j) (zL k)]
        abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zL k -
                (xR i * y + x * yL j - xR i * yL j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xR i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp only [quot_sub, quot_add, quot_right_distrib_sub, quot_right_distrib,
                   quot_left_distrib_sub, quot_left_distrib]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (xR i) (yL j) (mk zl zr zL zR)]
        rw [quot_mul_assoc (mk xl xr xL xR) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (xR i) (mk yl yr yL yR) (zL k)]
        rw [quot_mul_assoc (mk xl xr xL xR) (yL j) (zL k)]
        rw [quot_mul_assoc (xR i) (yL j) (zL k)]
        abel
  termination_by (x, y, z)
#align pgame.quot_mul_assoc SetTheory.PGame.quot_mul_assoc

/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem mul_assoc_equiv (x y z : PGame) : x * y * z ≈ x * (y * z) :=
  Quotient.exact <| quot_mul_assoc _ _ _
#align pgame.mul_assoc_equiv SetTheory.PGame.mul_assoc_equiv

/-- The left options of `x * y` of the first kind, i.e. of the form `xL * y + x * yL - xL * yL`. -/
def mulOption (x y : PGame) (i : LeftMoves x) (j : LeftMoves y) : PGame :=
  x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j

/-- Any left option of `x * y` of the first kind is also a left option of `x * -(-y)` of
  the first kind. -/
lemma mulOption_neg_neg {x} (y) {i j} :
    mulOption x y i j = mulOption x (-(-y)) i (toLeftMovesNeg <| toRightMovesNeg j) := by
  dsimp only [mulOption]
  congr 2
  rw [neg_neg]
  iterate 2 rw [moveLeft_neg, moveRight_neg, neg_neg]

/-- The left options of `x * y` agree with that of `y * x` up to equivalence. -/
lemma mulOption_symm (x y) {i j} : ⟦mulOption x y i j⟧ = (⟦mulOption y x j i⟧ : Game) := by
  dsimp only [mulOption, quot_sub, quot_add]
  rw [add_comm]
  congr 1
  on_goal 1 => congr 1
  all_goals rw [quot_mul_comm]

/-- The left options of `x * y` of the second kind are the left options of `(-x) * (-y)` of the
  first kind, up to equivalence. -/
lemma leftMoves_mul_iff {x y : PGame} (P : Game → Prop) :
    (∀ k, P ⟦(x * y).moveLeft k⟧) ↔
    (∀ i j, P ⟦mulOption x y i j⟧) ∧ (∀ i j, P ⟦mulOption (-x) (-y) i j⟧) := by
  cases x; cases y
  constructor <;> intro h
  on_goal 1 =>
    constructor <;> intros i j
    · exact h (Sum.inl (i, j))
    convert h (Sum.inr (i, j)) using 1
  on_goal 2 =>
    rintro (⟨i, j⟩ | ⟨i, j⟩)
    exact h.1 i j
    convert h.2 i j using 1
  all_goals
    dsimp only [mk_mul_moveLeft_inr, quot_sub, quot_add, neg_def, mulOption, moveLeft_mk]
    rw [← neg_def, ← neg_def]
    congr 1
    on_goal 1 => congr 1
    all_goals rw [quot_neg_mul_neg]

/-- The right options of `x * y` are the left options of `x * (-y)` and of `(-x) * y` of the first
  kind, up to equivalence. -/
lemma rightMoves_mul_iff {x y : PGame} (P : Game → Prop) :
    (∀ k, P ⟦(x * y).moveRight k⟧) ↔
    (∀ i j, P (-⟦mulOption x (-y) i j⟧)) ∧ (∀ i j, P (-⟦mulOption (-x) y i j⟧)) := by
  cases x; cases y
  constructor <;> intro h
  on_goal 1 =>
    constructor <;> intros i j
    convert h (Sum.inl (i, j))
  on_goal 2 => convert h (Sum.inr (i, j))
  on_goal 3 =>
    rintro (⟨i, j⟩ | ⟨i, j⟩)
    convert h.1 i j using 1
    on_goal 2 => convert h.2 i j using 1
  all_goals
    dsimp [mulOption]
    rw [neg_sub', neg_add, ← neg_def]
    congr 1
    on_goal 1 => congr 1
  any_goals rw [quot_neg_mul, neg_neg]
  iterate 6 rw [quot_mul_neg, neg_neg]

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `invVal` is the function part. -/
inductive InvTy (l r : Type u) : Bool → Type u
  | zero : InvTy l r false
  | left₁ : r → InvTy l r false → InvTy l r false
  | left₂ : l → InvTy l r true → InvTy l r false
  | right₁ : l → InvTy l r false → InvTy l r true
  | right₂ : r → InvTy l r true → InvTy l r true
#align pgame.inv_ty SetTheory.PGame.InvTy

instance (l r : Type u) [IsEmpty l] [IsEmpty r] : IsEmpty (InvTy l r true) :=
  ⟨by rintro (_ | _ | _ | a | a) <;> exact isEmptyElim a⟩

instance InvTy.instInhabited (l r : Type u) : Inhabited (InvTy l r false) :=
  ⟨InvTy.zero⟩

instance uniqueInvTy (l r : Type u) [IsEmpty l] [IsEmpty r] : Unique (InvTy l r false) :=
  { InvTy.instInhabited l r with
    uniq := by
      rintro (a | a | a)
      · rfl
      all_goals exact isEmptyElim a }
#align pgame.unique_inv_ty SetTheory.PGame.uniqueInvTy

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `InvTy`. -/
def invVal {l r} (L : l → PGame) (R : r → PGame) (IHl : l → PGame) (IHr : r → PGame)
    (x : PGame) : ∀ {b}, InvTy l r b → PGame
  | _, InvTy.zero => 0
  | _, InvTy.left₁ i j => (1 + (R i - x) * invVal L R IHl IHr x j) * IHr i
  | _, InvTy.left₂ i j => (1 + (L i - x) * invVal L R IHl IHr x j) * IHl i
  | _, InvTy.right₁ i j => (1 + (L i - x) * invVal L R IHl IHr x j) * IHl i
  | _, InvTy.right₂ i j => (1 + (R i - x) * invVal L R IHl IHr x j) * IHr i
#align pgame.inv_val SetTheory.PGame.invVal

@[simp]
theorem invVal_isEmpty {l r : Type u} {b} (L R IHl IHr) (i : InvTy l r b) (x) [IsEmpty l]
    [IsEmpty r] : invVal L R IHl IHr x i = 0 := by
  cases' i with a _ a _ a _ a
  · rfl
  all_goals exact isEmptyElim a
#align pgame.inv_val_is_empty SetTheory.PGame.invVal_isEmpty

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : PGame → PGame
  | ⟨l, r, L, R⟩ =>
    let l' := { i // 0 < L i }
    let L' : l' → PGame := fun i => L i.1
    let IHl' : l' → PGame := fun i => inv' (L i.1)
    let IHr i := inv' (R i)
    let x := mk l r L R
    ⟨InvTy l' r false, InvTy l' r true, invVal L' R IHl' IHr x, invVal L' R IHl' IHr x⟩
#align pgame.inv' SetTheory.PGame.inv'

theorem zero_lf_inv' : ∀ x : PGame, 0 ⧏ inv' x
  | ⟨xl, xr, xL, xR⟩ => by
    convert lf_mk _ _ InvTy.zero
    rfl
#align pgame.zero_lf_inv' SetTheory.PGame.zero_lf_inv'

/-- `inv' 0` has exactly the same moves as `1`. -/
lemma inv'_zero : inv' 0 ≡ (1 : PGame) := by
  refine ⟨?_, ?_⟩ <;> dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal]
  · simp_rw [Unique.forall_iff, Unique.exists_iff, and_self, PGame.invVal_isEmpty]
    exact identical_zero _
  · simp

theorem inv'_zero_equiv : inv' 0 ≈ 1 :=
  inv'_zero.equiv
#align pgame.inv'_zero_equiv SetTheory.PGame.inv'_zero_equiv

/-- `inv' 1` has exactly the same moves as `1`. -/
lemma inv'_one : inv'.{u} 1 ≡ 1 := by
  have : IsEmpty {_i : PUnit.{u+1} // (0 : PGame.{u}) < 0} := by
    rw [lt_self_iff_false]
    infer_instance
  refine ⟨?_, ?_⟩ <;> dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal]
  · simp_rw [Unique.forall_iff, Unique.exists_iff, PGame.invVal_isEmpty, and_self]
    exact identical_zero _
  · simp

theorem inv'_one_equiv : inv' 1 ≈ 1 :=
  inv'_one.equiv
#align pgame.inv'_one_equiv SetTheory.PGame.inv'_one_equiv

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : Inv PGame :=
  ⟨by classical exact fun x => if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x)⟩

noncomputable instance : Div PGame :=
  ⟨fun x y => x * y⁻¹⟩

theorem inv_eq_of_equiv_zero {x : PGame} (h : x ≈ 0) : x⁻¹ = 0 := by classical exact if_pos h
#align pgame.inv_eq_of_equiv_zero SetTheory.PGame.inv_eq_of_equiv_zero

@[simp]
theorem inv_zero : (0 : PGame)⁻¹ = 0 :=
  inv_eq_of_equiv_zero (equiv_refl _)
#align pgame.inv_zero SetTheory.PGame.inv_zero

theorem inv_eq_of_pos {x : PGame} (h : 0 < x) : x⁻¹ = inv' x := by
  classical exact (if_neg h.lf.not_equiv').trans (if_pos h)
#align pgame.inv_eq_of_pos SetTheory.PGame.inv_eq_of_pos

theorem inv_eq_of_lf_zero {x : PGame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) := by
  classical exact (if_neg h.not_equiv).trans (if_neg h.not_gt)
#align pgame.inv_eq_of_lf_zero SetTheory.PGame.inv_eq_of_lf_zero

/-- `1⁻¹` has exactly the same moves as `1`. -/
lemma inv_one : 1⁻¹ ≡ 1 := by
  rw [inv_eq_of_pos PGame.zero_lt_one]
  exact inv'_one

theorem inv_one_equiv : (1⁻¹ : PGame) ≈ 1 :=
  inv_one.equiv
#align pgame.inv_one_equiv SetTheory.PGame.inv_one_equiv

end PGame

end SetTheory
