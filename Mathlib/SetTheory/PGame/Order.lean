/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
import Mathlib.Logic.Small.Defs
import Mathlib.Order.GameAdd
import Mathlib.SetTheory.PGame.Basic
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "This module is now at `CombinatorialGames.Game.IGame` in the CGT repo <https://github.com/vihdzp/combinatorial-games>"
  (since := "2025-08-06")

/-!
# Order properties of pregames

Pregames have both a `≤` and a `<` relation, satisfying the usual properties of a `Preorder`. The
relation `0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won
by Left as the second player.

It turns out to be quite convenient to define various relations on top of these. We define the "less
or fuzzy" relation `x ⧏ y` as `¬ y ≤ x`, the equivalence relation `x ≈ y` as `x ≤ y ∧ y ≤ x`, and
the fuzzy relation `x ‖ y` as `x ⧏ y ∧ y ⧏ x`. If `0 ⧏ x`, then `x` can be won by Left as the
first player. If `x ≈ 0`, then `x` can be won by the second player. If `x ‖ 0`, then `x` can be won
by the first player.

Statements like `zero_le_lf`, `zero_lf_le`, etc. unfold these definitions. The theorems `le_def` and
`lf_def` give a recursive characterisation of each relation in terms of themselves two moves later.
The theorems `zero_le`, `zero_lf`, etc. also take into account that `0` has no moves.

Later, games will be defined as the quotient by the `≈` relation; that is to say, the
`Antisymmetrization` of `SetTheory.PGame`.
-/

namespace SetTheory.PGame

open Function Relation

universe u

/-- The less or equal relation on pre-games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`.
See `PGame.le_iff_sub_nonneg`. -/
instance le : LE PGame :=
  ⟨Sym2.GameAdd.fix wf_isOption fun x y le =>
      (∀ i, ¬le y (x.moveLeft i) (Sym2.GameAdd.snd_fst <| IsOption.moveLeft i)) ∧
        ∀ j, ¬le (y.moveRight j) x (Sym2.GameAdd.fst_snd <| IsOption.moveRight j)⟩

/-- The less or fuzzy relation on pre-games. `x ⧏ y` is defined as `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`.
See `PGame.lf_iff_sub_zero_lf`. -/
def LF (x y : PGame) : Prop :=
  ¬y ≤ x

@[inherit_doc]
scoped infixl:50 " ⧏ " => PGame.LF

@[simp]
protected theorem not_le {x y : PGame} : ¬x ≤ y ↔ y ⧏ x :=
  Iff.rfl

@[simp]
theorem not_lf {x y : PGame} : ¬x ⧏ y ↔ y ≤ x :=
  Classical.not_not

theorem _root_.LE.le.not_gf {x y : PGame} : x ≤ y → ¬y ⧏ x :=
  not_lf.2

theorem LF.not_ge {x y : PGame} : x ⧏ y → ¬y ≤ x :=
  id

/-- Definition of `x ≤ y` on pre-games, in terms of `⧏`.

The ordering here is chosen so that `And.left` refer to moves by Left, and `And.right` refer to
moves by Right. -/
theorem le_iff_forall_lf {x y : PGame} :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by
  unfold LE.le le
  simp only
  rw [Sym2.GameAdd.fix_eq]
  rfl

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ≤ mk yl yr yL yR ↔ (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
  le_iff_forall_lf

theorem le_of_forall_lf {x y : PGame} (h₁ : ∀ i, x.moveLeft i ⧏ y) (h₂ : ∀ j, x ⧏ y.moveRight j) :
    x ≤ y :=
  le_iff_forall_lf.2 ⟨h₁, h₂⟩

/-- Definition of `x ⧏ y` on pre-games, in terms of `≤`.

The ordering here is chosen so that `or.inl` refer to moves by Left, and `or.inr` refer to
moves by Right. -/
theorem lf_iff_exists_le {x y : PGame} :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [LF, le_iff_forall_lf, not_and_or]
  simp

/-- Definition of `x ⧏ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ⧏ mk yl yr yL yR ↔ (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
  lf_iff_exists_le

theorem le_or_gf (x y : PGame) : x ≤ y ∨ y ⧏ x := by
  rw [← PGame.not_le]
  apply em

theorem moveLeft_lf_of_le {x y : PGame} (h : x ≤ y) (i) : x.moveLeft i ⧏ y :=
  (le_iff_forall_lf.1 h).1 i

alias _root_.LE.le.moveLeft_lf := moveLeft_lf_of_le

theorem lf_moveRight_of_le {x y : PGame} (h : x ≤ y) (j) : x ⧏ y.moveRight j :=
  (le_iff_forall_lf.1 h).2 j

alias _root_.LE.le.lf_moveRight := lf_moveRight_of_le

theorem lf_of_moveRight_le {x y : PGame} {j} (h : x.moveRight j ≤ y) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨j, h⟩

theorem lf_of_le_moveLeft {x y : PGame} {i} (h : x ≤ y.moveLeft i) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨i, h⟩

theorem lf_of_le_mk {xl xr xL xR y} : mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
  moveLeft_lf_of_le

theorem lf_of_mk_le {x yl yr yL yR} : x ≤ mk yl yr yL yR → ∀ j, x ⧏ yR j :=
  lf_moveRight_of_le

theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → PGame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
  @lf_of_moveRight_le (mk _ _ _ _) y j

theorem lf_mk_of_le {x yl yr} {yL : yl → PGame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
  @lf_of_le_moveLeft x (mk _ _ _ _) i

/- We prove that `x ≤ y → y ≤ z → x ≤ z` inductively, by also simultaneously proving its cyclic
reorderings. This auxiliary lemma is used during said induction. -/
private theorem le_trans_aux {x y z : PGame}
    (h₁ : ∀ {i}, y ≤ z → z ≤ x.moveLeft i → y ≤ x.moveLeft i)
    (h₂ : ∀ {j}, z.moveRight j ≤ x → x ≤ y → z.moveRight j ≤ y) (hxy : x ≤ y) (hyz : y ≤ z) :
    x ≤ z :=
  le_of_forall_lf (fun i => PGame.not_le.1 fun h => (h₁ hyz h).not_gf <| hxy.moveLeft_lf i)
    fun j => PGame.not_le.1 fun h => (h₂ h hxy).not_gf <| hyz.lf_moveRight j

instance : Preorder PGame :=
  { PGame.le with
    le_refl := fun x => by
      induction x with | mk _ _ _ _ IHl IHr => _
      exact
        le_of_forall_lf (fun i => lf_of_le_moveLeft (IHl i)) fun i => lf_of_moveRight_le (IHr i)
    le_trans := by
      suffices
        ∀ {x y z : PGame},
          (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y) from
        fun x y z => this.1
      intro x y z
      induction x generalizing y z with | _ xl xr xL xR IHxl IHxr
      induction y generalizing   z with | _ yl yr yL yR IHyl IHyr
      induction z                  with | _ zl zr zL zR IHzl IHzr
      exact
        ⟨le_trans_aux (fun {i} => (IHxl i).2.1) fun {j} => (IHzr j).2.2,
          le_trans_aux (fun {i} => (IHyl i).2.2) fun {j} => (IHxr j).1,
          le_trans_aux (fun {i} => (IHzl i).1) fun {j} => (IHyr j).2.1⟩
    lt := fun x y => x ≤ y ∧ x ⧏ y }

lemma Identical.le : ∀ {x y}, x ≡ y → x ≤ y
  | mk _ _ _ _, mk _ _ _ _, ⟨hL, hR⟩ => le_of_forall_lf
    (fun i ↦ let ⟨_, hj⟩ := hL.1 i; lf_of_le_moveLeft hj.le)
    (fun i ↦ let ⟨_, hj⟩ := hR.2 i; lf_of_moveRight_le hj.le)

lemma Identical.ge {x y} (h : x ≡ y) : y ≤ x := h.symm.le

theorem lt_iff_le_and_lf {x y : PGame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
  Iff.rfl

theorem lt_of_le_of_lf {x y : PGame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
  ⟨h₁, h₂⟩

theorem lf_of_lt {x y : PGame} (h : x < y) : x ⧏ y :=
  h.2

alias _root_.LT.lt.lf := lf_of_lt

theorem lf_irrefl (x : PGame) : ¬x ⧏ x :=
  le_rfl.not_gf

instance : IsIrrefl _ (· ⧏ ·) :=
  ⟨lf_irrefl⟩

protected theorem not_lt {x y : PGame} : ¬ x < y ↔ y ⧏ x ∨ y ≤ x := not_lt_iff_not_le_or_ge

@[trans]
theorem lf_of_le_of_lf {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₂ ⊢
  exact fun h₃ => h₂ (h₃.trans h₁)

instance : Trans (· ≤ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_le_of_lf⟩

@[trans]
theorem lf_of_lf_of_le {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₁ ⊢
  exact fun h₃ => h₁ (h₂.trans h₃)

instance : Trans (· ⧏ ·) (· ≤ ·) (· ⧏ ·) := ⟨lf_of_lf_of_le⟩

alias _root_.LE.le.trans_lf := lf_of_le_of_lf

alias LF.trans_le := lf_of_lf_of_le

@[trans]
theorem lf_of_lt_of_lf {x y z : PGame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
  h₁.le.trans_lf h₂

@[trans]
theorem lf_of_lf_of_lt {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
  h₁.trans_le h₂.le

alias _root_.LT.lt.trans_lf := lf_of_lt_of_lf

alias LF.trans_lt := lf_of_lf_of_lt

theorem moveLeft_lf {x : PGame} : ∀ i, x.moveLeft i ⧏ x :=
  le_rfl.moveLeft_lf

theorem lf_moveRight {x : PGame} : ∀ j, x ⧏ x.moveRight j :=
  le_rfl.lf_moveRight

theorem lf_mk {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i) : xL i ⧏ mk xl xr xL xR :=
  @moveLeft_lf (mk _ _ _ _) i

theorem mk_lf {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j) : mk xl xr xL xR ⧏ xR j :=
  @lf_moveRight (mk _ _ _ _) j

/-- This special case of `PGame.le_of_forall_lf` is useful when dealing with surreals, where `<` is
preferred over `⧏`. -/
theorem le_of_forall_lt {x y : PGame} (h₁ : ∀ i, x.moveLeft i < y) (h₂ : ∀ j, x < y.moveRight j) :
    x ≤ y :=
  le_of_forall_lf (fun i => (h₁ i).lf) fun i => (h₂ i).lf

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later.

Note that it's often more convenient to use `le_iff_forall_lf`, which only unfolds the definition by
one step. -/
theorem le_def {x y : PGame} :
    x ≤ y ↔
      (∀ i, (∃ i', x.moveLeft i ≤ y.moveLeft i') ∨ ∃ j, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j, (∃ i, x ≤ (y.moveRight j).moveLeft i) ∨ ∃ j', x.moveRight j' ≤ y.moveRight j := by
  rw [le_iff_forall_lf]
  conv =>
    lhs
    simp only [lf_iff_exists_le]

/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later.

Note that it's often more convenient to use `lf_iff_exists_le`, which only unfolds the definition by
one step. -/
theorem lf_def {x y : PGame} :
    x ⧏ y ↔
      (∃ i, (∀ i', x.moveLeft i' ⧏ y.moveLeft i) ∧ ∀ j, x ⧏ (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i ⧏ y) ∧ ∀ j', x.moveRight j ⧏ y.moveRight j' := by
  rw [lf_iff_exists_le]
  conv =>
    lhs
    simp only [le_iff_forall_lf]

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem zero_le_lf {x : PGame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.moveRight j := by
  rw [le_iff_forall_lf]
  simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem le_zero_lf {x : PGame} : x ≤ 0 ↔ ∀ i, x.moveLeft i ⧏ 0 := by
  rw [le_iff_forall_lf]
  simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem zero_lf_le {x : PGame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.moveLeft i := by
  rw [lf_iff_exists_le]
  simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem lf_zero_le {x : PGame} : x ⧏ 0 ↔ ∃ j, x.moveRight j ≤ 0 := by
  rw [lf_iff_exists_le]
  simp

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : PGame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_def]
  simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : PGame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_def]
  simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ⧏` two moves later. -/
theorem zero_lf {x : PGame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.moveLeft i).moveRight j := by
  rw [lf_def]
  simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `⧏ 0` two moves later. -/
theorem lf_zero {x : PGame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.moveRight j).moveLeft i ⧏ 0 := by
  rw [lf_def]
  simp

@[simp]
theorem zero_le_of_isEmpty_rightMoves (x : PGame) [IsEmpty x.RightMoves] : 0 ≤ x :=
  zero_le.2 isEmptyElim

@[simp]
theorem le_zero_of_isEmpty_leftMoves (x : PGame) [IsEmpty x.LeftMoves] : x ≤ 0 :=
  le_zero.2 isEmptyElim

/-- Given a game won by the right player when they play second, provide a response to any move by
left. -/
noncomputable def rightResponse {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).RightMoves :=
  Classical.choose <| le_zero.1 h i

/-- Show that the response for right provided by `rightResponse` preserves the right-player-wins
condition. -/
theorem rightResponse_spec {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (rightResponse h i) ≤ 0 :=
  Classical.choose_spec <| le_zero.1 h i

/-- Given a game won by the left player when they play second, provide a response to any move by
right. -/
noncomputable def leftResponse {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    (x.moveRight j).LeftMoves :=
  Classical.choose <| zero_le.1 h j

/-- Show that the response for left provided by `leftResponse` preserves the left-player-wins
condition. -/
theorem leftResponse_spec {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (leftResponse h j) :=
  Classical.choose_spec <| zero_le.1 h j

/-- A small family of pre-games is bounded above. -/
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddAbove (Set.range f) := by
  let x : PGame.{u} := ⟨Σ i, (f <| (equivShrink.{u} ι).symm i).LeftMoves, PEmpty,
    fun x ↦ moveLeft _ x.2, PEmpty.elim⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @moveLeft_lf x ⟨equivShrink ι i, j⟩

/-- A small set of pre-games is bounded above. -/
lemma bddAbove_of_small (s : Set PGame.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → PGame.{u})

/-- A small family of pre-games is bounded below. -/
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddBelow (Set.range f) := by
  let x : PGame.{u} := ⟨PEmpty, Σ i, (f <| (equivShrink.{u} ι).symm i).RightMoves, PEmpty.elim,
    fun x ↦ moveRight _ x.2⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @lf_moveRight x ⟨equivShrink ι i, j⟩

/-- A small set of pre-games is bounded below. -/
lemma bddBelow_of_small (s : Set PGame.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → PGame.{u})

/-- The equivalence relation on pre-games. Two pre-games `x`, `y` are equivalent if `x ≤ y` and
`y ≤ x`.

If `x ≈ 0`, then the second player can always win `x`. -/
def Equiv (x y : PGame) : Prop :=
  x ≤ y ∧ y ≤ x

instance : IsEquiv _ PGame.Equiv where
  refl _ := ⟨le_rfl, le_rfl⟩
  trans := fun _ _ _ ⟨xy, yx⟩ ⟨yz, zy⟩ => ⟨xy.trans yz, zy.trans yx⟩
  symm _ _ := And.symm

instance setoid : Setoid PGame :=
  ⟨Equiv, refl, symm, Trans.trans⟩

theorem equiv_def {x y : PGame} : x ≈ y ↔ x ≤ y ∧ y ≤ x := Iff.rfl

theorem Equiv.le {x y : PGame} (h : x ≈ y) : x ≤ y :=
  h.1

theorem Equiv.ge {x y : PGame} (h : x ≈ y) : y ≤ x :=
  h.2

theorem equiv_rfl {x : PGame} : x ≈ x :=
  refl x

theorem equiv_refl (x : PGame) : x ≈ x :=
  refl x

@[symm]
protected theorem Equiv.symm {x y : PGame} : (x ≈ y) → (y ≈ x) :=
  symm

@[trans]
protected theorem Equiv.trans {x y z : PGame} : (x ≈ y) → (y ≈ z) → (x ≈ z) :=
  _root_.trans

protected theorem equiv_comm {x y : PGame} : (x ≈ y) ↔ (y ≈ x) :=
  comm

theorem equiv_of_eq {x y : PGame} (h : x = y) : x ≈ y := by subst h; rfl

lemma Identical.equiv {x y} (h : x ≡ y) : x ≈ y := ⟨h.le, h.ge⟩

@[trans]
theorem le_of_le_of_equiv {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  h₁.trans h₂.1

instance : Trans
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_le_of_equiv

@[trans]
theorem le_of_equiv_of_le {x y z : PGame} (h₁ : x ≈ y) : y ≤ z → x ≤ z :=
  h₁.1.trans

instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_equiv_of_le

theorem LF.not_equiv {x y : PGame} (h : x ⧏ y) : ¬(x ≈ y) := fun h' => h.not_ge h'.2

theorem LF.not_equiv' {x y : PGame} (h : x ⧏ y) : ¬(y ≈ x) := fun h' => h.not_ge h'.1

theorem LF.not_gt {x y : PGame} (h : x ⧏ y) : ¬y < x := fun h' => h.not_ge h'.le

theorem le_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
  hx.2.trans (h.trans hy.1)

theorem le_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
  ⟨le_congr_imp hx hy, le_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩

theorem le_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
  le_congr hx equiv_rfl

theorem le_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
  le_congr equiv_rfl hy

theorem lf_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
  PGame.not_le.symm.trans <| (not_congr (le_congr hy hx)).trans PGame.not_le

theorem lf_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
  (lf_congr hx hy).1

theorem lf_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
  lf_congr hx equiv_rfl

theorem lf_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
  lf_congr equiv_rfl hy

@[trans]
theorem lf_of_lf_of_equiv {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
  lf_congr_imp equiv_rfl h₂ h₁

instance : Trans (· ⧏ ·) (· ≈ ·) (· ⧏ ·) := ⟨lf_of_lf_of_equiv⟩

@[trans]
theorem lf_of_equiv_of_lf {x y z : PGame} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  lf_congr_imp (Equiv.symm h₁) equiv_rfl

instance : Trans (· ≈ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_equiv_of_lf⟩

@[trans]
theorem lt_of_lt_of_equiv {x y z : PGame} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1

instance : Trans
    ((· < ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_lt_of_equiv

@[trans]
theorem lt_of_equiv_of_lt {x y z : PGame} (h₁ : x ≈ y) : y < z → x < z :=
  h₁.1.trans_lt

instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_equiv_of_lt

theorem lt_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
  hx.2.trans_lt (h.trans_le hy.1)

theorem lt_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  ⟨lt_congr_imp hx hy, lt_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩

theorem lt_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
  lt_congr hx equiv_rfl

theorem lt_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
  lt_congr equiv_rfl hy

theorem lt_or_equiv_of_le {x y : PGame} (h : x ≤ y) : x < y ∨ (x ≈ y) :=
  and_or_left.mp ⟨h, (em <| y ≤ x).symm.imp_left PGame.not_le.1⟩

theorem lf_or_equiv_or_gf (x y : PGame) : x ⧏ y ∨ (x ≈ y) ∨ y ⧏ x := by
  rw [or_iff_not_imp_left]
  intro h
  rcases lt_or_equiv_of_le (PGame.not_lf.1 h) with h' | h'
  · exact Or.inr h'.lf
  · exact Or.inl (Equiv.symm h')

theorem equiv_congr_left {y₁ y₂ : PGame} : (y₁ ≈ y₂) ↔ ∀ x₁, (x₁ ≈ y₁) ↔ (x₁ ≈ y₂) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans h' h, fun h' => Equiv.trans h' (Equiv.symm h)⟩,
   fun h => (h y₁).1 <| equiv_rfl⟩

theorem equiv_congr_right {x₁ x₂ : PGame} : (x₁ ≈ x₂) ↔ ∀ y₁, (x₁ ≈ y₁) ↔ (x₂ ≈ y₁) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans (Equiv.symm h) h', fun h' => Equiv.trans h h'⟩,
   fun h => (h x₂).2 <| equiv_rfl⟩

theorem Equiv.of_exists {x y : PGame}
    (hl₁ : ∀ i, ∃ j, x.moveLeft i ≈ y.moveLeft j) (hr₁ : ∀ i, ∃ j, x.moveRight i ≈ y.moveRight j)
    (hl₂ : ∀ j, ∃ i, x.moveLeft i ≈ y.moveLeft j) (hr₂ : ∀ j, ∃ i, x.moveRight i ≈ y.moveRight j) :
    x ≈ y := by
  constructor <;> refine le_def.2 ⟨?_, ?_⟩ <;> intro i
  · obtain ⟨j, hj⟩ := hl₁ i
    exact Or.inl ⟨j, Equiv.le hj⟩
  · obtain ⟨j, hj⟩ := hr₂ i
    exact Or.inr ⟨j, Equiv.le hj⟩
  · obtain ⟨j, hj⟩ := hl₂ i
    exact Or.inl ⟨j, Equiv.ge hj⟩
  · obtain ⟨j, hj⟩ := hr₁ i
    exact Or.inr ⟨j, Equiv.ge hj⟩

theorem Equiv.of_equiv {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j, x.moveRight j ≈ y.moveRight (R j)) : x ≈ y := by
  apply Equiv.of_exists <;> intro i
  exacts [⟨_, hl i⟩, ⟨_, hr i⟩,
    ⟨_, by simpa using hl (L.symm i)⟩, ⟨_, by simpa using hr (R.symm i)⟩]

/-- The fuzzy, confused, or incomparable relation on pre-games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy (x y : PGame) : Prop :=
  x ⧏ y ∧ y ⧏ x

@[inherit_doc]
scoped infixl:50 " ‖ " => PGame.Fuzzy

@[symm]
theorem Fuzzy.swap {x y : PGame} : x ‖ y → y ‖ x :=
  And.symm

instance : IsSymm _ (· ‖ ·) :=
  ⟨fun _ _ => Fuzzy.swap⟩

theorem Fuzzy.swap_iff {x y : PGame} : x ‖ y ↔ y ‖ x :=
  ⟨Fuzzy.swap, Fuzzy.swap⟩

theorem fuzzy_irrefl (x : PGame) : ¬x ‖ x := fun h => lf_irrefl x h.1

instance : IsIrrefl _ (· ‖ ·) :=
  ⟨fuzzy_irrefl⟩

theorem lf_iff_lt_or_fuzzy {x y : PGame} : x ⧏ y ↔ x < y ∨ x ‖ y := by
  simp only [lt_iff_le_and_lf, Fuzzy, ← PGame.not_le]
  tauto

theorem lf_of_fuzzy {x y : PGame} (h : x ‖ y) : x ⧏ y :=
  lf_iff_lt_or_fuzzy.2 (Or.inr h)

alias Fuzzy.lf := lf_of_fuzzy

theorem lt_or_fuzzy_of_lf {x y : PGame} : x ⧏ y → x < y ∨ x ‖ y :=
  lf_iff_lt_or_fuzzy.1

theorem Fuzzy.not_equiv {x y : PGame} (h : x ‖ y) : ¬(x ≈ y) := fun h' => h'.1.not_gf h.2

theorem Fuzzy.not_equiv' {x y : PGame} (h : x ‖ y) : ¬(y ≈ x) := fun h' => h'.2.not_gf h.2

theorem not_fuzzy_of_le {x y : PGame} (h : x ≤ y) : ¬x ‖ y := fun h' => h'.2.not_ge h

theorem not_fuzzy_of_ge {x y : PGame} (h : y ≤ x) : ¬x ‖ y := fun h' => h'.1.not_ge h

theorem Equiv.not_fuzzy {x y : PGame} (h : x ≈ y) : ¬x ‖ y :=
  not_fuzzy_of_le h.1

theorem Equiv.not_fuzzy' {x y : PGame} (h : x ≈ y) : ¬y ‖ x :=
  not_fuzzy_of_le h.2

theorem fuzzy_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ ↔ x₂ ‖ y₂ :=
  show _ ∧ _ ↔ _ ∧ _ by rw [lf_congr hx hy, lf_congr hy hx]

theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ → x₂ ‖ y₂ :=
  (fuzzy_congr hx hy).1

theorem fuzzy_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ‖ y ↔ x₂ ‖ y :=
  fuzzy_congr hx equiv_rfl

theorem fuzzy_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ‖ y₁ ↔ x ‖ y₂ :=
  fuzzy_congr equiv_rfl hy

@[trans]
theorem fuzzy_of_fuzzy_of_equiv {x y z : PGame} (h₁ : x ‖ y) (h₂ : y ≈ z) : x ‖ z :=
  (fuzzy_congr_right h₂).1 h₁

@[trans]
theorem fuzzy_of_equiv_of_fuzzy {x y z : PGame} (h₁ : x ≈ y) (h₂ : y ‖ z) : x ‖ z :=
  (fuzzy_congr_left h₁).2 h₂

/-- Exactly one of the following is true (although we don't prove this here). -/
theorem lt_or_equiv_or_gt_or_fuzzy (x y : PGame) : x < y ∨ (x ≈ y) ∨ y < x ∨ x ‖ y := by
  rcases le_or_gf x y with h₁ | h₁ <;> rcases le_or_gf y x with h₂ | h₂
  · right
    left
    exact ⟨h₁, h₂⟩
  · left
    exact ⟨h₁, h₂⟩
  · right
    right
    left
    exact ⟨h₂, h₁⟩
  · right
    right
    right
    exact ⟨h₂, h₁⟩

theorem lt_or_equiv_or_gf (x y : PGame) : x < y ∨ (x ≈ y) ∨ y ⧏ x := by
  rw [lf_iff_lt_or_fuzzy, Fuzzy.swap_iff]
  exact lt_or_equiv_or_gt_or_fuzzy x y

/-! ### Interaction of relabelling with order -/

theorem Relabelling.le {x y : PGame} (r : x ≡r y) : x ≤ y :=
  le_def.2
    ⟨fun i => Or.inl ⟨_, (r.moveLeft i).le⟩, fun j =>
      Or.inr ⟨_, (r.moveRightSymm j).le⟩⟩
termination_by x

theorem Relabelling.ge {x y : PGame} (r : x ≡r y) : y ≤ x :=
  r.symm.le

/-- A relabelling lets us prove equivalence of games. -/
theorem Relabelling.equiv {x y : PGame} (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.ge⟩

theorem Equiv.isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≈ 0 :=
  (Relabelling.isEmpty x).equiv

instance {x y : PGame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩

/-! ### Interaction of option insertion with order -/

/-- A new left option cannot hurt Left. -/
lemma le_insertLeft (x x' : PGame) : x ≤ insertLeft x x' := by
  rw [le_def]
  constructor
  · intro i
    left
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [insertLeft, leftMoves_mk, moveLeft_mk, Sum.exists, Sum.elim_inl]
    left
    use i
  · intro j
    right
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [rightMoves_mk, moveRight_mk, insertLeft]
    use j

/-- A new right option cannot hurt Right. -/
lemma insertRight_le (x x' : PGame) : insertRight x x' ≤ x := by
  rw [le_def]
  constructor
  · intro j
    left
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [leftMoves_mk, moveLeft_mk, insertRight]
    use j
  · intro i
    right
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [insertRight, rightMoves_mk, moveRight_mk, Sum.exists, Sum.elim_inl]
    left
    use i

/-- Adding a gift horse left option does not change the value of `x`. A gift horse left option is
a game `x'` with `x' ⧏ x`. It is called "gift horse" because it seems like Left has gotten the
"gift" of a new option, but actually the value of the game did not change. -/
lemma insertLeft_equiv_of_lf {x x' : PGame} (h : x' ⧏ x) : insertLeft x x' ≈ x := by
  rw [equiv_def]
  constructor
  · rw [le_def]
    constructor
    · intro i
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertLeft, moveLeft_mk] at i ⊢
      rcases i with i | _
      · rw [Sum.elim_inl]
        left
        use i
      · rw [Sum.elim_inr]
        simpa only [lf_iff_exists_le] using h
    · intro j
      right
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertLeft, moveRight_mk]
      use j
  · apply le_insertLeft

/-- Adding a gift horse right option does not change the value of `x`. A gift horse right option is
a game `x'` with `x ⧏ x'`. It is called "gift horse" because it seems like Right has gotten the
"gift" of a new option, but actually the value of the game did not change. -/
lemma insertRight_equiv_of_lf {x x' : PGame} (h : x ⧏ x') : insertRight x x' ≈ x := by
  rw [equiv_def]
  constructor
  · apply insertRight_le
  · rw [le_def]
    constructor
    · intro j
      left
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertRight, moveLeft_mk]
      use j
    · intro i
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertRight, moveRight_mk] at i ⊢
      rcases i with i | _
      · rw [Sum.elim_inl]
        right
        use i
      · rw [Sum.elim_inr]
        simpa only [lf_iff_exists_le] using h

end SetTheory.PGame
