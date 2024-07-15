/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.SetTheory.Game.Basic

/-!
# Relabelling

`PGame.Relabelling` is more of a technical detail of computable constructions in Lean than
combinatorial game theory itself. It is better to import this file only when you care about
computation.
-/

noncomputable section

namespace SetTheory

open Function PGame

universe u

namespace PGame

/-! ### Relabellings -/


/-- `Relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `Relabelling`s for the consequent games.
-/
inductive Relabelling : PGame.{u} → PGame.{u} → Type (u + 1)
  |
  mk :
    ∀ {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves),
      (∀ i, Relabelling (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j, Relabelling (x.moveRight j) (y.moveRight (R j))) → Relabelling x y
#align pgame.relabelling SetTheory.PGame.Relabelling

@[inherit_doc]
scoped infixl:50 " ≡r " => PGame.Relabelling

namespace Relabelling

variable {x y : PGame.{u}}

/-- A constructor for relabellings swapping the equivalences. -/
def mk' (L : y.LeftMoves ≃ x.LeftMoves) (R : y.RightMoves ≃ x.RightMoves)
    (hL : ∀ i, x.moveLeft (L i) ≡r y.moveLeft i) (hR : ∀ j, x.moveRight (R j) ≡r y.moveRight j) :
    x ≡r y :=
  ⟨L.symm, R.symm, fun i => by simpa using hL (L.symm i), fun j => by simpa using hR (R.symm j)⟩
#align pgame.relabelling.mk' SetTheory.PGame.Relabelling.mk'

/-- The equivalence between left moves of `x` and `y` given by the relabelling. -/
def leftMovesEquiv : x ≡r y → x.LeftMoves ≃ y.LeftMoves
  | ⟨L,_, _,_⟩ => L
#align pgame.relabelling.left_moves_equiv SetTheory.PGame.Relabelling.leftMovesEquiv

@[simp]
theorem mk_leftMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).leftMovesEquiv = L :=
  rfl
#align pgame.relabelling.mk_left_moves_equiv SetTheory.PGame.Relabelling.mk_leftMovesEquiv

@[simp]
theorem mk'_leftMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).leftMovesEquiv = L.symm :=
  rfl
#align pgame.relabelling.mk'_left_moves_equiv SetTheory.PGame.Relabelling.mk'_leftMovesEquiv

/-- The equivalence between right moves of `x` and `y` given by the relabelling. -/
def rightMovesEquiv : x ≡r y → x.RightMoves ≃ y.RightMoves
  | ⟨_, R, _, _⟩ => R
#align pgame.relabelling.right_moves_equiv SetTheory.PGame.Relabelling.rightMovesEquiv

@[simp]
theorem mk_rightMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).rightMovesEquiv = R :=
  rfl
#align pgame.relabelling.mk_right_moves_equiv SetTheory.PGame.Relabelling.mk_rightMovesEquiv

@[simp]
theorem mk'_rightMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).rightMovesEquiv = R.symm :=
  rfl
#align pgame.relabelling.mk'_right_moves_equiv SetTheory.PGame.Relabelling.mk'_rightMovesEquiv

/-- A left move of `x` is a relabelling of a left move of `y`. -/
def moveLeft : ∀ (r : x ≡r y) (i : x.LeftMoves), x.moveLeft i ≡r y.moveLeft (r.leftMovesEquiv i)
  | ⟨_, _, hL, _⟩ => hL
#align pgame.relabelling.move_left SetTheory.PGame.Relabelling.moveLeft

/-- A left move of `y` is a relabelling of a left move of `x`. -/
def moveLeftSymm :
    ∀ (r : x ≡r y) (i : y.LeftMoves), x.moveLeft (r.leftMovesEquiv.symm i) ≡r y.moveLeft i
  | ⟨L, R, hL, hR⟩, i => by simpa using hL (L.symm i)
#align pgame.relabelling.move_left_symm SetTheory.PGame.Relabelling.moveLeftSymm

/-- A right move of `x` is a relabelling of a right move of `y`. -/
def moveRight :
    ∀ (r : x ≡r y) (i : x.RightMoves), x.moveRight i ≡r y.moveRight (r.rightMovesEquiv i)
  | ⟨_, _, _, hR⟩ => hR
#align pgame.relabelling.move_right SetTheory.PGame.Relabelling.moveRight

/-- A right move of `y` is a relabelling of a right move of `x`. -/
def moveRightSymm :
    ∀ (r : x ≡r y) (i : y.RightMoves), x.moveRight (r.rightMovesEquiv.symm i) ≡r y.moveRight i
  | ⟨L, R, hL, hR⟩, i => by simpa using hR (R.symm i)
#align pgame.relabelling.move_right_symm SetTheory.PGame.Relabelling.moveRightSymm

/-- The identity relabelling. -/
@[refl]
def refl (x : PGame) : x ≡r x :=
  ⟨Equiv.refl _, Equiv.refl _, fun i => refl _, fun j => refl _⟩
termination_by x
#align pgame.relabelling.refl SetTheory.PGame.Relabelling.refl

instance (x : PGame) : Inhabited (x ≡r x) :=
  ⟨refl _⟩

/-- Flip a relabelling. -/
@[symm]
def symm : ∀ {x y : PGame}, x ≡r y → y ≡r x
  | _, _, ⟨L, R, hL, hR⟩ => mk' L R (fun i => (hL i).symm) fun j => (hR j).symm
#align pgame.relabelling.symm SetTheory.PGame.Relabelling.symm

theorem le {x y : PGame} (r : x ≡r y) : x ≤ y :=
  le_def.2
    ⟨fun i => Or.inl ⟨_, (r.moveLeft i).le⟩, fun j =>
      Or.inr ⟨_, (r.moveRightSymm j).le⟩⟩
termination_by x
#align pgame.relabelling.le SetTheory.PGame.Relabelling.le

theorem ge {x y : PGame} (r : x ≡r y) : y ≤ x :=
  r.symm.le
#align pgame.relabelling.ge SetTheory.PGame.Relabelling.ge

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.ge⟩
#align pgame.relabelling.equiv SetTheory.PGame.Relabelling.equiv

/-- Transitivity of relabelling. -/
@[trans]
def trans : ∀ {x y z : PGame}, x ≡r y → y ≡r z → x ≡r z
  | _, _, _, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ j).trans (hR₂ _)⟩
#align pgame.relabelling.trans SetTheory.PGame.Relabelling.trans

/-- Any game without left or right moves is a relabelling of 0. -/
def isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equiv.equivPEmpty _, Equiv.equivOfIsEmpty _ _, isEmptyElim, isEmptyElim⟩
#align pgame.relabelling.is_empty SetTheory.PGame.Relabelling.isEmpty

end Relabelling

instance {x y : PGame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) : PGame :=
  ⟨xl', xr', x.moveLeft ∘ el, x.moveRight ∘ er⟩
#align pgame.relabel SetTheory.PGame.relabel

@[simp]
theorem relabel_moveLeft' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : xl') : moveLeft (relabel el er) i = x.moveLeft (el i) :=
  rfl
#align pgame.relabel_move_left' SetTheory.PGame.relabel_moveLeft'

theorem relabel_moveLeft {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : x.LeftMoves) : moveLeft (relabel el er) (el.symm i) = x.moveLeft i := by simp
#align pgame.relabel_move_left SetTheory.PGame.relabel_moveLeft

@[simp]
theorem relabel_moveRight' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : xr') : moveRight (relabel el er) j = x.moveRight (er j) :=
  rfl
#align pgame.relabel_move_right' SetTheory.PGame.relabel_moveRight'

theorem relabel_moveRight {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : x.RightMoves) : moveRight (relabel el er) (er.symm j) = x.moveRight j := by simp
#align pgame.relabel_move_right SetTheory.PGame.relabel_moveRight

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabelRelabelling {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) :
    x ≡r relabel el er :=
  -- Porting note: needed to add `rfl`
  Relabelling.mk' el er (fun i => by simp; rfl) (fun j => by simp; rfl)
#align pgame.relabel_relabelling SetTheory.PGame.relabelRelabelling

/-- If `x` has the same moves as `y`, then `-x` has the same moves as `-y`. -/
def Relabelling.negCongr : ∀ {x y : PGame}, x ≡r y → -x ≡r -y
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun j => (hR j).negCongr, fun i => (hL i).negCongr⟩
#align pgame.relabelling.neg_congr SetTheory.PGame.Relabelling.negCongr

/-- `x + 0` has exactly the same moves as `x`. -/
def addZeroRelabelling : ∀ x : PGame.{u}, x + 0 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.sumEmpty xl PEmpty, Equiv.sumEmpty xr PEmpty, ?_, ?_⟩ <;> rintro (⟨i⟩ | ⟨⟨⟩⟩) <;>
      apply addZeroRelabelling
termination_by x => x
#align pgame.add_zero_relabelling SetTheory.PGame.addZeroRelabelling

/-- `0 + x` has exactly the same moves as `x`. -/
def zeroAddRelabelling : ∀ x : PGame.{u}, 0 + x ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.emptySum PEmpty xl, Equiv.emptySum PEmpty xr, ?_, ?_⟩ <;> rintro (⟨⟨⟩⟩ | ⟨i⟩) <;>
      apply zeroAddRelabelling
#align pgame.zero_add_relabelling SetTheory.PGame.zeroAddRelabelling

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def Relabelling.addCongr : ∀ {w x y z : PGame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
  | ⟨wl, wr, wL, wR⟩, ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩, ⟨L₁, R₁, hL₁, hR₁⟩,
    ⟨L₂, R₂, hL₂, hR₂⟩ => by
    let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩
    let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩
    refine ⟨Equiv.sumCongr L₁ L₂, Equiv.sumCongr R₁ R₂, ?_, ?_⟩ <;> rintro (i | j)
    · exact (hL₁ i).addCongr Hyz
    · exact Hwx.addCongr (hL₂ j)
    · exact (hR₁ i).addCongr Hyz
    · exact Hwx.addCongr (hR₂ j)
termination_by _ x _ z => (x, z)
#align pgame.relabelling.add_congr SetTheory.PGame.Relabelling.addCongr

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def Relabelling.subCongr {w x y z : PGame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr
#align pgame.relabelling.sub_congr SetTheory.PGame.Relabelling.subCongr

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def negAddRelabelling : ∀ x y : PGame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.refl _, Equiv.refl _, ?_, ?_⟩
    all_goals
      exact fun j =>
        Sum.casesOn j (fun j => negAddRelabelling _ _) fun j =>
          negAddRelabelling ⟨xl, xr, xL, xR⟩ _
termination_by x y => (x, y)
#align pgame.neg_add_relabelling SetTheory.PGame.negAddRelabelling

/-- `x + y` has exactly the same moves as `y + x`. -/
def addCommRelabelling : ∀ x y : PGame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;> rintro (_ | _) <;>
      · dsimp
        apply addCommRelabelling
termination_by x y => (x, y)
#align pgame.add_comm_relabelling SetTheory.PGame.addCommRelabelling

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def addAssocRelabelling : ∀ x y z : PGame.{u}, x + y + z ≡r x + (y + z)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩ => by
    refine ⟨Equiv.sumAssoc _ _ _, Equiv.sumAssoc _ _ _, ?_, ?_⟩
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yL i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zL i)
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yR i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zR i)
termination_by x y z => (x, y, z)
#align pgame.add_assoc_relabelling SetTheory.PGame.addAssocRelabelling

/-- `x * y` and `y * x` have the same moves. -/
def mulCommRelabelling (x y : PGame.{u}) : x * y ≡r y * x :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _),
      (Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)), ?_, ?_⟩
      <;>
    rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
    { dsimp
      exact ((addCommRelabelling _ _).trans <|
        (mulCommRelabelling _ _).addCongr (mulCommRelabelling _ _)).subCongr
        (mulCommRelabelling _ _) }
  termination_by (x, y)
#align pgame.mul_comm_relabelling SetTheory.PGame.mulCommRelabelling

/-- `x * 0` has exactly the same moves as `0`. -/
def mulZeroRelabelling (x : PGame) : x * 0 ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.mul_zero_relabelling SetTheory.PGame.mulZeroRelabelling

/-- `0 * x` has exactly the same moves as `0`. -/
def zeroMulRelabelling (x : PGame) : 0 * x ≡r 0 :=
  Relabelling.isEmpty _
#align pgame.zero_mul_relabelling SetTheory.PGame.zeroMulRelabelling


/-- `-x * y` and `-(x * y)` have the same moves. -/
def negMulRelabelling (x y : PGame.{u}) : -x * y ≡r -(x * y) :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
      refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;>
      rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
      · dsimp
        apply ((negAddRelabelling _ _).trans _).symm
        apply ((negAddRelabelling _ _).trans (Relabelling.addCongr _ _)).subCongr
        -- Porting note: we used to just do `<;> exact (negMulRelabelling _ _).symm` from here.
        · exact (negMulRelabelling _ _).symm
        · exact (negMulRelabelling _ _).symm
        -- Porting note: not sure what has gone wrong here.
        -- The goal is hideous here, and the `exact` doesn't work,
        -- but if we just `change` it to look like the mathlib3 goal then we're fine!?
        change -(mk xl xr xL xR * _) ≡r _
        exact (negMulRelabelling _ _).symm
  termination_by (x, y)
#align pgame.neg_mul_relabelling SetTheory.PGame.negMulRelabelling

/-- `x * -y` and `-(x * y)` have the same moves. -/
def mulNegRelabelling (x y : PGame) : x * -y ≡r -(x * y) :=
  (mulCommRelabelling x _).trans <| (negMulRelabelling _ x).trans (mulCommRelabelling y x).negCongr
#align pgame.mul_neg_relabelling SetTheory.PGame.mulNegRelabelling

/-- `x * 1` has the same moves as `x`. -/
def mulOneRelabelling : ∀ x : PGame.{u}, x * 1 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    -- Porting note: the next four lines were just `unfold has_one.one,`
    show _ * One.one ≡r _
    unfold One.one
    unfold instOnePGame
    change mk _ _ _ _ * mk _ _ _ _ ≡r _
    refine ⟨(Equiv.sumEmpty _ _).trans (Equiv.prodPUnit _),
      (Equiv.emptySum _ _).trans (Equiv.prodPUnit _), ?_, ?_⟩ <;>
    (try rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩)) <;>
    { dsimp
      apply (Relabelling.subCongr (Relabelling.refl _) (mulZeroRelabelling _)).trans
      rw [sub_zero_eq_add_zero]
      exact (addZeroRelabelling _).trans <|
        (((mulOneRelabelling _).addCongr (mulZeroRelabelling _)).trans <| addZeroRelabelling _) }
#align pgame.mul_one_relabelling SetTheory.PGame.mulOneRelabelling

/-- `1 * x` has the same moves as `x`. -/
def oneMulRelabelling (x : PGame) : 1 * x ≡r x :=
  (mulCommRelabelling 1 x).trans <| mulOneRelabelling x
#align pgame.one_mul_relabelling SetTheory.PGame.oneMulRelabelling

/-- `inv' 0` has exactly the same moves as `1`. -/
def inv'Zero : inv' 0 ≡r 1 := by
  change mk _ _ _ _ ≡r 1
  refine ⟨?_, ?_, fun i => ?_, IsEmpty.elim ?_⟩
  · apply Equiv.equivPUnit (InvTy _ _ _)
  · apply Equiv.equivPEmpty (InvTy _ _ _)
  · -- Porting note: had to add `rfl`, because `simp` only uses the built-in `rfl`.
    simp; rfl
  · dsimp
    infer_instance
#align pgame.inv'_zero SetTheory.PGame.inv'Zero

/-- `inv' 1` has exactly the same moves as `1`. -/
def inv'One : inv' 1 ≡r (1 : PGame.{u}) := by
  change Relabelling (mk _ _ _ _) 1
  have : IsEmpty { _i : PUnit.{u + 1} // (0 : PGame.{u}) < 0 } := by
    rw [lt_self_iff_false]
    infer_instance
  refine ⟨?_, ?_, fun i => ?_, IsEmpty.elim ?_⟩ <;> dsimp
  · apply Equiv.equivPUnit
  · apply Equiv.equivOfIsEmpty
  · -- Porting note: had to add `rfl`, because `simp` only uses the built-in `rfl`.
    simp; rfl
  · infer_instance
#align pgame.inv'_one SetTheory.PGame.inv'One

/-- `1⁻¹` has exactly the same moves as `1`. -/
def invOne : 1⁻¹ ≡r 1 := by
  rw [inv_eq_of_pos PGame.zero_lt_one]
  exact inv'One
#align pgame.inv_one SetTheory.PGame.invOne

end PGame

end SetTheory

end
