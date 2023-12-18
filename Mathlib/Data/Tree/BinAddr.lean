/-
Copyright (c) 2019 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/

import Mathlib.Data.BitVec.Lemmas
import Mathlib.SetTheory.Tree

section ShouldBeMoved

universe u v w

variable {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}

theorem congrArg_heq (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → HEq (f a₁) (f a₂) := congr_arg_heq f

theorem congrArg₂_heq (f : (a : α) → (b : β a) → γ a b) :
    ∀ {x x' y y'}, x = x' → HEq y y' → HEq (f x y) (f x' y')
  | .(_), .(_), .(_), .(_), rfl, HEq.rfl => HEq.rfl

theorem congr_arg₂_heq (f : (a : α) → (b : β a) → γ a b) :
    ∀ {x x' y y'}, x = x' → HEq y y' → HEq (f x y) (f x' y') := congrArg₂_heq f

theorem congr_heq₂ {γ : Sort w} (f : (a : α) → (b : β a) → γ) :
    ∀ {x x' y y'}, HEq x x' → HEq y y' → f x y = f x' y'
  | .(_), .(_), _, _, HEq.rfl, h => eq_of_heq (congr_arg₂_heq f rfl h)

end ShouldBeMoved

open Std (RBNode BitVec)
open Std.BitVec

/-!
# Binary address

Encodes a path from the root in a binary tree.
The intended API for the `BinAddr` is the inductive type
```
inductive BinAddr
| here  : BinAddr
| left  : BinAddr → BinAddr
| right : BinAddr → BinAddr
```
Custom eliminators are defined for `BinAddr` to enable this.
Internally it's implemented as a pair of length and a `BitVec` of that length,
so at runtime a pair of two natural numbers.
This should ensure more efficient space usage than the inductive definition,
which is essentially a linked list of `Bool`s.
Certain operations can also be defined more efficiently by using bitwise operator primitives.
-/

structure BinAddr where
  length : ℕ
  private bitvec : BitVec length
  deriving DecidableEq, Repr

namespace BinAddr

universe u

private lemma ext {p q : BinAddr}
    (h1 : p.length = q.length) (h2 : HEq p.bitvec q.bitvec) : p = q :=
  eq_of_heq $ congrArg₂_heq BinAddr.mk h1 h2

def here : BinAddr := ⟨0, BitVec.nil⟩
def left (p : BinAddr) : BinAddr := ⟨p.length + 1, p.bitvec.concat false⟩
def right (p : BinAddr) : BinAddr := ⟨p.length + 1, p.bitvec.concat true⟩

@[simp] lemma length_here : length here = 0 := rfl
@[simp] lemma length_left {p} : length (left p) = length p + 1 := rfl
@[simp] lemma length_right {p} : length (right p) = length p + 1 := rfl

section lookaheads

def isHere? (p : BinAddr) := p.length = 0
def startsWithLeft?  (p : BinAddr) := p.length > 0 ∧ p.bitvec.lsb = false
def startsWithRight? (p : BinAddr) := p.bitvec.lsb = true

instance : DecidablePred isHere? :=
  fun p => (inferInstance : Decidable (p.length = 0))

instance : DecidablePred startsWithLeft? :=
  fun p => (inferInstance : Decidable (p.length > 0 ∧ p.bitvec.lsb = false))

instance : DecidablePred startsWithRight? :=
  fun p => (inferInstance : Decidable (p.bitvec.lsb = true))

private def tail {p} (h : ¬ isHere? p) : BinAddr :=
  ⟨p.length - 1, BitVec.dropLast (p.bitvec.cast (Nat.succ_pred h).symm)⟩

private lemma succ_length_tail {p} (h : ¬ isHere? p) :
    length (p.tail h) + 1 = length p := Nat.succ_pred h

@[simp] lemma isHere?_here : isHere? here := rfl
@[simp] lemma isHere?_left {p} : ¬ isHere? (left p) :=
  Nat.succ_ne_zero _
@[simp] lemma isHere?_right {p} : ¬ isHere? (right p) :=
  Nat.succ_ne_zero _

lemma eq_here_of_isHere? {p} (h : isHere? p) : p = here :=
  ext h $ heq_of_cast_eq (congrArg _ h) $ eq_nil _

@[simp] lemma isHere?_spec (p : BinAddr) : isHere? p ↔ p = here :=
  ⟨eq_here_of_isHere?, (Eq.substr . isHere?_here)⟩

@[eliminator]
def isHere?.rec {motive : (p : BinAddr) → p.isHere? → Sort u}
    (atHere : motive here isHere?_here) {p} (h : p.isHere?) : motive p h :=
  have := congrArg₂_heq _ (eq_here_of_isHere? h) $ heq_prop h isHere?_here
  cast (eq_of_heq $ HEq.symm this) atHere

@[elab_as_elim]
def isHere?.ndrec {motive : (p : BinAddr) → Sort u} (atHere : motive here) {p} :
    p.isHere? → motive p := isHere?.rec (motive := fun {p} _ => motive p) atHere

@[simp] lemma isHere?.rec_here {motive : (p : BinAddr) → p.isHere? → Sort u}
    {atHere : motive here isHere?_here} :
    isHere?_here.rec atHere = atHere := rfl

@[simp] lemma isHere?.ndrec_here {motive : (p : BinAddr) → Sort u}
    {atHere : motive here} :
    isHere?_here.ndrec atHere = atHere := isHere?.rec_here

@[simp] lemma startsWithLeft?_here : ¬ startsWithLeft? here :=
  not_and_of_not_left _  $ not_lt.mpr $ le_of_eq length_here
@[simp] lemma startsWithLeft?_left {p} : startsWithLeft? (left p) :=
  ⟨Nat.succ_pos _, BitVec.lsb_concat _ _⟩
@[simp] lemma startsWithLeft?_right {p} : ¬ startsWithLeft? (right p) :=
  not_and_of_not_right _ $ (Bool.not_eq_false _).mpr $ BitVec.lsb_concat _ _

lemma not_isHere?_of_startsWithLeft? {p} (h : startsWithLeft? p) : ¬ isHere? p :=
  mt (isHere?.ndrec id . h) startsWithLeft?_here

def unLeft {p} (h : startsWithLeft? p) : BinAddr :=
  p.tail (not_isHere?_of_startsWithLeft? h)

lemma succ_length_unLeft {p} (h : startsWithLeft? p) :
    length (p.unLeft h) + 1 = length p :=
  succ_length_tail (not_isHere?_of_startsWithLeft? h)

@[simp] lemma left_unLeft {p} (h : startsWithLeft? p) : left (p.unLeft h) = p :=
  ext (succ_length_unLeft h) $ heq_of_eq_of_heq
    (Eq.trans
      (congrArg (concat _) $ Eq.symm $ Eq.trans (getLsb_cast _ _ _) h.right)
      (dropLast_concat_lsb _))
    (p.bitvec.cast_heq _)

@[simp] lemma unLeft_left {p} : (left p).unLeft startsWithLeft?_left = p :=
  ext (Nat.pred_succ _)
  $ heq_of_heq_of_eq (congrArg₂_heq @dropLast (Nat.pred_succ _) (BitVec.cast_heq _ _))
  $ dropLast_concat p.bitvec false

@[eliminator]
def startsWithLeft?.rec {motive : (p : BinAddr) → p.startsWithLeft? → Sort u}
    (goLeft : ∀ (p : BinAddr), motive (left p) startsWithLeft?_left) {p}
    (h : p.startsWithLeft?) : motive p h :=
  have := congrArg₂_heq _ (left_unLeft h) $ heq_prop _ h
  cast (eq_of_heq this) (goLeft (p.unLeft h))

@[elab_as_elim]
def startsWithLeft?.ndrec {motive : (p : BinAddr) → Sort u}
    (goLeft : ∀ (p : BinAddr), motive (left p)) {p} : p.startsWithLeft? → motive p :=
  startsWithLeft?.rec (motive := fun {p} _ => motive p) goLeft

@[simp]
lemma startsWithLeft?.rec_left {motive : (p : BinAddr) → p.startsWithLeft? → Sort u}
    {goLeft : ∀ (p : BinAddr), motive (left p) startsWithLeft?_left} {p} :
    startsWithLeft?_left.rec goLeft = goLeft p :=
  eq_of_heq $ HEq.trans (_root_.cast_heq _ _) (congrArg_heq goLeft unLeft_left)

@[simp]
lemma startsWithLeft?.ndrec_left {motive : (p : BinAddr) → Sort u}
    {goLeft : ∀ (p : BinAddr), motive (left p)} {p} :
    startsWithLeft?_left.ndrec goLeft = goLeft p := startsWithLeft?.rec_left

@[simp] lemma startsWithRight?_here : ¬ startsWithRight? here :=
  Bool.false_ne_true
@[simp] lemma startsWithRight?_left {p} : ¬ startsWithRight? (left p) :=
  (Bool.not_eq_true _).mpr $ BitVec.lsb_concat _ _
@[simp] lemma startsWithRight?_right {p} : startsWithRight? (right p) :=
  BitVec.lsb_concat _ _

lemma not_isHere?_of_startsWithRight? {p} (h : startsWithRight? p) : ¬ isHere? p :=
  mt (isHere?.ndrec id . h) startsWithRight?_here

def unRight {p} (h : startsWithRight? p) : BinAddr :=
  p.tail (not_isHere?_of_startsWithRight? h)

lemma succ_length_unRight {p} (h : startsWithRight? p) :
    length (p.unRight h) + 1 = length p :=
  succ_length_tail (not_isHere?_of_startsWithRight? h)

@[simp]
lemma right_unRight {p} (h : startsWithRight? p) : right (p.unRight h) = p :=
  ext (succ_length_unRight h) $ heq_of_eq_of_heq
    (Eq.trans
      (congrArg (concat _) $ Eq.symm $ Eq.trans (getLsb_cast _ _ _) h)
      (dropLast_concat_lsb _))
    (p.bitvec.cast_heq _)

@[simp]
lemma unRight_right {p} : (right p).unRight startsWithRight?_right = p :=
  ext (Nat.pred_succ _)
  $ heq_of_heq_of_eq (congrArg₂_heq @dropLast (Nat.pred_succ _) (BitVec.cast_heq _ _))
  $ dropLast_concat p.bitvec true

@[eliminator]
def startsWithRight?.rec {motive : (p : BinAddr) → p.startsWithRight? → Sort u}
    (goRight : ∀ (p : BinAddr), motive (right p) startsWithRight?_right) {p}
    (h : p.startsWithRight?) : motive p h :=
  have := congrArg₂_heq _ (right_unRight h) $ heq_prop _ h
  cast (eq_of_heq this) (goRight (p.unRight h))

@[elab_as_elim]
def startsWithRight?.ndrec {motive : (p : BinAddr) → Sort u}
    (ih : ∀ (p : BinAddr), motive (right p)) {p} : p.startsWithRight? → motive p :=
  startsWithRight?.rec (motive := fun {p} _ => motive p) ih

@[simp]
lemma startsWithRight?.rec_right {motive : (p : BinAddr) → p.startsWithRight? → Sort u}
    {goRight : ∀ (p : BinAddr), motive (right p) startsWithRight?_right} {p} :
    startsWithRight?_right.rec goRight = goRight p :=
  eq_of_heq $ HEq.trans (_root_.cast_heq _ _) (congrArg_heq goRight unRight_right)

@[simp]
lemma startsWithRight?.ndrec_right {motive : (p : BinAddr) → Sort u}
    {goRight : ∀ (p : BinAddr), motive (right p)} {p} :
    startsWithRight?_right.ndrec goRight = goRight p := startsWithRight?.rec_right

private def trichot (p : BinAddr) :
    p.isHere? ⊕' p.startsWithLeft? ⊕' p.startsWithRight? :=
  if h₁ : p.length = 0 then PSum.inl h₁ else PSum.inr $
  if h₂ : p.bitvec.lsb = true then PSum.inr h₂ else PSum.inl $
  And.intro (Nat.pos_iff_ne_zero.mpr h₁) ((Bool.not_eq_true _).mp h₂)

private lemma trichot_here : trichot here = PSum.inl isHere?_here := rfl
private lemma trichot_left {p} :
    trichot (left p) = PSum.inr (PSum.inl startsWithLeft?_left) :=
  by simp only [trichot, left, Nat.succ_ne_zero, dite_false, lsb_concat]
private lemma trichot_right {p} :
    trichot (right p) = PSum.inr (PSum.inr startsWithRight?_right) :=
  by simp only [trichot, right, Nat.succ_ne_zero, dite_false, dite_true, lsb_concat]

@[simp] lemma left_ne_here {p : BinAddr} : left p ≠ here :=
  mt (Eq.substr . isHere?_here) isHere?_left
@[simp] lemma right_ne_here {p : BinAddr} : right p ≠ here :=
  mt (Eq.substr . isHere?_here) isHere?_right
@[simp] lemma left_ne_right {p q : BinAddr} : left p ≠ right q :=
  mt (Eq.substr . startsWithRight?_right) startsWithRight?_left
@[simp] lemma here_ne_left {p : BinAddr} : here ≠ left p := Ne.symm left_ne_here
@[simp] lemma here_ne_right {p : BinAddr} : here ≠ right p := Ne.symm right_ne_here
@[simp] lemma right_ne_left {p q : BinAddr} : right p ≠ left q := Ne.symm left_ne_right

lemma eq_of_left_eq {p q} (H : left p = left q) : p = q := by
  have h := Nat.succ_injective $ congrArg length H
  refine congr_heq₂ BinAddr.mk (heq_of_eq h) ?_
  rw [← dropLast_concat p.bitvec false, ← dropLast_concat q.bitvec false]
  exact congrArg₂_heq @dropLast h (congr_arg_heq BinAddr.bitvec H)
lemma left_injective : Function.Injective BinAddr.left := @eq_of_left_eq
@[simp] lemma left_eq_iff {p q} : left p = left q ↔ p = q := left_injective.eq_iff

lemma eq_of_right_eq {p q} (H : right p = right q) : p = q := by
  have h := Nat.succ_injective $ congrArg length H
  refine congr_heq₂ BinAddr.mk (heq_of_eq h) ?_
  rw [← dropLast_concat p.bitvec true, ← dropLast_concat q.bitvec true]
  exact congrArg₂_heq @dropLast h (congr_arg_heq BinAddr.bitvec H)
lemma right_injective : Function.Injective BinAddr.right := @eq_of_right_eq
@[simp] lemma right_eq_iff {p q} : right p = right q ↔ p = q := right_injective.eq_iff

end lookaheads

section recursors

@[eliminator] def rec' {motive : BinAddr → Sort u} (atHere : motive here)
    (goLeft  : (p : BinAddr) → motive p → motive (left  p))
    (goRight : (p : BinAddr) → motive p → motive (right p)) (p : BinAddr) : motive p :=
  -- can't use "cond"/"bif" because this is `Sort u` not `Type u`
  let step {w} : (v : BitVec w) → (b : Bool) → motive ⟨w, v⟩ → motive ⟨w+1, v.concat b⟩
    | v, false => goLeft ⟨w, v⟩
    | v, true => goRight ⟨w, v⟩
  concatRecOn (motive := fun {w} v => motive ⟨w, v⟩) atHere step p.bitvec

@[simp] lemma rec'_here {motive : BinAddr → Sort u} (atHere : motive here)
    (goLeft  : (p : BinAddr) → motive p → motive (left  p))
    (goRight : (p : BinAddr) → motive p → motive (right p)) :
    BinAddr.rec' atHere goLeft goRight here = atHere := rfl

@[simp] lemma rec'_left {motive : BinAddr → Sort u} (atHere : motive here)
    (goLeft  : (p : BinAddr) → motive p → motive (left  p))
    (goRight : (p : BinAddr) → motive p → motive (right p)) (p : BinAddr) :
    BinAddr.rec' atHere goLeft goRight (left p)
    = goLeft p (BinAddr.rec' atHere goLeft goRight p) := by apply concatRecOn_concat

@[simp] lemma rec'_right {motive : BinAddr → Sort u} (atHere : motive here)
    (goLeft  : (p : BinAddr) → motive p → motive (left  p))
    (goRight : (p : BinAddr) → motive p → motive (right p)) (p : BinAddr) :
    BinAddr.rec' atHere goLeft goRight (right p)
    = goRight p (BinAddr.rec' atHere goLeft goRight p) := by apply concatRecOn_concat

@[elab_as_elim] def cases' {motive : BinAddr → Sort u} (atHere : motive here)
    (goLeft  : (p : BinAddr) → motive (left  p))
    (goRight : (p : BinAddr) → motive (right p)) (p : BinAddr) : motive p :=
  match trichot p with
  | PSum.inl           h  => h.ndrec atHere
  | PSum.inr (PSum.inl h) => h.ndrec goLeft
  | PSum.inr (PSum.inr h) => h.ndrec goRight

@[simp] lemma cases'_here {motive : BinAddr → Sort u} (atHere : motive here)
    (goLeft  : (p : BinAddr) → motive (left  p))
    (goRight : (p : BinAddr) → motive (right p)) :
    BinAddr.cases' atHere goLeft goRight here = atHere :=
  by simp only [cases', trichot_here, isHere?.ndrec_here]

@[simp] lemma cases'_left {motive : BinAddr → Sort u} (atHere : motive here)
  (goLeft  : (p : BinAddr) → motive (left  p))
  (goRight : (p : BinAddr) → motive (right p)) (p : BinAddr) :
    BinAddr.cases' atHere goLeft goRight (left p) = goLeft p :=
  by simp only [cases', trichot_left, startsWithLeft?.ndrec_left]

@[simp] lemma cases'_right {motive : BinAddr → Sort u} (atHere : motive here)
  (goLeft  : (p : BinAddr) → motive (left  p))
  (goRight : (p : BinAddr) → motive (right p)) (p : BinAddr) :
    BinAddr.cases' atHere goLeft goRight (right p) = goRight p :=
  by simp only [cases', trichot_right, startsWithRight?.ndrec_right]

variable {β : Sort u} (b : β) (l : β → β) (r : β → β)

def run : BinAddr → β := BinAddr.rec' b (fun _ => l) (fun _ => r)
@[simp] lemma run_here : here.run b l r = b := by apply BinAddr.rec'_here
@[simp] lemma run_left p : (left p).run b l r = l (p.run b l r) := by apply BinAddr.rec'_left
@[simp] lemma run_right p : (right p).run b l r = r (p.run b l r) := by apply BinAddr.rec'_right

lemma reconstruct_eq_id' : ∀ (p : BinAddr), p.run here left right = p :=
  BinAddr.rec' (BinAddr.rec'_here _ _ _)
            (fun p => Eq.trans (BinAddr.rec'_left  _ _ _ p) ∘ congrArg BinAddr.left)
            (fun p => Eq.trans (BinAddr.rec'_right _ _ _ p) ∘ congrArg BinAddr.right)

lemma reconstruct_eq_id : BinAddr.run BinAddr.here BinAddr.left BinAddr.right = id :=
  funext reconstruct_eq_id'

end recursors

section append

def append (p q : BinAddr) : BinAddr := ⟨q.length + p.length, q.bitvec ++ p.bitvec⟩
instance : Append BinAddr := ⟨append⟩

@[simp] lemma length_append {p q} : length (p ++ q) = length p + length q :=
  Nat.add_comm _ _

@[simp] lemma here_append {q} : here ++ q = q :=
  congr_heq₂ _ (heq_of_eq $ Nat.add_zero _) $ append_nil_heq _

@[simp] lemma append_here {q} : q ++ here = q :=
  congr_heq₂ _ (heq_of_eq $ Nat.zero_add _) $ nil_append_heq _

private lemma succ_length_append {p q} :
    length (p ++ q) + 1 = length q + (length p + 1) :=
  Eq.trans (congrArg (. + 1) length_append)
  $ Eq.trans (Nat.add_right_comm _ _ _) $ Nat.add_comm _ _

@[simp] lemma left_append {p q} : (left p) ++ q = left (p ++ q) :=
  have : (p ++ q).length + 1 = q.length + (left p).length :=
     Eq.trans succ_length_append (congrArg _ length_left)
  congr_heq₂ _ (heq_of_eq this.symm) $ append_concat_heq _ _ _

@[simp] lemma right_append {p q} : (right p) ++ q = right (p ++ q) :=
  have : (p ++ q).length + 1 = q.length + (right p).length :=
     Eq.trans succ_length_append (congrArg _ length_right)
  congr_heq₂ _ (heq_of_eq this.symm) $ append_concat_heq _ _ _

lemma append_assoc (p q r : BinAddr) : p ++ (q ++ r) = p ++ q ++ r :=
  have : r.length + (p ++ q).length = (q ++ r).length + p.length :=
    Eq.trans (congrArg _ length_append)
    $ Eq.trans (Nat.add_left_comm _ _ _)
    $ Eq.trans (congrArg _ (Nat.add_comm _ _))
    $ Eq.trans (congrArg _ length_append.symm)
    $ Nat.add_comm _ _
  congr_heq₂ _ (heq_of_eq this.symm) $ HEq.symm $ append_assoc_heq _ _ _

lemma append_right_inj {q r} (p : BinAddr) : p ++ q = p ++ r ↔ q = r := by
  refine ⟨?_, congrArg _⟩
  induction p with
  | atHere       => simp only [here_append,  imp_self]
  | goLeft  p ih => simp only [left_append,  left_eq_iff]; exact ih
  | goRight p ih => simp only [right_append, right_eq_iff]; exact ih

end append

section involutions

def mirror (p : BinAddr) : BinAddr := ⟨p.length, ~~~p.bitvec⟩
def reverse (p : BinAddr) : BinAddr := ⟨p.length, p.bitvec.reverse⟩

@[simp] lemma length_reverse {p} : length (reverse p) = length p := rfl
@[simp] lemma length_mirror  {p} : length (mirror p)  = length p := rfl

lemma reverse_here : reverse here = here := rfl

lemma reverse_append (p q : BinAddr) : reverse (p ++ q) = reverse q ++ reverse p :=
  congr_heq₂ BinAddr.mk (heq_of_eq $ Nat.add_comm _ _) $ reverse_append_heq _ _

lemma reverse_left (p : BinAddr) : reverse (left p) = reverse p ++ left here :=
  Eq.trans (congrArg reverse
    $ Eq.symm $ Eq.trans left_append $ congrArg left here_append)
  $ reverse_append (left here) p

lemma reverse_right (p : BinAddr) : reverse (right p) = reverse p ++ right here :=
  Eq.trans (congrArg reverse
    $ Eq.symm $ Eq.trans right_append $ congrArg right here_append)
  $ reverse_append (right here) p

lemma reverse_reverse (p : BinAddr) : reverse (reverse p) = p :=
  congrArg (BinAddr.mk _) (BitVec.reverse_reverse _)

lemma involutive_reverse : Function.Involutive reverse := reverse_reverse

lemma mirror_here : mirror here = here := rfl

lemma mirror_append (p q : BinAddr) : mirror (p ++ q) = mirror p ++ mirror q :=
  congrArg (BinAddr.mk _) (BitVec.not_append _ _)

lemma mirror_left (p : BinAddr) : mirror (left p) = right (mirror p) :=
  congrArg (BinAddr.mk _) (BitVec.not_concat _ _)

lemma mirror_right (p : BinAddr) : mirror (right p) = left (mirror p) :=
  congrArg (BinAddr.mk _) (BitVec.not_concat _ _)

lemma mirror_mirror (p : BinAddr) : mirror (mirror p) = p :=
  congrArg (BinAddr.mk _) (BitVec.not_not _)

lemma involutive_mirror : Function.Involutive mirror := mirror_mirror

end involutions

lemma append_left_inj {p q} (r : BinAddr) : p ++ r = q ++ r ↔ p = q := by
  rw [← involutive_reverse.injective.eq_iff, reverse_append, reverse_append,
      append_right_inj, involutive_reverse.injective.eq_iff]

lemma isHere?_reverse {p} : isHere? (reverse p) ↔ isHere? p :=
  by rw [isHere?_spec, involutive_reverse.eq_iff, reverse_here, isHere?_spec]

section order

instance : Preorder BinAddr where
  le := fun p q => ∃ r, q = p ++ r
  le_refl := fun _ => ⟨here, append_here.symm⟩
  le_trans := fun p q r ⟨pq, hq⟩ ⟨qr, hr⟩ =>
    suffices r = p ++ (pq ++ qr) from ⟨pq ++ qr, this⟩
    Eq.trans hr (Eq.trans (congrArg (. ++ qr) hq) (append_assoc _ _ _).symm)

lemma le_def {p q : BinAddr} : p ≤ q ↔ ∃ r, q = p ++ r := Iff.rfl

lemma le_def_unique {p q : BinAddr} : p ≤ q ↔ ∃! r, q = p ++ r :=
  Iff.trans le_def $ Iff.symm $ Iff.intro ExistsUnique.exists
  $ flip exists_unique_of_exists_of_unique $ fun y₁ y₂ =>
      Iff.mpr (@forall_eq _ (. = _ → y₁ = y₂) _) (append_right_inj p).mp q

lemma eq_of_le_of_length_eq {p q} (h1 : p ≤ q) (h2 : length p = length q) : p = q := by
  rw [le_def] at h1; obtain ⟨r, h1⟩ := h1; rw [h1] at h2 ⊢
  rw [length_append, self_eq_add_right] at h2
  rw [eq_here_of_isHere? h2, append_here]

lemma length_mono : Monotone length := fun _ _ ⟨_, h⟩ =>
  le_of_le_of_eq (Nat.le_add_right _ _) (Eq.substr h length_append.symm)

lemma length_strict_mono : StrictMono length := fun _ _ h =>
  lt_of_le_of_ne (length_mono (le_of_lt h))
  $ mt (eq_of_le_of_length_eq (le_of_lt h)) (ne_of_lt h)

private def suffixAfter' (p q : BinAddr) : BinAddr :=
  have H := Nat.size'_le.mp $ le_of_eq_of_le (Nat.size'_shiftRight _ _)
          $ Nat.sub_le_sub_right (toNat_size'_le _) _
  ⟨q.length - p.length, ofFin ⟨q.bitvec.toNat >>> p.length, H⟩⟩

lemma suffixAfter'_append (p r : BinAddr) : suffixAfter' p (p ++ r) = r := by
  have H : (suffixAfter' p (p ++ r)).length = r.length :=
      Eq.trans (congrArg (. - _) length_append) (Nat.add_sub_cancel_left _ _)
  refine ext H $ heq_of_heq_of_eq (BitVec.cast_heq H _).symm ?_
  refine eq_of_toNat_eq (Eq.trans (toNat_cast _ _) ?_)
  refine Eq.trans (congrArg (. >>> _) (toNat_append _ _)) ?_
  refine Eq.trans (Nat.lor_shiftRight _ _ _).symm ?_
  refine Eq.trans (congrArg₂ _ ?_ ?_) (Nat.zero_or _)
  . refine Eq.trans (Nat.shiftRight_sub _ (le_refl _)).symm ?_
    exact Eq.trans (congrArg _ (Nat.sub_self _)) Nat.shiftRight_zero
  . refine Eq.trans (Nat.shiftRight_eq_div_pow _ _) ?_
    exact (Nat.div_eq_zero_iff (Nat.two_pow_pos _)).mpr p.bitvec.isLt

private lemma suffixAfter'_spec (p q : BinAddr) :
    p ≤ q ↔ q = p ++ suffixAfter' p q where
  mp := fun ⟨r, h⟩ => Eq.trans h $ (append_right_inj p).mpr $ Eq.symm
                     $ Eq.trans (congrArg _ h) (suffixAfter'_append p r)
  mpr := @Exists.intro _ (q = p ++ .) _

private lemma le_def_fast (p q : BinAddr) : p ≤ q ↔ p.length ≤ q.length
    ∧ q.bitvec.toNat &&& (BitVec.allOnes p.length).toNat = p.bitvec.toNat := by
  refine Iff.trans (suffixAfter'_spec p q) ?_
  conv_lhs => rw [BinAddr.mk.injEq]; left; simp only [length_append, suffixAfter']
  rw [eq_comm, add_tsub_cancel_iff_le]
  refine and_congr_right ?_
  intro h
  have H : (p ++ suffixAfter' p q).length = q.length :=
    Eq.trans length_append (Nat.add_sub_of_le h)
  have H' := q.bitvec.cast_heq H.symm
  refine Iff.trans ⟨eq_of_heq ∘ HEq.trans H', heq_of_heq_of_eq H'.symm⟩ ?_
  refine Iff.trans (toNat_eq _ _) ?_
  refine Iff.trans (eq_iff_eq_cancel_right.mpr (toNat_cast _ _)) ?_
  constructor
  . intro H''
    refine Eq.trans (congrArg₂ _ H'' toNat_allOnes) ?_
    refine Eq.trans (Nat.and_pow_two_is_mod _ _) ?_
    refine Eq.trans (congrArg (. % _) (toNat_append' _ _)) ?_
    exact Nat.mul_add_mod_of_lt (isLt p.bitvec)
  . intro H''
    have H''' := Eq.trans H''.symm (congrArg _ toNat_allOnes)
    refine Eq.symm ?_
    refine Eq.trans (toNat_append _ _) ?_
    refine Eq.trans (congrArg₂ _ (Nat.shiftRight_shiftLeft_eq _ _) H''') ?_
    apply Nat.eq_of_testBit_eq; intro
    simp only [Nat.testBit_lor, Nat.testBit_ldiff, Nat.testBit_two_pow_sub_one,
               Nat.testBit_land, ← Bool.and_or_distrib_left, Bool.not_or_self, Bool.and_true]

instance decidableLE : DecidableRel (. ≤ . : BinAddr → BinAddr → Prop) :=
  fun p q => decidable_of_decidable_of_iff (le_def_fast p q).symm

def suffixAfter (p q : BinAddr) : Option BinAddr :=
  if p ≤ q then some (suffixAfter' p q) else none

-- the proof of `suffixAfter_isSome_iff_le` relies on the def eqs
-- `decide P ≝ if P then true else false`,
-- `Option.isSome (some _) ≝ true`, and `Option.isNone (none _) ≝ false`
-- the latter two are pretty harmless, but the first is nonobvious
lemma suffixAfter_isSome_iff_le {p q} : (suffixAfter p q).isSome ↔ p ≤ q :=
  Iff.trans (Bool.eq_iff_iff.mp (Eq.trans (apply_ite _ _ _ _) rfl))
            (decide_eq_true_iff _)

lemma mem_suffixAfter_iff_append_eq {p q r} :
    r ∈ suffixAfter p q ↔ q = p ++ r := by
  dsimp only [suffixAfter]
  split_ifs with h
  . refine Iff.trans Option.mem_some_iff (Iff.symm ?_)
    refine Iff.trans (eq_iff_eq_cancel_right.mpr ?_) (append_right_inj p)
    exact (suffixAfter'_spec p q).mp h
  . refine iff_of_false (Option.not_mem_none r) ?_
    exact mt (@Exists.intro _ (q = p ++ .) _) h

@[simp] lemma here_le {p} : here ≤ p := le_def.mpr ⟨p, here_append.symm⟩

lemma isHere?_antitone : Antitone isHere? :=
  fun _ _ h h' => Nat.le_zero.mp $ le_of_le_of_eq (length_mono h) h'

lemma startsWithLeft?_monotone : Monotone startsWithLeft? := by
  intro p q ⟨r, h⟩ h'
  refine h.substr ?_
  induction h'
  exact Eq.mpr (congrArg _ left_append) startsWithLeft?_left

lemma startsWithRight?_monotone : Monotone startsWithRight? := by
  intro p q ⟨r, h⟩ h'
  refine h.substr ?_
  induction h'
  exact Eq.mpr (congrArg _ right_append) startsWithRight?_right

@[simp]
lemma left_le_left_iff {p q} : left p ≤ left q ↔ p ≤ q := exists_congr $
  fun _ => Iff.trans (iff_of_eq (congrArg _ left_append)) left_eq_iff

@[simp]
lemma right_le_right_iff {p q} : right p ≤ right q ↔ p ≤ q := exists_congr $
  fun _ => Iff.trans (iff_of_eq (congrArg _ right_append)) right_eq_iff

@[eliminator]
def le.rec {motive : (p q : BinAddr) → p ≤ q → Sort u}
    (atHere  : {q : BinAddr} → motive here q here_le)
    (goLeft  : {p q : BinAddr} → (h : p ≤ q) → motive p q h
                            → motive _ _ (left_le_left_iff.mpr h))
    (goRight : {p q : BinAddr} → (h : p ≤ q) → motive p q h
                            → motive _ _ (right_le_right_iff.mpr h))
    {p q} (h : p ≤ q) : motive p q h := by
  induction p generalizing q with
  | atHere       => exact atHere
  | goLeft  p ih =>
    induction startsWithLeft?_monotone h startsWithLeft?_left with
    | goLeft  q => have h' := left_le_left_iff.mp h
                   exact goLeft h' (ih h')
  | goRight p ih =>
    induction startsWithRight?_monotone h startsWithRight?_right with
    | goRight q => have h' := right_le_right_iff.mp h
                   exact goRight h' (ih h')

@[elab_as_elim]
lemma le.ndrec {motive : (p q : BinAddr) → Sort u}
    (atHere  : {q : BinAddr} → motive here q)
    (goLeft  : {p q : BinAddr} → p ≤ q → motive p q → motive (left  p) (left  q))
    (goRight : {p q : BinAddr} → p ≤ q → motive p q → motive (right p) (right q))
    {p q} : p ≤ q → motive p q := le.rec atHere goLeft goRight

instance : PartialOrder BinAddr where
  le_antisymm p q h h' := by
    induction h with
    | atHere => exact Eq.symm $ eq_here_of_isHere? $ isHere?_antitone h' isHere?_here
    | goLeft  _ ih => exact left_eq_iff.mpr  $ ih $ left_le_left_iff.mp h'
    | goRight _ ih => exact right_eq_iff.mpr $ ih $ right_le_right_iff.mp h'

lemma lt_def {p q} : p < q ↔ ∃ r, ¬ isHere? r ∧ q = p ++ r :=
  Iff.trans lt_iff_le_and_ne $ Iff.trans and_comm
  $ Iff.trans exists_and_left.symm $ exists_congr
  $ fun _ => and_congr_left $ fun h =>
  Iff.not $ Iff.trans (eq_iff_eq_cancel_left.mpr h)
          $ Iff.trans (eq_iff_eq_cancel_right.mpr append_here.symm)
          $ Iff.trans (append_right_inj p)
          $ Iff.trans eq_comm (isHere?_spec _).symm

private lemma lt_def_fast (p q : BinAddr) : p < q ↔ p.length < q.length
    ∧ q.bitvec.toNat &&& (BitVec.allOnes p.length).toNat = p.bitvec.toNat :=
  Iff.trans lt_iff_le_and_ne
  $ Iff.trans (and_congr_right $ Iff.not
              ∘ Iff.intro (congrArg length) ∘ eq_of_le_of_length_eq)
  $ Iff.trans (and_congr_left' (le_def_fast _ _))
  $ Iff.trans and_right_comm $ and_congr_left' lt_iff_le_and_ne.symm

instance decidableLT : DecidableRel (. < . : BinAddr → BinAddr → Prop) :=
  fun p q => decidable_of_decidable_of_iff (lt_def_fast p q).symm

@[simp]
lemma left_lt_left_iff {p q} : left p < left q ↔ p < q :=
  suffices _ from Iff.trans lt_def (Iff.trans this lt_def.symm)
  exists_congr $ fun _ =>
    and_congr_right' $ Iff.trans (iff_of_eq (congrArg _ left_append)) left_eq_iff

@[simp]
lemma right_lt_right_iff {p q} : right p < right q ↔ p < q :=
  suffices _ from Iff.trans lt_def (Iff.trans this lt_def.symm)
  exists_congr $ fun _ =>
    and_congr_right' $ Iff.trans (iff_of_eq (congrArg _ right_append)) right_eq_iff

lemma le_total_of_common_extension :
    ∀ {p q r : BinAddr}, p ≤ r → q ≤ r → p ≤ q ∨ q ≤ p := by
  suffices {p q r} (h1 : p ≤ r) (h2 : q ≤ r) (h3 : length p ≤ length q) : p ≤ q
  . intros p q r h1 h2
    exact (Nat.le_total p.length q.length).imp (this h1 h2) (this h2 h1)
  rw [le_def_fast] at h1 h2 ⊢
  refine ⟨h3, ?_⟩
  rw [← h1.right, ← h2.right, Nat.land_assoc]
  refine congrArg _ ?_
  rw [toNat_allOnes, Nat.land_comm, Nat.and_pow_two_is_mod]
  exact Nat.mod_eq_of_lt (Nat.size'_le.mp (le_trans (toNat_size'_le _) h3))

lemma lt_trichot_of_common_extension {p q r : BinAddr} (h1 : p ≤ r) (h2 : q ≤ r) :
    p < q ∨ p = q ∨ q < p :=
  if   h : p = q
  then Or.inr (Or.inl h)
  else Or.imp (Ne.lt_of_le h) (Or.inr ∘ Ne.lt_of_le (Ne.symm h))
              (le_total_of_common_extension h1 h2)

instance : IsTree BinAddr where
  bot := here
  bot_le := @here_le
  downset_trichot _ _ _ h1 h2 :=
    lt_trichot_of_common_extension (le_of_lt h1) (le_of_lt h2)
  toWellFoundedLT :=
    ⟨WellFounded.mono (InvImage.wf length wellFounded_lt) length_strict_mono⟩

end order

section longestCommonPrefix

def longestCommonPrefix : BinAddr → BinAddr → BinAddr :=
  let rec go : BinAddr → BinAddr → BinAddr → BinAddr :=
    BinAddr.rec' (fun _ acc => acc)
              (fun _ self => BinAddr.cases' id (self . $ left .) (fun _ => id))
              (fun _ self => BinAddr.cases' id (fun _ => id) (self . $ right .))
  fun p q => reverse (go p q here)

private lemma longestCommonPrefix.go_left_left {p q acc} :
    go (left p) (left q) acc = go p q (left acc) :=
  by rw [go, rec'_left, cases'_left]

private lemma longestCommonPrefix.go_right_right {p q acc} :
    go (right p) (right q) acc = go p q (right acc) :=
  by rw [go, rec'_right, cases'_right]

private lemma longestCommonPrefix.go_eq_acc {p q acc}
    (h1 : ¬(p.startsWithLeft? ∧ q.startsWithLeft?))
    (h2 : ¬(p.startsWithRight? ∧ q.startsWithRight?)) : go p q acc = acc := by
  cases' p using BinAddr.cases' with p p <;> cases' q using BinAddr.cases' with q q
  on_goal 9 => simp only [startsWithRight?_right, and_true, not_true] at h2
  on_goal 5 => simp only [startsWithLeft?_left, and_true, not_true] at h1
  all_goals simp only [go, rec'_here, rec'_left, rec'_right,
                       cases'_here, cases'_left, cases'_right, id_eq]

private lemma longestCommonPrefix.go_eq_go_here_rev_append_acc {p q} (acc : BinAddr) :
    go p q acc = (go p q here) ++ acc := by
  induction p generalizing q acc with
  | atHere =>
    simp only [longestCommonPrefix.go_eq_acc, longestCommonPrefix.go_eq_acc,
               here_append, startsWithLeft?_here, startsWithRight?_here,
               false_and, not_false_eq_true]
  | goLeft _ ih =>
    by_cases h : q.startsWithLeft?
    . induction h
      simp only [longestCommonPrefix.go_left_left, ih (left _),
                 ← append_assoc, left_append, here_append]
    . simp only [longestCommonPrefix.go_eq_acc, longestCommonPrefix.go_eq_acc,
                 here_append, h, startsWithRight?_left, and_false,
                 false_and, not_false_eq_true]
  | goRight _ ih =>
    by_cases h : q.startsWithRight?
    . induction h
      simp only [longestCommonPrefix.go_right_right, ih (right _),
                 ← append_assoc, right_append, here_append]
    . simp only [longestCommonPrefix.go_eq_acc, longestCommonPrefix.go_eq_acc,
                 here_append, h, startsWithLeft?_right, and_false, false_and,
                 not_false_eq_true]

lemma longestCommonPrefix_left_left (p q : BinAddr) :
    longestCommonPrefix (left p) (left q) = left (longestCommonPrefix p q) := by
  dsimp only [longestCommonPrefix]
  rw [involutive_reverse.eq_iff, reverse_left, reverse_reverse,
      ← longestCommonPrefix.go_eq_go_here_rev_append_acc]
  exact longestCommonPrefix.go_left_left

lemma longestCommonPrefix_right_right (p q : BinAddr) :
    longestCommonPrefix (right p) (right q) = right (longestCommonPrefix p q) := by
  dsimp only [longestCommonPrefix]
  rw [involutive_reverse.eq_iff, reverse_right, reverse_reverse,
      ← longestCommonPrefix.go_eq_go_here_rev_append_acc]
  exact longestCommonPrefix.go_right_right

lemma longestCommonPrefix_eq_here {p q}
    (h1 : ¬(p.startsWithLeft? ∧ q.startsWithLeft?))
    (h2 : ¬(p.startsWithRight? ∧ q.startsWithRight?)) :
    longestCommonPrefix p q = here :=
  involutive_reverse.eq_iff.mpr
  $ Eq.trans (longestCommonPrefix.go_eq_acc h1 h2) $ reverse_here.symm

lemma longestCommonPrefix_comm :
    ∀ p q, longestCommonPrefix p q = longestCommonPrefix q p := by
  intro p
  induction p <;> intro q <;> cases q using BinAddr.cases'
  any_goals
    simp only [longestCommonPrefix_left_left, longestCommonPrefix_right_right,
               left_eq_iff, right_eq_iff]
    apply_assumption
  . simp only [longestCommonPrefix_eq_here, startsWithLeft?_here, startsWithRight?_here]
  all_goals
    simp only [longestCommonPrefix_eq_here, longestCommonPrefix_eq_here,
               startsWithLeft?_left, startsWithLeft?_right, startsWithLeft?_here,
               startsWithRight?_left, startsWithRight?_right, startsWithRight?_here,
               and_false, false_and, not_false_eq_true]

lemma longestCommonPrefix_le_left :
    ∀ p q, longestCommonPrefix p q ≤ p := by
  intro p; induction' p using BinAddr.rec' <;> intro q <;> cases' q using BinAddr.cases'
  any_goals
    simp only [longestCommonPrefix_left_left, longestCommonPrefix_right_right,
               left_le_left_iff, right_le_right_iff]
    apply_assumption
  all_goals
    simp only [here_le, longestCommonPrefix_eq_here, startsWithLeft?_left,
               startsWithLeft?_right, startsWithLeft?_here,
               startsWithRight?_left, startsWithRight?_right, startsWithRight?_here,
               false_and, and_false, not_false_eq_true]

lemma longestCommonPrefix_le_right (p q : BinAddr) :
    longestCommonPrefix p q ≤ q :=
  longestCommonPrefix_comm p q ▸ longestCommonPrefix_le_left q p

lemma longestCommonPrefix_is_maximum {p q r} (h1 : p ≤ q) (h2 : p ≤ r) :
    p ≤ (longestCommonPrefix q r) := by
  induction h1 generalizing r with
  | atHere => exact here_le
  | goLeft =>
    induction startsWithLeft?_monotone h2 startsWithLeft?_left
    rw [longestCommonPrefix_left_left]
    rw [left_le_left_iff] at h2 ⊢
    apply_assumption; assumption
  | goRight =>
    induction startsWithRight?_monotone h2 startsWithRight?_right
    rw [longestCommonPrefix_right_right]
    rw [right_le_right_iff] at h2 ⊢
    apply_assumption; assumption

lemma longestCommonPrefix_is_longest {p q r} (h1 : p ≤ q) (h2 : p ≤ r) :
    length p ≤ length (longestCommonPrefix q r) :=
  length_mono $ longestCommonPrefix_is_maximum h1 h2

instance : SemilatticeInf BinAddr where
  inf := longestCommonPrefix
  inf_le_left := longestCommonPrefix_le_left
  inf_le_right := longestCommonPrefix_le_right
  le_inf := @longestCommonPrefix_is_maximum

end longestCommonPrefix

end BinAddr
