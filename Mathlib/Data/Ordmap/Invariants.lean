/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Ordmap.Ordnode
import Mathlib.Tactic.Abel

/-!
# Invariants for the verification of `Ordnode`

An `Ordnode`, defined in `Mathlib/Data/Ordmap/Ordnode.lean`, is an inductive type which describes a
tree which stores the `size` at internal nodes.

In this file we define the correctness invariant of an `Ordnode`, comprising:

* `Ordnode.Sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `Ordnode.Balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `Ordnode.Bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬(b ≤ a)`. We enforce this using `Ordnode.Bounded` which includes also a global
  upper and lower bound.

This whole file is in the `Ordnode` namespace, because we first have to prove the correctness of
all the operations (and defining what correctness means here is somewhat subtle).
The actual `Ordset` operations are in `Mathlib/Data/Ordmap/Ordset.lean`.

## TODO

This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `Ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming
-/


variable {α : Type*}

namespace Ordnode

/-! ### delta and ratio -/


theorem not_le_delta {s} (H : 1 ≤ s) : ¬s ≤ delta * 0 :=
  not_le_of_gt H

theorem delta_lt_false {a b : ℕ} (h₁ : delta * a < b) (h₂ : delta * b < a) : False :=
  not_le_of_gt (lt_trans (mul_lt_mul_of_pos_left h₁ <| by decide) h₂) <| by
    simpa [mul_assoc] using Nat.mul_le_mul_right a (by decide : 1 ≤ delta * delta)

/-! ### `singleton` -/


/-! ### `size` and `empty` -/


/-- O(n). Computes the actual number of elements in the set, ignoring the cached `size` field. -/
def realSize : Ordnode α → ℕ
  | nil => 0
  | node _ l _ r => realSize l + realSize r + 1

/-! ### `Sized` -/


/-- The `Sized` property asserts that all the `size` fields in nodes match the actual size of the
respective subtrees. -/
def Sized : Ordnode α → Prop
  | nil => True
  | node s l _ r => s = size l + size r + 1 ∧ Sized l ∧ Sized r

theorem Sized.node' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (node' l x r) :=
  ⟨rfl, hl, hr⟩

theorem Sized.eq_node' {s l x r} (h : @Sized α (node s l x r)) : node s l x r = .node' l x r := by
  rw [h.1]

theorem Sized.size_eq {s l x r} (H : Sized (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.1

@[elab_as_elim]
theorem Sized.induction {t} (hl : @Sized α t) {C : Ordnode α → Prop} (H0 : C nil)
    (H1 : ∀ l x r, C l → C r → C (.node' l x r)) : C t := by
  induction t with
  | nil => exact H0
  | node _ _ _ _ t_ih_l t_ih_r =>
    rw [hl.eq_node']
    exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)

theorem size_eq_realSize : ∀ {t : Ordnode α}, Sized t → size t = realSize t
  | nil, _ => rfl
  | node s l x r, ⟨h₁, h₂, h₃⟩ => by
    rw [size, h₁, size_eq_realSize h₂, size_eq_realSize h₃]; rfl

@[simp]
theorem Sized.size_eq_zero {t : Ordnode α} (ht : Sized t) : size t = 0 ↔ t = nil := by
  cases t <;> [simp;simp [ht.1]]

theorem Sized.pos {s l x r} (h : Sized (@node α s l x r)) : 0 < s := by
  rw [h.1]; apply Nat.le_add_left

/-! `dual` -/


theorem dual_dual : ∀ t : Ordnode α, dual (dual t) = t
  | nil => rfl
  | node s l x r => by rw [dual, dual, dual_dual l, dual_dual r]

@[simp]
theorem size_dual (t : Ordnode α) : size (dual t) = size t := by cases t <;> rfl

/-! `Balanced` -/


/-- The `BalancedSz l r` asserts that a hypothetical tree with children of sizes `l` and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a singleton on one side
and nothing on the other. -/
def BalancedSz (l r : ℕ) : Prop :=
  l + r ≤ 1 ∨ l ≤ delta * r ∧ r ≤ delta * l

instance BalancedSz.dec : DecidableRel BalancedSz := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The `Balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level). -/
def Balanced : Ordnode α → Prop
  | nil => True
  | node _ l _ r => BalancedSz (size l) (size r) ∧ Balanced l ∧ Balanced r

instance Balanced.dec : DecidablePred (@Balanced α)
  | nil => by
    unfold Balanced
    infer_instance
  | node _ l _ r => by
    unfold Balanced
    haveI := Balanced.dec l
    haveI := Balanced.dec r
    infer_instance

@[symm]
theorem BalancedSz.symm {l r : ℕ} : BalancedSz l r → BalancedSz r l :=
  Or.imp (by rw [add_comm]; exact id) And.symm

theorem balancedSz_zero {l : ℕ} : BalancedSz l 0 ↔ l ≤ 1 := by
  simp +contextual [BalancedSz]

theorem balancedSz_up {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ r₂ ≤ delta * l)
    (H : BalancedSz l r₁) : BalancedSz l r₂ := by
  refine or_iff_not_imp_left.2 fun h => ?_
  refine ⟨?_, h₂.resolve_left h⟩
  cases H with
  | inl H =>
    cases r₂
    · cases h (le_trans (Nat.add_le_add_left (Nat.zero_le _) _) H)
    · exact le_trans (le_trans (Nat.le_add_right _ _) H) (Nat.le_add_left 1 _)
  | inr H =>
    exact le_trans H.1 (Nat.mul_le_mul_left _ h₁)

theorem balancedSz_down {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ l ≤ delta * r₁)
    (H : BalancedSz l r₂) : BalancedSz l r₁ :=
  have : l + r₂ ≤ 1 → BalancedSz l r₁ := fun H => Or.inl (le_trans (Nat.add_le_add_left h₁ _) H)
  Or.casesOn H this fun H => Or.casesOn h₂ this fun h₂ => Or.inr ⟨h₂, le_trans h₁ H.2⟩

theorem Balanced.dual : ∀ {t : Ordnode α}, Balanced t → Balanced (dual t)
  | nil, _ => ⟨⟩
  | node _ l _ r, ⟨b, bl, br⟩ => ⟨by rw [size_dual, size_dual]; exact b.symm, br.dual, bl.dual⟩

/-! ### `rotate` and `balance` -/


/-- Build a tree from three nodes, left associated (ignores the invariants). -/
def node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' (node' l x m) y r

/-- Build a tree from three nodes, right associated (ignores the invariants). -/
def node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' l x (node' m y r)

/-- Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b) (c d))`. -/
def node4L : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3L l x nil z r

-- should not happen
/-- Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b) (c d))`. -/
def node4R : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3R l x nil z r

-- should not happen
/-- Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset. -/
def rotateL : Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ m y r => if size m < ratio * size r then node3L l x m y r else node4L l x m y r
  | l, x, nil => node' l x nil

theorem rotateL_node (l : Ordnode α) (x : α) (sz : ℕ) (m : Ordnode α) (y : α) (r : Ordnode α) :
    rotateL l x (node sz m y r) =
      if size m < ratio * size r then node3L l x m y r else node4L l x m y r :=
  rfl

theorem rotateL_nil (l : Ordnode α) (x : α) : rotateL l x nil = node' l x nil :=
  rfl

-- should not happen
/-- Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset. -/
def rotateR : Ordnode α → α → Ordnode α → Ordnode α
  | node _ l x m, y, r => if size m < ratio * size l then node3R l x m y r else node4R l x m y r
  | nil, y, r => node' nil y r

theorem rotateR_node (sz : ℕ) (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    rotateR (node sz l x m) y r =
      if size m < ratio * size l then node3R l x m y r else node4R l x m y r :=
  rfl

theorem rotateR_nil (y : α) (r : Ordnode α) : rotateR nil y r = node' nil y r :=
  rfl

-- should not happen
/-- A left balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balanceL' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else if size l > delta * size r then rotateR l x r else node' l x r

/-- A right balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balanceR' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else if size r > delta * size l then rotateL l x r else node' l x r

/-- The full balance operation. This is the same as `balance`, but with less manual inlining.
It is somewhat easier to work with this version in proofs. -/
def balance' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else
    if size r > delta * size l then rotateL l x r
    else if size l > delta * size r then rotateR l x r else node' l x r

theorem dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (node' l x r) = node' (dual r) x (dual l) := by simp [node', add_comm]

theorem dual_node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3L l x m y r) = node3R (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, add_comm]

theorem dual_node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3R l x m y r) = node3L (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, add_comm]

theorem dual_node4L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4L l x m y r) = node4R (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3R, dual_node3L, add_comm]

theorem dual_node4R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4R l x m y r) = node4L (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3L, dual_node3R, add_comm]

theorem dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateL l x r) = rotateR (dual r) x (dual l) := by
  cases r <;> simp [rotateL, rotateR]; split_ifs <;>
    simp [dual_node3L, dual_node4L, node3R]

theorem dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateR l x r) = rotateL (dual r) x (dual l) := by
  rw [← dual_dual (rotateL _ _ _), dual_rotateL, dual_dual, dual_dual]

theorem dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balance' l x r) = balance' (dual r) x (dual l) := by
  simp [balance', add_comm]; split_ifs with h h_1 h_2 <;>
    simp [dual_rotateL, dual_rotateR, add_comm]
  cases delta_lt_false h_1 h_2

theorem dual_balanceL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceL l x r) = balanceR (dual r) x (dual l) := by
  unfold balanceL balanceR
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
      dsimp only [dual, id] <;> try rfl
    split_ifs with h <;> repeat simp [add_comm]
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    dsimp only [dual, id]
    split_ifs; swap; · simp [add_comm]
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;> try rfl
    dsimp only [dual, id]
    split_ifs with h <;> simp [add_comm]

theorem dual_balanceR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceR l x r) = balanceL (dual r) x (dual l) := by
  rw [← dual_dual (balanceL _ _ _), dual_balanceL, dual_dual, dual_dual]

theorem Sized.node3L {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node3L l x m y r) :=
  (hl.node' hm).node' hr

theorem Sized.node3R {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node3R l x m y r) :=
  hl.node' (hm.node' hr)

theorem Sized.node4L {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node4L l x m y r) := by
  cases m <;> [exact (hl.node' hm).node' hr; exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

theorem node3L_size {l x m y r} : size (@node3L α l x m y r) = size l + size m + size r + 2 := by
  dsimp [node3L, node', size]; rw [add_right_comm _ 1]

theorem node3R_size {l x m y r} : size (@node3R α l x m y r) = size l + size m + size r + 2 := by
  dsimp [node3R, node', size]; rw [← add_assoc, ← add_assoc]

theorem node4L_size {l x m y r} (hm : Sized m) :
    size (@node4L α l x m y r) = size l + size m + size r + 2 := by
  cases m
  · simp [node4L, node3L, node']
    abel
  · simp [node4L, node', size, hm.1]; abel

theorem Sized.dual : ∀ {t : Ordnode α}, Sized t → Sized (dual t)
  | nil, _ => ⟨⟩
  | node _ l _ r, ⟨rfl, sl, sr⟩ => ⟨by simp [size_dual, add_comm], Sized.dual sr, Sized.dual sl⟩

theorem Sized.dual_iff {t : Ordnode α} : Sized (.dual t) ↔ Sized t :=
  ⟨fun h => by rw [← dual_dual t]; exact h.dual, Sized.dual⟩

theorem Sized.rotateL {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateL l x r) := by
  cases r; · exact hl.node' hr
  rw [Ordnode.rotateL_node]; split_ifs
  · exact hl.node3L hr.2.1 hr.2.2
  · exact hl.node4L hr.2.1 hr.2.2

theorem Sized.rotateR {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateR l x r) :=
  Sized.dual_iff.1 <| by rw [dual_rotateR]; exact hr.dual.rotateL hl.dual

theorem Sized.rotateL_size {l x r} (hm : Sized r) :
    size (@Ordnode.rotateL α l x r) = size l + size r + 1 := by
  cases r <;> simp [Ordnode.rotateL]
  simp only [hm.1]
  split_ifs <;> simp [node3L_size, node4L_size hm.2.1] <;> abel

theorem Sized.rotateR_size {l x r} (hl : Sized l) :
    size (@Ordnode.rotateR α l x r) = size l + size r + 1 := by
  rw [← size_dual, dual_rotateR, hl.dual.rotateL_size, size_dual, size_dual, add_comm (size l)]

theorem Sized.balance' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (balance' l x r) := by
  unfold Ordnode.balance'; split_ifs
  · exact hl.node' hr
  · exact hl.rotateL hr
  · exact hl.rotateR hr
  · exact hl.node' hr

theorem size_balance' {l x r} (hl : @Sized α l) (hr : Sized r) :
    size (@balance' α l x r) = size l + size r + 1 := by
  unfold balance'; split_ifs
  · rfl
  · exact hr.rotateL_size
  · exact hl.rotateR_size
  · rfl

/-! ## `All`, `Any`, `Emem`, `Amem` -/


theorem All.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, All P t → All Q t
  | nil, _ => ⟨⟩
  | node _ _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨h₁.imp H, H _ h₂, h₃.imp H⟩

theorem Any.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, Any P t → Any Q t
  | nil => id
  | node _ _ _ _ => Or.imp (Any.imp H) <| Or.imp (H _) (Any.imp H)

theorem all_singleton {P : α → Prop} {x : α} : All P (singleton x) ↔ P x :=
  ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩

theorem any_singleton {P : α → Prop} {x : α} : Any P (singleton x) ↔ P x :=
  ⟨by rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩); exact h, fun h => Or.inr (Or.inl h)⟩

theorem all_dual {P : α → Prop} : ∀ {t : Ordnode α}, All P (dual t) ↔ All P t
  | nil => Iff.rfl
  | node _ _l _x _r =>
    ⟨fun ⟨hr, hx, hl⟩ => ⟨all_dual.1 hl, hx, all_dual.1 hr⟩, fun ⟨hl, hx, hr⟩ =>
      ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩

theorem all_iff_forall {P : α → Prop} : ∀ {t}, All P t ↔ ∀ x, Emem x t → P x
  | nil => (iff_true_intro <| by rintro _ ⟨⟩).symm
  | node _ l x r => by simp [All, Emem, all_iff_forall, Any, or_imp, forall_and]

theorem any_iff_exists {P : α → Prop} : ∀ {t}, Any P t ↔ ∃ x, Emem x t ∧ P x
  | nil => ⟨by rintro ⟨⟩, by rintro ⟨_, ⟨⟩, _⟩⟩
  | node _ l x r => by simp only [Emem]; simp [Any, any_iff_exists, or_and_right, exists_or]

theorem emem_iff_all {x : α} {t} : Emem x t ↔ ∀ P, All P t → P x :=
  ⟨fun h _ al => all_iff_forall.1 al _ h, fun H => H _ <| all_iff_forall.2 fun _ => id⟩

theorem all_node' {P l x r} : @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r :=
  Iff.rfl

theorem all_node3L {P l x m y r} :
    @All α P (node3L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  simp [node3L, all_node', and_assoc]

theorem all_node3R {P l x m y r} :
    @All α P (node3R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r :=
  Iff.rfl

theorem all_node4L {P l x m y r} :
    @All α P (node4L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [node4L, all_node', All, all_node3L, and_assoc]

theorem all_node4R {P l x m y r} :
    @All α P (node4R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [node4R, all_node', All, all_node3R, and_assoc]

theorem all_rotateL {P l x r} : @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r := by
  cases r <;> simp [rotateL, all_node']; split_ifs <;>
    simp [all_node3L, all_node4L, All]

theorem all_rotateR {P l x r} : @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [← all_dual, dual_rotateR, all_rotateL]; simp [all_dual, and_comm, and_left_comm, and_assoc]

theorem all_balance' {P l x r} : @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balance']; split_ifs <;> simp [all_node', all_rotateL, all_rotateR]

/-! ### `toList` -/


theorem foldr_cons_eq_toList : ∀ (t : Ordnode α) (r : List α), t.foldr List.cons r = toList t ++ r
  | nil, _ => rfl
  | node _ l x r, r' => by
    rw [foldr, foldr_cons_eq_toList l, foldr_cons_eq_toList r, ← List.cons_append,
        ← List.append_assoc, ← foldr_cons_eq_toList l]; rfl

@[simp]
theorem toList_nil : toList (@nil α) = [] :=
  rfl

@[simp]
theorem toList_node (s l x r) : toList (@node α s l x r) = toList l ++ x :: toList r := by
  rw [toList, foldr, foldr_cons_eq_toList]; rfl

theorem emem_iff_mem_toList {x : α} {t} : Emem x t ↔ x ∈ toList t := by
  unfold Emem; induction t <;> simp [Any, *]

theorem length_toList' : ∀ t : Ordnode α, (toList t).length = t.realSize
  | nil => rfl
  | node _ l _ r => by
    rw [toList_node, List.length_append, List.length_cons, length_toList' l,
        length_toList' r]; rfl

theorem length_toList {t : Ordnode α} (h : Sized t) : (toList t).length = t.size := by
  rw [length_toList', size_eq_realSize h]

theorem equiv_iff {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂) :
    Equiv t₁ t₂ ↔ toList t₁ = toList t₂ :=
  and_iff_right_of_imp fun h => by rw [← length_toList h₁, h, length_toList h₂]

/-! ### `mem` -/


theorem pos_size_of_mem [LE α] [DecidableLE α] {x : α} {t : Ordnode α} (h : Sized t)
    (h_mem : x ∈ t) : 0 < size t := by cases t; · { contradiction }; · { simp [h.1] }

/-! ### `(find/erase/split)(Min/Max)` -/


theorem findMin'_dual : ∀ (t) (x : α), findMin' (dual t) x = findMax' x t
  | nil, _ => rfl
  | node _ _ x r, _ => findMin'_dual r x

theorem findMax'_dual (t) (x : α) : findMax' x (dual t) = findMin' t x := by
  rw [← findMin'_dual, dual_dual]

theorem findMin_dual : ∀ t : Ordnode α, findMin (dual t) = findMax t
  | nil => rfl
  | node _ _ _ _ => congr_arg some <| findMin'_dual _ _

theorem findMax_dual (t : Ordnode α) : findMax (dual t) = findMin t := by
  rw [← findMin_dual, dual_dual]

theorem dual_eraseMin : ∀ t : Ordnode α, dual (eraseMin t) = eraseMax (dual t)
  | nil => rfl
  | node _ nil _ _ => rfl
  | node _ (node sz l' y r') x r => by
    rw [eraseMin, dual_balanceR, dual_eraseMin (node sz l' y r'), dual, dual, dual, eraseMax]

theorem dual_eraseMax (t : Ordnode α) : dual (eraseMax t) = eraseMin (dual t) := by
  rw [← dual_dual (eraseMin _), dual_eraseMin, dual_dual]

theorem splitMin_eq :
    ∀ (s l) (x : α) (r), splitMin' l x r = (findMin' l x, eraseMin (node s l x r))
  | _, nil, _, _ => rfl
  | _, node ls ll lx lr, x, r => by rw [splitMin', splitMin_eq ls ll lx lr, findMin', eraseMin]

theorem splitMax_eq :
    ∀ (s l) (x : α) (r), splitMax' l x r = (eraseMax (node s l x r), findMax' x r)
  | _, _, _, nil => rfl
  | _, l, x, node ls ll lx lr => by rw [splitMax', splitMax_eq ls ll lx lr, findMax', eraseMax]

@[elab_as_elim]
theorem findMin'_all {P : α → Prop} : ∀ (t) (x : α), All P t → P x → P (findMin' t x)
  | nil, _x, _, hx => hx
  | node _ ll lx _, _, ⟨h₁, h₂, _⟩, _ => findMin'_all ll lx h₁ h₂

@[elab_as_elim]
theorem findMax'_all {P : α → Prop} : ∀ (x : α) (t), P x → All P t → P (findMax' x t)
  | _x, nil, hx, _ => hx
  | _, node _ _ lx lr, _, ⟨_, h₂, h₃⟩ => findMax'_all lx lr h₂ h₃

/-! ### `glue` -/


/-! ### `merge` -/


@[simp]
theorem merge_nil_left (t : Ordnode α) : merge t nil = t := by cases t <;> rfl

@[simp]
theorem merge_nil_right (t : Ordnode α) : merge nil t = t :=
  rfl

@[simp]
theorem merge_node {ls ll lx lr rs rl rx rr} :
    merge (@node α ls ll lx lr) (node rs rl rx rr) =
      if delta * ls < rs then balanceL (merge (node ls ll lx lr) rl) rx rr
      else if delta * rs < ls then balanceR ll lx (merge lr (node rs rl rx rr))
      else glue (node ls ll lx lr) (node rs rl rx rr) :=
  rfl

/-! ### `insert` -/


theorem dual_insert [LE α] [IsTotal α (· ≤ ·)] [DecidableLE α] (x : α) :
    ∀ t : Ordnode α, dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t)
  | nil => rfl
  | node _ l y r => by
    have : @cmpLE αᵒᵈ _ _ x y = cmpLE y x := rfl
    rw [Ordnode.insert, dual, Ordnode.insert, this, ← cmpLE_swap x y]
    cases cmpLE x y <;>
      simp [Ordering.swap, dual_balanceL, dual_balanceR, dual_insert]

/-! ### `balance` properties -/


theorem balance_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r) : @balance α l x r = balance' l x r := by
  obtain - | ⟨ls, ll, lx, lr⟩ := l
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rfl
    · rw [sr.eq_node'] at hr ⊢
      obtain - | ⟨rls, rll, rlx, rlr⟩ := rl <;> obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr <;>
        dsimp [balance, balance']
      · rfl
      · have : size rrl = 0 ∧ size rrr = 0 := by
          have := balancedSz_zero.1 hr.1.symm
          rwa [size, sr.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sr.2.2.2.1.size_eq_zero.1 this.1
        cases sr.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : rrs = 1 := sr.2.2.1
        rw [if_neg, if_pos, rotateL_node, if_pos]; · rfl
        all_goals dsimp only [size]; decide
      · have : size rll = 0 ∧ size rlr = 0 := by
          have := balancedSz_zero.1 hr.1
          rwa [size, sr.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sr.2.1.2.1.size_eq_zero.1 this.1
        cases sr.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : rls = 1 := sr.2.1.1
        rw [if_neg, if_pos, rotateL_node, if_neg]; · rfl
        all_goals dsimp only [size]; decide
      · symm; rw [zero_add, if_neg, if_pos, rotateL]
        · dsimp only [size_node]; split_ifs
          · simp [node3L, node']; abel
          · simp [node4L, node', sr.2.1.1]; abel
        · apply Nat.zero_lt_succ
        · exact not_le_of_gt (Nat.succ_lt_succ (add_pos sr.2.1.pos sr.2.2.pos))
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rw [sl.eq_node'] at hl ⊢
      obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
        dsimp [balance, balance']
      · rfl
      · have : size lrl = 0 ∧ size lrr = 0 := by
          have := balancedSz_zero.1 hl.1.symm
          rwa [size, sl.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sl.2.2.2.1.size_eq_zero.1 this.1
        cases sl.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : lrs = 1 := sl.2.2.1
        rw [if_neg, if_pos, rotateR_node, if_neg]; · rfl
        all_goals dsimp only [size]; decide
      · have : size lll = 0 ∧ size llr = 0 := by
          have := balancedSz_zero.1 hl.1
          rwa [size, sl.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sl.2.1.2.1.size_eq_zero.1 this.1
        cases sl.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : lls = 1 := sl.2.1.1
        rw [if_neg, if_pos, rotateR_node, if_pos]; · rfl
        all_goals dsimp only [size]; decide
      · symm; rw [if_neg, if_pos, rotateR]
        · dsimp only [size_node]; split_ifs
          · simp [node3R, node']; abel
          · simp [node4R, node', sl.2.2.1]; abel
        · apply Nat.zero_lt_succ
        · exact not_le_of_gt (Nat.succ_lt_succ (add_pos sl.2.1.pos sl.2.2.pos))
    · simp only [balance, id_eq, balance', size_node, gt_iff_lt]
      symm; rw [if_neg]
      · split_ifs with h h_1
        · have rd : delta ≤ size rl + size rr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sl.pos) h
            rwa [sr.1, Nat.lt_succ_iff] at this
          obtain - | ⟨rls, rll, rlx, rlr⟩ := rl
          · rw [size, zero_add] at rd
            exact absurd (le_trans rd (balancedSz_zero.1 hr.1.symm)) (by decide)
          obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr
          · exact absurd (le_trans rd (balancedSz_zero.1 hr.1)) (by decide)
          dsimp [rotateL]; split_ifs
          · simp [node3L, node', sr.1]; abel
          · simp [node4L, node', sr.1, sr.2.1.1]; abel
        · have ld : delta ≤ size ll + size lr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sr.pos) h_1
            rwa [sl.1, Nat.lt_succ_iff] at this
          obtain - | ⟨lls, lll, llx, llr⟩ := ll
          · rw [size, zero_add] at ld
            exact absurd (le_trans ld (balancedSz_zero.1 hl.1.symm)) (by decide)
          obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr
          · exact absurd (le_trans ld (balancedSz_zero.1 hl.1)) (by decide)
          dsimp [rotateR]; split_ifs
          · simp [node3R, node', sl.1]; abel
          · simp [node4R, node', sl.1, sl.2.2.1]; abel
        · simp [node']
      · exact not_le_of_gt (add_le_add (Nat.succ_le_of_lt sl.pos) (Nat.succ_le_of_lt sr.pos))

theorem balanceL_eq_balance {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 → size r ≤ 1)
    (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) :
    @balanceL α l x r = balance l x r := by
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · rfl
  · obtain - | ⟨ls, ll, lx, lr⟩ := l
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_zero.1 this.2
      rw [sr.eq_node']; rfl
    · replace H2 : ¬rs > delta * ls := not_lt_of_ge (H2 sl.pos sr.pos)
      simp [balanceL, balance, H2]; split_ifs <;> simp [add_comm]

/-- `Raised n m` means `m` is either equal or one up from `n`. -/
def Raised (n m : ℕ) : Prop :=
  m = n ∨ m = n + 1

theorem raised_iff {n m} : Raised n m ↔ n ≤ m ∧ m ≤ n + 1 := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, Nat.le_succ _⟩
    · exact ⟨Nat.le_succ _, le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with (rfl | h₁)
    · exact Or.inl rfl
    · exact Or.inr (le_antisymm h₂ h₁)

theorem Raised.dist_le {n m} (H : Raised n m) : Nat.dist n m ≤ 1 := by
  obtain ⟨H1, H2⟩ := raised_iff.1 H; rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

theorem Raised.dist_le' {n m} (H : Raised n m) : Nat.dist m n ≤ 1 := by
  rw [Nat.dist_comm]; exact H.dist_le

theorem Raised.add_left (k) {n m} (H : Raised n m) : Raised (k + n) (k + m) := by
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem Raised.add_right (k) {n m} (H : Raised n m) : Raised (n + k) (m + k) := by
  rw [add_comm, add_comm m]; exact H.add_left _

theorem Raised.right {l x₁ x₂ r₁ r₂} (H : Raised (size r₁) (size r₂)) :
    Raised (size (@node' α l x₁ r₁)) (size (@node' α l x₂ r₂)) := by
  rw [node', size_node, size_node]; generalize size r₂ = m at H ⊢
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem balanceL_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H :
      (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    @balanceL α l x r = balance' l x r := by
  rw [← balance_eq_balance' hl hr sl sr, balanceL_eq_balance sl sr]
  · intro l0; rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balancedSz_zero.1 H.symm
    exact le_trans (raised_iff.1 e).1 (balancedSz_zero.1 H.symm)
  · intro l1 _
    rcases H with (⟨l', e, H | ⟨_, H₂⟩⟩ | ⟨r', e, H | ⟨_, H₂⟩⟩)
    · exact le_trans (le_trans (Nat.le_add_left _ _) H) (mul_pos (by decide) l1 : (0 : ℕ) < _)
    · exact le_trans H₂ (Nat.mul_le_mul_left _ (raised_iff.1 e).1)
    · cases raised_iff.1 e; unfold delta; omega
    · exact le_trans (raised_iff.1 e).1 H₂

theorem balance_sz_dual {l r}
    (H : (∃ l', Raised (@size α l) l' ∧ BalancedSz l' (@size α r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    (∃ l', Raised l' (size (dual r)) ∧ BalancedSz l' (size (dual l))) ∨
      ∃ r', Raised (size (dual l)) r' ∧ BalancedSz (size (dual r)) r' := by
  rw [size_dual, size_dual]
  exact
    H.symm.imp (Exists.imp fun _ => And.imp_right BalancedSz.symm)
      (Exists.imp fun _ => And.imp_right BalancedSz.symm)

theorem size_balanceL {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    size (@balanceL α l x r) = size l + size r + 1 := by
  rw [balanceL_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balanceL {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H :
      (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    All P (@balanceL α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balanceL_eq_balance' hl hr sl sr H, all_balance']

theorem balanceR_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    @balanceR α l x r = balance' l x r := by
  rw [← dual_dual (balanceR l x r), dual_balanceR,
    balanceL_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H), ← dual_balance',
    dual_dual]

theorem size_balanceR {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    size (@balanceR α l x r) = size l + size r + 1 := by
  rw [balanceR_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balanceR {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H :
      (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    All P (@balanceR α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balanceR_eq_balance' hl hr sl sr H, all_balance']

section Bounded

variable [Preorder α]

/-- `Bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`, and also this
property holds recursively in subtrees, making the full tree a BST. The bounds can be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints. -/
def Bounded : Ordnode α → WithBot α → WithTop α → Prop
  | nil, some a, some b => a < b
  | nil, _, _ => True
  | node _ l x r, o₁, o₂ => Bounded l o₁ x ∧ Bounded r (↑x) o₂

theorem Bounded.dual :
    ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → @Bounded αᵒᵈ _ (dual t) o₂ o₁
  | nil, o₁, o₂, h => by cases o₁ <;> cases o₂ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨Or.dual, ol.dual⟩

theorem Bounded.dual_iff {t : Ordnode α} {o₁ o₂} :
    Bounded t o₁ o₂ ↔ @Bounded αᵒᵈ _ (.dual t) o₂ o₁ :=
  ⟨Bounded.dual, fun h => by
    have := Bounded.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

theorem Bounded.weak_left : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t ⊥ o₂
  | nil, o₁, o₂, h => by cases o₂ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨ol.weak_left, Or⟩

theorem Bounded.weak_right : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t o₁ ⊤
  | nil, o₁, o₂, h => by cases o₁ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨ol, Or.weak_right⟩

theorem Bounded.weak {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂) : Bounded t ⊥ ⊤ :=
  h.weak_left.weak_right

theorem Bounded.mono_left {x y : α} (xy : x ≤ y) :
    ∀ {t : Ordnode α} {o}, Bounded t y o → Bounded t x o
  | nil, none, _ => ⟨⟩
  | nil, some _, h => lt_of_le_of_lt xy h
  | node _ _ _ _, _o, ⟨ol, or⟩ => ⟨ol.mono_left xy, or⟩

theorem Bounded.mono_right {x y : α} (xy : x ≤ y) :
    ∀ {t : Ordnode α} {o}, Bounded t o x → Bounded t o y
  | nil, none, _ => ⟨⟩
  | nil, some _, h => lt_of_lt_of_le h xy
  | node _ _ _ _, _o, ⟨ol, or⟩ => ⟨ol, or.mono_right xy⟩

theorem Bounded.to_lt : ∀ {t : Ordnode α} {x y : α}, Bounded t x y → x < y
  | nil, _, _, h => h
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ => lt_trans h₁.to_lt h₂.to_lt

theorem Bounded.to_nil {t : Ordnode α} : ∀ {o₁ o₂}, Bounded t o₁ o₂ → Bounded nil o₁ o₂
  | none, _, _ => ⟨⟩
  | some _, none, _ => ⟨⟩
  | some _, some _, h => h.to_lt

theorem Bounded.trans_left {t₁ t₂ : Ordnode α} {x : α} :
    ∀ {o₁ o₂}, Bounded t₁ o₁ x → Bounded t₂ x o₂ → Bounded t₂ o₁ o₂
  | none, _, _, h₂ => h₂.weak_left
  | some _, _, h₁, h₂ => h₂.mono_left (le_of_lt h₁.to_lt)

theorem Bounded.trans_right {t₁ t₂ : Ordnode α} {x : α} :
    ∀ {o₁ o₂}, Bounded t₁ o₁ x → Bounded t₂ x o₂ → Bounded t₁ o₁ o₂
  | _, none, h₁, _ => h₁.weak_right
  | _, some _, h₁, h₂ => h₁.mono_right (le_of_lt h₂.to_lt)

theorem Bounded.mem_lt : ∀ {t o} {x : α}, Bounded t o x → All (· < x) t
  | nil, _, _, _ => ⟨⟩
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ =>
    ⟨h₁.mem_lt.imp fun _ h => lt_trans h h₂.to_lt, h₂.to_lt, h₂.mem_lt⟩

theorem Bounded.mem_gt : ∀ {t o} {x : α}, Bounded t x o → All (· > x) t
  | nil, _, _, _ => ⟨⟩
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ => ⟨h₁.mem_gt, h₁.to_lt, h₂.mem_gt.imp fun _ => lt_trans h₁.to_lt⟩

theorem Bounded.of_lt :
    ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil o₁ x → All (· < x) t → Bounded t o₁ x
  | nil, _, _, _, _, hn, _ => hn
  | node _ _ _ _, _, _, _, ⟨h₁, h₂⟩, _, ⟨_, al₂, al₃⟩ => ⟨h₁, h₂.of_lt al₂ al₃⟩

theorem Bounded.of_gt :
    ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil x o₂ → All (· > x) t → Bounded t x o₂
  | nil, _, _, _, _, hn, _ => hn
  | node _ _ _ _, _, _, _, ⟨h₁, h₂⟩, _, ⟨al₁, al₂, _⟩ => ⟨h₁.of_gt al₂ al₁, h₂⟩

theorem Bounded.to_sep {t₁ t₂ o₁ o₂} {x : α}
    (h₁ : Bounded t₁ o₁ (x : WithTop α)) (h₂ : Bounded t₂ (x : WithBot α) o₂) :
    t₁.All fun y => t₂.All fun z : α => y < z := by
  refine h₁.mem_lt.imp fun y yx => ?_
  exact h₂.mem_gt.imp fun z xz => lt_trans yx xz

end Bounded

end Ordnode
