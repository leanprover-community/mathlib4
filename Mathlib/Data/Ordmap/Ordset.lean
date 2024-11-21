/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Group.Int
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Ordmap.Ordnode
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Verification of the `Ordnode α` datatype

This file proves the correctness of the operations in `Data.Ordmap.Ordnode`.
The public facing version is the type `Ordset α`, which is a wrapper around
`Ordnode α` which includes the correctness invariant of the type, and it exposes
parallel operations like `insert` as functions on `Ordset` that do the same
thing but bundle the correctness proofs. The advantage is that it is possible
to, for example, prove that the result of `find` on `insert` will actually find
the element, while `Ordnode` cannot guarantee this if the input tree did not
satisfy the type invariants.

## Main definitions

* `Ordset α`: A well formed set of values of type `α`

## Implementation notes

The majority of this file is actually in the `Ordnode` namespace, because we first
have to prove the correctness of all the operations (and defining what correctness
means here is actually somewhat subtle). So all the actual `Ordset` operations are
at the very end, once we have all the theorems.

An `Ordnode α` is an inductive type which describes a tree which stores the `size` at
internal nodes. The correctness invariant of an `Ordnode α` is:

* `Ordnode.Sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `Ordnode.Balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `Ordnode.Bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬ (b ≤ a)`. We enforce this using `Ordnode.Bounded` which includes also a global
  upper and lower bound.

Because the `Ordnode` file was ported from Haskell, the correctness invariants of some
of the functions have not been spelled out, and some theorems like
`Ordnode.Valid'.balanceL_aux` show very intricate assumptions on the sizes,
which may need to be revised if it turns out some operations violate these assumptions,
because there is a decent amount of slop in the actual data structure invariants, so the
theorem will go through with multiple choices of assumption.

**Note:** This file is incomplete, in the sense that the intent is to have verified
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
  not_le_of_lt (lt_trans ((mul_lt_mul_left (by decide)).2 h₁) h₂) <| by
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

-- Porting note (https://github.com/leanprover-community/mathlib4/pull/11467): during the port we marked these lemmas with `@[eqns]`
-- to emulate the old Lean 3 behaviour.

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

-- Porting note (https://github.com/leanprover-community/mathlib4/pull/11467): during the port we marked these lemmas with `@[eqns]`
-- to emulate the old Lean 3 behaviour.

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
  simp [node3L, node3R, dual_node', add_comm]

theorem dual_node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3R l x m y r) = node3L (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, dual_node', add_comm]

theorem dual_node4L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4L l x m y r) = node4R (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3R, dual_node3L, dual_node', add_comm]

theorem dual_node4R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4R l x m y r) = node4L (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3L, dual_node3R, dual_node', add_comm]

theorem dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateL l x r) = rotateR (dual r) x (dual l) := by
  cases r <;> simp [rotateL, rotateR, dual_node']; split_ifs <;>
    simp [dual_node3L, dual_node4L, node3R, add_comm]

theorem dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateR l x r) = rotateL (dual r) x (dual l) := by
  rw [← dual_dual (rotateL _ _ _), dual_rotateL, dual_dual, dual_dual]

theorem dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balance' l x r) = balance' (dual r) x (dual l) := by
  simp [balance', add_comm]; split_ifs with h h_1 h_2 <;>
    simp [dual_node', dual_rotateL, dual_rotateR, add_comm]
  cases delta_lt_false h_1 h_2

theorem dual_balanceL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceL l x r) = balanceR (dual r) x (dual l) := by
  unfold balanceL balanceR
  cases' r with rs rl rx rr
  · cases' l with ls ll lx lr; · rfl
    cases' ll with lls lll llx llr <;> cases' lr with lrs lrl lrx lrr <;> dsimp only [dual, id] <;>
      try rfl
    split_ifs with h <;> repeat simp [h, add_comm]
  · cases' l with ls ll lx lr; · rfl
    dsimp only [dual, id]
    split_ifs; swap; · simp [add_comm]
    cases' ll with lls lll llx llr <;> cases' lr with lrs lrl lrx lrr <;> try rfl
    dsimp only [dual, id]
    split_ifs with h <;> simp [h, add_comm]

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
  cases m <;> simp [node4L, node3L, node'] <;> [abel; (simp [size, hm.1]; abel)]

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
    simp [all_node3L, all_node4L, All, and_assoc]

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
  unfold Emem; induction t <;> simp [Any, *, or_assoc]

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


theorem pos_size_of_mem [LE α] [@DecidableRel α (· ≤ ·)] {x : α} {t : Ordnode α} (h : Sized t)
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


theorem dual_insert [Preorder α] [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) :
    ∀ t : Ordnode α, dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t)
  | nil => rfl
  | node _ l y r => by
    have : @cmpLE αᵒᵈ _ _ x y = cmpLE y x := rfl
    rw [Ordnode.insert, dual, Ordnode.insert, this, ← cmpLE_swap x y]
    cases cmpLE x y <;>
      simp [Ordering.swap, Ordnode.insert, dual_balanceL, dual_balanceR, dual_insert]

/-! ### `balance` properties -/


theorem balance_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r) : @balance α l x r = balance' l x r := by
  cases' l with ls ll lx lr
  · cases' r with rs rl rx rr
    · rfl
    · rw [sr.eq_node'] at hr ⊢
      cases' rl with rls rll rlx rlr <;> cases' rr with rrs rrl rrx rrr <;>
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
  · cases' r with rs rl rx rr
    · rw [sl.eq_node'] at hl ⊢
      cases' ll with lls lll llx llr <;> cases' lr with lrs lrl lrx lrr <;>
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
    · simp [balance, balance']
      symm; rw [if_neg]
      · split_ifs with h h_1
        · have rd : delta ≤ size rl + size rr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sl.pos) h
            rwa [sr.1, Nat.lt_succ_iff] at this
          cases' rl with rls rll rlx rlr
          · rw [size, zero_add] at rd
            exact absurd (le_trans rd (balancedSz_zero.1 hr.1.symm)) (by decide)
          cases' rr with rrs rrl rrx rrr
          · exact absurd (le_trans rd (balancedSz_zero.1 hr.1)) (by decide)
          dsimp [rotateL]; split_ifs
          · simp [node3L, node', sr.1]; abel
          · simp [node4L, node', sr.1, sr.2.1.1]; abel
        · have ld : delta ≤ size ll + size lr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sr.pos) h_1
            rwa [sl.1, Nat.lt_succ_iff] at this
          cases' ll with lls lll llx llr
          · rw [size, zero_add] at ld
            exact absurd (le_trans ld (balancedSz_zero.1 hl.1.symm)) (by decide)
          cases' lr with lrs lrl lrx lrr
          · exact absurd (le_trans ld (balancedSz_zero.1 hl.1)) (by decide)
          dsimp [rotateR]; split_ifs
          · simp [node3R, node', sl.1]; abel
          · simp [node4R, node', sl.1, sl.2.2.1]; abel
        · simp [node']
      · exact not_le_of_gt (add_le_add (Nat.succ_le_of_lt sl.pos) (Nat.succ_le_of_lt sr.pos))

theorem balanceL_eq_balance {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 → size r ≤ 1)
    (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) :
    @balanceL α l x r = balance l x r := by
  cases' r with rs rl rx rr
  · rfl
  · cases' l with ls ll lx lr
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_zero.1 this.2
      rw [sr.eq_node']; rfl
    · replace H2 : ¬rs > delta * ls := not_lt_of_le (H2 sl.pos sr.pos)
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
  cases' raised_iff.1 H with H1 H2; rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

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

/-! ### `bounded` -/


section

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

end

/-! ### `Valid` -/


section

variable [Preorder α]

/-- The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. This version of `Valid` also puts all elements in the tree in the interval `(lo, hi)`. -/
structure Valid' (lo : WithBot α) (t : Ordnode α) (hi : WithTop α) : Prop where
  ord : t.Bounded lo hi
  sz : t.Sized
  bal : t.Balanced

/-- The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. -/
def Valid (t : Ordnode α) : Prop :=
  Valid' ⊥ t ⊤

theorem Valid'.mono_left {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : Valid' y t o) :
    Valid' x t o :=
  ⟨h.1.mono_left xy, h.2, h.3⟩

theorem Valid'.mono_right {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : Valid' o t x) :
    Valid' o t y :=
  ⟨h.1.mono_right xy, h.2, h.3⟩

theorem Valid'.trans_left {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ x)
    (H : Valid' x t₂ o₂) : Valid' o₁ t₂ o₂ :=
  ⟨h.trans_left H.1, H.2, H.3⟩

theorem Valid'.trans_right {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t₁ x)
    (h : Bounded t₂ x o₂) : Valid' o₁ t₁ o₂ :=
  ⟨H.1.trans_right h, H.2, H.3⟩

theorem Valid'.of_lt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil o₁ x)
    (h₂ : All (· < x) t) : Valid' o₁ t x :=
  ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩

theorem Valid'.of_gt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil x o₂)
    (h₂ : All (· > x) t) : Valid' x t o₂ :=
  ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩

theorem Valid'.valid {t o₁ o₂} (h : @Valid' α _ o₁ t o₂) : Valid t :=
  ⟨h.1.weak, h.2, h.3⟩

theorem valid'_nil {o₁ o₂} (h : Bounded nil o₁ o₂) : Valid' o₁ (@nil α) o₂ :=
  ⟨h, ⟨⟩, ⟨⟩⟩

theorem valid_nil : Valid (@nil α) :=
  valid'_nil ⟨⟩

theorem Valid'.node {s l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : BalancedSz (size l) (size r)) (hs : s = size l + size r + 1) :
    Valid' o₁ (@node α s l x r) o₂ :=
  ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

theorem Valid'.dual : ∀ {t : Ordnode α} {o₁ o₂}, Valid' o₁ t o₂ → @Valid' αᵒᵈ _ o₂ (dual t) o₁
  | .nil, _, _, h => valid'_nil h.1.dual
  | .node _ l _ r, _, _, ⟨⟨ol, Or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ =>
    let ⟨ol', sl', bl'⟩ := Valid'.dual ⟨ol, sl, bl⟩
    let ⟨or', sr', br'⟩ := Valid'.dual ⟨Or, sr, br⟩
    ⟨⟨or', ol'⟩, ⟨by simp [size_dual, add_comm], sr', sl'⟩,
      ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩

theorem Valid'.dual_iff {t : Ordnode α} {o₁ o₂} : Valid' o₁ t o₂ ↔ @Valid' αᵒᵈ _ o₂ (.dual t) o₁ :=
  ⟨Valid'.dual, fun h => by
    have := Valid'.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

theorem Valid.dual {t : Ordnode α} : Valid t → @Valid αᵒᵈ _ (.dual t) :=
  Valid'.dual

theorem Valid.dual_iff {t : Ordnode α} : Valid t ↔ @Valid αᵒᵈ _ (.dual t) :=
  Valid'.dual_iff

theorem Valid'.left {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂) : Valid' o₁ l x :=
  ⟨H.1.1, H.2.2.1, H.3.2.1⟩

theorem Valid'.right {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂) : Valid' x r o₂ :=
  ⟨H.1.2, H.2.2.2, H.3.2.2⟩

nonrec theorem Valid.left {s l x r} (H : Valid (@node α s l x r)) : Valid l :=
  H.left.valid

nonrec theorem Valid.right {s l x r} (H : Valid (@node α s l x r)) : Valid r :=
  H.right.valid

theorem Valid.size_eq {s l x r} (H : Valid (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.2.1

theorem Valid'.node' {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : BalancedSz (size l) (size r)) : Valid' o₁ (@node' α l x r) o₂ :=
  hl.node hr H rfl

theorem valid'_singleton {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ x) (h₂ : Bounded nil x o₂) :
    Valid' o₁ (singleton x : Ordnode α) o₂ :=
  (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl

theorem valid_singleton {x : α} : Valid (singleton x : Ordnode α) :=
  valid'_singleton ⟨⟩ ⟨⟩

theorem Valid'.node3L {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' y r o₂) (H1 : BalancedSz (size l) (size m))
    (H2 : BalancedSz (size l + size m + 1) (size r)) : Valid' o₁ (@node3L α l x m y r) o₂ :=
  (hl.node' hm H1).node' hr H2

theorem Valid'.node3R {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' y r o₂) (H1 : BalancedSz (size l) (size m + size r + 1))
    (H2 : BalancedSz (size m) (size r)) : Valid' o₁ (@node3R α l x m y r) o₂ :=
  hl.node' (hm.node' hr H2) H1

theorem Valid'.node4L_lemma₁ {a b c d : ℕ} (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9)
    (mr₂ : b + c + 1 ≤ 3 * d) (mm₁ : b ≤ 3 * c) : b < 3 * a + 1 := by omega

theorem Valid'.node4L_lemma₂ {b c d : ℕ} (mr₂ : b + c + 1 ≤ 3 * d) : c ≤ 3 * d := by omega

theorem Valid'.node4L_lemma₃ {b c d : ℕ} (mr₁ : 2 * d ≤ b + c + 1) (mm₁ : b ≤ 3 * c) :
    d ≤ 3 * c := by omega

theorem Valid'.node4L_lemma₄ {a b c d : ℕ} (lr₁ : 3 * a ≤ b + c + 1 + d) (mr₂ : b + c + 1 ≤ 3 * d)
    (mm₁ : b ≤ 3 * c) : a + b + 1 ≤ 3 * (c + d + 1) := by omega

theorem Valid'.node4L_lemma₅ {a b c d : ℕ} (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9)
    (mr₁ : 2 * d ≤ b + c + 1) (mm₂ : c ≤ 3 * b) : c + d + 1 ≤ 3 * (a + b + 1) := by omega

theorem Valid'.node4L {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' (↑y) r o₂) (Hm : 0 < size m)
    (H : size l = 0 ∧ size m = 1 ∧ size r ≤ 1 ∨
        0 < size l ∧
          ratio * size r ≤ size m ∧
            delta * size l ≤ size m + size r ∧
              3 * (size m + size r) ≤ 16 * size l + 9 ∧ size m ≤ delta * size r) :
    Valid' o₁ (@node4L α l x m y r) o₂ := by
  cases' m with s ml z mr; · cases Hm
  suffices
    BalancedSz (size l) (size ml) ∧
      BalancedSz (size mr) (size r) ∧ BalancedSz (size l + size ml + 1) (size mr + size r + 1) from
    Valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2
  rcases H with (⟨l0, m1, r0⟩ | ⟨l0, mr₁, lr₁, lr₂, mr₂⟩)
  · rw [hm.2.size_eq, Nat.succ_inj', add_eq_zero] at m1
    rw [l0, m1.1, m1.2]; revert r0; rcases size r with (_ | _ | _) <;>
      [decide; decide; (intro r0; unfold BalancedSz delta; omega)]
  · rcases Nat.eq_zero_or_pos (size r) with r0 | r0
    · rw [r0] at mr₂; cases not_le_of_lt Hm mr₂
    rw [hm.2.size_eq] at lr₁ lr₂ mr₁ mr₂
    by_cases mm : size ml + size mr ≤ 1
    · have r1 :=
        le_antisymm
          ((mul_le_mul_left (by decide)).1 (le_trans mr₁ (Nat.succ_le_succ mm) : _ ≤ ratio * 1)) r0
      rw [r1, add_assoc] at lr₁
      have l1 :=
        le_antisymm
          ((mul_le_mul_left (by decide)).1 (le_trans lr₁ (add_le_add_right mm 2) : _ ≤ delta * 1))
          l0
      rw [l1, r1]
      revert mm; cases size ml <;> cases size mr <;> intro mm
      · decide
      · rw [zero_add] at mm; rcases mm with (_ | ⟨⟨⟩⟩)
        decide
      · rcases mm with (_ | ⟨⟨⟩⟩); decide
      · rw [Nat.succ_add] at mm; rcases mm with (_ | ⟨⟨⟩⟩)
    rcases hm.3.1.resolve_left mm with ⟨mm₁, mm₂⟩
    rcases Nat.eq_zero_or_pos (size ml) with ml0 | ml0
    · rw [ml0, mul_zero, Nat.le_zero] at mm₂
      rw [ml0, mm₂] at mm; cases mm (by decide)
    have : 2 * size l ≤ size ml + size mr + 1 := by
      have := Nat.mul_le_mul_left ratio lr₁
      rw [mul_left_comm, mul_add] at this
      have := le_trans this (add_le_add_left mr₁ _)
      rw [← Nat.succ_mul] at this
      exact (mul_le_mul_left (by decide)).1 this
    refine ⟨Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · refine (mul_le_mul_left (by decide)).1 (le_trans this ?_)
      rw [two_mul, Nat.succ_le_iff]
      refine add_lt_add_of_lt_of_le ?_ mm₂
      simpa using (mul_lt_mul_right ml0).2 (by decide : 1 < 3)
    · exact Nat.le_of_lt_succ (Valid'.node4L_lemma₁ lr₂ mr₂ mm₁)
    · exact Valid'.node4L_lemma₂ mr₂
    · exact Valid'.node4L_lemma₃ mr₁ mm₁
    · exact Valid'.node4L_lemma₄ lr₁ mr₂ mm₁
    · exact Valid'.node4L_lemma₅ lr₂ mr₁ mm₂

theorem Valid'.rotateL_lemma₁ {a b c : ℕ} (H2 : 3 * a ≤ b + c) (hb₂ : c ≤ 3 * b) : a ≤ 3 * b := by
  omega

theorem Valid'.rotateL_lemma₂ {a b c : ℕ} (H3 : 2 * (b + c) ≤ 9 * a + 3) (h : b < 2 * c) :
    b < 3 * a + 1 := by omega

theorem Valid'.rotateL_lemma₃ {a b c : ℕ} (H2 : 3 * a ≤ b + c) (h : b < 2 * c) : a + b < 3 * c := by
  omega

theorem Valid'.rotateL_lemma₄ {a b : ℕ} (H3 : 2 * b ≤ 9 * a + 3) : 3 * b ≤ 16 * a + 9 := by
  omega

theorem Valid'.rotateL {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H1 : ¬size l + size r ≤ 1) (H2 : delta * size l < size r)
    (H3 : 2 * size r ≤ 9 * size l + 5 ∨ size r ≤ 3) : Valid' o₁ (@rotateL α l x r) o₂ := by
  cases' r with rs rl rx rr; · cases H2
  rw [hr.2.size_eq, Nat.lt_succ_iff] at H2
  rw [hr.2.size_eq] at H3
  replace H3 : 2 * (size rl + size rr) ≤ 9 * size l + 3 ∨ size rl + size rr ≤ 2 :=
    H3.imp (@Nat.le_of_add_le_add_right _ 2 _) Nat.le_of_succ_le_succ
  have H3_0 : size l = 0 → size rl + size rr ≤ 2 := by
    intro l0; rw [l0] at H3
    exact
      (or_iff_right_of_imp fun h => (mul_le_mul_left (by decide)).1 (le_trans h (by decide))).1 H3
  have H3p : size l > 0 → 2 * (size rl + size rr) ≤ 9 * size l + 3 := fun l0 : 1 ≤ size l =>
    (or_iff_left_of_imp <| by omega).1 H3
  have ablem : ∀ {a b : ℕ}, 1 ≤ a → a + b ≤ 2 → b ≤ 1 := by omega
  have hlp : size l > 0 → ¬size rl + size rr ≤ 1 := fun l0 hb =>
    absurd (le_trans (le_trans (Nat.mul_le_mul_left _ l0) H2) hb) (by decide)
  rw [Ordnode.rotateL_node]; split_ifs with h
  · have rr0 : size rr > 0 :=
      (mul_lt_mul_left (by decide)).1 (lt_of_le_of_lt (Nat.zero_le _) h : ratio * 0 < _)
    suffices BalancedSz (size l) (size rl) ∧ BalancedSz (size l + size rl + 1) (size rr) by
      exact hl.node3L hr.left hr.right this.1 this.2
    rcases Nat.eq_zero_or_pos (size l) with l0 | l0
    · rw [l0]; replace H3 := H3_0 l0
      have := hr.3.1
      rcases Nat.eq_zero_or_pos (size rl) with rl0 | rl0
      · rw [rl0] at this ⊢
        rw [le_antisymm (balancedSz_zero.1 this.symm) rr0]
        decide
      have rr1 : size rr = 1 := le_antisymm (ablem rl0 H3) rr0
      rw [add_comm] at H3
      rw [rr1, show size rl = 1 from le_antisymm (ablem rr0 H3) rl0]
      decide
    replace H3 := H3p l0
    rcases hr.3.1.resolve_left (hlp l0) with ⟨_, hb₂⟩
    refine ⟨Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · exact Valid'.rotateL_lemma₁ H2 hb₂
    · exact Nat.le_of_lt_succ (Valid'.rotateL_lemma₂ H3 h)
    · exact Valid'.rotateL_lemma₃ H2 h
    · exact
        le_trans hb₂
          (Nat.mul_le_mul_left _ <| le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  · rcases Nat.eq_zero_or_pos (size rl) with rl0 | rl0
    · rw [rl0, not_lt, Nat.le_zero, Nat.mul_eq_zero] at h
      replace h := h.resolve_left (by decide)
      rw [rl0, h, Nat.le_zero, Nat.mul_eq_zero] at H2
      rw [hr.2.size_eq, rl0, h, H2.resolve_left (by decide)] at H1
      cases H1 (by decide)
    refine hl.node4L hr.left hr.right rl0 ?_
    rcases Nat.eq_zero_or_pos (size l) with l0 | l0
    · replace H3 := H3_0 l0
      rcases Nat.eq_zero_or_pos (size rr) with rr0 | rr0
      · have := hr.3.1
        rw [rr0] at this
        exact Or.inl ⟨l0, le_antisymm (balancedSz_zero.1 this) rl0, rr0.symm ▸ zero_le_one⟩
      exact Or.inl ⟨l0, le_antisymm (ablem rr0 <| by rwa [add_comm]) rl0, ablem rl0 H3⟩
    exact
      Or.inr ⟨l0, not_lt.1 h, H2, Valid'.rotateL_lemma₄ (H3p l0), (hr.3.1.resolve_left (hlp l0)).1⟩

theorem Valid'.rotateR {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H1 : ¬size l + size r ≤ 1) (H2 : delta * size r < size l)
    (H3 : 2 * size l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@rotateR α l x r) o₂ := by
  refine Valid'.dual_iff.2 ?_
  rw [dual_rotateR]
  refine hr.dual.rotateL hl.dual ?_ ?_ ?_
  · rwa [size_dual, size_dual, add_comm]
  · rwa [size_dual, size_dual]
  · rwa [size_dual, size_dual]

theorem Valid'.balance'_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3)
    (H₂ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@balance' α l x r) o₂ := by
  rw [balance']; split_ifs with h h_1 h_2
  · exact hl.node' hr (Or.inl h)
  · exact hl.rotateL hr h h_1 H₁
  · exact hl.rotateR hr h h_2 H₂
  · exact hl.node' hr (Or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩)

theorem Valid'.balance'_lemma {α l l' r r'} (H1 : BalancedSz l' r')
    (H2 : Nat.dist (@size α l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l') :
    2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3 := by
  suffices @size α r ≤ 3 * (size l + 1) by
    rcases Nat.eq_zero_or_pos (size l) with l0 | l0
    · apply Or.inr; rwa [l0] at this
    change 1 ≤ _ at l0; apply Or.inl; omega
  rcases H2 with (⟨hl, rfl⟩ | ⟨hr, rfl⟩) <;> rcases H1 with (h | ⟨_, h₂⟩)
  · exact le_trans (Nat.le_add_left _ _) (le_trans h (Nat.le_add_left _ _))
  · exact
      le_trans h₂
        (Nat.mul_le_mul_left _ <| le_trans (Nat.dist_tri_right _ _) (Nat.add_le_add_left hl _))
  · exact
      le_trans (Nat.dist_tri_left' _ _)
        (le_trans (add_le_add hr (le_trans (Nat.le_add_left _ _) h)) (by omega))
  · rw [Nat.mul_succ]
    exact le_trans (Nat.dist_tri_right' _ _) (add_le_add h₂ (le_trans hr (by decide)))

theorem Valid'.balance' {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : ∃ l' r', BalancedSz l' r' ∧
          (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    Valid' o₁ (@balance' α l x r) o₂ :=
  let ⟨_, _, H1, H2⟩ := H
  Valid'.balance'_aux hl hr (Valid'.balance'_lemma H1 H2) (Valid'.balance'_lemma H1.symm H2.symm)

theorem Valid'.balance {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : ∃ l' r', BalancedSz l' r' ∧
          (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    Valid' o₁ (@balance α l x r) o₂ := by
  rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]; exact hl.balance' hr H

theorem Valid'.balanceL_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : size l = 0 → size r ≤ 1) (H₂ : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l)
    (H₃ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balanceL_eq_balance hl.2 hr.2 H₁ H₂, balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
  refine hl.balance'_aux hr (Or.inl ?_) H₃
  rcases Nat.eq_zero_or_pos (size r) with r0 | r0
  · rw [r0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos (size l) with l0 | l0
  · rw [l0]; exact le_trans (Nat.mul_le_mul_left _ (H₁ l0)) (by decide)
  replace H₂ : _ ≤ 3 * _ := H₂ l0 r0; omega

theorem Valid'.balanceL {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balanceL_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
  refine hl.balance' hr ?_
  rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
  · exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
  · exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩

theorem Valid'.balanceR_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : size r = 0 → size l ≤ 1) (H₂ : 1 ≤ size r → 1 ≤ size l → size l ≤ delta * size r)
    (H₃ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3) : Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [Valid'.dual_iff, dual_balanceR]
  have := hr.dual.balanceL_aux hl.dual
  rw [size_dual, size_dual] at this
  exact this H₁ H₂ H₃

theorem Valid'.balanceR {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [Valid'.dual_iff, dual_balanceR]; exact hr.dual.balanceL hl.dual (balance_sz_dual H)

theorem Valid'.eraseMax_aux {s l x r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂) :
    Valid' o₁ (@eraseMax α (.node' l x r)) ↑(findMax' x r) ∧
      size (.node' l x r) = size (eraseMax (.node' l x r)) + 1 := by
  have := H.2.eq_node'; rw [this] at H; clear this
  induction' r with rs rl rx rr _ IHrr generalizing l x o₁
  · exact ⟨H.left, rfl⟩
  have := H.2.2.2.eq_node'; rw [this] at H ⊢
  rcases IHrr H.right with ⟨h, e⟩
  refine ⟨Valid'.balanceL H.left h (Or.inr ⟨_, Or.inr e, H.3.1⟩), ?_⟩
  rw [eraseMax, size_balanceL H.3.2.1 h.3 H.2.2.1 h.2 (Or.inr ⟨_, Or.inr e, H.3.1⟩)]
  rw [size_node, e]; rfl

theorem Valid'.eraseMin_aux {s l} {x : α} {r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂) :
    Valid' ↑(findMin' l x) (@eraseMin α (.node' l x r)) o₂ ∧
      size (.node' l x r) = size (eraseMin (.node' l x r)) + 1 := by
  have := H.dual.eraseMax_aux
  rwa [← dual_node', size_dual, ← dual_eraseMin, size_dual, ← Valid'.dual_iff, findMax'_dual]
    at this

theorem eraseMin.valid : ∀ {t}, @Valid α _ t → Valid (eraseMin t)
  | nil, _ => valid_nil
  | node _ l x r, h => by rw [h.2.eq_node']; exact h.eraseMin_aux.1.valid

theorem eraseMax.valid {t} (h : @Valid α _ t) : Valid (eraseMax t) := by
  rw [Valid.dual_iff, dual_eraseMax]; exact eraseMin.valid h.dual

theorem Valid'.glue_aux {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
    (sep : l.All fun x => r.All fun y => x < y) (bal : BalancedSz (size l) (size r)) :
    Valid' o₁ (@glue α l r) o₂ ∧ size (glue l r) = size l + size r := by
  cases' l with ls ll lx lr; · exact ⟨hr, (zero_add _).symm⟩
  cases' r with rs rl rx rr; · exact ⟨hl, rfl⟩
  dsimp [glue]; split_ifs
  · rw [splitMax_eq]
    · cases' Valid'.eraseMax_aux hl with v e
      suffices H : _ by
        refine ⟨Valid'.balanceR v (hr.of_gt ?_ ?_) H, ?_⟩
        · refine findMax'_all (P := fun a : α => Bounded nil (a : WithTop α) o₂)
            lx lr hl.1.2.to_nil (sep.2.2.imp ?_)
          exact fun x h => hr.1.2.to_nil.mono_left (le_of_lt h.2.1)
        · exact @findMax'_all _ (fun a => All (· > a) (.node rs rl rx rr)) lx lr sep.2.1 sep.2.2
        · rw [size_balanceR v.3 hr.3 v.2 hr.2 H, add_right_comm, ← e, hl.2.1]; rfl
      refine Or.inl ⟨_, Or.inr e, ?_⟩
      rwa [hl.2.eq_node'] at bal
  · rw [splitMin_eq]
    · cases' Valid'.eraseMin_aux hr with v e
      suffices H : _ by
        refine ⟨Valid'.balanceL (hl.of_lt ?_ ?_) v H, ?_⟩
        · refine @findMin'_all (P := fun a : α => Bounded nil o₁ (a : WithBot α))
            _ rl rx (sep.2.1.1.imp ?_) hr.1.1.to_nil
          exact fun y h => hl.1.1.to_nil.mono_right (le_of_lt h)
        · exact
            @findMin'_all _ (fun a => All (· < a) (.node ls ll lx lr)) rl rx
              (all_iff_forall.2 fun x hx => sep.imp fun y hy => all_iff_forall.1 hy.1 _ hx)
              (sep.imp fun y hy => hy.2.1)
        · rw [size_balanceL hl.3 v.3 hl.2 v.2 H, add_assoc, ← e, hr.2.1]; rfl
      refine Or.inr ⟨_, Or.inr e, ?_⟩
      rwa [hr.2.eq_node'] at bal

theorem Valid'.glue {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂) :
    BalancedSz (size l) (size r) →
      Valid' o₁ (@glue α l r) o₂ ∧ size (@glue α l r) = size l + size r :=
  Valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)

theorem Valid'.merge_lemma {a b c : ℕ} (h₁ : 3 * a < b + c + 1) (h₂ : b ≤ 3 * c) :
    2 * (a + b) ≤ 9 * c + 5 := by omega

theorem Valid'.merge_aux₁ {o₁ o₂ ls ll lx lr rs rl rx rr t}
    (hl : Valid' o₁ (@Ordnode.node α ls ll lx lr) o₂) (hr : Valid' o₁ (.node rs rl rx rr) o₂)
    (h : delta * ls < rs) (v : Valid' o₁ t rx) (e : size t = ls + size rl) :
    Valid' o₁ (.balanceL t rx rr) o₂ ∧ size (.balanceL t rx rr) = ls + rs := by
  rw [hl.2.1] at e
  rw [hl.2.1, hr.2.1, delta] at h
  rcases hr.3.1 with (H | ⟨hr₁, hr₂⟩); · omega
  suffices H₂ : _ by
    suffices H₁ : _ by
      refine ⟨Valid'.balanceL_aux v hr.right H₁ H₂ ?_, ?_⟩
      · rw [e]; exact Or.inl (Valid'.merge_lemma h hr₁)
      · rw [balanceL_eq_balance v.2 hr.2.2.2 H₁ H₂, balance_eq_balance' v.3 hr.3.2.2 v.2 hr.2.2.2,
          size_balance' v.2 hr.2.2.2, e, hl.2.1, hr.2.1]
        abel
    · rw [e, add_right_comm]; rintro ⟨⟩
  intro _ _; rw [e]; unfold delta at hr₂ ⊢; omega

theorem Valid'.merge_aux {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
    (sep : l.All fun x => r.All fun y => x < y) :
    Valid' o₁ (@merge α l r) o₂ ∧ size (merge l r) = size l + size r := by
  induction' l with ls ll lx lr _ IHlr generalizing o₁ o₂ r
  · exact ⟨hr, (zero_add _).symm⟩
  induction' r with rs rl rx rr IHrl _ generalizing o₁ o₂
  · exact ⟨hl, rfl⟩
  rw [merge_node]; split_ifs with h h_1
  · cases'
      IHrl (hl.of_lt hr.1.1.to_nil <| sep.imp fun x h => h.2.1) hr.left
        (sep.imp fun x h => h.1) with
      v e
    exact Valid'.merge_aux₁ hl hr h v e
  · cases' IHlr hl.right (hr.of_gt hl.1.2.to_nil sep.2.1) sep.2.2 with v e
    have := Valid'.merge_aux₁ hr.dual hl.dual h_1 v.dual
    rw [size_dual, add_comm, size_dual, ← dual_balanceR, ← Valid'.dual_iff, size_dual,
      add_comm rs] at this
    exact this e
  · refine Valid'.glue_aux hl hr sep (Or.inr ⟨not_lt.1 h_1, not_lt.1 h⟩)

theorem Valid.merge {l r} (hl : Valid l) (hr : Valid r)
    (sep : l.All fun x => r.All fun y => x < y) : Valid (@merge α l r) :=
  (Valid'.merge_aux hl hr sep).1

theorem insertWith.valid_aux [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (f : α → α) (x : α)
    (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) :
    ∀ {t o₁ o₂},
      Valid' o₁ t o₂ →
        Bounded nil o₁ x →
          Bounded nil x o₂ →
            Valid' o₁ (insertWith f x t) o₂ ∧ Raised (size t) (size (insertWith f x t))
  | nil, _, _, _, bl, br => ⟨valid'_singleton bl br, Or.inr rfl⟩
  | node sz l y r, o₁, o₂, h, bl, br => by
    rw [insertWith, cmpLE]
    split_ifs with h_1 h_2 <;> dsimp only
    · rcases h with ⟨⟨lx, xr⟩, hs, hb⟩
      rcases hf _ ⟨h_1, h_2⟩ with ⟨xf, fx⟩
      refine
        ⟨⟨⟨lx.mono_right (le_trans h_2 xf), xr.mono_left (le_trans fx h_1)⟩, hs, hb⟩, Or.inl rfl⟩
    · rcases insertWith.valid_aux f x hf h.left bl (lt_of_le_not_le h_1 h_2) with ⟨vl, e⟩
      suffices H : _ by
        refine ⟨vl.balanceL h.right H, ?_⟩
        rw [size_balanceL vl.3 h.3.2.2 vl.2 h.2.2.2 H, h.2.size_eq]
        exact (e.add_right _).add_right _
      exact Or.inl ⟨_, e, h.3.1⟩
    · have : y < x := lt_of_le_not_le ((total_of (· ≤ ·) _ _).resolve_left h_1) h_1
      rcases insertWith.valid_aux f x hf h.right this br with ⟨vr, e⟩
      suffices H : _ by
        refine ⟨h.left.balanceR vr H, ?_⟩
        rw [size_balanceR h.3.2.1 vr.3 h.2.2.1 vr.2 H, h.2.size_eq]
        exact (e.add_left _).add_right _
      exact Or.inr ⟨_, e, h.3.1⟩

theorem insertWith.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (f : α → α) (x : α)
    (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) {t} (h : Valid t) : Valid (insertWith f x t) :=
  (insertWith.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

theorem insert_eq_insertWith [@DecidableRel α (· ≤ ·)] (x : α) :
    ∀ t, Ordnode.insert x t = insertWith (fun _ => x) x t
  | nil => rfl
  | node _ l y r => by
    unfold Ordnode.insert insertWith; cases cmpLE x y <;> simp [insert_eq_insertWith]

theorem insert.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : Valid t) :
    Valid (Ordnode.insert x t) := by
  rw [insert_eq_insertWith]; exact insertWith.valid _ _ (fun _ _ => ⟨le_rfl, le_rfl⟩) h

theorem insert'_eq_insertWith [@DecidableRel α (· ≤ ·)] (x : α) :
    ∀ t, insert' x t = insertWith id x t
  | nil => rfl
  | node _ l y r => by
    unfold insert' insertWith; cases cmpLE x y <;> simp [insert'_eq_insertWith]

theorem insert'.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : Valid t) :
    Valid (insert' x t) := by
  rw [insert'_eq_insertWith]; exact insertWith.valid _ _ (fun _ => id) h

theorem Valid'.map_aux {β} [Preorder β] {f : α → β} (f_strict_mono : StrictMono f) {t a₁ a₂}
    (h : Valid' a₁ t a₂) :
    Valid' (Option.map f a₁) (map f t) (Option.map f a₂) ∧ (map f t).size = t.size := by
  induction t generalizing a₁ a₂ with
  | nil =>
    simp only [map, size_nil, and_true]; apply valid'_nil
    cases a₁; · trivial
    cases a₂; · trivial
    simp only [Bounded]
    exact f_strict_mono h.ord
  | node _ _ _ _ t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    cases' t_ih_l' with t_l_valid t_l_size
    cases' t_ih_r' with t_r_valid t_r_size
    simp only [map, size_node, and_true]
    constructor
    · exact And.intro t_l_valid.ord t_r_valid.ord
    · constructor
      · rw [t_l_size, t_r_size]; exact h.sz.1
      · constructor
        · exact t_l_valid.sz
        · exact t_r_valid.sz
    · constructor
      · rw [t_l_size, t_r_size]; exact h.bal.1
      · constructor
        · exact t_l_valid.bal
        · exact t_r_valid.bal

theorem map.valid {β} [Preorder β] {f : α → β} (f_strict_mono : StrictMono f) {t} (h : Valid t) :
    Valid (map f t) :=
  (Valid'.map_aux f_strict_mono h).1

theorem Valid'.erase_aux [@DecidableRel α (· ≤ ·)] (x : α) {t a₁ a₂} (h : Valid' a₁ t a₂) :
    Valid' a₁ (erase x t) a₂ ∧ Raised (erase x t).size t.size := by
  induction t generalizing a₁ a₂ with
  | nil =>
    simpa [erase, Raised]
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    simp only [erase, size_node]
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    cases' t_ih_l' with t_l_valid t_l_size
    cases' t_ih_r' with t_r_valid t_r_size
    cases cmpLE x t_x <;> rw [h.sz.1]
    · suffices h_balanceable : _ by
        constructor
        · exact Valid'.balanceR t_l_valid h.right h_balanceable
        · rw [size_balanceR t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz h_balanceable]
          repeat apply Raised.add_right
          exact t_l_size
      left; exists t_l.size; exact And.intro t_l_size h.bal.1
    · have h_glue := Valid'.glue h.left h.right h.bal.1
      cases' h_glue with h_glue_valid h_glue_sized
      constructor
      · exact h_glue_valid
      · right; rw [h_glue_sized]
    · suffices h_balanceable : _ by
        constructor
        · exact Valid'.balanceL h.left t_r_valid h_balanceable
        · rw [size_balanceL h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz h_balanceable]
          apply Raised.add_right
          apply Raised.add_left
          exact t_r_size
      right; exists t_r.size; exact And.intro t_r_size h.bal.1

theorem erase.valid [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : Valid t) : Valid (erase x t) :=
  (Valid'.erase_aux x h).1

theorem size_erase_of_mem [@DecidableRel α (· ≤ ·)] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂)
    (h_mem : x ∈ t) : size (erase x t) = size t - 1 := by
  induction t generalizing a₁ a₂ with
  | nil =>
    contradiction
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    dsimp only [Membership.mem, mem] at h_mem
    unfold erase
    revert h_mem; cases cmpLE x t_x <;> intro h_mem <;> dsimp only at h_mem ⊢
    · have t_ih_l := t_ih_l' h_mem
      clear t_ih_l' t_ih_r'
      have t_l_h := Valid'.erase_aux x h.left
      cases' t_l_h with t_l_valid t_l_size
      rw [size_balanceR t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz
          (Or.inl (Exists.intro t_l.size (And.intro t_l_size h.bal.1)))]
      rw [t_ih_l, h.sz.1]
      have h_pos_t_l_size := pos_size_of_mem h.left.sz h_mem
      revert h_pos_t_l_size; cases' t_l.size with t_l_size <;> intro h_pos_t_l_size
      · cases h_pos_t_l_size
      · simp [Nat.add_right_comm]
    · rw [(Valid'.glue h.left h.right h.bal.1).2, h.sz.1]; rfl
    · have t_ih_r := t_ih_r' h_mem
      clear t_ih_l' t_ih_r'
      have t_r_h := Valid'.erase_aux x h.right
      cases' t_r_h with t_r_valid t_r_size
      rw [size_balanceL h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz
          (Or.inr (Exists.intro t_r.size (And.intro t_r_size h.bal.1)))]
      rw [t_ih_r, h.sz.1]
      have h_pos_t_r_size := pos_size_of_mem h.right.sz h_mem
      revert h_pos_t_r_size; cases' t_r.size with t_r_size <;> intro h_pos_t_r_size
      · cases h_pos_t_r_size
      · simp [Nat.add_assoc]

end

end Ordnode

/-- An `Ordset α` is a finite set of values, represented as a tree. The operations on this type
maintain that the tree is balanced and correctly stores subtree sizes at each level. The
correctness property of the tree is baked into the type, so all operations on this type are correct
by construction. -/
def Ordset (α : Type*) [Preorder α] :=
  { t : Ordnode α // t.Valid }

namespace Ordset

open Ordnode

variable [Preorder α]

/-- O(1). The empty set. -/
nonrec def nil : Ordset α :=
  ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-- O(1). Get the size of the set. -/
def size (s : Ordset α) : ℕ :=
  s.1.size

/-- O(1). Construct a singleton set containing value `a`. -/
protected def singleton (a : α) : Ordset α :=
  ⟨singleton a, valid_singleton⟩

instance instEmptyCollection : EmptyCollection (Ordset α) :=
  ⟨nil⟩

instance instInhabited : Inhabited (Ordset α) :=
  ⟨nil⟩

instance instSingleton : Singleton α (Ordset α) :=
  ⟨Ordset.singleton⟩

/-- O(1). Is the set empty? -/
def Empty (s : Ordset α) : Prop :=
  s = ∅

theorem empty_iff {s : Ordset α} : s = ∅ ↔ s.1.empty :=
  ⟨fun h => by cases h; exact rfl,
    fun h => by cases s with | mk s_val _ => cases s_val <;> [rfl; cases h]⟩

instance Empty.instDecidablePred : DecidablePred (@Empty α _) :=
  fun _ => decidable_of_iff' _ empty_iff

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, this replaces it. -/
protected def insert [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) :
    Ordset α :=
  ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩

instance instInsert [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] : Insert α (Ordset α) :=
  ⟨Ordset.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
nonrec def insert' [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) :
    Ordset α :=
  ⟨insert' x s.1, insert'.valid _ s.2⟩

section

variable [@DecidableRel α (· ≤ ·)]

/-- O(log n). Does the set contain the element `x`? That is,
  is there an element that is equivalent to `x` in the order? -/
def mem (x : α) (s : Ordset α) : Bool :=
  x ∈ s.val

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
  if it exists. -/
def find (x : α) (s : Ordset α) : Option α :=
  Ordnode.find x s.val

instance instMembership : Membership α (Ordset α) :=
  ⟨fun s x => mem x s⟩

instance mem.decidable (x : α) (s : Ordset α) : Decidable (x ∈ s) :=
  instDecidableEqBool _ _

theorem pos_size_of_mem {x : α} {t : Ordset α} (h_mem : x ∈ t) : 0 < size t := by
  simp? [Membership.mem, mem] at h_mem says
    simp only [Membership.mem, mem, Bool.decide_eq_true] at h_mem
  apply Ordnode.pos_size_of_mem t.property.sz h_mem

end

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element. -/
def erase [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

/-- O(n). Map a function across a tree, without changing the structure. -/
def map {β} [Preorder β] (f : α → β) (f_strict_mono : StrictMono f) (s : Ordset α) : Ordset β :=
  ⟨Ordnode.map f s.val, Ordnode.map.valid f_strict_mono s.property⟩

end Ordset

set_option linter.style.longFile 1700
