/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki, Brendan Murphy
-/
import Std.Data.RBMap.Basic
import Mathlib.Data.Num.Basic
import Mathlib.Order.Basic
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Util.CompileInductive
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.FinEnum

#align_import data.tree from "leanprover-community/mathlib"@"ed989ff568099019c6533a4d94b27d852a5710d8"

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `Tree Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `Tree Unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

/-- A binary tree with values stored in non-leaf nodes. -/
inductive Tree.{u} (α : Type u) : Type u
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α
  deriving DecidableEq, Repr -- Porting note: Removed `has_reflect`, added `Repr`.
#align tree Tree

namespace Tree

universe u

variable {α : Type u}

-- Porting note: replaced with `deriving Repr` which builds a better instance anyway
#noalign tree.repr

open Std (RBNode)

/-- Makes a `Tree α` out of a red-black tree. -/
def ofRBNode : RBNode α → Tree α
  | RBNode.nil => nil
  | RBNode.node _color l key r => node key (ofRBNode l) (ofRBNode r)
#align tree.of_rbnode Tree.ofRBNode

inductive Path where
  | here  : Path
  | left  : Path → Path
  | right : Path → Path
  deriving DecidableEq, Repr, Ord

@[reducible]
def PosNum.toPath : PosNum → Path
  | PosNum.one    => Path.here
  | PosNum.bit0 b => Path.left (PosNum.toPath b)
  | PosNum.bit1 b => Path.right (PosNum.toPath b)

namespace Path

lemma left_injective : Function.Injective left :=
  fun x y => Eq.mp (left.injEq x y)

lemma right_injective : Function.Injective right :=
  fun x y => Eq.mp (right.injEq x y)

def isHere?  : Path → Bool | here    => true | left _ | right _ => false
def isLeft?  : Path → Bool | left  _ => true | here   | right _ => false
def isRight? : Path → Bool | right _ => true | here   | left  _ => false

-- def isLeft?

section
variable {β : Sort u} (b : β) (l : β → β) (r : β → β)
def run : Path → β
  | here    => b
  | left  p => l (run p)
  | right p => r (run p)
@[simp] lemma run_here : here.run b l r = b := rfl
@[simp] lemma run_left p : (left p).run b l r = l (p.run b l r) := rfl
@[simp] lemma run_right p : (right p).run b l r = r (p.run b l r) := rfl
end

-- would be nice if Lean could synthesize this one
def equivPosNum : Path ≃ PosNum where
  toFun     := Path.run PosNum.one PosNum.bit0 PosNum.bit1
  invFun    := PosNum.toPath
  left_inv  := by
    intro p
    induction' p with _ ih _ ih
    <;> dsimp only [PosNum.toPath] <;> rw [ih]
  right_inv := by
    intro b
    induction' b with _ ih _ ih
    <;> dsimp only [Path.run] <;> rw [ih]

def equivBitString : Path ≃ List Bool where
  toFun     := Path.run [] (List.cons false) (List.cons true)
  invFun    := List.foldr (fun b => bif b then right else left) here
  left_inv  := by
    intro p
    induction' p with _ ih _ ih
    <;> dsimp only [run, List.foldr]
    <;> simp only [cond_false, cond_true, ih]
  right_inv := by
    intro bs
    induction' bs with b bs ih; rfl
    cases b <;> dsimp only [run] <;> rw [ih]

lemma foldr_equivBitString_eq_run {β : Type u} (b : β) (l : β → β) (r : β → β)
    : ∀ p, List.foldr (cond . r l) b (equivBitString p) = p.run b l r := by
  dsimp only [equivBitString, Equiv.coe_fn_mk]
  intro p; induction' p with p ih p ih
    <;> dsimp only [List.foldr, run] <;> simp only [ih, cond_true, cond_false]

def length' : Path → ℕ :=
  let rec go (acc : ℕ) : Path → ℕ
    | here    => acc
    | left p  => go (acc + 1) p
    | right p => go (acc + 1) p
  go 0

@[implemented_by length']
def length : Path → ℕ := run 0 (. + 1) (. + 1)

lemma length'_correct : length' = length := by
  suffices : ∀ p acc, length'.go acc p = run 0 (. + 1) (. + 1) p + acc
  . funext p; exact Eq.trans (this p 0) (Nat.add_zero _)
  intro p; induction' p with p ih p ih
  <;> simp only [length'.go, run, self_eq_add_left, implies_true]
  <;> simp only [ih, Nat.add_comm, Nat.add_assoc, implies_true]

lemma length_equivBitString_eq_length (p : Path)
    : (equivBitString p).length = length p :=
  by refine Eq.trans (congrFun ?_ _) (foldr_equivBitString_eq_run _ _ _ p)
     simp only [Bool.cond_self]
     -- how is this not in the standard library??
     funext xs; induction xs; rfl
     simp only [List.length_cons, List.foldr_cons, Nat.succ.injEq]; apply_assumption

-- appendRev p q appends the reverse of p to q
-- analogous to List.reverseAux
def appendRev : Path → Path → Path
  | here,    acc => acc
  | left  p, acc => appendRev p (left acc)
  | right p, acc => appendRev p (right acc)

private def reverse' (p : Path) : Path := appendRev p here
private def append' (p q : Path) : Path := appendRev (reverse' p) q

@[implemented_by append']
def append : Path → Path → Path
  | here,    q => q
  | left  p, q => left (append p q)
  | right p, q => right (append p q)

@[implemented_by reverse']
def reverse := run here (append . (left here)) (append . (right here))

lemma appendRev_eq_BitString_reverseAux :
    ∀ (p q : Path), equivBitString (appendRev p q)
                  = List.reverseAux (equivBitString p) (equivBitString q) := by
  dsimp only [equivBitString, Equiv.coe_fn_mk]
  intro p; induction' p with p ih p ih <;> intro q
    <;> dsimp only [List.reverseAux, appendRev, run] <;> rw [ih] <;> rfl

lemma append_eq_BitString_append :
    ∀ (p q : Path), equivBitString (append p q)
              = List.append (equivBitString p) (equivBitString q) := by
  dsimp only [equivBitString, Equiv.coe_fn_mk]
  intro p; induction' p with p ih p ih <;> intro q
    <;> dsimp only [List.append, append, run] <;> rw [ih]

lemma reverse_eq_BitString_reverse :
    ∀ (p : Path), equivBitString (reverse p)
                = List.reverse (equivBitString p) := by
  dsimp only [equivBitString, Equiv.coe_fn_mk, reverse]
  intro p; induction' p with p ih p ih
    <;> dsimp only [append, run, List.reverse_nil]
    <;> rw [List.reverse_cons]
    <;> refine Eq.trans (append_eq_BitString_append _ _) ?_
    <;> simp only [equivBitString, Equiv.coe_fn_mk, ih] <;> rfl

lemma reverse'_correct : reverse' = reverse :=
  funext $ fun p => equivBitString.left_inv.injective
         $ Eq.trans (appendRev_eq_BitString_reverseAux p here)
                    $ Eq.symm $ reverse_eq_BitString_reverse p

lemma append'_correct : append' = append :=
  funext₂ $ fun p q => equivBitString.left_inv.injective $ by
    dsimp [append', append]
    rw [reverse'_correct, appendRev_eq_BitString_reverseAux,
        append_eq_BitString_append, reverse_eq_BitString_reverse,
        List.append_eq_appendTR, List.appendTR]

lemma reverse_reverse (p : Path) : p.reverse.reverse = p :=
  equivBitString.left_inv.injective
  $ by simp only [Equiv.toFun_as_coe, reverse_eq_BitString_reverse, List.reverse_reverse]

lemma appendRev_correct : appendRev = append ∘ reverse :=
  funext $ by
    simp only [funext, ← append'_correct, append', reverse'_correct,
                Function.comp_apply, reverse_reverse, implies_true]

section AppendLemmas

instance : Append Path where append := append

@[simp] theorem append_eq (p q : Path) : append p q = p ++ q := rfl
@[simp] theorem here_append (p : Path) : here ++ p = p := rfl
@[simp] theorem append_here (p : Path) : p ++ here = p :=
  equivBitString.left_inv.injective $ by
    simp only [← append_eq, Equiv.toFun_as_coe, append_eq_BitString_append]
    exact List.append_nil _

@[simp] theorem left_append  (p q : Path) : left  p ++ q = left  (p ++ q) := rfl
@[simp] theorem right_append (p q : Path) : right p ++ q = right (p ++ q) := rfl

theorem append_assoc (p q r : Path) : (p ++ q) ++ r = p ++ (q ++ r) :=
  equivBitString.left_inv.injective $ by
    simp only [← append_eq, Equiv.toFun_as_coe, append_eq_BitString_append]
    rw [List.append_eq, List.append_eq, List.append_assoc]; rfl

@[simp] theorem length_append (p q : Path) :
    length (p ++ q) = length p + length q := by
  induction' p with p ih p ih <;> simp only [length, run, zero_add, here_append]
    <;> rw [add_right_comm, add_left_inj] <;> apply_assumption

end AppendLemmas

def validFor : Path → Tree α → Bool
  | _, nil => false
  | here,    node _ _ _ => true
  | left  p, node _ l _ => p.validFor l
  | right p, node _ _ r => p.validFor r

@[simp] lemma validFor_nil {p : Path} : p.validFor (@nil α) = false :=
  by cases p <;> rfl

lemma reconstruct_eq_id' :
    ∀ (p : Path), p.run Path.here Path.left Path.right = p
  | here    => rfl
  | left  p => congrArg left  (reconstruct_eq_id' p)
  | right p => congrArg right (reconstruct_eq_id' p)

lemma reconstruct_eq_id : Path.run Path.here Path.left Path.right = id :=
  funext reconstruct_eq_id'

def isPrefix : Path → Path → Bool
  | here,    _       => true
  | left  p, left  q => isPrefix p q
  | right p, right q => isPrefix p q
  | _,       _       => false

lemma isPrefix_def : ∀ p q, isPrefix p q ↔ (∃ r, q = append p r) := by
  intro p; induction' p with p ih p ih <;> intro q <;> cases' q with q q
    <;> simp only [isPrefix, append, exists_eq', exists_false, left.injEq, right.injEq]
    <;> simp only [ih]

lemma isPrefix_correct p q :
    isPrefix p q ↔ equivBitString p <+: equivBitString q :=
  by simp only [isPrefix_def, List.IsPrefix, Equiv.toFun_as_coe,
                equivBitString.right_inv.surjective.exists,
                ← List.append_eq, ← append_eq_BitString_append,
                EmbeddingLike.apply_eq_iff_eq]
     exact exists_congr $ fun _ => Iff.intro Eq.symm Eq.symm

def isStrictPrefix : Path → Path → Bool
  | here,    here    => false
  | here,    _       => true
  | left  p, left  q => isStrictPrefix p q
  | right p, right q => isStrictPrefix p q
  | _,       _       => false

lemma isStrictPrefix_def :
    ∀ p q, isStrictPrefix p q ↔ isPrefix p q ∧ p ≠ q := by
  intro p; induction' p with p ih p ih <;> intro q <;> cases' q with q q
    <;> simp only [isStrictPrefix, isPrefix, ne_eq, not_false_eq_true,
                   and_self, and_true, left.injEq, right.injEq, iff_self_and]
    <;> simp only [ih]

lemma isStrictPrefix_length_lt :
    ∀ {p q}, isStrictPrefix p q → length p < length q := by
  dsimp [length]; intro p; induction p <;> intro q <;> cases q
    <;> simp only [isStrictPrefix, run, add_pos_iff, or_true, forall_true_left,
                   not_lt_zero', IsEmpty.forall_iff, Nat.succ_lt_succ_iff]
    <;> apply_assumption

lemma isPrefix_length_le (p q : Path) (h : isPrefix p q) :
    length p ≤ length q :=
  if h' : p = q
  then h' ▸ le_refl (length q)
  else Nat.le_of_lt $ isStrictPrefix_length_lt $ (isStrictPrefix_def p q).mpr ⟨h, h'⟩

-- the lexicographic order, interpreting paths as lists with L < R
def lexLE : Path → Path → Bool
  | here,    _       => true
  | _,       here    => false
  | left  p, left  q => lexLE p q
  | right p, right q => lexLE p q
  | left  _, right _ => true
  | right _, left  _ => false

lemma lexLE_rel : ∀ p, lexLE p p
  | here => rfl
  | left p => lexLE_rel p
  | right p => lexLE_rel p

lemma lexLE_trans : ∀ p q r, lexLE p q → lexLE q r → lexLE p r := by
  intro p; induction' p with p ih_p p ih_p
    <;> intro q <;> cases' q with q q <;> intro r <;> cases' r with r r
    <;> simp only [lexLE, IsEmpty.forall_iff, implies_true]
    <;> apply_assumption

lemma lexLE_antisymm : ∀ p q, lexLE p q → lexLE q p → p = q := by
  intro p; induction' p with p ih_p p ih_p
    <;> intro q <;> cases' q with q q
    <;> simp only [lexLE, IsEmpty.forall_iff, left.injEq, right.injEq]
    <;> apply_assumption

open List.Lex

lemma lexLE_correct : ∀ p q,
    lexLE p q ↔ equivBitString p ≤ equivBitString q := by
  dsimp [equivBitString]
  intro p; induction' p with p ih p ih <;> intro q <;> cases' q with q q
  <;> simp only [LE.le, lexLE, equivBitString, run, false_or, true_iff, or_self,
                 not_nil_right, List.cons.injEq, true_and, false_and, false_iff]
  <;> try { exact (nil_left_or_eq_nil _).resolve_right (List.cons_ne_nil _ _) }
  <;> try { rw [ih, List.Lex.cons_iff]; exact le_iff_eq_or_lt }
  . constructor; exact Bool.false_lt_true
  . rintro ⟨⟩; apply not_lt_of_lt Bool.false_lt_true; assumption

private def longestCommonPrefix' : Path → Path → Path :=
  let rec go (acc : Path) : Path → Path → Path
    | left  p, left  q => go (left  acc) p q
    | right p, right q => go (right acc) p q
    | _,       _       => acc
  fun p q => reverse (go here p q)

@[implemented_by longestCommonPrefix']
def longestCommonPrefix : Path → Path → Path
  | left  p, left  q => left  (longestCommonPrefix p q)
  | right p, right q => right (longestCommonPrefix p q)
  | _,       _       => here

lemma longestCommonPrefix'_correct :
    longestCommonPrefix' = longestCommonPrefix := by
  suffices : ∀ acc p q, longestCommonPrefix'.go acc p q
                      = appendRev (longestCommonPrefix p q) acc
  . ext p q; specialize this here p q
    simp only [appendRev_correct, Function.comp_apply, append_eq, append_here] at this
    exact Eq.trans (congrArg reverse this) (reverse_reverse _)
  intro acc p; revert acc; induction p <;> intros _ q <;> cases q
    <;> simp only [longestCommonPrefix'.go, appendRev] <;> apply_assumption

lemma longestCommonPrefix_comm :
    ∀ p q, longestCommonPrefix p q = longestCommonPrefix q p := by
  intro p; induction p <;> intro q <;> cases q
    <;> simp only [longestCommonPrefix, left.injEq, right.injEq]
    <;> apply_assumption

lemma longestCommonPrefix_isPrefix_left :
    ∀ p q, isPrefix (longestCommonPrefix p q) p := by
  intro p; induction p <;> intro q <;> cases q
    <;> simp only [longestCommonPrefix, left.injEq, right.injEq]
    <;> apply_assumption

lemma longestCommonPrefix_isPrefix_right (p q : Path) :
    isPrefix (longestCommonPrefix p q) q :=
  longestCommonPrefix_comm p q ▸ longestCommonPrefix_isPrefix_left q p

lemma longestCommonPrefix_is_maximum :
    ∀ {p q r}, isPrefix p q → isPrefix p r
             → isPrefix p (longestCommonPrefix q r) := by
  intro p; induction' p with p ih p ih <;> intro q
    <;> induction' q with q ih' q ih' <;> intro r <;> cases' r with r r
    <;> simp only [isPrefix, IsEmpty.forall_iff, forall_true_left, implies_true]
    <;> apply_assumption

lemma longestCommonPrefix_is_longest {p q r} (h1 : isPrefix p q)
    (h2 : isPrefix p r) : length p ≤ length (longestCommonPrefix q r) :=
  isPrefix_length_le _ _ $ longestCommonPrefix_is_maximum h1 h2

lemma isPrefix_total_of_common_extension :
    ∀ {p q r}, isPrefix p r → isPrefix q r → isPrefix p q ∨ isPrefix q p := by
  intro p; induction' p with p ih p ih <;> intro q
    <;> induction' q with q ih' q ih' <;> intro r <;> cases' r with r r
    <;> simp only [isPrefix, IsEmpty.forall_iff, forall_true_left, implies_true]
    <;> apply_assumption

lemma isStrictPrefix_trichot_of_common_extension {p q r}
    (h1 : isStrictPrefix p r) (h2 : isStrictPrefix q r)
    : isStrictPrefix p q ∨ p = q ∨ isStrictPrefix q p := by
  simp only [isStrictPrefix_def, ne_eq] at h1 h2 ⊢
  obtain ⟨h1, h1'⟩ := h1; obtain ⟨h2, h2'⟩ := h2
  by_cases p = q
  . right; left; assumption
  cases isPrefix_total_of_common_extension h1 h2
  . left; constructor <;> assumption
  . replace h := Ne.symm h; right; right; constructor <;> assumption

end Path

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
def indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) : Tree α → Option Path
  | nil => none
  | node a t₁ t₂ =>
    match cmpUsing lt x a with
    | Ordering.lt => Path.left <$> indexOf lt x t₁
    | Ordering.eq => some Path.here
    | Ordering.gt => Path.right <$> indexOf lt x t₂
#align tree.index_of Tree.indexOf

/-- Retrieves the element obtained by following the given path in the tree,
or none if there tree does not contain this path. -/
def follow : Path → Tree α → Option α
  | _, nil => none
  | Path.here,    node a _ _ => some a
  | Path.left  p, node _ l _ => l.follow p
  | Path.right p, node _ _ r => r.follow p

/-- Retrieves an element uniquely determined by a `PosNum` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `PosNum.one` - retrieve from here -/
def get : PosNum → Tree α → Option α
  | _, nil => none
  | PosNum.one,    node a _ _ => some a
  | PosNum.bit0 n, node _ l _ => l.get n
  | PosNum.bit1 n, node _ _ r => r.get n
#align tree.get Tree.get

lemma get_eq_follow (p : PosNum) :
    ∀ (t : Tree α), t.follow (PosNum.toPath p) = t.get p :=
  by induction' p <;> intro t <;> induction' t <;> apply_assumption

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `Tree.follow`. -/
def followOrElse (p : Path) (t : Tree α) (v : α) : α :=
  (t.follow p).getD v

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `Tree.get`. -/
def getOrElse (n : PosNum) (t : Tree α) (v : α) : α :=
  (t.get n).getD v
#align tree.get_or_else Tree.getOrElse

lemma followable_iff_validFor (p : Path) :
    ∀ (t : Tree α), (t.follow p).isSome = p.validFor t :=
  by induction' p <;> intro t <;> induction' t <;> apply_assumption

/-- Apply a function to each value in the tree.  This is the `map` function for the `Tree` functor. -/
def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)
#align tree.map Tree.map

@[simp] lemma map_nil {β} (f : α → β) : map f nil = nil := rfl
@[simp] lemma map_node {β} (f : α → β) {a l r} :
    map f (node a l r) = node (f a) (map f l) (map f r) := rfl

-- states that `follow` is a natural transformation
-- could define a version of this for traverse too,
-- saying it's a traversable morphism
@[simp]
lemma follow_naturality {β} (f : α → β) (p : Path) (t : Tree α) :
    (Tree.map f t).follow p = Option.map f (t.follow p) := by
  revert t
  induction' p with p ih p ih
    <;> intro t <;> cases' t with a l r
    <;> simp only [map, follow, Option.map_none', Option.map_some']
    <;> simp [ih]

@[simp]
lemma validFor_map {β} (f : α → β) (p : Path) (t : Tree α) :
    p.validFor (Tree.map f t) = p.validFor t :=
  by simp only [← followable_iff_validFor, follow_naturality, Option.isSome_map]

lemma validFor_map' {β} (f : α → β) (p : Path) (t : Tree α) :
    p.validFor t → p.validFor (Tree.map f t) := Eq.trans (validFor_map f p t)

inductive VisitOrder | Node1st | Node2nd | Node3rd
  deriving DecidableEq, Repr, Ord

section traversals

-- really what's going on here is that for any `σ ∈ S_n` and applicative `m` there is an operation
-- liftA σ : {α₁ … αₙ β : Type} → (f : α₁ → … → αₙ → β) → (x₁ : m α₁) → ⋯ (xₙ : m αₙ) → m β
-- liftA σ f x₁ … xₙ = (f ∘ σ) <$> x₁ <*> x₂ <*> … <*> xₙ
-- which sequences the input actions in the order determined by σ and then applies the function
-- + some stuff about thunking or macros or such
@[inline]
def depthFirst.branch_step (o : VisitOrder) {m} [Applicative m] {β}
  : (Unit → (m β)) → (Unit → (m (Tree β))) → (Unit → (m (Tree β))) → m (Tree β) :=
  match o with
  | VisitOrder.Node1st =>
    fun b l r => Seq.seq (Seq.seq (node <$> b ()) l) r
  | VisitOrder.Node2nd =>
    fun b l r => Seq.seq (Seq.seq ((fun l' b' r' => node b' l' r') <$> l ()) b) r
  | VisitOrder.Node3rd =>
    fun b l r => Seq.seq (Seq.seq ((fun l' r' b' => node b' l' r') <$> l ()) r) b

-- recursively traverses the tree, visitng the left subtree before the right subtree
-- the parameter `o` determines whether the node is visited before, between, or after the subtrees
-- to traverse the right subtree before the left subtree use `SeqOpposite m`
def depthFirst (o : VisitOrder) :=
  let helper := @depthFirst.branch_step o
  let rec go {m} [Applicative m] {α β} (f : α → m β) : Tree α → m (Tree β)
    | nil => pure nil
    | node a l r => helper (fun _ => f a) (fun _ => go f l) (fun _ => go f r)
  @go

def traversePreorder {m} [Applicative m] {α β} (f : α → m β) (t : Tree α)
  := inline (depthFirst VisitOrder.Node1st f t)

def traverseInorder {m} [Applicative m] {α β} (f : α → m β) (t : Tree α)
  := inline (depthFirst VisitOrder.Node2nd f t)

def traversePostorder {m} [Applicative m] {α β} (f : α → m β) (t : Tree α)
  := inline (depthFirst VisitOrder.Node3rd f t)

@[simp]
lemma traversePreorder_nil {m} [Applicative m] {α β} (f : α → m β)
  : traversePreorder f nil = pure nil := rfl

@[simp]
lemma traversePreorder_node {m} [Applicative m] {α β} (f : α → m β) : ∀ (a l r),
    traversePreorder f (node a l r)
    = node <$> f a <*> traversePreorder f l <*> traversePreorder f r :=
  fun _ _ _ => rfl

@[simp]
lemma traverseInorder_nil {m} [Applicative m] {α β} (f : α → m β)
  : traverseInorder f nil = pure nil := rfl

@[simp]
lemma traverseInorder_node {m} [Applicative m] {α β} (f : α → m β) : ∀ (a l r),
    traverseInorder f (node a l r)
    = (fun l' b' r' => node b' l' r') <$> traverseInorder f l <*> f a <*> traverseInorder f r :=
  fun _ _ _ => rfl

@[simp]
lemma traversePostorder_nil {m} [Applicative m] {α β} (f : α → m β)
  : traversePostorder f nil = pure nil := rfl

@[simp]
lemma traversePostorder_node {m} [Applicative m] {α β} (f : α → m β) : ∀ (a l r),
    traversePostorder f (node a l r)
    = (fun l' r' b' => node b' l' r') <$> traversePostorder f l <*> traversePostorder f r <*> f a :=
  fun _ _ _ => rfl

-- not sure how to implement breadth first search efficiently
-- but it should also give a Traversable instance?

end traversals

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp]
def numNodes : Tree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1
#align tree.num_nodes Tree.numNodes

/-- The number of leaves of a binary tree -/
@[simp]
def numLeaves : Tree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves
#align tree.num_leaves Tree.numLeaves

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
def height : Tree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1
#align tree.height Tree.height

theorem numLeaves_eq_numNodes_succ (x : Tree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
#align tree.num_leaves_eq_num_nodes_succ Tree.numLeaves_eq_numNodes_succ

theorem numLeaves_pos (x : Tree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ
#align tree.num_leaves_pos Tree.numLeaves_pos

theorem height_le_numNodes : ∀ x : Tree α, x.height ≤ x.numNodes
  | nil => le_rfl
  | node _ a b =>
    Nat.succ_le_succ
      (max_le (_root_.trans a.height_le_numNodes <| a.numNodes.le_add_right _)
        (_root_.trans b.height_le_numNodes <| b.numNodes.le_add_left _))
#align tree.height_le_num_nodes Tree.height_le_numNodes

-- Notation for making a node with `Unit` data
scoped infixr:65 " △ " => Tree.node ()

-- porting note: workaround for leanprover/lean4#2049
compile_inductive% Tree

@[elab_as_elim]
def unitRecOn {motive : Tree Unit → Sort*} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
    -- Porting note: Old proof was `t.recOn base fun u => u.recOn ind` but
    -- structure eta makes it unnecessary (https://github.com/leanprover/lean4/issues/777).
    t.recOn base fun _u => ind
#align tree.unit_rec_on Tree.unitRecOn

end Tree

/-- A binary tree with values of one type stored in non-leaf nodes
and values of another in the leaves. -/
inductive Tree'.{u, v} (N : Type u) (L : Type v) : Type (max u v)
  | leaf : L → Tree' N L
  | branch : N → Tree' N L → Tree' N L → Tree' N L
  deriving DecidableEq, Repr

namespace Tree'

def bimap.{u₁, v₁, u₂, v₂} {N : Type u₁} {N' : Type u₂} {L : Type v₁} {L' : Type v₂}
  (f : N → N') (g : L → L') : Tree' N L → Tree' N' L'
  | leaf x => leaf (g x)
  | branch y l r => branch (f y) (bimap f g l) (bimap f g r)

def mapLeaves.{u₁, v₁, v₂} {N : Type u₁} {L : Type v₁} {L' : Type v₂} (g : L → L') :=
  bimap (id : N → N) g

def mapNodes.{u₁, v₁, u₂} {N : Type u₁} {N' : Type u₂} {L : Type v₁} (f : N → N') :=
  bimap f (id : L → L)

universe u v w

-- grafts a new tree onto each leaf
def bind {N : Type u} {L : Type v} {L' : Type w}
    : Tree' N L → (L → Tree' N L') → Tree' N L'
  | leaf x, f => f x
  | branch y l r, f => branch y (bind l f) (bind r f)

section traversals

open Tree (VisitOrder)

@[inline]
def depthFirst.branch_step (o : VisitOrder) {m : Type (max u v) → Type w} [Applicative m]
  {N' L' : Type (max u v)}
  : (Unit → m N') → (Unit → (m (Tree' N' L'))) → (Unit → (m (Tree' N' L'))) → m (Tree' N' L') :=
  match o with
  | VisitOrder.Node1st =>
    fun b l r => Seq.seq (Seq.seq (branch <$> b ()) l) r
  | VisitOrder.Node2nd =>
    fun b l r => Seq.seq (Seq.seq ((fun l' b' r' => branch b' l' r') <$> l ()) b) r
  | VisitOrder.Node3rd =>
    fun b l r => Seq.seq (Seq.seq ((fun l' r' b' => branch b' l' r') <$> l ()) r) b

def depthFirst (o : VisitOrder) :=
  let helper := @depthFirst.branch_step.{u, v, w} o
  let rec go {m : Type (max u v) → Type w} [Applicative m]
             {N : Type u} {N' : Type (max u v)} {L : Type v} {L' : Type (max u v)}
             (f : N → m N') (g : L → m L') : Tree' N L → m (Tree' N' L')
    | leaf x => leaf <$> g x
    | branch y l r => inline (@helper m _ N' L' (fun _ => f y) (fun _ => go f g l) (fun _ => go f g r))
  @go

variable {m : Type (max u v) → Type w} [Applicative m]
         {N : Type u} {N' : Type (max u v)} {L : Type v} {L' : Type (max u v)}
         (f : N → m N') (g : L → m L')

def traversePreorder (t) := inline (depthFirst VisitOrder.Node1st f g t)

def traverseInorder (t) := inline (depthFirst VisitOrder.Node2nd f g t)

def traversePostorder (t) := inline (depthFirst VisitOrder.Node3rd f g t)

@[simp]
lemma traversePreorder_leaf
  : ∀ x, traversePreorder f g (leaf x) = @leaf N' L' <$> g x := fun _ => rfl

@[simp]
lemma traversePreorder_branch : ∀ (a : N) (l r : Tree' N L),
    traversePreorder f g (branch a l r)
    = @branch N' L' <$> f a <*> traversePreorder f g l <*> traversePreorder f g r :=
  fun _ _ _ => rfl

@[simp]
lemma traverseInorder_leaf
  : ∀ x, traverseInorder f g (leaf x) = @leaf N' L' <$> g x := fun _ => rfl

@[simp]
lemma traverseInorder_branch : ∀ (y : N) (l r : Tree' N L),
    traverseInorder f g (branch y l r)
    = (fun l' y' r' => @branch N' L' y' l' r')
      <$> traverseInorder f g l <*> f y <*> traverseInorder f g r :=
  fun _ _ _ => rfl

@[simp]
lemma traversePostorder_leaf
  : ∀ x, traversePostorder f g (leaf x) = @leaf N' L' <$> g x := fun _ => rfl

@[simp]
lemma traversePostorder_branch : ∀ (y : N) (l r : Tree' N L),
    traversePostorder f g (branch y l r)
    = (fun l' r' y' => @branch N' L' y' l' r')
      <$> traversePostorder f g l <*> traversePostorder f g r <*> f y :=
  fun _ _ _ => rfl

end traversals

variable {N : Type v} {L : Type u}

def eraseLeafData : Tree' N L → Tree N
  | leaf _ => Tree.nil
  | branch y l r => Tree.node y (eraseLeafData l) (eraseLeafData r)

def fillLeavesDefault (L : Type u) [Inhabited L] : Tree N → Tree' N L
  | Tree.nil => Tree'.leaf default
  | Tree.node a l r => Tree'.branch a (fillLeavesDefault L l) (fillLeavesDefault L r)

open Std

private
def getLeaves' :=
  let rec go (acc : List L) : Tree' N L → List L
    | leaf x => x :: acc
    | branch _ l r => go (go acc r) l
  go []

@[implemented_by getLeaves']
def getLeaves : Tree' N L → List L
  | leaf x => [x]
  | branch _ l r => getLeaves l ++ getLeaves r

lemma getLeaves'_correct : @getLeaves' N L = @getLeaves N L := by
  funext t
  suffices : ∀ ls, Tree'.getLeaves'.go ls t = t.getLeaves ++ ls
  . exact Eq.trans (this []) (List.append_nil _)
  induction' t with _ _ _ _ ihₗ ihᵣ <;> intro ls
  . exact rfl
  . simp only [getLeaves, getLeaves'.go, ihₗ, ihᵣ, List.append_assoc]

@[simp]
def numNodes : Tree' N L → ℕ
  | leaf _ => 0
  | branch _ l r => l.numNodes + r.numNodes + 1

@[simp]
def numLeaves : Tree' N L → ℕ
  | leaf _ => 1
  | branch _ l r => l.numLeaves + r.numLeaves

@[simp]
def height : Tree' N L → ℕ
  | leaf _ => 0
  | branch _ l r => max l.height r.height + 1

theorem numLeaves_eq_numNodes_succ (x : Tree' N L) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

theorem getLeaves_length_eq_eraseLeafData_numLeaves (t : Tree' N L)
  : t.getLeaves.length = t.eraseLeafData.numLeaves := by
  induction t
  . exact rfl
  . refine Eq.trans (List.length_append _ _) (congr_arg₂ _ ?_ ?_)  <;> assumption

theorem numLeaves_pos (x : Tree' N L) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

theorem height_le_numNodes : ∀ x : Tree' N L, x.height ≤ x.numNodes
  | leaf _ => le_rfl
  | branch _ l r =>
    Nat.succ_le_succ
      (max_le (_root_.trans l.height_le_numNodes <| l.numNodes.le_add_right _)
        (_root_.trans r.height_le_numNodes <| r.numNodes.le_add_left _))

end Tree'
