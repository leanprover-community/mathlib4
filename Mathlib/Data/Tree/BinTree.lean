/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki, Brendan Murphy
-/
import Std.Data.RBMap
import Mathlib.Data.DList.Defs
import Mathlib.Util.CompileInductive
import Mathlib.Data.FinEnum
import Mathlib.Data.Tree.BinAddr
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Fold
import Mathlib.Data.Finmap

#align_import data.tree from "leanprover-community/mathlib"@"ed989ff568099019c6533a4d94b27d852a5710d8"

section ShouldBeMoved

namespace Option

lemma isSome_bind_iff {α β} {f : α → Option β} : ∀ {o : Option α},
    (o.bind f).isSome ↔ ∃ (h : o.isSome), (f (o.get h)).isSome
  | some _ => Iff.symm (exists_prop_of_true rfl)
  | none => iff_of_false Bool.false_ne_true $ exists_prop_of_false Bool.false_ne_true

lemma isSome_bind_eq {α β} {f : α → Option β} {o : Option α} :
    (o.bind f).isSome = decide (∃ (h : o.isSome), (f (o.get h)).isSome) :=
  Eq.trans (Bool.decide_coe _).symm (Bool.decide_congr isSome_bind_iff)

end Option

end ShouldBeMoved

/-!
# Binary tree

Provides binary tree storage with data at both the leaves and nodes.
Data at nodes can be retrieved with O(lg n) comparisons.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `BinTree Unit Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making
a `BinTree Unit Unit` with children `a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

/-- A binary tree with values of one type stored in non-leaf nodes
and values of another in the leaves. -/
inductive BinTree.{u, v} (N : Type u) (L : Type v) : Type (max u v)
  | leaf : L → BinTree N L
  | branch : N → BinTree N L → BinTree N L → BinTree N L
  deriving DecidableEq, Repr

-- porting note: workaround for leanprover/lean4#2049
compile_inductive% BinTree

namespace BinTree

instance {L N} [Inhabited L] : Inhabited (BinTree N L) := ⟨leaf default⟩

universe u v w

variable {α : Type u} {β : Type v}

abbrev Leafless N := BinTree N Unit
abbrev Bare := Leafless Unit

@[match_pattern, simp, reducible]
def nil {N : Type v} : Leafless N := leaf ()

open Std (RBNode DList)
def ofRBNode : RBNode α → Leafless α
  | RBNode.nil => nil
  | RBNode.node _color l key r => branch key (ofRBNode l) (ofRBNode r)

def perfect (x : α) (y : β) : ℕ → BinTree α β
  | 0 => leaf y
  | n+1 => branch x (perfect x y n) (perfect x y n)

nonrec def Bare.perfect : ℕ → Bare := perfect () ()

-- Notation for making a node with `Unit` data
scoped infixr:65 " △ " => BinTree.branch ()

@[eliminator]
def recOnBare {motive : Bare → Sort*} (t : Bare) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
    -- Porting note: Old proof was `t.recOn base fun u => u.recOn ind` but
    -- structure eta makes it unnecessary (https://github.com/leanprover/lean4/issues/777).
    t.recOn (fun _ => base) fun _u => ind
#align tree.unit_rec_on BinTree.recOnBare

section getNodeAt?

def getNodeData : BinTree α β → α ⊕ β
  | leaf x => Sum.inr x
  | branch y _ _ => Sum.inl y

def getSubtreeAt? : BinTree α β → BinAddr → Option (BinTree α β)
  | leaf x => BinAddr.cases' (some (leaf x)) (fun _ => none) (fun _ => none)
  | branch y l r => BinAddr.cases' (some (branch y l r)) l.getSubtreeAt? r.getSubtreeAt?

@[reducible] def getNodeAt? (t : BinTree α β) (p : BinAddr) :=
  Option.map getNodeData (getSubtreeAt? t p)

section equations

lemma getSubtreeAt?_here_mem (t : BinTree α β) : t ∈ getSubtreeAt? t BinAddr.here :=
  by cases t <;> simp only [getSubtreeAt?, BinAddr.cases'_here, Option.mem_some_iff]

lemma getSubtreeAt?_here_eq (t : BinTree α β) : getSubtreeAt? t BinAddr.here = some t :=
  Option.mem_def.mp $ getSubtreeAt?_here_mem t

lemma getSubtreeAt?_leaf_left (x : β) (p : BinAddr) :
    getSubtreeAt? (@leaf α β x) (BinAddr.left p) = none :=
  BinAddr.cases'_left _ _ _ _

lemma getSubtreeAt?_leaf_right (x : β) (p : BinAddr) :
    getSubtreeAt? (@leaf α β x) (BinAddr.right p) = none :=
  BinAddr.cases'_right _ _ _ _

lemma getSubtreeAt?_leaf_eq_none (x : β) {p : BinAddr} :
    ¬ p.isHere? → getSubtreeAt? (@leaf α β x) p = none :=
  p.cases' (absurd BinAddr.isHere?_here) (fun _ _ => getSubtreeAt?_leaf_left _ _)
                                         (fun _ _ => getSubtreeAt?_leaf_right _ _)

lemma getSubtreeAt?_branch_left (y : α) (l r : BinTree α β) (p : BinAddr) :
    getSubtreeAt? (branch y l r) (BinAddr.left p) = getSubtreeAt? l p :=
  BinAddr.cases'_left _ _ _ _

lemma getSubtreeAt?_branch_right (y : α) (l r : BinTree α β) (p : BinAddr) :
    getSubtreeAt? (branch y l r) (BinAddr.right p) = getSubtreeAt? r p :=
  BinAddr.cases'_right _ _ _ _

lemma getNodeAt?_leaf_here_mem (x : β) :
    Sum.inr x ∈ getNodeAt? (@leaf α β x) BinAddr.here :=
  Option.mem_map_of_mem _ (getSubtreeAt?_here_mem (leaf x))

lemma getNodeAt?_leaf_here_eq (x : β) :
    getNodeAt? (@leaf α β x) BinAddr.here = some (Sum.inr x) :=
  Option.mem_def.mp $ getNodeAt?_leaf_here_mem x

lemma getNodeAt?_branch_here_mem (y : α) (l r : BinTree α β) :
    Sum.inl y ∈ getNodeAt? (branch y l r) BinAddr.here :=
  Option.mem_map_of_mem _ (getSubtreeAt?_here_mem (branch y l r))

lemma getNodeAt?_branch_here_eq (y : α) (l r : BinTree α β) :
    getNodeAt? (branch y l r) BinAddr.here = some (Sum.inl y) :=
  Option.mem_def.mp $ getNodeAt?_branch_here_mem y l r

lemma getNodeAt?_leaf_eq_none (x : β) {p : BinAddr} (h : ¬ p.isHere?) :
    getNodeAt? (@leaf α β x) p = none :=
  Option.map_eq_none'.mpr (getSubtreeAt?_leaf_eq_none x h)

lemma getNodeAt?_leaf_left (x : β) (p : BinAddr) :
    getNodeAt? (@leaf α β x) (BinAddr.left p) = none :=
  congrArg _ (getSubtreeAt?_leaf_left x p)

lemma getNodeAt?_leaf_right (x : β) (p : BinAddr) :
    getNodeAt? (@leaf α β x) (BinAddr.right p) = none :=
  congrArg _ (getSubtreeAt?_leaf_right x p)

lemma getNodeAt?_branch_left (y : α) (l r : BinTree α β) (p : BinAddr) :
    getNodeAt? (branch y l r) (BinAddr.left p) = getNodeAt? l p :=
  congrArg _ (getSubtreeAt?_branch_left y l r p)

lemma getNodeAt?_branch_right (y : α) (l r : BinTree α β) (p : BinAddr) :
    getNodeAt? (branch y l r) (BinAddr.right p) = getNodeAt? r p :=
  congrArg _ (getSubtreeAt?_branch_right y l r p)

lemma getSubtreeAt?_append (t : BinTree α β) (p q : BinAddr) :
    getSubtreeAt? t (p ++ q) = (getSubtreeAt? t p).bind (getSubtreeAt? . q) := by
  induction p generalizing t <;> cases t
  <;> simp only [BinAddr.left_append, BinAddr.right_append, BinAddr.here_append,
                 getSubtreeAt?_here_eq, getSubtreeAt?_branch_left,
                 getSubtreeAt?_branch_right, getSubtreeAt?_leaf_left,
                 getSubtreeAt?_leaf_right, Option.some_bind, Option.none_bind]
  <;> apply_assumption

end equations

section predicates

variable (t : BinTree α β) (p : BinAddr)

def hasNodeAt := ∃ n, n ∈ getNodeAt? t p
def hasLeafAt := ∃ b, Sum.inr b ∈ getNodeAt? t p
def hasInnerNodeAt := ∃ a, Sum.inl a ∈ getNodeAt? t p

lemma hasNodeAt_iff_getNodeAt?_isSome : hasNodeAt t p ↔ (getNodeAt? t p).isSome := by
  dsimp only [hasNodeAt]
  rcases getNodeAt? t p with ⟨⟩ | ⟨_⟩
  <;> simp only [Option.not_mem_none, Option.isSome_none, Option.isSome_some,
                 Option.mem_some_iff, exists_false, exists_eq']

lemma hasLeafAt_iff_getNodeAt?_getRight?_isSome :
    hasLeafAt t p ↔ ((getNodeAt? t p).bind Sum.getRight?).isSome := by
  dsimp only [hasLeafAt]
  rcases getNodeAt? t p with ⟨⟩ | ⟨_|_⟩
  <;> simp only [Option.none_bind, Option.some_bind, Option.isSome_none, exists_eq',
                 Option.not_mem_none, exists_false, Sum.isRight_inl, Sum.isRight_inr,
                 Sum.isSome_getRight?_iff_isRight, Option.mem_some_iff, Sum.inr.inj_iff]

lemma hasInnerNodeAt_iff_getNodeAt?_getLeft?_isSome :
    hasInnerNodeAt t p ↔ ((getNodeAt? t p).bind Sum.getLeft?).isSome := by
  dsimp only [hasInnerNodeAt]
  rcases getNodeAt? t p with ⟨⟩ | ⟨_|_⟩
  <;> simp only [Option.none_bind, Option.some_bind, Option.isSome_none, exists_eq',
                 Option.not_mem_none, exists_false, Sum.isLeft_inl, Sum.isLeft_inr,
                 Sum.isSome_getLeft?_iff_isLeft, Option.mem_some_iff, Sum.inl.inj_iff]

def getSubtreeAt {t : BinTree α β} {p} (h : hasNodeAt t p) : BinTree α β :=
  Option.get (getSubtreeAt? t p)
  $ Iff.mp (eq_iff_eq_cancel_right.mpr Option.isSome_map)
  $ Iff.mp (hasNodeAt_iff_getNodeAt?_isSome _ _) h

def getNodeAt {t : BinTree α β} {p} (h : hasNodeAt t p) : α ⊕ β :=
  Option.get (getNodeAt? t p)
  $ Iff.mp (hasNodeAt_iff_getNodeAt?_isSome _ _) h

def getLeafAt {t : BinTree α β} {p} (h : hasLeafAt t p) : β :=
  Option.get ((getNodeAt? t p).bind Sum.getRight?)
  $ Iff.mp (hasLeafAt_iff_getNodeAt?_getRight?_isSome _ _) h

def getInnerNodeAt {t : BinTree α β} {p} (h : hasInnerNodeAt t p) : α :=
  Option.get ((getNodeAt? t p).bind Sum.getLeft?)
  $ Iff.mp (hasInnerNodeAt_iff_getNodeAt?_getLeft?_isSome _ _) h

instance : Decidable (hasNodeAt t p) :=
  decidable_of_bool _ (hasNodeAt_iff_getNodeAt?_isSome t p).symm
instance : Decidable (hasLeafAt t p) :=
  decidable_of_bool _ (hasLeafAt_iff_getNodeAt?_getRight?_isSome t p).symm
instance : Decidable (hasInnerNodeAt t p) :=
  decidable_of_bool _ (hasInnerNodeAt_iff_getNodeAt?_getLeft?_isSome t p).symm

lemma hasNodeAt_here (t : BinTree α β) : hasNodeAt t BinAddr.here :=
  by rw [hasNodeAt_iff_getNodeAt?_isSome, getNodeAt?, Option.isSome_map,
         getSubtreeAt?_here_eq, Option.isSome_some]

lemma hasNodeAt_pushLeft (t : BinTree α β) (p : BinAddr) :
    hasNodeAt t p.pushLeft ↔ hasInnerNodeAt t p := by
  simp only [hasNodeAt_iff_getNodeAt?_isSome, getNodeAt?, getSubtreeAt?_append,
             Option.isSome_map, BinAddr.pushLeft_eq_append_left_here,
             hasInnerNodeAt_iff_getNodeAt?_getLeft?_isSome, Option.isSome_bind_iff]
  refine exists_congr ?_
  intro h; rw [Option.get_map h]
  cases (Option.get (getSubtreeAt? t p) h)
  <;> simp only [getSubtreeAt?_leaf_left, getSubtreeAt?_branch_left,
                 getSubtreeAt?_here_eq, getNodeData, Sum.getLeft?_inr,
                 Sum.getLeft?_inl, Option.isSome_some, Option.isSome_none]

lemma hasNodeAt_pushRight (t : BinTree α β) (p : BinAddr) :
    hasNodeAt t p.pushRight ↔ hasInnerNodeAt t p := by
  simp only [hasNodeAt_iff_getNodeAt?_isSome, getNodeAt?, getSubtreeAt?_append,
             Option.isSome_map, BinAddr.pushRight_eq_append_right_here,
             hasInnerNodeAt_iff_getNodeAt?_getLeft?_isSome, Option.isSome_bind_iff]
  refine exists_congr ?_
  intro h; rw [Option.get_map h]
  cases (Option.get (getSubtreeAt? t p) h)
  <;> simp only [getSubtreeAt?_leaf_right, getSubtreeAt?_branch_right,
                 getSubtreeAt?_here_eq, getNodeData, Sum.getLeft?_inr,
                 Sum.getLeft?_inl, Option.isSome_some, Option.isSome_none]

end predicates

lemma getNodeAt?_faithful ⦃t₁ t₂ : BinTree α β⦄
    (h : ∀ p, t₁.getNodeAt? p = t₂.getNodeAt? p) : t₁ = t₂ := by
  have {x y l r} : ¬ ∀ p, (@leaf α β x).getNodeAt? p = (branch y l r).getNodeAt? p
  . refine not_forall_of_exists_not ?_
    use BinAddr.left BinAddr.here
    cases' l
    <;> simp only [getNodeAt?_leaf_left, getNodeAt?_leaf_right, getNodeAt?_leaf_here_eq,
                   getNodeAt?_branch_left, getNodeAt?_branch_right, getNodeAt?_branch_here_eq]
    <;> exact not_false
  revert t₂ h; induction' t₁ <;> intro t₂ h <;> cases' t₂
  . specialize h BinAddr.here
    simp_rw [getNodeAt?_leaf_here_eq, Option.some_inj, Sum.inr.inj_iff] at h
    exact congrArg leaf h
  . exact absurd h this
  . exact absurd (Eq.symm ∘' h) this
  . refine congr (congrArg₂ _ ?_ ?_) ?_
    . specialize h BinAddr.here
      simp_rw [getNodeAt?_branch_here_eq, Option.some_inj, Sum.inl.inj_iff] at h
      exact h
    . apply_assumption
      intro p
      specialize h (BinAddr.left p)
      simp_rw [getNodeAt?_branch_left] at h
      exact h
    . apply_assumption
      intro p
      specialize h (BinAddr.right p)
      simp only [getNodeAt?_branch_right] at h
      exact h

def autoEval : BinTree (α → α → α) α → α
  | leaf a => a
  | branch f l r => f (autoEval l) (autoEval r)

@[simp] lemma autoEval_leaf {a : α} : autoEval (leaf a) = a := rfl
@[simp] lemma autoEval_branch {y : α → α → α} {l r} :
    @autoEval α (branch y l r) = y l.autoEval r.autoEval := rfl

section HigherOrderFunctions

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂
variable {N : Type u₁} {N' : Type u₂} {N'' : Type u₃}
         {L : Type v₁} {L' : Type v₂} {L'' : Type v₃}
         {ω : Type w₁} {ν : Type w₂} {σ : Type w}

-- in time it would be nice to swap this for a version with memoization
def cata (f : L → ω) (g : N → ω → ω → ω) : BinTree N L → ω
  | leaf x => f x
  | branch y l r => g y (cata f g l) (cata f g r)

def terminatesOn (f : σ → L ⊕ (N × σ × σ)) : σ → Prop := Acc isChild
  where isChild (s s₀ : σ) := s ∈ (f s₀).getRight?.map (Prod.fst ∘ Prod.snd)
                              ∨ s ∈ (f s₀).getRight?.map (Prod.snd ∘ Prod.snd)

def ana (f : σ → L ⊕ (N × σ × σ)) (s : σ) (h : terminatesOn f s) : BinTree N L :=
  h.rec $ fun s' _ self =>
  have Hₗ {y sₗ sᵣ} (h' : f s' = Sum.inr (y, sₗ, sᵣ)) :
      terminatesOn.isChild f sₗ s' := Or.inl (h'.substr rfl)
  have Hᵣ {y sₗ sᵣ} (h' : f s' = Sum.inr (y, sₗ, sᵣ)) :
      terminatesOn.isChild f sᵣ s' := Or.inr (h'.substr rfl)
  match f s', @Hₗ, @Hᵣ with
  | Sum.inl x, _, _ => leaf x
  | Sum.inr (y, sₗ, sᵣ), h1, h2 => branch y (self sₗ (h1 rfl)) (self sᵣ (h2 rfl))

def ana' (f : σ → L ⊕ (N × σ × σ)) (s : σ) : Part (BinTree N L) := ⟨_, ana f s⟩

@[inline] def bimap (f : N → N') (g : L → L') : BinTree N L → BinTree N' L' :=
  cata (leaf ∘ g) (branch ∘ f)

-- grafts a new tree onto each leaf
@[inline] def bind (t : BinTree N L) (f : L → BinTree N L') : BinTree N L' :=
  cata f branch t

-- I don't define this as in bimapIdx_asCata because
-- I'm not sure whether that would create a bunch of closures or not
def bimapIdx (f : BinAddr → N → N') (g : BinAddr → L → L') :
    BinTree N L → BinTree N' L' := go BinAddr.here
  where go (curr : BinAddr) : BinTree N L → BinTree N' L'
        | leaf x => leaf (g curr x)
        | branch y l r => branch (f curr y) (go curr.pushLeft l) (go curr.pushRight r)

instance : Bifunctor BinTree where
  bimap := bimap

instance {N : Type u} : Monad (BinTree N) :=
  { Bifunctor.functor with
    pure := leaf
    bind := bind }

section cataLemmas
variable {f : L → ω} {g : N → ω → ω → ω} {x y l r}

@[simp] lemma cata_leaf : cata f g (leaf x) = f x := rfl
@[simp] lemma cata_branch :
    cata f g (branch y l r) = g y (cata f g l) (cata f g r) := rfl

lemma cata_eq_autoEval_bimap (t : BinTree N L) :
    cata f g t = autoEval (bimap g f t) := by
  induction t with
  | leaf => simp only [bimap, cata_leaf, Function.comp_apply, autoEval_leaf]
  | branch => simp only [bimap, cata_branch, Function.comp_apply, autoEval_branch]; congr
end cataLemmas

section anaLemmas
variable {f : σ → L ⊕ (N × σ × σ)} {s : σ} {p : BinAddr}
         {x : L} {y : N} {l r : BinTree N L}

lemma ana_def (h : terminatesOn f s) : ana f s h = Part.get (ana' f s) h := rfl

lemma ana'_step : ana' f s = (f s).elim (Part.some ∘ leaf) (fun (y, s₁, s₂) =>
                               branch y <$> ana' f s₁ <*> ana' f s₂) := by
  apply Part.ext'
  . rw [ana']
    generalize h : f s = e
    rcases e with ⟨_⟩ | ⟨⟨y, s₁, s₂⟩⟩
    . dsimp only [terminatesOn, Sum.elim_inl, Function.comp_apply, Part.some]
      refine iff_true_intro $ Acc.intro _ (fun s' => Not.elim $ not_or.mpr ?_)
      simp only [terminatesOn.isChild, h, Sum.getRight?_inl, Option.map_none']
      exact ⟨Option.not_mem_none _, Option.not_mem_none _⟩
    . dsimp only [(. <$> .), Seq.seq, Sum.elim, Part.map, Part.bind, Part.assert]
      refine Iff.trans ?_ exists_prop.symm
      dsimp only [ana']
      constructor
      . refine imp_and.mpr ⟨(Acc.inv . (Or.inl ?_)), (Acc.inv . (Or.inr ?_))⟩
        <;> simp only [terminatesOn.isChild, h, Sum.getRight?_inr, Sum.getLeft?_inr,
                       Option.map_some', Option.map_none', Option.mem_some_iff]
        <;> rfl
      . intro ⟨h1, h2⟩
        constructor
        intro s'
        simp only [terminatesOn.isChild, h, Sum.getRight?_inr, Sum.getLeft?_inr,
                   Option.map_some', Option.map_none', Option.mem_some_iff, Function.comp_apply]
        rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> assumption
  . intro (h : terminatesOn f s) h'
    rw [← ana_def]
    generalize h'' : f s = e at h'
    rcases e with ⟨_⟩ | ⟨⟨y, s₁, s₂⟩⟩
    <;> dsimp only [(. <$> .), Seq.seq, Sum.elim, Part.map, Part.bind,
                    Part.assert, Function.comp_apply] at h' ⊢
    <;> cases h <;> dsimp only [ana] <;> split
    <;> simp only [h'', Sum.inl.inj_iff, Sum.inr.inj_iff,
                   Prod.mk.injEq, Sum.inl_ne_inr] at *
    . refine congrArg leaf (Eq.symm ?_); assumption
    . rw [← ana, ← ana, ← ana_def, ← ana_def]
      congr <;> refine Eq.symm ?_
      . apply And.left ?_; swap; assumption
      . apply And.left ?_; on_goal -1 => apply And.right ?_; on_goal -1 => assumption
      . apply And.right ?_; on_goal -1 => apply And.right ?_; on_goal -1 => assumption

lemma leaf_mem_ana'_iff : leaf x ∈ ana' f s ↔ x ∈ (f s).getLeft? := by
  rw [ana'_step]
  generalize f s = e
  cases e
  <;> simp only [Sum.elim, Sum.getLeft?, Function.comp_apply, Part.mem_some_iff,
                 Option.mem_some_iff, leaf.injEq, (. <$> .), Seq.seq, and_false,
                 Option.not_mem_none, Part.mem_map_iff, Part.mem_bind_iff,
                 exists_exists_and_eq_and, exists_false]
  exact eq_comm

lemma branch_mem_ana'_iff :
    branch y l r ∈ ana' f s
    ↔ y ∈ (f s).getRight?.map Prod.fst
    ∧ l ∈ ((f s).getRight? : Part (N ×σ × σ)).bind (ana' f ∘ Prod.fst ∘ Prod.snd)
    ∧ r ∈ ((f s).getRight? : Part (N ×σ × σ)).bind (ana' f ∘ Prod.snd ∘ Prod.snd) := by
  rw [ana'_step]
  generalize f s = e
  cases e
  <;> simp only [Sum.elim, Sum.getRight?, Function.comp_apply, Part.coe_none,
                 Part.mem_some_iff, Option.map_none', Part.bind_none, Seq.seq,
                 Option.not_mem_none, Part.not_mem_none, false_and, (. <$> .),
                 Option.map_some', Part.coe_some, Part.bind_some, branch.injEq,
                 Option.mem_some_iff, Part.mem_bind_iff, Part.mem_map_iff,
                 exists_exists_and_eq_and]
  conv_lhs => simp only [← exists_and_left, ← and_assoc, exists_eq_right]
  rw [and_comm]

def mem_ana'_ndrec {motive : (s : σ) → (t : BinTree N L) → Sort u}
                   (halt : {x : L} → {s : σ} → f s = Sum.inl x → motive s (leaf x))
                   (step : {y : N} → {l r : BinTree N L} → {s sₗ sᵣ : σ}
                           → f s = Sum.inr (y, sₗ, sᵣ) → l ∈ ana' f sₗ → r ∈ ana' f sᵣ
                           → motive sₗ l → motive sᵣ r → motive s (branch y l r))
                   {s : σ} : ∀ {t : BinTree N L}, t ∈ ana' f s → motive s t
  | leaf x, h => halt $ Sum.getLeft?_eq_some_iff.mp
                      $ Option.mem_def.mp $ leaf_mem_ana'_iff.mp h
  | branch y l r, h =>
    have ⟨h1, h2, h3⟩ := branch_mem_ana'_iff.mp h
    have h0 := Sum.isSome_getRight?_iff_isRight.mp
               $ Eq.trans Option.isSome_map.symm
               $ Option.isSome_iff_exists.mpr ⟨_, h1⟩
    have H : Sum.getRight? (f s) = some (Sum.getRight (f s) h0) :=
      Sum.getRight?_eq_some_iff.mpr $ Eq.symm $ Sum.inr_getRight _ h0
    let sₗ := (Sum.getRight (f s) h0).snd.fst
    let sᵣ := (Sum.getRight (f s) h0).snd.snd
    have h4 : f s = Sum.inr (y, sₗ, sᵣ) := by
      rw [H] at h1
      refine Eq.trans (Sum.inr_getRight _ h0).symm (congrArg Sum.inr ?_)
      refine Prod.ext (Option.some_injective _ h1) rfl
    have h5 : l ∈ ana' f sₗ := by rw [H, Part.coe_some, Part.bind_some] at h2; exact h2
    have h6 : r ∈ ana' f sᵣ := by rw [H, Part.coe_some, Part.bind_some] at h3; exact h3
    step h4 h5 h6 (mem_ana'_ndrec halt step h5) (mem_ana'_ndrec halt step h6)

def hypothetical_getNodeAt?_ana (f : σ → L ⊕ (N × σ × σ)) (s : σ) (p : BinAddr) :=
  p.rec' (motive := fun _ => σ → Option (N ⊕ L))
         (some ∘ Sum.swap ∘ Sum.map id Prod.fst ∘ f)
         (fun _ self s => (f s).elim (fun _ => none) (fun (_, s₁, _) => self s₁))
         (fun _ self s => (f s).elim (fun _ => none) (fun (_, _, s₂) => self s₂)) s

lemma getNodeAt?_ana'_le_hypothetical_getNodeAt?_ana :
    (ana' f s).bind (Part.ofOption $ getNodeAt? . p)
    ≤ hypothetical_getNodeAt?_ana f s p := by
  intro node h
  simp only [Part.mem_bind_iff, Part.mem_coe] at h ⊢
  obtain ⟨t, h1, h2⟩ := h
  revert node p; revert t s; apply mem_ana'_ndrec
  . intro x s h1 p node h2
    have : p.isHere? :=
      Decidable.not_imp_not.mp
        (Option.not_isSome_iff_eq_none.mpr ∘ getSubtreeAt?_leaf_eq_none x)
      $ Eq.trans Option.isSome_map.symm (Option.isSome_iff_exists.mpr ⟨_, h2⟩)
    induction this
    simp only [hypothetical_getNodeAt?_ana, BinAddr.rec'_here, Function.comp_apply,
               Option.mem_some_iff, h1, Sum.map_inl, Sum.swap_inl, id_eq]
    simp only [getNodeAt?_leaf_here_eq, Option.mem_some_iff] at h2
    exact h2
  . intros y l r s sₗ sᵣ h1 _ _ ihₗ ihᵣ p node h2
    cases p using BinAddr.cases' with
    | atHere =>
      simp only [hypothetical_getNodeAt?_ana, BinAddr.rec'_here, Function.comp_apply,
                 Option.mem_some_iff, h1, Sum.map_inr, Sum.swap_inr, id_eq]
      simp only [getNodeAt?_branch_here_eq, Option.mem_some_iff] at h2
      exact h2
    | goLeft =>
      rw [getNodeAt?_branch_left] at h2
      simp only [hypothetical_getNodeAt?_ana, BinAddr.rec'_left, h1]
      exact ihₗ node h2
    | goRight =>
      rw [getNodeAt?_branch_right] at h2
      simp only [hypothetical_getNodeAt?_ana, BinAddr.rec'_right, h1]
      exact ihᵣ node h2

lemma getNodeAt?_ana_eq_hypothetical_getNodeAt?_ana (h : terminatesOn f s) :
    getNodeAt? (ana f s h) p = hypothetical_getNodeAt?_ana f s p := by
  refine Eq.trans (Part.to_ofOption _).symm (Eq.trans ?_ (Part.to_ofOption _))
  congr 1
  apply Part.ext'
  . constructor
    . intro H
      refine Part.dom_iff_mem.mpr ⟨Part.get _ H, ?_⟩
      refine getNodeAt?_ana'_le_hypothetical_getNodeAt?_ana _ ?_
      refine Part.mem_bind (Part.get_mem ?_) (Part.get_mem H)
      exact h
    . simp only [Part.ofOption_dom, Option.isSome_map]
      generalize h' : ana f s h = t
      rw [ana_def, Part.get_eq_iff_mem] at h'; clear h; revert s t
      apply mem_ana'_ndrec
      . intros

        admit
      . intros

        admit
      -- induction p with
      -- | atHere =>
      --   simp only [hypothetical_getNodeAt?_ana, BinAddr.rec'_here, implies_true,
      --              getSubtreeAt?_here_eq, Function.comp_apply, Option.isSome_some]
      -- | goLeft p ih =>

      --   -- simp_rw (config:={singlePass:=true}) [ana_def, ana'_step]
      --   simp only [hypothetical_getNodeAt?_ana, BinAddr.rec'_left]

      --   admit
      -- | goRight =>
      --   admit
  . intro h1 h2
    refine Part.mem_unique ?_ (Part.get_mem _)
    refine getNodeAt?_ana'_le_hypothetical_getNodeAt?_ana _ ?_
    rw [Part.bind, Part.assert_pos]
    exact Part.get_mem _

end anaLemmas

section bimapLemmas
variable {f : N → N'} {g : L → L'} {x y l r} {t : BinTree N L}
@[simp] lemma bimap_leaf : bimap f g (leaf x) = leaf (g x) := cata_leaf
@[simp] lemma bimap_branch :
    bimap f g (branch y l r) = branch (f y) (bimap f g l) (bimap f g r) := cata_branch
lemma bimap_asCata : bimap f g = cata (leaf ∘ g) (branch ∘ f) := rfl
lemma bimap_asCata' : bimap f g t = cata (leaf ∘ g) (branch ∘ f) t := rfl

protected def bimap_asAna'.go (f : N → N') (g : L → L') (x : { p // hasNodeAt t p }) :
    L' ⊕ N' × { p // hasNodeAt t p } × { p // hasNodeAt t p } :=
  let y := getNodeAt x.property
  if h : y.isRight
  then Sum.inl (g (Sum.getRight y h))
  else have H : hasInnerNodeAt t x.val :=
        (hasInnerNodeAt_iff_getNodeAt?_getLeft?_isSome _ _).mpr
        $ Option.isSome_bind_iff.mpr ⟨_, Sum.isSome_getLeft?_iff_isLeft.mpr
                                         $ Sum.not_isRight.mp h⟩
       Sum.inr (f (Sum.getLeft y (Sum.not_isRight.mp h)),
                ⟨BinAddr.pushLeft x.val, (hasNodeAt_pushLeft _ _).mpr H⟩,
                ⟨BinAddr.pushRight x.val, (hasNodeAt_pushRight _ _).mpr H⟩)

private lemma bimap_asAna'.go_total :
    ∀ (x : { p // hasNodeAt t p }), terminatesOn (bimap_asAna'.go f g) x := by
  rintro ⟨p, h⟩
  -- have := BinAddr.reverse_reverse p
  -- generalize BinAddr.reverse p = p' at this
  -- induction p'
  -- . admit
  -- . admit

  -- have : IsWellFounded BinAddr (. < . : BinAddr → BinAddr → Prop) := inferInstance

-- #print bimap_asAna'.go_total
  -- rw [hasNodeAt_iff_getNodeAt?_isSome, getNodeAt?,
  --     eq_iff_eq_cancel_right.mpr Option.isSome_map,
  --     Option.isSome_iff_exists] at h
  -- obtain ⟨t', h⟩ := h
  -- induction t' generalizing p t with
  -- | leaf =>
  --   admit
    -- cases p with
    -- | atHere =>

    --   admit
    -- | goLeft => admit
    -- | goRight => admit
    -- rw [getSubtreeAt?_here_eq] at h

    -- admit
  -- | branch => admit

lemma bimap_asAna' :
    bimap f g t ∈ ana' (bimap_asAna'.go f g) ⟨BinAddr.here, hasNodeAt_here t⟩ := by
  rw [show bimap f g t = getSubtreeAt (hasNodeAt_here (bimap f g t))
      from Option.mem_unique (getSubtreeAt?_here_mem _) (Option.get_mem _)]
  dsimp [ana', Part.mem_eq]
  use ?_; swap
  . refine Function.app (Subtype.forall.mpr (BinAddr.rec' ?_ ?_ ?_)) _
    .
      admit
    . admit
    . admit
  .
    admit

abbrev mapLeaves := bimap (id : N → N) g
abbrev mapNodes := bimap f (id : L → L)

@[simp] theorem bimap_id_id (t : BinTree α β) : bimap id id t = t := by
  induction t with
  | leaf => exact bimap_leaf
  | branch => rw [bimap_branch]; congr

@[simp] theorem bimap_bimap (f₁ : N → N') (f₂ : N' → N'') (g₁ : L → L')
    (g₂ : L' → L'') (t : BinTree N L) :
    bimap f₂ g₂ (bimap f₁ g₁ t) = bimap (f₂ ∘ f₁) (g₂ ∘ g₁) t := by
  induction t with
  | leaf => exact bimap_leaf
  | branch => (repeat rw [bimap_branch]); congr

end bimapLemmas

section bindLemmas
variable {f : L → BinTree N L'} {x y l r t}
@[simp] lemma bind_leaf : bind (leaf x) f = f x := cata_leaf
@[simp] lemma bind_branch :
    bind (branch y l r) f = branch y (bind l f) (bind r f) := cata_branch
lemma bind_asCata : (bind . f) = cata f branch := rfl
lemma bind_asCata' : bind t f = cata f branch t := rfl

end bindLemmas

section bimapLemmas

-- lemma bimapIdx_asMap

-- lemma bimapIdx_asCata' (f : BinAddr → N → N') (g : BinAddr → L → L')
--     (t : BinTree N L) :
--     bimapIdx f g t = cata (fun x p => leaf (g p x) : L → BinAddr → BinTree N' L')
--                           (fun y goL goR p => branch (f p y) (goL p.pushLeft)
--                                                              (goR p.pushRight))
--                           t BinAddr.here := by
--   dsimp only [bimapIdx]
--   rw [← BinAddr.reverse_here]
--   simp only [BinAddr.pushLeft_eq_append_left_here,
--              BinAddr.pushRight_eq_append_right_here]
--   generalize BinAddr.here = curr
--   induction t generalizing curr with
--   | leaf => rw [bimapIdx.go, cata_leaf]
--   | branch _ _ _ ihₗ ihᵣ  =>
--     rw [bimapIdx.go, cata_branch]
--     refine congrArg₂ _ ?_ ?_
--     .
--       admit
--       -- rw [ihₗ]

--       -- simp only [BinAddr.pushLeft_eq_append_left_here, ← BinAddr.reverse_left, ihₗ]


--       -- rw [BinAddr.pushLeft_eq_append_left_here]

--       -- apply_assumption
--       admit
--     .
--       admit

def bimapIdx_alt (f : BinAddr → N → N') (g : BinAddr → L → L') (t : BinTree N L) : BinTree N' L' :=
  cata (fun x p => leaf (g p x) : L → BinAddr → BinTree N' L')
       (fun y goL goR p => branch (f p y) (goL p.pushLeft) (goR p.pushRight))
       t BinAddr.here

end bimapLemmas

end HigherOrderFunctions

section bifunctor

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {N : Type u₁} {N' : Type u₂} {N'' : Type u₃}
         {L : Type v₁} {L' : Type v₂} {L'' : Type v₃}

instance : LawfulBifunctor BinTree where
  id_bimap := bimap_id_id
  bimap_bimap := bimap_bimap

@[simp]
theorem bimap_def {t : BinTree N L} {f : N → N'} {g : L → L'}
  : bimap f g t = t.bimap f g := rfl

@[simp]
theorem leaf_bind (x : L) (f : L → BinTree N L') : (leaf x).bind f = f x := rfl

@[simp]
theorem branch_bind (y : N) (l r : BinTree N L) (f : L → BinTree N L')
  : (branch y l r).bind f = branch y (l.bind f) (r.bind f) := rfl

@[simp]
theorem bind_leaf_comp {L' : Type v₁} (f : L → L') :
    ∀ (t : BinTree N L), t.bind (leaf ∘ f) = f <$> t
  | leaf _ => rfl
  | branch y l r => congr_arg₂ (branch y) (bind_leaf_comp f l) (bind_leaf_comp f r)

@[simp]
theorem bind_assoc : ∀ (t : BinTree N L) (f : L → BinTree N L') (g : L' → BinTree N L''),
    (t.bind f).bind g = t.bind (fun x => (f x).bind g)
  | leaf _ => fun _ _ => rfl
  | branch y l r => fun f g => congr_arg₂ (branch y) (bind_assoc l f g) (bind_assoc r f g)

instance {N : Type u} : LawfulMonad (BinTree N) :=
  { Bifunctor.lawfulFunctor with
    pure_bind := leaf_bind
    bind_pure_comp := bind_leaf_comp
    bind_map := fun _ _ => rfl
    bind_assoc := bind_assoc
    -- doesn't use anything specific to Trees
    -- but it can't be implemented as a default :/
    seqLeft_eq := by
      intros L L' t s
      dsimp [SeqLeft.seqLeft, Seq.seq]
      rw [← bind_leaf_comp, bind_assoc]
      refine congrArg _ $ funext $ fun x => ?_
      exact Eq.trans (bind_leaf_comp (Function.const _ x) s)
                     (Eq.symm (leaf_bind _ _))
    seqRight_eq := by
      intros L L' t s
      dsimp [SeqRight.seqRight, Seq.seq]
      rw [← bind_leaf_comp, bind_assoc]
      refine congrArg _ $ funext $ fun x => ?_
      refine Eq.trans (Eq.symm (id_map s)) (Eq.symm (leaf_bind _ _))
    pure_seq := fun f t => leaf_bind f (· <$> t) }

def labelWithIndex : BinTree N L → BinTree (BinAddr × N) (BinAddr × L) :=
  bimapIdx Prod.mk Prod.mk

lemma bimapIdx_eq_bimap_uncurry_labelWithIndex
    (f : BinAddr → N → N') (g : BinAddr → L → L') (t : BinTree N L) :
    bimapIdx f g t = bimap f.uncurry g.uncurry t.labelWithIndex := by
  dsimp only [labelWithIndex, bimapIdx]
  generalize BinAddr.here = curr
  induction t generalizing curr with
  | leaf _ => rfl
  | branch y l r ihₗ ihᵣ => exact congrArg₂ (branch (f curr y)) (ihₗ _) (ihᵣ _)

lemma bimap_eq_bimapIdx_const (f : N → N') (g : L → L') (t : BinTree N L) :
    bimap f g t = bimapIdx (Function.const BinAddr f) (Function.const BinAddr g) t := by
  dsimp only [labelWithIndex, bimapIdx]
  generalize BinAddr.here = curr
  induction t generalizing curr with
  | leaf _ => rfl
  | branch y l r ihₗ ihᵣ => exact congrArg₂ (branch (f y)) (ihₗ _) (ihᵣ _)

end bifunctor

/-
Implementation of bitraversable for BinTree
Less useful than it seems since it forces stuff to be universe-monomorphic
Commented out until I figure out what to do with it
-/

-- section traversals

-- inductive VisitOrder | Node1st | Node2nd | Node3rd
--   deriving DecidableEq, Repr, Ord

-- open BinTree (VisitOrder)

-- universe u₁ u₂ v₁ v₂

-- variable {m : Type (max u v) → Type w} [Applicative m]
--          {N : Type u} {N' : Type (max u v)} {L : Type v} {L' : Type (max u v)}

-- -- really what's going on here is that for any `σ ∈ S_n` and applicative `m` there is an operation
-- -- liftA σ : {α₁ … αₙ β : Type} → (f : α₁ → … → αₙ → β) → (x₁ : m α₁) → ⋯ (xₙ : m αₙ) → m β
-- -- liftA σ f x₁ … xₙ = (f ∘ σ) <$> x₁ <*> x₂ <*> … <*> xₙ
-- -- which sequences the input actions in the order determined by σ and then applies the function
-- @[macro_inline]
-- private def depthFirst.branch_step (o : VisitOrder)
--   (b : m N') (l : m (BinTree N' L')) (r : m (BinTree N' L')) : m (BinTree N' L') :=
--   match o with
--   | VisitOrder.Node1st => branch <$> b <*> l <*> r
--   | VisitOrder.Node2nd =>
--     (fun l' b' r' => branch b' l' r') <$> l <*> b <*> r
--   | VisitOrder.Node3rd =>
--     (fun l' r' b' => branch b' l' r') <$> l <*> r <*> b

-- -- recursively traverses the tree, visitng the left subtree before the right subtree
-- -- the parameter `o` determines whether the node is visited before, between, or after the subtrees
-- -- to traverse the right subtree before the left subtree use `SeqOpposite m`
-- def depthFirst (o : VisitOrder) :=
--   let rec go (f : N → m N') (g : L → m L') : BinTree N L → m (BinTree N' L')
--     | leaf x => leaf <$> g x
--     | branch y l r => depthFirst.branch_step.{u, v, w} o (f y) (go f g l) (go f g r)
--   @go

-- variable (f : N → m N') (g : L → m L')

-- def traversePreorder (t : BinTree N L) := depthFirst VisitOrder.Node1st f g t
-- def traverseInorder (t : BinTree N L) := depthFirst VisitOrder.Node2nd f g t
-- def traversePostorder (t : BinTree N L) := depthFirst VisitOrder.Node3rd f g t

-- @[simp]
-- lemma traversePreorder_leaf (x : L) :
--     traversePreorder f g (leaf x) = leaf.{max u v, max u v} <$> g x := rfl

-- @[simp]
-- lemma traversePreorder_branch (a : N) (l r : BinTree N L) :
--     traversePreorder f g (branch a l r)
--     = branch.{max u v, max u v}
--       <$> f a <*> traversePreorder f g l <*> traversePreorder f g r := rfl

-- @[simp]
-- lemma traverseInorder_leaf (x : L) :
--     traverseInorder f g (leaf x) = leaf.{max u v, max u v} <$> g x := rfl

-- @[simp]
-- lemma traverseInorder_branch (y : N) (l r : BinTree N L) :
--     traverseInorder f g (branch y l r)
--     = (fun l' y' r' => branch.{max u v, max u v} y' l' r')
--       <$> traverseInorder f g l <*> f y <*> traverseInorder f g r := rfl

-- @[simp]
-- lemma traversePostorder_leaf (x : L) :
--     traversePostorder f g (leaf x) = leaf.{max u v, max u v} <$> g x := rfl

-- @[simp]
-- lemma traversePostorder_branch (y : N) (l r : BinTree N L) :
--     traversePostorder f g (branch y l r)
--     = (fun l' r' y' => branch.{max u v, max u v} y' l' r')
--       <$> traversePostorder f g l <*> traversePostorder f g r <*> f y := rfl

-- variable (o : VisitOrder)

-- def depthFirstBitraversable : Bitraversable BinTree := ⟨depthFirst.{u, u} o⟩

-- @[simp]
-- theorem id_bitraverse {N L : Type u} (t : BinTree N L) :
--     depthFirst.{u, u} o (m := Id) pure pure t = t := by
--   dsimp only [depthFirst]
--   induction' t with _ y l r ihₗ ihᵣ; exact rfl
--   dsimp [depthFirst.go]
--   rw [ihₗ, ihᵣ]
--   cases o <;> exact rfl

-- open Functor (Comp map)

-- @[simp]
-- theorem comp_bitraverse
--   {F : Type (max v u) → Type (max v u)} {G : Type (max v u) → Type w}
--   [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
--   {N L N' L' N'' L''}
--   (f₂ : N' → F N'') (f₁ : L' → F L'') (g₂ : N → G N') (g₁ : L → G L') (t : BinTree N L)
--   : @depthFirst.{u, v, w} (Comp G F) _ _ _ _ _ o (Comp.mk ∘ map f₂ ∘ g₂) (Comp.mk ∘ map f₁ ∘ g₁) t
--     = Comp.mk (@Functor.map G _ _ _ (depthFirst o f₂ f₁) (depthFirst o g₂ g₁ t)) := by
--   dsimp only [depthFirst]
--   induction' t with _ y l r ihₗ ihᵣ
--   . dsimp only [depthFirst.branch_step, depthFirst.go, Function.comp_apply]
--     rw [← comp_map, Comp.map_mk, ← comp_map]
--     exact rfl
--   . dsimp [depthFirst.go]
--     rw [ihₗ, ihᵣ]
--     generalize h1 : depthFirst.go o f₂ f₁ = e1
--     generalize h2 : depthFirst.go o g₂ g₁ = e2
--     cases o <;> dsimp only [depthFirst.branch_step] <;> subst h1 <;> subst h2
--             <;> simp only [Comp.instApplicativeComp, Comp.map, Comp.mk,
--                            Comp.seq, Functor.map_map, seq_map_assoc, map_seq]
--             <;> exact rfl

-- @[simp]
-- theorem bitraverse_eq_bimap_id (f : N → N') (g : L → L') (t : BinTree N L) :
--     depthFirst o (m := Id) (pure ∘ f) (pure ∘ g) t = pure (bimap f g t) := by
--   dsimp only [depthFirst]
--   induction' t with x y l r ihₗ ihᵣ; exact rfl
--   dsimp [depthFirst.go]
--   rw [ihₗ, ihᵣ]
--   cases o <;> exact rfl

-- def depthFirstLawfulBitraversable :
--     @LawfulBitraversable BinTree (depthFirstBitraversable o) := by
--   letI := depthFirstBitraversable o
--   refine ⟨BinTree.id_bitraverse o, BinTree.comp_bitraverse o,
--           BinTree.bitraverse_eq_bimap_id o, ?_⟩
--   intros F G _ _ _ _ η N L N' L' f g t
--   dsimp only [depthFirstBitraversable, depthFirst]
--   induction' t with x y l r ihₗ ihᵣ <;> dsimp only [depthFirst.go]
--   . apply ApplicativeTransformation.preserves_map
--   . generalize h : depthFirst.go o f g = e1
--     cases o <;> dsimp only [depthFirst.branch_step] <;> subst h
--             <;> simp only [ApplicativeTransformation.preserves_seq, Function.comp_apply,
--                           ApplicativeTransformation.preserves_map, inline,
--                           ApplicativeTransformation.app_eq_coe, ihₗ, ihᵣ]

-- -- def depthFirstTraversable_leaves (N : Type u) : Traversable (BinTree.{u, max u v} N) :=
-- --   { Bifunctor.functor with
-- --     traverse := fun {m _ L L'} => @depthFirst m _ N (ULift.{v} N) L L' o pure }

-- -- #print depthFirstTraversable_leaves

-- end traversals

/-
It would be great if we could use existing code like Traversable.length
But that enforces a constraint that N and L live in the same universe
Does this constraint matter? /shrug
-/

open Functor

section folds

variable {ω : Type w} [Mul ω] [One ω] [Add ω] [Zero ω]
         (op : ω → ω → ω) (f : α → ω) (g : β → ω)

def fold : BinTree ω ω → ω
  | leaf x => x
  | branch y l r => op (fold r) (op (fold l) y)

-- slightly more general than if we used traversePostorder
-- since we don't need a base case
-- traverses post-order
-- we could implement this with an accumulator and make one call tail recursive
-- but it would have to be left or right biased
def foldBimap' : BinTree α β → ω
  | leaf x => g x
  | branch y l r => op (foldBimap' r) (op (foldBimap' l) (f y))

lemma homomorphism_fold_eq_foldBimap' {ω' : Type*} {op' : ω' → ω' → ω'}
    {f : ω → ω'} (H : ∀ x y, f (op x y) = op' (f x) (f y)) {t : BinTree ω ω} :
    f (fold op t) = foldBimap' op' f f t := by
  induction t
  . rfl
  . simp only [fold, foldBimap', H]; congr

lemma foldBimap'_eq_fold_bimap (t : BinTree α β) :
    foldBimap' op f g t = fold op (bimap f g t) := by
  induction t
  . rfl
  . refine congrArg₂ (op . $ op . $ f _) ?_ ?_ <;> apply_assumption

lemma foldBimap'_bimap.{u', v'} {α' : Type u'} {β' : Type v'}
    (f' : α' → α) (g' : β' → β) (t : BinTree α' β') :
    foldBimap' op f g (bimap f' g' t) = foldBimap' op (f ∘ f') (g ∘ g') t :=
  by rw [foldBimap'_eq_fold_bimap, bimap_bimap, ← foldBimap'_eq_fold_bimap]

lemma homomorphism_foldBimap'_eq_foldBimap'_comp {ω' : Type*} (op' : ω' → ω' → ω')
    (p : ω → ω') (H : ∀ x y, p (op x y) = op' (p x) (p y)) (t : BinTree α β) :
    p (foldBimap' op f g t) = foldBimap' op' (p ∘ f) (p ∘ g) t := by
  rw [foldBimap'_eq_fold_bimap, homomorphism_fold_eq_foldBimap' op H,
      foldBimap'_bimap]

def foldBimap'Idx (f : BinAddr → α → ω) (g : BinAddr → β → ω) :
    BinTree α β → ω := go BinAddr.here
  where go (curr : BinAddr) : BinTree α β → ω
        | leaf x => g curr x
        | branch y l r => op (go curr.pushRight r) (op (go curr.pushLeft l) (f curr y))

@[simp]
lemma foldBimap'_leaf {ω : Type w} (op : ω → ω → ω) (f : α → ω) (g : β → ω)
    (x : β) : foldBimap' op f g (leaf x) = g x := rfl

@[simp]
lemma foldBimap'_branch {ω : Type w} (op : ω → ω → ω) (f : α → ω) (g : β → ω)
    (y : α) (l r : BinTree α β) :
    foldBimap' op f g (branch y l r)
    = op (foldBimap' op f g r) (op (foldBimap' op f g l) (f y)) := rfl

@[simp] def foldBimap := foldBimap' (. * .) f g
@[simp] def foldAddBimap := foldBimap' (. + .) f g
@[simp] def foldMapLeaves := foldBimap (Function.const α 1) g
@[simp] def foldMapInnerNodes := foldBimap f (Function.const β 1)
@[simp] def foldAddMapLeaves := foldAddBimap (Function.const α 0) g
@[simp] def foldAddMapInnerNodes := foldAddBimap f (Function.const β 0)

/-
TODO: Implement memoized versions of these using "evalPtrCache" as in
"Sealing Pointer-Based Optimizations Behind Pure Functions"
-/

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
abbrev numInnerNodes : BinTree α β → ℕ := foldAddMapInnerNodes (fun _ => 1)

/-- The number of leaves of a binary tree -/
abbrev numLeaves : BinTree α β → ℕ := foldAddMapLeaves (fun _ => 1)

-- not a foldMap
/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
def height : BinTree α β → ℕ
  | leaf _ => 0
  | branch _ l r => max l.height r.height + 1

def flatten (t : BinTree α β) : List (α ⊕ β) :=
  DList.toList $ t.foldBimap' (. ++ .) (DList.singleton ∘ Sum.inl)
                                       (DList.singleton ∘ Sum.inr)

lemma flatten_asList (t : BinTree α β) :
    flatten t = t.foldBimap' (. ++ .) (fun y => [Sum.inl y]) (fun x => [Sum.inr x]) := by
  rw [flatten, foldBimap'_eq_fold_bimap]
  refine Eq.trans (homomorphism_fold_eq_foldBimap' _ DList.toList_append) ?_
  exact foldBimap'_bimap _ _ _ _ _ _

-- true by rfl, but better to avoid relying on def-eqs
@[simp] lemma flatten_leaf {x : β} : flatten (@leaf α β x) = [Sum.inr x] :=
  Eq.trans (flatten_asList _) (foldBimap'_leaf _ _ _ _)

@[simp] lemma flatten_branch {y : α} {l r : BinTree α β} :
    flatten (branch y l r) = flatten r ++ flatten l ++ [Sum.inl y] :=
  by simp only [flatten_asList, foldBimap'_branch, List.append_assoc]

end folds

section

universe u₁ u₂ v₁ v₂
variable {N : Type u₁} {N' : Type u₂} {L : Type v₁} {L' : Type v₂}

-- def foldl_flatten {ω : Type w} (op : ω → ω → ω) (b : ω) [IsAssociative ω op]
--     (t : BinTree ω ω) :
--     List.foldl (fun x => Sum.elim (op x) (op x)) b (flatten t) = op b (fold op t) := by
--   induction' t with _ _ _ _ ihₗ ihᵣ generalizing b
--     <;> simp only [fold, flatten_branch, flatten_leaf]
--   . simp only [List.foldl, Sum.elim_inr]
--   . simp only [List.foldl_append, Sum.elim_inl, List.foldl_cons, List.foldl_nil, ihₗ, ihᵣ]
--     exact Eq.trans (IsAssociative.assoc _ _ _) (IsAssociative.assoc _ _ _)

-- def foldr_flatten {ω : Type w} (op : ω → ω → ω) (b : ω) [IsAssociative ω op]
--     (t : BinTree ω ω) :
--     List.foldr (Sum.elim op op) b (flatten t) = op (fold op t) b := by
--   induction' t with _ _ _ _ ihₗ ihᵣ generalizing b
--     <;> simp only [fold, flatten_branch, flatten_leaf]
--   . simp only [List.foldr, Sum.elim_inr]
--   . simp only [List.foldr_append, Sum.elim_inl, List.foldr_cons, List.foldr_nil, ihₗ, ihᵣ]
--     refine Eq.trans (IsAssociative.assoc _ _ _).symm ?_
--     refine Eq.trans (IsAssociative.assoc _ _ _).symm ?_
--     exact congrArg (op . b) (IsAssociative.assoc _ _ _)

def getNodeAt?_bimapIdx (f : BinAddr → N → N') (g : BinAddr → L → L')
    (t : BinTree N L) (p : BinAddr) :
    (bimapIdx f g t).getNodeAt? p = Option.map (Sum.map (f p .) (g p .)) (t.getNodeAt? p) := by
  conv_rhs => left; simp (config:={singlePass:=true}) [← BinAddr.here_append]
  dsimp only [bimapIdx]
  generalize BinAddr.here = curr
  induction' t with _ _ _ _ ihₗ ihᵣ generalizing p curr
  <;> cases' p using BinAddr.cases'
  <;> simp only [bimapIdx.go, getNodeAt?, Option.map_some', Option.map_none', Sum.map_inr, Sum.map_inl,
                 BinAddr.cases'_here, BinAddr.cases'_left, BinAddr.cases'_right, BinAddr.append_here,
                 BinAddr.append_left_eq_pushLeft_append, BinAddr.append_right__eq_pushRight_append]
  <;> apply_assumption

-- could define a version of this for traverse too,
-- saying it's a traversable morphism
def getNodeAt?_bimap (f : N → N') (g : L → L') (t : BinTree N L) (p : BinAddr) :
    (bimap f g t).getNodeAt? p = Option.map (Sum.map f g) (t.getNodeAt? p) :=
  Eq.trans (congrArg (getNodeAt? . p) (bimap_eq_bimapIdx_const _ _ _))
           (getNodeAt?_bimapIdx _ _ _ _)

lemma bimapIdx_leaf {f : BinAddr → N → N'} {g : BinAddr → L → L'} {x : L} :
    bimapIdx f g (leaf x) = leaf (g BinAddr.here x) := rfl

lemma bimapIdx_branch {f : BinAddr → N → N'} {g : BinAddr → L → L'}
    {y : N} {l r : BinTree N L} :
    bimapIdx f g (branch y l r)
    = branch (f BinAddr.here y)
             (l.bimapIdx (f ∘ BinAddr.left) (g ∘ BinAddr.left))
             (r.bimapIdx (f ∘ BinAddr.right) (g ∘ BinAddr.right)) := by
  apply getNodeAt?_faithful
  intro p
  rw [getNodeAt?_bimapIdx]; dsimp only [getNodeAt?]
  cases' p using BinAddr.cases'
  . simp only [BinAddr.cases'_here, Option.map_some', Sum.map_inl]
  . simp only [BinAddr.cases'_left, getNodeAt?_bimapIdx]; rfl
  . simp only [BinAddr.cases'_right, getNodeAt?_bimapIdx]; rfl

lemma getNodeAt?_labelWithIndex (t : BinTree N L) (p : BinAddr) :
    getNodeAt? t.labelWithIndex p = Option.map (Sum.map (Prod.mk p) (Prod.mk p)) (t.getNodeAt? p) :=
  getNodeAt?_bimapIdx _ _ t p

lemma labelWithIndex_leaf {x} :
    labelWithIndex (@leaf N L x) = leaf (BinAddr.here, x) := bimapIdx_leaf

lemma labelWithIndex_branch {y : N} {l r : BinTree N L} :
    labelWithIndex (branch y l r)
    = branch (BinAddr.here, y)
             ((labelWithIndex l).bimap (Prod.map BinAddr.left  id)
                                       (Prod.map BinAddr.left  id))
             ((labelWithIndex r).bimap (Prod.map BinAddr.right id)
                                       (Prod.map BinAddr.right id)) := by
  rw [labelWithIndex, bimapIdx_branch, ← labelWithIndex]
  refine congrArg₂ _ ?_ ?_ <;> apply getNodeAt?_faithful <;> intro
  <;> simp only [getNodeAt?_bimapIdx, getNodeAt?_bimap, getNodeAt?_labelWithIndex,
                 Option.map_map, Sum.map_comp_map]
  <;> refine congrFun (congrArg Option.map (congrArg₂ Sum.map ?_ ?_)) _
  <;> funext <;> simp only [Function.comp_apply, Prod_map, id_eq]

-- lemma bimap_labelWithIndex (f : N → N') (g : L → L') (t : BinTree N L) :
--     labelWithIndex (bimap f g t)
--     = bimap (Prod.map id f) (Prod.map id g) (labelWithIndex t) := by
--   apply getNodeAt?_faithful
--   intro
--   simp only [getNodeAt?_labelWithIndex, getNodeAt?_bimap, Option.map_map]
--   admit

lemma foldBimap'Idx_eq_foldBimap'_uncurry_labelWithIndex {ω : Type w}
    (op : ω → ω → ω) (f : BinAddr → N → ω) (g : BinAddr → L → ω) (t : BinTree N L) :
    foldBimap'Idx op f g t = foldBimap' op f.uncurry g.uncurry t.labelWithIndex := by
  dsimp only [labelWithIndex, foldBimap'Idx, bimapIdx]
  generalize BinAddr.here = curr
  induction t generalizing curr with
  | leaf _ => rfl
  | branch y l r ihₗ ihᵣ => exact congrArg₂ (op . $ op . $ f curr y) (ihᵣ _) (ihₗ _)

lemma foldBimap'Idx_leaf {ω : Type w} {op : ω → ω → ω}
    {f : BinAddr → N → ω} {g : BinAddr → L → ω} {x} :
    foldBimap'Idx op f g (leaf x) = g BinAddr.here x := rfl

lemma foldBimap'Idx_branch {ω : Type w} {op : ω → ω → ω}
    {f : BinAddr → N → ω} {g : BinAddr → L → ω} {y : N} {l r : BinTree N L} :
    foldBimap'Idx op f g (branch y l r)
    = (op (r.foldBimap'Idx op (f ∘ BinAddr.right) (g ∘ BinAddr.right))
      $ op (l.foldBimap'Idx op (f ∘ BinAddr.left) (g ∘ BinAddr.left))
      $ f BinAddr.here y) := by
  simp only [foldBimap'Idx_eq_foldBimap'_uncurry_labelWithIndex, bimap, fold,
             foldBimap'_eq_fold_bimap, labelWithIndex_branch, bimap_bimap]
  rfl

lemma foldBimap'Idx_bimap.{u', v'} {α' : Type u'} {β' : Type v'} {ω : Type w}
    (op : ω → ω → ω) (f : BinAddr → α → ω) (g : BinAddr → β → ω)
    (f' : α' → α) (g' : β' → β) (t : BinTree α' β') :
    foldBimap'Idx op f g (bimap f' g' t)
    = foldBimap'Idx op (f . $ f' .) (g . $ g' .) t := by
  simp only [foldBimap'Idx_eq_foldBimap'_uncurry_labelWithIndex]

  -- have := @foldBimap'_bimap
  admit
  -- rw [foldBimap'_eq_fold_bimap, bimap_bimap, ← foldBimap'_eq_fold_bimap]

-- lemma homomorphism_foldBimap'Idx_eq_foldBimap'Idx_comp {ω' : Type*} (op' : ω' → ω' → ω')
--     (p : ω → ω') (H : ∀ x y, p (op x y) = op' (p x) (p y)) (t : BinTree α β) :
--     p (foldBimap' op f g t) = foldBimap' op' (p ∘ f) (p ∘ g) t := by
--   rw [foldBimap'_eq_fold_bimap, homomorphism_fold_eq_foldBimap' op H,
--       foldBimap'_bimap]

end

def flattenWithIndex (t : BinTree α β) : List (BinAddr × (α ⊕ β)) :=
  DList.toList
  $ t.foldBimap'Idx (. ++ .) (DList.singleton $ Prod.mk . $ Sum.inl .)
                             (DList.singleton $ Prod.mk . $ Sum.inr .)

lemma flattenWithIndex_asList (t : BinTree α β) :
    flattenWithIndex t = t.foldBimap'Idx (. ++ .) (fun p y => [(p, Sum.inl y)])
                                                  (fun p x => [(p, Sum.inr x)]) := by
  rw [flattenWithIndex, foldBimap'Idx_eq_foldBimap'_uncurry_labelWithIndex,
      foldBimap'_eq_fold_bimap]
  refine Eq.trans (homomorphism_fold_eq_foldBimap' _ _ _ DList.toList_append _) ?_
  simp only [foldBimap'_bimap, ← Function.uncurry_bicompr]
  unfold Function.bicompr
  simp only [DList.toList_singleton]
  exact Eq.symm (foldBimap'Idx_eq_foldBimap'_uncurry_labelWithIndex _ _ _ _)

@[simp] lemma flattenWithIndex_leaf {x : β} :
    flattenWithIndex (@leaf α β x) = [(BinAddr.here, Sum.inr x)] :=
  Eq.trans (flattenWithIndex_asList _) foldBimap'Idx_leaf

@[simp] lemma flattenWithIndex_branch {y : α} {l r : BinTree α β} :
    flattenWithIndex (branch y l r)
    = List.map (Prod.map BinAddr.right id) (flattenWithIndex r)
      ++ List.map (Prod.map BinAddr.left id) (flattenWithIndex l)
      ++ [(BinAddr.here, Sum.inl y)] := by
  simp only [flattenWithIndex_asList, foldBimap'Idx_branch, List.append_assoc]
  simp only [foldBimap'Idx_eq_foldBimap'_uncurry_labelWithIndex, foldBimap'_eq_fold_bimap,
             homomorphism_fold_eq_foldBimap' _ _ _ (List.map_append _),
             bimap_bimap]
  rfl

lemma flattenWithIndex_eq_flatten_labelWithIndex (t : BinTree α β) :
    flattenWithIndex t
    = List.map (Equiv.prodSumDistrib _ _ _).symm (flatten t.labelWithIndex) := by
  dsimp only [Equiv.coe_fn_mk, Equiv.symm]
  have : (Equiv.prodSumDistrib BinAddr α β).invFun
       = Sum.elim (Prod.map id Sum.inl) (Prod.map id Sum.inr)
  . ext (⟨_, _⟩ | ⟨_, _⟩) <;> rfl
  rw [this, flatten_asList, foldBimap'_eq_fold_bimap]

  admit

-- def toAList : BinTree α β → AList (Function.const BinAddr (α ⊕ β)) :=
--   foldBimap'Idx sorry sorry sorry

-- def toLookupTable (t : BinTree α β) : Finmap (Function.const BinAddr (α ⊕ β)) :=
--   sorry

end getNodeAt?

end BinTree
