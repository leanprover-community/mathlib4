/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Data.Tree.Defs
import Mathlib.Control.Fold
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Associated
import Mathlib.SetTheory.Tree.Basic

section ShouldBeMoved

lemma lt_iff_le_not_le' {α : Type*} [LE α]
    (h : ∀ (a b : α), a ≤ b → b ≤ a → a = b)
    (a b : α) : (a ≤ b ∧ a ≠ b) ↔ a ≤ b ∧ ¬b ≤ a :=
  and_congr_right $ fun h' => not_congr $
    Iff.intro (fun h'' => h'' ▸ h''.subst (motive := (. ≤ b)) h') (h a b h')

def PartialOrder.mk' {α : Type*} [LE α] (le_refl : ∀ a : α, a ≤ a)
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b) : PartialOrder α := {
  le_refl := le_refl, le_trans := le_trans, le_antisymm := le_antisymm,
  lt := fun a b => a ≤ b ∧ a ≠ b
  lt_iff_le_not_le := lt_iff_le_not_le' le_antisymm
}

end ShouldBeMoved

namespace Tree

universe u v w

variable (o : Tree.VisitOrder) {α : Type u} {β : Type v} {γ : Type w}

namespace VisitOrder

instance : FinEnum VisitOrder :=
  FinEnum.ofNodupList [Node1st, Node2nd, Node3rd]
                      (fun o => by cases o <;> simp only []) (by simp only [])

end VisitOrder

namespace Path

instance : Inhabited Path where default := Path.here
instance : EmptyCollection Path where emptyCollection := Path.here
instance : IsAssociative Path (· ++ ·) where assoc := append_assoc

lemma isPrefix_antisymm : ∀ {p q}, isPrefix p q → isPrefix q p → p = q := by
  intro p; induction p <;> intro q <;> cases q
  <;> simp only [isPrefix, forall_true_left, IsEmpty.forall_iff, left.injEq, right.injEq]
  <;> apply_assumption

instance : LE Path where le p q := ∃ r, q = p ++ r

lemma le_def (p q : Path) : p ≤ q ↔ ∃ r, q = p ++ r := Iff.rfl
lemma le_iff_isPrefix {p q} : p ≤ q ↔ isPrefix p q := (isPrefix_def p q).symm

instance : @DecidableRel Path (. ≤ .) :=
  fun _ _ => decidable_of_bool _ le_iff_isPrefix.symm

private def instMonoid : Monoid Path :=
  { one := Path.here, mul := (. ++ .),
    one_mul := here_append, mul_one := append_here, mul_assoc := append_assoc }

instance : PartialOrder Path :=
  PartialOrder.mk' (@dvd_refl _ instMonoid)
                   (@dvd_trans _ instMonoid.toSemigroup)
                   (by simp only [le_iff_isPrefix]; exact @isPrefix_antisymm)

lemma lt_def (p q : Path) : p < q ↔ p ≤ q ∧ p ≠ q := Iff.rfl
lemma lt_iff_isStrictPrefix {p q} : p < q ↔ isStrictPrefix p q :=
  Iff.trans (and_congr_left' le_iff_isPrefix) (isStrictPrefix_def p q).symm

instance : @DecidableRel Path (. < .) :=
  fun _ _ => decidable_of_bool _ lt_iff_isStrictPrefix.symm

@[simp] lemma left_le_left_iff_le {p q} : left p ≤ left q ↔ p ≤ q := by simp only [le_iff_isPrefix, isPrefix]
@[simp] lemma right_le_right_iff_le {p q} : right p ≤ right q ↔ p ≤ q := by simp only [le_iff_isPrefix, isPrefix]
@[simp] lemma not_left_le_right {p q} : ¬ (left p ≤ right q) := by simp only [le_iff_isPrefix, isPrefix]
@[simp] lemma not_right_le_left {p q} : ¬ (right p ≤ left q) := by simp only [le_iff_isPrefix, isPrefix]
@[simp] lemma not_left_le_here {p} : ¬ (left p ≤ here) := by simp only [le_iff_isPrefix, isPrefix]
@[simp] lemma not_right_le_here {p} : ¬ (right p ≤ here) := by simp only [le_iff_isPrefix, isPrefix]
@[simp] lemma left_lt_left_iff_lt {p q} : left p < left q ↔ p < q := by simp only [lt_iff_isStrictPrefix, isStrictPrefix]
@[simp] lemma right_lt_right_iff_lt {p q} : right p < right q ↔ p < q := by simp only [lt_iff_isStrictPrefix, isStrictPrefix]
@[simp] lemma not_left_lt_right {p q} : ¬ (left p < right q) := by simp only [lt_iff_isStrictPrefix, isStrictPrefix]
@[simp] lemma not_right_lt_left {p q} : ¬ (right p < left q) := by simp only [lt_iff_isStrictPrefix, isStrictPrefix]
@[simp] lemma not_lt_here {p} : ¬ (p < here) := by cases p <;> simp only [lt_iff_isStrictPrefix, isStrictPrefix]

lemma here_le {p} : here ≤ p := ⟨p, rfl⟩

instance : OrderBot Path := { bot := here, bot_le := @here_le }

lemma eq_here_of_le_here : ∀ {p}, p ≤ here → p = here := bot_unique

lemma le_here_iff_eq_here : ∀ {p}, p ≤ here ↔ p = here :=
  Iff.intro eq_here_of_le_here (fun h => h ▸ le_refl here)

lemma le_append_right (p q : Path) : p ≤ p ++ q := ⟨q, rfl⟩
lemma left_append_le_of_le p {q r : Path} : q ≤ r → p ++ q ≤ p ++ r
  | ⟨s, h⟩ => ⟨s, Eq.trans (congrArg _ h) $ Eq.symm $ append_assoc p q s⟩

instance : SemilatticeInf Path where
  inf := longestCommonPrefix
  inf_le_left := by simp only [le_iff_isPrefix, implies_true,
                               longestCommonPrefix_isPrefix_left]
  inf_le_right := by simp only [le_iff_isPrefix, implies_true,
                               longestCommonPrefix_isPrefix_right]
  le_inf := by simp_rw [le_iff_isPrefix]; exact @longestCommonPrefix_is_maximum

instance : WellFoundedLT Path where
  wf := WellFounded.mono (InvImage.wf length wellFounded_lt)
        $ fun _ _ h => isStrictPrefix_length_lt (lt_iff_isStrictPrefix.mp h)

instance : IsTree Path where
  toWellFoundedLT := inferInstance
  downset_trichot p q r := by
    simp_rw [lt_iff_isStrictPrefix]
    exact isStrictPrefix_trichot_of_common_extension

end Path

instance : GetElem (Tree α) Path α (fun t p => p.validFor t) where
  getElem t p h := (t.follow p).get (Eq.trans (followable_iff_validFor p t) h)

@[simp]
lemma follow_eq_getElem? (t : Tree α) (p : Path) : t.follow p = t[p]? :=
  by simp only [getElem?, ← followable_iff_validFor, getElem, Option.some_get,
                dite_eq_ite, eq_ite_iff, and_true, Bool.not_eq_true, and_self,
                ← Option.not_isSome_iff_eq_none, Bool.eq_false_or_eq_true]

@[simp] lemma getElem?_nil (p : Path) : (@nil α)[p]? = none := by cases p <;> rfl
@[simp] lemma getElem?_here {a : α} {l r} : (node a l r)[Path.here]? = a := rfl
@[simp] lemma getElem?_left {a : α} {l r} (p : Path) :
    (node a l r)[Path.left p]? = l[p]? := rfl
@[simp] lemma getElem?_right {a : α} {l r} (p : Path) :
    (node a l r)[Path.right p]? = r[p]? := rfl

@[simp] lemma getElem_here {a : α} {l r} : (node a l r)[Path.here] = a := rfl
@[simp] lemma getElem_left {a : α} {l r} (p : Path) (h : p.validFor l) :
    (node a l r)[Path.left p] = l[p] := rfl
@[simp] lemma getElem_right {a : α} {l r} (p : Path) (h : p.validFor r) :
    (node a l r)[Path.right p] = r[p] := rfl

@[simp]
lemma getElem?_map (f : α → β) (t : Tree α) (p : Path) :
    (Tree.map f t)[p]? = Option.map f t[p]? :=
  by rw [← follow_eq_getElem?, follow_naturality, follow_eq_getElem?]

@[simp]
lemma getElem_map (f : α → β) (t : Tree α) (p : Path) (h : p.validFor t) :
    (Tree.map f t)[p]'(validFor_map' f p t h) = f t[p] :=
  by simp only [getElem, follow_naturality]; rw [Option.get_map]

instance : Inhabited (Tree α) := ⟨nil⟩

@[simp] theorem default_def {α} : (default : Tree α) = nil := rfl

instance : Functor Tree where
  map := Tree.map

@[simp] theorem map_id : ∀ (t : Tree α), map id t = t
  | nil => rfl
  | node a l r => congr_arg₂ (node a) (map_id l) (map_id r)

@[simp] theorem map_map (g : β → γ) (f : α → β)
  : ∀ (t : Tree α), map g (map f t) = map (g ∘ f) t
  | nil => rfl
  | node a l r => congr_arg₂ (node (g (f a))) (map_map g f l) (map_map g f r)

instance : LawfulFunctor Tree where
  map_const := by intros; dsimp only [Functor.mapConst, Functor.map]
  id_map := map_id
  comp_map g f t := Eq.symm $ map_map f g t

@[simp]
theorem fmap_def {α β} {t : Tree α} (f : α → β) : f <$> t = t.map f := rfl

def depthFirstTraversable : Traversable Tree := ⟨depthFirst o⟩

@[simp]
theorem id_traverse (t : Tree α) : depthFirst o (m := Id) pure t = t := by
  dsimp only [depthFirst]
  induction' t with a l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

@[simp]
theorem comp_traverse {F G} [Applicative F] [Applicative G]
  [LawfulApplicative F] [LawfulApplicative G] {α β γ} (f : β → F γ) (g : α → G β)
  (t : Tree α) : depthFirst o (Functor.Comp.mk ∘ Functor.map f ∘ g) t
               = Functor.Comp.mk (depthFirst o f <$> depthFirst o g t) := by
  dsimp only [depthFirst]
  induction' t with a l r ihₗ ihᵣ
  . exact Eq.symm $ map_pure _ _
  . dsimp [depthFirst.go]
    rw [ihₗ, ihᵣ]
    generalize h1 : depthFirst.go (@depthFirst.branch_step o) f = e1
    generalize h2 : depthFirst.go (@depthFirst.branch_step o) g = e2
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h1 <;> subst h2
            <;> rw [map_seq, map_seq]
            <;> simp [functor_norm, Functor.Comp.instApplicativeComp,
                      Functor.Comp.map, Functor.Comp.seq, Functor.Comp.mk]
            <;> exact rfl

@[simp]
theorem traverse_eq_map_id (f : α → β) (t : Tree α)
  : depthFirst o (@pure Id _ β ∘ f) t = id.mk (map f t) := by
  dsimp only [depthFirst]
  induction' t with a l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

def depthFirstLawfulTraversable : @LawfulTraversable Tree (depthFirstTraversable o) := by
  letI := depthFirstTraversable o
  refine ⟨Tree.id_traverse o, Tree.comp_traverse o, Tree.traverse_eq_map_id o, ?_⟩
  intros F G _ _ _ _ η α β f t
  dsimp only [depthFirstTraversable, depthFirst]
  induction' t with a l r ihₗ ihᵣ <;> dsimp only [depthFirst.go]
  . rw [ApplicativeTransformation.preserves_pure']
  . generalize h : depthFirst.go (@depthFirst.branch_step o) f = e
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h
    <;> simp only [ApplicativeTransformation.preserves_seq, Function.comp_apply,
                   ApplicativeTransformation.preserves_map,
                   ApplicativeTransformation.app_eq_coe, ihₗ, ihᵣ]
    <;> exact rfl

@[inline]
def foldMap.branch_step {ω : Type u} [Mul ω] : ω → ω → ω → ω :=
  match o with
  | VisitOrder.Node1st => fun x y z => x * y * z
  | VisitOrder.Node2nd => fun x y z => y * x * z
  | VisitOrder.Node3rd => fun x y z => y * z * x

@[simp]
lemma foldMap_def {ω : Type u} [One ω] [Mul ω] (f : α → ω) (t : Tree α)
  : @Traversable.foldMap _ (depthFirstTraversable o) _ _ _ _ f t
    = Tree.rec (1 : ω) (fun a _ _ => foldMap.branch_step o (f a)) t := by
  induction' t with a l r ihₗ ihᵣ; exact rfl
  dsimp only []
  rw [← ihₗ, ← ihᵣ]
  cases o <;> exact rfl

@[inline]
def toList.branch_step {ω : Type u} [Append ω] : ω → ω → ω → ω :=
  match o with
  | VisitOrder.Node1st => fun x y z => x ++ y ++ z
  | VisitOrder.Node2nd => fun x y z => y ++ x ++ z
  | VisitOrder.Node3rd => fun x y z => y ++ z ++ x

@[simp]
lemma toList_def (t : Tree α)
  : @Traversable.toList _ _ (depthFirstTraversable o) t
  = Tree.rec [] (fun a _ _ => toList.branch_step o [a]) t := by
    rw [@Traversable.toList_spec _ _ (depthFirstTraversable o)
                                     (depthFirstLawfulTraversable o),
        Tree.foldMap_def]
    cases' t; exact rfl; cases o <;> exact rfl

lemma mem_toList_iff_exists_follow_eq (t : Tree α) (a : α) :
    a ∈ @Traversable.toList _ _ (depthFirstTraversable o) t
    ↔ ∃ p, t.follow p = some a := by
  induction' t with x l r ihₗ ihᵣ
  . simp only [toList_def, List.find?_nil, List.not_mem_nil, follow, exists_const]
  . rw [toList_def]; dsimp only [follow]; rw [← toList_def, ← toList_def]
    refine @Iff.trans _ (a = x ∨ (∃ p, follow p l = some a)
                               ∨ (∃ p, follow p r = some a)) _ ?_ ?_
    . rw [← ihₗ, ← ihᵣ]
      cases o
      <;> simp only [toList.branch_step, List.mem_append, List.mem_singleton]
      . rw [or_assoc]
      . rw [or_left_comm, or_assoc]
      . rw [or_comm]
    . constructor
      . rintro (h | ⟨p, h⟩ | ⟨p, h⟩)
        . exact ⟨Path.here, Eq.symm $ congrArg some h⟩
        . exact ⟨Path.left p, h⟩
        . exact ⟨Path.right p, h⟩
      . simp only [forall_exists_index]
        rintro (_ | p | p) h
        . exact Or.inl $ Eq.symm (Option.some_injective _ h)
        . exact Or.inr $ Or.inl ⟨p, h⟩
        . exact Or.inr $ Or.inr $ ⟨p, h⟩

end Tree

namespace Tree'

variable (o : Tree.VisitOrder) {N : Type _} {L : Type _}
  {N' : Type _} {L' : Type _} {N'' : Type _} {L'' : Type _}

instance [Inhabited L] : Inhabited (Tree' N L) := ⟨leaf default⟩

@[simp]
theorem default_def [Inhabited L] : (default : Tree' N L) = leaf default := rfl

instance : Bifunctor Tree' where
  bimap := Tree'.bimap

@[simp] theorem id_bimap : ∀ (t : Tree' N L), bimap id id t = t
  | leaf _ => rfl
  | branch y l r => congr_arg₂ (branch y) (id_bimap l) (id_bimap r)

@[simp] theorem bimap_bimap (f₁ : N → N') (f₂ : N' → N'') (g₁ : L → L') (g₂ : L' → L'')
  : ∀ (t : Tree' N L), bimap f₂ g₂ (bimap f₁ g₁ t) = bimap (f₂ ∘ f₁) (g₂ ∘ g₁) t
  | leaf _ => rfl
  | branch y l r => congr_arg₂ (branch (f₂ (f₁ y))) (bimap_bimap f₁ f₂ g₁ g₂ l)
                                                    (bimap_bimap f₁ f₂ g₁ g₂ r)

instance : LawfulBifunctor Tree' where
  id_bimap := id_bimap
  bimap_bimap := bimap_bimap

@[simp]
theorem bimap_def {t : Tree' N L} (f : N → N') (g : L → L')
  : bimap f g t = t.bimap f g := rfl

def depthFirstBitraversable : Bitraversable Tree' := ⟨depthFirst o⟩

@[simp]
theorem id_bitraverse (t : Tree' N L) : depthFirst o (m := Id) pure pure t = t := by
  dsimp only [depthFirst]
  induction' t with _ y l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

open Functor (Comp map)

@[simp]
theorem comp_bitraverse.{u, v, w}
  {F : Type (max v u) → Type (max v u)} {G : Type (max v u) → Type w}
  [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
  {N L N' L' N'' L''}
  (f₂ : N' → F N'') (f₁ : L' → F L'') (g₂ : N → G N') (g₁ : L → G L') (t : Tree' N L)
  : @depthFirst.{u, v, w} o (Comp G F) _ _ _ _ _ (Comp.mk ∘ map f₂ ∘ g₂) (Comp.mk ∘ map f₁ ∘ g₁) t
    = Comp.mk (@Functor.map G _ _ _ (depthFirst o f₂ f₁) (depthFirst o g₂ g₁ t)) := by
  dsimp only [depthFirst]
  induction' t with _ y l r ihₗ ihᵣ
  . dsimp only [depthFirst.branch_step, depthFirst.go, Function.comp_apply]
    rw [← comp_map, Comp.map_mk, ← comp_map]
    exact rfl
  . dsimp [depthFirst.go]
    rw [ihₗ, ihᵣ]
    generalize h1 : depthFirst.go (@depthFirst.branch_step.{max u v, max u v, max u v} o) f₂ f₁ = e1
    generalize h2 : depthFirst.go (@depthFirst.branch_step.{u, v, w} o) g₂ g₁ = e2
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h1 <;> subst h2
            <;> simp only [Comp.instApplicativeComp, Comp.map, Comp.mk,
                           Comp.seq, Functor.map_map, seq_map_assoc, map_seq]
            <;> exact rfl

@[simp]
theorem bitraverse_eq_bimap_id (f : N → N') (g : L → L') (t : Tree' N L)
  : depthFirst o (m := Id) (pure ∘ f) (pure ∘ g) t = pure (bimap f g t) := by
  dsimp only [depthFirst]
  induction' t with x y l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

def depthFirstLawfulTraversable.{u}
   : @LawfulBitraversable Tree' (depthFirstBitraversable.{u, u} o) := by
  letI := depthFirstBitraversable.{u, u} o
  refine ⟨Tree'.id_bitraverse.{u, u} o, Tree'.comp_bitraverse o,
          Tree'.bitraverse_eq_bimap_id o, ?_⟩

  intros F G _ _ _ _ η N L N' L' f g t
  dsimp only [depthFirstBitraversable, depthFirst]
  induction' t with x y l r ihₗ ihᵣ <;> dsimp only [depthFirst.go]
  . apply ApplicativeTransformation.preserves_map.{u, u, u}
  . generalize h : depthFirst.go.{u, u, u} (@depthFirst.branch_step.{u, u, u} o) f g = e1
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h
            <;> simp only [ApplicativeTransformation.preserves_seq, Function.comp_apply,
                          ApplicativeTransformation.preserves_map, inline,
                          ApplicativeTransformation.app_eq_coe, ihₗ, ihᵣ]
            <;> exact rfl

instance : Monad (Tree' N) :=
  { Bifunctor.functor with
    pure := leaf
    bind := Tree'.bind }

-- @[simp]
theorem fmap_def (f : L → L') (t : Tree' N L)
  : f <$> t = Tree'.mapLeaves f t := rfl

@[simp]
theorem leaf_bind (x : L) (f : L → Tree' N L') : (leaf x).bind f = f x := rfl

@[simp]
theorem branch_bind (y : N) (l r : Tree' N L) (f : L → Tree' N L')
  : (branch y l r).bind f = branch y (l.bind f) (r.bind f) := rfl

@[simp]
theorem bind_leaf_comp (f : L → L') : ∀ (t : Tree' N L), t.bind (leaf ∘ f) = f <$> t
  | leaf _ => rfl
  | branch y l r => congr_arg₂ (branch y) (bind_leaf_comp f l) (bind_leaf_comp f r)

@[simp]
theorem bind_assoc : ∀ (t : Tree' N L) (f : L → Tree' N L') (g : L' → Tree' N L''),
    (t.bind f).bind g = t.bind (fun x => (f x).bind g)
  | leaf _ => fun _ _ => rfl
  | branch y l r => fun f g => congr_arg₂ (branch y) (bind_assoc l f g) (bind_assoc r f g)

instance : LawfulMonad (Tree' N) :=
  { Bifunctor.lawfulFunctor with
    pure_bind := Tree'.leaf_bind
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
    pure_seq := fun f t => Tree'.leaf_bind f (· <$> t) }

end Tree'
