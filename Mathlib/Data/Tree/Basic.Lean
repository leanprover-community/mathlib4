/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Control.Fold
import Mathlib.Data.Tree.Defs
import Mathlib.Data.Tree.Instances
import Mathlib.Control.Monad.MonadState
import Mathlib.Control.Monad.MonadLift
import Mathlib.Data.Set.Finite

namespace Tree

def perfect : ℕ → Tree Unit
  | 0 => nil
  | n+1 => perfect n △ perfect n

universe u v

variable {α : Type u} {β : Type v}

open MonadState renaming get → get'

lemma follow_faithful ⦃t₁ t₂ : Tree α⦄ (h : ∀ p, t₁.follow p = t₂.follow p)
    : t₁ = t₂ := by
  revert t₂ h; induction' t₁ with a₁ l₁ r₁ ihₗ ihᵣ <;> intro t₂ h
  . cases t₂; rfl
    exact absurd (Eq.symm (h Path.here)) (Option.some_ne_none _)
  . cases' t₂ with a₂ l₂ r₂; exact absurd (h Path.here) (Option.some_ne_none _)
    congr
    . exact Option.some_injective _ (h Path.here)
    . apply ihₗ; intro p; exact h (Path.left p)
    . apply ihᵣ; intro p; exact h (Path.right p)

@[ext]
def ext (t₁ t₂ : Tree α) (h : ∀ p : Path, t₁[p]? = t₂[p]?) : t₁ = t₂ :=
  by simp only [← follow_eq_getElem?] at h; exact follow_faithful h

private def labelWithIndex' : Tree α → Tree (α × Path) :=
  let rec go (acc : Path) : Tree α → Tree (α × Path)
    | nil => nil
    | node a l r =>
      node (a, acc.reverse) (go (Path.left acc) l) (go (Path.right acc) r)
  go Path.here

@[implemented_by labelWithIndex']
def labelWithIndex : Tree α → Tree (α × Path)
  | nil => nil
  | node a l r =>
    node (a, Path.here)
         (Tree.map (Prod.map id Path.left) $ labelWithIndex l)
         (Tree.map (Prod.map id Path.right) $ labelWithIndex r)

lemma labelWithIndex'_correct : @labelWithIndex' α = @labelWithIndex α := by
  dsimp [labelWithIndex']
  funext t
  suffices : ∀ (acc : Path),
    labelWithIndex'.go acc t = (labelWithIndex t).map (Prod.map id acc.appendRev)
  . rw [this]; exact Tree.map_id _
  induction' t with a l r ihₗ ihᵣ <;> intro acc
  . rfl
  . simp only [labelWithIndex'.go, ← Path.reverse'_correct, ihₗ, ihᵣ, id_eq,
               Prod.map, Tree.map, Tree.map_map]; rfl

-- this fully specifies the function due to `follow_faithful`
lemma labelWithIndex_spec (t : Tree α) (p : Path) :
    (labelWithIndex t)[p]? = t[p]?.map (fun a => (a, p)) := by
  revert t; induction' p with p ih p ih <;> intro t
  <;> cases' t with a l r
  <;> simp only [labelWithIndex, follow, Option.map_some', Option.map_none',
                 getElem?_map, getElem?_nil, getElem?_here, getElem?_left, getElem?_right]
  <;> rw [ih, Option.map_map] <;> rfl

lemma labelWithIndex_naturality {β : Type v} (f : α → β) :
    labelWithIndex ∘ Tree.map f = Tree.map (Prod.map f id) ∘ labelWithIndex := by
  ext t p : 2
  simp only [Function.comp_apply, labelWithIndex_spec, getElem?_map, Option.map_map]
  rfl

@[simp] lemma labelWithIndex_map {β : Type v} (f : α → β) : ∀ (t : Tree α),
    labelWithIndex (Tree.map f t) = Tree.map (Prod.map f id) (labelWithIndex t) :=
  congrFun (labelWithIndex_naturality f)

-- produce a list of node-values by performing a preorder traversal
def flatten : Tree α → List α :=
  (depthFirstTraversable VisitOrder.Node1st).foldl (flip List.cons) []

lemma flatten_eq_toList_reverse :
    @flatten α = List.reverse ∘ (depthFirstTraversable VisitOrder.Node1st).toList := by
  simp only [Traversable.toList, flatten, ← Function.comp.assoc,
             List.reverse_involutive.comp_self, Function.comp.left_id]

@[simp] lemma flatten_nil : flatten (@nil α) = [] := rfl
@[simp] lemma flatten_node (a : α) l r :
    flatten (node a l r) = flatten r ++ flatten l ++ [a] :=
  by simp only [flatten_eq_toList_reverse, Function.comp_apply,
                ← List.reverse_append, ← List.reverse_cons, toList_def]; rfl

lemma flatten_naturality {β : Type v} (f : α → β) :
    flatten ∘ Tree.map f = List.map f ∘ flatten := by
  ext t : 1
  induction t
  <;> simp only [Function.comp_apply, map_node, flatten_node, List.map_cons,
                 List.map_append, List.cons.injEq, true_and, map_nil,
                 flatten_nil, List.map_nil]
  congr

@[simp] lemma flatten_map {β : Type v} (f : α → β) : ∀ (t : Tree α),
    flatten (Tree.map f t) = List.map f (flatten t) :=
  congrFun (flatten_naturality f)

-- def

def validPaths (t : Tree α) : List Path :=
  List.map Prod.snd $ flatten $ labelWithIndex t

@[simp] lemma validPaths_nil : validPaths (@nil α) = [] := rfl
@[simp] lemma validPaths_node (a : α) l r :
    validPaths (node a l r)
    = List.map Path.right (validPaths r)
      ++ List.map Path.left (validPaths l)
      ++ [Path.here] :=
  by simp only [validPaths, labelWithIndex, flatten_node, List.map_cons,
                List.map_append, List.cons.injEq, true_and, flatten_map,
                List.map_map]; congr

@[simp] lemma validPaths_map (f : α → β) (t : Tree α) :
    validPaths (Tree.map f t) = validPaths t := by
  induction t
  <;> simp only [map_nil, map_node, validPaths_nil, validPaths_node,
                 List.cons.injEq, true_and]
  congr

@[simp] lemma mem_validPaths_iff_validFor (p : Path) (t : Tree α) :
    p ∈ t.validPaths ↔ p.validFor t := by
  revert p; induction t <;> intro p <;> cases p
    <;> simp only [validPaths_nil, List.find?_nil, List.not_mem_nil, Path.validFor,
                   validPaths_node, Bool.not_eq_true, List.mem_cons, List.mem_append,
                   List.mem_map, and_false, exists_const, or_self, or_false, false_or,
                   Path.left.injEq, Path.right.injEq, exists_eq_right]
    <;> apply_assumption

lemma validPaths_nodup (t : Tree α) : t.validPaths.Nodup := by
  induction t
  . exact List.nodup_nil
  . simp only [validPaths_node, List.nodup_cons, List.mem_append, List.mem_map,
               and_false, exists_const, or_self, not_false_eq_true, and_true,
               List.nodup_append, List.disjoint_singleton]
    rw [List.nodup_map_iff Path.left_injective, List.nodup_map_iff Path.right_injective]
    simp only [List.Disjoint, List.mem_map, forall_exists_index, and_imp, forall_const,
               forall_apply_eq_imp_iff₂, IsEmpty.forall_iff, implies_true, and_true]
    constructor <;> assumption

@[reducible, simp] def before_in_flattening (p q : Path) :=
  q < p ∨ (p ⊓ q ++ Path.left Path.here ≤ q ∧ p ⊓ q ++ Path.right Path.here ≤ p)

lemma validPaths_order : ∀ (p q : Path) (t : Tree α),
    List.Sublist [p, q] (validPaths t)
    ↔ (before_in_flattening p q ∧ p.validFor t ∧ q.validFor t) :=
  have lem0 {t : Tree α} {p q : Path} :
      List.Sublist [p, q] (validPaths t) → p.validFor t ∧ q.validFor t :=
    by refine ?_ ∘ List.Sublist.subset
       simp only [List.cons_subset, mem_validPaths_iff_validFor,
                  List.nil_subset, and_true, imp_self]
  have lem1 (p q r : Path) : ¬ List.Sublist [p, q] [r]
    | List.Sublist.cons   x h => List.cons_ne_nil _ _ $ List.sublist_nil.mp h
    | List.Sublist.cons₂  x h => List.cons_ne_nil _ _ $ List.sublist_nil.mp h
  have lem2 (t : Tree α) p (h : p ≠ Path.here) :
      List.Sublist [p, Path.here] (validPaths t) ↔ p.validFor t := by
    refine ⟨And.left ∘ lem0, ?_⟩
    intro h'; revert h
    rw [← Decidable.or_iff_not_imp_left, ← List.reverse_sublist]; revert h'
    cases t <;> cases p
    <;> simp only [Path.validFor, true_or, false_or, forall_true_left,
                   IsEmpty.forall_iff, validPaths_nil, validPaths_node,
                   List.cons_sublist_cons, List.singleton_sublist, and_false,
                   mem_validPaths_iff_validFor, exists_eq_right, imp_self,
                   exists_const, or_false, List.mem_map, List.reverse_nil,
                   List.mem_append, Path.left.injEq, Path.right.injEq,
                   List.reverse_append, List.reverse_map, List.reverse_cons,
                   List.nil_append, List.singleton_append, List.mem_reverse]
  have lem3 (t : Tree α) q :
      ¬ List.Sublist [Path.here, q] (validPaths t) := by
    cases t
    <;> simp only [validPaths_nil, validPaths_node, List.sublist_nil,
                   not_false_eq_true, List.map_nil]
    rw [← List.reverse_sublist]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
               List.append_assoc, List.reverse_append, List.cons_append,
               List.singleton_append, List.reverse_map, or_self,
               List.cons_sublist_cons_iff', List.singleton_sublist,
               List.mem_append, List.mem_map, List.mem_reverse, false_or,
               mem_validPaths_iff_validFor, and_false, exists_const,
               List.pair_sublist_append, not_or]
    constructor
    <;> refine mt List.Sublist.subset ?_
    <;> simp only [List.cons_subset, List.mem_map, and_false, exists_false,
                   List.nil_subset, and_true, not_false_eq_true]
  have lem4 (t : Tree α) p q :
      ¬ List.Sublist [Path.left p, Path.right q] (validPaths t) := by
    cases t
    <;> simp only [validPaths_nil, validPaths_node, List.append_assoc, List.pair_sublist_append, List.mem_map,
                   and_false, exists_const, List.mem_append, List.mem_singleton, or_self, and_self,
                   Path.left.injEq, exists_eq_right, lem1, or_false, false_or, not_or, List.sublist_nil]
    constructor
    <;> refine mt List.Sublist.subset ?_
    <;> simp only [List.cons_subset, List.mem_map, Path.left.injEq, exists_eq_right, and_false,
                   exists_const, List.nil_subset, and_true, not_false_eq_true, false_and]
  have lem5 (t : Tree α) p q :
      List.Sublist [Path.right p, Path.left q] (validPaths t)
      ↔ (Path.validFor (Path.right p) t ∧ Path.validFor (Path.left q) t) := by
    refine ⟨lem0, ?_⟩
    cases t
    <;> simp only [Path.validFor, validPaths_nil, List.pair_sublist_append,
                   List.mem_map, mem_validPaths_iff_validFor, Path.right.injEq,
                   List.mem_append, Path.left.injEq, List.mem_singleton,
                   and_self, false_or, List.sublist_nil, IsEmpty.forall_iff,
                   or_assoc, exists_eq_right, and_false, exists_const,
                   or_false, validPaths_node]
    exact Or.inr ∘ Or.inl
  have lem6 a (l r : Tree α) p q :
      List.Sublist [Path.left p, Path.left q] (validPaths (node a l r))
      ↔ List.Sublist [p, q] (validPaths l) := by
    simp only [validPaths_nil, validPaths_node, List.append_assoc,
               List.pair_sublist_append, false_and, false_or, or_false,
               List.mem_map, and_false, exists_const, List.mem_append,
               Path.left.injEq, exists_eq_right, List.mem_singleton, lem1]
    rw [or_iff_right]
    . refine @List.Sublist.map_inj _ _ Path.left ?_ [p, q] _
      intro _ _; exact Eq.mp (Path.left.injEq _ _)
    . refine mt List.Sublist.subset ?_
      simp only [List.cons_subset, List.mem_map, and_false, exists_const,
                 List.nil_subset, and_true, and_self, not_false_eq_true]
  have lem7 a (l r : Tree α) p q :
      List.Sublist [Path.right p, Path.right q] (validPaths (node a l r))
      ↔ List.Sublist [p, q] (validPaths r) := by
    simp only [validPaths_nil, validPaths_node, List.append_assoc,
               List.mem_map, and_false, exists_const, List.mem_append,
               Path.right.injEq, exists_eq_right, List.mem_singleton,
               List.pair_sublist_append, false_and, or_false, false_or, lem1]
    rw [or_iff_left]
    . refine @List.Sublist.map_inj _ _ Path.right ?_ [p, q] _
      intro _ _; exact Eq.mp (Path.right.injEq _ _)
    . refine mt List.Sublist.subset ?_
      simp only [List.cons_subset, List.mem_map, and_false, exists_const,
                 List.nil_subset, and_true, and_self, not_false_eq_true]
  by intros p q t
     dsimp only [before_in_flattening]
     by_cases h : p = q
     . subst h
       apply iff_of_false
       . refine List.nodup_iff_sublist.mp ?_ p
         apply validPaths_nodup
       . simp only [lt_self_iff_false, le_refl, inf_of_le_left, false_or]
         refine mt (And.left ∘ And.left) (not_le_of_lt ?_)
         refine ⟨⟨Path.left Path.here, rfl⟩, mt (congrArg Path.length) ?_⟩
         simp only [Path.length_append, self_eq_add_right, not_false_eq_true]
     dsimp only [Inf.inf]
     rw [← and_iff_left_of_imp lem0, and_congr_left_iff, and_imp]
     revert h p q
     induction' t with a l r ihₗ ihᵣ <;> intro p q h
     . simp only [Path.validFor, IsEmpty.forall_iff, implies_true]
     . intro hp hq
       cases' q with q q
       . simp only [ne_eq, Path.lt_def, Path.here_le, true_and, true_iff,
                    Path.le_here_iff_eq_here, false_and, or_false, h,
                    Path.longestCommonPrefix, lem2, hp]
         apply Ne.symm; assumption
       all_goals cases' p with p p
       all_goals simp only
         [Path.longestCommonPrefix, false_or, Path.right_le_right_iff_le,
          Path.here_append, Path.left_lt_left_iff_lt, Path.not_right_lt_left,
          and_false, or_self, Path.not_left_lt_right, Path.left_le_left_iff_le,
          true_and, and_self, Path.right_lt_right_iff_lt, Path.here_le,
          false_and, Path.not_left_le_right,
          iff_true, true_iff, or_false, true_or, false_iff, Path.not_lt_here,
          hp, hq, lem3, lem4, lem5, lem6, lem7]
       . refine Iff.trans (ihₗ p q (Path.left.injEq p q ▸ h) hp hq) (or_congr_right ?_)
         simp only [Path.left_append, Path.left_le_left_iff_le]
       . refine Iff.trans (ihᵣ p q (Path.right.injEq p q ▸ h) hp hq) (or_congr_right ?_)
         simp only [Path.right_append, Path.right_le_right_iff_le]

-- need to think harder about how this should work ...
def mkTreeWithNodes (nodes : List (Path × α)) : Option (Tree α) :=
  StateT.run' (nodes.foldlM (m := StateT (Option (Tree α) × Tree α) Option) (s := Tree α)
    sorry
    nil) (some nil, nil)
  -- StateT.run' (m := Option) (σ := Option (Tree α) × Tree α)
  --   ∘ List.foldlM (m := StateT (Option (Tree α) × Tree α) Option) (s := Tree α)
  --       sorry sorry

-- grr irritating not to be able to use do notation here
-- def mkTreeWithNodes : List (Path × α) → Option (Tree α)
--   | [] => none
--   | x::xs => (go x.fst.reverse $ xs.map (Prod.map Path.reverse id)).map Prod.fst
--   where
--   go (car : Path) (cdr : List (Path × α)) : Option (Tree α × List (Path × α)) :=
--     bif car.isRight? && (cdr.head?.map (Path.isLeft? ∘ Prod.fst)).getD false
--     then cdr.head?.map (fun x => (node x.snd nil nil, cdr.tail))
--     else match cdr with
--          | [] => none
--          | cadr::cddr => go cadr.fst cddr

-- lemma mkTreeWithNodes_map_validPaths_eq_self
--     {paths} (h : paths.Sorted before_in_flattening) :
--     paths ∈ Option.map validPaths (mkTreeWithNodes paths) := by

--   admit

-- lemma mkTreeWithNodes_defined_iff_sorted (paths : List Path) :
--     (mkTreeWithNodes paths).isSome ↔ paths.Sorted before_in_flattening := by
--   constructor
--   . dsimp only [mkTreeWithNodes, Function.comp_apply, StateT.run'_eq, Option.map_eq_map]
--     rw [List.Sorted, ← List.pairwise_reverse, ← List.Sorted]
--     conv => left; left; right; right; right
--             rw [← List.reverse_reverse paths, List.foldl_reverse, ← List.map_eq_foldr]
--     generalize List.reverse paths = paths'; clear paths; rename List Path => paths

--     intro h
--     generalize h' : List.length paths = n
--     revert h; revert paths
--     induction' n using Nat.strongInductionOn with n ih
--     intro paths _; subst n
--     conv at ih => intro; rw [imp_forall_iff]; intro; rw [imp.swap]
--     rw [forall_swap] at ih; simp only [forall_eq'] at ih



    -- simp_rw [imp.swap] at ih

    -- cases paths with
    --   | List.nil => admit
    --   | List.cons (Path.left _) (List.cons (Path.right _) ps) => admit
    --   | _ :: ps =>admit
  -- . refine ?_ ∘ mkTreeWithNodes_map_validPaths_eq_self
  --   rw [Option.mem_def, Option.map_eq_some', Option.isSome_iff_exists]
  --   refine Exists.imp (fun _ => And.left)

-- should state the constructive version of this at least for Tree Unit
lemma validPaths_characterization [Nonempty α] (s : Set Path) :
    (∃ (t : Tree α), s = setOf (. ∈ validPaths t))
    ↔ s.Finite ∧ (∀ p q, p ++ q ∈ s → p ∈ s) := by
  constructor
  . rintro ⟨t, ⟨rfl⟩⟩
    refine ⟨List.finite_toSet _, ?_⟩
    simp_rw [mem_validPaths_iff_validFor]
    intros p q hpq
    -- TODO: prove lemma about p ++ q being followable iff p is followable and q is followable from p

    admit
  . rintro ⟨h1, h2⟩
    simp only [mem_validPaths_iff_validFor, ← followable_iff_validFor]
    suffices : ∃ t : Tree Unit, s = {x | Option.isSome (follow x t) }
    . obtain ⟨t, h⟩ := this; subst h
      apply @Nonempty.elim_to_inhabited α; rintro ⟨a⟩
      existsi t.map (fun _ => a)
      ext p
      dsimp only [Set.mem_setOf_eq]
      simp only [mem_validPaths_iff_validFor, ← followable_iff_validFor,
                 Option.isSome_iff_exists, map_follow, Option.map_eq_some',
                 exists_and_left, exists_and_right, exists_eq', and_true]

    -- idea: generate a tree until the path from root is bigger than every element of s

    -- or show that for any path and any tree we can (minimally) extend the tree so that it contains the path
    -- then induct to do this for any finite set, et voila
    admit

/-- Auxiliary definition for `Tree.graft`. -/
def graftAux (g : Tree α) (t' : Tree α) {m : Type u → Type u}
             [Monad m] [MonadStateOf (ULift ℕ) m] : m (Tree α) := do
    let curr := (← get').down
    bif curr == 0
    then return t'
    else (match t' with
          | nil => do
              set (ULift.up (curr - 1))
              bif curr == 1 then return g else return nil
          | node a l r => do
              let l' ← graftAux g l
              let r' ← graftAux g r
              return node a l' r')

-- not well defined if i > numLeaves t
def graft (t : Tree α) (i : ℕ) (g : Tree α) : Tree α :=
  (graftAux (m := StateM.{u} (ULift ℕ)) t g).run' (ULift.up (i + 1))

open LawfulMonadStateOf
lemma graft.go_remainder_eq (t : Tree α) (g : Tree α) {m : Type u → Type u}
  [Monad m] [MonadStateOf (ULift ℕ) m] [LawfulMonad m] [LawfulMonadStateOf (ULift ℕ) m]
    : (graftAux (m := m) g t >>= fun _ => get' (m := m))
    = modifyThenGet (m := m) (ULift.up ∘ (ULift.down · - numLeaves t)) := by
  induction' t with a l r ihₗ ihᵣ
  <;> dsimp only [graftAux]
  <;> simp only [bind_assoc, cond_bind, pure_bind, modifyThenGet_def,
                 modify_def, Function.comp_apply, set_get]
  <;> rw [← get_set_pure_eq_get_assoc]
  <;> apply bind_congr <;> intro ⟨i⟩
  <;> simp only [Bool.cond_eq_ite, beq_iff_eq, numLeaves]
  <;> split
  <;> try { rename (i = 0) => h; subst h; simp only [set_get, tsub_eq_zero_of_le, zero_le] }
  . simp only [ite_self, set_get, set_set_assoc]
  . simp only [ihᵣ, modifyThenGet_def, modify_def, Function.comp_apply, bind_assoc, set_get]
    conv => enter [1, 2, u]; rw [← bind_assoc, ihₗ]
    simp only [modifyThenGet_def, modify_def, Function.comp_apply, bind_assoc,
               set_get, pure_bind, tsub_le_iff_right, Nat.sub_sub, set_set_assoc, set_get_assoc]

def graftManyAux {m : Type u → Type u} [Monad m]
    [MonadStateOf (List (Tree α)) m] (t' : Tree α) : m (Tree α) := do
  let gs ← get'
  if h : gs.isEmpty
  then return t'
  else match t' with
       | nil =>
           set gs.tail -- we know gs ≠ []
           return List.head gs (List.isEmpty_iff_eq_nil.not.mp h)
       | node a l r =>
           let l' ← graftManyAux l
           let r' ← graftManyAux r
           return node a l' r'

-- not well defined if the length of the list is > numLeaves t
def graftMany (t : Tree α) : List (Tree α) → Tree α :=
  (graftManyAux (m := StateM.{u} (List (Tree α))) t).run'

def labelLeavesAux {m : Type (max u v) → Type (max u v)} [Monad m]
    [MonadStateOf (ULift.{u} (List β)) m] : Tree α → OptionT m (Tree' α β)
  | nil => do
    let bs := (← get').down
    let b := (← ((Option.traverse (pure ∘ ULift.up.{u}) (List.head? bs))
              : OptionT m (ULift.{u} β))).down
    set (ULift.up bs.tail)
    return Tree'.leaf b
  | node a l r => do
      let l' ← labelLeavesAux l
      let r' ← labelLeavesAux r
      return Tree'.branch a l' r'

def labelLeaves (t : Tree α) (bs : List β) : Option (Tree' α β) :=
  (labelLeavesAux (m := StateM (ULift.{u} (List β))) t).run.run' ⟨bs⟩

-- encapsulates both the info about the remainder/return value & the failure state!
lemma labelLeavesAux_remainder_concat (t : Tree α) {m : Type (max u v) → Type (max u v)}
    [Monad m] [MonadStateOf (ULift (List β)) m] [LawfulMonad m]
    [LawfulMonadStateOf (ULift (List β)) m]
    : (do let t' ← labelLeavesAux.{u, v} (m:=m) t
          let rem := (← get').down
          set (ULift.up (t'.getLeaves ++ rem)))
    = (do let bs ← get'
          bif (Nat.blt (numLeaves t) (List.length bs.down))
          then set bs
          else failure) := by
  admit

-- lemma labelLeaves.go_rem_eq_drop (t : Tree α) (bs : List β)
--     : ((go t).run.run ⟨bs⟩).snd.down = List.drop (numLeaves t) bs := by
--   refine @And.left _ (((go t).run.run ⟨bs⟩).fst.isNone → ((go t).run.run ⟨bs⟩).snd.down = []) ?_
--   revert bs; induction' t with a l r ihₗ ihᵣ <;> intro bs
--   . cases bs <;> refine ⟨rfl, ?_⟩
--     . intro; exact rfl
--     . intro h; exact (Bool.false_ne_true h).elim
--   . simp only [go, OptionT.run_bind, OptionT.run_pure, StateT.run_bind, Id.bind_eq, numLeaves]
--     specialize ihₗ bs
--     generalize h' : StateT.run (OptionT.run (labelLeaves.go l)) ⟨bs⟩ = e at ihₗ
--     obtain ⟨ihₗ, ihₗ'⟩ := ihₗ
--     obtain ⟨o, ⟨bs'⟩⟩ := e
--     specialize ihᵣ bs'
--     cases' o with t₁
--     <;> simp only [Option.isNone_none, forall_true_left, StateT.run_pure,
--                    Id.pure_eq, Option.isNone_some, IsEmpty.forall_iff,
--                    StateT.run_bind] at ihₗ ihₗ' ⊢
--     <;> cases ihₗ'
--     <;> rw [Nat.add_comm, List.drop_add, ← ihₗ]
--     <;> simp only [Id.bind_eq, List.drop_nil]
--     generalize h'' : StateT.run (OptionT.run (labelLeaves.go r)) ⟨bs'⟩ = e at ihᵣ
--     obtain ⟨ihᵣ, ihᵣ'⟩ := ihᵣ
--     obtain ⟨o, ⟨bs''⟩⟩ := e
--     cases' o with t₂
--     <;> simp only [Option.isNone_none, forall_true_left, StateT.run_pure,
--                     Id.pure_eq, Option.isNone_some, IsEmpty.forall_iff,
--                     StateT.run_pure, Id.pure_eq, and_true] at ihᵣ ihᵣ' ⊢
--     <;> cases ihᵣ'
--     <;> simp only [ihᵣ]

-- lemma labelLeaves.go_happy_path (t : Tree α) (bs : List β)
--   (h : Option.isSome ((OptionT.run (go t)).run' ⟨bs⟩) = true)
--   : t ∈ Option.map Tree'.eraseLeafData ((OptionT.run (go t)).run' ⟨bs⟩)
--   ∧ bs ∈ Option.map (Tree'.getLeaves · ++ ((OptionT.run (go t)).run ⟨bs⟩).snd.down)
--                     ((OptionT.run (go t)).run' ⟨bs⟩) := by
--   simp only [StateT.run'_eq, Id.map_eq, Option.mem_def] at h ⊢
--   revert h bs; induction' t with a l r ihₗ ihᵣ <;> intro bs h
--   . cases bs
--     . exfalso; exact Bool.false_ne_true h
--     . exact ⟨rfl, rfl⟩
--   . simp only [go, OptionT.run_bind, OptionT.run_pure, StateT.run_bind] at h ⊢

--     specialize ihₗ bs
--     rw [Option.isSome_iff_exists, forall_exists_index] at ihₗ
--     generalize h' : StateT.run (OptionT.run (go l)) ⟨bs⟩ = e at h ihₗ
--     obtain ⟨o, ⟨bs'⟩⟩ := e
--     cases' o with t₁
--     . exfalso; exact Bool.false_ne_true (Eq.trans (Eq.symm Option.isSome_none) h)
--     specialize ihₗ t₁ rfl
--     simp only [Option.map_some', Option.some.injEq] at ihₗ

--     specialize ihᵣ bs'
--     rw [Option.isSome_iff_exists, forall_exists_index] at ihᵣ
--     simp only [Id.bind_eq, StateT.run_bind] at h
--     simp only [Id.bind_eq, StateT.run_bind]
--     generalize h'' : StateT.run (OptionT.run (go r)) ⟨bs'⟩ = e at h ihᵣ
--     obtain ⟨o, ⟨bs''⟩⟩ := e
--     cases' o with t₂
--     . exfalso; exact Bool.false_ne_true (Eq.trans (Eq.symm Option.isSome_none) h)
--     specialize ihᵣ t₂ rfl
--     simp only [Option.map_some', Option.some.injEq] at ihᵣ

--     simp only [Id.pure_eq, Id.bind_eq, StateT.run_pure, StateT.run_bind,
--                Option.map_some', Option.some.injEq, Tree'.eraseLeafData,
--                Tree'.getLeaves, node.injEq, true_and, List.append_assoc]
--     rw [← ihᵣ.right] at ihₗ
--     exact ⟨⟨ihₗ.left, ihᵣ.left⟩, ihₗ.right⟩

-- lemma labelLeaves_nodes_unchanged (t : Tree α) (bs : List β)
--   (h : Option.isSome (labelLeaves t bs) = true)
--   : t ∈ Option.map Tree'.eraseLeafData (labelLeaves t bs)
--   := (labelLeaves.go_happy_path t bs h).left

-- lemma labelLeaves_leaves_eq_take (t : Tree α) (bs : List β)
--   (h : Option.isSome (labelLeaves t bs) = true)
--   : List.take (numLeaves t) bs
--   ∈ Option.map Tree'.getLeaves (labelLeaves t bs) := by
--     unfold labelLeaves; rw [StateT.run'_eq, Id.map_eq]

--     obtain ⟨hl, hr⟩ := labelLeaves.go_happy_path t bs h
--     rw [Option.mem_map] at hl; obtain ⟨t', hl, hl'⟩ := hl
--     rw [← congrArg numLeaves hl',
--         ← Tree'.getLeaves_length_eq_eraseLeafData_numLeaves t']
--     rw [StateT.run'_eq, Id.map_eq, Option.mem_def] at hl hr
--     rw [hl] at hr
--     simp only [Option.map_some', Option.some.injEq] at hr

--     rw [congrArg (List.take _) (Eq.symm hr)]
--     simp only [List.take_left, Option.mem_def]
--     exact hl ▸ rfl

-- lemma labelLeaves.go_rem_length (t : Tree α) (bs : List β)
--   (h : Option.isSome (labelLeaves t bs) = true)
--   : numLeaves t + List.length ((OptionT.run (go t)).run ⟨bs⟩).snd.down
--     = List.length bs := by
--   rw [labelLeaves.go_rem_eq_drop t bs]
--   have H := Option.mem_map_of_mem List.length (labelLeaves_leaves_eq_take t bs h)
--   rw [← Option.comp_map, Option.mem_map] at H
--   obtain ⟨rem, h', h''⟩ := H
--   simp only [Function.comp_apply, List.length_take, ge_iff_le] at h''
--   rw [min_eq_left] at h''


--   -- obtain ⟨hl, hr⟩ := labelLeaves.go_happy_path t bs h
--   -- rw [Option.mem_map] at hl; obtain ⟨t', hl, hl'⟩ := hl
--   -- rw [← congrArg numLeaves hl',
--   --     ← Tree'.getLeaves_length_eq_eraseLeafData_numLeaves t']
--   -- rw [StateT.run'_eq, Id.map_eq, Option.mem_def] at hl hr
--   -- rw [hl] at hr
--   -- simp only [Option.map_some', Option.some.injEq] at hr
--   -- exact Eq.trans (Eq.symm (List.length_append _ _)) (congrArg List.length hr)

-- lemma labelLeaves_isNone_iff (t : Tree α) (bs : List β)
--   : (labelLeaves t bs).isNone ↔ List.length bs < Tree.numLeaves t := by
--     unfold labelLeaves
--     constructor
--     . rw [StateT.run'_eq, Id.map_eq, Option.isNone_iff_eq_none]
--       revert bs; induction' t with a l r ihₗ ihᵣ <;> intros bs h
--       . cases bs
--         <;> simp only [OptionT.run, labelLeaves.go, bind, OptionT.bind, pure,
--                        OptionT.mk, StateT.bind, liftM, monadLift, StateT.pure,
--                        MonadLift.monadLift, OptionT.lift, StateT.get, numLeaves,
--                        StateT.set, OptionT.pure, StateT.run'_eq, StateT.run,
--                        Id.map_eq, List.length_nil, zero_lt_one] at h ⊢
--       . simp only [labelLeaves.go, OptionT.run_bind, OptionT.run_pure,
--                    StateT.run_bind, Id.bind_eq] at h
--         specialize ihₗ bs
--         generalize h' : StateT.run (OptionT.run (labelLeaves.go l)) ⟨bs⟩ = e at h ihₗ
--         obtain ⟨o, ⟨bs'⟩⟩ := e
--         cases' o with t₁
--         . exact lt_of_lt_of_le (ihₗ rfl) (Nat.le_add_right _ _)
--         simp only [StateT.run_bind, Id.bind_eq] at h

--         specialize ihᵣ bs'
--         generalize h'' : StateT.run (OptionT.run (labelLeaves.go r)) ⟨bs'⟩ = e at h ihᵣ
--         obtain ⟨o, ⟨bs''⟩⟩ := e
--         cases' o with t₂
--         . have H := Option.isSome_iff_exists.mpr ⟨_, congrArg Prod.fst h'⟩
--           have := labelLeaves_leaves_eq l bs H

--           refine lt_of_eq_of_lt (Eq.symm $ labelLeaves.go_rem_length l bs H) ?_
--           apply Nat.add_lt_add_left
--           rw [h']
--           exact ihᵣ rfl
--         . exfalso; exact Option.some_ne_none _ h
--     . rw [← Decidable.not_imp_not]
--       simp only [Option.isNone_iff_eq_none, Option.ne_none_iff_isSome,
--                  ← Ne.def, Nat.not_lt]
--       intro h
--       exact le_of_le_of_eq (Nat.le_add_right _ _) (labelLeaves.go_rem_length t bs h)

end Tree

def unit_leaves_equiv_Tree {N} : Tree' N Unit ≃ Tree N where
  toFun := Tree'.eraseLeafData
  invFun := Tree'.fillLeavesDefault Unit
  left_inv := by
    intro t; induction t; exact rfl
    dsimp [Tree'.eraseLeafData, Tree'.fillLeavesDefault]
    refine congr_arg₂ _ ?_ ?_ <;> assumption
  right_inv := by
    intro t; induction t; exact rfl
    dsimp [Tree'.eraseLeafData, Tree'.fillLeavesDefault]
    refine congr_arg₂ _ ?_ ?_ <;> assumption

def leaves_equiv_Tree {N L}
  : Tree' N L ≃ { p : Tree N × List L // p.fst.numLeaves = p.snd.length } where
  toFun t := ⟨(Tree'.eraseLeafData t, Tree'.getLeaves t),
              Eq.symm $ Tree'.getLeaves_length_eq_eraseLeafData_numLeaves t⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
