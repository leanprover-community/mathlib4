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

namespace Tree

def perfect : ℕ → Tree Unit
  | 0 => nil
  | n+1 => perfect n △ perfect n

universe u v

variable {α : Type u} {β : Type v}

open MonadState renaming get → get'

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

section ShouldBeMoved

abbrev List.headB (xs : List α) h := xs.head $ mt List.isEmpty_iff_eq_nil.mpr h

@[reassocM (attr:=simp)]
lemma cond_bind {m : Type u → Type v} [Monad m] {α β}
  (b : Bool) (t e : m α) (f : α → m β)
    : (cond b t e) >>= f = cond b (t >>= f) (e >>= f) :=
  by cases b <;> exact rfl

@[reassocM (attr:=simp)]
lemma ite_bind {m : Type u → Type v} [Monad m] {α β}
  (P : Prop) [d : Decidable P] (t e : m α) (f : α → m β)
    : (ite P t e) >>= f = ite P (t >>= f) (e >>= f) :=
  by cases d <;> exact rfl

@[reassocM (attr:=simp)]
lemma dite_bind {m : Type u → Type v} [Monad m] {α β}
  (P : Prop) [d : Decidable P] (t : P → m α) (e : ¬ P → m α) (f : α → m β)
    : (dite P t e) >>= f = dite P (t . >>= f) (e . >>= f) :=
  by cases d <;> exact rfl

end ShouldBeMoved

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
           return List.headB gs h
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
