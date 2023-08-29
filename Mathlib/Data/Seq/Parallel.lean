/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Seq.WSeq

#align_import data.seq.parallel from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Parallel computation

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)
-/

universe u v

namespace Computation
open Stream'

variable {α : Type u} {β : Type v}

def parallel.aux2 : List (Computation α) → Sum α (List (Computation α)) :=
  List.foldr
    (fun c o =>
      match o with
      | Sum.inl a => Sum.inl a
      | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c))
    (Sum.inr [])
#align computation.parallel.aux2 Computation.parallel.aux2

def parallel.aux1 :
    List (Computation α) × WSeq (Computation α) →
      Sum α (List (Computation α) × WSeq (Computation α))
  | (l, S) =>
    rmap
      (fun l' =>
        match Seq.destruct S with
        | none => (l', Seq.nil)
        | some (none, S') => (l', S')
        | some (some c, S') => (c :: l', S'))
      (parallel.aux2 l)
#align computation.parallel.aux1 Computation.parallel.aux1

/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
def parallel (S : WSeq (Computation α)) : Computation α :=
  corec parallel.aux1 ([], S)
#align computation.parallel Computation.parallel

theorem terminates_parallel.aux :
    ∀ {l : List (Computation α)} {S c},
      c ∈ l → Terminates c → Terminates (corec parallel.aux1 (l, S)) := by
  have lem1 :
    ∀ l S, (∃ a : α, parallel.aux2 l = Sum.inl a) → Terminates (corec parallel.aux1 (l, S)) := by
    intro l S e
    cases' e with a e
    have : corec parallel.aux1 (l, S) = return a := by
      apply destruct_eq_pure
      simp [parallel.aux1]
      rw [e]
    rw [this]
    -- Porting note: This line is required.
    exact ret_terminates a
  intro l S c m T
  -- ⊢ Terminates (corec parallel.aux1 (l, S))
  revert l S
  -- ⊢ ∀ {l : List (Computation α)} {S : WSeq (Computation α)}, c ∈ l → Terminates  …
  apply @terminatesRecOn _ _ c T _ _
  -- ⊢ ∀ (a : α) {l : List (Computation α)} {S : WSeq (Computation α)}, pure a ∈ l  …
  · intro a l S m
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
    apply lem1
    -- ⊢ ∃ a, parallel.aux2 l = Sum.inl a
    induction' l with c l IH <;> simp at m
    -- ⊢ ∃ a, parallel.aux2 [] = Sum.inl a
                                 -- 🎉 no goals
                                 -- ⊢ ∃ a, parallel.aux2 (c :: l) = Sum.inl a
    cases' m with e m
    -- ⊢ ∃ a, parallel.aux2 (c :: l) = Sum.inl a
    · rw [← e]
      -- ⊢ ∃ a_1, parallel.aux2 (pure a :: l) = Sum.inl a_1
      simp [parallel.aux2]
      -- ⊢ ∃ a_1,
      cases' List.foldr (fun c o =>
        match o with
        | Sum.inl a => Sum.inl a
        | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c)) (Sum.inr List.nil) l with a' ls
      exacts [⟨a', rfl⟩, ⟨a, rfl⟩]
      -- 🎉 no goals
    · cases' IH m with a' e
      -- ⊢ ∃ a, parallel.aux2 (c :: l) = Sum.inl a
      simp [parallel.aux2]
      -- ⊢ ∃ a,
      simp [parallel.aux2] at e
      -- ⊢ ∃ a,
      rw [e]
      -- ⊢ ∃ a,
      exact ⟨a', rfl⟩
      -- 🎉 no goals
  · intro s IH l S m
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
    have H1 : ∀ l', parallel.aux2 l = Sum.inr l' → s ∈ l' := by
      induction' l with c l IH' <;> intro l' e' <;> simp at m
      cases' m with e m <;> simp [parallel.aux2] at e'
      · rw [← e] at e'
        -- Porting note: `revert e'` & `intro e'` are required.
        revert e'
        cases' List.foldr (fun c o =>
            match o with
            | Sum.inl a => Sum.inl a
            | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c))
          (Sum.inr []) l with a' ls <;> intro e' <;> [injection e'; injection e' with e']
        rw [← e']
        simp
      · induction' e : List.foldr (fun c o =>
            match o with
            | Sum.inl a => Sum.inl a
            | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c))
          (Sum.inr List.nil) l with a' ls <;> erw [e] at e'
        · contradiction
        have := IH' m _ e
        simp [parallel.aux2] at e'
        -- Porting note: `revert e'` & `intro e'` are required.
        revert e'
        cases destruct c <;> intro e' <;> [injection e'; injection e' with h']
        rw [← h']
        simp [this]
    induction' h : parallel.aux2 l with a l'
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
    · exact lem1 _ _ ⟨a, h⟩
      -- 🎉 no goals
    · have H2 : corec parallel.aux1 (l, S) = think _ := by
        apply destruct_eq_think
        simp [parallel.aux1]
        rw [h]
      rw [H2]
      -- ⊢ Terminates
      refine @Computation.think_terminates _ _ ?_
      -- ⊢ Terminates
      have := H1 _ h
      -- ⊢ Terminates
      rcases Seq.destruct S with (_ | ⟨_ | c, S'⟩) <;> simp [parallel.aux1] <;> apply IH <;>
                                                       -- ⊢ Terminates
                                                       -- ⊢ Terminates
                                                       -- ⊢ Terminates
                                                                                -- ⊢ s ∈ l'
                                                                                -- ⊢ s ∈ l'
                                                                                -- ⊢ s ∈ c :: l'
        simp [this]
        -- 🎉 no goals
        -- 🎉 no goals
        -- 🎉 no goals
#align computation.terminates_parallel.aux Computation.terminates_parallel.aux

theorem terminates_parallel {S : WSeq (Computation α)} {c} (h : c ∈ S) [T : Terminates c] :
    Terminates (parallel S) := by
  suffices
    ∀ (n) (l : List (Computation α)) (S c),
      c ∈ l ∨ some (some c) = Seq.get? S n → Terminates c → Terminates (corec parallel.aux1 (l, S))
    from
    let ⟨n, h⟩ := h
    this n [] S c (Or.inr h) T
  intro n; induction' n with n IH <;> intro l S c o T
  -- ⊢ ∀ (l : List (Computation α)) (S : Stream'.Seq (Option (Computation α))) (c : …
           -- ⊢ ∀ (l : List (Computation α)) (S : Stream'.Seq (Option (Computation α))) (c : …
                                      -- ⊢ Terminates (corec parallel.aux1 (l, S))
                                      -- ⊢ Terminates (corec parallel.aux1 (l, S))
  · cases' o with a a
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
    · exact terminates_parallel.aux a T
      -- 🎉 no goals
    have H : Seq.destruct S = some (some c, _) := by
      dsimp [Seq.destruct, (· <$> ·)]
      rw [← a]
      simp
      rfl
    induction' h : parallel.aux2 l with a l' <;> have C : corec parallel.aux1 (l, S) = _
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
                                                 -- ⊢ corec parallel.aux1 (l, S) = ?m.66152
                                                 -- ⊢ corec parallel.aux1 (l, S) = ?m.66183
    · -- Porting note: To adjust RHS of `C`, these lines are changed.
      apply destruct_eq_pure
      -- ⊢ destruct (corec parallel.aux1 (l, S)) = Sum.inl ?C.a
      rw [corec_eq, parallel.aux1]
      dsimp only []
      rw [h]
      simp only [rmap]
      rfl
      -- 🎉 no goals
    · rw [C]
      -- ⊢ Terminates (pure a)
      skip
      -- ⊢ Terminates (pure a)
      infer_instance
      -- 🎉 no goals
    · apply destruct_eq_think
      -- ⊢ destruct (corec parallel.aux1 (l, S)) = Sum.inr ?C.s'
      simp [parallel.aux1]
      -- ⊢ (match
      rw [h, H]
      -- 🎉 no goals
    · rw [C]
      -- ⊢ Terminates
      refine @Computation.think_terminates _ _ ?_
      -- ⊢ Terminates
      apply terminates_parallel.aux _ T
      -- ⊢ c ∈ c :: l'
      simp
      -- 🎉 no goals
  · cases' o with a a
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
    · exact terminates_parallel.aux a T
      -- 🎉 no goals
    induction' h : parallel.aux2 l with a l' <;> have C : corec parallel.aux1 (l, S) = _
    -- ⊢ Terminates (corec parallel.aux1 (l, S))
                                                 -- ⊢ corec parallel.aux1 (l, S) = ?m.72564
                                                 -- ⊢ corec parallel.aux1 (l, S) = ?m.72595
    · -- Porting note: To adjust RHS of `C`, these lines are changed.
      apply destruct_eq_pure
      -- ⊢ destruct (corec parallel.aux1 (l, S)) = Sum.inl ?C.a
      rw [corec_eq, parallel.aux1]
      dsimp only []
      rw [h]
      simp only [rmap]
      rfl
      -- 🎉 no goals
    · rw [C]
      -- ⊢ Terminates (pure a)
      skip
      -- ⊢ Terminates (pure a)
      infer_instance
      -- 🎉 no goals
    · apply destruct_eq_think
      -- ⊢ destruct (corec parallel.aux1 (l, S)) = Sum.inr ?C.s'
      simp [parallel.aux1]
      -- ⊢ (match
      rw [h]
      -- 🎉 no goals
    · rw [C]
      -- ⊢ Terminates
      refine @Computation.think_terminates _ _ ?_
      -- ⊢ Terminates
      have TT : ∀ l', Terminates (corec parallel.aux1 (l', S.tail)) := by
        intro
        apply IH _ _ _ (Or.inr _) T
        rw [a]
        cases' S with f al
        rfl
      induction' e : Seq.get? S 0 with o
      · have D : Seq.destruct S = none := by
          dsimp [Seq.destruct]
          rw [e]
          rfl
        rw [D]
        -- ⊢ Terminates
        simp [parallel.aux1]
        -- ⊢ Terminates (corec parallel.aux1 (l', Seq.nil))
        have TT := TT l'
        -- ⊢ Terminates (corec parallel.aux1 (l', Seq.nil))
        rwa [Seq.destruct_eq_nil D, Seq.tail_nil] at TT
        -- 🎉 no goals
      · have D : Seq.destruct S = some (o, S.tail) := by
          dsimp [Seq.destruct]
          rw [e]
          rfl
        rw [D]
        -- ⊢ Terminates
        cases' o with c <;> simp [parallel.aux1, TT]
                            -- 🎉 no goals
                            -- 🎉 no goals
#align computation.terminates_parallel Computation.terminates_parallel

theorem exists_of_mem_parallel {S : WSeq (Computation α)} {a} (h : a ∈ parallel S) :
    ∃ c ∈ S, a ∈ c := by
  suffices
    ∀ C, a ∈ C → ∀ (l : List (Computation α)) (S),
      corec parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c from
    let ⟨c, h1, h2⟩ := this _ h [] S rfl
    ⟨c, h1.resolve_left <| List.not_mem_nil _, h2⟩
  let F : List (Computation α) → Sum α (List (Computation α)) → Prop := by
    intro l a
    cases' a with a l'
    exact ∃ c ∈ l, a ∈ c
    exact ∀ a', (∃ c ∈ l', a' ∈ c) → ∃ c ∈ l, a' ∈ c
  have lem1 : ∀ l : List (Computation α), F l (parallel.aux2 l) := by
    intro l
    induction' l with c l IH <;> simp only [parallel.aux2, List.foldr]
    · intro a h
      rcases h with ⟨c, hn, _⟩
      exact False.elim <| List.not_mem_nil _ hn
    · simp only [parallel.aux2] at IH
      -- Porting note: `revert IH` & `intro IH` are required.
      revert IH
      cases' List.foldr (fun c o =>
        match o with
        | Sum.inl a => Sum.inl a
        | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c)) (Sum.inr List.nil) l with a ls <;>
        intro IH <;>
        simp only [parallel.aux2]
      · rcases IH with ⟨c', cl, ac⟩
        refine' ⟨c', List.Mem.tail _ cl, ac⟩
      · induction' h : destruct c with a c' <;> simp only [rmap]
        · refine' ⟨c, List.mem_cons_self _ _, _⟩
          rw [destruct_eq_pure h]
          apply ret_mem
        · intro a' h
          rcases h with ⟨d, dm, ad⟩
          simp at dm
          cases' dm with e dl
          · rw [e] at ad
            refine' ⟨c, List.mem_cons_self _ _, _⟩
            rw [destruct_eq_think h]
            exact think_mem ad
          · cases' IH a' ⟨d, dl, ad⟩ with d dm
            cases' dm with dm ad
            exact ⟨d, List.Mem.tail _ dm, ad⟩
  intro C aC
  -- ⊢ ∀ (l : List (Computation α)) (S : WSeq (Computation α)), corec parallel.aux1 …
  -- Porting note: `revert e'` & `intro e'` are required.
  apply memRecOn aC <;> [skip; intro C' IH] <;> intro l S e <;> have e' := congr_arg destruct e <;>
    have := lem1 l <;> simp only [parallel.aux1, corec_eq, destruct_pure, destruct_think] at e' <;>
    revert this e' <;> cases' parallel.aux2 l with a' l' <;> intro this e' <;>
    [injection e' with h'; injection e'; injection e'; injection e' with h']
  · rw [h'] at this
    -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
    rcases this with ⟨c, cl, ac⟩
    -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
    exact ⟨c, Or.inl cl, ac⟩
    -- 🎉 no goals
  · induction' e : Seq.destruct S with a <;> rw [e] at h'
                                             -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
                                             -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a✝ ∈ c
    · exact
        let ⟨d, o, ad⟩ := IH _ _ h'
        let ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (WSeq.not_mem_nil _), ad⟩
        ⟨c, Or.inl cl, ac⟩
    · cases' a with o S'
      -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
      cases' o with c <;> simp [parallel.aux1] at h' <;> rcases IH _ _ h' with ⟨d, dl | dS', ad⟩
                          -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
                          -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
                                                         -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
                                                         -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
      · exact
          let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
          ⟨c, Or.inl cl, ac⟩
      · refine' ⟨d, Or.inr _, ad⟩
        -- ⊢ d ∈ S
        rw [Seq.destruct_eq_cons e]
        -- ⊢ d ∈ Seq.cons none S'
        exact Seq.mem_cons_of_mem _ dS'
        -- 🎉 no goals
      · simp at dl
        -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
        cases' dl with dc dl
        -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
        · rw [dc] at ad
          -- ⊢ ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
          refine' ⟨c, Or.inr _, ad⟩
          -- ⊢ c ∈ S
          rw [Seq.destruct_eq_cons e]
          -- ⊢ c ∈ Seq.cons (some c) S'
          apply Seq.mem_cons
          -- 🎉 no goals
        · exact
            let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
            ⟨c, Or.inl cl, ac⟩
      · refine' ⟨d, Or.inr _, ad⟩
        -- ⊢ d ∈ S
        rw [Seq.destruct_eq_cons e]
        -- ⊢ d ∈ Seq.cons (some c) S'
        exact Seq.mem_cons_of_mem _ dS'
        -- 🎉 no goals
#align computation.exists_of_mem_parallel Computation.exists_of_mem_parallel

theorem map_parallel (f : α → β) (S) : map f (parallel S) = parallel (S.map (map f)) := by
  refine'
    eq_of_bisim
      (fun c1 c2 =>
        ∃ l S,
          c1 = map f (corec parallel.aux1 (l, S)) ∧
            c2 = corec parallel.aux1 (l.map (map f), S.map (map f)))
      _ ⟨[], S, rfl, rfl⟩
  intro c1 c2 h
  -- ⊢ BisimO (fun c1 c2 => ∃ l S, c1 = map f (corec parallel.aux1 (l, S)) ∧ c2 = c …
  exact
    match c1, c2, h with
    | _, _, ⟨l, S, rfl, rfl⟩ => by
      have : parallel.aux2 (l.map (map f))
          = lmap f (rmap (List.map (map f)) (parallel.aux2 l)) := by
        simp [parallel.aux2]
        induction' l with c l IH <;> simp
        rw [IH]
        cases List.foldr (fun c o =>
            match o with
            | Sum.inl a => Sum.inl a
            | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c)) (Sum.inr List.nil) l <;>
          simp [parallel.aux2]
        cases destruct c <;> simp
      simp [parallel.aux1]
      rw [this]
      cases' parallel.aux2 l with a l' <;> simp
      induction' S using WSeq.recOn with c S S <;> simp <;>
        exact ⟨_, _, rfl, rfl⟩
#align computation.map_parallel Computation.map_parallel

theorem parallel_empty (S : WSeq (Computation α)) (h : S.head ~> none) : parallel S = empty _ :=
  eq_empty_of_not_terminates fun ⟨⟨a, m⟩⟩ => by
    let ⟨c, cs, _⟩ := exists_of_mem_parallel m
    -- ⊢ False
    let ⟨n, nm⟩ := WSeq.exists_get?_of_mem cs
    -- ⊢ False
    let ⟨c', h'⟩ := WSeq.head_some_of_get?_some nm
    -- ⊢ False
    injection h h'
    -- 🎉 no goals
#align computation.parallel_empty Computation.parallel_empty

-- The reason this isn't trivial from exists_of_mem_parallel is because it eliminates to Sort
def parallelRec {S : WSeq (Computation α)} (C : α → Sort v) (H : ∀ s ∈ S, ∀ a ∈ s, C a) {a}
    (h : a ∈ parallel S) : C a := by
  let T : WSeq (Computation (α × Computation α)) := S.map fun c => c.map fun a => (a, c)
  -- ⊢ C a
  have : S = T.map (map fun c => c.1) := by
    rw [← WSeq.map_comp]
    refine' (WSeq.map_id _).symm.trans (congr_arg (fun f => WSeq.map f S) _)
    funext c
    dsimp [id, Function.comp]
    rw [← map_comp]
    exact (map_id _).symm
  have pe := congr_arg parallel this
  -- ⊢ C a
  rw [← map_parallel] at pe
  -- ⊢ C a
  have h' := h
  -- ⊢ C a
  rw [pe] at h'
  -- ⊢ C a
  haveI : Terminates (parallel T) := (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩
  -- ⊢ C a
  induction' e : get (parallel T) with a' c
  -- ⊢ C a
  have : a ∈ c ∧ c ∈ S := by
    rcases exists_of_mem_map h' with ⟨d, dT, cd⟩
    rw [get_eq_of_mem _ dT] at e
    cases e
    dsimp at cd
    cases cd
    rcases exists_of_mem_parallel dT with ⟨d', dT', ad'⟩
    rcases WSeq.exists_of_mem_map dT' with ⟨c', cs', e'⟩
    rw [← e'] at ad'
    rcases exists_of_mem_map ad' with ⟨a', ac', e'⟩
    injection e' with i1 i2
    constructor
    rwa [i1, i2] at ac'
    rwa [i2] at cs'
  cases' this with ac cs
  -- ⊢ C a
  apply H _ cs _ ac
  -- 🎉 no goals
#align computation.parallel_rec Computation.parallelRec

theorem parallel_promises {S : WSeq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) : parallel S ~> a :=
  fun _ ma' =>
  let ⟨_, cs, ac⟩ := exists_of_mem_parallel ma'
  H _ cs ac
#align computation.parallel_promises Computation.parallel_promises

theorem mem_parallel {S : WSeq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) {c} (cs : c ∈ S)
    (ac : a ∈ c) : a ∈ parallel S := by
  haveI := terminates_of_mem ac
  -- ⊢ a ∈ parallel S
  haveI := terminates_parallel cs
  -- ⊢ a ∈ parallel S
  exact mem_of_promises _ (parallel_promises H)
  -- 🎉 no goals
#align computation.mem_parallel Computation.mem_parallel

theorem parallel_congr_lem {S T : WSeq (Computation α)} {a} (H : S.LiftRel Equiv T) :
    (∀ s ∈ S, s ~> a) ↔ ∀ t ∈ T, t ~> a :=
  ⟨fun h1 _ tT =>
    let ⟨_, sS, se⟩ := WSeq.exists_of_liftRel_right H tT
    (promises_congr se _).1 (h1 _ sS),
    fun h2 _ sS =>
    let ⟨_, tT, se⟩ := WSeq.exists_of_liftRel_left H sS
    (promises_congr se _).2 (h2 _ tT)⟩
#align computation.parallel_congr_lem Computation.parallel_congr_lem

-- The parallel operation is only deterministic when all computation paths lead to the same value
theorem parallel_congr_left {S T : WSeq (Computation α)} {a} (h1 : ∀ s ∈ S, s ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  let h2 := (parallel_congr_lem H).1 h1
  fun a' =>
  ⟨fun h => by
    have aa := parallel_promises h1 h
    -- ⊢ a' ∈ parallel T
    rw [← aa]
    -- ⊢ a ∈ parallel T
    rw [← aa] at h
    -- ⊢ a ∈ parallel T
    exact
      let ⟨s, sS, as⟩ := exists_of_mem_parallel h
      let ⟨t, tT, st⟩ := WSeq.exists_of_liftRel_left H sS
      let aT := (st _).1 as
      mem_parallel h2 tT aT,
    fun h => by
    have aa := parallel_promises h2 h
    -- ⊢ a' ∈ parallel S
    rw [← aa]
    -- ⊢ a ∈ parallel S
    rw [← aa] at h
    -- ⊢ a ∈ parallel S
    exact
      let ⟨s, sS, as⟩ := exists_of_mem_parallel h
      let ⟨t, tT, st⟩ := WSeq.exists_of_liftRel_right H sS
      let aT := (st _).2 as
      mem_parallel h1 tT aT⟩
#align computation.parallel_congr_left Computation.parallel_congr_left

theorem parallel_congr_right {S T : WSeq (Computation α)} {a} (h2 : ∀ t ∈ T, t ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  parallel_congr_left ((parallel_congr_lem H).2 h2) H
#align computation.parallel_congr_right Computation.parallel_congr_right

end Computation
