/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)

! This file was ported from Lean 3 source module data.seq.parallel
! leanprover-community/mathlib commit a7e36e48519ab281320c4d192da6a7b348ce40ad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Seq.Wseq

universe u v

namespace Computation

/- ./././Mathport/Syntax/Translate/Command.lean:224:11: unsupported: unusual advanced open style -/
/- ./././Mathport/Syntax/Translate/Command.lean:224:11: unsupported: unusual advanced open style -/
variable {α : Type u} {β : Type v}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def Parallel.aux2 : List (Computation α) → Sum α (List (Computation α)) :=
  List.foldr
    (fun c o =>
      match o with
      | Sum.inl a => Sum.inl a
      | Sum.inr ls => rmap (fun c' => c'::ls) (destruct c))
    (Sum.inr [])
#align computation.parallel.aux2 Computation.Parallel.aux2

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def Parallel.aux1 :
    List (Computation α) × Wseq (Computation α) →
      Sum α (List (Computation α) × Wseq (Computation α))
  | (l, S) =>
    rmap
      (fun l' =>
        match Seq.destruct S with
        | none => (l', Seq.nil)
        | some (none, S') => (l', S')
        | some (some c, S') => (c::l', S'))
      (Parallel.aux2 l)
#align computation.parallel.aux1 Computation.Parallel.aux1

/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
def parallel (S : Wseq (Computation α)) : Computation α :=
  corec Parallel.aux1 ([], S)
#align computation.parallel Computation.parallel

theorem TerminatesParallel.aux :
    ∀ {l : List (Computation α)} {S c},
      c ∈ l → Terminates c → Terminates (corec Parallel.aux1 (l, S)) :=
  by
  have lem1 :
    ∀ l S, (∃ a : α, parallel.aux2 l = Sum.inl a) → terminates (corec parallel.aux1 (l, S)) :=
    by
    intro l S e
    cases' e with a e
    have : corec parallel.aux1 (l, S) = return a :=
      by
      apply destruct_eq_ret
      simp [parallel.aux1]
      rw [e]
      simp [rmap]
    rw [this]
    infer_instance
  intro l S c m T
  revert l S
  apply @terminates_rec_on _ _ c T _ _
  · intro a l S m
    apply lem1
    induction' l with c l IH generalizing m <;> simp at m
    · contradiction
    cases' m with e m
    · rw [← e]
      simp [parallel.aux2]
      cases' List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l with a' ls
      exacts[⟨a', rfl⟩, ⟨a, rfl⟩]
    · cases' IH m with a' e
      simp [parallel.aux2]
      simp [parallel.aux2] at e
      rw [e]
      exact ⟨a', rfl⟩
  · intro s IH l S m
    have H1 : ∀ l', parallel.aux2 l = Sum.inr l' → s ∈ l' :=
      by
      induction' l with c l IH' generalizing m <;> intro l' e' <;> simp at m
      · contradiction
      cases' m with e m <;> simp [parallel.aux2] at e'
      · rw [← e] at e'
        cases' List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l with a' ls <;>
          injection e' with e'
        rw [← e']
        simp
      · induction' e : List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l with a' ls <;>
          rw [e] at e'
        · contradiction
        have := IH' m _ e
        simp [parallel.aux2] at e'
        cases destruct c <;> injection e' with h'
        rw [← h']
        simp [this]
    induction' h : parallel.aux2 l with a l'
    · exact lem1 _ _ ⟨a, h⟩
    · have H2 : corec parallel.aux1 (l, S) = think _ :=
        by
        apply destruct_eq_think
        simp [parallel.aux1]
        rw [h]
        simp [rmap]
      rw [H2]
      apply @Computation.think_terminates _ _ _
      have := H1 _ h
      rcases seq.destruct S with (_ | ⟨_ | c, S'⟩) <;> simp [parallel.aux1] <;> apply IH <;>
        simp [this]
#align computation.terminates_parallel.aux Computation.TerminatesParallel.aux

theorem terminates_parallel {S : Wseq (Computation α)} {c} (h : c ∈ S) [T : Terminates c] :
    Terminates (parallel S) :=
  by
  suffices
    ∀ (n) (l : List (Computation α)) (S c),
      c ∈ l ∨ some (some c) = Seq.get? S n → Terminates c → Terminates (corec Parallel.aux1 (l, S))
    from
    let ⟨n, h⟩ := h
    this n [] S c (Or.inr h) T
  intro n; induction' n with n IH <;> intro l S c o T
  · cases' o with a a
    · exact terminates_parallel.aux a T
    have H : seq.destruct S = some (some c, _) :=
      by
      unfold seq.destruct Functor.map
      rw [← a]
      simp
    induction' h : parallel.aux2 l with a l' <;> have C : corec parallel.aux1 (l, S) = _
    · apply destruct_eq_ret
      simp [parallel.aux1]
      rw [h]
      simp [rmap]
    · rw [C]
      skip
      infer_instance
    · apply destruct_eq_think
      simp [parallel.aux1]
      rw [h, H]
      simp [rmap]
    · rw [C]
      apply @Computation.think_terminates _ _ _
      apply terminates_parallel.aux _ T
      simp
  · cases' o with a a
    · exact terminates_parallel.aux a T
    induction' h : parallel.aux2 l with a l' <;> have C : corec parallel.aux1 (l, S) = _
    · apply destruct_eq_ret
      simp [parallel.aux1]
      rw [h]
      simp [rmap]
    · rw [C]
      skip
      infer_instance
    · apply destruct_eq_think
      simp [parallel.aux1]
      rw [h]
      simp [rmap]
    · rw [C]
      apply @Computation.think_terminates _ _ _
      have TT : ∀ l', terminates (corec parallel.aux1 (l', S.tail)) :=
        by
        intro
        apply IH _ _ _ (Or.inr _) T
        rw [a]
        cases' S with f al
        rfl
      induction' e : seq.nth S 0 with o
      · have D : seq.destruct S = none := by
          dsimp [seq.destruct]
          rw [e]
          rfl
        rw [D]
        simp [parallel.aux1]
        have TT := TT l'
        rwa [seq.destruct_eq_nil D, seq.tail_nil] at TT
      · have D : seq.destruct S = some (o, S.tail) :=
          by
          dsimp [seq.destruct]
          rw [e]
          rfl
        rw [D]
        cases' o with c <;> simp [parallel.aux1, TT]
#align computation.terminates_parallel Computation.terminates_parallel

theorem exists_of_mem_parallel {S : Wseq (Computation α)} {a} (h : a ∈ parallel S) :
    ∃ c ∈ S, a ∈ c :=
  by
  suffices
    ∀ C,
      a ∈ C →
        ∀ (l : List (Computation α)) (S),
          corec Parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c
    from
    let ⟨c, h1, h2⟩ := this _ h [] S rfl
    ⟨c, h1.resolve_left id, h2⟩
  let F : List (Computation α) → Sum α (List (Computation α)) → Prop :=
    by
    intro l a
    cases' a with a l'
    exact ∃ c ∈ l, a ∈ c
    exact ∀ a', (∃ c ∈ l', a' ∈ c) → ∃ c ∈ l, a' ∈ c
  have lem1 : ∀ l : List (Computation α), F l (parallel.aux2 l) :=
    by
    intro l
    induction' l with c l IH <;> simp [parallel.aux2]
    · intro a h
      rcases h with ⟨c, hn, _⟩
      exact False.elim hn
    · simp [parallel.aux2] at IH
      cases' List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l with a ls <;>
        simp [parallel.aux2]
      · rcases IH with ⟨c', cl, ac⟩
        refine' ⟨c', Or.inr cl, ac⟩
      · induction' h : destruct c with a c' <;> simp [rmap]
        · refine' ⟨c, List.mem_cons_self _ _, _⟩
          rw [destruct_eq_ret h]
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
            exact ⟨d, Or.inr dm, ad⟩
  intro C aC
  refine' mem_rec_on aC _ fun C' IH => _ <;> intro l S e <;> have e' := congr_arg destruct e <;>
          have := lem1 l <;>
        simp [parallel.aux1] at e' <;>
      cases' parallel.aux2 l with a' l' <;>
    injection e' with h'
  · rw [h'] at this
    rcases this with ⟨c, cl, ac⟩
    exact ⟨c, Or.inl cl, ac⟩
  · induction' e : seq.destruct S with a <;> rw [e] at h'
    ·
      exact
        let ⟨d, o, ad⟩ := IH _ _ h'
        let ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (wseq.not_mem_nil _), ad⟩
        ⟨c, Or.inl cl, ac⟩
    · cases' a with o S'
      cases' o with c <;> simp [parallel.aux1] at h' <;> rcases IH _ _ h' with ⟨d, dl | dS', ad⟩
      ·
        exact
          let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
          ⟨c, Or.inl cl, ac⟩
      · refine' ⟨d, Or.inr _, ad⟩
        rw [seq.destruct_eq_cons e]
        exact seq.mem_cons_of_mem _ dS'
      · simp at dl
        cases' dl with dc dl
        · rw [dc] at ad
          refine' ⟨c, Or.inr _, ad⟩
          rw [seq.destruct_eq_cons e]
          apply seq.mem_cons
        ·
          exact
            let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
            ⟨c, Or.inl cl, ac⟩
      · refine' ⟨d, Or.inr _, ad⟩
        rw [seq.destruct_eq_cons e]
        exact seq.mem_cons_of_mem _ dS'
#align computation.exists_of_mem_parallel Computation.exists_of_mem_parallel

theorem map_parallel (f : α → β) (S) : map f (parallel S) = parallel (S.map (map f)) :=
  by
  refine'
    eq_of_bisim
      (fun c1 c2 =>
        ∃ l S,
          c1 = map f (corec parallel.aux1 (l, S)) ∧
            c2 = corec parallel.aux1 (l.map (map f), S.map (map f)))
      _ ⟨[], S, rfl, rfl⟩
  intro c1 c2 h;
  exact
    match c1, c2, h with
    | _, _, ⟨l, S, rfl, rfl⟩ => by
      clear _match
      have : parallel.aux2 (l.map (map f)) = lmap f (rmap (List.map (map f)) (parallel.aux2 l)) :=
        by
        simp [parallel.aux2]
        induction' l with c l IH <;> simp
        rw [IH]
        cases List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l <;> simp [parallel.aux2]
        cases destruct c <;> simp
      simp [parallel.aux1]
      rw [this]
      cases' parallel.aux2 l with a l' <;> simp
      apply S.rec_on _ (fun c S => _) fun S => _ <;> simp <;> simp [parallel.aux1] <;>
        exact ⟨_, _, rfl, rfl⟩
#align computation.map_parallel Computation.map_parallel

theorem parallel_empty (S : Wseq (Computation α)) (h : S.headI ~> none) : parallel S = empty _ :=
  eq_empty_of_not_terminates fun ⟨⟨a, m⟩⟩ =>
    by
    let ⟨c, cs, ac⟩ := exists_of_mem_parallel m
    let ⟨n, nm⟩ := Wseq.exists_nth_of_mem cs
    let ⟨c', h'⟩ := Wseq.head_some_of_nth_some nm
    injection h h'
#align computation.parallel_empty Computation.parallel_empty

-- The reason this isn't trivial from exists_of_mem_parallel is because it eliminates to Sort
def parallelRec {S : Wseq (Computation α)} (C : α → Sort v) (H : ∀ s ∈ S, ∀ a ∈ s, C a) {a}
    (h : a ∈ parallel S) : C a :=
  by
  let T : wseq (Computation (α × Computation α)) := S.map fun c => c.map fun a => (a, c)
  have : S = T.map (map fun c => c.1) :=
    by
    rw [← wseq.map_comp]
    refine' (wseq.map_id _).symm.trans (congr_arg (fun f => wseq.map f S) _)
    funext c
    dsimp [id, Function.comp]
    rw [← map_comp]
    exact (map_id _).symm
  have pe := congr_arg parallel this
  rw [← map_parallel] at pe
  have h' := h
  rw [pe] at h'
  haveI : terminates (parallel T) := (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩
  induction' e : get (parallel T) with a' c
  have : a ∈ c ∧ c ∈ S := by
    rcases exists_of_mem_map h' with ⟨d, dT, cd⟩
    rw [get_eq_of_mem _ dT] at e
    cases e
    dsimp at cd
    cases cd
    rcases exists_of_mem_parallel dT with ⟨d', dT', ad'⟩
    rcases wseq.exists_of_mem_map dT' with ⟨c', cs', e'⟩
    rw [← e'] at ad'
    rcases exists_of_mem_map ad' with ⟨a', ac', e'⟩
    injection e' with i1 i2
    constructor
    rwa [i1, i2] at ac'
    rwa [i2] at cs'
  cases' this with ac cs
  apply H _ cs _ ac
#align computation.parallel_rec Computation.parallelRec

theorem parallel_promises {S : Wseq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) : parallel S ~> a :=
  fun a' ma' =>
  let ⟨c, cs, ac⟩ := exists_of_mem_parallel ma'
  H _ cs ac
#align computation.parallel_promises Computation.parallel_promises

theorem mem_parallel {S : Wseq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) {c} (cs : c ∈ S)
    (ac : a ∈ c) : a ∈ parallel S := by
  haveI := terminates_of_mem ac <;> haveI := terminates_parallel cs <;>
    exact mem_of_promises _ (parallel_promises H)
#align computation.mem_parallel Computation.mem_parallel

theorem parallel_congr_lem {S T : Wseq (Computation α)} {a} (H : S.LiftRel Equiv T) :
    (∀ s ∈ S, s ~> a) ↔ ∀ t ∈ T, t ~> a :=
  ⟨fun h1 t tT =>
    let ⟨s, sS, se⟩ := Wseq.exists_of_liftRel_right H tT
    (promises_congr se _).1 (h1 _ sS),
    fun h2 s sS =>
    let ⟨t, tT, se⟩ := Wseq.exists_of_liftRel_left H sS
    (promises_congr se _).2 (h2 _ tT)⟩
#align computation.parallel_congr_lem Computation.parallel_congr_lem

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- The parallel operation is only deterministic when all computation paths lead to the same value
theorem parallel_congr_left {S T : Wseq (Computation α)} {a} (h1 : ∀ s ∈ S, s ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  let h2 := (parallel_congr_lem H).1 h1
  fun a' =>
  ⟨fun h => by
    have aa := parallel_promises h1 h <;> rw [← aa] <;> rw [← aa] at h <;>
      exact
        let ⟨s, sS, as⟩ := exists_of_mem_parallel h
        let ⟨t, tT, st⟩ := wseq.exists_of_lift_rel_left H sS
        let aT := (st _).1 as
        mem_parallel h2 tT aT,
    fun h => by
    have aa := parallel_promises h2 h <;> rw [← aa] <;> rw [← aa] at h <;>
      exact
        let ⟨s, sS, as⟩ := exists_of_mem_parallel h
        let ⟨t, tT, st⟩ := wseq.exists_of_lift_rel_right H sS
        let aT := (st _).2 as
        mem_parallel h1 tT aT⟩
#align computation.parallel_congr_left Computation.parallel_congr_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem parallel_congr_right {S T : Wseq (Computation α)} {a} (h2 : ∀ t ∈ T, t ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  parallel_congr_left ((parallel_congr_lem H).2 h2) H
#align computation.parallel_congr_right Computation.parallel_congr_right

end Computation

