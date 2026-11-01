/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.WSeq.Relation

/-!
# Parallel computation

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)
-/

@[expose] public section

universe u v

namespace Computation
open Stream'

variable {α : Type u} {β : Type v}

private def parallel.aux2 : List (Computation α) → α ⊕ List (Computation α)
  | [] => .inr []
  | .cons c l => (parallel.aux2 l).elim .inl fun ls ↦ rmap (· :: ls) (destruct c)

private def parallel.aux1 :
    List (Computation α) × WSeq (Computation α) → α ⊕ (List (Computation α) × WSeq (Computation α))
  | (l, S) => rmap (fun l' ↦ match Seq.destruct S with
      | none => (l', Seq.nil)
      | some (o, S') => (o.elim l' (· :: l'), S')) (parallel.aux2 l)

/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
@[no_expose] def parallel (S : WSeq (Computation α)) : Computation α :=
  corec parallel.aux1 ([], S)

private theorem parallel.aux2_eq_inr {l : List (Computation α)} {l'}
    (h : parallel.aux2 l = .inr l') : l' = l.map tail ∧ ∀ c ∈ l, destruct c = .inr c.tail := by
  induction l generalizing l' with
  | nil => simp_all [parallel.aux2]
  | cons c l ih =>
    rcases e : parallel.aux2 l <;> cases c using Computation.recOn <;>
      simp_all [parallel.aux2, rmap]

private theorem parallel.aux2_eq_inl {l : List (Computation α)} {a}
    (h : parallel.aux2 l = .inl a) : ∃ c ∈ l, a ∈ c := by
  induction l with
  | nil => simp [parallel.aux2] at h
  | cons c l ih =>
    rcases e : parallel.aux2 l <;> cases c using Computation.recOn <;>
      simp_all [parallel.aux2, rmap, mem_pure_iff]

private theorem terminates_parallel.aux {l : List (Computation α)} {S c} (m : c ∈ l)
    [Terminates c] : Terminates (corec parallel.aux1 (l, S)) := by
  induction c using terminatesRecOn generalizing l S with
  | h1 a =>
    rw [corec_eq_elim]
    rcases e : parallel.aux2 l with b | l'
    · simp only [parallel.aux1, rmap, e, Sum.elim_inl, ret_terminates]
    · simpa using (parallel.aux2_eq_inr e).2 _ m
  | h2 c ih =>
    rw [corec_eq_elim]
    rcases e : parallel.aux2 l with b | l'
    · simp only [parallel.aux1, rmap, e, Sum.elim_inl, ret_terminates]
    obtain ⟨rfl, -⟩ := parallel.aux2_eq_inr e
    simp only [parallel.aux1, rmap, e, Sum.elim_inr, Function.comp_apply]
    split
    all_goals refine @think_terminates _ _ (ih ?_); grind [tail_think, cases Option]

theorem terminates_parallel {S : WSeq (Computation α)} {c} (h : c ∈ S) [T : Terminates c] :
    Terminates (parallel S) := by
  suffices ∀ l, Terminates (corec parallel.aux1 (l, S)) from this []
  refine WSeq.mem_rec_on (C := fun S ↦ ∀ l, Terminates (corec parallel.aux1 (l, S))) h
    (fun b S h l ↦ ?_) (fun S ih l ↦ ?_)
  all_goals
    rw [corec_eq_elim]
    rcases e : parallel.aux2 l with b | l'
    · simp only [parallel.aux1, rmap, e, Sum.elim_inl, ret_terminates]
    simp only [parallel.aux1, rmap, e, Sum.elim_inr, Function.comp_apply]
    refine @think_terminates _ _ ?_
  · simp only [WSeq.seq_destruct_cons, Option.elim_some]
    exact h.elim (· ▸ terminates_parallel.aux List.mem_cons_self) (· _)
  · simp only [WSeq.seq_destruct_think, Option.elim_none]
    exact ih _

theorem exists_of_mem_parallel {S : WSeq (Computation α)} {a} (h : a ∈ parallel S) :
    ∃ c ∈ S, a ∈ c := by
  suffices ∀ C, a ∈ C → ∀ (l : List (Computation α)) S,
      corec parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c by
    simpa using this _ h [] S rfl
  intro C h
  apply memRecOn h
  · intro l S e
    have := congr(destruct $e)
    rcases e' : parallel.aux2 l with b | l'
    · simp only [corec_eq, rmap, parallel.aux1, e', destruct_pure, Sum.inl.injEq] at this
      grind [parallel.aux2_eq_inl]
    · simp [corec_eq, rmap, parallel.aux1, e'] at this
  · intro C' IH l S e
    have := congr(destruct $e)
    rcases e' : parallel.aux2 l with b | l'
    · simp [corec_eq, rmap, parallel.aux1, e'] at this
    obtain ⟨rfl, H⟩ := parallel.aux2_eq_inr e'
    simp only [corec_eq, rmap, parallel.aux1, e', destruct_think, Sum.inr.injEq] at this
    cases S using WSeq.recOn
    all_goals
      simp only [WSeq.seq_destruct_nil, WSeq.seq_destruct_cons, WSeq.seq_destruct_think] at this
      obtain ⟨d, hd, ad⟩ := IH _ _ this
      simp [← WSeq.nil.eq_1, WSeq.notMem_nil] at hd ⊢
      grind [=> destruct_eq_think, think_mem]

theorem map_parallel (f : α → β) (S) : map f (parallel S) = parallel (S.map (map f)) := by
  refine eq_of_bisim (fun c1 c2 ↦ ∃ l S, c1 = map f (corec parallel.aux1 (l, S)) ∧
    c2 = corec parallel.aux1 (l.map (map f), S.map (map f))) ?_ ⟨[], S, rfl, rfl⟩
  rintro _ _ ⟨l, S, rfl, rfl⟩
  have : parallel.aux2 (l.map (map f)) = lmap f (rmap (List.map (map f)) (parallel.aux2 l)) := by
    induction l with
    | nil => rfl
    | cons c l ih =>
      simp only [parallel.aux2, List.map_cons, ih]
      rcases parallel.aux2 l <;> cases c using Computation.recOn <;> simp [lmap, rmap]
  simp only [BisimO, destruct_map, corec_eq, parallel.aux1, this]
  rcases parallel.aux2 l with a | l'
  · simp [lmap, rmap]
  · simp only [lmap, rmap]
    induction S using WSeq.recOn <;> simpa using ⟨_, _, rfl, rfl⟩

theorem parallel_empty (S : WSeq (Computation α)) (h : S.head ~> none) : parallel S = empty _ :=
  eq_empty_of_not_terminates fun ⟨⟨a, m⟩⟩ => by
    let ⟨c, cs, _⟩ := exists_of_mem_parallel m
    let ⟨n, nm⟩ := WSeq.exists_get?_of_mem cs
    let ⟨c', h'⟩ := WSeq.head_some_of_get?_some nm
    injection h h'

/-- Induction principle for parallel computations.
The reason this isn't trivial from `exists_of_mem_parallel` is because it eliminates to `Sort`. -/
def parallelRec {S : WSeq (Computation α)} (C : α → Sort v) (H : ∀ s ∈ S, ∀ a ∈ s, C a) {a}
    (h : a ∈ parallel S) : C a := by
  let T : WSeq (Computation (α × Computation α)) := S.map fun c => c.map fun a => (a, c)
  have h' : a ∈ map Prod.fst (parallel T) := by
    rw [map_parallel, ← WSeq.map_comp]
    convert h
    convert WSeq.map_id S
    exact funext fun c ↦ (map_comp _ _ c).symm.trans (map_id c)
  have : Terminates (parallel T) := (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩
  rcases e : get (parallel T) with ⟨a', c⟩
  have : a ∈ c ∧ c ∈ S := by
    obtain ⟨d, dT, rfl⟩ := exists_of_mem_map h'
    obtain ⟨_, dT', ad'⟩ := exists_of_mem_parallel dT
    obtain ⟨c', cs', rfl⟩ := WSeq.exists_of_mem_map dT'
    obtain ⟨a'', ac', rfl⟩ := exists_of_mem_map ad'
    simp_all [get_eq_of_mem _ dT]
  exact H c this.2 a this.1

theorem parallel_promises {S : WSeq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) : parallel S ~> a :=
  fun _ ma' =>
  let ⟨_, cs, ac⟩ := exists_of_mem_parallel ma'
  H _ cs ac

theorem mem_parallel {S : WSeq (Computation α)} {a} (H : ∀ s ∈ S, s ~> a) {c} (cs : c ∈ S)
    (ac : a ∈ c) : a ∈ parallel S :=
  @mem_of_promises _ _ (terminates_parallel (T := terminates_of_mem ac) cs) _ (parallel_promises H)

theorem parallel_congr_lem {S T : WSeq (Computation α)} {a} (H : S.LiftRel Equiv T) :
    (∀ s ∈ S, s ~> a) ↔ ∀ t ∈ T, t ~> a :=
  ⟨fun h1 _ tT =>
    let ⟨_, sS, se⟩ := WSeq.exists_of_liftRel_right H tT
    (promises_congr se _).1 (h1 _ sS),
    fun h2 _ sS =>
    let ⟨_, tT, se⟩ := WSeq.exists_of_liftRel_left H sS
    (promises_congr se _).2 (h2 _ tT)⟩

-- The parallel operation is only deterministic when all computation paths lead to the same value
theorem parallel_congr_left {S T : WSeq (Computation α)} {a} (h1 : ∀ s ∈ S, s ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T := by
  have h2 := (parallel_congr_lem H).1 h1
  refine fun a' ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨s, sS, as⟩ := exists_of_mem_parallel h
    obtain ⟨t, tT, st⟩ := WSeq.exists_of_liftRel_left H sS
    obtain rfl := h1 _ sS as
    exact mem_parallel h2 tT ((st _).1 as)
  · obtain ⟨s, sS, as⟩ := exists_of_mem_parallel h
    obtain ⟨t, tT, st⟩ := WSeq.exists_of_liftRel_right H sS
    obtain rfl := h2 s sS as
    exact mem_parallel h1 tT ((st _).2 as)

theorem parallel_congr_right {S T : WSeq (Computation α)} {a} (h2 : ∀ t ∈ T, t ~> a)
    (H : S.LiftRel Equiv T) : parallel S ~ parallel T :=
  parallel_congr_left ((parallel_congr_lem H).2 h2) H

end Computation
