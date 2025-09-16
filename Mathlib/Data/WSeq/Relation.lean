/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.WSeq.Basic
import Mathlib.Logic.Relation

/-!
# Relations between and equivalence of weak sequences

This file defines a relation between weak sequences as a relation between their `some` elements,
ignoring computation time (`none` elements). Equivalence is then defined in the obvious way.

## Main definitions

* `Stream'.WSeq.LiftRelO`: Lift a relation to a relation over weak sequences.
* `Stream'.WSeq.LiftRel`: Two sequences are `LiftRel R`-related if their corresponding `some`
  elements are `R`-related.
* `Stream'.WSeq.Equiv`: Two sequences are equivalent if they are `LiftRel (· = ·)`-related.
-/

universe u v w

namespace Stream'.WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

/-- lift a relation to a relation over weak sequences -/
@[simp]
def LiftRelO (R : α → β → Prop) (C : WSeq α → WSeq β → Prop) :
    Option (α × WSeq α) → Option (β × WSeq β) → Prop
  | none, none => True
  | some (a, s), some (b, t) => R a b ∧ C s t
  | _, _ => False
attribute [nolint simpNF] LiftRelO.eq_3

theorem LiftRelO.imp {R S : α → β → Prop} {C D : WSeq α → WSeq β → Prop} (H1 : ∀ a b, R a b → S a b)
    (H2 : ∀ s t, C s t → D s t) : ∀ {o p}, LiftRelO R C o p → LiftRelO S D o p
  | none, none, _ => trivial
  | some (_, _), some (_, _), h => And.imp (H1 _ _) (H2 _ _) h
  | none, some _, h => False.elim h
  | some (_, _), none, h => False.elim h

theorem LiftRelO.imp_right (R : α → β → Prop) {C D : WSeq α → WSeq β → Prop}
    (H : ∀ s t, C s t → D s t) {o p} : LiftRelO R C o p → LiftRelO R D o p :=
  LiftRelO.imp (fun _ _ => id) H

theorem LiftRelO.swap (R : α → β → Prop) (C) :
    swap (LiftRelO R C) = LiftRelO (swap R) (swap C) := by
  funext x y
  rcases x with ⟨⟩ | ⟨hx, jx⟩ <;> rcases y with ⟨⟩ | ⟨hy, jy⟩ <;> rfl

/-- Definition of bisimilarity for weak sequences -/
@[simp]
def BisimO (R : WSeq α → WSeq α → Prop) : Option (α × WSeq α) → Option (α × WSeq α) → Prop :=
  LiftRelO (· = ·) R

theorem BisimO.imp {R S : WSeq α → WSeq α → Prop} (H : ∀ s t, R s t → S s t) {o p} :
    BisimO R o p → BisimO S o p :=
  LiftRelO.imp_right _ H

/-- Two weak sequences are `LiftRel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `LiftRel R` related. (This is a coinductive definition.) -/
def LiftRel (R : α → β → Prop) (s : WSeq α) (t : WSeq β) : Prop :=
  ∃ C : WSeq α → WSeq β → Prop,
    C s t ∧ ∀ {s t}, C s t → Computation.LiftRel (LiftRelO R C) (destruct s) (destruct t)

theorem liftRel_destruct {R : α → β → Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t → Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t)
  | ⟨R, h1, h2⟩ => by
    refine Computation.LiftRel.imp ?_ _ _ (h2 h1)
    apply LiftRelO.imp_right
    exact fun s' t' h' => ⟨R, h', @h2⟩

theorem liftRel_destruct_iff {R : α → β → Prop} {s : WSeq α} {t : WSeq β} :
    LiftRel R s t ↔ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) :=
  ⟨liftRel_destruct, fun h =>
    ⟨fun s t =>
      LiftRel R s t ∨ Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t),
      Or.inr h, fun {s t} h => by
      have h : Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct s) (destruct t) := by
        obtain h | h := h
        · exact liftRel_destruct h
        · assumption
      apply Computation.LiftRel.imp _ _ _ h
      intro a b
      apply LiftRelO.imp_right
      intro s t
      apply Or.inl⟩⟩

theorem LiftRel.swap_lem {R : α → β → Prop} {s1 s2} (h : LiftRel R s1 s2) :
    LiftRel (swap R) s2 s1 := by
  refine ⟨swap (LiftRel R), h, fun {s t} (h : LiftRel R t s) => ?_⟩
  rw [← LiftRelO.swap, Computation.LiftRel.swap]
  apply liftRel_destruct h

theorem LiftRel.swap (R : α → β → Prop) : swap (LiftRel R) = LiftRel (swap R) :=
  funext fun _ => funext fun _ => propext ⟨LiftRel.swap_lem, LiftRel.swap_lem⟩

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun s => by
  refine ⟨(· = ·), rfl, fun {s t} (h : s = t) => ?_⟩
  rw [← h]
  apply Computation.LiftRel.refl
  intro a
  rcases a with - | a
  · simp
  · cases a
    simp only [LiftRelO, and_true]
    apply H

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun s1 s2 (h : Function.swap (LiftRel R) s2 s1) => by rwa [LiftRel.swap, H.swap_eq] at h

theorem LiftRel.trans (R : α → α → Prop) (H : Transitive R) : Transitive (LiftRel R) :=
  fun s t u h1 h2 => by
  refine ⟨fun s u => ∃ t, LiftRel R s t ∧ LiftRel R t u, ⟨t, h1, h2⟩, fun {s u} h => ?_⟩
  rcases h with ⟨t, h1, h2⟩
  have h1 := liftRel_destruct h1
  have h2 := liftRel_destruct h2
  refine
    Computation.liftRel_def.2
      ⟨(Computation.terminates_of_liftRel h1).trans (Computation.terminates_of_liftRel h2),
        fun {a c} ha hc => ?_⟩
  rcases h1.left ha with ⟨b, hb, t1⟩
  have t2 := Computation.rel_of_liftRel h2 hb hc
  obtain - | a := a <;> obtain - | c := c
  · trivial
  · cases b
    · cases t2
    · cases t1
  · cases a
    rcases b with - | b
    · cases t1
    · cases b
      cases t2
  · obtain ⟨a, s⟩ := a
    rcases b with - | b
    · cases t1
    obtain ⟨b, t⟩ := b
    obtain ⟨c, u⟩ := c
    obtain ⟨ab, st⟩ := t1
    obtain ⟨bc, tu⟩ := t2
    exact ⟨H ab bc, t, st, tu⟩

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, @(LiftRel.symm R @symm), @(LiftRel.trans R @trans)⟩

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def Equiv : WSeq α → WSeq α → Prop :=
  LiftRel (· = ·)

@[inherit_doc] infixl:50 " ~ʷ " => Equiv

@[refl]
theorem Equiv.refl : ∀ s : WSeq α, s ~ʷ s :=
  LiftRel.refl (· = ·) Eq.refl

@[symm]
theorem Equiv.symm : ∀ {s t : WSeq α}, s ~ʷ t → t ~ʷ s :=
  @(LiftRel.symm (· = ·) (@Eq.symm _))

@[trans]
theorem Equiv.trans : ∀ {s t u : WSeq α}, s ~ʷ t → t ~ʷ u → s ~ʷ u :=
  @(LiftRel.trans (· = ·) (@Eq.trans _))

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

theorem destruct_congr {s t : WSeq α} :
    s ~ʷ t → Computation.LiftRel (BisimO (· ~ʷ ·)) (destruct s) (destruct t) :=
  liftRel_destruct

theorem destruct_congr_iff {s t : WSeq α} :
    s ~ʷ t ↔ Computation.LiftRel (BisimO (· ~ʷ ·)) (destruct s) (destruct t) :=
  liftRel_destruct_iff

open Computation

theorem liftRel_dropn_destruct {R : α → β → Prop} {s t} (H : LiftRel R s t) :
    ∀ n, Computation.LiftRel (LiftRelO R (LiftRel R)) (destruct (drop s n)) (destruct (drop t n))
  | 0 => liftRel_destruct H
  | n + 1 => by
    simp only [drop, destruct_tail]
    apply liftRel_bind
    · apply liftRel_dropn_destruct H n
    exact fun {a b} o =>
      match a, b, o with
      | none, none, _ => by simp
      | some (a, s), some (b, t), ⟨_, h2⟩ => by simpa [tail.aux] using liftRel_destruct h2

theorem exists_of_liftRel_left {R : α → β → Prop} {s t} (H : LiftRel R s t) {a} (h : a ∈ s) :
    ∃ b, b ∈ t ∧ R a b := by
  let ⟨n, h⟩ := exists_get?_of_mem h
  let ⟨some (_, s'), sd, rfl⟩ := Computation.exists_of_mem_map h
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (liftRel_dropn_destruct H n).left sd
  exact ⟨b, get?_mem (Computation.mem_map (Prod.fst.{v, v} <$> ·) td), ab⟩

theorem exists_of_liftRel_right {R : α → β → Prop} {s t} (H : LiftRel R s t) {b} (h : b ∈ t) :
    ∃ a, a ∈ s ∧ R a b := by rw [← LiftRel.swap] at H; exact exists_of_liftRel_left H h

@[simp]
theorem liftRel_nil (R : α → β → Prop) : LiftRel R nil nil := by
  simp [liftRel_destruct_iff]

@[simp]
theorem liftRel_cons (R : α → β → Prop) (a b s t) :
    LiftRel R (cons a s) (cons b t) ↔ R a b ∧ LiftRel R s t := by
  simp [liftRel_destruct_iff]

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (s t) : LiftRel R (think s) t ↔ LiftRel R s t := by
  rw [liftRel_destruct_iff, liftRel_destruct_iff]; simp

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (s t) : LiftRel R s (think t) ↔ LiftRel R s t := by
  rw [liftRel_destruct_iff, liftRel_destruct_iff]; simp

theorem cons_congr {s t : WSeq α} (a : α) (h : s ~ʷ t) : cons a s ~ʷ cons a t := by
  unfold Equiv; simpa using h

theorem think_equiv (s : WSeq α) : think s ~ʷ s := by unfold Equiv; simpa using Equiv.refl _

theorem think_congr {s t : WSeq α} (h : s ~ʷ t) : think s ~ʷ think t := by
  unfold Equiv; simpa using h

theorem head_congr : ∀ {s t : WSeq α}, s ~ʷ t → head s ~ head t := by
  suffices ∀ {s t : WSeq α}, s ~ʷ t → ∀ {o}, o ∈ head s → o ∈ head t from fun s t h o =>
    ⟨this h, this h.symm⟩
  intro s t h o ho
  rcases @Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
  rw [← dse]
  obtain ⟨l, r⟩ := destruct_congr h
  rcases l dsm with ⟨dt, dtm, dst⟩
  rcases ds with - | a <;> rcases dt with - | b
  · apply Computation.mem_map _ dtm
  · cases b
    cases dst
  · cases a
    cases dst
  · obtain ⟨a, s'⟩ := a
    obtain ⟨b, t'⟩ := b
    rw [dst.left]
    exact @Computation.mem_map _ _ (@Functor.map _ _ (α × WSeq α) _ Prod.fst)
      (some (b, t')) (destruct t) dtm

theorem flatten_equiv {c : Computation (WSeq α)} {s} (h : s ∈ c) : flatten c ~ʷ s := by
  apply Computation.memRecOn h
  · simp [Equiv.refl]
  · intro s'
    apply Equiv.trans
    simp [think_equiv]

theorem liftRel_flatten {R : α → β → Prop} {c1 : Computation (WSeq α)} {c2 : Computation (WSeq β)}
    (h : c1.LiftRel (LiftRel R) c2) : LiftRel R (flatten c1) (flatten c2) :=
  let S s t := ∃ c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (LiftRel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩, fun {s t} h =>
    match s, t, h with
    | _, _, ⟨c1, c2, rfl, rfl, h⟩ => by
      simp only [destruct_flatten]; apply liftRel_bind _ _ h
      intro a b ab; apply Computation.LiftRel.imp _ _ _ (liftRel_destruct ab)
      intro a b; apply LiftRelO.imp_right
      intro s t h; refine ⟨Computation.pure s, Computation.pure t, ?_, ?_, ?_⟩ <;> simp [h]⟩

theorem flatten_congr {c1 c2 : Computation (WSeq α)} :
    Computation.LiftRel Equiv c1 c2 → flatten c1 ~ʷ flatten c2 :=
  liftRel_flatten

theorem tail_congr {s t : WSeq α} (h : s ~ʷ t) : tail s ~ʷ tail t := by
  apply flatten_congr
  dsimp only [(· <$> ·)]; rw [← Computation.bind_pure, ← Computation.bind_pure]
  apply liftRel_bind _ _ (destruct_congr h)
  intro a b h; simp only [comp_apply, liftRel_pure]
  rcases a with - | a <;> rcases b with - | b
  · trivial
  · cases h
  · cases a
    cases h
  · obtain ⟨a, s'⟩ := a
    obtain ⟨b, t'⟩ := b
    exact h.right

theorem dropn_congr {s t : WSeq α} (h : s ~ʷ t) (n) : drop s n ~ʷ drop t n := by
  induction n <;> simp [*, tail_congr, drop]

theorem get?_congr {s t : WSeq α} (h : s ~ʷ t) (n) : get? s n ~ get? t n :=
  head_congr (dropn_congr h _)

theorem mem_congr {s t : WSeq α} (h : s ~ʷ t) (a) : a ∈ s ↔ a ∈ t :=
  suffices ∀ {s t : WSeq α}, s ~ʷ t → a ∈ s → a ∈ t from ⟨this h, this h.symm⟩
  fun {_ _} h as =>
  let ⟨_, hn⟩ := exists_get?_of_mem as
  get?_mem ((get?_congr h _ _).1 hn)

theorem Equiv.ext {s t : WSeq α} (h : ∀ n, get? s n ~ get? t n) : s ~ʷ t :=
  ⟨fun s t => ∀ n, get? s n ~ get? t n, h, fun {s t} h => by
    refine liftRel_def.2 ⟨?_, ?_⟩
    · rw [← head_terminates_iff, ← head_terminates_iff]
      exact terminates_congr (h 0)
    · intro a b ma mb
      rcases a with - | a <;> rcases b with - | b
      · trivial
      · injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb))
      · injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb))
      · obtain ⟨a, s'⟩ := a
        obtain ⟨b, t'⟩ := b
        injection mem_unique (Computation.mem_map _ ma) ((h 0 _).2 (Computation.mem_map _ mb)) with
          ab
        refine ⟨ab, fun n => ?_⟩
        refine
          (get?_congr (flatten_equiv (Computation.mem_map _ ma)) n).symm.trans
            ((?_ : get? (tail s) n ~ get? (tail t) n).trans
              (get?_congr (flatten_equiv (Computation.mem_map _ mb)) n))
        rw [get?_tail, get?_tail]
        apply h⟩

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) :
    LiftRel S (map f1 s1) (map f2 s2) :=
  ⟨fun s1 s2 => ∃ s t, s1 = map f1 s ∧ s2 = map f2 t ∧ LiftRel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun {s1 s2} h =>
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_map]
      apply Computation.liftRel_map _ _ (liftRel_destruct h)
      intro o p h
      rcases o with - | a <;> rcases p with - | b
      · simp
      · cases b; cases h
      · cases a; cases h
      · obtain ⟨a, s⟩ := a; obtain ⟨b, t⟩ := b
        obtain ⟨r, h⟩ := h
        exact ⟨h2 r, s, rfl, t, rfl, h⟩⟩

theorem map_congr (f : α → β) {s t : WSeq α} (h : s ~ʷ t) : map f s ~ʷ map f t :=
  liftRel_map _ _ h fun {_ _} => congr_arg _

theorem liftRel_append (R : α → β → Prop) {s1 s2 : WSeq α} {t1 t2 : WSeq β} (h1 : LiftRel R s1 t1)
    (h2 : LiftRel R s2 t2) : LiftRel R (append s1 s2) (append t1 t2) :=
  ⟨fun s t => LiftRel R s t ∨ ∃ s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ LiftRel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩, fun {s t} h =>
    match s, t, h with
    | s, t, Or.inl h => by
      apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h)
      intro a b; apply LiftRelO.imp_right
      intro s t; apply Or.inl
    | _, _, Or.inr ⟨s1, t1, rfl, rfl, h⟩ => by
      simp only [exists_and_left, destruct_append]
      apply Computation.liftRel_bind _ _ (liftRel_destruct h)
      intro o p h
      rcases o with - | a <;> rcases p with - | b
      · simp only [destruct_append.aux]
        apply Computation.LiftRel.imp _ _ _ (liftRel_destruct h2)
        intro a b
        apply LiftRelO.imp_right
        intro s t
        apply Or.inl
      · cases b; cases h
      · cases a; cases h
      · obtain ⟨a, s⟩ := a; obtain ⟨b, t⟩ := b
        obtain ⟨r, h⟩ := h
        simpa using ⟨r, Or.inr ⟨s, rfl, t, rfl, h⟩⟩⟩

theorem liftRel_join.lem (R : α → β → Prop) {S T} {U : WSeq α → WSeq β → Prop}
    (ST : LiftRel (LiftRel R) S T)
    (HU :
      ∀ s1 s2,
        (∃ s t S T,
            s1 = append s (join S) ∧
              s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T) →
          U s1 s2)
    {a} (ma : a ∈ destruct (join S)) : ∃ b, b ∈ destruct (join T) ∧ LiftRelO R U a b := by
  obtain ⟨n, h⟩ := exists_results_of_mem ma; clear ma; revert S T ST a
  induction n using Nat.strongRecOn with | _ n IH
  intro S T ST a ra; simp only [destruct_join] at ra
  exact
    let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra
    let ⟨p, mT, rop⟩ := Computation.exists_of_liftRel_left (liftRel_destruct ST) rs1.mem
    match o, p, rop, rs1, rs2, mT with
    | none, none, _, _, rs2, mT => by
      simp only [destruct_join]
      exact ⟨none, mem_bind mT (ret_mem _), by rw [eq_of_pure_mem rs2.mem]; trivial⟩
    | some (s, S'), some (t, T'), ⟨st, ST'⟩, _, rs2, mT => by
      simp? [destruct_append]  at rs2  says simp only [destruct_join.aux, destruct_append] at rs2
      exact
        let ⟨k1, rs3, ek⟩ := of_results_think rs2
        let ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3
        let ⟨p', mt, rop'⟩ := Computation.exists_of_liftRel_left (liftRel_destruct st) rs4.mem
        match o', p', rop', rs4, rs5, mt with
        | none, none, _, _, rs5', mt => by
          have : n1 < n := by
            rw [en, ek, ek1]
            apply lt_of_lt_of_le _ (Nat.le_add_right _ _)
            apply Nat.lt_succ_of_le (Nat.le_add_right _ _)
          let ⟨ob, mb, rob⟩ := IH _ this ST' rs5'
          refine ⟨ob, ?_, rob⟩
          · simp +unfoldPartialApp only [destruct_join, destruct_join.aux]
            apply mem_bind mT
            simp only [destruct_append]
            apply think_mem
            apply mem_bind mt
            exact mb
        | some (a, s'), some (b, t'), ⟨ab, st'⟩, _, rs5, mt => by
          simp?  at rs5  says simp only [destruct_append.aux] at rs5
          refine ⟨some (b, append t' (join T')), ?_, ?_⟩
          · simp +unfoldPartialApp only [destruct_join, destruct_join.aux]
            apply mem_bind mT
            simp only [destruct_append]
            apply think_mem
            apply mem_bind mt
            apply ret_mem
          rw [eq_of_pure_mem rs5.mem]
          exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩

theorem liftRel_join (R : α → β → Prop) {S : WSeq (WSeq α)} {T : WSeq (WSeq β)}
    (h : LiftRel (LiftRel R) S T) : LiftRel R (join S) (join T) :=
  ⟨fun s1 s2 =>
    ∃ s t S T,
      s1 = append s (join S) ∧ s2 = append t (join T) ∧ LiftRel R s t ∧ LiftRel (LiftRel R) S T,
    ⟨nil, nil, S, T, by simp, by simp, by simp, h⟩, fun {s1 s2} ⟨s, t, S, T, h1, h2, st, ST⟩ => by
    rw [h1, h2]; rw [destruct_append, destruct_append]
    apply Computation.liftRel_bind _ _ (liftRel_destruct st)
    exact fun {o p} h =>
      match o, p, h with
      | some (a, s), some (b, t), ⟨h1, h2⟩ => by
        simpa using ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
      | none, none, _ => by
        -- We do not `dsimp` with `LiftRelO` since `liftRel_join.lem` uses `LiftRelO`.
        dsimp only [destruct_append.aux, Computation.LiftRel]; constructor
        · intro
          apply liftRel_join.lem _ ST fun _ _ => id
        · intro b mb
          rw [← LiftRelO.swap]
          apply liftRel_join.lem (swap R)
          · rw [← LiftRel.swap R, ← LiftRel.swap]
            apply ST
          · rw [← LiftRel.swap R, ← LiftRel.swap (LiftRel R)]
            exact fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ => ⟨t, s, T, S, h2, h1, st, ST⟩
          · exact mb⟩

theorem join_congr {S T : WSeq (WSeq α)} (h : LiftRel Equiv S T) : join S ~ʷ join T :=
  liftRel_join _ h

theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : WSeq α} {s2 : WSeq β}
    {f1 : α → WSeq γ} {f2 : β → WSeq δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  liftRel_join _ (liftRel_map _ _ h1 @h2)

theorem bind_congr {s1 s2 : WSeq α} {f1 f2 : α → WSeq β} (h1 : s1 ~ʷ s2) (h2 : ∀ a, f1 a ~ʷ f2 a) :
    bind s1 f1 ~ʷ bind s2 f2 :=
  liftRel_bind _ _ h1 fun {a b} h => by rw [h]; apply h2

@[simp]
theorem join_ret (s : WSeq α) : join (ret s) ~ʷ s := by simpa [ret] using think_equiv _

@[simp]
theorem join_map_ret (s : WSeq α) : join (map ret s) ~ʷ s := by
  refine ⟨fun s1 s2 => join (map ret s2) = s1, rfl, ?_⟩
  intro s' s h; rw [← h]
  apply liftRel_rec fun c1 c2 => ∃ s, c1 = destruct (join (map ret s)) ∧ c2 = destruct s
  · exact fun {c1 c2} h =>
      match c1, c2, h with
      | _, _, ⟨s, rfl, rfl⟩ => by
        clear h
        have (s : WSeq α) : ∃ s' : WSeq α,
            (map ret s).join.destruct = (map ret s').join.destruct ∧ destruct s = s'.destruct :=
          ⟨s, rfl, rfl⟩
        induction s using WSeq.recOn <;> simp [ret, this]
  · exact ⟨s, rfl, rfl⟩

@[simp]
theorem join_append (S T : WSeq (WSeq α)) : join (append S T) ~ʷ append (join S) (join T) := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
      ⟨nil, S, T, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        ∃ (s : WSeq α) (S T : _),
          c1 = destruct (append s (join (append S T))) ∧
            c2 = destruct (append s (append (join S) (join T))))
      _ _ _
      (let ⟨s, S, T, h1, h2⟩ := h
      ⟨s, S, T, congr_arg destruct h1, congr_arg destruct h2⟩)
  rintro c1 c2 ⟨s, S, T, rfl, rfl⟩
  induction s using WSeq.recOn with
  | nil =>
    induction S using WSeq.recOn with
    | nil =>
      simp only [nil_append, join_nil]
      induction T using WSeq.recOn with
      | nil => simp
      | cons s T =>
        simp only [join_cons, destruct_think, Computation.destruct_think, liftRelAux_inr_inr]
        refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
      | think T =>
        simp only [join_think, destruct_think, Computation.destruct_think, liftRelAux_inr_inr]
        refine ⟨nil, nil, T, ?_, ?_⟩ <;> simp
    | cons s S => simpa using ⟨s, S, T, rfl, rfl⟩
    | think S => refine ⟨nil, S, T, ?_, ?_⟩ <;> simp
  | cons a s => simpa using ⟨s, S, T, rfl, rfl⟩
  | think s => simpa using ⟨s, S, T, rfl, rfl⟩

@[simp]
theorem bind_ret (f : α → β) (s) : bind s (ret ∘ f) ~ʷ map f s := by
  dsimp [bind]
  rw [map_comp]
  apply join_map_ret

@[simp]
theorem ret_bind (a : α) (f : α → WSeq β) : bind (ret a) f ~ʷ f a := by simp [bind]

@[simp]
theorem join_join (SS : WSeq (WSeq (WSeq α))) : join (join SS) ~ʷ join (map join SS) := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        ∃ s S SS,
          c1 = destruct (append s (join (append S (join SS)))) ∧
            c2 = destruct (append s (append (join S) (join (map join SS)))))
      _ (destruct s1) (destruct s2)
      (let ⟨s, S, SS, h1, h2⟩ := h
      ⟨s, S, SS, by simp [h1], by simp [h2]⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | _, _, ⟨s, S, SS, rfl, rfl⟩ => by
      clear h
      induction s using WSeq.recOn with
      | nil =>
        induction S using WSeq.recOn with
        | nil =>
          simp only [nil_append, join_nil]
          induction SS using WSeq.recOn with
          | nil => simp
          | cons S SS => refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
          | think SS => refine ⟨nil, nil, SS, ?_, ?_⟩ <;> simp
        | cons s S => simpa using ⟨s, S, SS, rfl, rfl⟩
        | think S => refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
      | cons a s => simpa using ⟨s, S, SS, rfl, rfl⟩
      | think s => simpa using ⟨s, S, SS, rfl, rfl⟩

@[simp]
theorem bind_assoc_comp (s : WSeq α) (f : α → WSeq β) (g : β → WSeq γ) :
    bind (bind s f) g ~ʷ bind s ((fun y : WSeq β => bind y g) ∘ f) := by
  simp only [bind, map_join]
  rw [← map_comp f (map g), ← Function.comp_def, comp_assoc, map_comp (map g ∘ f) join s]
  exact join_join (map (map g ∘ f) s)

@[simp]
theorem bind_assoc (s : WSeq α) (f : α → WSeq β) (g : β → WSeq γ) :
    bind (bind s f) g ~ʷ bind s fun x : α => bind (f x) g := by
  exact bind_assoc_comp s f g

end Stream'.WSeq
