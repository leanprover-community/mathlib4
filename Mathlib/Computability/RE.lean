/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Computable and Recursively Enumerable Predicates

This file defines computable (`ComputablePred`) and recursively enumerable (`REPred`)
predicates. It also provides basic closure properties and Post's theorem on the
equivalence of recursive, r.e., and co-r.e. sets.
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable

namespace Nat.Partrec

open Computable Part

theorem merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) :
    ∃ h, Nat.Partrec h ∧
      ∀ a, (∀ x ∈ h a, x ∈ f a ∨ x ∈ g a) ∧ ((h a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  obtain ⟨cg, rfl⟩ := Code.exists_code.1 hg
  have : Nat.Partrec fun n => Nat.rfindOpt fun k => cf.evaln k n <|> cg.evaln k n :=
    Partrec.nat_iff.1
      (Partrec.rfindOpt <|
        Primrec.option_orElse.to_comp.comp
          (Code.primrec_evaln.to_comp.comp <| (snd.pair (const cf)).pair fst)
          (Code.primrec_evaln.to_comp.comp <| (snd.pair (const cg)).pair fst))
  refine ⟨_, this, fun n => ?_⟩
  have : ∀ x ∈ rfindOpt fun k ↦ Code.evaln k cf n <|> Code.evaln k cg n,
      x ∈ Code.eval cf n ∨ x ∈ Code.eval cg n := by
    intro x h
    obtain ⟨k, e⟩ := Nat.rfindOpt_spec h
    rw [Option.mem_def, Option.orElse_eq_some, ← Option.mem_def, ← Option.mem_def] at e
    obtain e | ⟨-, e⟩ := e <;> simp [Code.evaln_sound e]
  refine ⟨this, fun h ↦ (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, fun h ↦ ?_⟩
  rw [Nat.rfindOpt_dom]
  simp only [dom_iff_mem, Code.evaln_complete, Option.mem_def] at h
  obtain ⟨x, k, e⟩ | ⟨x, k, e⟩ := h
  · exact ⟨k, x, by simp [e]⟩
  · refine ⟨k, ?_⟩
    rcases cf.evaln k n with - | y
    · exact ⟨x, by simp [e]⟩
    · exact ⟨y, by simp⟩

end Nat.Partrec

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable Part

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem merge' {f g : α →. σ} (hf : Partrec f) (hg : Partrec g) :
    ∃ k : α →. σ,
      Partrec k ∧ ∀ a, (∀ x ∈ k a, x ∈ f a ∨ x ∈ g a) ∧ ((k a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  let ⟨k, hk, H⟩ := Nat.Partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg)
  let k' (a : α) := (k (encode a)).bind fun n => (decode (α := σ) n : Part σ)
  refine
    ⟨k', ((nat_iff.2 hk).comp Computable.encode).bind (Computable.decode.ofOption.comp snd).to₂,
      fun a => ?_⟩
  have : ∀ x ∈ k' a, x ∈ f a ∨ x ∈ g a := by
    intro x h'
    simp only [k', mem_coe, mem_bind_iff, Option.mem_def] at h'
    obtain ⟨n, hn, hx⟩ := h'
    have := (H _).1 _ hn
    simp only [decode₂_encode, coe_some, bind_some, mem_map_iff] at this
    obtain ⟨a', ha, rfl⟩ | ⟨a', ha, rfl⟩ := this <;> simp only [encodek, Option.some_inj] at hx <;>
      rw [hx] at ha
    · exact Or.inl ha
    · exact Or.inr ha
  refine ⟨this, ⟨fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, ?_⟩⟩
  intro h
  rw [bind_dom]
  have hk : (k (encode a)).Dom :=
    (H _).2.2 (by simpa only [encodek₂, bind_some, coe_some] using h)
  exists hk
  simp only [mem_map_iff, mem_coe, mem_bind_iff, Option.mem_def] at H
  obtain ⟨a', _, y, _, e⟩ | ⟨a', _, y, _, e⟩ := (H _).1 _ ⟨hk, rfl⟩ <;>
    simp only [e.symm, encodek, coe_some, some_dom]

theorem merge {f g : α →. σ} (hf : Partrec f) (hg : Partrec g)
    (H : ∀ (a), ∀ x ∈ f a, ∀ y ∈ g a, x = y) :
    ∃ k : α →. σ, Partrec k ∧ ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a :=
  let ⟨k, hk, K⟩ := merge' hf hg
  ⟨k, hk, fun a x =>
    ⟨(K _).1 _, fun h => by
      have : (k a).Dom := (K _).2.2 (h.imp Exists.fst Exists.fst)
      refine ⟨this, ?_⟩
      rcases h with h | h <;> rcases (K _).1 _ ⟨this, rfl⟩ with h' | h'
      · exact mem_unique h' h
      · exact (H _ _ h _ h').symm
      · exact H _ _ h' _ h
      · exact mem_unique h' h⟩⟩

theorem cond {c : α → Bool} {f : α →. σ} {g : α →. σ} (hc : Computable c) (hf : Partrec f)
    (hg : Partrec g) : Partrec fun a => cond (c a) (f a) (g a) :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.encode).bind
    ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq
    fun a => by cases c a <;> simp [ef, eg, encodek]

nonrec theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Partrec₂ h) : @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (sumCasesOn hf (const true).to₂ (const false).to₂)
          (sumCasesOn_left hf (option_some_iff.2 hg).to₂ (const Option.none).to₂)
          (sumCasesOn_right hf (const Option.none).to₂ (option_some_iff.2 hh).to₂)).of_eq
      fun a => by cases f a <;> simp only [Bool.cond_true, Bool.cond_false]

end Partrec

/-- A computable predicate is one whose indicator function is computable. -/
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ (_ : DecidablePred p), Computable fun a => decide (p a)

section decide

variable {α} [Primcodable α]

protected lemma ComputablePred.decide {p : α → Prop} [DecidablePred p] (hp : ComputablePred p) :
    Computable (fun a => decide (p a)) := by
  convert hp.choose_spec

lemma Computable.computablePred {p : α → Prop} [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) : ComputablePred p :=
  ⟨inferInstance, hp⟩

lemma computablePred_iff_computable_decide {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ Computable (fun a => decide (p a)) where
  mp := ComputablePred.decide
  mpr := Computable.computablePred

lemma PrimrecPred.computablePred {α} [Primcodable α] {p : α → Prop} :
    (hp : PrimrecPred p) → ComputablePred p
  | ⟨_, hp⟩ => hp.to_comp.computablePred

end decide

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
-/
def REPred {α} [Primcodable α] (p : α → Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()

theorem REPred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : REPred p) (H : ∀ a, p a ↔ q a) :
    REPred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) :
    REPred fun a => (f a).Dom :=
  (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]

theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : ComputablePred p)
    (H : ∀ a, p a ↔ q a) : ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

namespace Computable

/-- If `P` is computable, and if for every `x` there exists an `n` such that `P x n` holds,
then the function mapping `x` to the minimal such `n` (using `Nat.find`) is computable.
This formally bridges `Partrec.rfind` with total unbounded search. -/
lemma find {α : Type*} [Primcodable α] {P : α → ℕ → Prop} [DecidableRel P]
    (hP_comp : ComputablePred (fun p : α × ℕ => P p.1 p.2)) (hP_ex : ∀ x, ∃ n, P x n) :
    Computable (fun x => Nat.find (hP_ex x)) := by
  have h : Partrec (fun x ↦ Nat.rfind fun n => Part.some (decide (P x n))) :=
    Partrec.rfind hP_comp.decide.partrec
  refine h.of_eq_tot fun x ↦ ?_
  simp +contextual [Nat.find_spec]

end Computable

namespace ComputablePred

variable {α : Type*} [Primcodable α]

open Nat.Partrec (Code)

open Nat.Partrec.Code Computable

theorem computable_iff {p : α → Prop} :
    ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => (f a : Prop) :=
  ⟨fun ⟨_, h⟩ => ⟨_, h, funext fun _ => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩

protected theorem not {p : α → Prop} :
    (hp : ComputablePred p) → ComputablePred fun a => ¬p a
  | ⟨_, hp⟩ => Computable.computablePred <| Primrec.not.to_comp.comp hp |>.of_eq <| by simp

/-- The computable functions are closed under if-then-else definitions
with computable predicates. -/
theorem ite {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
    {c : ℕ → Prop} [DecidablePred c] (hc : ComputablePred c) :
    Computable fun k ↦ if c k then f₁ k else f₂ k := by
  simpa [Bool.cond_decide] using hc.decide.cond hf₁ hf₂

theorem to_re {p : α → Prop} (hp : ComputablePred p) : REPred p := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only []
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

-- Post's theorem on the equivalence of r.e., co-r.e. sets and
-- computable sets. The assumption that p is decidable is required
-- unless we assume Markov's principle or LEM.
set_option linter.unusedDecidableInType false in
theorem computable_iff_re_compl_re {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a :=
  ⟨fun h => ⟨h.to_re, h.not.to_re⟩, fun ⟨h₁, h₂⟩ =>
    ⟨‹_›, by
      obtain ⟨k, pk, hk⟩ :=
        Partrec.merge (h₁.map (Computable.const true).to₂) (h₂.map (Computable.const false).to₂)
        (by
          intro a x hx y hy
          simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop,
            and_true, exists_const] at hx hy
          cases hy.1 hx.1)
      refine Partrec.of_eq pk fun n => Part.eq_some_iff.2 ?_
      rw [hk]
      simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop, and_true,
        true_eq_decide_iff, and_self, exists_const, false_eq_decide_iff]
      apply Decidable.em⟩⟩

theorem computable_iff_re_compl_re' {p : α → Prop} :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a := by
  classical exact computable_iff_re_compl_re

end ComputablePred
