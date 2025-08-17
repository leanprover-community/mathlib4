/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Set.Subsingleton

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

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
  have : ∀ x ∈ rfindOpt fun k ↦ HOrElse.hOrElse (Code.evaln k cf n) fun _x ↦ Code.evaln k cg n,
      x ∈ Code.eval cf n ∨ x ∈ Code.eval cg n := by
    intro x h
    obtain ⟨k, e⟩ := Nat.rfindOpt_spec h
    revert e
    simp only [Option.mem_def]
    rcases e' : cf.evaln k n with - | y <;> simp <;> intro e
    · exact Or.inr (Code.evaln_sound e)
    · subst y
      exact Or.inl (Code.evaln_sound e')
  refine ⟨this, ⟨fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, ?_⟩⟩
  intro h
  rw [Nat.rfindOpt_dom]
  simp only [dom_iff_mem, Code.evaln_complete, Option.mem_def] at h
  obtain ⟨x, k, e⟩ | ⟨x, k, e⟩ := h
  · refine ⟨k, x, ?_⟩
    simp only [e, Option.orElse_some, Option.mem_def, Option.orElse_eq_orElse]
  · refine ⟨k, ?_⟩
    rcases cf.evaln k n with - | y
    · exact ⟨x, by simp only [e, Option.mem_def, Option.orElse_eq_orElse, Option.orElse_none]⟩
    · exact ⟨y, by simp only [Option.orElse_eq_orElse, Option.orElse_some, Option.mem_def]⟩

/-- If a partial recursive function on pairs depends only on the first component,
it can be represented as a partial recursive function omitting the second argument. -/
lemma projection {f : ℕ →. ℕ} (hf : Nat.Partrec f)
    (unif : ∀ {m n₁ n₂ a₁ a₂ : ℕ}, a₁ ∈ f (m.pair n₁) → a₂ ∈ f (m.pair n₂) → a₁ = a₂) :
    ∃ g : ℕ →. ℕ, Nat.Partrec g ∧ ∀ a m, (a ∈ g m ↔ ∃ z, a ∈ f (m.pair z)) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  let F : ℕ → ℕ → Option ℕ := fun m n ↦
    Nat.rec .none (fun x ih ↦ ih.casesOn (cf.evaln n (m.pair x)) .some) n
  have : Primrec₂ F := .to₂
    <| Primrec.nat_rec' Primrec.snd (.const Option.none)
      (Primrec.option_casesOn (Primrec.snd.comp .snd)
        (Code.primrec_evaln.comp
          <| _root_.Primrec.pair
            (_root_.Primrec.pair (Primrec.snd.comp .fst) (.const cf))
            (Primrec₂.natPair.comp (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)))
        (Primrec.option_some.comp .snd).to₂).to₂
  have hF : ∀ {m n a}, a ∈ F m n ↔ ∃ x < n, a ∈ cf.evaln n (m.pair x) := by
    suffices ∀ m n s a : ℕ,
      Nat.rec Option.none
        (fun x ih ↦ ih.casesOn (cf.evaln s (m.pair x)) Option.some) n = Option.some a ↔
      ∃ x < n, cf.evaln s (m.pair x) = .some a from fun m n a ↦ this m n n a
    intro m n s a
    induction n generalizing a
    case zero => simp
    case succ n ih =>
      cases hC :
        @Nat.rec (fun _ ↦ Option ℕ) Option.none
          (fun x ih ↦ ih.rec (cf.evaln s (m.pair x)) Option.some) n
      · simp only [hC]
        grind
      · simp only [hC, Option.some.injEq]
        constructor
        · grind
        · rintro ⟨x, _, Hx⟩
          rcases (ih _).mp hC with ⟨y, _, Hy⟩
          exact unif (Nat.Partrec.Code.evaln_sound Hy) (Nat.Partrec.Code.evaln_sound Hx)
  have mono : ∀ {a m n₁ n₂ : ℕ}, n₁ ≤ n₂ → a ∈ F m n₁ → a ∈ F m n₂ := by
    intro a m n₁ n₂ hn h₁
    rcases hF.mp h₁ with ⟨x, hx, H⟩
    apply hF.mpr ⟨x, lt_of_lt_of_le hx hn, Code.evaln_mono hn H⟩
  have : Partrec (fun m ↦ rfindOpt (F m)) := Partrec.nat_iff.1 <| Partrec.rfindOpt <| this.to_comp
  refine ⟨_, this, fun a m ↦ ?_⟩
  rw [Nat.rfindOpt_mono mono]
  constructor
  · rintro ⟨n, H⟩
    obtain ⟨x, _, H⟩ := hF.mp H
    exact ⟨x, Code.evaln_sound H⟩
  · rintro ⟨x, H⟩
    obtain ⟨s, Hs⟩ := Code.evaln_complete.mp H
    exact ⟨max s x + 1, (@hF m (max s x + 1) a).mpr
      ⟨x, by simp [Nat.lt_succ],
        Code.evaln_mono (le_trans (Nat.le_max_left s x) (le_add_right (max s x) 1)) Hs⟩⟩

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

@[deprecated (since := "2025-02-21")] alias sum_casesOn := Partrec.sumCasesOn

lemma projection {f : α → β →. γ} (hf : Partrec₂ f)
    (unif : ∀ {a b₁ b₂ c₁ c₂}, c₁ ∈ f a b₁ → c₂ ∈ f a b₂ → c₁ = c₂) :
    ∃ g : α →. γ, Partrec g ∧ ∀ c a, c ∈ g a ↔ ∃ b, c ∈ f a b := by
  have := Nat.Partrec.projection (Partrec.bind_decode₂_iff.mp hf)
    (by intro m n₁ n₂ c₁ c₂; simp [decode₂_eq_some]; aesop)
  rcases this with ⟨g, hg, H⟩
  let g' : α →. γ := fun a ↦ (g (encode a)).bind fun n ↦ decode (α := γ) n
  refine ⟨g',
    ((nat_iff.2 hg).comp Computable.encode).bind
    (Computable.decode.ofOption.comp Computable.snd).to₂, ?_⟩
  have H : ∀ {c a : ℕ}, c ∈ g a ↔ ∃ a' b, encode a' = a ∧ ∃ c' ∈ f a' b, encode c' = c := by
    have H : ∀ c a : ℕ,
      c ∈ g a ↔ ∃ z a' b, (encode a' = a ∧ encode b = z) ∧ ∃ c' ∈ f a' b, encode c' = c := by
      simpa [Encodable.decode₂_eq_some] using H
    intro c a
    constructor <;> grind
  intro c a
  suffices (∃ c' ∈ g (encode a), decode c' = Option.some c) ↔ ∃ b, c ∈ f a b by simpa [g']
  constructor
  · rintro ⟨c', h, hc⟩
    rcases H.mp h with ⟨a, b, ae, c, habc, rfl⟩;
    rcases by simpa using hc
    rcases Encodable.encode_inj.mp ae
    exact ⟨b, habc⟩
  · rintro ⟨b, habc⟩
    exact ⟨encode c, H.mpr ⟨a, b, rfl, c, habc, rfl⟩, by simp⟩

end Partrec

/-- A computable predicate is one whose indicator function is computable. -/
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ _ : DecidablePred p, Computable fun a => decide (p a)

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
-/
def REPred {α} [Primcodable α] (p : α → Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()

@[deprecated (since := "2025-02-06")] alias RePred := REPred

theorem REPred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : REPred p) (H : ∀ a, p a ↔ q a) :
    REPred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

@[deprecated (since := "2025-02-06")] alias RePred.of_eq := REPred.of_eq

theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) :
    REPred fun a => (f a).Dom :=
  (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]

theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : ComputablePred p)
    (H : ∀ a, p a ↔ q a) : ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

namespace REPred

variable {α β : Type*} [Primcodable α] [Primcodable β] {p q : α → Prop}

@[simp] protected lemma const (p : Prop) : REPred fun _ : α ↦ p := by
  by_cases h : p
  · simpa [h] using Partrec.some.dom_re
  · simpa [h] using (Partrec.none (α := α) (σ := α)).dom_re

lemma _root_.rePred_iff : REPred p ↔ ∃ f : α →. Unit, Partrec f ∧ p = fun x ↦ (f x).Dom :=
  ⟨fun h ↦ ⟨_, h, by ext x; simp [Part.assert]⟩, by rintro ⟨f, hf, rfl⟩; exact hf.dom_re⟩

lemma inter : REPred p → REPred q → REPred fun x ↦ p x ∧ q x := by
  simp_rw [rePred_iff]
  rintro ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  let h : α →. Unit := fun x ↦ (f x).bind fun _ ↦ (g x).map fun _ ↦ ()
  refine ⟨fun x ↦ (f x).bind fun _ ↦ (g x).map fun _ ↦ (), ?_, by funext x; simp⟩
  exact hf.bind <| .to₂ <| .map (hg.comp .fst) (Computable.const ()).to₂

lemma union : REPred p → REPred q → REPred fun x ↦ p x ∨ q x := by
  simp_rw [rePred_iff]
  rintro ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  rcases hf.merge hg (by intro a x; simp) with ⟨k, hk, h⟩
  exact ⟨k, hk, by funext x; simp [Part.dom_iff_mem, h, Unique.exists_iff]⟩

lemma projection {p : α × β → Prop} : REPred p → REPred fun x ↦ ∃ y, p (x, y) := by
  simp_rw [rePred_iff]
  rintro ⟨f, hf, rfl⟩
  have : Partrec₂ fun a b ↦ f (a, b) := hf.comp <| Computable.pair .fst .snd
  obtain ⟨g, hg, Hg⟩ := Partrec.projection this (by simp)
  exact ⟨g, hg, by funext x; simp [Part.dom_iff_mem, exists_comm (β := Unit), Hg]⟩

lemma comp {f : α → β} (hf : Computable f) {p : β → Prop} :
    REPred p → REPred fun x ↦ p (f x) := by
  simp_rw [rePred_iff]
  rintro ⟨p, pp, rfl⟩
  exact ⟨_, pp.comp hf, by ext x; simp⟩

end REPred

namespace ComputablePred

variable {α : Type*} [Primcodable α]

open Nat.Partrec (Code)

open Nat.Partrec.Code Computable

theorem computable_iff {p : α → Prop} :
    ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => (f a : Prop) :=
  ⟨fun ⟨_, h⟩ => ⟨_, h, funext fun _ => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩

protected theorem not {p : α → Prop} (hp : ComputablePred p) : ComputablePred fun a => ¬p a := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  exact
    ⟨by infer_instance,
      (cond hf (const false) (const true)).of_eq fun n => by
        simp only [Bool.not_eq_true]
        cases f n <;> rfl⟩

/-- The computable functions are closed under if-then-else definitions
with computable predicates. -/
theorem ite {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
    {c : ℕ → Prop} [DecidablePred c] (hc : ComputablePred c) :
    Computable fun k ↦ if c k then f₁ k else f₂ k := by
  simp_rw [← Bool.cond_decide]
  obtain ⟨inst, hc⟩ := hc
  convert hc.cond hf₁ hf₂

theorem to_re {p : α → Prop} (hp : ComputablePred p) : REPred p := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only []
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

/-- **Rice's Theorem** -/
theorem rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C := by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c ∈ C
  · simp only [H, if_true] at e
    change (fun b => g b) ∈ C
    rwa [← e]
  · simp only [H, if_false] at e
    rw [e] at H
    contradiction

theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ := by
  classical exact
      have hC : ∀ f, f ∈ C ↔ eval f ∈ eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C0
            (hC _).2 <|
              rice (eval '' C) (h.of_eq hC)
                (Partrec.nat_iff.1 <| eval_part.comp (const cf) Computable.id)
                (Partrec.nat_iff.1 <| eval_part.comp (const cg) Computable.id) ((hC _).1 fC),
        fun h => by {
          obtain rfl | rfl := h <;> simpa [ComputablePred, Set.mem_empty_iff_false] using
            Computable.const _}⟩

/-- The Halting problem is recursively enumerable -/
theorem halting_problem_re (n) : REPred fun c => (eval c n).Dom :=
  (eval_part.comp Computable.id (Computable.const _)).dom_re

/-- The **Halting problem** is not computable -/
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom
  | h => rice { f | (f n).Dom } h Nat.Partrec.zero Nat.Partrec.none trivial

-- Post's theorem on the equivalence of r.e., co-r.e. sets and
-- computable sets. The assumption that p is decidable is required
-- unless we assume Markov's principle or LEM.
-- @[nolint decidable_classical]
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

theorem halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom
  | h => halting_problem _ <| computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩

end ComputablePred

namespace Nat

open Vector Part

/-- A simplified basis for `Partrec`. -/
inductive Partrec' : ∀ {n}, (List.Vector ℕ n →. ℕ) → Prop
  | prim {n f} : @Primrec' n f → @Partrec' n f
  | comp {m n f} (g : Fin n → List.Vector ℕ m →. ℕ) :
    Partrec' f → (∀ i, Partrec' (g i)) →
      Partrec' fun v => (List.Vector.mOfFn fun i => g i v) >>= f
  | rfind {n} {f : List.Vector ℕ (n + 1) → ℕ} :
    @Partrec' (n + 1) f → Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)

end Nat

namespace Nat.Partrec'

open List.Vector Partrec Computable

open Nat.Partrec'

theorem to_part {n f} (pf : @Partrec' n f) : _root_.Partrec f := by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | comp _ _ _ hf hg => exact (Partrec.vector_mOfFn hg).bind (hf.comp snd)
  | rfind _ hf =>
    have := hf.comp (vector_cons.comp snd fst)
    have :=
      ((Primrec.eq.comp _root_.Primrec.id (_root_.Primrec.const 0)).to_comp.comp
        this).to₂.partrec₂
    exact _root_.Partrec.rfind this

theorem of_eq {n} {f g : List.Vector ℕ n →. ℕ} (hf : Partrec' f) (H : ∀ i, f i = g i) :
    Partrec' g :=
  (funext H : f = g) ▸ hf

theorem of_prim {n} {f : List.Vector ℕ n → ℕ} (hf : Primrec f) : @Partrec' n f :=
  prim (Nat.Primrec'.of_prim hf)

theorem head {n : ℕ} : @Partrec' n.succ (@head ℕ n) :=
  prim Nat.Primrec'.head

theorem tail {n f} (hf : @Partrec' n f) : @Partrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    simp; rw [← ofFn_get v.tail]; congr; funext i; simp

protected theorem bind {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g) :
    @Partrec' n fun v => (f v).bind fun a => g (a ::ᵥ v) :=
  (@comp n (n + 1) g (fun i => Fin.cases f (fun i v => some (v.get i)) i) hg fun i => by
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [*]
      exact prim (Nat.Primrec'.get _)).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]

protected theorem map {n f} {g : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' n f)
    (hg : @Partrec' (n + 1) g) : @Partrec' n fun v => (f v).map fun a => g (a ::ᵥ v) := by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg

/-- Analogous to `Nat.Partrec'` for `ℕ`-valued functions, a predicate for partial recursive
  vector-valued functions. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) :=
  ∀ i, Partrec' fun v => (f v).get i

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim <| hf i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

protected theorem cons {n m} {f : List.Vector ℕ n → ℕ} {g} (hf : @Partrec' n f)
    (hg : @Vec n m g) : Vec fun v => f v ::ᵥ g v := fun i =>
  Fin.cases (by simpa using hf) (fun i => by simp only [hg i, get_cons_succ]) i

theorem idv {n} : @Vec n n id :=
  Vec.prim Nat.Primrec'.idv

theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

theorem comp₁ {n} (f : ℕ →. ℕ) {g : List.Vector ℕ n → ℕ} (hf : @Partrec' 1 fun v => f v.head)
    (hg : @Partrec' n g) : @Partrec' n fun v => f (g v) := by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

theorem rfindOpt {n} {f : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' (n + 1) f) :
    @Partrec' n fun v => Nat.rfindOpt fun a => ofNat (Option ℕ) (f (a ::ᵥ v)) :=
  ((rfind <|
        (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (fun n => Part.some (1 - n)) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ Nat.pred hf)).of_eq
    fun v =>
    Part.ext fun b => by
      simp only [Nat.rfindOpt, Nat.sub_eq_zero_iff_le, PFun.coe_val, Part.mem_bind_iff,
        Part.mem_some_iff, Option.mem_def, Part.mem_coe]
      refine
        exists_congr fun a => (and_congr (iff_of_eq ?_) Iff.rfl).trans (and_congr_right fun h => ?_)
      · congr
        funext n
        cases f (n ::ᵥ v) <;> simp <;> rfl
      · have := Nat.rfind_spec h
        simp only [Part.coe_some, Part.mem_some_iff] at this
        revert this; rcases f (a ::ᵥ v) with - | c <;> intro this
        · cases this
        rw [← Option.some_inj, eq_comm]
        rfl

open Nat.Partrec.Code

theorem of_part : ∀ {n f}, _root_.Partrec f → @Partrec' n f :=
  @(suffices ∀ f, Nat.Partrec f → @Partrec' 1 fun v => f v.head from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := List.Vector ℕ n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq fun i => by
          dsimp only [g]; simp [encodek, Part.map_id']
    fun f hf => by
    obtain ⟨c, rfl⟩ := exists_code.1 hf
    simpa [eval_eq_rfindOpt] using
      rfindOpt <|
        of_prim <|
          Primrec.encode_iff.2 <|
            primrec_evaln.comp <|
              (Primrec.vector_head.pair (_root_.Primrec.const c)).pair <|
                Primrec.vector_head.comp Primrec.vector_tail)

theorem part_iff {n f} : @Partrec' n f ↔ _root_.Partrec f :=
  ⟨to_part, of_part⟩

theorem part_iff₁ {f : ℕ →. ℕ} : (@Partrec' 1 fun v => f v.head) ↔ _root_.Partrec f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq fun v => by
        simp only [id, head_ofFn],
      fun h => h.comp vector_head⟩

theorem part_iff₂ {f : ℕ → ℕ →. ℕ} : (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq fun v => by
        simp only [head_cons, tail_cons],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

theorem vec_iff {m n f} : @Vec m n f ↔ Computable f :=
  ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
    of_part <| vector_get.comp h (const i)⟩

end Nat.Partrec'
