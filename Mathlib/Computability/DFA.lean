/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Chris Wong
-/
import Mathlib.Computability.Language
import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Prod

/-!
# Deterministic Finite Automata

A Deterministic Finite Automaton (DFA) is a state machine which
decides membership in a particular `Language`, by following a path
uniquely determined by an input string.

We define regular languages to be ones for which a DFA exists, other formulations
are later proved equivalent.

Note that this definition allows for automata with infinite states,
a `Fintype` instance must be supplied for true DFAs.

## Main definitions

- `DFA α σ`: automaton over alphabet `α` and set of states `σ`
- `M.accepts`: the language accepted by the DFA `M`
- `Language.IsRegular L`: a predicate stating that `L` is a regular language, i.e. there exists
  a DFA that recognizes the language

## Main theorems

- `DFA.pumping_lemma` : every sufficiently long string accepted by the DFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)

## Implementation notes

Currently, there are two disjoint sets of simp lemmas: one for `DFA.eval`, and another for
`DFA.evalFrom`. You can switch from the former to the latter using `simp [eval]`.

## TODO

- Should we unify these simp sets, such that `eval` is rewritten to `evalFrom` automatically?
- Should `mem_accepts` and `mem_acceptsFrom` be marked `@[simp]`?
-/

universe u v

open Computability

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) where
  /-- A transition function from state to state labelled by the alphabet. -/
  step : σ → α → σ
  /-- Starting state. -/
  start : σ
  /-- Set of acceptance states. -/
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default) default ∅⟩

/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/
def evalFrom (s : σ) : List α → σ :=
  List.foldl M.step s

@[simp]
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s :=
  rfl

@[simp]
theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  rfl

@[simp]
theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : List α → σ :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

theorem evalFrom_of_append (start : σ) (x y : List α) :
    M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y :=
  List.foldl_append

/--
`M.acceptsFrom s` is the language of `x` such that `M.evalFrom s x` is an accept state.
-/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x ∈ M.accept}

theorem mem_acceptsFrom {s : σ} {x : List α} :
    x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := by rfl

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α := M.acceptsFrom M.start

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ M.eval x ∈ M.accept := by rfl

theorem evalFrom_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ ≤ x.length)
    (hx : M.evalFrom s x = t) :
    ∃ q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧
          b ≠ [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t := by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by simp)
  wlog hle : (n : ℕ) ≤ m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  refine
    ⟨M.evalFrom s ((x.take m).take n), (x.take m).take n, (x.take m).drop n,
                    x.drop m, ?_, ?_, ?_, by rfl, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    omega
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    omega
  have hq : M.evalFrom (M.evalFrom s ((x.take m).take n)) ((x.take m).drop n) =
      M.evalFrom s ((x.take m).take n) := by
    rw [List.take_take, min_eq_left hle, ← evalFrom_of_append, heq, ← min_eq_left hle, ←
      List.take_take, min_eq_left hle, List.take_append_drop]
  use hq
  rwa [← hq, ← evalFrom_of_append, ← evalFrom_of_append, ← List.append_assoc,
    List.take_append_drop, List.take_append_drop]

theorem evalFrom_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s)
    (hy : y ∈ ({x} : Language α)∗) : M.evalFrom s y = s := by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten_cons, evalFrom_of_append, ha, hx]
    apply ih
    intro z hz
    exact hS z (List.mem_cons_of_mem a hz)

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split (s := M.start) hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, hab, c', hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', ha', b', hb', rfl⟩
  rw [Set.mem_singleton_iff] at ha' hc'
  substs ha' hc'
  have h := M.evalFrom_of_pow hb hb'
  rwa [mem_accepts, eval, evalFrom_of_append, evalFrom_of_append, h, hc]

section SetClosure

variable {σ' : Type v}

/--
`M.compl` constructs a DFA for the complement of the language of `M`.

Use `Mᶜ` rather than directly using this function.
-/
def compl (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

instance : HasCompl (DFA α σ) := ⟨compl⟩

@[simp]
theorem compl_accept_eq_accept_compl : Mᶜ.accept = M.acceptᶜ := rfl

@[simp]
theorem compl_accepts_eq_accepts_compl : Mᶜ.accepts = M.acceptsᶜ := rfl

theorem mem_accept_compl {s : σ} : s ∈ Mᶜ.accept ↔ s ∉ M.accept := by simp

theorem mem_accepts_compl {x : List α} : x ∈ Mᶜ.accepts ↔ x ∉ M.accepts :=
  mem_accept_compl M

/--
Cartesian product of two DFAs with an arbitrary acceptance condition given by the binary Boolean
algebra operation `p`. `p` takes in whether `M₁` and `M₂` accept their respective inputs and
returns whether the product of the two DFAs should accept the pair of inputs.

This is a generalization of the intersection of two DFAs to arbitrary binary set operations.
-/
def prod (M₁ : DFA α σ) (M₂ : DFA α σ') (p : Prop → Prop → Prop) : DFA α (σ × σ') where
  step := fun ⟨s₁, s₂⟩ a => (M₁.step s₁ a, M₂.step s₂ a)
  start := (M₁.start, M₂.start)
  accept := {s | p (s.fst ∈ M₁.accept) (s.snd ∈ M₂.accept)}

theorem prod_accept_iff
    (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') (s : σ × σ') :
    s ∈ (M₁.prod M₂ p).accept ↔ p (s.fst ∈ M₁.accept) (s.snd ∈ M₂.accept) := by
  simp [prod]

theorem prod_evalFrom
    (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) (s : σ × σ') :
    (M₁.prod M₂ p).evalFrom s x = ⟨M₁.evalFrom s.1 x, M₂.evalFrom s.2 x⟩ := by
  revert s
  dsimp [evalFrom, prod]
  induction x with
  | nil => simp
  | cons a x ih =>
    intro s
    simp [List.foldl, ih, DFA.step]

theorem prod_accepts_iff
    (p : Prop → Prop → Prop) (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) :
    x ∈ (M₁.prod M₂ p).accepts ↔ p (x ∈ M₁.accepts) (x ∈ M₂.accepts) := by
  simp only [accepts, acceptsFrom, prod_evalFrom]
  rfl

/--
Constructs a DFA for the intersection of the languages of two DFAs.

There is no instance for this to provide the `M₁ ∩ M₂` syntax, because M₁ and M₂ have
different state types. -/
def inter (M₁ : DFA α σ) (M₂ : DFA α σ') : DFA α (σ × σ') := prod M₁ M₂ And

theorem inter_accept_iff (M₁ : DFA α σ) (M₂ : DFA α σ') (s : σ × σ') :
    s ∈ (M₁.inter M₂).accept ↔ s.fst ∈ M₁.accept ∧ s.snd ∈ M₂.accept := by
  simp [inter, prod_accept_iff]

theorem inter_accepts_iff (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) :
    x ∈ (M₁.inter M₂).accepts ↔ x ∈ M₁.accepts ∧ x ∈ M₂.accepts := by
  simp [inter, prod_accepts_iff]

theorem inter_accept_eq_prod_accept (M₁ : DFA α σ) (M₂ : DFA α σ') :
    (M₁.inter M₂).accept = M₁.accept ×ˢ M₂.accept := by
  ext ⟨s₁, s₂⟩
  simp [inter_accept_iff]

theorem inter_accepts_eq_inter (M₁ : DFA α σ) (M₂ : DFA α σ') :
    (M₁.inter M₂).accepts = M₁.accepts ∩ M₂.accepts := by
  ext x
  simp only [inter_accepts_iff]
  rfl

/--
Constructs a DFA for the union of the languages of two DFAs.

There is no instance for this to provide the `M₁ ∪ M₂` syntax, because M₁ and M₂ have
different state types. -/
def union (M₁ : DFA α σ) (M₂ : DFA α σ') : DFA α (σ × σ') := prod M₁ M₂ Or

theorem union_accept_iff (M₁ : DFA α σ) (M₂ : DFA α σ') (s : σ × σ') :
    s ∈ (M₁.union M₂).accept ↔ s.fst ∈ M₁.accept ∨ s.snd ∈ M₂.accept := by
  simp [union, prod_accept_iff]

theorem union_accepts_iff (M₁ : DFA α σ) (M₂ : DFA α σ') (x : List α) :
    x ∈ (M₁.union M₂).accepts ↔ x ∈ M₁.accepts ∨ x ∈ M₂.accepts := by
  simp [union, prod_accepts_iff]

theorem union_accepts_union (M₁ : DFA α σ) (M₂ : DFA α σ') :
    (M₁.union M₂).accepts = M₁.accepts + M₂.accepts := by
  ext x
  simp only [union_accepts_iff]
  rfl

end SetClosure

section Maps

variable {α' σ' : Type*}

/--
`M.comap f` pulls back the alphabet of `M` along `f`. In other words, it applies `f` to the input
before passing it to `M`.
-/
@[simps]
def comap (f : α' → α) (M : DFA α σ) : DFA α' σ where
  step s a := M.step s (f a)
  start := M.start
  accept := M.accept

@[simp]
theorem comap_id : M.comap id = M := rfl

@[simp]
theorem evalFrom_comap (f : α' → α) (s : σ) (x : List α') :
    (M.comap f).evalFrom s x = M.evalFrom s (x.map f) := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]
theorem eval_comap (f : α' → α) (x : List α') : (M.comap f).eval x = M.eval (x.map f) := by
  simp [eval]

@[simp]
theorem accepts_comap (f : α' → α) : (M.comap f).accepts = List.map f ⁻¹' M.accepts := by
  ext x
  conv =>
    rhs
    rw [Set.mem_preimage, mem_accepts]
  simp [mem_accepts]

/-- Lifts an equivalence on states to an equivalence on DFAs. -/
@[simps apply_step apply_start apply_accept]
def reindex (g : σ ≃ σ') : DFA α σ ≃ DFA α σ' where
  toFun M := {
    step := fun s a => g (M.step (g.symm s) a)
    start := g M.start
    accept := g.symm ⁻¹' M.accept
  }
  invFun M := {
    step := fun s a => g.symm (M.step (g s) a)
    start := g.symm M.start
    accept := g ⁻¹' M.accept
  }
  left_inv M := by simp
  right_inv M := by simp

@[simp]
theorem reindex_refl : reindex (Equiv.refl σ) M = M := rfl

@[simp]
theorem symm_reindex (g : σ ≃ σ') : (reindex (α := α) g).symm = reindex g.symm := rfl

@[simp]
theorem evalFrom_reindex (g : σ ≃ σ') (s : σ') (x : List α) :
    (reindex g M).evalFrom s x = g (M.evalFrom (g.symm s) x) := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]
theorem eval_reindex (g : σ ≃ σ') (x : List α) : (reindex g M).eval x = g (M.eval x) := by
  simp [eval]

@[simp]
theorem accepts_reindex (g : σ ≃ σ') : (reindex g M).accepts = M.accepts := by
  ext x
  simp [mem_accepts]

theorem comap_reindex (f : α' → α) (g : σ ≃ σ') :
    (reindex g M).comap f = reindex g (M.comap f) := by
  simp [comap, reindex]

end Maps

end DFA

variable {α : Type u}

/-- A regular language is a language that is defined by a DFA with finite states. -/
def Language.IsRegular {T : Type u} (L : Language T) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

/-- Lifts the state type `σ` inside `Language.IsRegular` to a different universe. -/
private lemma Language.isRegular_iff.helper.{v'} {T : Type u} {L : Language T}
    (hL : ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L) :
    ∃ σ' : Type v', ∃ _ : Fintype σ', ∃ M : DFA T σ', M.accepts = L :=
  have ⟨σ, _, M, hM⟩ := hL
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f, hM ▸ DFA.accepts_reindex M f⟩

/--
A language is regular if and only if it is defined by a DFA with finite states.

This is more general than using the definition of `Language.IsRegular` directly, as the state type
`σ` is universe-polymorphic.
-/
theorem Language.isRegular_iff {T : Type u} {L : Language T} :
    L.IsRegular ↔ ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L :=
  ⟨Language.isRegular_iff.helper, Language.isRegular_iff.helper⟩

/-- Regular languages are closed under complement. -/
theorem Language.isRegular_compl_iff {L : Language α} : Lᶜ.IsRegular ↔ L.IsRegular := by
  constructor
  · rintro ⟨σ, _, M, hM⟩
    rw [<- compl_compl M.accepts] at hM
    apply compl_inj_iff.mp at hM
    rw [<- DFA.compl_accepts_eq_accepts_compl] at hM
    exact ⟨σ, inferInstance, Mᶜ, hM⟩
  · rintro ⟨σ, _, M, hM⟩
    use σ, inferInstance, Mᶜ
    rw [DFA.compl_accepts_eq_accepts_compl, hM]

/-- Regular languages are closed under binary set operations. -/
theorem Language.isRegular_prod (p : Prop → Prop → Prop) {L₁ L₂ : Language α}
    {h₁ : L₁.IsRegular} {h₂ : L₂.IsRegular} : IsRegular ({ x : List α | p (x ∈ L₁) (x ∈ L₂) }) := by
  have ⟨σ₁, _, M₁, hM₁⟩ := h₁
  have ⟨σ₂, _, M₂, hM₂⟩ := h₂
  use σ₁ × σ₂, inferInstance, M₁.prod M₂ p
  rw [<- hM₁, <- hM₂]
  apply Set.ext
  intro x
  simp
  apply DFA.prod_accepts_iff

/-- Regular languages are closed under intersection. -/
theorem Language.isRegular_inter {L₁ L₂ : Language α} {h₁ : L₁.IsRegular} {h₂ : L₂.IsRegular} :
    (L₁ ∩ L₂).IsRegular := by
  apply Language.isRegular_prod And
  · exact h₁
  · exact h₂

/-- Regular languages are closed under union. -/
theorem Language.isRegular_union {L₁ L₂ : Language α} {h₁ : L₁.IsRegular} {h₂ : L₂.IsRegular} :
    (L₁ ∪ L₂).IsRegular := by
  apply Language.isRegular_prod Or
  · exact h₁
  · exact h₂
