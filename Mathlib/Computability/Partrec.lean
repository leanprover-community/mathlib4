/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.Primrec
import Mathlib.Data.Nat.PSub
import Mathlib.Data.PFun

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `Part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization: `μ f` returns the
least natural number `n` for which `f n = 0`, or diverges if such `n` doesn't exist.

## Main definitions

- `Nat.Partrec f`: `f` is partial recursive, for functions `f : ℕ →. ℕ`
- `Partrec f`: `f` is partial recursive, for partial functions between `Primcodable` types
- `Computable f`: `f` is partial recursive, for total functions between `Primcodable` types

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open List (Vector)
open Encodable Denumerable Part

attribute [-simp] not_forall

namespace Nat

section Rfind

variable (p : ℕ →. Bool)

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, false ∈ p k

private def wf_lbp (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom) : WellFounded (lbp p) :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)⟩

variable (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom)

/-- Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined as false.
Returns a subtype. -/
def rfindX : { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } :=
  suffices ∀ k, (∀ n < k, false ∈ p n) → { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices ∀ᵉ k ≤ m, false ∈ p k from IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        rcases h.lt_or_eq_dec with h | h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)

end Rfind

/-- Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined as false.
Returns a `Part`. -/
def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩

theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : true ∈ p n :=
  h.snd ▸ (rfindX p h.fst).2.1

theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → false ∈ p m :=
  @(h.snd ▸ @((rfindX p h.fst).2.2))

@[simp]
theorem rfind_dom {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).Dom :=
  Iff.rfl

theorem rfind_dom' {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).Dom :=
  exists_congr fun _ =>
    and_congr_right fun pn =>
      ⟨fun H _ h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H _ h =>
        H (le_of_lt h)⟩

@[simp]
theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} :
    n ∈ rfind p ↔ true ∈ p n ∧ ∀ {m : ℕ}, m < n → false ∈ p m :=
  ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ => by
    let ⟨m, hm⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨_, h₁, fun {m} mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm h)⟩

theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : p m) : ∃ n ∈ rfind p, n ≤ m :=
  have : true ∈ (p : ℕ →. Bool) m := ⟨trivial, pm⟩
  let ⟨n, hn⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨m, this, fun {_} _ => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩

theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = Part.none) : rfind p = Part.none :=
  eq_none_iff.2 fun _ h =>
    let ⟨_, _, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)

/-- Find the smallest `n` satisfying `f n`, where all `f k` for `k < n` are defined as false.
Returns a `Part`. -/
def rfindOpt {α} (f : ℕ → Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n

theorem rfindOpt_spec {α} {f : ℕ → Option α} {a} (h : a ∈ rfindOpt f) : ∃ n, a ∈ f n :=
  let ⟨n, _, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩

theorem rfindOpt_dom {α} {f : ℕ → Option α} : (rfindOpt f).Dom ↔ ∃ n a, a ∈ f n :=
  ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun _ h => ⟨_, h⟩, fun h => by
    have h' : ∃ n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
    refine ⟨fd, ?_⟩
    have := rfind_spec (get_mem fd)
    simpa using this⟩

theorem rfindOpt_mono {α} {f : ℕ → Option α} (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a} :
    a ∈ rfindOpt f ↔ ∃ n, a ∈ f n :=
  ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := rfindOpt_spec ⟨h', rfl⟩
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩

/-- `Partrec f` means that the partial function `f : ℕ → ℕ` is partially recursive. -/
inductive Partrec : (ℕ →. ℕ) → Prop
  | zero : Partrec (pure 0)
  | succ : Partrec succ
  | left : Partrec ↑fun n : ℕ => n.unpair.1
  | right : Partrec ↑fun n : ℕ => n.unpair.2
  | pair {f g} : Partrec f → Partrec g → Partrec fun n => pair <$> f n <*> g n
  | comp {f g} : Partrec f → Partrec g → Partrec fun n => g n >>= f
  | prec {f g} : Partrec f → Partrec g → Partrec (unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (pair a (pair y i)))
  | rfind {f} : Partrec f → Partrec fun a => rfind fun n => (fun m => m = 0) <$> f (pair a n)

namespace Partrec

theorem of_eq {f g : ℕ →. ℕ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Partrec g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)

theorem of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Partrec f := by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | pair _ _ pf pg =>
    refine (pf.pair pg).of_eq_tot fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine (pf.comp pg).of_eq_tot fun n => (by simp)
  | prec _ _ pf pg =>
    refine (pf.prec pg).of_eq_tot fun n => ?_
    simp only [unpaired, PFun.coe_val, bind_eq_bind]
    induction n.unpair.2 with
    | zero => simp
    | succ m IH =>
      simp only [mem_bind_iff, mem_some_iff]
      exact ⟨_, IH, rfl⟩

protected theorem some : Partrec some :=
  of_primrec Primrec.id

theorem none : Partrec fun _ => none :=
  (of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

theorem prec' {f g h} (hf : Partrec f) (hg : Partrec g) (hh : Partrec h) :
    Partrec fun a => (f a).bind fun n => n.rec (g a)
      fun y IH => do {let i ← IH; h (Nat.pair a (Nat.pair y i))} :=
  ((prec hg hh).comp (pair Partrec.some hf)).of_eq fun a =>
    ext fun s => by simp [Seq.seq]

theorem ppred : Partrec fun n => ppred n :=
  have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
      (@PrimrecRel.comp _ _ _ _ _ _ _ _ _
        Primrec.eq Primrec.fst (_root_.Primrec.succ.comp Primrec.snd))
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfind.of_eq fun n => by
    cases n <;> simp
    · exact
        eq_none_iff.2 fun a ⟨⟨m, h, _⟩, _⟩ => by
          simp at h
    · refine eq_some_iff.2 ?_
      simp only [mem_rfind, decide_true, mem_some_iff,
        false_eq_decide_iff, true_and]
      intro m h
      simp [ne_of_gt h]

end Partrec

end Nat

/-- Partially recursive partial functions `α → σ` between `Primcodable` types -/
def Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) :=
  Nat.Partrec fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/-- Partially recursive partial functions `α → β → σ` between `Primcodable` types -/
def Partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β →. σ) :=
  Partrec fun p : α × β => f p.1 p.2

/-- Computable functions `α → σ` between `Primcodable` types:
  a function is computable if and only if it is partially recursive (as a partial function) -/
def Computable {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) :=
  Partrec (f : α →. σ)

/-- Computable functions `α → β → σ` between `Primcodable` types -/
def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Computable fun p : α × β => f p.1 p.2

theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Primrec f) :
    Computable f :=
  (Nat.Partrec.ppred.comp (Nat.Partrec.of_primrec hf)).of_eq fun n => by
    simp; cases decode (α := α) n <;> simp

nonrec theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp

protected theorem Computable.partrec {α σ} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : Computable f) : Partrec (f : α →. σ) :=
  hf

protected theorem Computable₂.partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Computable₂ f) : Partrec₂ fun a => (f a : β →. σ) :=
  hf

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem of_eq {f g : α → σ} (hf : Computable f) (H : ∀ n, f n = g n) : Computable g :=
  (funext H : f = g) ▸ hf

theorem const (s : σ) : Computable fun _ : α => s :=
  (Primrec.const _).to_comp

theorem ofOption {f : α → Option β} (hf : Computable f) : Partrec fun a => (f a : Part β) :=
  (Nat.Partrec.ppred.comp hf).of_eq fun n => by
    rcases decode (α := α) n with - | a <;> simp
    rcases f a with - | b <;> simp

theorem to₂ {f : α × β → σ} (hf : Computable f) : Computable₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

protected theorem id : Computable (@id α) :=
  Primrec.id.to_comp

theorem fst : Computable (@Prod.fst α β) :=
  Primrec.fst.to_comp

theorem snd : Computable (@Prod.snd α β) :=
  Primrec.snd.to_comp

nonrec theorem pair {f : α → β} {g : α → γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode (α := α) n <;> simp [Seq.seq]

theorem unpair : Computable Nat.unpair :=
  Primrec.unpair.to_comp

theorem succ : Computable Nat.succ :=
  Primrec.succ.to_comp

theorem pred : Computable Nat.pred :=
  Primrec.pred.to_comp

theorem nat_bodd : Computable Nat.bodd :=
  Primrec.nat_bodd.to_comp

theorem nat_div2 : Computable Nat.div2 :=
  Primrec.nat_div2.to_comp

theorem sumInl : Computable (@Sum.inl α β) :=
  Primrec.sumInl.to_comp

theorem sumInr : Computable (@Sum.inr α β) :=
  Primrec.sumInr.to_comp

theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_comp

theorem list_reverse : Computable (@List.reverse α) :=
  Primrec.list_reverse.to_comp

theorem list_getElem? : Computable₂ ((·[·]? : List α → ℕ → Option α)) :=
  Primrec.list_getElem?.to_comp

theorem list_append : Computable₂ ((· ++ ·) : List α → List α → List α) :=
  Primrec.list_append.to_comp

theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] :=
  Primrec.list_concat.to_comp

theorem list_length : Computable (@List.length α) :=
  Primrec.list_length.to_comp

theorem vector_cons {n} : Computable₂ (@List.Vector.cons α n) :=
  Primrec.vector_cons.to_comp

theorem vector_toList {n} : Computable (@List.Vector.toList α n) :=
  Primrec.vector_toList.to_comp

theorem vector_length {n} : Computable (@List.Vector.length α n) :=
  Primrec.vector_length.to_comp

theorem vector_head {n} : Computable (@List.Vector.head α n) :=
  Primrec.vector_head.to_comp

theorem vector_tail {n} : Computable (@List.Vector.tail α n) :=
  Primrec.vector_tail.to_comp

theorem vector_get {n} : Computable₂ (@List.Vector.get α n) :=
  Primrec.vector_get.to_comp

theorem vector_ofFn' {n} : Computable (@List.Vector.ofFn α n) :=
  Primrec.vector_ofFn'.to_comp

theorem fin_app {n} : Computable₂ (@id (Fin n → σ)) :=
  Primrec.fin_app.to_comp

protected theorem encode : Computable (@encode α _) :=
  Primrec.encode.to_comp

protected theorem decode : Computable (decode (α := α)) :=
  Primrec.decode.to_comp

protected theorem ofNat (α) [Denumerable α] : Computable (ofNat α) :=
  (Primrec.ofNat _).to_comp

theorem encode_iff {f : α → σ} : (Computable fun a => encode (f a)) ↔ Computable f :=
  Iff.rfl

theorem option_some : Computable (@Option.some α) :=
  Primrec.option_some.to_comp

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

theorem of_eq {f g : α →. σ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {f : α →. σ} {g : α → σ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Computable g :=
  hf.of_eq fun a => eq_some_iff.2 (H a)

theorem none : Partrec fun _ : α => @Part.none σ :=
  Nat.Partrec.none.of_eq fun n => by cases decode (α := α) n <;> simp

protected theorem some : Partrec (@Part.some α) :=
  Computable.id

theorem _root_.Decidable.Partrec.const' (s : Part σ) [Decidable s.Dom] : Partrec fun _ : α => s :=
  (Computable.ofOption (const (toOption s))).of_eq fun _ => of_toOption s

theorem const' (s : Part σ) : Partrec fun _ : α => s :=
  haveI := Classical.dec s.Dom
  Decidable.Partrec.const' s

protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a => (f a).bind (g a) :=
  (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    simp [Seq.seq]; rcases e : decode (α := α) n with - | a <;> simp [e, encodek]

theorem map {f : α →. β} {g : α → β → σ} (hf : Partrec f) (hg : Computable₂ g) :
    Partrec fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using Partrec.bind (g := fun a x => some (g a x)) hf hg

theorem to₂ {f : α × β →. σ} (hf : Partrec f) : Partrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

theorem nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : Computable f) (hg : Partrec g)
    (hh : Partrec₂ h) : Partrec fun a => (f a).rec (g a) fun y IH => IH.bind fun i => h a (y, i) :=
  (Nat.Partrec.prec' hf hg hh).of_eq fun n => by
    rcases e : decode (α := α) n with - | a <;> simp [e]
    induction f a with simp | succ m IH
    rw [IH, Part.bind_map]
    congr; funext s
    simp [encodek]

nonrec theorem comp {f : β →. σ} {g : α → β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g a) :=
  (hf.comp hg).of_eq fun n => by simp; rcases e : decode (α := α) n with - | a <;> simp [encodek]

theorem nat_iff {f : ℕ →. ℕ} : Partrec f ↔ Nat.Partrec f := by simp [Partrec, map_id']

theorem map_encode_iff {f : α →. σ} : (Partrec fun a => (f a).map encode) ↔ Partrec f :=
  Iff.rfl

end Partrec

namespace Partrec₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem unpaired {f : ℕ → ℕ →. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  ⟨fun h => by simpa using Partrec.comp (g := fun p : ℕ × ℕ => (p.1, p.2)) h Primrec₂.pair.to_comp,
    fun h => h.comp Primrec.unpair.to_comp⟩

theorem unpaired' {f : ℕ → ℕ →. ℕ} : Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  Partrec.nat_iff.symm.trans unpaired

nonrec theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

end Partrec₂

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

nonrec theorem comp {f : β → σ} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) :=
  hf.comp hg

theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : Computable f) (hg : Computable₂ g) :
    Computable₂ fun a b => f (g a b) :=
  hf.comp hg

end Computable

namespace Computable₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem mk {f : α → β → σ} (hf : Computable fun p : α × β => f p.1 p.2) : Computable₂ f := hf

nonrec theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Computable₂ f)
    (hg : Computable g) (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Computable₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Computable₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

end Computable₂

namespace Partrec

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

open Computable

theorem rfind {p : α → ℕ →. Bool} (hp : Partrec₂ p) : Partrec fun a => Nat.rfind (p a) :=
  (Nat.Partrec.rfind <|
        hp.map ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.to_comp).of_eq
    fun n => by
    rcases e : decode (α := α) n with - | a <;> simp [e, Nat.rfind_zero_none, map_id']
    congr; funext n
    simp only [map_map]
    refine map_id' (fun b => ?_) _
    cases b <;> rfl

theorem rfindOpt {f : α → ℕ → Option σ} (hf : Computable₂ f) :
    Partrec fun a => Nat.rfindOpt (f a) :=
  (rfind (Primrec.option_isSome.to_comp.comp hf).partrec.to₂).bind (ofOption hf)

theorem nat_casesOn_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ} (hf : Computable f)
    (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).casesOn (some (g a)) (h a) :=
  (nat_rec hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a => by
    simp only [PFun.coe_val, Nat.pred_eq_sub_one]; rcases f a with - | n <;> simp
    refine ext fun b => ⟨fun H => ?_, fun H => ?_⟩
    · rcases mem_bind_iff.1 H with ⟨c, _, h₂⟩
      exact h₂
    · have : ∀ m, (Nat.rec (motive := fun _ => Part σ)
          (Part.some (g a)) (fun y IH => IH.bind fun _ => h a n) m).Dom := by
        intro m
        induction m <;> simp [*, H.fst]
      exact ⟨⟨this n, H.fst⟩, H.snd⟩

theorem bind_decode₂_iff {f : α →. σ} :
    Partrec f ↔ Nat.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode :=
  ⟨fun hf =>
    nat_iff.1 <|
      (Computable.ofOption Primrec.decode₂.to_comp).bind <|
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
    map_encode_iff.1 <| by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩

theorem vector_mOfFn :
    ∀ {n} {f : Fin n → α →. σ},
      (∀ i, Partrec (f i)) → Partrec fun a : α => Vector.mOfFn fun i => f i a
  | 0, _, _ => const _
  | n + 1, f, hf => by
    simp only [Vector.mOfFn, pure_eq_some, bind_eq_bind]
    exact
      (hf 0).bind
        (Partrec.bind ((vector_mOfFn fun i => hf i.succ).comp fst)
          (Primrec.vector_cons.to_comp.comp (snd.comp fst) snd))

end Partrec

@[simp]
theorem Vector.mOfFn_part_some {α n} :
    ∀ f : Fin n → α,
      (List.Vector.mOfFn fun i => Part.some (f i)) = Part.some (List.Vector.ofFn f) :=
  Vector.mOfFn_pure

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem option_some_iff {f : α → σ} : (Computable fun a => Option.some (f a)) ↔ Computable f :=
  ⟨fun h => encode_iff.1 <| Primrec.pred.to_comp.comp <| encode_iff.2 h, option_some.comp⟩

theorem bind_decode_iff {f : α → β → Option σ} :
    (Computable₂ fun a n => (decode (α := β) n).bind (f a)) ↔ Computable₂ f :=
  ⟨fun hf =>
    Nat.Partrec.of_eq
      (((Partrec.nat_iff.2
        (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primcodable.prim (α := β))).comp
            snd).bind
        (Computable.comp hf fst).to₂.partrec₂)
      fun n => by
        simp only [decode_prod_val, decode_nat, Option.map_some, PFun.coe_val, bind_eq_bind,
          bind_some, Part.map_bind, map_some]
        cases decode (α := α) n.unpair.1 <;> simp
        cases decode (α := β) n.unpair.2 <;> simp,
    fun hf => by
    have :
      Partrec fun a : α × ℕ =>
        (encode (decode (α := β) a.2)).casesOn (some Option.none)
          fun n => Part.map (f a.1) (decode (α := β) n) :=
      Partrec.nat_casesOn_right
        (h := fun (a : α × ℕ) (n : ℕ) ↦ map (fun b ↦ f a.1 b) (Part.ofOption (decode n)))
        (Primrec.encdec.to_comp.comp snd) (const Option.none)
        ((ofOption (Computable.decode.comp snd)).map (hf.comp (fst.comp <| fst.comp fst) snd).to₂)
    refine this.of_eq fun a => ?_
    simp; cases decode (α := β) a.2 <;> simp [encodek]⟩

theorem map_decode_iff {f : α → β → σ} :
    (Computable₂ fun a n => (decode (α := β) n).map (f a)) ↔ Computable₂ f := by
  convert (bind_decode_iff (f := fun a => Option.some ∘ f a)).trans option_some_iff
  apply Option.map_eq_bind

theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.rec (motive := fun _ => σ) (g a) (fun y IH => h a (y, IH)) (f a) :=
  (Partrec.nat_rec hf hg hh.partrec₂).of_eq fun a => by simp; induction f a <;> simp [*]

theorem nat_casesOn {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.casesOn (motive := fun _ => σ) (f a) (g a) (h a) :=
  nat_rec hf hg (hh.comp fst <| fst.comp snd).to₂

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Computable c) (hf : Computable f)
    (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Computable o)
    (hf : Computable f) (hg : Computable₂ g) :
    @Computable _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  option_some_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek]

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).bind (g a) :=
  (option_casesOn hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl

theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by
  convert option_bind hf (option_some.comp₂ hg)
  apply Option.map_eq_bind

theorem option_getD {f : α → Option β} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getD (g a) :=
  (Computable.option_casesOn hf hg (show Computable₂ fun _ b => b from Computable.snd)).of_eq
    fun a => by cases f a <;> rfl

theorem subtype_mk {f : α → β} {p : β → Prop} [DecidablePred p] {h : ∀ a, p (f a)}
    (hp : PrimrecPred p) (hf : Computable f) :
    @Computable _ _ _ (Primcodable.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p) :=
  hf

theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by
        rcases f a with b | c <;> simp [Nat.div2_val]

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Computable₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = Option.some (f a n)) : Computable₂ f :=
  suffices Computable₂ fun a n => (List.range n).map (f a) from
    option_some_iff.1 <|
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp
  option_some_iff.1 <|
    (nat_rec snd (const (Option.some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp <| fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a => by
      induction a.2 with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ},
      (∀ i, Computable (f i)) → Computable fun a => List.ofFn fun i => f i a
  | 0, _, _ => by
    simp only [List.ofFn_zero]
    exact const []
  | n + 1, f, hf => by
    simp only [List.ofFn_succ]
    exact list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)

theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Computable (f i)) :
    Computable fun a => List.Vector.ofFn fun i => f i a :=
  (Partrec.vector_mOfFn hf).of_eq fun a => by simp

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

theorem option_some_iff {f : α →. σ} : (Partrec fun a => (f a).map Option.some) ↔ Partrec f :=
  ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩

theorem optionCasesOn_right {o : α → Option β} {f : α → σ} {g : α → β →. σ} (ho : Computable o)
    (hf : Computable f) (hg : Partrec₂ g) :
    @Partrec _ σ _ _ fun a => Option.casesOn (o a) (Part.some (f a)) (g a) :=
  have :
    Partrec fun a : α =>
      Nat.casesOn (encode (o a)) (Part.some (f a)) (fun n => Part.bind (decode (α := β) n) (g a)) :=
    nat_casesOn_right (h := fun a n ↦ Part.bind (ofOption (decode n)) fun b ↦ g a b)
      (encode_iff.2 ho) hf.partrec <|
        ((@Computable.decode β _).comp snd).ofOption.bind (hg.comp (fst.comp fst) snd).to₂
  this.of_eq fun a => by rcases o a with - | b <;> simp [encodek]

theorem sumCasesOn_right {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Partrec₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (fun b => Part.some (g a b)) (h a) :=
  have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun _ => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun _ => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    optionCasesOn_right (g := fun a n => Part.map Option.some (h a n))
      (sumCasesOn hf (const Option.none).to₂ (option_some.comp snd).to₂)
      (sumCasesOn (g := fun a n => Option.some (g a n)) hf (option_some.comp hg)
        (const Option.none).to₂)
      (option_some_iff.2 hh)
  option_some_iff.1 <| this.of_eq fun a => by cases f a <;> simp

theorem sumCasesOn_left {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Computable₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) fun c => Part.some (h a c) :=
  (sumCasesOn_right (sumCasesOn hf (sumInr.comp snd).to₂ (sumInl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp

theorem fix_aux {α σ} (f : α →. σ ⊕ α) (a : α) (b : σ) :
    let F : α → ℕ →. σ ⊕ α := fun a n =>
      n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (∃ n : ℕ,
        ((∃ b' : σ, Sum.inl b' ∈ F a n) ∧ ∀ {m : ℕ}, m < n → ∃ b : α, Sum.inr b ∈ F a m) ∧
          Sum.inl b ∈ F a n) ↔
      b ∈ PFun.fix f a := by
  intro F; refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩
    have : ∀ m a', Sum.inr a' ∈ F a m → b ∈ PFun.fix f a' → b ∈ PFun.fix f a := by
      intro m a' am ba
      induction m generalizing a' with simp [F] at am
      | zero => rwa [← am]
      | succ m IH =>
        rcases am with ⟨a₂, am₂, fa₂⟩
        exact IH _ am₂ (PFun.mem_fix_iff.2 (Or.inr ⟨_, fa₂, ba⟩))
    cases n <;> simp [F] at h₂
    rcases h₂ with (h₂ | ⟨a', am', fa'⟩)
    · obtain ⟨a', h⟩ := h₁ (Nat.lt_succ_self _)
      injection mem_unique h h₂
    · exact this _ _ am' (PFun.mem_fix_iff.2 (Or.inl fa'))
  · suffices ∀ a', b ∈ PFun.fix f a' → ∀ k, Sum.inr a' ∈ F a k →
        ∃ n, Sum.inl b ∈ F a n ∧ ∀ m < n, k ≤ m → ∃ a₂, Sum.inr a₂ ∈ F a m by
      rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩
      exact ⟨_, ⟨⟨_, hn₁⟩, fun {m} mn => hn₂ m mn (Nat.zero_le _)⟩, hn₁⟩
    intro a₁ h₁
    apply @PFun.fixInduction _ _ _ _ _ _ h₁
    intro a₂ h₂ IH k hk
    rcases PFun.mem_fix_iff.1 h₂ with (h₂ | ⟨a₃, am₃, _⟩)
    · refine ⟨k.succ, ?_, fun m mk km => ⟨a₂, ?_⟩⟩
      · simpa [F] using Or.inr ⟨_, hk, h₂⟩
      · rwa [le_antisymm (Nat.le_of_lt_succ mk) km]
    · rcases IH _ am₃ k.succ (by simpa [F] using ⟨_, hk, am₃⟩) with ⟨n, hn₁, hn₂⟩
      grind

theorem fix {f : α →. σ ⊕ α} (hf : Partrec f) : Partrec (PFun.fix f) := by
  let F : α → ℕ →. σ ⊕ α := fun a n =>
    n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_rec snd (sumInr.comp fst).partrec
      (sumCasesOn_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.comp snd).to₂).to₂
  let p a n := @Part.map _ Bool (fun s => Sum.casesOn s (fun _ => true) fun _ => false) (F a n)
  have hp : Partrec₂ p :=
    hF.map ((sumCasesOn Computable.id (const true).to₂ (const false).to₂).comp snd).to₂
  exact ((Partrec.rfind hp).bind (hF.bind (sumCasesOn_right snd snd.to₂ none.to₂).to₂).to₂).of_eq
    fun a => ext fun b => by simpa [p] using fix_aux f _ _

end Partrec
