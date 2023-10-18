/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Stream.Defs

#align_import data.stream.init from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

Porting note:
This file used to be in the core library. It was moved to `mathlib` and renamed to `init` to avoid
name clashes.  -/

set_option autoImplicit true

open Nat Function Option PFunctor

namespace Stream'

variable {α : Type u} {β : Type v} {δ : Type w}

instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩

protected theorem eta (s : Stream' α) : head s ::ₛ tail s = s :=
  M.mk_dest s
#align stream.eta Stream'.eta

@[simp]
theorem head_cons (a : α) (s : Stream' α) : head (a ::ₛ s) = a := by
  rw [head, cons, M.dest_mk]
#align stream.head_cons Stream'.head_cons

@[simp]
theorem get_zero_cons (a : α) (s : Stream' α) : get (a ::ₛ s) 0 = a :=
  head_cons a s
#align stream.nth_zero_cons Stream'.get_zero_cons

@[simp]
theorem tail_cons (a : α) (s : Stream' α) : tail (a ::ₛ s) = s := by
  rw [tail, cons, M.dest_mk]
#align stream.tail_cons Stream'.tail_cons

@[simp]
theorem get_drop (n m : Nat) (s : Stream' α) : get (drop m s) n = get s (n + m) := by
  induction m using Nat.recAux generalizing s with
  | zero => rfl
  | succ m hm =>
    rw [drop, hm, ← Nat.add_assoc, get]
#align stream.nth_drop Stream'.get_drop

theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl
#align stream.tail_eq_drop Stream'.tail_eq_drop

@[simp]
theorem drop_drop (n m : Nat) (s : Stream' α) : drop n (drop m s) = drop (n + m) s := by
  induction m using Nat.recAux generalizing s with
  | zero => rfl
  | succ m hm =>
    rw [drop, hm, ← Nat.add_assoc, drop]
#align stream.drop_drop Stream'.drop_drop

@[simp] theorem get_tail {s : Stream' α} : s.tail.get n = s.get (n + 1) := rfl

@[simp] theorem tail_drop' {s : Stream' α} : tail (drop i s) = s.drop (i + 1) := by
  rw [tail_eq_drop, drop_drop, Nat.add_comm 1 i]

@[simp] theorem drop_tail' {s : Stream' α} : drop i (tail s) = s.drop (i + 1) := rfl

theorem tail_drop (n : Nat) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by simp
#align stream.tail_drop Stream'.tail_drop

theorem get_succ (n : Nat) (s : Stream' α) : get s (succ n) = get (tail s) n :=
  rfl
#align stream.nth_succ Stream'.get_succ

@[simp]
theorem get_succ_cons (n : Nat) (s : Stream' α) (x : α) : get (x ::ₛ s) n.succ = get s n := by
  rw [get, tail_cons]
#align stream.nth_succ_cons Stream'.get_succ_cons

@[simp] theorem drop_zero {s : Stream' α} : s.drop 0 = s := rfl

theorem drop_succ (n : Nat) (s : Stream' α) : drop (succ n) s = drop n (tail s) :=
  rfl
#align stream.drop_succ Stream'.drop_succ

@[simp]
theorem head_drop (a : Stream' α) (n : ℕ) : (a.drop n).head = a.get n := by
  change get (a.drop n) 0 = get a n
  rw [get_drop, Nat.zero_add]
#align stream.head_drop Stream'.head_drop

theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := fun x y s t h =>
  ⟨by rw [← head_cons x s, h, head_cons], by rw [← tail_cons x s, h, tail_cons]⟩
#align stream.cons_injective2 Stream'.cons_injective2

theorem cons_injective_left (s : Stream' α) : Function.Injective (· ::ₛ s) :=
  cons_injective2.left _
#align stream.cons_injective_left Stream'.cons_injective_left

theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _
#align stream.cons_injective_right Stream'.cons_injective_right

@[simp]
theorem all_iff (p : α → Prop) (s : Stream' α) : All p s ↔ ∀ n, p (get s n) := by
  constructor
  case mp =>
    rintro ⟨q, hs, hq⟩ n
    suffices hn : p (get s n) ∧ q (drop (n + 1) s) from hn.1
    induction n using Nat.recAux with
    | zero =>
      exact hq s hs
    | succ n hn =>
      specialize hq _ hn.2
      rwa [head_drop, tail_drop'] at hq
  case mpr =>
    intro h
    use fun s' => ∀ n, p (get s' n), h
    intro s' hs'
    exact ⟨hs' 0, fun n => hs' n.succ⟩
#align stream.all_def Stream'.all_iff

@[simp]
theorem any_iff (p : α → Prop) (s : Stream' α) : Any p s ↔ ∃ n, p (get s n) := by
  constructor
  case mp =>
    intro hs
    induction hs with
    | head s hs => exact ⟨0, hs⟩
    | tail s _ hs =>
      rcases hs with ⟨n, hs⟩
      exact ⟨n + 1, hs⟩
  case mpr =>
    rintro ⟨n, hs⟩
    induction n using Nat.recAux generalizing s with
    | zero => exact Any.head s hs
    | succ n hn => exact Any.tail s <| hn (tail s) hs
#align stream.any_def Stream'.any_iff

@[simp]
theorem mem_cons (a : α) (s : Stream' α) : a ∈ a ::ₛ s :=
  Any.head (a ::ₛ s) (head_cons a s).symm
#align stream.mem_cons Stream'.mem_cons

theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) (hs : a ∈ s) : a ∈ b ::ₛ s :=
  Any.tail (b ::ₛ s) (by rwa [tail_cons])
#align stream.mem_cons_of_mem Stream'.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} (h : a ∈ b ::ₛ s) : a = b ∨ a ∈ s := by
  cases h with
  | head _ ha => left; rwa [head_cons] at ha
  | tail _ hs => right; rwa [tail_cons] at hs
#align stream.eq_or_mem_of_mem_cons Stream'.eq_or_mem_of_mem_cons

theorem mem_of_get_eq {n : Nat} {s : Stream' α} {a : α} (h : a = get s n) : a ∈ s := by
  rw [mem_def, any_iff]
  exists n
#align stream.mem_of_nth_eq Stream'.mem_of_get_eq

section Bisim

variable (R : Stream' α → Stream' α → Prop)

/-- Streams `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations. -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ → head s₁ = head s₂ ∧ R (tail s₁) (tail s₂)
#align stream.is_bisimulation Stream'.IsBisimulation

/-- If two streams are bisimilar, then they are equal. -/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (hs : R s₁ s₂) : s₁ = s₂ := by
  refine M.bisim R ?_ _ _ hs; clear s₁ s₂ hs
  intro s₁ s₂ hs
  specialize bisim hs; rcases bisim with ⟨hhs, hts⟩
  refine ⟨head s₁, fun _ => tail s₁, fun _ => tail s₂, rfl, ?_, ?_⟩
  · exact Sigma.ext_iff.mpr ⟨hhs.symm, HEq.refl _⟩
  · exact fun _ => hts
#align stream.eq_of_bisim Stream'.eq_of_bisim

theorem get_of_bisim (bisim : IsBisimulation R) :
    ∀ {s₁ s₂} (n), R s₁ s₂ → get s₁ n = get s₂ n ∧ R (drop (n + 1) s₁) (drop (n + 1) s₂)
  | _, _, 0, h => bisim h
  | _, _, n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel
#align stream.nth_of_bisim Stream'.get_of_bisim

end Bisim

theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by
      constructor; exact h₁; rw [← h₂, ← h₃]
      (repeat' constructor) <;> assumption)
    (And.intro hh (And.intro ht₁ ht₂))
#align stream.bisim_simple Stream'.bisim_simple

theorem coinduction {s₁ s₂ : Stream' α} :
    head s₁ = head s₂ →
      (∀ (β : Type u) (fr : Stream' α → β),
        fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
  fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        ∀ (β : Type u) (fr : Stream' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α (@head α) h₁
      have h₃ :
        ∀ (β : Type u) (fr : Stream' α → β),
          fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
        fun β fr => And.right h β fun s => fr (tail s)
      And.intro h₁ (And.intro h₂ h₃))
    (And.intro hh ht)
#align stream.coinduction Stream'.coinduction

section Corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 ::ₛ corec' f (f a).2 :=
  M.corec_def _ _
#align stream.corec'_eq Stream'.corec'_eq

@[simp]
theorem head_corec' (f : α → β × α) (a : α) : head (corec' f a) = (f a).1 := by
  rw [corec'_eq, head_cons]

@[simp]
theorem tail_corec' (f : α → β × α) (a : α) : tail (corec' f a) = corec' f (f a).2 := by
  rw [corec'_eq, tail_cons]

end Corec'

section Corec

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a ::ₛ corec f g (g a) :=
  corec'_eq _ _
#align stream.corec_eq Stream'.corec_eq
#align stream.unfolds_eq Stream'.corec_eq

@[simp]
theorem head_corec (f : α → β) (g : α → α) (a : α) : head (corec f g a) = f a :=
  head_corec' _ _

@[simp]
theorem tail_corec (f : α → β) (g : α → α) (a : α) : tail (corec f g a) = corec f g (g a) :=
  tail_corec' _ _

theorem corec_head_eq (s : Stream' α) : corec head tail s = s :=
  eq_of_bisim (fun s₁ s₂ => corec head tail s₂ = s₁)
    (by rintro _ s rfl; simp)
    rfl
#align stream.unfolds_head_eq Stream'.corec_head_eq

theorem get_corec_head_tail (n : Nat) (s : Stream' α) :
    get (corec head tail s) n = get s n := by
  rw [corec_head_eq]
#align stream.nth_unfolds_head_tail Stream'.get_corec_head_tail

end Corec

section Map

variable (f : α → β)

@[simp]
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  head_corec _ _ _
#align stream.head_map Stream'.head_map

@[simp]
theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) :=
  tail_corec _ _ _
#align stream.tail_map Stream'.tail_map

theorem drop_map (n : Nat) (s : Stream' α) : drop n (map f s) = map f (drop n s) := by
  induction n using Nat.recAux generalizing s <;> simp [drop, *]
#align stream.drop_map Stream'.drop_map

@[simp]
theorem get_map (n : Nat) (s : Stream' α) : get (map f s) n = f (get s n) := by
  induction n using Nat.recAux generalizing s <;> simp [get, *]
#align stream.nth_map Stream'.get_map

theorem map_eq (s : Stream' α) : map f s = f (head s) ::ₛ map f (tail s) := by
  rw [← Stream'.eta (map f s), tail_map, head_map]
#align stream.map_eq Stream'.map_eq

theorem map_cons (a : α) (s : Stream' α) : map f (a ::ₛ s) = f a ::ₛ map f s := by
  rw [← Stream'.eta (map f (a ::ₛ s)), map_eq, Stream'.eta, head_cons, tail_cons]
#align stream.map_cons Stream'.map_cons

@[simp]
theorem map_id (s : Stream' α) : map id s = s :=
  eq_of_bisim (fun s₁ s₂ => map id s₂ = s₁) (by rintro _ s rfl; simp) rfl
#align stream.map_id Stream'.map_id

@[simp]
theorem map_map (g : β → δ) (f : α → β) (s : Stream' α) : map g (map f s) = map (g ∘ f) s :=
  eq_of_bisim (fun s₁ s₂ => ∃ s₃, map g (map f s₃) = s₁ ∧ map (g ∘ f) s₃ = s₂)
    (by rintro _ _ ⟨s, rfl, rfl⟩; simp; exists tail s)
    ⟨s, rfl, rfl⟩
#align stream.map_map Stream'.map_map

@[simp]
theorem map_tail (s : Stream' α) : map f (tail s) = tail (map f s) :=
  eq_of_bisim (fun s₁ s₂ => ∃ s₃, map f (tail s₃) = s₁ ∧ tail (map f s₃) = s₂)
    (by rintro _ _ ⟨s, rfl, rfl⟩; simp)
    ⟨s, rfl, rfl⟩
#align stream.map_tail Stream'.map_tail

theorem mem_map {a : α} {s : Stream' α} (h : a ∈ s) : f a ∈ map f s := by
  simp [mem_def] at h ⊢
  rcases h with ⟨n, rfl⟩
  exists n
#align stream.mem_map Stream'.mem_map

theorem exists_of_mem_map {f} {b : β} {s : Stream' α} (h : b ∈ map f s) : ∃ a, a ∈ s ∧ f a = b := by
  simp [mem_def] at h ⊢
  rcases h with ⟨n, rfl⟩
  exact ⟨get s n, ⟨n, rfl⟩, rfl⟩
#align stream.exists_of_mem_map Stream'.exists_of_mem_map

end Map

@[simp]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  head_corec _ _ _
#align stream.head_iterate Stream'.head_iterate

@[simp]
theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) :=
  tail_corec _ _ _
#align stream.tail_iterate Stream'.tail_iterate

theorem get_succ_iterate' (n : Nat) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = f (get (iterate f a) n) := by
  rw [get_succ, tail_iterate]
  induction n using Nat.recAux generalizing a <;> simp [get, *]

theorem corec_eq_map_iterate (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  eq_of_bisim (fun s₁ s₂ => ∃ a, corec f g a = s₁ ∧ map f (iterate g a) = s₂)
    (by rintro _ _ ⟨a, rfl, rfl⟩; simp; exists g a)
    ⟨a, rfl, rfl⟩
#align stream.corec_def Stream'.corec_eq_map_iterate

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl
#align stream.corec_id_f_eq_iterate Stream'.corec_id_f_eq_iterate

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a ::ₛ iterate f (f a) := by
  rw [← Stream'.eta (iterate f a), head_iterate, tail_iterate]
#align stream.iterate_eq Stream'.iterate_eq

@[simp]
theorem get_zero_iterate (f : α → α) (a : α) : get (iterate f a) 0 = a :=
  head_iterate f a
#align stream.nth_zero_iterate Stream'.get_zero_iterate

theorem get_succ_iterate (n : Nat) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = get (iterate f (f a)) n := by rw [get_succ, tail_iterate]
#align stream.nth_succ_iterate Stream'.get_succ_iterate

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) :=
  eq_of_bisim (fun s₁ s₂ => ∃ a, iterate f (f a) = s₁ ∧ map f (iterate f a) = s₂)
    (by rintro _ _ ⟨a, rfl, rfl⟩; simp; exists f a)
    ⟨a, rfl, rfl⟩
#align stream.map_iterate Stream'.map_iterate

@[simp]
theorem head_natsFrom (n : ℕ) : head (natsFrom n) = n :=
  head_iterate _ _

@[simp]
theorem tail_natsFrom (n : ℕ) : tail (natsFrom n) = natsFrom (n + 1) :=
  tail_iterate _ _

theorem get_natsFrom (m n : ℕ) : get (natsFrom m) n = m + n := by
  induction n using Nat.recAux generalizing m <;> simp [get, Nat.add_assoc, Nat.add_comm 1, *]

theorem get_nats (n : ℕ) : get nats n = n := by
  rw [get_natsFrom, Nat.zero_add]
#align stream.nth_nats Stream'.get_nats

theorem natsFrom_eq (n : ℕ) : natsFrom n = n ::ₛ natsFrom (n + 1) := by
  rw [← Stream'.eta (natsFrom n), head_natsFrom, tail_natsFrom]

theorem nats_eq : nats = 0 ::ₛ natsFrom 1 :=
  natsFrom_eq 0
#align stream.nats_eq Stream'.nats_eq

section OfFn

@[simp]
theorem get_ofFn (f : ℕ → α) (n : ℕ) : get (ofFn f) n = f n := by
  rw [ofFn, get_map, get_nats]

@[simp]
theorem ofFn_get (s : Stream' α) : ofFn (get s) = s :=
  eq_of_bisim (fun s₁ s₂ => ∃ s₃ n, map (get s₃) (natsFrom n) = s₁ ∧ drop n s₃ = s₂)
    (by
      rintro _ _ ⟨s, n, rfl, rfl⟩
      simp
      exists s, n + 1)
    ⟨s, 0, rfl, rfl⟩

@[ext]
protected theorem ext {s₁ s₂ : Stream' α} (h : ∀ n, get s₁ n = get s₂ n) : s₁ = s₂ := by
  rw [← ofFn_get s₁, funext (f := get s₁) (g := get s₂) h, ofFn_get s₂]
#align stream.ext Stream'.ext

/-- The natural equivalence between streams and functions from naturals. -/
@[simps]
def _root_.Equiv.streamEquivNat (α : Type u) : Stream' α ≃ (ℕ → α) where
  toFun := Stream'.get
  invFun := Stream'.ofFn
  left_inv s := ofFn_get s
  right_inv f := funext (get_ofFn f)

end OfFn

section Zip

variable (f : α → β → δ)

@[simp]
theorem head_zipWith (s₁ : Stream' α) (s₂ : Stream' β) :
    head (zipWith f s₁ s₂) = f (head s₁) (head s₂) :=
  head_corec _ _ _
#align stream.head_zip Stream'.head_zipWith

@[simp]
theorem head_zip (s₁ : Stream' α) (s₂ : Stream' β) :
    head (zip s₁ s₂) = (head s₁, head s₂) :=
  head_zipWith _ _ _

@[simp]
theorem tail_zipWith (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zipWith f s₁ s₂) = zipWith f (tail s₁) (tail s₂) :=
  tail_corec _ _ _
#align stream.tail_zip Stream'.tail_zipWith

theorem tail_zip (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zip s₁ s₂) = zip (tail s₁) (tail s₂) :=
  tail_zipWith _ _ _

@[simp]
theorem get_zipWith (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    get (zipWith f s₁ s₂) n = f (get s₁ n) (get s₂ n) := by
  induction n using Nat.recAux generalizing s₁ s₂ <;> simp [get, *]
#align stream.nth_zip Stream'.get_zipWith

@[simp]
theorem get_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    get (zip s₁ s₂) n = (get s₁ n, get s₂ n) :=
  get_zipWith _ _ _ _

theorem drop_zipWith (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zipWith f s₁ s₂) = zipWith f (drop n s₁) (drop n s₂) := by
  ext n; simp
#align stream.drop_zip Stream'.drop_zipWith

theorem drop_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip s₁ s₂) = zip (drop n s₁) (drop n s₂) :=
  drop_zipWith _ _ _ _

theorem zipWith_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zipWith f s₁ s₂ = f (head s₁) (head s₂) ::ₛ zipWith f (tail s₁) (tail s₂) := by
  rw [← Stream'.eta (zipWith f s₁ s₂), head_zipWith, tail_zipWith]
#align stream.zip_eq Stream'.zipWith_eq

theorem zip_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zip s₁ s₂ = (head s₁, head s₂) ::ₛ zip (tail s₁) (tail s₂) :=
  zipWith_eq _ _ _

@[simp]
theorem get_enum (s : Stream' α) (n : ℕ) : get (enum s) n = (n, s.get n) := by
  rw [enum, get_zip, get_nats]
#align stream.nth_enum Stream'.get_enum

#align stream.enum_eq_zip Stream'.enum

end Zip

@[simp]
theorem head_const (a : α) : head (const a) = a :=
  head_corec _ _ _

@[simp]
theorem tail_const (a : α) : tail (const a) = const a :=
  tail_corec _ _ _
#align stream.tail_const Stream'.tail_const

theorem const_eq (a : α) : const a = a ::ₛ const a := by
  conv_lhs => rw [← Stream'.eta (const a), head_const, tail_const]
#align stream.const_eq Stream'.const_eq

@[simp]
theorem mem_const (a : α) : a ∈ const a :=
  (const_eq a).symm ▸ mem_cons a (const a)
#align stream.mem_const Stream'.mem_const

@[simp]
theorem get_const (n : Nat) (a : α) : get (const a) n = a := by
  induction n using Nat.recAux <;> simp [get, *]
#align stream.nth_const Stream'.get_const

@[simp]
theorem iterate_id (a : α) : iterate id a = const a :=
  eq_of_bisim (fun s₁ s₂ => ∃ a, iterate id a = s₁ ∧ const a = s₂)
    (by rintro _ _ ⟨a, rfl, rfl⟩; simp; exists a)
    ⟨a, rfl, rfl⟩
#align stream.iterate_id Stream'.iterate_id

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_eq_map_iterate, map_id, iterate_id]
#align stream.corec_id_id_eq_const Stream'.corec_id_id_eq_const

@[simp]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) := by
  ext n; simp
#align stream.map_const Stream'.map_const

@[simp]
theorem drop_const (n : Nat) (a : α) : drop n (const a) = const a := by
  ext n; simp
#align stream.drop_const Stream'.drop_const

@[simp]
theorem head_interleave (s₁ s₂ : Stream' α) : head (s₁ ⋈ s₂) = head s₁ :=
  head_corec _ _ _

@[simp]
theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ :=
  tail_corec _ _ _
#align stream.tail_interleave Stream'.tail_interleave

theorem interleave_tail_tail (s₁ s₂ : Stream' α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [tail_interleave, tail_interleave]
#align stream.interleave_tail_tail Stream'.interleave_tail_tail

theorem interleave_eq (s₁ s₂ : Stream' α) :
    s₁ ⋈ s₂ = head s₁ ::ₛ head s₂ ::ₛ (tail s₁ ⋈ tail s₂) := by
  conv_lhs =>
    rw [← Stream'.eta (s₁ ⋈ s₂), head_interleave, tail_interleave,
      ← Stream'.eta (s₂ ⋈ tail s₁), head_interleave, tail_interleave]
#align stream.interleave_eq Stream'.interleave_eq

theorem get_interleave_left : ∀ (n : Nat) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n) = get s₁ n
  | 0, s₁, s₂ => head_interleave _ _
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n))) = get s₁ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons]
    have : n < succ n := Nat.lt_succ_self n
    rw [get_interleave_left n (tail s₁) (tail s₂)]
    rfl
#align stream.nth_interleave_left Stream'.get_interleave_left

theorem get_interleave_right : ∀ (n : Nat) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n + 1) = get s₂ n
  | 0, s₁, s₂ => by simp [get]
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = get s₂ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons,
      get_interleave_right n (tail s₁) (tail s₂)]
    rfl
#align stream.nth_interleave_right Stream'.get_interleave_right

theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) (h : a ∈ s₁) :
    a ∈ s₁ ⋈ s₂ := by
  rw [mem_def, any_iff] at h ⊢
  rcases h with ⟨n, rfl⟩
  use 2 * n; rw [get_interleave_left]
#align stream.mem_interleave_left Stream'.mem_interleave_left

theorem mem_interleave_right {a : α} {s₁ : Stream' α} (s₂ : Stream' α) (h : a ∈ s₂) :
    a ∈ s₁ ⋈ s₂ := by
  rw [mem_def, any_iff] at h ⊢
  rcases h with ⟨n, rfl⟩
  use 2 * n + 1; rw [get_interleave_right]
#align stream.mem_interleave_right Stream'.mem_interleave_right

theorem odd_eq (s : Stream' α) : odd s = even (tail s) :=
  rfl
#align stream.odd_eq Stream'.odd_eq

@[simp]
theorem head_even (s : Stream' α) : head (even s) = head s :=
  head_corec _ _ _
#align stream.head_even Stream'.head_even

@[simp]
theorem tail_even (s : Stream' α) : tail (even s) = even (tail (tail s)) :=
  tail_corec _ _ _
#align stream.tail_even Stream'.tail_even

theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁ ::ₛ a₂ ::ₛ s) = a₁ ::ₛ even s := by
  unfold even
  rw [corec_eq]; simp
#align stream.even_cons_cons Stream'.even_cons_cons

theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl
#align stream.even_tail Stream'.even_tail

theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rw [head_even, head_interleave]
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)
#align stream.even_interleave Stream'.even_interleave

theorem interleave_even_odd (s₁ : Stream' α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rw [head_interleave, head_even]
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl
#align stream.interleave_even_odd Stream'.interleave_even_odd

theorem get_even : ∀ (n : Nat) (s : Stream' α), get (even s) n = get s (2 * n)
  | 0, s => head_even _
  | succ n, s => by
    change get (even s) (succ n) = get s (succ (succ (2 * n)))
    rw [get_succ, get_succ, tail_even, get_even n]; rfl
#align stream.nth_even Stream'.get_even

theorem get_odd : ∀ (n : Nat) (s : Stream' α), get (odd s) n = get s (2 * n + 1) := fun n s => by
  rw [odd_eq, get_even]; rfl
#align stream.nth_odd Stream'.get_odd

theorem mem_of_mem_even (a : α) (s : Stream' α) (h : a ∈ even s) : a ∈ s := by
  rw [mem_def, any_iff] at h ⊢
  rcases h with ⟨n, rfl⟩
  use 2 * n
  rw [get_even]
#align stream.mem_of_mem_even Stream'.mem_of_mem_even

theorem mem_of_mem_odd (a : α) (s : Stream' α) (h : a ∈ odd s) : a ∈ s := by
  rw [mem_def, any_iff] at h ⊢
  rcases h with ⟨n, rfl⟩
  use 2 * n + 1
  rw [get_odd]
#align stream.mem_of_mem_odd Stream'.mem_of_mem_odd

@[simp]
theorem nil_append (s : Stream' α) : ([] : List α) ++ s = s :=
  rfl
#align stream.nil_append_stream Stream'.nil_append

@[simp]
theorem cons_append (a : α) (l : List α) (s : Stream' α) :
    a :: l ++ s = a ::ₛ (l ++ s) :=
  rfl
#align stream.cons_append_stream Stream'.cons_append

theorem append_assoc : ∀ (l₁ l₂ : List α) (s : Stream' α),
    l₁ ++ l₂ ++ s = l₁ ++ (l₂ ++ s)
  | [], l₂, s => rfl
  | a :: l₁, l₂, s => by
    rw [List.cons_append, cons_append, cons_append, append_assoc l₁]
#align stream.append_append_stream Stream'.append_assoc

theorem map_append (f : α → β) :
    ∀ (l : List α) (s : Stream' α), map f (l ++ s) = List.map f l ++ map f s
  | [], s => rfl
  | a :: l, s => by
    rw [cons_append, List.map_cons, map_cons, cons_append, map_append f l]
#align stream.map_append_stream Stream'.map_append

theorem drop_append : ∀ (l : List α) (s : Stream' α), drop l.length (l ++ s) = s
  | [], s => by rfl
  | a :: l, s => by
    rw [List.length_cons, drop_succ, cons_append, tail_cons, drop_append l s]
#align stream.drop_append_stream Stream'.drop_append

theorem append_head_tail (s : Stream' α) : [head s] ++ tail s = s := by
  rw [cons_append, nil_append, Stream'.eta]
#align stream.append_stream_head_tail Stream'.append_head_tail

theorem mem_append_right : ∀ {a : α} (l : List α) {s : Stream' α}, a ∈ s → a ∈ l ++ s
  | _, [], _, h => h
  | a, _ :: l, s, h =>
    have ih : a ∈ l ++ s := mem_append_right l h
    mem_cons_of_mem _ ih
#align stream.mem_append_stream_right Stream'.mem_append_right

theorem mem_append_left : ∀ {a : α} {l : List α} (s : Stream' α), a ∈ l → a ∈ l ++ s
  | _, [], _, h => absurd h (List.not_mem_nil _)
  | a, b :: l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_cons h)
      (fun aeqb : a = b => by rw [cons_append, aeqb]; apply mem_cons)
      (fun ainl : a ∈ l => mem_cons_of_mem b (mem_append_left s ainl))
#align stream.mem_append_stream_left Stream'.mem_append_left

@[simp]
theorem take_zero (s : Stream' α) : take 0 s = [] :=
  rfl
#align stream.take_zero Stream'.take_zero

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
theorem take_succ (n : Nat) (s : Stream' α) : take (succ n) s = head s::take n (tail s) :=
  rfl
#align stream.take_succ Stream'.take_succ

@[simp]
theorem take_succ_cons (n : Nat) (s : Stream' α) :
    take (n + 1) (a ::ₛ s) = a :: take n s := by
  simp [take_succ]

theorem take_succ' {s : Stream' α} : ∀ n, s.take (n+1) = s.take n ++ [s.get n]
  | 0 => rfl
  | n + 1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp]
theorem length_take (n : ℕ) (s : Stream' α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]
#align stream.length_take Stream'.length_take

@[simp]
theorem take_take {s : Stream' α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [zero_min, take_zero, List.take_nil]
  | m + 1, n + 1 => by rw [take_succ, List.take_cons, Nat.min_succ_succ, take_succ, take_take]

@[simp] theorem concat_take_get {s : Stream' α} : s.take n ++ [s.get n] = s.take (n+1) :=
  (take_succ' n).symm

theorem get?_take {s : Stream' α} : ∀ {k n}, k < n → (s.take n).get? k = s.get k
  | 0, n + 1, _ => rfl
  | k + 1, n + 1, h => by rw [take_succ, List.get?, get?_take (Nat.lt_of_succ_lt_succ h), get_succ]

theorem get?_take_succ (n : Nat) (s : Stream' α) :
    List.get? (take (succ n) s) n = some (get s n) :=
  get?_take (Nat.lt_succ_self n)
#align stream.nth_take_succ Stream'.get?_take_succ

@[simp] theorem dropLast_take {xs : Stream' α} :
    (Stream'.take n xs).dropLast = Stream'.take (n - 1) xs := by
  cases n; case zero => simp
  case succ n => rw [take_succ', List.dropLast_concat, Nat.succ_sub_one]

@[simp]
theorem append_take_drop (n : Nat) (s : Stream' α) :
    take n s ++ drop n s = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [take_succ, drop_succ, cons_append, ih (tail s), Stream'.eta]
#align stream.append_take_drop Stream'.append_take_drop

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : Stream' α) : (∀ n : Nat, take n s₁ = take n s₂) → s₁ = s₂ := by
  intro h; apply Stream'.ext; intro n
  induction' n with n _
  · have aux := h 1
    simp [take] at aux
    exact aux
  · have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← get?_take_succ, ← get?_take_succ, h (succ (succ n))]
    injection h₁
#align stream.take_theorem Stream'.take_theorem

protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, a₁ :: l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl
#align stream.cycle_g_cons Stream'.cycle_g_cons

theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ cycle l h
  | [], h => absurd rfl h
  | a :: l, _ =>
    have gen : ∀ l' a', corec Stream'.cycleF Stream'.cycleG (a', l', a, l) =
        a' :: l' ++ corec Stream'.cycleF Stream'.cycleG (a, l, a, l) := by
      intro l'
      induction' l' with a₁ l₁ ih
      · intros
        rw [corec_eq]
        rfl
      · intros
        rw [corec_eq, Stream'.cycle_g_cons, ih a₁]
        rfl
    gen l a
#align stream.cycle_eq Stream'.cycle_eq

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_left _ ainl
#align stream.mem_cycle Stream'.mem_cycle

@[simp]
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
  coinduction (by simp [cycle, Stream'.cycleF])
    (fun β fr ch => by rw [cycle_eq, const_eq]; simpa using ch)
#align stream.cycle_singleton Stream'.cycle_singleton

theorem tails_eq (s : Stream' α) : tails s = s ::ₛ tails (tail s) :=
  iterate_eq _ _
#align stream.tails_eq Stream'.tails_eq

@[simp]
theorem get_tails (n : Nat) (s : Stream' α) : get (tails s) n = drop n s := by
  induction n using Nat.recAux generalizing s with
  | zero => simp [get, tails]
  | succ n ih =>
    rw [get_succ, drop_succ, tails_eq, tail_cons, ih]
#align stream.nth_tails Stream'.get_tails

theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail s :=
  rfl
#align stream.tails_eq_iterate Stream'.tails_eq_iterate

@[simp]
theorem head_initsCore (l : List α) (s : Stream' α) : head (initsCore l s) = l :=
  head_corec _ _ _

@[simp]
theorem tail_initsCore (l : List α) (s : Stream' α) :
    tail (initsCore l s) = initsCore (l.concat (head s)) (tail s) :=
  tail_corec _ _ _

theorem initsCore_eq (l : List α) (s : Stream' α) :
    initsCore l s = l ::ₛ initsCore (l.concat (head s)) (tail s) :=
  corec_eq _ _ _
#align stream.inits_core_eq Stream'.initsCore_eq

@[simp]
theorem head_inits (s : Stream' α) : head (inits s) = [] :=
  head_corec _ _ _

@[simp]
theorem tail_inits (s : Stream' α) :
    tail (inits s) = initsCore [head s] (tail s) :=
  tail_corec _ _ _
#align stream.tail_inits Stream'.tail_inits

theorem inits_tail (s : Stream' α) :
    inits (tail s) = initsCore [] (tail s) :=
  rfl
#align stream.inits_tail Stream'.inits_tail

theorem cons_get_initsCore (a : α) (n : Nat) (l : List α) (s : Stream' α) :
    a :: get (initsCore l s) n = get (initsCore (a :: l) s) n := by
  induction n using Nat.recAux generalizing l s with
  | zero => simp [get]
  | succ n ih => simp [get, ih]
#align stream.cons_nth_inits_core Stream'.cons_get_initsCore

@[simp]
theorem get_inits (n : Nat) (s : Stream' α) : get (inits s) n = take n s := by
  induction n using Nat.recAux generalizing s with
  | zero => simp [get]
  | succ n ih =>
    rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_initsCore]
#align stream.nth_inits Stream'.get_inits

theorem inits_eq (s : Stream' α) :
    inits s = [] ::ₛ map (List.cons (head s)) (inits (tail s)) := by
  ext1 (_ | n)
  · simp [get]
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits, take]
#align stream.inits_eq Stream'.inits_eq

theorem zipWith_inits_tails (s : Stream' α) : zipWith (· ++ ·) (inits s) (tails s) = const s := by
  ext1 n
  rw [get_zipWith, get_inits, get_tails, get_const, append_take_drop]
#align stream.zip_inits_tails Stream'.zipWith_inits_tails

theorem identity (s : Stream' α) : const id ⊛ s = s := by
  ext n; simp [apply]
#align stream.identity Stream'.identity

theorem composition (g : Stream' (β → δ)) (f : Stream' (α → β)) (s : Stream' α) :
    const comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) := by
  ext n; simp [apply]
#align stream.composition Stream'.composition

theorem homomorphism (f : α → β) (a : α) : const f ⊛ const a = const (f a) := by
  ext n; simp [apply]
#align stream.homomorphism Stream'.homomorphism

theorem interchange (fs : Stream' (α → β)) (a : α) :
    fs ⊛ const a = const (eval a) ⊛ fs := by
  ext n; simp [apply]
#align stream.interchange Stream'.interchange

theorem map_eq_apply (f : α → β) (s : Stream' α) : map f s = const f ⊛ s := by
  ext n; simp [apply]
#align stream.map_eq_apply Stream'.map_eq_apply

end Stream'
