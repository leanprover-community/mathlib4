/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.fin_enum
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Monad.Basic
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.List.ProdSigma

/-!
Type class for finitely enumerable types. The property is stronger
than `fintype` in that it assigns each element a rank in a finite
enumeration.
-/


universe u v

open Finset

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`Equiv] [] -/
/-- `fin_enum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `fin n` for some n. -/
class FinEnum (α : Sort _) where
  card : ℕ
  Equiv : α ≃ Fin card
  [decEq : DecidableEq α]
#align fin_enum FinEnum

attribute [instance] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α → Type v}

/-- transport a `fin_enum` instance across an equivalence -/
def ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β
    where
  card := card α
  Equiv := h.trans (equiv α)
  decEq := (h.trans (equiv _)).DecidableEq
#align fin_enum.of_equiv FinEnum.ofEquiv

/-- create a `fin_enum` instance from an exhaustive list without duplicates -/
def ofNodupList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) : FinEnum α
    where
  card := xs.length
  Equiv :=
    ⟨fun x => ⟨xs.indexOf x, by rw [List.indexOf_lt_length] <;> apply h⟩, fun ⟨i, h⟩ =>
      xs.nthLe _ h, fun x => by simp [of_nodup_list._match_1], fun ⟨i, h⟩ => by
      simp [of_nodup_list._match_1, *] <;> rw [List.nthLe_index_of] <;> apply List.nodup_dedup⟩
#align fin_enum.of_nodup_list FinEnum.ofNodupList

/-- create a `fin_enum` instance from an exhaustive list; duplicates are removed -/
def ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)
#align fin_enum.of_list FinEnum.ofList

/-- create an exhaustive list of the values of a given type -/
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map (equiv α).symm
#align fin_enum.to_list FinEnum.toList

open Function

@[simp]
theorem mem_to_list [FinEnum α] (x : α) : x ∈ toList α := by
  simp [to_list] <;> exists Equiv α x <;> simp
#align fin_enum.mem_to_list FinEnum.mem_to_list

@[simp]
theorem nodup_to_list [FinEnum α] : List.Nodup (toList α) := by
  simp [to_list] <;> apply List.Nodup.map <;> [apply Equiv.injective, apply List.nodup_finRange]
#align fin_enum.nodup_to_list FinEnum.nodup_to_list

/-- create a `fin_enum` instance using a surjection -/
def ofSurjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro <;> simp <;> exact h _)
#align fin_enum.of_surjective FinEnum.ofSurjective

/-- create a `fin_enum` instance using an injection -/
noncomputable def ofInjective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_to_list, true_and_iff, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])
#align fin_enum.of_injective FinEnum.ofInjective

instance pempty : FinEnum PEmpty :=
  ofList [] fun x => PEmpty.elim x
#align fin_enum.pempty FinEnum.pempty

instance empty : FinEnum Empty :=
  ofList [] fun x => Empty.elim x
#align fin_enum.empty FinEnum.empty

instance punit : FinEnum PUnit :=
  ofList [PUnit.unit] fun x => by cases x <;> simp
#align fin_enum.punit FinEnum.punit

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x <;> simp
#align fin_enum.prod FinEnum.prod

instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (Sum α β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp
#align fin_enum.sum FinEnum.sum

instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)
#align fin_enum.fin FinEnum.fin

instance Quotient.enum [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    FinEnum (Quotient s) :=
  FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.induction_on x fun x => ⟨x, rfl⟩
#align fin_enum.quotient.enum FinEnum.Quotient.enum

/-- enumerate all finite sets of a given type -/
def Finset.enum [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => do
    let r ← finset.enum xs
    [r, {x} ∪ r]
#align fin_enum.finset.enum FinEnum.Finset.enum

@[simp]
theorem Finset.mem_enum [DecidableEq α] (s : Finset α) (xs : List α) :
    s ∈ Finset.enum xs ↔ ∀ x ∈ s, x ∈ xs :=
  by
  induction xs generalizing s <;> simp [*, finset.enum]
  · simp [Finset.eq_empty_iff_forall_not_mem, (· ∉ ·)]
    rfl
  · constructor
    rintro ⟨a, h, h'⟩ x hx
    cases h'
    · right
      apply h
      subst a
      exact hx
    · simp only [h', mem_union, mem_singleton] at hx⊢
      cases hx
      · exact Or.inl hx
      · exact Or.inr (h _ hx)
    intro h
    exists s \ ({xs_hd} : Finset α)
    simp only [and_imp, mem_sdiff, mem_singleton]
    simp only [or_iff_not_imp_left] at h
    exists h
    by_cases xs_hd ∈ s
    · have : {xs_hd} ⊆ s
      simp only [HasSubset.Subset, *, forall_eq, mem_singleton]
      simp only [union_sdiff_of_subset this, or_true_iff, Finset.union_sdiff_of_subset,
        eq_self_iff_true]
    · left
      symm
      simp only [sdiff_eq_self]
      intro a
      simp only [and_imp, mem_inter, mem_singleton]
      rintro h₀ rfl
      apply h h₀
#align fin_enum.finset.mem_enum FinEnum.Finset.mem_enum

instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by intro <;> simp)
#align fin_enum.finset.fin_enum FinEnum.Finset.finEnum

instance Subtype.finEnum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩ <;> simp <;> exists x <;> simp [*])
#align fin_enum.subtype.fin_enum FinEnum.Subtype.finEnum

instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).bind fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x <;> cases x <;> simp)

instance Psigma.finEnum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)
#align fin_enum.psigma.fin_enum FinEnum.Psigma.finEnum

instance Psigma.finEnumPropLeft {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ'a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, Ba⟩ => (h a).elim
#align fin_enum.psigma.fin_enum_prop_left FinEnum.Psigma.finEnumPropLeft

instance Psigma.finEnumPropRight {β : α → Prop} [FinEnum α] [∀ a, Decidable (β a)] :
    FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => rfl, fun ⟨x, y⟩ => rfl⟩
#align fin_enum.psigma.fin_enum_prop_right FinEnum.Psigma.finEnumPropRight

instance Psigma.finEnumPropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    FinEnum (Σ'a, β a) :=
  if h : ∃ a, β a then ofList [⟨h.fst, h.snd⟩] (by rintro ⟨⟩ <;> simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim
#align fin_enum.psigma.fin_enum_prop_prop FinEnum.Psigma.finEnumPropProp

instance (priority := 100) [FinEnum α] : Fintype α
    where
  elems := univ.map (equiv α).symm.toEmbedding
  complete := by intros <;> simp <;> exists Equiv α x <;> simp

/-- For `pi.cons x xs y f` create a function where every `i ∈ xs` is mapped to `f i` and
`x` is mapped to `y`  -/
def Pi.cons [DecidableEq α] (x : α) (xs : List α) (y : β x) (f : ∀ a, a ∈ xs → β a) :
    ∀ a, a ∈ (x :: xs : List α) → β a
  | b, h => if h' : b = x then cast (by rw [h']) y else f b (List.mem_of_ne_of_mem h' h)
#align fin_enum.pi.cons FinEnum.Pi.cons

/-- Given `f` a function whose domain is `x :: xs`, produce a function whose domain
is restricted to `xs`.  -/
def Pi.tail {x : α} {xs : List α} (f : ∀ a, a ∈ (x :: xs : List α) → β a) : ∀ a, a ∈ xs → β a
  | a, h => f a (List.mem_cons_of_mem _ h)
#align fin_enum.pi.tail FinEnum.Pi.tail

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi {β : α → Type max u v} [DecidableEq α] :
    ∀ xs : List α, (∀ a, List (β a)) → List (∀ a, a ∈ xs → β a)
  | [], fs => [fun x h => h.elim]
  | x :: xs, fs => FinEnum.Pi.cons x xs <$> fs x <*> pi xs fs
#align fin_enum.pi FinEnum.pi

theorem mem_pi {β : α → Type max u v} [FinEnum α] [∀ a, FinEnum (β a)] (xs : List α)
    (f : ∀ a, a ∈ xs → β a) : f ∈ pi xs fun x => toList (β x) :=
  by
  induction xs <;> simp [pi, -List.map_eq_map, monad_norm, functor_norm]
  · ext (a⟨⟩)
  · exists pi.cons xs_hd xs_tl (f _ (List.mem_cons_self _ _))
    constructor
    exact ⟨_, rfl⟩
    exists pi.tail f
    constructor
    · apply xs_ih
    · ext (x h)
      simp [pi.cons]
      split_ifs
      subst x
      rfl
      rfl
#align fin_enum.mem_pi FinEnum.mem_pi

/-- enumerate all functions whose domain and range are finitely enumerable -/
def pi.enum (β : α → Type max u v) [FinEnum α] [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi (toList α) fun x => toList (β x)).map fun f x => f x (mem_to_list _)
#align fin_enum.pi.enum FinEnum.pi.enum

theorem pi.mem_enum {β : α → Type max u v} [FinEnum α] [∀ a, FinEnum (β a)] (f : ∀ a, β a) :
    f ∈ pi.enum β := by simp [pi.enum] <;> refine' ⟨fun a h => f a, mem_pi _ _, rfl⟩
#align fin_enum.pi.mem_enum FinEnum.pi.mem_enum

instance pi.finEnum {β : α → Type max u v} [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (∀ a, β a) :=
  ofList (pi.enum _) fun x => pi.mem_enum _
#align fin_enum.pi.fin_enum FinEnum.pi.finEnum

instance pfunFinEnum (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, FinEnum (α hp)] :
    FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x hp' => x) (by intro <;> simp <;> exact ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by intro <;> simp <;> ext hp' <;> cases hp hp')
#align fin_enum.pfun_fin_enum FinEnum.pfunFinEnum

end FinEnum

