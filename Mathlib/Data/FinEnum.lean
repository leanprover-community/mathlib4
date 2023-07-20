/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Pi

#align_import data.fin_enum from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
Type class for finitely enumerable types. The property is stronger
than `Fintype` in that it assigns each element a rank in a finite
enumeration.
-/


universe u v

open Finset

/- ./././Mathport/Syntax/Translate/Command.lean:379:30:
  infer kinds are unsupported in Lean 4: #[`Equiv] [] -/
/-- `FinEnum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `Fin n` for some n. -/
class FinEnum (α : Sort _) where
  /-- `FinEnum.card` is the cardinality of the `FinEnum` -/
  card : ℕ
  /-- `FinEnum.Equiv` states that type `α` is in bijection with `Fin card`,
    the size of the `FinEnum` -/
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]
#align fin_enum FinEnum

attribute [instance 100] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α → Type v}

/-- transport a `FinEnum` instance across an equivalence -/
def ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β
    where
  card := card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq
#align fin_enum.of_equiv FinEnum.ofEquiv

/-- create a `FinEnum` instance from an exhaustive list without duplicates -/
def ofNodupList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) : FinEnum α
    where
  card := xs.length
  equiv :=
    ⟨fun x => ⟨xs.indexOf x, by rw [List.indexOf_lt_length]; apply h⟩, fun ⟨i, h⟩ =>
      xs.nthLe _ h, fun x => by simp, fun ⟨i, h⟩ => by
      simp [*]⟩
#align fin_enum.of_nodup_list FinEnum.ofNodupList

/-- create a `FinEnum` instance from an exhaustive list; duplicates are removed -/
def ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)
#align fin_enum.of_list FinEnum.ofList

/-- create an exhaustive list of the values of a given type -/
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map (equiv).symm
#align fin_enum.to_list FinEnum.toList

open Function

@[simp]
theorem mem_toList [FinEnum α] (x : α) : x ∈ toList α := by
  simp [toList]; exists equiv x; simp
#align fin_enum.mem_to_list FinEnum.mem_toList

@[simp]
theorem nodup_toList [FinEnum α] : List.Nodup (toList α) := by
  simp [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]
#align fin_enum.nodup_to_list FinEnum.nodup_toList

/-- create a `FinEnum` instance using a surjection -/
def ofSurjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro; simp; exact h _)
#align fin_enum.of_surjective FinEnum.ofSurjective

/-- create a `FinEnum` instance using an injection -/
noncomputable def ofInjective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and_iff, List.mem_filterMap]
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
  ofList [PUnit.unit] fun x => by cases x; simp
#align fin_enum.punit FinEnum.punit

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x; simp
#align fin_enum.prod FinEnum.prod

instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (Sum α β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp
#align fin_enum.sum FinEnum.sum

instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)
#align fin_enum.fin FinEnum.fin

instance Quotient.enum [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    FinEnum (Quotient s) :=
  FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩
#align fin_enum.quotient.enum FinEnum.Quotient.enum

/-- enumerate all finite sets of a given type -/
def Finset.enum [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => do
    let r ← Finset.enum xs
    [r, {x} ∪ r]
#align fin_enum.finset.enum FinEnum.Finset.enum

@[simp]
theorem Finset.mem_enum [DecidableEq α] (s : Finset α) (xs : List α) :
    s ∈ Finset.enum xs ↔ ∀ x ∈ s, x ∈ xs := by
  induction' xs with xs_hd generalizing s <;> simp [*, Finset.enum]
  · simp [Finset.eq_empty_iff_forall_not_mem]
  · constructor
    · rintro ⟨a, h, h'⟩ x hx
      cases' h' with _ h' a b
      · right
        apply h
        subst a
        exact hx
      · simp only [h', mem_union, mem_singleton] at hx ⊢
        cases' hx with hx hx'
        · exact Or.inl hx
        · exact Or.inr (h _ hx')
    · intro h
      exists s \ ({xs_hd} : Finset α)
      simp only [and_imp, mem_sdiff, mem_singleton]
      simp only [or_iff_not_imp_left] at h
      exists h
      by_cases h : xs_hd ∈ s
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
        exact (h h₀).elim
#align fin_enum.finset.mem_enum FinEnum.Finset.mem_enum

instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by intro; simp)
#align fin_enum.finset.fin_enum FinEnum.Finset.finEnum

instance Subtype.finEnum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simp; exists x; simp [*])
#align fin_enum.subtype.fin_enum FinEnum.Subtype.finEnum

instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).bind fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x; cases x; simp)

instance PSigma.finEnum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)
#align fin_enum.psigma.fin_enum FinEnum.PSigma.finEnum

instance PSigma.finEnumPropLeft {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ'a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, Ba⟩ => (h a).elim
#align fin_enum.psigma.fin_enum_prop_left FinEnum.PSigma.finEnumPropLeft

instance PSigma.finEnumPropRight {β : α → Prop} [FinEnum α] [∀ a, Decidable (β a)] :
    FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
#align fin_enum.psigma.fin_enum_prop_right FinEnum.PSigma.finEnumPropRight

instance PSigma.finEnumPropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    FinEnum (Σ'a, β a) :=
  if h : ∃ a, β a then ofList [⟨h.fst, h.snd⟩] (by rintro ⟨⟩; simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim
#align fin_enum.psigma.fin_enum_prop_prop FinEnum.PSigma.finEnumPropProp

instance (priority := 100) [FinEnum α] : Fintype α where
  elems := univ.map (equiv).symm.toEmbedding
  complete := by intros; simp

end FinEnum

namespace List
variable {α : Type _} [FinEnum α] {β : α → Type _} [∀ a, FinEnum (β a)]
open FinEnum

theorem mem_pi_toList (xs : List α)
    (f : ∀ a, a ∈ xs → β a) : f ∈ pi xs fun x => toList (β x) :=
  (mem_pi _ _).mpr fun _ _ ↦ mem_toList _
#align fin_enum.mem_pi List.mem_pi_toList

/-- enumerate all functions whose domain and range are finitely enumerable -/
def Pi.enum (β : α → Type _) [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))
#align fin_enum.pi.enum List.Pi.enum

theorem Pi.mem_enum (f : ∀ a, β a) :
    f ∈ Pi.enum β := by simp [Pi.enum]; refine' ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩
#align fin_enum.pi.mem_enum List.Pi.mem_enum

instance Pi.finEnum : FinEnum (∀ a, β a) :=
  ofList (Pi.enum _) fun _ => Pi.mem_enum _
#align fin_enum.pi.fin_enum List.Pi.finEnum

instance pfunFinEnum (p : Prop) [Decidable p] (α : p → Type) [∀ hp, FinEnum (α hp)] :
    FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simp; exact ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by intro; simp; ext hp'; cases hp hp')
#align fin_enum.pfun_fin_enum List.pfunFinEnum

end List
