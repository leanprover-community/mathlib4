/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.ProdSigma

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
class FinEnum (α : Sort*) where
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
                                -- ⊢ x ∈ xs
                                                             -- 🎉 no goals
      xs.nthLe _ h, fun x => by simp, fun ⟨i, h⟩ => by
                                -- 🎉 no goals
      simp [*]⟩
      -- 🎉 no goals
#align fin_enum.of_nodup_list FinEnum.ofNodupList

/-- create a `FinEnum` instance from an exhaustive list; duplicates are removed -/
def ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)
                           -- 🎉 no goals
#align fin_enum.of_list FinEnum.ofList

/-- create an exhaustive list of the values of a given type -/
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map (equiv).symm
#align fin_enum.to_list FinEnum.toList

open Function

@[simp]
theorem mem_toList [FinEnum α] (x : α) : x ∈ toList α := by
  simp [toList]; exists equiv x; simp
  -- ⊢ ∃ a, ↑equiv.symm a = x
                 -- ⊢ ↑equiv.symm (↑equiv x) = x
                                 -- 🎉 no goals
#align fin_enum.mem_to_list FinEnum.mem_toList

@[simp]
theorem nodup_toList [FinEnum α] : List.Nodup (toList α) := by
  simp [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]
  -- ⊢ List.Nodup (List.map (↑equiv.symm) (List.finRange (card α)))
                 -- 🎉 no goals
#align fin_enum.nodup_to_list FinEnum.nodup_toList

/-- create a `FinEnum` instance using a surjection -/
def ofSurjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro; simp; exact h _)
                                -- ⊢ x✝ ∈ List.map f (toList β)
                                       -- ⊢ ∃ a, f a = x✝
                                             -- 🎉 no goals
#align fin_enum.of_surjective FinEnum.ofSurjective

/-- create a `FinEnum` instance using an injection -/
noncomputable def ofInjective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      -- ⊢ x ∈ List.filterMap (partialInv f) (toList β)
      simp only [mem_toList, true_and_iff, List.mem_filterMap]
      -- ⊢ ∃ a, partialInv f a = some x
      use f x
      -- ⊢ partialInv f (f x) = some x
      simp only [h, Function.partialInv_left])
      -- 🎉 no goals
#align fin_enum.of_injective FinEnum.ofInjective

instance pempty : FinEnum PEmpty :=
  ofList [] fun x => PEmpty.elim x
#align fin_enum.pempty FinEnum.pempty

instance empty : FinEnum Empty :=
  ofList [] fun x => Empty.elim x
#align fin_enum.empty FinEnum.empty

instance punit : FinEnum PUnit :=
  ofList [PUnit.unit] fun x => by cases x; simp
                                  -- ⊢ PUnit.unit ∈ [PUnit.unit]
                                           -- 🎉 no goals
#align fin_enum.punit FinEnum.punit

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x; simp
                                            -- ⊢ (fst✝, snd✝) ∈ toList α ×ˢ toList β
                                                     -- 🎉 no goals
#align fin_enum.prod FinEnum.prod

instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (Sum α β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp
                                                                        -- ⊢ Sum.inl val✝ ∈ List.map Sum.inl (toList α) ++ List.map Sum.inr (toList β)
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align fin_enum.sum FinEnum.sum

instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)
                               -- 🎉 no goals
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
  -- ⊢ s ∈ enum [] ↔ ∀ (x : α), x ∈ s → x ∈ []
                                              -- ⊢ s = ∅ ↔ ∀ (x : α), x ∈ s → False
                                              -- ⊢ (∃ a, (∀ (x : α), x ∈ a → x ∈ tail✝) ∧ (s = a ∨ s = {xs_hd} ∪ a)) ↔ ∀ (x : α …
  · simp [Finset.eq_empty_iff_forall_not_mem]
    -- 🎉 no goals
  · constructor
    -- ⊢ (∃ a, (∀ (x : α), x ∈ a → x ∈ tail✝) ∧ (s = a ∨ s = {xs_hd} ∪ a)) → ∀ (x : α …
    · rintro ⟨a, h, h'⟩ x hx
      -- ⊢ x = xs_hd ∨ x ∈ tail✝
      cases' h' with _ h' a b
      -- ⊢ x = xs_hd ∨ x ∈ tail✝
      · right
        -- ⊢ x ∈ tail✝
        apply h
        -- ⊢ x ∈ a
        subst a
        -- ⊢ x ∈ s
        exact hx
        -- 🎉 no goals
      · simp only [h', mem_union, mem_singleton] at hx ⊢
        -- ⊢ x = xs_hd ∨ x ∈ tail✝
        cases' hx with hx hx'
        -- ⊢ x = xs_hd ∨ x ∈ tail✝
        · exact Or.inl hx
          -- 🎉 no goals
        · exact Or.inr (h _ hx')
          -- 🎉 no goals
    · intro h
      -- ⊢ ∃ a, (∀ (x : α), x ∈ a → x ∈ tail✝) ∧ (s = a ∨ s = {xs_hd} ∪ a)
      exists s \ ({xs_hd} : Finset α)
      -- ⊢ (∀ (x : α), x ∈ s \ {xs_hd} → x ∈ tail✝) ∧ (s = s \ {xs_hd} ∨ s = {xs_hd} ∪  …
      simp only [and_imp, mem_sdiff, mem_singleton]
      -- ⊢ (∀ (x : α), x ∈ s → ¬x = xs_hd → x ∈ tail✝) ∧ (s = s \ {xs_hd} ∨ s = {xs_hd} …
      simp only [or_iff_not_imp_left] at h
      -- ⊢ (∀ (x : α), x ∈ s → ¬x = xs_hd → x ∈ tail✝) ∧ (s = s \ {xs_hd} ∨ s = {xs_hd} …
      exists h
      -- ⊢ s = s \ {xs_hd} ∨ s = {xs_hd} ∪ s \ {xs_hd}
      by_cases h : xs_hd ∈ s
      -- ⊢ s = s \ {xs_hd} ∨ s = {xs_hd} ∪ s \ {xs_hd}
      · have : {xs_hd} ⊆ s
        -- ⊢ {xs_hd} ⊆ s
        simp only [HasSubset.Subset, *, forall_eq, mem_singleton]
        -- ⊢ s = s \ {xs_hd} ∨ s = {xs_hd} ∪ s \ {xs_hd}
        simp only [union_sdiff_of_subset this, or_true_iff, Finset.union_sdiff_of_subset,
          eq_self_iff_true]
      · left
        -- ⊢ s = s \ {xs_hd}
        symm
        -- ⊢ s \ {xs_hd} = s
        simp only [sdiff_eq_self]
        -- ⊢ s ∩ {xs_hd} ⊆ ∅
        intro a
        -- ⊢ a ∈ s ∩ {xs_hd} → a ∈ ∅
        simp only [and_imp, mem_inter, mem_singleton]
        -- ⊢ a ∈ s → a = xs_hd → a ∈ ∅
        rintro h₀ rfl
        -- ⊢ a ∈ ∅
        exact (h h₀).elim
        -- 🎉 no goals
#align fin_enum.finset.mem_enum FinEnum.Finset.mem_enum

instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by intro; simp)
                                      -- ⊢ x✝ ∈ enum (toList α)
                                             -- 🎉 no goals
#align fin_enum.finset.fin_enum FinEnum.Finset.finEnum

instance Subtype.finEnum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simp; exists x; simp [*])
        -- ⊢ { val := x, property := h } ∈ List.filterMap (fun x => if h : p x then some  …
                       -- ⊢ ∃ a, (if h : p a then some { val := a, property := h } else none) = some { v …
                             -- ⊢ (if h : p x then some { val := x, property := h } else none) = some { val := …
                                       -- 🎉 no goals
#align fin_enum.subtype.fin_enum FinEnum.Subtype.finEnum

instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).bind fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x; cases x; simp)
        -- ⊢ x ∈ List.bind (toList α) fun a => List.map (Sigma.mk a) (toList (β a))
                 -- ⊢ { fst := fst✝, snd := snd✝ } ∈ List.bind (toList α) fun a => List.map (Sigma …
                          -- 🎉 no goals

instance PSigma.finEnum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)
#align fin_enum.psigma.fin_enum FinEnum.PSigma.finEnum

instance PSigma.finEnumPropLeft {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ'a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
                                                                             -- 🎉 no goals
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
                                                   -- ⊢ { fst := fst✝, snd := snd✝ } ∈ [{ fst := (_ : α), snd := (_ : β (_ : α)) }]
                                                              -- 🎉 no goals
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim
#align fin_enum.psigma.fin_enum_prop_prop FinEnum.PSigma.finEnumPropProp

instance (priority := 100) [FinEnum α] : Fintype α where
  elems := univ.map (equiv).symm.toEmbedding
  complete := by intros; simp
                 -- ⊢ x✝ ∈ map (Equiv.toEmbedding equiv.symm) univ
                         -- 🎉 no goals

/-- For `Pi.cons x xs y f` create a function where every `i ∈ xs` is mapped to `f i` and
`x` is mapped to `y`  -/
def Pi.cons [DecidableEq α] (x : α) (xs : List α) (y : β x) (f : ∀ a, a ∈ xs → β a) :
    ∀ a, a ∈ (x :: xs : List α) → β a
  | b, h => if h' : b = x then cast (by rw [h']) y else f b (List.mem_of_ne_of_mem h' h)
                                        -- 🎉 no goals
#align fin_enum.pi.cons FinEnum.Pi.cons

/-- Given `f` a function whose domain is `x :: xs`, produce a function whose domain
is restricted to `xs`.  -/
def Pi.tail {x : α} {xs : List α} (f : ∀ a, a ∈ (x :: xs : List α) → β a) : ∀ a, a ∈ xs → β a
  | a, h => f a (List.mem_cons_of_mem _ h)
#align fin_enum.pi.tail FinEnum.Pi.tail

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi {β : α → Type max u v} [DecidableEq α] :
    ∀ xs : List α, (∀ a, List (β a)) → List (∀ a, a ∈ xs → β a)
  | [], _ => [fun x h => (List.not_mem_nil x h).elim]
  | x :: xs, fs => FinEnum.Pi.cons x xs <$> fs x <*> pi xs fs
#align fin_enum.pi FinEnum.pi

theorem mem_pi {β : α → Type _} [FinEnum α] [∀ a, FinEnum (β a)] (xs : List α)
    (f : ∀ a, a ∈ xs → β a) : f ∈ pi xs fun x => toList (β x) := by
  induction' xs with xs_hd xs_tl xs_ih <;> simp [pi, -List.map_eq_map, monad_norm, functor_norm]
  -- ⊢ f ∈ pi [] fun x => toList (β x)
                                           -- ⊢ f = fun x h => False.elim (_ : False)
                                           -- ⊢ ∃ a, (∃ a_1, a = Pi.cons xs_hd xs_tl a_1) ∧ ∃ a_1, (a_1 ∈ pi xs_tl fun x =>  …
  · ext a ⟨⟩
    -- 🎉 no goals
  · exists Pi.cons xs_hd xs_tl (f _ (List.mem_cons_self _ _))
    -- ⊢ (∃ a, Pi.cons xs_hd xs_tl (f xs_hd (_ : xs_hd ∈ xs_hd :: xs_tl)) = Pi.cons x …
    constructor
    -- ⊢ ∃ a, Pi.cons xs_hd xs_tl (f xs_hd (_ : xs_hd ∈ xs_hd :: xs_tl)) = Pi.cons xs …
    exact ⟨_, rfl⟩
    -- ⊢ ∃ a, (a ∈ pi xs_tl fun x => toList (β x)) ∧ f = Pi.cons xs_hd xs_tl (f xs_hd …
    exists Pi.tail f
    -- ⊢ (Pi.tail f ∈ pi xs_tl fun x => toList (β x)) ∧ f = Pi.cons xs_hd xs_tl (f xs …
    constructor
    -- ⊢ Pi.tail f ∈ pi xs_tl fun x => toList (β x)
    · apply xs_ih
      -- 🎉 no goals
    · ext x h
      -- ⊢ f x h = Pi.cons xs_hd xs_tl (f xs_hd (_ : xs_hd ∈ xs_hd :: xs_tl)) (Pi.tail  …
      simp [Pi.cons]
      -- ⊢ f x h = if h' : x = xs_hd then cast (_ : β xs_hd = β x) (f xs_hd (_ : xs_hd  …
      split_ifs
      -- ⊢ f x h = cast (_ : β xs_hd = β x) (f xs_hd (_ : xs_hd ∈ xs_hd :: xs_tl))
      · subst x
        -- ⊢ f xs_hd h = cast (_ : β xs_hd = β xs_hd) (f xs_hd (_ : xs_hd ∈ xs_hd :: xs_t …
        rfl
        -- 🎉 no goals
      · rfl
        -- 🎉 no goals
#align fin_enum.mem_pi FinEnum.mem_pi

/-- enumerate all functions whose domain and range are finitely enumerable -/
def pi.enum (β : α → Type (max u v)) [FinEnum α] [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi.{u, v} (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))
#align fin_enum.pi.enum FinEnum.pi.enum

theorem pi.mem_enum {β : α → Type (max u v)} [FinEnum α] [∀ a, FinEnum (β a)] (f : ∀ a, β a) :
    f ∈ pi.enum.{u, v} β := by simp [pi.enum]; refine' ⟨fun a _ => f a, mem_pi _ _, rfl⟩
                               -- ⊢ ∃ a, (a ∈ pi (toList α) fun x => toList (β x)) ∧ (fun x => a x (_ : x ∈ toLi …
                                               -- 🎉 no goals
#align fin_enum.pi.mem_enum FinEnum.pi.mem_enum

instance pi.finEnum {β : α → Type (max u v)} [FinEnum α] [∀ a, FinEnum (β a)] :
    FinEnum (∀ a, β a) :=
  ofList (pi.enum.{u, v} _) fun _ => pi.mem_enum _
#align fin_enum.pi.fin_enum FinEnum.pi.finEnum

instance pfunFinEnum (p : Prop) [Decidable p] (α : p → Type) [∀ hp, FinEnum (α hp)] :
    FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simp; exact ⟨x hp, rfl⟩)
                                                  -- ⊢ x ∈ List.map (fun x x_1 => x) (toList (α hp))
                                                           -- ⊢ ∃ a, (fun x => a) = x
                                                                 -- 🎉 no goals
  else ofList [fun hp' => (hp hp').elim] (by intro; simp; ext hp'; cases hp hp')
                                             -- ⊢ x✝ ∈ [fun hp' => False.elim (_ : False)]
                                                    -- ⊢ x✝ = fun hp' => False.elim (_ : False)
                                                          -- ⊢ x✝ hp' = False.elim (_ : False)
                                                                   -- 🎉 no goals
#align fin_enum.pfun_fin_enum FinEnum.pfunFinEnum

end FinEnum
