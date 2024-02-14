/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
import Mathlib.Data.List.Chain

#align_import data.list.destutter from "leanprover-community/mathlib"@"7b78d1776212a91ecc94cf601f83bdcc46b04213"

/-!
# Destuttering of Lists

This file proves theorems about `List.destutter` (in `Data.List.Defs`), which greedily removes all
non-related items that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].destutter (≠) = [2, 3, 2]`.
Note that we make no guarantees of being the longest sublist with this property; e.g.,
`[123, 1, 2, 5, 543, 1000].destutter (<) = [123, 543, 1000]`, but a longer ascending chain could be
`[1, 2, 5, 543, 1000]`.

## Main statements

* `List.destutter_sublist`: `l.destutter` is a sublist of `l`.
* `List.destutter_is_chain'`: `l.destutter` satisfies `Chain' R`.
* Analogies of these theorems for `List.destutter'`, which is the `destutter` equivalent of `Chain`.

## Tags

adjacent, chain, duplicates, remove, list, stutter, destutter
-/

open Function

variable {α β : Type*} (l l₂ : List α) (R : α → α → Prop) [DecidableRel R] {a b : α}

variable {R₂ : β → β → Prop} [DecidableRel R₂]

namespace List

@[simp]
theorem destutter'_nil : destutter' R a [] = [a] :=
  rfl
#align list.destutter'_nil List.destutter'_nil

theorem destutter'_cons :
    (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl
#align list.destutter'_cons List.destutter'_cons

variable {R}

@[simp]
theorem destutter'_cons_pos (h : R b a) : (a :: l).destutter' R b = b :: l.destutter' R a := by
  rw [destutter', if_pos h]
#align list.destutter'_cons_pos List.destutter'_cons_pos

@[simp]
theorem destutter'_cons_neg (h : ¬R b a) : (a :: l).destutter' R b = l.destutter' R b := by
  rw [destutter', if_neg h]
#align list.destutter'_cons_neg List.destutter'_cons_neg

variable (R)

@[simp]
theorem destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] := by
  split_ifs with h <;> simp! [h]
#align list.destutter'_singleton List.destutter'_singleton

theorem destutter'_sublist (a) : l.destutter' R a <+ a :: l := by
  induction' l with b l hl generalizing a
  · simp
  rw [destutter']
  split_ifs
  · exact Sublist.cons₂ a (hl b)
  · exact (hl a).trans ((l.sublist_cons b).cons_cons a)
#align list.destutter'_sublist List.destutter'_sublist

theorem mem_destutter' (a) : a ∈ l.destutter' R a := by
  induction' l with b l hl
  · simp
  rw [destutter']
  split_ifs
  · simp
  · assumption
#align list.mem_destutter' List.mem_destutter'

theorem destutter'_is_chain : ∀ l : List α, ∀ {a b}, R a b → (l.destutter' R b).Chain R a
  | [], a, b, h => chain_singleton.mpr h
  | c :: l, a, b, h => by
    rw [destutter']
    split_ifs with hbc
    · rw [chain_cons]
      exact ⟨h, destutter'_is_chain l hbc⟩
    · exact destutter'_is_chain l h
#align list.destutter'_is_chain List.destutter'_is_chain

theorem destutter'_is_chain' (a) : (l.destutter' R a).Chain' R := by
  induction' l with b l hl generalizing a
  · simp
  rw [destutter']
  split_ifs with h
  · exact destutter'_is_chain R l h
  · exact hl a
#align list.destutter'_is_chain' List.destutter'_is_chain'

theorem destutter'_of_chain (h : l.Chain R a) : l.destutter' R a = a :: l := by
  induction' l with b l hb generalizing a
  · simp
  obtain ⟨h, hc⟩ := chain_cons.mp h
  rw [l.destutter'_cons_pos h, hb hc]
#align list.destutter'_of_chain List.destutter'_of_chain

@[simp]
theorem destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ l.Chain R a :=
  ⟨fun h => by
    suffices Chain' R (a::l) by
      assumption
    rw [← h]
    exact l.destutter'_is_chain' R a, destutter'_of_chain _ _⟩
#align list.destutter'_eq_self_iff List.destutter'_eq_self_iff

theorem destutter'_ne_nil : l.destutter' R a ≠ [] :=
  ne_nil_of_mem <| l.mem_destutter' R a
#align list.destutter'_ne_nil List.destutter'_ne_nil

@[simp]
theorem destutter_nil : ([] : List α).destutter R = [] :=
  rfl
#align list.destutter_nil List.destutter_nil

theorem destutter_cons' : (a :: l).destutter R = destutter' R a l :=
  rfl
#align list.destutter_cons' List.destutter_cons'

theorem destutter_cons_cons :
    (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl
#align list.destutter_cons_cons List.destutter_cons_cons

@[simp]
theorem destutter_singleton : destutter R [a] = [a] :=
  rfl
#align list.destutter_singleton List.destutter_singleton

@[simp]
theorem destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
  destutter_cons_cons _ R
#align list.destutter_pair List.destutter_pair

theorem destutter_sublist : ∀ l : List α, l.destutter R <+ l
  | [] => Sublist.slnil
  | h :: l => l.destutter'_sublist R h
#align list.destutter_sublist List.destutter_sublist

theorem destutter_is_chain' : ∀ l : List α, (l.destutter R).Chain' R
  | [] => List.chain'_nil
  | h :: l => l.destutter'_is_chain' R h
#align list.destutter_is_chain' List.destutter_is_chain'

theorem destutter_of_chain' : ∀ l : List α, l.Chain' R → l.destutter R = l
  | [], _ => rfl
  | _ :: l, h => l.destutter'_of_chain _ h
#align list.destutter_of_chain' List.destutter_of_chain'

@[simp]
theorem destutter_eq_self_iff : ∀ l : List α, l.destutter R = l ↔ l.Chain' R
  | [] => by simp
  | a :: l => l.destutter'_eq_self_iff R a
#align list.destutter_eq_self_iff List.destutter_eq_self_iff

theorem destutter_idem : (l.destutter R).destutter R = l.destutter R :=
  destutter_of_chain' R _ <| l.destutter_is_chain' R
#align list.destutter_idem List.destutter_idem

@[simp]
theorem destutter_eq_nil : ∀ {l : List α}, destutter R l = [] ↔ l = []
  | [] => Iff.rfl
  | _ :: l => ⟨fun h => absurd h <| l.destutter'_ne_nil R, fun h => nomatch h⟩
#align list.destutter_eq_nil List.destutter_eq_nil

/-- For a relation-preserving map, `destutter'` commutes with `map`. -/
theorem map_destutter (f : α → β) (h : ∀ a b, R a b ↔ R₂ (f a) (f b)) :
    (l.destutter R).map f = (l.map f).destutter R₂ := by
  cases h2 : l with
  | nil => simp -- l = []
  | cons a as =>
    clear h2
    induction as generalizing a with
    | nil => simp -- l = a :: []
    | cons a2 bs ih => -- l = a :: a2 :: bs
      repeat rw [map_cons, destutter_cons_cons]
      simp_rw [← h a a2]
      by_cases hr : (R a a2) <;>
        simp [hr, ← destutter_cons', ih]

/-- For a injective function `f`, `destutter' (·≠·)` commutes with `map f`. -/
theorem map_destutter_ne {f : α → β} (h : Injective f) [DecidableEq α] [DecidableEq β] :
    (l.destutter (·≠·)).map f = (l.map f).destutter (·≠·) :=
  map_destutter l _ f fun _ _ ↦ h.ne_iff.symm

/-- `destutter'` on a relation like ≠ or <, whose negation is transitive, has length monotonic
    under a ¬R changing of the first element. -/
theorem length_destutter'_cotrans_ge [i : IsTrans α Rᶜ] (hba : ¬R b a) :
    (List.destutter' R b l).length ≤ (List.destutter' R a l).length := by
  induction l generalizing a with
  | nil => simp
  | cons c cs ih =>
    by_cases hbc : R b c
    case pos =>
      have hac : ¬Rᶜ a c := (mt (_root_.trans hba)) (not_not.2 hbc)
      simp_rw [destutter', if_pos (not_not.1 hac), if_pos hbc, length_cons, le_refl]
    case neg =>
      simp only [destutter', if_neg hbc]
      by_cases hac : R a c
      case pos =>
        simp only [if_pos hac, length_cons]
        exact Nat.le_succ_of_le (ih hbc)
      case neg =>
        simp only [if_neg hac]
        exact ih hba

/-- `List.destutter'` on a relation like `≠`, whose negation is an equivalence, gives the same
length if the first elements are not related. -/
theorem length_destutter'_congr [IsEquiv α Rᶜ] (hab : ¬R a b) :
    (l.destutter' R a).length = (l.destutter' R b).length := by
  apply eq_of_le_of_not_lt
  · exact length_destutter'_cotrans_ge _ _ hab
  · apply not_lt_of_ge
    exact length_destutter'_cotrans_ge _ _ (symm hab : Rᶜ b a)

/-- `List.destutter'` on a relation like ≠, whose negation is an equivalence, has length
    monotonic under List.cons -/
/-
TODO: Replace this lemma by the more general version:
theorem Sublist.length_destutter'_mono [IsEquiv α Rᶜ] (h : a :: l₁ <+ b :: l₂) :
    (List.destutter' R a l₁).length ≤ (List.destutter' R b l₂).length
-/
theorem le_length_destutter'_cons [IsEquiv α Rᶜ] :
    (List.destutter' R b l).length ≤ (List.destutter' R a (b :: l)).length := by
  cases l with
  | nil => by_cases hab : (R a b) <;> simp_all [Nat.le_succ]
  | cons c cs =>
    by_cases hab : (R a b)
    case pos => simp [destutter', if_pos hab, Nat.le_succ]
    obtain hac | hac : R a c ∨ Rᶜ a c := em _
    · have hbc : ¬Rᶜ b c := mt (_root_.trans hab) (not_not.2 hac)
      simp [destutter', if_pos hac, if_pos (not_not.1 hbc), if_neg hab]
    · have hbc : ¬R b c := trans (symm hab) hac
      apply le_of_eq
      simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
      exact (length_destutter'_congr cs R hab).symm

/-- `List.destutter` on a relation like ≠, whose negation is an equivalence, has length
    monotonic under List.cons -/
theorem length_destutter_cons_ge_length_destutter [IsEquiv α Rᶜ] :
    (l.destutter R).length ≤ ((a::l).destutter R).length := by
  cases l
  · simp [destutter]
  · exact le_length_destutter'_cons _ R

/-- `destutter ≠` has length monotonic under List.cons --/
theorem length_destutter_ne_cons_ge_length_destutter [DecidableEq α] :
    (l.destutter (·≠·)).length ≤ ((a::l).destutter (·≠·)).length :=
  length_destutter_cons_ge_length_destutter l (·≠·)

/-- `destutter` of relations like `≠`, whose negation is an equivalence relation,
    gives a list of maximal length over any chain. In other words: `l.destutter R` is an
    R-chain sublist of l, and is at least as long as any other R-chain sublist.
-/
theorem Chain.length_le_length_destutter [IsEquiv α Rᶜ] (h₁ : l₂ <+ l) (h₂ : l₂.Chain' R) :
    l₂.length ≤ (l.destutter R).length := by
  set n := l.length with hn
  revert hn
  --Do induction on the length of l. The case of zero length is easy.
  induction n generalizing l l₂ with
  | zero => -- if l is length zero, l₂ is too, done.
    intro hn
    rw [Nat.zero_eq] at hn
    rw [length_eq_zero.mp hn.symm] at h₁ ⊢
    simp [sublist_nil.mp h₁]
  | succ n ih => -- otherwise induction on lists l of length at most n1...
    intro hn
    cases hl₂ : l₂ with
    --l.dedup always starts with the first element of l.
    | nil => simp only [length_nil, zero_le] -- if l2 is length zero, done.
    | cons o os => -- otherwise write l₂ = o::os
      cases l with -- deconstruct l = a::as
      | nil => simp at hn -- l can't be [], contradiction with 'succ n1 ih', a nonzero length
      | cons a as =>
        by_cases hao : (o=a) --split on whether l₂ starts with a or not
        case neg =>
          --If l₂ doesn't start with the first element, write l = a::as.
          --Then l.dedup.length ≥ as.dedup.length ≥ l₂.length, by monotonicity of destutter
          --length and induction respectively.
          rw [← hl₂]
          calc length ((a :: as).destutter R)
            _ ≥ length (as.destutter R) := length_destutter_cons_ge_length_destutter as R
            _ ≥ length l₂ := by
              apply ih as l₂
              · rw [hl₂] at h₁ ⊢
                apply Sublist.of_cons_of_ne hao h₁
              · assumption
              · rwa [length_cons, Nat.succ.injEq] at hn
        case pos =>
          --If l₂ does start with the first element, write l₂ = a::os.
          rw [hao] at hl₂ ⊢
          have hlos : l₂.length = Nat.succ os.length :=
            hl₂ ▸ length_cons o os
          cases as with -- deconstruct as = b::bs
          | nil => -- when l₂ = [a]
            have hlen2 : l₂.length ≤ [a].length := Sublist.length_le h₁
            rw [length_singleton] at hlen2
            simp only [destutter_singleton, length_singleton, length_cons]
            exact le_of_eq_of_le hlos.symm hlen2
          | cons b bs => -- Okay! l₂ = a::os, l = a::b::bs.
            cases hos : os with -- deconstruct os=p::ps
            | nil =>
              simp only [destutter, length_singleton]
              exact List.length_pos_of_ne_nil (destutter'_ne_nil _ _)
            | cons p ps =>
              rw [hos] at hl₂
              -- One more split needed: does a≅b or not?
              by_cases hab : R a b
              case neg =>
                --If a≅b, then l.dedup does not contain b, and l₂ doesn't either. So we can define
                --l₃ = a::bs, we know that l.dedup = l₃.dedup, and l₂ is a chain sublist of l₃ just
                --like l. So we can apply the inductive hypothesis.
                simp only [destutter, destutter', ite_not, length_cons,
                    ge_iff_le, hab, not_true_eq_false, ite_false]
                have hlp := hos.symm ▸ (length_cons p ps)
                rw [← hlp, ← hlos]
                apply ih (a::bs) l₂
                · rw [hl₂] at h₁ ⊢
                  apply cons_sublist_cons.mpr
                  apply Sublist.of_cons_of_ne _ (cons_sublist_cons.mp h₁)
                  by_contra hpb
                  exact hab (hpb ▸ (rel_of_chain_cons (hl₂ ▸ h₂)))
                · assumption
                · rwa [length_cons, Nat.succ.injEq] at hn
              case pos =>
                --If a≇b, then l.dedup starts with [a,b...] and we can write l.dedup.length =
                --1 + as.dedup.length ≥ l2.length, where ≥ is the inductive hypothesis.
                rw [← hl₂]
                calc length ((a::b::bs).destutter R)
                  _ = length ((b::bs).destutter R) + 1 := ?_
                  _ ≥ length os + 1 := ?_
                  _ = length l₂ := by simp [hl₂, hos];
                · dsimp [destutter, destutter']
                  rw [if_pos hab, length_cons]
                · rw [ge_iff_le, add_le_add_iff_right]
                  apply ih (b::bs) os
                  · exact hos ▸ sublist_of_cons_sublist_cons (hl₂ ▸ h₁)
                  · simp_all
                  · rwa [length_cons, Nat.succ.injEq] at hn

/-- `destutter` of `≠` gives a list of maximal length over any chain.
    In other words: (l.destutter ≠) is an ≠-chain sublist of l, and is at
    least as long as any other ≠-chain sublist.
-/
theorem length_destutter_maximal_chain_neg_trans [DecidableEq α] (h₁ : l₂ <+ l)
    (h₂ : l₂.Chain' (·≠·)) : l₂.length ≤ (l.destutter (·≠·)).length := by
  apply Chain.length_le_length_destutter l l₂ (·≠·) h₁ h₂

end List
