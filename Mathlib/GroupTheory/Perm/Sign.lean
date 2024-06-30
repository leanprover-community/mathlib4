/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Order.Units
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.NormNum.Ineq

#align_import group_theory.perm.sign from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Sign of a permutation

The main definition of this file is `Equiv.Perm.sign`,
associating a `ℤˣ` sign with a permutation.

Other lemmas have been moved to `Mathlib.GroupTheory.Perm.Fintype`

-/

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} [DecidableEq α] {β : Type v}

namespace Equiv.Perm

/-- `modSwap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `Matrix.det_zero_of_row_eq`, such that each partition
sums up to `0`.
-/
def modSwap (i j : α) : Setoid (Perm α) :=
  ⟨fun σ τ => σ = τ ∨ σ = swap i j * τ, fun σ => Or.inl (refl σ), fun {σ τ} h =>
    Or.casesOn h (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, swap_mul_self_mul]),
    fun {σ τ υ} hστ hτυ => by
    cases' hστ with hστ hστ <;> cases' hτυ with hτυ hτυ <;> try rw [hστ, hτυ, swap_mul_self_mul] <;>
    simp [hστ, hτυ] -- Porting note: should close goals, but doesn't
    · simp [hστ, hτυ]
    · simp [hστ, hτυ]
    · simp [hστ, hτυ]⟩
#align equiv.perm.mod_swap Equiv.Perm.modSwap

noncomputable instance {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    DecidableRel (modSwap i j).r :=
  fun _ _ => Or.decidable

/-- Given a list `l : List α` and a permutation `f : Perm α` such that the nonfixed points of `f`
  are in `l`, recursively factors `f` as a product of transpositions. -/
def swapFactorsAux :
    ∀ (l : List α) (f : Perm α),
      (∀ {x}, f x ≠ x → x ∈ l) → { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g }
  | [] => fun f h =>
    ⟨[],
      Equiv.ext fun x => by
        rw [List.prod_nil]
        exact (Classical.not_not.1 (mt h (List.not_mem_nil _))).symm,
      by simp⟩
  | x::l => fun f h =>
    if hfx : x = f x then
      swapFactorsAux l f fun {y} hy =>
        List.mem_of_ne_of_mem (fun h : y = x => by simp [h, hfx.symm] at hy) (h hy)
    else
      let m :=
        swapFactorsAux l (swap x (f x) * f) fun {y} hy =>
          have : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem this.2 (h this.1)
      ⟨swap x (f x)::m.1, by
        rw [List.prod_cons, m.2.1, ← mul_assoc, mul_def (swap x (f x)), swap_swap, ← one_def,
          one_mul],
        fun {g} hg => ((List.mem_cons).1 hg).elim (fun h => ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩
#align equiv.perm.swap_factors_aux Equiv.Perm.swapFactorsAux

/-- `swapFactors` represents a permutation as a product of a list of transpositions.
The representation is non unique and depends on the linear order structure.
For types without linear order `truncSwapFactors` can be used. -/
def swapFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g } :=
  swapFactorsAux ((@univ α _).sort (· ≤ ·)) f fun {_ _} => (mem_sort _).2 (mem_univ _)
#align equiv.perm.swap_factors Equiv.Perm.swapFactors

/-- This computably represents the fact that any permutation can be represented as the product of
  a list of transpositions. -/
def truncSwapFactors [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swapFactorsAux l f (h _)))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)
#align equiv.perm.trunc_swap_factors Equiv.Perm.truncSwapFactors

/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_elim]
theorem swap_induction_on [Finite α] {P : Perm α → Prop} (f : Perm α) :
    P 1 → (∀ f x y, x ≠ y → P f → P (swap x y * f)) → P f := by
  cases nonempty_fintype α
  cases' (truncSwapFactors f).out with l hl
  induction' l with g l ih generalizing f
  · simp (config := { contextual := true }) only [hl.left.symm, List.prod_nil, forall_true_iff]
  · intro h1 hmul_swap
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩
    rw [← hl.1, List.prod_cons, hxy.2]
    exact
      hmul_swap _ _ _ hxy.1
        (ih _ ⟨rfl, fun v hv => hl.2 _ (List.mem_cons_of_mem _ hv)⟩ h1 hmul_swap)
#align equiv.perm.swap_induction_on Equiv.Perm.swap_induction_on

theorem mclosure_isSwap [Finite α] : Submonoid.closure { σ : Perm α | IsSwap σ } = ⊤ := by
  cases nonempty_fintype α
  refine top_unique fun x _ ↦ ?_
  obtain ⟨h1, h2⟩ := Subtype.mem (truncSwapFactors x).out
  rw [← h1]
  exact Submonoid.list_prod_mem _ fun y hy ↦ Submonoid.subset_closure (h2 y hy)

theorem closure_isSwap [Finite α] : Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_isSwap
#align equiv.perm.closure_is_swap Equiv.Perm.closure_isSwap

/-- Every finite symmetric group is generated by transpositions of adjacent elements. -/
theorem mclosure_swap_castSucc_succ (n : ℕ) :
    Submonoid.closure (Set.range fun i : Fin n ↦ swap i.castSucc i.succ) = ⊤ := by
  apply top_unique
  rw [← mclosure_isSwap, Submonoid.closure_le]
  rintro _ ⟨i, j, ne, rfl⟩
  wlog lt : i < j generalizing i j
  · rw [swap_comm]; exact this _ _ ne.symm (ne.lt_or_lt.resolve_left lt)
  induction' j using Fin.induction with j ih
  · cases lt
  have mem : swap j.castSucc j.succ ∈ Submonoid.closure
      (Set.range fun (i : Fin n) ↦ swap i.castSucc i.succ) := Submonoid.subset_closure ⟨_, rfl⟩
  obtain rfl | lts := (Fin.le_castSucc_iff.mpr lt).eq_or_lt
  · exact mem
  rw [swap_comm, ← swap_mul_swap_mul_swap (y := Fin.castSucc j) lts.ne lt.ne]
  exact mul_mem (mul_mem mem <| ih lts.ne lts) mem

/-- Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_elim]
theorem swap_induction_on' [Finite α] {P : Perm α → Prop} (f : Perm α) :
    P 1 → (∀ f x y, x ≠ y → P f → P (f * swap x y)) → P f := fun h1 IH =>
  inv_inv f ▸ swap_induction_on f⁻¹ h1 fun f => IH f⁻¹
#align equiv.perm.swap_induction_on' Equiv.Perm.swap_induction_on'

theorem isConj_swap {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : IsConj (swap w x) (swap y z) :=
  isConj_iff.2
    (have h :
      ∀ {y z : α},
        y ≠ z → w ≠ z → swap w y * swap x z * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
      fun {y z} hyz hwz => by
      rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y), mul_assoc (swap w y), ←
        mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz, ← mul_assoc,
        swap_mul_swap_mul_swap hwz.symm hyz.symm]
    if hwz : w = z then
      have hwy : w ≠ y := by rw [hwz]; exact hyz.symm
      ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
    else ⟨swap w y * swap x z, h hyz hwz⟩)
#align equiv.perm.is_conj_swap Equiv.Perm.isConj_swap

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def finPairsLT (n : ℕ) : Finset (Σ_ : Fin n, Fin n) :=
  (univ : Finset (Fin n)).sigma fun a => (range a).attachFin fun _ hm => (mem_range.1 hm).trans a.2
#align equiv.perm.fin_pairs_lt Equiv.Perm.finPairsLT

theorem mem_finPairsLT {n : ℕ} {a : Σ_ : Fin n, Fin n} : a ∈ finPairsLT n ↔ a.2 < a.1 := by
  simp only [finPairsLT, Fin.lt_iff_val_lt_val, true_and_iff, mem_attachFin, mem_range, mem_univ,
    mem_sigma]
#align equiv.perm.mem_fin_pairs_lt Equiv.Perm.mem_finPairsLT

/-- `signAux σ` is the sign of a permutation on `Fin n`, defined as the parity of the number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂` -/
def signAux {n : ℕ} (a : Perm (Fin n)) : ℤˣ :=
  ∏ x ∈ finPairsLT n, if a x.1 ≤ a x.2 then -1 else 1
#align equiv.perm.sign_aux Equiv.Perm.signAux

@[simp]
theorem signAux_one (n : ℕ) : signAux (1 : Perm (Fin n)) = 1 := by
  unfold signAux
  conv => rhs; rw [← @Finset.prod_const_one _ _ (finPairsLT n)]
  exact Finset.prod_congr rfl fun a ha => if_neg (mem_finPairsLT.1 ha).not_le
#align equiv.perm.sign_aux_one Equiv.Perm.signAux_one

/-- `signBijAux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasing order. -/
def signBijAux {n : ℕ} (f : Perm (Fin n)) (a : Σ_ : Fin n, Fin n) : Σ_ : Fin n, Fin n :=
  if _ : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩
#align equiv.perm.sign_bij_aux Equiv.Perm.signBijAux

theorem signBijAux_injOn {n : ℕ} {f : Perm (Fin n)} :
    (finPairsLT n : Set (Σ _, Fin n)).InjOn (signBijAux f) := by
  rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb h
  dsimp [signBijAux] at h
  rw [Finset.mem_coe, mem_finPairsLT] at *
  have : ¬b₁ < b₂ := hb.le.not_lt
  split_ifs at h <;>
  simp_all [(Equiv.injective f).eq_iff, eq_self_iff_true, and_self_iff, heq_iff_eq]
  · exact absurd this (not_le.mpr ha)
  · exact absurd this (not_le.mpr ha)
#align equiv.perm.sign_bij_aux_inj Equiv.Perm.signBijAux_injOn

theorem signBijAux_surj {n : ℕ} {f : Perm (Fin n)} :
    ∀ a ∈ finPairsLT n, ∃ b ∈ finPairsLT n, signBijAux f b = a :=
  fun ⟨a₁, a₂⟩ ha =>
    if hxa : f⁻¹ a₂ < f⁻¹ a₁ then
      ⟨⟨f⁻¹ a₁, f⁻¹ a₂⟩, mem_finPairsLT.2 hxa, by
        dsimp [signBijAux]
        rw [apply_inv_self, apply_inv_self, if_pos (mem_finPairsLT.1 ha)]⟩
    else
      ⟨⟨f⁻¹ a₂, f⁻¹ a₁⟩,
        mem_finPairsLT.2 <|
          (le_of_not_gt hxa).lt_of_ne fun h => by
            simp [mem_finPairsLT, f⁻¹.injective h, lt_irrefl] at ha, by
              dsimp [signBijAux]
              rw [apply_inv_self, apply_inv_self, if_neg (mem_finPairsLT.1 ha).le.not_lt]⟩
#align equiv.perm.sign_bij_aux_surj Equiv.Perm.signBijAux_surj

theorem signBijAux_mem {n : ℕ} {f : Perm (Fin n)} :
    ∀ a : Σ_ : Fin n, Fin n, a ∈ finPairsLT n → signBijAux f a ∈ finPairsLT n :=
  fun ⟨a₁, a₂⟩ ha => by
    unfold signBijAux
    split_ifs with h
    · exact mem_finPairsLT.2 h
    · exact mem_finPairsLT.2
        ((le_of_not_gt h).lt_of_ne fun h => (mem_finPairsLT.1 ha).ne (f.injective h.symm))
#align equiv.perm.sign_bij_aux_mem Equiv.Perm.signBijAux_mem

@[simp]
theorem signAux_inv {n : ℕ} (f : Perm (Fin n)) : signAux f⁻¹ = signAux f :=
  prod_nbij (signBijAux f⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj fun ⟨a, b⟩ hab ↦
    if h : f⁻¹ b < f⁻¹ a then by
      simp_all [signBijAux, dif_pos h, if_neg h.not_le, apply_inv_self, apply_inv_self,
        if_neg (mem_finPairsLT.1 hab).not_le]
    else by
      simp_all [signBijAux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self, apply_inv_self,
        if_pos (mem_finPairsLT.1 hab).le]
#align equiv.perm.sign_aux_inv Equiv.Perm.signAux_inv

theorem signAux_mul {n : ℕ} (f g : Perm (Fin n)) : signAux (f * g) = signAux f * signAux g := by
  rw [← signAux_inv g]
  unfold signAux
  rw [← prod_mul_distrib]
  refine prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj ?_
  rintro ⟨a, b⟩ hab
  dsimp only [signBijAux]
  rw [mul_apply, mul_apply]
  rw [mem_finPairsLT] at hab
  by_cases h : g b < g a
  · rw [dif_pos h]
    simp only [not_le_of_gt hab, mul_one, mul_ite, mul_neg, Perm.inv_apply_self, if_false]
  · rw [dif_neg h, inv_apply_self, inv_apply_self, if_pos hab.le]
    by_cases h₁ : f (g b) ≤ f (g a)
    · have : f (g b) ≠ f (g a) := by
        rw [Ne, f.injective.eq_iff, g.injective.eq_iff]
        exact ne_of_lt hab
      rw [if_pos h₁, if_neg (h₁.lt_of_ne this).not_le]
      rfl
    · rw [if_neg h₁, if_pos (lt_of_not_ge h₁).le]
      rfl
#align equiv.perm.sign_aux_mul Equiv.Perm.signAux_mul

private theorem signAux_swap_zero_one' (n : ℕ) : signAux (swap (0 : Fin (n + 2)) 1) = -1 :=
  show _ = ∏ x ∈ {(⟨1, 0⟩ : Σ a : Fin (n + 2), Fin (n + 2))},
      if (Equiv.swap 0 1) x.1 ≤ swap 0 1 x.2 then (-1 : ℤˣ) else 1 by
    refine Eq.symm (prod_subset (fun ⟨x₁, x₂⟩ => by
      simp (config := { contextual := true }) [mem_finPairsLT, Fin.one_pos]) fun a ha₁ ha₂ => ?_)
    rcases a with ⟨a₁, a₂⟩
    replace ha₁ : a₂ < a₁ := mem_finPairsLT.1 ha₁
    dsimp only
    rcases a₁.zero_le.eq_or_lt with (rfl | H)
    · exact absurd a₂.zero_le ha₁.not_le
    rcases a₂.zero_le.eq_or_lt with (rfl | H')
    · simp only [and_true_iff, eq_self_iff_true, heq_iff_eq, mem_singleton, Sigma.mk.inj_iff] at ha₂
      have : 1 < a₁ := lt_of_le_of_ne (Nat.succ_le_of_lt ha₁)
        (Ne.symm (by intro h; apply ha₂; simp [h]))
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 0 = 1 := by simp
      rw [swap_apply_of_ne_of_ne (ne_of_gt H) ha₂, h01, if_neg this.not_le]
    · have le : 1 ≤ a₂ := Nat.succ_le_of_lt H'
      have lt : 1 < a₁ := le.trans_lt ha₁
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 1 = 0 := by simp only [swap_apply_right]
      rcases le.eq_or_lt with (rfl | lt')
      · rw [swap_apply_of_ne_of_ne H.ne' lt.ne', h01, if_neg H.not_le]
      · rw [swap_apply_of_ne_of_ne (ne_of_gt H) (ne_of_gt lt),
          swap_apply_of_ne_of_ne (ne_of_gt H') (ne_of_gt lt'), if_neg ha₁.not_le]

private theorem signAux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
    signAux (swap (⟨0, lt_of_lt_of_le (by decide) hn⟩ : Fin n) ⟨1, lt_of_lt_of_le (by decide) hn⟩) =
      -1 := by
  rcases n with (_ | _ | n)
  · norm_num at hn
  · norm_num at hn
  · exact signAux_swap_zero_one' n

theorem signAux_swap : ∀ {n : ℕ} {x y : Fin n} (_hxy : x ≠ y), signAux (swap x y) = -1
  | 0, x, y => by intro; exact Fin.elim0 x
  | 1, x, y => by
    dsimp [signAux, swap, swapCore]
    simp only [eq_iff_true_of_subsingleton, not_true, ite_true, le_refl, prod_const,
               IsEmpty.forall_iff]
  | n + 2, x, y => fun hxy => by
    have h2n : 2 ≤ n + 2 := by exact le_add_self
    rw [← isConj_iff_eq, ← signAux_swap_zero_one h2n]
    exact (MonoidHom.mk' signAux signAux_mul).map_isConj
      (isConj_swap hxy (by exact of_decide_eq_true rfl))
#align equiv.perm.sign_aux_swap Equiv.Perm.signAux_swap

/-- When the list `l : List α` contains all nonfixed points of the permutation `f : Perm α`,
  `signAux2 l f` recursively calculates the sign of `f`. -/
def signAux2 : List α → Perm α → ℤˣ
  | [], _ => 1
  | x::l, f => if x = f x then signAux2 l f else -signAux2 l (swap x (f x) * f)
#align equiv.perm.sign_aux2 Equiv.Perm.signAux2

theorem signAux_eq_signAux2 {n : ℕ} :
    ∀ (l : List α) (f : Perm α) (e : α ≃ Fin n) (_h : ∀ x, f x ≠ x → x ∈ l),
      signAux ((e.symm.trans f).trans e) = signAux2 l f
  | [], f, e, h => by
    have : f = 1 := Equiv.ext fun y => Classical.not_not.1 (mt (h y) (List.not_mem_nil _))
    rw [this, one_def, Equiv.trans_refl, Equiv.symm_trans_self, ← one_def, signAux_one, signAux2]
  | x::l, f, e, h => by
    rw [signAux2]
    by_cases hfx : x = f x
    · rw [if_pos hfx]
      exact
        signAux_eq_signAux2 l f _ fun y (hy : f y ≠ y) =>
          List.mem_of_ne_of_mem (fun h : y = x => by simp [h, hfx.symm] at hy) (h y hy)
    · have hy : ∀ y : α, (swap x (f x) * f) y ≠ y → y ∈ l := fun y hy =>
        have : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy
        List.mem_of_ne_of_mem this.2 (h _ this.1)
      have : (e.symm.trans (swap x (f x) * f)).trans e =
          swap (e x) (e (f x)) * (e.symm.trans f).trans e := by
        ext
        rw [← Equiv.symm_trans_swap_trans, mul_def, Equiv.symm_trans_swap_trans, mul_def]
        repeat (rw [trans_apply])
        simp [swap, swapCore]
        split_ifs <;> rfl
      have hefx : e x ≠ e (f x) := mt e.injective.eq_iff.1 hfx
      rw [if_neg hfx, ← signAux_eq_signAux2 _ _ e hy, this, signAux_mul, signAux_swap hefx]
      simp only [neg_neg, one_mul, neg_mul]
#align equiv.perm.sign_aux_eq_sign_aux2 Equiv.Perm.signAux_eq_signAux2

/-- When the multiset `s : Multiset α` contains all nonfixed points of the permutation `f : Perm α`,
  `signAux2 f _` recursively calculates the sign of `f`. -/
def signAux3 [Finite α] (f : Perm α) {s : Multiset α} : (∀ x, x ∈ s) → ℤˣ :=
  Quotient.hrecOn s (fun l _ => signAux2 l f) fun l₁ l₂ h ↦ by
    rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
    refine Function.hfunext (forall_congr fun _ ↦ propext h.mem_iff) fun h₁ h₂ _ ↦ ?_
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₁ _, ← signAux_eq_signAux2 _ _ e fun _ _ => h₂ _]
#align equiv.perm.sign_aux3 Equiv.Perm.signAux3

theorem signAux3_mul_and_swap [Finite α] (f g : Perm α) (s : Multiset α) (hs : ∀ x, x ∈ s) :
    signAux3 (f * g) hs = signAux3 f hs * signAux3 g hs ∧
      Pairwise fun x y => signAux3 (swap x y) hs = -1 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  induction s using Quotient.inductionOn with | _ l => ?_
  show
    signAux2 l (f * g) = signAux2 l f * signAux2 l g ∧
    Pairwise fun x y => signAux2 l (swap x y) = -1
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.symm.trans g).trans e :=
    Equiv.ext fun h => by simp [mul_apply]
  constructor
  · rw [← signAux_eq_signAux2 _ _ e fun _ _ => hs _, ←
      signAux_eq_signAux2 _ _ e fun _ _ => hs _, ← signAux_eq_signAux2 _ _ e fun _ _ => hs _,
      hfg, signAux_mul]
  · intro x y hxy
    rw [← e.injective.ne_iff] at hxy
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => hs _, symm_trans_swap_trans, signAux_swap hxy]
#align equiv.perm.sign_aux3_mul_and_swap Equiv.Perm.signAux3_mul_and_swap

theorem signAux3_symm_trans_trans [Finite α] [DecidableEq β] [Finite β] (f : Perm α) (e : α ≃ β)
    {s : Multiset α} {t : Multiset β} (hs : ∀ x, x ∈ s) (ht : ∀ x, x ∈ t) :
    signAux3 ((e.symm.trans f).trans e) ht = signAux3 f hs := by
  -- Porting note: switched from term mode to tactic mode
  induction' t, s using Quotient.inductionOn₂ with t s ht hs
  show signAux2 _ _ = signAux2 _ _
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e'⟩⟩
  rw [← signAux_eq_signAux2 _ _ e' fun _ _ => ht _,
    ← signAux_eq_signAux2 _ _ (e.trans e') fun _ _ => hs _]
  exact congr_arg signAux
    (Equiv.ext fun x => by simp [Equiv.coe_trans, apply_eq_iff_eq, symm_trans_apply])
#align equiv.perm.sign_aux3_symm_trans_trans Equiv.Perm.signAux3_symm_trans_trans

/-- `SignType.sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`Perm α` to the group with two elements. -/
def sign [Fintype α] : Perm α →* ℤˣ :=
  MonoidHom.mk' (fun f => signAux3 f mem_univ) fun f g => (signAux3_mul_and_swap f g _ mem_univ).1
#align equiv.perm.sign Equiv.Perm.sign

section SignType.sign

variable [Fintype α]

--@[simp] Porting note (#10618): simp can prove
theorem sign_mul (f g : Perm α) : sign (f * g) = sign f * sign g :=
  MonoidHom.map_mul sign f g
#align equiv.perm.sign_mul Equiv.Perm.sign_mul

@[simp]
theorem sign_trans (f g : Perm α) : sign (f.trans g) = sign g * sign f := by
  rw [← mul_def, sign_mul]
#align equiv.perm.sign_trans Equiv.Perm.sign_trans

--@[simp] Porting note (#10618): simp can prove
theorem sign_one : sign (1 : Perm α) = 1 :=
  MonoidHom.map_one sign
#align equiv.perm.sign_one Equiv.Perm.sign_one

@[simp]
theorem sign_refl : sign (Equiv.refl α) = 1 :=
  MonoidHom.map_one sign
#align equiv.perm.sign_refl Equiv.Perm.sign_refl

--@[simp] Porting note (#10618): simp can prove
theorem sign_inv (f : Perm α) : sign f⁻¹ = sign f := by
  rw [MonoidHom.map_inv sign f, Int.units_inv_eq_self]
#align equiv.perm.sign_inv Equiv.Perm.sign_inv

@[simp]
theorem sign_symm (e : Perm α) : sign e.symm = sign e :=
  sign_inv e
#align equiv.perm.sign_symm Equiv.Perm.sign_symm

theorem sign_swap {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
  (signAux3_mul_and_swap 1 1 _ mem_univ).2 h
#align equiv.perm.sign_swap Equiv.Perm.sign_swap

@[simp]
theorem sign_swap' {x y : α} : sign (swap x y) = if x = y then 1 else -1 :=
  if H : x = y then by simp [H, swap_self] else by simp [sign_swap H, H]
#align equiv.perm.sign_swap' Equiv.Perm.sign_swap'

theorem IsSwap.sign_eq {f : Perm α} (h : f.IsSwap) : sign f = -1 :=
  let ⟨_, _, hxy⟩ := h
  hxy.2.symm ▸ sign_swap hxy.1
#align equiv.perm.is_swap.sign_eq Equiv.Perm.IsSwap.sign_eq

@[simp]
theorem sign_symm_trans_trans [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β) :
    sign ((e.symm.trans f).trans e) = sign f :=
  signAux3_symm_trans_trans f e mem_univ mem_univ
#align equiv.perm.sign_symm_trans_trans Equiv.Perm.sign_symm_trans_trans

@[simp]
theorem sign_trans_trans_symm [DecidableEq β] [Fintype β] (f : Perm β) (e : α ≃ β) :
    sign ((e.trans f).trans e.symm) = sign f :=
  sign_symm_trans_trans f e.symm
#align equiv.perm.sign_trans_trans_symm Equiv.Perm.sign_trans_trans_symm

theorem sign_prod_list_swap {l : List (Perm α)} (hl : ∀ g ∈ l, IsSwap g) :
    sign l.prod = (-1) ^ l.length := by
  have h₁ : l.map sign = List.replicate l.length (-1) :=
    List.eq_replicate.2
      ⟨by simp, fun u hu =>
        let ⟨g, hg⟩ := List.mem_map.1 hu
        hg.2 ▸ (hl _ hg.1).sign_eq⟩
  rw [← List.prod_replicate, ← h₁, List.prod_hom _ (@sign α _ _)]
#align equiv.perm.sign_prod_list_swap Equiv.Perm.sign_prod_list_swap

@[simp]
theorem sign_abs (f : Perm α) :
    |(Equiv.Perm.sign f : ℤ)| = 1 := by
  rw [Int.abs_eq_natAbs, Int.units_natAbs, Nat.cast_one]

variable (α)

theorem sign_surjective [Nontrivial α] : Function.Surjective (sign : Perm α → ℤˣ) := fun a =>
  (Int.units_eq_one_or a).elim (fun h => ⟨1, by simp [h]⟩) fun h =>
    let ⟨x, y, hxy⟩ := exists_pair_ne α
    ⟨swap x y, by rw [sign_swap hxy, h]⟩
#align equiv.perm.sign_surjective Equiv.Perm.sign_surjective

variable {α}

theorem eq_sign_of_surjective_hom {s : Perm α →* ℤˣ} (hs : Surjective s) : s = sign :=
  have : ∀ {f}, IsSwap f → s f = -1 := fun {f} ⟨x, y, hxy, hxy'⟩ =>
    hxy'.symm ▸
      by_contradiction fun h => by
        have : ∀ f, IsSwap f → s f = 1 := fun f ⟨a, b, hab, hab'⟩ => by
          rw [← isConj_iff_eq, ← Or.resolve_right (Int.units_eq_one_or _) h, hab']
          exact s.map_isConj (isConj_swap hab hxy)
        let ⟨g, hg⟩ := hs (-1)
        let ⟨l, hl⟩ := (truncSwapFactors g).out
        have : ∀ a ∈ l.map s, a = (1 : ℤˣ) := fun a ha =>
          let ⟨g, hg⟩ := List.mem_map.1 ha
          hg.2 ▸ this _ (hl.2 _ hg.1)
        have : s l.prod = 1 := by
          rw [← l.prod_hom s, List.eq_replicate_length.2 this, List.prod_replicate, one_pow]
        rw [hl.1, hg] at this
        exact absurd this (by simp_all)
  MonoidHom.ext fun f => by
    let ⟨l, hl₁, hl₂⟩ := (truncSwapFactors f).out
    have hsl : ∀ a ∈ l.map s, a = (-1 : ℤˣ) := fun a ha =>
      let ⟨g, hg⟩ := List.mem_map.1 ha
      hg.2 ▸ this (hl₂ _ hg.1)
    rw [← hl₁, ← l.prod_hom s, List.eq_replicate_length.2 hsl, List.length_map, List.prod_replicate,
      sign_prod_list_swap hl₂]
#align equiv.perm.eq_sign_of_surjective_hom Equiv.Perm.eq_sign_of_surjective_hom

theorem sign_subtypePerm (f : Perm α) {p : α → Prop} [DecidablePred p] (h₁ : ∀ x, p x ↔ p (f x))
    (h₂ : ∀ x, f x ≠ x → p x) : sign (subtypePerm f h₁) = sign f := by
  let l := (truncSwapFactors (subtypePerm f h₁)).out
  have hl' : ∀ g' ∈ l.1.map ofSubtype, IsSwap g' := fun g' hg' =>
    let ⟨g, hg⟩ := List.mem_map.1 hg'
    hg.2 ▸ (l.2.2 _ hg.1).of_subtype_isSwap
  have hl'₂ : (l.1.map ofSubtype).prod = f := by
    rw [l.1.prod_hom ofSubtype, l.2.1, ofSubtype_subtypePerm _ h₂]
  conv =>
    congr
    rw [← l.2.1]
  simp_rw [← hl'₂]
  rw [sign_prod_list_swap l.2.2, sign_prod_list_swap hl', List.length_map]
#align equiv.perm.sign_subtype_perm Equiv.Perm.sign_subtypePerm

theorem sign_eq_sign_of_equiv [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) : sign f = sign g := by
  have hg : g = (e.symm.trans f).trans e := Equiv.ext <| by simp [h]
  rw [hg, sign_symm_trans_trans]
#align equiv.perm.sign_eq_sign_of_equiv Equiv.Perm.sign_eq_sign_of_equiv

theorem sign_bij [DecidableEq β] [Fintype β] {f : Perm α} {g : Perm β} (i : ∀ x : α, f x ≠ x → β)
    (h : ∀ x hx hx', i (f x) hx' = g (i x hx)) (hi : ∀ x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ → x₁ = x₂)
    (hg : ∀ y, g y ≠ y → ∃ x hx, i x hx = y) : sign f = sign g :=
  calc
    sign f = sign (subtypePerm f <| by simp : Perm { x // f x ≠ x }) :=
      (sign_subtypePerm _ _ fun _ => id).symm
    _ = sign (subtypePerm g <| by simp : Perm { x // g x ≠ x }) :=
      sign_eq_sign_of_equiv _ _
        (Equiv.ofBijective
          (fun x : { x // f x ≠ x } =>
            (⟨i x.1 x.2, by
                have : f (f x) ≠ f x := mt (fun h => f.injective h) x.2
                rw [← h _ x.2 this]
                exact mt (hi _ _ this x.2) x.2⟩ :
              { y // g y ≠ y }))
          ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ h => Subtype.eq (hi _ _ _ _ (Subtype.mk.inj h)), fun ⟨y, hy⟩ =>
            let ⟨x, hfx, hx⟩ := hg y hy
            ⟨⟨x, hfx⟩, Subtype.eq hx⟩⟩)
        fun ⟨x, _⟩ => Subtype.eq (h x _ _)
    _ = sign g := sign_subtypePerm _ _ fun _ => id
#align equiv.perm.sign_bij Equiv.Perm.sign_bij

/-- If we apply `prod_extendRight a (σ a)` for all `a : α` in turn,
we get `prod_congrRight σ`. -/
theorem prod_prodExtendRight {α : Type*} [DecidableEq α] (σ : α → Perm β) {l : List α}
    (hl : l.Nodup) (mem_l : ∀ a, a ∈ l) :
    (l.map fun a => prodExtendRight a (σ a)).prod = prodCongrRight σ := by
  ext ⟨a, b⟩ : 1
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices a ∈ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, σ a b) ∨
      a ∉ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, b) by
    obtain ⟨_, prod_eq⟩ := Or.resolve_right this (not_and.mpr fun h _ => h (mem_l a))
    rw [prod_eq, prodCongrRight_apply]
  clear mem_l
  induction' l with a' l ih
  · refine Or.inr ⟨List.not_mem_nil _, ?_⟩
    rw [List.map_nil, List.prod_nil, one_apply]
  rw [List.map_cons, List.prod_cons, mul_apply]
  rcases ih (List.nodup_cons.mp hl).2 with (⟨mem_l, prod_eq⟩ | ⟨not_mem_l, prod_eq⟩) <;>
    rw [prod_eq]
  · refine Or.inl ⟨List.mem_cons_of_mem _ mem_l, ?_⟩
    rw [prodExtendRight_apply_ne _ fun h : a = a' => (List.nodup_cons.mp hl).1 (h ▸ mem_l)]
  by_cases ha' : a = a'
  · rw [← ha'] at *
    refine Or.inl ⟨l.mem_cons_self a, ?_⟩
    rw [prodExtendRight_apply_eq]
  · refine Or.inr ⟨fun h => not_or_of_not ha' not_mem_l ((List.mem_cons).mp h), ?_⟩
    rw [prodExtendRight_apply_ne _ ha']
#align equiv.perm.prod_prod_extend_right Equiv.Perm.prod_prodExtendRight

section congr

variable [DecidableEq β] [Fintype β]

@[simp]
theorem sign_prodExtendRight (a : α) (σ : Perm β) : sign (prodExtendRight a σ) = sign σ :=
  sign_bij (fun (ab : α × β) _ => ab.snd)
    (fun ⟨a', b⟩ hab _ => by simp [eq_of_prodExtendRight_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h => by
      simpa [eq_of_prodExtendRight_ne hab₁, eq_of_prodExtendRight_ne hab₂] using h)
    fun y hy => ⟨(a, y), by simpa, by simp⟩
#align equiv.perm.sign_prod_extend_right Equiv.Perm.sign_prodExtendRight

theorem sign_prodCongrRight (σ : α → Perm β) : sign (prodCongrRight σ) = ∏ k, sign (σ k) := by
  obtain ⟨l, hl, mem_l⟩ := Finite.exists_univ_list α
  have l_to_finset : l.toFinset = Finset.univ := by
    apply eq_top_iff.mpr
    intro b _
    exact List.mem_toFinset.mpr (mem_l b)
  rw [← prod_prodExtendRight σ hl mem_l, map_list_prod sign, List.map_map, ← l_to_finset,
    List.prod_toFinset _ hl]
  simp_rw [← fun a => sign_prodExtendRight a (σ a), Function.comp]
#align equiv.perm.sign_prod_congr_right Equiv.Perm.sign_prodCongrRight

theorem sign_prodCongrLeft (σ : α → Perm β) : sign (prodCongrLeft σ) = ∏ k, sign (σ k) := by
  refine (sign_eq_sign_of_equiv _ _ (prodComm β α) ?_).trans (sign_prodCongrRight σ)
  rintro ⟨b, α⟩
  rfl
#align equiv.perm.sign_prod_congr_left Equiv.Perm.sign_prodCongrLeft

@[simp]
theorem sign_permCongr (e : α ≃ β) (p : Perm α) : sign (e.permCongr p) = sign p :=
  sign_eq_sign_of_equiv _ _ e.symm (by simp)
#align equiv.perm.sign_perm_congr Equiv.Perm.sign_permCongr

@[simp]
theorem sign_sumCongr (σa : Perm α) (σb : Perm β) : sign (sumCongr σa σb) = sign σa * sign σb := by
  suffices sign (sumCongr σa (1 : Perm β)) = sign σa ∧ sign (sumCongr (1 : Perm α) σb) = sign σb
    by rw [← this.1, ← this.2, ← sign_mul, sumCongr_mul, one_mul, mul_one]
  constructor
  · refine σa.swap_induction_on ?_ fun σa' a₁ a₂ ha ih => ?_
    · simp
    · rw [← one_mul (1 : Perm β), ← sumCongr_mul, sign_mul, sign_mul, ih, sumCongr_swap_one,
        sign_swap ha, sign_swap (Sum.inl_injective.ne_iff.mpr ha)]
  · refine σb.swap_induction_on ?_ fun σb' b₁ b₂ hb ih => ?_
    · simp
    · rw [← one_mul (1 : Perm α), ← sumCongr_mul, sign_mul, sign_mul, ih, sumCongr_one_swap,
        sign_swap hb, sign_swap (Sum.inr_injective.ne_iff.mpr hb)]
#align equiv.perm.sign_sum_congr Equiv.Perm.sign_sumCongr

@[simp]
theorem sign_subtypeCongr {p : α → Prop} [DecidablePred p] (ep : Perm { a // p a })
    (en : Perm { a // ¬p a }) : sign (ep.subtypeCongr en) = sign ep * sign en := by
  simp [subtypeCongr]
#align equiv.perm.sign_subtype_congr Equiv.Perm.sign_subtypeCongr

@[simp]
theorem sign_extendDomain (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    Equiv.Perm.sign (e.extendDomain f) = Equiv.Perm.sign e := by
  simp only [Equiv.Perm.extendDomain, sign_subtypeCongr, sign_permCongr, sign_refl, mul_one]
#align equiv.perm.sign_extend_domain Equiv.Perm.sign_extendDomain

@[simp]
theorem sign_ofSubtype {p : α → Prop} [DecidablePred p] (f : Equiv.Perm (Subtype p)) :
    sign (ofSubtype f) = sign f :=
  sign_extendDomain f (Equiv.refl (Subtype p))
#align equiv.perm.sign_of_subtype Equiv.Perm.sign_ofSubtype

end congr

end SignType.sign

end Equiv.Perm
