/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module group_theory.perm.sign
! leanprover-community/mathlib commit f694c7dead66f5d4c80f446c796a5aad14707f0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Perm.Support
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.Data.Finset.Fin
import Mathbin.Data.Int.Order.Units

/-!
# Sign of a permutation

The main definition of this file is `equiv.perm.sign`, associating a `ℤˣ` sign with a
permutation.

This file also contains miscellaneous lemmas about `equiv.perm` and `equiv.swap`, building on top
of those in `data/equiv/basic` and other files in `group_theory/perm/*`.

-/


universe u v

open Equiv Function Fintype Finset

open BigOperators

variable {α : Type u} {β : Type v}

-- An example on how to determine the order of an element of a finite group.
example : orderOf (-1 : ℤˣ) = 2 :=
  orderOf_eq_prime (Int.units_sq _) (by decide)

namespace Equiv.Perm

/-- `mod_swap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `matrix.det_zero_of_row_eq`, such that each partition
sums up to `0`.
-/
def modSwap [DecidableEq α] (i j : α) : Setoid (Perm α) :=
  ⟨fun σ τ => σ = τ ∨ σ = swap i j * τ, fun σ => Or.inl (refl σ), fun σ τ h =>
    Or.cases_on h (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, swap_mul_self_mul]),
    fun σ τ υ hστ hτυ => by
    cases hστ <;> cases hτυ <;> try rw [hστ, hτυ, swap_mul_self_mul] <;> simp [hστ, hτυ]⟩
#align equiv.perm.mod_swap Equiv.Perm.modSwap

instance {α : Type _} [Fintype α] [DecidableEq α] (i j : α) : DecidableRel (modSwap i j).R :=
  fun σ τ => Or.decidable

theorem perm_inv_on_of_perm_on_finset {s : Finset α} {f : Perm α} (h : ∀ x ∈ s, f x ∈ s) {y : α}
    (hy : y ∈ s) : f⁻¹ y ∈ s :=
  by
  have h0 : ∀ y ∈ s, ∃ (x : _)(hx : x ∈ s), y = (fun i (hi : i ∈ s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i hi => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp HEq) rfl.ge
  obtain ⟨y2, hy2, heq⟩ := h0 y hy
  convert hy2
  rw [HEq]
  simp only [inv_apply_self]
#align equiv.perm.perm_inv_on_of_perm_on_finset Equiv.Perm.perm_inv_on_of_perm_on_finset

theorem perm_inv_mapsTo_of_mapsTo (f : Perm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s) :
    Set.MapsTo (f⁻¹ : _) s s := by
  cases nonempty_fintype s <;>
    exact fun x hx =>
      set.mem_to_finset.mp <|
        perm_inv_on_of_perm_on_finset
          (fun a ha => set.mem_to_finset.mpr (h (set.mem_to_finset.mp ha)))
          (set.mem_to_finset.mpr hx)
#align equiv.perm.perm_inv_maps_to_of_maps_to Equiv.Perm.perm_inv_mapsTo_of_mapsTo

@[simp]
theorem perm_inv_mapsTo_iff_mapsTo {f : Perm α} {s : Set α} [Finite s] :
    Set.MapsTo (f⁻¹ : _) s s ↔ Set.MapsTo f s s :=
  ⟨perm_inv_mapsTo_of_mapsTo f⁻¹, perm_inv_mapsTo_of_mapsTo f⟩
#align equiv.perm.perm_inv_maps_to_iff_maps_to Equiv.Perm.perm_inv_mapsTo_iff_mapsTo

theorem perm_inv_on_of_perm_on_finite {f : Perm α} {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) {x : α} (hx : p x) : p (f⁻¹ x) :=
  perm_inv_mapsTo_of_mapsTo f h hx
#align equiv.perm.perm_inv_on_of_perm_on_finite Equiv.Perm.perm_inv_on_of_perm_on_finite

/-- If the permutation `f` maps `{x // p x}` into itself, then this returns the permutation
  on `{x // p x}` induced by `f`. Note that the `h` hypothesis is weaker than for
  `equiv.perm.subtype_perm`. -/
abbrev subtypePermOfFintype (f : Perm α) {p : α → Prop} [Fintype { x // p x }]
    (h : ∀ x, p x → p (f x)) : Perm { x // p x } :=
  f.subtypePerm fun x => ⟨h x, fun h₂ => f.inv_apply_self x ▸ perm_inv_on_of_perm_on_finite h h₂⟩
#align equiv.perm.subtype_perm_of_fintype Equiv.Perm.subtypePermOfFintype

@[simp]
theorem subtypePermOfFintype_apply (f : Perm α) {p : α → Prop} [Fintype { x // p x }]
    (h : ∀ x, p x → p (f x)) (x : { x // p x }) : subtypePermOfFintype f h x = ⟨f x, h x x.2⟩ :=
  rfl
#align equiv.perm.subtype_perm_of_fintype_apply Equiv.Perm.subtypePermOfFintype_apply

@[simp]
theorem subtypePermOfFintype_one (p : α → Prop) [Fintype { x // p x }]
    (h : ∀ x, p x → p ((1 : Perm α) x)) : @subtypePermOfFintype α 1 p _ h = 1 :=
  Equiv.ext fun ⟨_, _⟩ => rfl
#align equiv.perm.subtype_perm_of_fintype_one Equiv.Perm.subtypePermOfFintype_one

theorem perm_mapsTo_inl_iff_mapsTo_inr {m n : Type _} [Finite m] [Finite n] (σ : Perm (Sum m n)) :
    Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) ↔
      Set.MapsTo σ (Set.range Sum.inr) (Set.range Sum.inr) :=
  by
  cases nonempty_fintype m
  cases nonempty_fintype n
  constructor <;>
    ( intro h
      classical
        rw [← perm_inv_maps_to_iff_maps_to] at h
        intro x
        cases' hx : σ x with l r)
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
    rw [← hx, σ.inv_apply_self] at hy
    exact absurd hy Sum.inl_ne_inr
  · rintro ⟨a, ha⟩
    exact ⟨r, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨l, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
    rw [← hx, σ.inv_apply_self] at hy
    exact absurd hy Sum.inr_ne_inl
#align equiv.perm.perm_maps_to_inl_iff_maps_to_inr Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr

theorem mem_sumCongrHom_range_of_perm_mapsTo_inl {m n : Type _} [Finite m] [Finite n]
    {σ : Perm (Sum m n)} (h : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl)) :
    σ ∈ (sumCongrHom m n).range := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  classical
    have h1 : ∀ x : Sum m n, (∃ a : m, Sum.inl a = x) → ∃ a : m, Sum.inl a = σ x :=
      by
      rintro x ⟨a, ha⟩
      apply h
      rw [← ha]
      exact ⟨a, rfl⟩
    have h3 : ∀ x : Sum m n, (∃ b : n, Sum.inr b = x) → ∃ b : n, Sum.inr b = σ x :=
      by
      rintro x ⟨b, hb⟩
      apply (perm_maps_to_inl_iff_maps_to_inr σ).mp h
      rw [← hb]
      exact ⟨b, rfl⟩
    let σ₁' := subtype_perm_of_fintype σ h1
    let σ₂' := subtype_perm_of_fintype σ h3
    let σ₁ := perm_congr (Equiv.ofInjective _ Sum.inl_injective).symm σ₁'
    let σ₂ := perm_congr (Equiv.ofInjective _ Sum.inr_injective).symm σ₂'
    rw [MonoidHom.mem_range, Prod.exists]
    use σ₁, σ₂
    rw [perm.sum_congr_hom_apply]
    ext
    cases' x with a b
    · rw [Equiv.sumCongr_apply, Sum.map_inl, perm_congr_apply, Equiv.symm_symm,
        apply_of_injective_symm Sum.inl_injective]
      erw [subtype_perm_apply]
      rw [of_injective_apply, Subtype.coe_mk, Subtype.coe_mk]
    · rw [Equiv.sumCongr_apply, Sum.map_inr, perm_congr_apply, Equiv.symm_symm,
        apply_of_injective_symm Sum.inr_injective]
      erw [subtype_perm_apply]
      rw [of_injective_apply, Subtype.coe_mk, Subtype.coe_mk]
#align equiv.perm.mem_sum_congr_hom_range_of_perm_maps_to_inl Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl

theorem Disjoint.orderOf {σ τ : Perm α} (hστ : Disjoint σ τ) :
    orderOf (σ * τ) = Nat.lcm (orderOf σ) (orderOf τ) :=
  haveI h : ∀ n : ℕ, (σ * τ) ^ n = 1 ↔ σ ^ n = 1 ∧ τ ^ n = 1 := fun n => by
    rw [hστ.commute.mul_pow, disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n)]
  Nat.dvd_antisymm hστ.commute.order_of_mul_dvd_lcm
    (Nat.lcm_dvd
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).1)
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).2))
#align equiv.perm.disjoint.order_of Equiv.Perm.Disjoint.orderOf

theorem Disjoint.extendDomain {α : Type _} {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)
    {σ τ : Perm α} (h : Disjoint σ τ) : Disjoint (σ.extendDomain f) (τ.extendDomain f) :=
  by
  intro b
  by_cases pb : p b
  ·
    refine' (h (f.symm ⟨b, pb⟩)).imp _ _ <;>
      · intro h
        rw [extend_domain_apply_subtype _ _ pb, h, apply_symm_apply, Subtype.coe_mk]
  · left
    rw [extend_domain_apply_not_subtype _ _ pb]
#align equiv.perm.disjoint.extend_domain Equiv.Perm.Disjoint.extendDomain

variable [DecidableEq α]

section Fintype

variable [Fintype α]

theorem support_pow_coprime {σ : Perm α} {n : ℕ} (h : Nat.coprime n (orderOf σ)) :
    (σ ^ n).Support = σ.Support :=
  by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  exact
    le_antisymm (support_pow_le σ n)
      (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m))
#align equiv.perm.support_pow_coprime Equiv.Perm.support_pow_coprime

end Fintype

/- warning: equiv.perm.swap_factors_aux -> Equiv.Perm.swapFactorsAux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (f : Equiv.Perm.{succ u1} α), (forall {x : α}, (Ne.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f x) x) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) -> (Subtype.{succ u1} (List.{u1} (Equiv.Perm.{succ u1} α)) (fun (l : List.{u1} (Equiv.Perm.{succ u1} α)) => And (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (List.prod.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) l) f) (forall (g : Equiv.Perm.{succ u1} α), (Membership.Mem.{u1, u1} (Equiv.Perm.{succ u1} α) (List.{u1} (Equiv.Perm.{succ u1} α)) (List.hasMem.{u1} (Equiv.Perm.{succ u1} α)) g l) -> (Equiv.Perm.IsSwap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g))))
but is expected to have type
  PUnit.{succ (succ u1)}
Case conversion may be inaccurate. Consider using '#align equiv.perm.swap_factors_aux Equiv.Perm.swapFactorsAuxₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a list `l : list α` and a permutation `f : perm α` such that the nonfixed points of `f`
  are in `l`, recursively factors `f` as a product of transpositions. -/
def swapFactorsAux :
    ∀ (l : List α) (f : Perm α),
      (∀ {x}, f x ≠ x → x ∈ l) → { l : List (Perm α) // l.Prod = f ∧ ∀ g ∈ l, IsSwap g }
  | [] => fun f h =>
    ⟨[],
      Equiv.ext fun x => by
        rw [List.prod_nil]
        exact (Classical.not_not.1 (mt h (List.not_mem_nil _))).symm,
      by simp⟩
  | x::l => fun f h =>
    if hfx : x = f x then
      swap_factors_aux l f fun y hy =>
        List.mem_of_ne_of_mem (fun h : y = x => by simpa [h, hfx.symm] using hy) (h hy)
    else
      let m :=
        swap_factors_aux l (swap x (f x) * f) fun y hy =>
          have : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem this.2 (h this.1)
      ⟨swap x (f x)::m.1, by
        rw [List.prod_cons, m.2.1, ← mul_assoc, mul_def (swap x (f x)), swap_swap, ← one_def,
          one_mul],
        fun g hg => ((List.mem_cons _ _ _).1 hg).elim (fun h => ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩
#align equiv.perm.swap_factors_aux Equiv.Perm.swapFactorsAux

/-- `swap_factors` represents a permutation as a product of a list of transpositions.
The representation is non unique and depends on the linear order structure.
For types without linear order `trunc_swap_factors` can be used. -/
def swapFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.Prod = f ∧ ∀ g ∈ l, IsSwap g } :=
  swapFactorsAux ((@univ α _).sort (· ≤ ·)) f fun _ _ => (mem_sort _).2 (mem_univ _)
#align equiv.perm.swap_factors Equiv.Perm.swapFactors

/-- This computably represents the fact that any permutation can be represented as the product of
  a list of transpositions. -/
def truncSwapFactors [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.Prod = f ∧ ∀ g ∈ l, IsSwap g } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swapFactorsAux l f h))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)
#align equiv.perm.trunc_swap_factors Equiv.Perm.truncSwapFactors

/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_elim]
theorem swap_induction_on [Finite α] {P : Perm α → Prop} (f : Perm α) :
    P 1 → (∀ f x y, x ≠ y → P f → P (swap x y * f)) → P f :=
  by
  cases nonempty_fintype α
  cases' (trunc_swap_factors f).out with l hl
  induction' l with g l ih generalizing f
  · simp (config := { contextual := true }) only [hl.left.symm, List.prod_nil, forall_true_iff]
  · intro h1 hmul_swap
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩
    rw [← hl.1, List.prod_cons, hxy.2]
    exact
      hmul_swap _ _ _ hxy.1
        (ih _ ⟨rfl, fun v hv => hl.2 _ (List.mem_cons_of_mem _ hv)⟩ h1 hmul_swap)
#align equiv.perm.swap_induction_on Equiv.Perm.swap_induction_on

theorem closure_isSwap [Finite α] : Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤ :=
  by
  cases nonempty_fintype α
  refine' eq_top_iff.mpr fun x hx => _
  obtain ⟨h1, h2⟩ := Subtype.mem (trunc_swap_factors x).out
  rw [← h1]
  exact Subgroup.list_prod_mem _ fun y hy => Subgroup.subset_closure (h2 y hy)
#align equiv.perm.closure_is_swap Equiv.Perm.closure_isSwap

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
      fun y z hyz hwz => by
      rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y), mul_assoc (swap w y), ←
        mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz, ← mul_assoc,
        swap_mul_swap_mul_swap hwz.symm hyz.symm]
    if hwz : w = z then
      have hwy : w ≠ y := by cc
      ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
    else ⟨swap w y * swap x z, h hyz hwz⟩)
#align equiv.perm.is_conj_swap Equiv.Perm.isConj_swap

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def finPairsLt (n : ℕ) : Finset (Σa : Fin n, Fin n) :=
  (univ : Finset (Fin n)).Sigma fun a => (range a).attachFin fun m hm => (mem_range.1 hm).trans a.2
#align equiv.perm.fin_pairs_lt Equiv.Perm.finPairsLt

theorem mem_finPairsLt {n : ℕ} {a : Σa : Fin n, Fin n} : a ∈ finPairsLt n ↔ a.2 < a.1 := by
  simp only [fin_pairs_lt, Fin.lt_iff_val_lt_val, true_and_iff, mem_attach_fin, mem_range, mem_univ,
    mem_sigma]
#align equiv.perm.mem_fin_pairs_lt Equiv.Perm.mem_finPairsLt

/-- `sign_aux σ` is the sign of a permutation on `fin n`, defined as the parity of the number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂` -/
def signAux {n : ℕ} (a : Perm (Fin n)) : ℤˣ :=
  ∏ x in finPairsLt n, if a x.1 ≤ a x.2 then -1 else 1
#align equiv.perm.sign_aux Equiv.Perm.signAux

@[simp]
theorem signAux_one (n : ℕ) : signAux (1 : Perm (Fin n)) = 1 :=
  by
  unfold sign_aux
  conv =>
    rhs
    rw [← @Finset.prod_const_one ℤˣ _ (fin_pairs_lt n)]
  exact Finset.prod_congr rfl fun a ha => if_neg (mem_fin_pairs_lt.1 ha).not_le
#align equiv.perm.sign_aux_one Equiv.Perm.signAux_one

/-- `sign_bij_aux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasing order. -/
def signBijAux {n : ℕ} (f : Perm (Fin n)) (a : Σa : Fin n, Fin n) : Σa : Fin n, Fin n :=
  if hxa : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩
#align equiv.perm.sign_bij_aux Equiv.Perm.signBijAux

theorem signBijAux_inj {n : ℕ} {f : Perm (Fin n)} :
    ∀ a b : Σa : Fin n, Fin n,
      a ∈ finPairsLt n → b ∈ finPairsLt n → signBijAux f a = signBijAux f b → a = b :=
  fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h => by
  unfold sign_bij_aux at h
  rw [mem_fin_pairs_lt] at *
  have : ¬b₁ < b₂ := hb.le.not_lt
  split_ifs  at h <;>
    simp_all only [(Equiv.injective f).eq_iff, eq_self_iff_true, and_self_iff, heq_iff_eq]
#align equiv.perm.sign_bij_aux_inj Equiv.Perm.signBijAux_inj

theorem signBijAux_surj {n : ℕ} {f : Perm (Fin n)} :
    ∀ a ∈ finPairsLt n, ∃ b ∈ finPairsLt n, a = signBijAux f b := fun ⟨a₁, a₂⟩ ha =>
  if hxa : f⁻¹ a₂ < f⁻¹ a₁ then
    ⟨⟨f⁻¹ a₁, f⁻¹ a₂⟩, mem_finPairsLt.2 hxa,
      by
      dsimp [sign_bij_aux]
      rw [apply_inv_self, apply_inv_self, if_pos (mem_fin_pairs_lt.1 ha)]⟩
  else
    ⟨⟨f⁻¹ a₂, f⁻¹ a₁⟩,
      mem_finPairsLt.2 <|
        (le_of_not_gt hxa).lt_of_ne fun h => by
          simpa [mem_fin_pairs_lt, f⁻¹.Injective h, lt_irrefl] using ha,
      by
      dsimp [sign_bij_aux]
      rw [apply_inv_self, apply_inv_self, if_neg (mem_fin_pairs_lt.1 ha).le.not_lt]⟩
#align equiv.perm.sign_bij_aux_surj Equiv.Perm.signBijAux_surj

theorem signBijAux_mem {n : ℕ} {f : Perm (Fin n)} :
    ∀ a : Σa : Fin n, Fin n, a ∈ finPairsLt n → signBijAux f a ∈ finPairsLt n := fun ⟨a₁, a₂⟩ ha =>
  by
  unfold sign_bij_aux
  split_ifs with h
  · exact mem_fin_pairs_lt.2 h
  ·
    exact
      mem_fin_pairs_lt.2
        ((le_of_not_gt h).lt_of_ne fun h => (mem_fin_pairs_lt.1 ha).Ne (f.injective h.symm))
#align equiv.perm.sign_bij_aux_mem Equiv.Perm.signBijAux_mem

@[simp]
theorem signAux_inv {n : ℕ} (f : Perm (Fin n)) : signAux f⁻¹ = signAux f :=
  prod_bij (fun a ha => signBijAux f⁻¹ a) signBijAux_mem
    (fun ⟨a, b⟩ hab =>
      if h : f⁻¹ b < f⁻¹ a then by
        rw [sign_bij_aux, dif_pos h, if_neg h.not_le, apply_inv_self, apply_inv_self,
          if_neg (mem_fin_pairs_lt.1 hab).not_le]
      else by
        rw [sign_bij_aux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self, apply_inv_self,
          if_pos (mem_fin_pairs_lt.1 hab).le])
    signBijAux_inj signBijAux_surj
#align equiv.perm.sign_aux_inv Equiv.Perm.signAux_inv

theorem signAux_mul {n : ℕ} (f g : Perm (Fin n)) : signAux (f * g) = signAux f * signAux g :=
  by
  rw [← sign_aux_inv g]
  unfold sign_aux
  rw [← prod_mul_distrib]
  refine'
    prod_bij (fun a ha => sign_bij_aux g a) sign_bij_aux_mem _ sign_bij_aux_inj sign_bij_aux_surj
  rintro ⟨a, b⟩ hab
  rw [sign_bij_aux, mul_apply, mul_apply]
  rw [mem_fin_pairs_lt] at hab
  by_cases h : g b < g a
  · rw [dif_pos h]
    simp only [not_le_of_gt hab, mul_one, perm.inv_apply_self, if_false]
  · rw [dif_neg h, inv_apply_self, inv_apply_self, if_pos hab.le]
    by_cases h₁ : f (g b) ≤ f (g a)
    · have : f (g b) ≠ f (g a) :=
        by
        rw [Ne.def, f.injective.eq_iff, g.injective.eq_iff]
        exact ne_of_lt hab
      rw [if_pos h₁, if_neg (h₁.lt_of_ne this).not_le]
      rfl
    · rw [if_neg h₁, if_pos (lt_of_not_ge h₁).le]
      rfl
#align equiv.perm.sign_aux_mul Equiv.Perm.signAux_mul

private theorem sign_aux_swap_zero_one' (n : ℕ) : signAux (swap (0 : Fin (n + 2)) 1) = -1 :=
  show
    _ =
      ∏ x : Σa : Fin (n + 2), Fin (n + 2) in {(⟨1, 0⟩ : Σa : Fin (n + 2), Fin (n + 2))},
        if (Equiv.swap 0 1) x.1 ≤ swap 0 1 x.2 then (-1 : ℤˣ) else 1
    by
    refine'
      Eq.symm
        (prod_subset
          (fun ⟨x₁, x₂⟩ => by
            simp (config := { contextual := true }) [mem_fin_pairs_lt, Fin.one_pos])
          fun a ha₁ ha₂ => _)
    rcases a with ⟨a₁, a₂⟩
    replace ha₁ : a₂ < a₁ := mem_fin_pairs_lt.1 ha₁
    dsimp only
    rcases a₁.zero_le.eq_or_lt with (rfl | H)
    · exact absurd a₂.zero_le ha₁.not_le
    rcases a₂.zero_le.eq_or_lt with (rfl | H')
    · simp only [and_true_iff, eq_self_iff_true, heq_iff_eq, mem_singleton] at ha₂
      have : 1 < a₁ := lt_of_le_of_ne (Nat.succ_le_of_lt ha₁) (Ne.symm ha₂)
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 0 = 1 := by simp
      -- TODO : fix properly
      norm_num [swap_apply_of_ne_of_ne (ne_of_gt H) ha₂, this.not_le, h01]
    · have le : 1 ≤ a₂ := Nat.succ_le_of_lt H'
      have lt : 1 < a₁ := le.trans_lt ha₁
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 1 = 0 := by simp
      -- TODO
      rcases le.eq_or_lt with (rfl | lt')
      · norm_num [swap_apply_of_ne_of_ne H.ne' lt.ne', H.not_le, h01]
      ·
        norm_num [swap_apply_of_ne_of_ne (ne_of_gt H) (ne_of_gt lt),
          swap_apply_of_ne_of_ne (ne_of_gt H') (ne_of_gt lt'), ha₁.not_le]
#align equiv.perm.sign_aux_swap_zero_one' equiv.perm.sign_aux_swap_zero_one'

private theorem sign_aux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
    signAux (swap (⟨0, lt_of_lt_of_le (by decide) hn⟩ : Fin n) ⟨1, lt_of_lt_of_le (by decide) hn⟩) =
      -1 :=
  by
  rcases n with (_ | _ | n)
  · norm_num at hn
  · norm_num at hn
  · exact sign_aux_swap_zero_one' n
#align equiv.perm.sign_aux_swap_zero_one equiv.perm.sign_aux_swap_zero_one

theorem signAux_swap : ∀ {n : ℕ} {x y : Fin n} (hxy : x ≠ y), signAux (swap x y) = -1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => fun x y hxy => by
    have h2n : 2 ≤ n + 2 := by decide
    rw [← isConj_iff_eq, ← sign_aux_swap_zero_one h2n]
    exact (MonoidHom.mk' sign_aux sign_aux_mul).map_isConj (is_conj_swap hxy (by decide))
#align equiv.perm.sign_aux_swap Equiv.Perm.signAux_swap

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- When the list `l : list α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 l f` recursively calculates the sign of `f`. -/
def signAux2 : List α → Perm α → ℤˣ
  | [], f => 1
  | x::l, f => if x = f x then sign_aux2 l f else -sign_aux2 l (swap x (f x) * f)
#align equiv.perm.sign_aux2 Equiv.Perm.signAux2

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem signAux_eq_signAux2 {n : ℕ} :
    ∀ (l : List α) (f : Perm α) (e : α ≃ Fin n) (h : ∀ x, f x ≠ x → x ∈ l),
      signAux ((e.symm.trans f).trans e) = signAux2 l f
  | [], f, e, h =>
    by
    have : f = 1 := Equiv.ext fun y => Classical.not_not.1 (mt (h y) (List.not_mem_nil _))
    rw [this, one_def, Equiv.trans_refl, Equiv.symm_trans_self, ← one_def, sign_aux_one, sign_aux2]
  | x::l, f, e, h => by
    rw [sign_aux2]
    by_cases hfx : x = f x
    · rw [if_pos hfx]
      exact
        sign_aux_eq_sign_aux2 l f _ fun y (hy : f y ≠ y) =>
          List.mem_of_ne_of_mem (fun h : y = x => by simpa [h, hfx.symm] using hy) (h y hy)
    · have hy : ∀ y : α, (swap x (f x) * f) y ≠ y → y ∈ l := fun y hy =>
        have : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy
        List.mem_of_ne_of_mem this.2 (h _ this.1)
      have :
        (e.symm.trans (swap x (f x) * f)).trans e =
          swap (e x) (e (f x)) * (e.symm.trans f).trans e :=
        by ext <;> simp [← Equiv.symm_trans_swap_trans, mul_def]
      have hefx : e x ≠ e (f x) := mt e.injective.eq_iff.1 hfx
      rw [if_neg hfx, ← sign_aux_eq_sign_aux2 _ _ e hy, this, sign_aux_mul, sign_aux_swap hefx]
      simp only [neg_neg, one_mul, neg_mul]
#align equiv.perm.sign_aux_eq_sign_aux2 Equiv.Perm.signAux_eq_signAux2

/-- When the multiset `s : multiset α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 f _` recursively calculates the sign of `f`. -/
def signAux3 [Fintype α] (f : Perm α) {s : Multiset α} : (∀ x, x ∈ s) → ℤˣ :=
  Quotient.hrecOn s (fun l h => signAux2 l f)
    (Trunc.induction_on (Fintype.truncEquivFin α) fun e l₁ l₂ h =>
      Function.hfunext (show (∀ x, x ∈ l₁) = ∀ x, x ∈ l₂ by simp only [h.mem_iff]) fun h₁ h₂ _ => by
        rw [← sign_aux_eq_sign_aux2 _ _ e fun _ _ => h₁ _, ←
          sign_aux_eq_sign_aux2 _ _ e fun _ _ => h₂ _])
#align equiv.perm.sign_aux3 Equiv.Perm.signAux3

theorem signAux3_mul_and_swap [Fintype α] (f g : Perm α) (s : Multiset α) (hs : ∀ x, x ∈ s) :
    signAux3 (f * g) hs = signAux3 f hs * signAux3 g hs ∧
      ∀ x y, x ≠ y → signAux3 (swap x y) hs = -1 :=
  by
  let ⟨l, hl⟩ := Quotient.exists_rep s
  let e := equivFin α
  clear _let_match
  subst hl
  show
    sign_aux2 l (f * g) = sign_aux2 l f * sign_aux2 l g ∧ ∀ x y, x ≠ y → sign_aux2 l (swap x y) = -1
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.symm.trans g).trans e :=
    Equiv.ext fun h => by simp [mul_apply]
  constructor
  ·
    rw [← sign_aux_eq_sign_aux2 _ _ e fun _ _ => hs _, ←
      sign_aux_eq_sign_aux2 _ _ e fun _ _ => hs _, ← sign_aux_eq_sign_aux2 _ _ e fun _ _ => hs _,
      hfg, sign_aux_mul]
  · intro x y hxy
    have hexy : e x ≠ e y := mt e.injective.eq_iff.1 hxy
    rw [← sign_aux_eq_sign_aux2 _ _ e fun _ _ => hs _, symm_trans_swap_trans, sign_aux_swap hexy]
#align equiv.perm.sign_aux3_mul_and_swap Equiv.Perm.signAux3_mul_and_swap

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`perm α` to the group with two elements.-/
def sign [Fintype α] : Perm α →* ℤˣ :=
  MonoidHom.mk' (fun f => signAux3 f mem_univ) fun f g => (signAux3_mul_and_swap f g _ mem_univ).1
#align equiv.perm.sign Equiv.Perm.sign

section SignType.sign

variable [Fintype α]

@[simp]
theorem sign_mul (f g : Perm α) : sign (f * g) = sign f * sign g :=
  MonoidHom.map_mul sign f g
#align equiv.perm.sign_mul Equiv.Perm.sign_mul

@[simp]
theorem sign_trans (f g : Perm α) : sign (f.trans g) = sign g * sign f := by
  rw [← mul_def, sign_mul]
#align equiv.perm.sign_trans Equiv.Perm.sign_trans

@[simp]
theorem sign_one : sign (1 : Perm α) = 1 :=
  MonoidHom.map_one sign
#align equiv.perm.sign_one Equiv.Perm.sign_one

@[simp]
theorem sign_refl : sign (Equiv.refl α) = 1 :=
  MonoidHom.map_one sign
#align equiv.perm.sign_refl Equiv.Perm.sign_refl

@[simp]
theorem sign_inv (f : Perm α) : sign f⁻¹ = sign f := by
  rw [MonoidHom.map_inv SignType.sign f, Int.units_inv_eq_self]
#align equiv.perm.sign_inv Equiv.Perm.sign_inv

@[simp]
theorem sign_symm (e : Perm α) : sign e.symm = sign e :=
  sign_inv e
#align equiv.perm.sign_symm Equiv.Perm.sign_symm

theorem sign_swap {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
  (signAux3_mul_and_swap 1 1 _ mem_univ).2 x y h
#align equiv.perm.sign_swap Equiv.Perm.sign_swap

@[simp]
theorem sign_swap' {x y : α} : (swap x y).sign = if x = y then 1 else -1 :=
  if H : x = y then by simp [H, swap_self] else by simp [sign_swap H, H]
#align equiv.perm.sign_swap' Equiv.Perm.sign_swap'

theorem IsSwap.sign_eq {f : Perm α} (h : f.IsSwap) : sign f = -1 :=
  let ⟨x, y, hxy⟩ := h
  hxy.2.symm ▸ sign_swap hxy.1
#align equiv.perm.is_swap.sign_eq Equiv.Perm.IsSwap.sign_eq

theorem signAux3_symm_trans_trans [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β)
    {s : Multiset α} {t : Multiset β} (hs : ∀ x, x ∈ s) (ht : ∀ x, x ∈ t) :
    signAux3 ((e.symm.trans f).trans e) ht = signAux3 f hs :=
  Quotient.induction_on₂ t s
    (fun l₁ l₂ h₁ h₂ =>
      show signAux2 _ _ = signAux2 _ _ by
        let n := equivFin β
        rw [← sign_aux_eq_sign_aux2 _ _ n fun _ _ => h₁ _, ←
          sign_aux_eq_sign_aux2 _ _ (e.trans n) fun _ _ => h₂ _]
        exact
          congr_arg sign_aux
            (Equiv.ext fun x => by simp only [Equiv.coe_trans, apply_eq_iff_eq, symm_trans_apply]))
    ht hs
#align equiv.perm.sign_aux3_symm_trans_trans Equiv.Perm.signAux3_symm_trans_trans

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
    sign l.Prod = (-1) ^ l.length :=
  by
  have h₁ : l.map sign = List.replicate l.length (-1) :=
    List.eq_replicate.2
      ⟨by simp, fun u hu =>
        let ⟨g, hg⟩ := List.mem_map'.1 hu
        hg.2 ▸ (hl _ hg.1).sign_eq⟩
  rw [← List.prod_replicate, ← h₁, List.prod_hom _ (@SignType.sign α _ _)]
#align equiv.perm.sign_prod_list_swap Equiv.Perm.sign_prod_list_swap

variable (α)

theorem sign_surjective [Nontrivial α] : Function.Surjective (sign : Perm α → ℤˣ) := fun a =>
  (Int.units_eq_one_or a).elim (fun h => ⟨1, by simp [h]⟩) fun h =>
    let ⟨x, y, hxy⟩ := exists_pair_ne α
    ⟨swap x y, by rw [sign_swap hxy, h]⟩
#align equiv.perm.sign_surjective Equiv.Perm.sign_surjective

variable {α}

theorem eq_sign_of_surjective_hom {s : Perm α →* ℤˣ} (hs : Surjective s) : s = sign :=
  have : ∀ {f}, IsSwap f → s f = -1 := fun f ⟨x, y, hxy, hxy'⟩ =>
    hxy'.symm ▸
      by_contradiction fun h =>
        by
        have : ∀ f, IsSwap f → s f = 1 := fun f ⟨a, b, hab, hab'⟩ =>
          by
          rw [← isConj_iff_eq, ← Or.resolve_right (Int.units_eq_one_or _) h, hab']
          exact s.map_is_conj (is_conj_swap hab hxy)
        let ⟨g, hg⟩ := hs (-1)
        let ⟨l, hl⟩ := (truncSwapFactors g).out
        have : ∀ a ∈ l.map s, a = (1 : ℤˣ) := fun a ha =>
          let ⟨g, hg⟩ := List.mem_map'.1 ha
          hg.2 ▸ this _ (hl.2 _ hg.1)
        have : s l.Prod = 1 := by
          rw [← l.prod_hom s, List.eq_replicate_length.2 this, List.prod_replicate, one_pow]
        rw [hl.1, hg] at this
        exact absurd this (by decide)
  MonoidHom.ext fun f => by
    let ⟨l, hl₁, hl₂⟩ := (truncSwapFactors f).out
    have hsl : ∀ a ∈ l.map s, a = (-1 : ℤˣ) := fun a ha =>
      let ⟨g, hg⟩ := List.mem_map'.1 ha
      hg.2 ▸ this (hl₂ _ hg.1)
    rw [← hl₁, ← l.prod_hom s, List.eq_replicate_length.2 hsl, List.length_map, List.prod_replicate,
      sign_prod_list_swap hl₂]
#align equiv.perm.eq_sign_of_surjective_hom Equiv.Perm.eq_sign_of_surjective_hom

theorem sign_subtypePerm (f : Perm α) {p : α → Prop} [DecidablePred p] (h₁ : ∀ x, p x ↔ p (f x))
    (h₂ : ∀ x, f x ≠ x → p x) : sign (subtypePerm f h₁) = sign f :=
  by
  let l := (truncSwapFactors (subtypePerm f h₁)).out
  have hl' : ∀ g' ∈ l.1.map ofSubtype, IsSwap g' := fun g' hg' =>
    let ⟨g, hg⟩ := List.mem_map'.1 hg'
    hg.2 ▸ (l.2.2 _ hg.1).of_subtype_isSwap
  have hl'₂ : (l.1.map ofSubtype).Prod = f := by
    rw [l.1.prod_hom of_subtype, l.2.1, of_subtype_subtype_perm _ h₂]
  conv =>
    congr
    rw [← l.2.1]
    skip
    rw [← hl'₂]
  rw [sign_prod_list_swap l.2.2, sign_prod_list_swap hl', List.length_map]
#align equiv.perm.sign_subtype_perm Equiv.Perm.sign_subtypePerm

theorem sign_eq_sign_of_equiv [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) : sign f = sign g :=
  by
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
                have : f (f x) ≠ f x := mt (fun h => f.Injective h) x.2
                rw [← h _ x.2 this]
                exact mt (hi _ _ this x.2) x.2⟩ :
              { y // g y ≠ y }))
          ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ h => Subtype.eq (hi _ _ _ _ (Subtype.mk.inj h)), fun ⟨y, hy⟩ =>
            let ⟨x, hfx, hx⟩ := hg y hy
            ⟨⟨x, hfx⟩, Subtype.eq hx⟩⟩)
        fun ⟨x, _⟩ => Subtype.eq (h x _ _)
    _ = sign g := sign_subtypePerm _ _ fun _ => id
    
#align equiv.perm.sign_bij Equiv.Perm.sign_bij

/-- If we apply `prod_extend_right a (σ a)` for all `a : α` in turn,
we get `prod_congr_right σ`. -/
theorem prod_prodExtendRight {α : Type _} [DecidableEq α] (σ : α → Perm β) {l : List α}
    (hl : l.Nodup) (mem_l : ∀ a, a ∈ l) :
    (l.map fun a => prodExtendRight a (σ a)).Prod = prodCongrRight σ :=
  by
  ext ⟨a, b⟩ : 1
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices
    a ∈ l ∧ (l.map fun a => prod_extend_right a (σ a)).Prod (a, b) = (a, σ a b) ∨
      a ∉ l ∧ (l.map fun a => prod_extend_right a (σ a)).Prod (a, b) = (a, b)
    by
    obtain ⟨_, prod_eq⟩ := Or.resolve_right this (not_and.mpr fun h _ => h (mem_l a))
    rw [prod_eq, prod_congr_right_apply]
  clear mem_l
  induction' l with a' l ih
  · refine' Or.inr ⟨List.not_mem_nil _, _⟩
    rw [List.map_nil, List.prod_nil, one_apply]
  rw [List.map_cons, List.prod_cons, mul_apply]
  rcases ih (list.nodup_cons.mp hl).2 with (⟨mem_l, prod_eq⟩ | ⟨not_mem_l, prod_eq⟩) <;>
    rw [prod_eq]
  · refine' Or.inl ⟨List.mem_cons_of_mem _ mem_l, _⟩
    rw [prod_extend_right_apply_ne _ fun h : a = a' => (list.nodup_cons.mp hl).1 (h ▸ mem_l)]
  by_cases ha' : a = a'
  · rw [← ha'] at *
    refine' Or.inl ⟨l.mem_cons_self a, _⟩
    rw [prod_extend_right_apply_eq]
  · refine' Or.inr ⟨fun h => not_or_of_not ha' not_mem_l ((List.mem_cons _ _ _).mp h), _⟩
    rw [prod_extend_right_apply_ne _ ha']
#align equiv.perm.prod_prod_extend_right Equiv.Perm.prod_prodExtendRight

section congr

variable [DecidableEq β] [Fintype β]

@[simp]
theorem sign_prodExtendRight (a : α) (σ : Perm β) : (prodExtendRight a σ).sign = σ.sign :=
  sign_bij (fun (ab : α × β) _ => ab.snd)
    (fun ⟨a', b⟩ hab hab' => by simp [eq_of_prod_extend_right_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h => by
      simpa [eq_of_prod_extend_right_ne hab₁, eq_of_prod_extend_right_ne hab₂] using h)
    fun y hy => ⟨(a, y), by simpa, by simp⟩
#align equiv.perm.sign_prod_extend_right Equiv.Perm.sign_prodExtendRight

theorem sign_prodCongrRight (σ : α → Perm β) : sign (prodCongrRight σ) = ∏ k, (σ k).sign :=
  by
  obtain ⟨l, hl, mem_l⟩ := Finite.exists_univ_list α
  have l_to_finset : l.to_finset = Finset.univ :=
    by
    apply eq_top_iff.mpr
    intro b _
    exact list.mem_to_finset.mpr (mem_l b)
  rw [← prod_prod_extend_right σ hl mem_l, sign.map_list_prod, List.map_map, ← l_to_finset,
    List.prod_toFinset _ hl]
  simp_rw [← fun a => sign_prod_extend_right a (σ a)]
#align equiv.perm.sign_prod_congr_right Equiv.Perm.sign_prodCongrRight

theorem sign_prodCongrLeft (σ : α → Perm β) : sign (prodCongrLeft σ) = ∏ k, (σ k).sign :=
  by
  refine' (sign_eq_sign_of_equiv _ _ (prod_comm β α) _).trans (sign_prod_congr_right σ)
  rintro ⟨b, α⟩
  rfl
#align equiv.perm.sign_prod_congr_left Equiv.Perm.sign_prodCongrLeft

@[simp]
theorem sign_permCongr (e : α ≃ β) (p : Perm α) : (e.permCongr p).sign = p.sign :=
  sign_eq_sign_of_equiv _ _ e.symm (by simp)
#align equiv.perm.sign_perm_congr Equiv.Perm.sign_permCongr

@[simp]
theorem sign_sumCongr (σa : Perm α) (σb : Perm β) : (sumCongr σa σb).sign = σa.sign * σb.sign :=
  by
  suffices (sum_congr σa (1 : perm β)).sign = σa.sign ∧ (sum_congr (1 : perm α) σb).sign = σb.sign
    by rw [← this.1, ← this.2, ← sign_mul, sum_congr_mul, one_mul, mul_one]
  constructor
  · apply σa.swap_induction_on _ fun σa' a₁ a₂ ha ih => _
    · simp
    ·
      rw [← one_mul (1 : perm β), ← sum_congr_mul, sign_mul, sign_mul, ih, sum_congr_swap_one,
        sign_swap ha, sign_swap (sum.inl_injective.ne_iff.mpr ha)]
  · apply σb.swap_induction_on _ fun σb' b₁ b₂ hb ih => _
    · simp
    ·
      rw [← one_mul (1 : perm α), ← sum_congr_mul, sign_mul, sign_mul, ih, sum_congr_one_swap,
        sign_swap hb, sign_swap (sum.inr_injective.ne_iff.mpr hb)]
#align equiv.perm.sign_sum_congr Equiv.Perm.sign_sumCongr

@[simp]
theorem sign_subtypeCongr {p : α → Prop} [DecidablePred p] (ep : Perm { a // p a })
    (en : Perm { a // ¬p a }) : (ep.subtypeCongr en).sign = ep.sign * en.sign := by
  simp [subtype_congr]
#align equiv.perm.sign_subtype_congr Equiv.Perm.sign_subtypeCongr

@[simp]
theorem sign_extendDomain (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    Equiv.Perm.sign (e.extendDomain f) = Equiv.Perm.sign e := by
  simp only [Equiv.Perm.extendDomain, sign_subtype_congr, sign_perm_congr, sign_refl, mul_one]
#align equiv.perm.sign_extend_domain Equiv.Perm.sign_extendDomain

@[simp]
theorem sign_ofSubtype {p : α → Prop} [DecidablePred p] (f : Equiv.Perm (Subtype p)) :
    Equiv.Perm.sign f.ofSubtype = Equiv.Perm.sign f :=
  sign_extendDomain f (Equiv.refl (Subtype p))
#align equiv.perm.sign_of_subtype Equiv.Perm.sign_ofSubtype

end congr

end SignType.sign

end Equiv.Perm

