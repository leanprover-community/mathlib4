/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Family

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.AList

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

## Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

## Todo

- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

public noncomputable section

universe u

open List

namespace Ordinal.CNF

/-! ### Cantor normal form as a list -/

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
protected def rec (b : Ordinal) {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNF.rec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[deprecated (since := "2025-08-18")]
noncomputable alias _root_.Ordinal.CNFRec := CNF.rec

@[simp]
theorem rec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : CNF.rec b H0 H 0 = H0 := by
  rw [CNF.rec, dif_pos rfl]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNFRec_zero := rec_zero

theorem rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    CNF.rec b H0 H o = H o ho (@CNF.rec b C H0 H _) := by
  rw [CNF.rec, dif_neg]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNFRec_pos := rec_pos

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def _root_.Ordinal.CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNF.rec b [] (fun o _ IH ↦ (log b o, o / b ^ log b o)::IH) o

@[simp]
theorem zero_right (b : Ordinal) : CNF b 0 = [] :=
  rec_zero b _ _

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_zero := zero_right

/-- Recursive definition for the Cantor normal form. -/
protected theorem ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
  rec_pos b ho _ _

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_ne_zero := CNF.ne_zero

protected theorem opow_mul_add {b e x y : Ordinal}
    (hb : 1 < b) (hx : x ≠ 0) (hxb : x < b) (hy : y < b ^ e) :
    CNF b (b ^ e * x + y) = (e, x) :: CNF b y := by
  have hb' := hb.ne_bot
  rw [CNF.ne_zero]
  · rw [log_opow_mul_add hb hx hy, log_eq_zero hxb, add_zero,
      mul_add_div _ (opow_ne_zero _ hb'), Ordinal.div_eq_zero_of_lt hy, add_zero,
      mul_add_mod_self, mod_eq_of_lt hy]
  · simp_all

protected theorem zero_left {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [(0, o)] := by
  simp [CNF.ne_zero ho]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.zero_CNF := CNF.zero_left

protected theorem one_left {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [(0, o)] := by
  simp [CNF.ne_zero ho]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.one_CNF := CNF.one_left

protected theorem of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [(0, o)] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  exacts [CNF.zero_left ho, CNF.one_left ho]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_of_le_one := CNF.of_le_one

protected theorem of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [(0, o)] := by
  rw [CNF.ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, zero_right]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_of_lt := CNF.of_lt

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
protected theorem foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNF.rec b ?_ ?_ o
  · rw [zero_right, foldr_nil]
  · intro o ho IH
    rw [CNF.ne_zero ho, foldr_cons, IH, div_add_mod]

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_foldr := CNF.foldr

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → x.1 ≤ log b o := by
  refine CNF.rec b ?_ (fun o ho H ↦ ?_) o
  · simp
  · rw [CNF.ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_fst_le_log := fst_le_log

/-- Every coefficient in a Cantor normal form is positive. -/
theorem snd_pos {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 := by
  refine CNF.rec b (by simp) (fun o ho IH ↦ ?_) o
  rw [CNF.ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

@[deprecated (since := "2026-01-11")]
alias lt_snd := snd_pos

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_lt_snd := snd_pos

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine CNF.rec b ?_ (fun o ho IH ↦ ?_) o
  · simp
  · rw [CNF.ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_snd_lt := snd_lt

/-- The exponents of the Cantor normal form are decreasing. -/
protected theorem sortedGT (b o : Ordinal) : ((CNF b o).map Prod.fst).SortedGT := by
  simp_rw [sortedGT_iff_pairwise]
  refine CNF.rec b ?_ (fun o ho IH ↦ ?_) o
  · rw [zero_right]
    exact .nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF.of_le_one hb ho]
      exact pairwise_singleton _ _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF.of_lt ho hob]
        exact pairwise_singleton _ _
      · rw [CNF.ne_zero ho, map_cons, pairwise_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

@[deprecated (since := "2026-01-11")]
alias sorted := CNF.sortedGT

@[deprecated (since := "2025-08-18")]
alias _root_.Ordinal.CNF_sorted := CNF.sortedGT

private theorem nodupKeys (b o : Ordinal) : (map Prod.toSigma (CNF b o)).NodupKeys := by
  rw [NodupKeys, List.keys, map_map, Prod.fst_comp_toSigma]
  exact (CNF.sortedGT ..).nodup

/-! ### Cantor normal form as a finsupp -/

open AList Finsupp

/-- `CNF.coeff b o` is the finitely supported function returning the coefficient of `b ^ e` in the
Cantor Normal Form (`CNF`) of `o`, for each `e`. -/
@[pp_nodot]
def coeff (b o : Ordinal) : Ordinal →₀ Ordinal :=
  lookupFinsupp ⟨_, nodupKeys b o⟩

theorem support_coeff (b o : Ordinal) :
    (coeff b o).support = ((CNF b o).map Prod.fst).toFinset := by
  rw [coeff, lookupFinsupp_support, filter_eq_self.2]
  · simp [List.keys]
  · simp_rw [mem_map]
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    simpa using (snd_pos ha).ne'

theorem coeff_of_mem_CNF {b o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    coeff b o e = c := by
  rw [coeff, lookupFinsupp_apply, mem_lookup_iff.2, Option.getD_some]
  simpa

theorem coeff_of_notMem_CNF {b o e : Ordinal} (h : e ∉ (CNF b o).map Prod.fst) :
    coeff b o e = 0 := by
  rwa [← notMem_support_iff, support_coeff, mem_toFinset]

@[deprecated (since := "2026-01-11")]
alias coeff_of_not_mem_CNF := coeff_of_notMem_CNF

theorem coeff_eq_zero_of_lt {b o e : Ordinal} (h : o < b ^ e) : coeff b o e = 0 := by
  apply coeff_of_notMem_CNF
  intro he
  rw [mem_map] at he
  obtain ⟨⟨e, c⟩, he, rfl⟩ := he
  obtain rfl | he' := eq_or_ne e 0
  · simp_all
  · exact (opow_le_of_le_log he' (fst_le_log he)).not_gt h

theorem coeff_zero_apply (b e : Ordinal) : coeff b 0 e = 0 := by
  apply coeff_of_notMem_CNF
  simp

@[simp]
theorem coeff_zero_right (b : Ordinal) : coeff b 0 = 0 := by
  ext e
  exact coeff_zero_apply b e

theorem coeff_of_le_one {b : Ordinal} (hb : b ≤ 1) (o : Ordinal) : coeff b o = single 0 o := by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply coeff_of_mem_CNF
      rw [CNF.of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha]
      apply coeff_of_notMem_CNF
      rw [CNF.of_le_one hb ho]
      simpa using ha

@[simp]
theorem coeff_zero_left (o : Ordinal) : coeff 0 o = single 0 o :=
  coeff_of_le_one zero_le_one o

@[simp]
theorem coeff_one_left (o : Ordinal) : coeff 1 o = single 0 o :=
  coeff_of_le_one le_rfl o

theorem coeff_opow_mul_add {b e x y : Ordinal}
    (hb : 1 < b) (hx : x ≠ 0) (hxb : x < b) (hy : y < b ^ e) :
    coeff b (b ^ e * x + y) = single e x + coeff b y := by
  ext e'
  rw [add_apply]
  obtain rfl | he := eq_or_ne e e'
  · rw [single_eq_same, coeff_eq_zero_of_lt hy, add_zero]
    apply coeff_of_mem_CNF
    rw [CNF.opow_mul_add hb hx hxb hy]
    exact mem_cons_self
  · rw [single_eq_of_ne' he, zero_add]
    by_cases h : e' ∈ (CNF b y).map Prod.fst
    · rw [mem_map] at h
      obtain ⟨⟨f, c⟩, hf, rfl⟩ := h
      rw [coeff_of_mem_CNF hf]
      apply coeff_of_mem_CNF
      rw [CNF.opow_mul_add hb hx hxb hy]
      exact mem_cons_of_mem _ hf
    · rw [coeff_of_notMem_CNF h, coeff_of_notMem_CNF]
      rw [mem_map] at h ⊢
      rw [CNF.opow_mul_add hb hx hxb hy]
      simp_all

/-! ### Evaluate a Cantor normal form -/

/-- `CNF.eval f` evaluates a Finsupp `f : Ordinal →₀ Ordinal`, interpreted as a
base `b` expansion on ordinals. -/
def eval (b : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal :=
  (f.support.sort (· ≥ ·)).foldr (fun p r ↦ b ^ p * f p + r) 0

@[simp]
theorem eval_zero_right (b : Ordinal) : eval b 0 = 0 := by
  simp [eval]

/-- For a slightly stronger version, see `eval_single_add`. -/
theorem eval_single_add' (b : Ordinal) {e x : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : ∀ e' ∈ f.support, e' < e) : eval b (.single e x + f) = b ^ e * x + eval b f := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  have hf : f e = 0 := by
    rw [← notMem_support_iff]
    exact fun he ↦ (h e he).false
  rw [eval, support_single_add (by simpa) hx, Finset.sort_cons]
  · simp only [add_apply, foldr_cons, single_eq_same, hf, add_zero, add_right_inj]
    apply foldr_ext
    intro e' he' _
    congr
    rw [single_eq_of_ne, zero_add]
    aesop
  · exact fun e' he' ↦ (h e' he').le

@[simp]
theorem eval_single (b e x : Ordinal) : eval b (.single e x) = b ^ e * x := by
  simpa using eval_single_add' b (f := 0)

theorem eval_single_add (b : Ordinal) {e x : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : ∀ e' ∈ f.support, e' ≤ e) : eval b (.single e x + f) = b ^ e * x + eval b f := by
  cases f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e' y f hf hy =>
    obtain rfl | he' := (h e' (by simp [hy])).eq_or_lt
    · simp only [← add_assoc, ← single_add, eval_single_add' _ hf, mul_add]
    · rw [eval_single_add']
      refine fun a ha ↦ (h a ha).lt_of_ne ?_
      rintro rfl
      apply (hf a _).not_gt he'
      simpa [he'.ne'] using ha

theorem eval_add (b : Ordinal) {f₁ f₂ : Ordinal →₀ Ordinal}
    (h : ∀ e₁ ∈ f₁.support, ∀ e₂ ∈ f₂.support, e₂ ≤ e₁) :
    eval b (f₁ + f₂) = eval b f₁ + eval b f₂ := by
  induction f₁ using Finsupp.induction_on_max with
  | zero => simp
  | single_add e₁ x f₁ hf₁ hx IH =>
    rw [add_assoc, eval_single_add, eval_single_add' _ hf₁, IH, add_assoc]
    · simp_all
    · intro e₂ he₂
      obtain he₂ | he₂ := Finset.mem_union.1 <| support_add he₂
      · exact (hf₁ _ he₂).le
      · apply h _ _ _ he₂
        simp_all

theorem eval_lt {b e : Ordinal} {f : Ordinal →₀ Ordinal}
    (hb : ∀ e', f e' < b) (he : ∀ e' ∈ f.support, e' < e) : eval b f < b ^ e := by
  induction f using Finsupp.induction_on_max generalizing e with
  | zero =>
    rw [eval_zero_right]
    exact opow_pos _ (hb 0)
  | single_add e' x f hf hx IH =>
    have he' : e' ∉ f.support := fun h ↦ (hf _ h).false
    rw [eval_single_add' _ hf]
    apply opow_mul_add_lt_opow _ (IH _ hf)
    · convert he e' _
      simp [hx]
    · convert hb e'
      rw [add_apply, single_eq_same, notMem_support_iff.1, add_zero]
      exact fun h ↦ (hf _ h).false
    · intro a
      by_cases ha : a ∈ f.support
      · convert hb a using 1
        rw [add_apply, single_eq_of_ne, zero_add]
        rintro rfl
        contradiction
      · rw [notMem_support_iff.1 ha]
        exact (hb 0).pos

@[simp]
theorem eval_coeff (b o : Ordinal) : eval b (coeff b o) = o := by
  conv_rhs => rw [← CNF.foldr b o]
  rw [eval, support_coeff, (toFinset_sort _ _).2, foldr_map]
  · apply foldr_ext
    intro a ha x
    rw [coeff_of_mem_CNF ha]
  · exact (CNF.sortedGT b o).sortedGE.pairwise
  · exact (CNF.sortedGT b o).nodup

theorem coeff_eval {b : Ordinal} (hb : 1 < b) {f : Ordinal →₀ Ordinal} (hf : ∀ e, f e < b) :
    coeff b (eval b f) = f := by
  induction f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e x f hf' hx IH =>
    have IH' (e') : f e' < b := by
      by_cases he' : e' ∈ f.support
      · convert hf e' using 1
        rw [add_apply, single_eq_of_ne, zero_add]
        exact (hf' _ he').ne
      · rw [notMem_support_iff.1 he']
        exact hb.pos
    rw [eval_single_add' _ hf', coeff_opow_mul_add hb hx, IH IH']
    · convert hf e
      rw [add_apply, single_eq_same, notMem_support_iff.1, add_zero]
      exact fun h ↦ (hf' _ h).false
    · exact eval_lt IH' hf'

theorem coeff_injective (b : Ordinal) : Function.Injective (coeff b) :=
  Function.LeftInverse.injective fun _ ↦ eval_coeff ..

@[simp]
theorem coeff_inj {b x y : Ordinal} : coeff b x = coeff b y ↔ x = y :=
  (coeff_injective b).eq_iff

end Ordinal.CNF
