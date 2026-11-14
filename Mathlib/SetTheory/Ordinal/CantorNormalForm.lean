/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Ordinal.Exponential

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.AList

/-!
# Cantor normal form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.cantorNF` in this manner, which is well-behaved for any `b ≥ 2`.

## Implementation notes

We implement `Ordinal.cantorNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

For the Cantor normal form as a finitely supported function, use `Ordinal.cantorCoeff`.

## Todo

- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

public noncomputable section

universe u

open List

namespace Ordinal

/-! ### Cantor normal form as a list -/

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
def cantorRec (b : Ordinal) {motive : Ordinal → Sort*} (zero : motive 0)
    (ne_zero : ∀ o, o ≠ 0 → motive (o % b ^ log b o) → motive o) (o : Ordinal) : motive o :=
  if h : o = 0 then h ▸ zero else ne_zero o h (cantorRec b zero ne_zero (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[deprecated (since := "2026-11-12")]
protected alias CNF.rec := cantorRec

@[simp]
theorem cantorRec_zero {b : Ordinal} {motive : Ordinal → Sort*} (zero : motive 0)
    (ne_zero : ∀ o, o ≠ 0 → motive (o % b ^ log b o) → motive o) :
    cantorRec b zero ne_zero 0 = zero := by
  rw [cantorRec, dite_eq_left rfl]

@[deprecated (since := "2026-11-12")]
alias CNF.rec_zero := cantorRec_zero

theorem cantorRec_of_ne_zero {b : Ordinal} {motive : Ordinal → Sort*} (zero : motive 0)
    (ne_zero : ∀ o, o ≠ 0 → motive (o % b ^ log b o) → motive o) {o : Ordinal} (ho : o ≠ 0) :
    cantorRec b zero ne_zero o = ne_zero o ho (@cantorRec b motive zero ne_zero _) := by
  rw [cantorRec, dite_eq_right]

@[deprecated (since := "2026-11-12")]
alias CNF.rec_pos := cantorRec_of_ne_zero

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`. As an example,
`cantorNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]`.

We have the junk values `cantorNF 0 o = cantorNF 1 o = [(0, o)]` for `o ≠ 0`. -/
@[pp_nodot]
def cantorNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  cantorRec b [] (fun o _ ↦ ((log b o, o / b ^ log b o) :: ·)) o

@[deprecated (since := "2026-11-12")]
alias CNF := cantorNF

@[simp]
theorem cantorNF_zero_right (b : Ordinal) : cantorNF b 0 = [] :=
  cantorRec_zero ..

@[deprecated (since := "2026-11-12")]
alias CNF.zero_right := cantorNF_zero_right

/-- Recursive definition for the Cantor normal form. -/
theorem cantorNF_of_ne_zero (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) :
    cantorNF b o = (log b o, o / b ^ log b o) :: cantorNF b (o % b ^ log b o) :=
  cantorRec_of_ne_zero _ _ ho

@[deprecated (since := "2026-11-12")]
alias CNF.ne_zero := cantorNF_of_ne_zero

theorem cantorNF_opow_mul_add {b e x y : Ordinal} (hx : x ≠ 0) (hxb : x < b) (hy : y < b ^ e) :
    cantorNF b (b ^ e * x + y) = (e, x) :: cantorNF b y := by
  obtain hb | hb := le_or_gt b 1
  · grw [hb, Order.lt_one_iff] at hxb
    contradiction
  · have hb' := hb.ne_zero
    rw [cantorNF_of_ne_zero b (by simp_all), log_opow_mul_add hb hx hy, log_eq_zero hxb, add_zero,
      mul_add_div _ (opow_ne_zero _ hb'), div_eq_zero_of_lt hy, add_zero, mul_add_mod_self,
      mod_eq_of_lt hy]

@[deprecated (since := "2026-11-12")]
alias CNF.opow_mul_add := cantorNF_opow_mul_add

-- TODO: `cantorNF_opow_mul`, `cantorNF_opow_add`, `cantorNF_opow`.

theorem cantorNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) :
    cantorNF b o = [(0, o)] := by
  simpa [log_of_left_le_one hb] using cantorNF_of_ne_zero b ho

@[deprecated (since := "2026-11-12")]
alias CNF.of_le_one := cantorNF_of_le_one

theorem cantorNF_zero_left {o : Ordinal} (ho : o ≠ 0) : cantorNF 0 o = [(0, o)] :=
  cantorNF_of_le_one zero_le_one ho

@[deprecated (since := "2026-11-12")]
alias CNF.zero_left := cantorNF_zero_left

theorem cantorNF_one_left {o : Ordinal} (ho : o ≠ 0) : cantorNF 1 o = [(0, o)] :=
  cantorNF_of_le_one le_rfl ho

@[deprecated (since := "2026-11-12")]
alias CNF.one_left := cantorNF_one_left

theorem cantorNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : cantorNF b o = [(0, o)] := by
  rw [cantorNF_of_ne_zero b ho, log_eq_zero hb, opow_zero, div_one, mod_one, cantorNF_zero_right]

@[deprecated (since := "2026-11-12")]
alias CNF.of_lt := cantorNF_of_lt

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem foldr_cantorNF (b o : Ordinal) :
    (cantorNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  induction o using cantorRec b with
  | zero => simp
  | ne_zero o ho IH => rw [cantorNF_of_ne_zero b ho, foldr_cons, IH, div_add_mod]

@[deprecated (since := "2026-11-12")]
alias CNF.foldr := foldr_cantorNF

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem fst_le_log_of_mem_cantorNF {b o : Ordinal} {x : Ordinal × Ordinal} :
    x ∈ cantorNF b o → x.1 ≤ log b o := by
  induction o using cantorRec b with
  | zero => simp
  | ne_zero o ho IH =>
    rw [cantorNF_of_ne_zero b ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · grw [IH h, mod_opow_log_lt_self b ho]

@[deprecated (since := "2026-11-12")]
alias CNF.fst_le_log := fst_le_log_of_mem_cantorNF

/-- Every coefficient in a Cantor normal form is positive. -/
theorem snd_pos_of_mem_cantorNF {b o : Ordinal} {x : Ordinal × Ordinal} :
    x ∈ cantorNF b o → 0 < x.2 := by
  induction o using cantorRec b with
  | zero => simp
  | ne_zero o ho IH =>
    rw [cantorNF_of_ne_zero b ho, mem_cons]
    rintro (rfl | h)
    · exact div_opow_log_pos b ho
    · exact IH h

@[deprecated (since := "2026-11-12")]
alias CNF.snd_pos := snd_pos_of_mem_cantorNF

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem snd_lt_of_mem_cantorNF {b o : Ordinal} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ cantorNF b o → x.2 < b := by
  induction o using cantorRec b with
  | zero => simp
  | ne_zero o ho IH =>
    rw [cantorNF_of_ne_zero b ho, mem_cons]
    rintro (rfl | h)
    · exact div_opow_log_lt o hb
    · exact IH h

@[deprecated (since := "2026-11-12")]
alias CNF.snd_lt := snd_lt_of_mem_cantorNF

/-- The exponents of the Cantor normal form are strictly decreasing. -/
theorem sortedGT_cantorNF (b o : Ordinal) : ((cantorNF b o).map Prod.fst).SortedGT := by
  simp_rw [sortedGT_iff_pairwise]
  induction o using cantorRec b with
  | zero => simp
  | ne_zero o ho IH =>
    rcases le_or_gt b 1 with hb | hb
    · rw [cantorNF_of_le_one hb ho]
      exact pairwise_singleton _ _
    · obtain hob | hbo := lt_or_ge o b
      · rw [cantorNF_of_lt ho hob]
        exact pairwise_singleton _ _
      · rw [cantorNF_of_ne_zero b ho, map_cons, pairwise_cons]
        refine ⟨fun a H ↦ ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (fst_le_log_of_mem_cantorNF H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

@[deprecated (since := "2026-11-12")]
alias CNF.sortedGT := sortedGT_cantorNF

private theorem nodupKeys (b o : Ordinal) : (map Prod.toSigma (cantorNF b o)).NodupKeys := by
  rw [NodupKeys, List.keys, map_map, Prod.fst_comp_toSigma]
  exact (sortedGT_cantorNF b o).nodup

/-! ### Cantor normal form as a finsupp -/

open AList Finsupp

/-- `cantorCoeff b o` is the finitely supported function returning the coefficient of `b ^ e` in the
Cantor normal form of `o`, for each `e`. -/
@[pp_nodot]
def cantorCoeff (b o : Ordinal) : Ordinal →₀ Ordinal :=
  lookupFinsupp ⟨_, nodupKeys b o⟩

@[deprecated (since := "2026-11-12")]
alias CNF.coeff := cantorCoeff

theorem support_cantorCoeff (b o : Ordinal) :
    (cantorCoeff b o).support = ((cantorNF b o).map Prod.fst).toFinset := by
  rw [cantorCoeff, lookupFinsupp_support, filter_eq_self.2]
  · simp [List.keys]
  · simp_rw [mem_map]
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    apply decide_eq_true
    simpa using (snd_pos_of_mem_cantorNF ha).ne'

@[deprecated (since := "2026-11-12")]
alias CNF.support_coeff := support_cantorCoeff

theorem cantorCoeff_of_mem {b o e c : Ordinal} (h : ⟨e, c⟩ ∈ cantorNF b o) :
    cantorCoeff b o e = c := by
  rw [cantorCoeff, lookupFinsupp_apply, mem_lookup_iff.2, Option.getD_some]
  simpa

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_of_mem_CNF := cantorCoeff_of_mem

theorem cantorCoeff_of_notMem {b o e : Ordinal} (h : e ∉ (cantorNF b o).map Prod.fst) :
    cantorCoeff b o e = 0 := by
  rwa [← notMem_support_iff, support_cantorCoeff, mem_toFinset]

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_of_notMem_CNF := cantorCoeff_of_notMem

theorem cantorCoeff_eq_zero_of_lt {b o e : Ordinal} (h : o < b ^ e) : cantorCoeff b o e = 0 := by
  apply cantorCoeff_of_notMem
  rw [mem_map]
  rintro ⟨⟨e, c⟩, he, rfl⟩
  obtain rfl | he' := eq_or_ne e 0
  · simp_all
  · exact (opow_le_of_le_log he' (fst_le_log_of_mem_cantorNF he)).not_gt h

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_eq_zero_of_lt := cantorCoeff_eq_zero_of_lt

theorem cantorCoeff_zero_apply (b e : Ordinal) : cantorCoeff b 0 e = 0 := by
  apply cantorCoeff_of_notMem
  simp

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_zero_apply := cantorCoeff_zero_apply

@[simp]
theorem cantorCoeff_zero_right (b : Ordinal) : cantorCoeff b 0 = 0 := by
  ext e
  exact cantorCoeff_zero_apply b e

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_zero_right := cantorCoeff_zero_right

theorem cantorCoeff_of_le_one {b : Ordinal} (hb : b ≤ 1) : cantorCoeff b = single 0 := by
  ext o a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply cantorCoeff_of_mem
      rw [cantorNF_of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha]
      apply cantorCoeff_of_notMem
      rw [cantorNF_of_le_one hb ho]
      simpa

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_of_le_one := cantorCoeff_of_le_one

@[simp]
theorem cantorCoeff_zero_left : cantorCoeff 0 = single 0 :=
  cantorCoeff_of_le_one zero_le_one

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_zero_left := cantorCoeff_zero_left

@[simp]
theorem cantorCoeff_one_left : cantorCoeff 1 = single 0 :=
  cantorCoeff_of_le_one le_rfl

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_one_left := cantorCoeff_one_left

theorem cantorCoeff_opow_mul_add {b e x y : Ordinal} (hx : x ≠ 0) (hxb : x < b) (hy : y < b ^ e) :
    cantorCoeff b (b ^ e * x + y) = single e x + cantorCoeff b y := by
  ext e'
  rw [Finsupp.add_apply]
  obtain rfl | he := eq_or_ne e e'
  · rw [single_eq_same, cantorCoeff_eq_zero_of_lt hy, add_zero]
    apply cantorCoeff_of_mem
    rw [cantorNF_opow_mul_add hx hxb hy]
    exact mem_cons_self
  · rw [single_eq_of_ne' he, zero_add]
    by_cases h : e' ∈ (cantorNF b y).map Prod.fst
    · rw [mem_map] at h
      obtain ⟨⟨f, c⟩, hf, rfl⟩ := h
      rw [cantorCoeff_of_mem hf]
      apply cantorCoeff_of_mem
      rw [cantorNF_opow_mul_add hx hxb hy]
      exact mem_cons_of_mem _ hf
    · rw [cantorCoeff_of_notMem h]
      apply cantorCoeff_of_notMem
      rw [mem_map, cantorNF_opow_mul_add hx hxb hy]
      simpa [he] using h

-- TODO: `cantorCoeff_opow_mul`, `cantorCoeff_opow_add`, `cantorCoeff_opow`.

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_opow_mul_add := cantorCoeff_opow_mul_add

/-! ### Evaluate a Cantor normal form -/

/-- `cantorEval f` evaluates a Finsupp `f : Ordinal →₀ Ordinal`, interpreted as a
base `b` expansion on ordinals. -/
def cantorEval (b : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal :=
  (f.support.sort (· ≥ ·)).foldr (fun p r ↦ b ^ p * f p + r) 0

@[deprecated (since := "2026-11-12")]
alias CNF.eval := cantorEval

@[simp]
theorem cantorEval_zero_right (b : Ordinal) : cantorEval b 0 = 0 := by
  simp [cantorEval]

@[deprecated (since := "2026-11-12")]
alias CNF.eval_zero_right := cantorEval_zero_right

private theorem cantorEval_single_add' (b : Ordinal) {e x : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : ∀ e' ∈ f.support, e' < e) :
    cantorEval b (.single e x + f) = b ^ e * x + cantorEval b f := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  have hf : f e = 0 := by
    rw [← notMem_support_iff]
    exact fun he ↦ (h e he).false
  rw [cantorEval, support_single_add (by simpa) hx, Finset.sort_cons]
  · simp only [Finsupp.add_apply, foldr_cons, single_eq_same, hf, add_zero, add_right_inj]
    apply foldr_ext
    intro e' he' _
    congr
    rw [single_eq_of_ne, zero_add]
    aesop
  · exact fun e' he' ↦ (h e' he').le

@[simp]
theorem cantorEval_single (b e x : Ordinal) : cantorEval b (.single e x) = b ^ e * x := by
  simpa using cantorEval_single_add' b (f := 0)

@[deprecated (since := "2026-11-12")]
alias CNF.eval_single := cantorEval_single

theorem cantorEval_single_add (b : Ordinal) {e x : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : ∀ e' ∈ f.support, e' ≤ e) :
    cantorEval b (.single e x + f) = b ^ e * x + cantorEval b f := by
  cases f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e' y f hf hy =>
    obtain rfl | he' := (h e' (by simp [hy])).eq_or_lt
    · simp only [← add_assoc, ← single_add, cantorEval_single_add' _ hf, mul_add]
    · rw [cantorEval_single_add']
      refine fun a ha ↦ (h a ha).lt_of_ne ?_
      rintro rfl
      apply (hf a _).not_gt he'
      simpa [he'.ne'] using ha

@[deprecated (since := "2026-11-12")]
alias CNF.eval_single_add := cantorEval_single_add
@[deprecated (since := "2026-11-12")]
alias CNF.eval_single_add' := cantorEval_single_add

theorem cantorEval_add (b : Ordinal) {f₁ f₂ : Ordinal →₀ Ordinal}
    (h : ∀ e₁ ∈ f₁.support, ∀ e₂ ∈ f₂.support, e₂ ≤ e₁) :
    cantorEval b (f₁ + f₂) = cantorEval b f₁ + cantorEval b f₂ := by
  induction f₁ using Finsupp.induction_on_max with
  | zero => simp
  | single_add e₁ x f₁ hf₁ hx IH =>
    rw [add_assoc, cantorEval_single_add, cantorEval_single_add' _ hf₁, IH, add_assoc]
    · simp_all
    · intro e₂ he₂
      obtain he₂ | he₂ := Finset.mem_union.1 <| support_add he₂
      · exact (hf₁ _ he₂).le
      · apply h _ _ _ he₂
        simp_all

@[deprecated (since := "2026-11-12")]
alias CNF.eval_add := cantorEval_add

theorem cantorEval_lt {b e : Ordinal} {f : Ordinal →₀ Ordinal}
    (hb : ∀ e', f e' < b) (he : ∀ e' ∈ f.support, e' < e) : cantorEval b f < b ^ e := by
  induction f using Finsupp.induction_on_max generalizing e with
  | zero =>
    rw [cantorEval_zero_right]
    exact opow_pos _ (hb 0)
  | single_add e' x f hf hx IH =>
    have he' : e' ∉ f.support := fun h ↦ (hf _ h).false
    rw [cantorEval_single_add' _ hf]
    apply opow_mul_add_lt_opow _ (IH _ hf)
    · apply he e' _
      simp [hx]
    · apply (hb e').trans_eq'
      rw [Finsupp.add_apply, single_eq_same, notMem_support_iff.1, add_zero]
      exact fun h ↦ (hf _ h).false
    · intro a
      by_cases ha : a ∈ f.support
      · apply (hb a).trans_eq'
        rw [Finsupp.add_apply, single_eq_of_ne, zero_add]
        rintro rfl
        contradiction
      · rw [notMem_support_iff.1 ha]
        exact (hb 0).pos

@[deprecated (since := "2026-11-12")]
alias CNF.eval_lt := cantorEval_lt

@[simp]
theorem cantorEval_cantorCoeff (b o : Ordinal) : cantorEval b (cantorCoeff b o) = o := by
  conv_rhs => rw [← foldr_cantorNF b o]
  rw [cantorEval, support_cantorCoeff, (sortedGT_cantorNF b o).sort_toFinset, foldr_map]
  apply foldr_ext
  intro a ha x
  rw [cantorCoeff_of_mem ha]

@[deprecated (since := "2026-11-12")]
alias CNF.eval_coeff := cantorEval_cantorCoeff

theorem cantorCoeff_cantorEval {b : Ordinal} {f : Ordinal →₀ Ordinal} (hf : ∀ e, f e < b) :
    cantorCoeff b (cantorEval b f) = f := by
  induction f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e x f hf' hx IH =>
    have IH' (e') : f e' < b := by
      by_cases he' : e' ∈ f.support
      · apply (hf e').trans_eq'
        rw [Finsupp.add_apply, single_eq_of_ne, zero_add]
        exact (hf' _ he').ne
      · rw [notMem_support_iff.1 he']
        exact (hf 0).pos
    rw [cantorEval_single_add' _ hf', cantorCoeff_opow_mul_add hx, IH IH']
    · apply (hf e).trans_eq'
      rw [Finsupp.add_apply, single_eq_same, notMem_support_iff.1, add_zero]
      exact fun h ↦ (hf' _ h).false
    · exact cantorEval_lt IH' hf'

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_eval := cantorCoeff_cantorEval

theorem cantorCoeff_injective (b : Ordinal) : Function.Injective (cantorCoeff b) :=
  Function.LeftInverse.injective (cantorEval_cantorCoeff b)

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_injective := cantorCoeff_injective

@[simp]
theorem cantorCoeff_inj {b x y : Ordinal} : cantorCoeff b x = cantorCoeff b y ↔ x = y :=
  (cantorCoeff_injective b).eq_iff

@[deprecated (since := "2026-11-12")]
alias CNF.coeff_inj := cantorCoeff_inj

end Ordinal
