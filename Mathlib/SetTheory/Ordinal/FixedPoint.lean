/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
import Mathlib.Logic.Small.List
import Mathlib.SetTheory.Ordinal.Enum
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `not_bddAbove_fp_family`, `not_bddAbove_fp`: the (common) fixed points of a (family of) normal
  function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega0_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega0_mul`: a characterization of the derivative of multiplication.
-/


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section

variable {ι : Type*} {f : ι → Ordinal.{u} → Ordinal.{u}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reachable by applying
finitely many functions in the family to `a`.

`Ordinal.nfpFamily_fp` shows this is a fixed point, `Ordinal.le_nfpFamily` shows it's at
least `a`, and `Ordinal.nfpFamily_le_fp` shows this is the least ordinal with these properties. -/
def nfpFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) : Ordinal :=
  ⨆ i, List.foldr f a i

theorem foldr_le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a l) :
    List.foldr f a l ≤ nfpFamily f a :=
  Ordinal.le_iSup _ _

theorem le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a) : a ≤ nfpFamily f a :=
  foldr_le_nfpFamily f a []

theorem lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  Ordinal.lt_iSup_iff

@[deprecated (since := "2025-02-16")]
alias lt_nfpFamily := lt_nfpFamily_iff

theorem nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  Ordinal.iSup_le_iff

theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  Ordinal.iSup_le

theorem nfpFamily_monotone [Small.{u} ι] (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) :=
  fun _ _ h ↦ nfpFamily_le <| fun l ↦ (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)

theorem apply_lt_nfpFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b}
    (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩

theorem apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a := by
  refine ⟨fun h ↦ ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
  exact lt_nfpFamily_iff.2 <| ⟨l, (H _).le_apply.trans_lt hl⟩

theorem nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfpFamily_iff H

theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily f a ≤ b := by
  apply Ordinal.iSup_le fun l ↦ ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)

theorem nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily f a) = nfpFamily f a := by
  rw [nfpFamily, H.map_iSup]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.le_apply.trans (Ordinal.le_iSup _ _)

theorem apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h

theorem nfpFamily_eq_self [Small.{u} ι] {a} (h : ∀ i, f i a = a) : nfpFamily f a = a := by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

theorem range_nfpFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    Set.range (nfpFamily f) = ⋂ i, Function.fixedPoints (f i) := by
  ext x
  rw [Set.mem_iInter]
  refine ⟨?_, fun h ↦ ⟨x, nfpFamily_eq_self h⟩⟩
  rintro ⟨a, rfl⟩ i
  exact nfpFamily_fp (H i) a

theorem mem_range_nfpFamily_iff [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {o} :
    o ∈ Set.range (nfpFamily f) ↔ ∀ i, f i o = o := by
  rw [range_nfpFamily H]
  simp [IsFixedPt]

-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem not_bddAbove_fp_family [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    ¬ BddAbove (⋂ i, Function.fixedPoints (f i)) := by
  rw [not_bddAbove_iff]
  refine fun a ↦ ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivFamily (f : ι → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  enumOrd (⋂ i, Function.fixedPoints (f i))

theorem derivFamily_eq_enumOrd : derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) :=
  rfl

theorem isNormal_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    IsNormal (derivFamily f) := by
  apply isNormal_enumOrd (fun t ht ht₀ ht' ↦ ?_) (not_bddAbove_fp_family H)
  aesop (add simp [IsNormal.map_sSup_of_bddAbove, Set.subset_def, IsFixedPt])

theorem derivFamily_strictMono [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    StrictMono (derivFamily f) :=
  (isNormal_derivFamily H).strictMono

theorem derivFamily_fp [Small.{u} ι] {i} (H : ∀ i, IsNormal (f i)) (o : Ordinal) :
    f i (derivFamily f o) = derivFamily f o :=
  (Set.mem_iInter.1 <| enumOrd_mem (not_bddAbove_fp_family H) o) i

theorem range_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    Set.range (derivFamily f) = ⋂ i, Function.fixedPoints (f i) :=
  range_enumOrd (not_bddAbove_fp_family H)

theorem mem_range_derivFamily_iff [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {o} :
    o ∈ Set.range (derivFamily f) ↔ ∀ i, f i o = o := by
  rw [range_derivFamily H]
  simp [IsFixedPt]

@[deprecated mem_range_derivFamily_iff (since := "2025-07-01")]
theorem le_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a := by
  simpa [(H _).le_iff_eq] using (mem_range_derivFamily_iff H).symm

@[deprecated mem_range_derivFamily_iff (since := "2025-07-01")]
theorem fp_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a := by
  simpa using (mem_range_derivFamily_iff H).symm

theorem derivFamily_zero [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    derivFamily f 0 = nfpFamily f 0 := by
  apply (nfpFamily_le_fp _ (Ordinal.zero_le _) _).antisymm'
  · rw [derivFamily, enumOrd_zero]
    apply csInf_le'
    simpa using fun i ↦ nfpFamily_fp (H i) _
  · exact fun i ↦ (H i).monotone
  · exact fun _ ↦ (derivFamily_fp H _).le

theorem derivFamily_succ [Small.{u} ι] (H : ∀ i, IsNormal (f i)) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) := by
  apply (nfpFamily_le_fp _ _ _).antisymm'
  · apply enumOrd_succ_le (not_bddAbove_fp_family H)
    · simpa using fun i ↦ nfpFamily_fp (H i) _
    · exact (lt_succ _).trans_le (le_nfpFamily f _)
  · exact fun i ↦ (H i).monotone
  · simpa using derivFamily_strictMono H (lt_succ o)
  · exact fun i ↦ (derivFamily_fp H _).le

@[deprecated isNormal_derivFamily (since := "2025-07-01")]
theorem derivFamily_limit [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {o} :
    IsLimit o → derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b :=
  (isNormal_derivFamily H).apply_of_isLimit

end

/-! ### Fixed points of a single function -/

section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.

This is defined as `nfpFamily` applied to a family consisting only of `f`. -/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f

theorem nfp_eq_nfpFamily (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl

theorem iSup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    ⨆ n : ℕ, f^[n] a = nfp f a := by
  refine (Equiv.listUniqueEquiv _).symm.iSup_congr fun n ↦ ?_
  induction n with
  | zero => rfl
  | succ n IH => rw [Function.iterate_succ_apply', ← IH]; rfl

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.le_iSup (fun n ↦ f^[n] a) n

theorem le_nfp (f a) : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem lt_nfp_iff {a b} : a < nfp f b ↔ ∃ n, a < f^[n] b := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.lt_iSup_iff

theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, f^[n] a ≤ b := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_le_iff

theorem nfp_le {a b} : (∀ n, f^[n] a ≤ b) → nfp f a ≤ b :=
  nfp_le_iff.2

@[simp]
theorem nfp_id : nfp id = id := by
  ext
  simp_rw [← iSup_iterate_eq_nfp, iterate_id, ciSup_const]

theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfpFamily_monotone fun _ => hf

theorem iterate_lt_nfp (hf : StrictMono f) {a} (h : a < f a) (n : ℕ) : f^[n] a < nfp f a := by
  apply (hf.iterate n h).trans_le
  rw [← iterate_succ_apply]
  exact iterate_le_nfp ..

theorem IsNormal.apply_lt_nfp (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by
  unfold nfp
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

theorem IsNormal.nfp_le_apply (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp

theorem nfp_le_fp (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  nfpFamily_le_fp (fun _ ↦ H) ab fun _ => h

theorem IsNormal.nfp_fp (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a :=
  nfpFamily_fp (i := ⟨⟩) H

theorem IsNormal.apply_le_nfp (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨H.le_apply.trans, fun h => by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {a} (h : f a = a) : nfp f a = a :=
  nfpFamily_eq_self fun _ => h

theorem range_nfp (H : IsNormal f) : Set.range (nfp f) = Function.fixedPoints f := by
  simpa [Set.iInter_const] using range_nfpFamily fun _ : Unit ↦ H

theorem mem_range_nfp_iff (H : IsNormal f) {o} : o ∈ Set.range (nfp f) ↔ f o = o := by
  simpa using mem_range_nfpFamily_iff fun _ : Unit ↦ H

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem not_bddAbove_fp (H : IsNormal f) : ¬ BddAbove (Function.fixedPoints f) := by
  simpa [Set.iInter_const] using not_bddAbove_fp_family fun _ : Unit ↦ H

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `Ordinal.derivFamily` applied to a trivial family consisting only of `f`. -/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f

@[deprecated "use `rw [deriv]` instead" (since := "2025-07-01")]
theorem deriv_eq_derivFamily (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl

/-- `Ordinal.deriv` enumerates the fixed points of a normal function. -/
theorem deriv_eq_enumOrd : deriv f = enumOrd (Function.fixedPoints f) := by
  rw [deriv, derivFamily, Set.iInter_const]

theorem isNormal_deriv (H : IsNormal f) : IsNormal (deriv f) :=
  isNormal_derivFamily fun _ ↦ H

protected alias IsNormal.deriv := isNormal_deriv

theorem deriv_strictMono (H : IsNormal f) : StrictMono (deriv f) :=
  derivFamily_strictMono fun _ ↦ H

protected alias IsNormal.deriv_strictMono := deriv_strictMono

@[deprecated "on normal functions, `nfp f = id` implies `f = id`" (since := "2025-07-01")]
theorem deriv_id_of_nfp_id (h : nfp f = id) (H : IsNormal f) : deriv f = id := by
  apply_fun Set.range at h
  rw [Set.range_id, range_nfp H] at h
  rw [deriv_eq_enumOrd, h, enumOrd_univ]

theorem IsNormal.deriv_fp (H : IsNormal f) : ∀ o : Ordinal, f (deriv f o) = deriv f o :=
  derivFamily_fp.{u} (i := ()) fun _ ↦ H

theorem IsNormal.range_deriv (H : IsNormal f) : Set.range (deriv f) = Function.fixedPoints f := by
  simpa [Set.iInter_const] using range_derivFamily fun _ : Unit ↦ H

theorem mem_range_deriv_iff (H : IsNormal f) {o} : o ∈ Set.range (deriv f) ↔ f o = o := by
  simpa using mem_range_derivFamily_iff fun _ : Unit ↦ H

set_option linter.deprecated false in
@[deprecated mem_range_deriv_iff (since := "2025-07-01")]
theorem IsNormal.fp_iff_deriv {f} (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by
  simpa using fp_iff_derivFamily fun _ : Unit ↦ H

@[deprecated (since := "2025-07-01")]
alias deriv_eq_id_of_nfp_eq_id := deriv_id_of_nfp_id

theorem deriv_zero_right (H : IsNormal f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero fun _ ↦ H

theorem deriv_succ (H : IsNormal f) : ∀ o, deriv f (succ o) = nfp f (succ (deriv f o)) :=
  derivFamily_succ fun _ ↦ H

set_option linter.deprecated false in
@[deprecated IsNormal.deriv (since := "2025-07-01")]
theorem deriv_limit (H : IsNormal f) {o} :
    IsLimit o → deriv f o = ⨆ b : Set.Iio o, deriv f b :=
  derivFamily_limit fun _ ↦ H

theorem nfp_zero_left (a) : nfp 0 a = a := by
  rw [← iSup_iterate_eq_nfp]
  apply (Ordinal.iSup_le ?_).antisymm (Ordinal.le_iSup _ 0)
  rintro (_ | _)
  · rfl
  · rw [Function.iterate_succ']
    simp

@[simp]
theorem nfp_zero : nfp 0 = id := by
  ext
  exact nfp_zero_left _

end

/-! ### Fixed points of addition -/

@[simp]
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * ω := by
  simp_rw [← iSup_iterate_eq_nfp, ← iSup_mul_nat]
  congr; funext n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, iterate_zero_apply]
  | succ n hn => rw [iterate_succ_apply', Nat.add_comm, Nat.cast_add, Nat.cast_one, mul_one_add, hn]

theorem nfp_add_eq_mul_omega0 {a b} (hba : b ≤ a * ω) : nfp (a + ·) b = a * ω := by
  apply le_antisymm (nfp_le_fp (isNormal_add_right a).monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (isNormal_add_right a).monotone (Ordinal.zero_le b)
  · rw [← mul_one_add, one_add_omega0]

theorem add_eq_right_iff_mul_omega0_le {a b : Ordinal} : a + b = b ↔ a * ω ≤ b := by
  have H := isNormal_add_right a
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero_right H]
    obtain ⟨c, rfl⟩ := (mem_range_deriv_iff H).2 h
    exact H.deriv.monotone (Ordinal.zero_le _)
  · rw [← Ordinal.add_sub_cancel_of_le h, ← add_assoc, ← mul_one_add, one_add_omega0]

theorem add_le_right_iff_mul_omega0_le {a b : Ordinal} : a + b ≤ b ↔ a * ω ≤ b := by
  rw [← add_eq_right_iff_mul_omega0_le]
  exact (isNormal_add_right a).le_iff_eq

theorem deriv_add_eq_mul_omega0_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * ω + b := by
  revert b
  have H := isNormal_add_right a
  rw [← funext_iff, H.deriv.eq_iff_zero_and_succ (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [deriv_zero_right H, add_zero]
    exact nfp_add_zero a
  · rw [deriv_succ H, h, add_succ]
    exact nfp_eq_self (add_eq_right_iff_mul_omega0_le.2 ((le_add_right _ _).trans (le_succ _)))

/-! ### Fixed points of multiplication -/

@[simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω := by
  rw [← iSup_iterate_eq_nfp, ← iSup_pow ha]
  congr
  funext n
  induction n with
  | zero => rw [pow_zero, iterate_zero_apply]
  | succ n hn => rw [iterate_succ_apply', Nat.add_comm, pow_add, pow_one, hn]

@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  rw [← Ordinal.le_zero, nfp_le_iff]
  intro n
  induction n with
  | zero => rfl
  | succ n IH => rwa [iterate_succ_apply, mul_zero]

theorem nfp_mul_eq_opow_omega0 {a b : Ordinal} (hb : 0 < b) (hba : b ≤ a ^ ω) :
    nfp (a * ·) b = a ^ ω := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero] at hba ⊢
    simp_rw [Ordinal.le_zero.1 hba, zero_mul]
    exact nfp_zero_left 0
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone hba
    rw [← opow_one_add, one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (isNormal_mul_right ha).monotone (one_le_iff_pos.2 hb)

theorem eq_zero_or_opow_omega0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ a ^ ω ≤ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero]
    exact Or.inr (Ordinal.zero_le b)
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne, ← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (isNormal_mul_right ha).monotone hb (le_of_eq hab)

theorem mul_eq_right_iff_opow_omega0_dvd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega0,
      add_left_cancel_iff] at hab
    rcases eq_zero_or_opow_omega0_le_of_mul_eq_right hab with hab | hab
    · exact hab
    refine (not_lt_of_ge hab (mod_lt b (opow_ne_zero ω ?_))).elim
    rwa [← Ordinal.pos_iff_ne_zero]
  obtain ⟨c, hc⟩ := h
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega0]

theorem mul_le_right_iff_opow_omega0_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b ≤ b ↔ (a ^ ω) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega0_dvd]
  exact (isNormal_mul_right ha).le_iff_eq

theorem nfp_mul_opow_omega0_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
    (hca : c ≤ a ^ ω) : nfp (a * ·) (a ^ ω * b + c) = a ^ ω * succ b := by
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone
    · rw [mul_succ]
      apply add_le_add_left hca
    · dsimp only; rw [← mul_assoc, ← opow_one_add, one_add_omega0]
  · obtain ⟨d, hd⟩ :=
      mul_eq_right_iff_opow_omega0_dvd.1 ((isNormal_mul_right ha).nfp_fp ((a ^ ω) * b + c))
    rw [hd]
    apply mul_le_mul_left'
    have := le_nfp (a * ·) (a ^ ω * b + c)
    rw [hd] at this
    have := (add_lt_add_left hc (a ^ ω * b)).trans_le this
    rw [add_zero, mul_lt_mul_iff_left (opow_pos ω ha)] at this
    rwa [succ_le_iff]

theorem deriv_mul_eq_opow_omega0_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) b = a ^ ω * b := by
  have H := isNormal_mul_right ha
  revert b
  rw [← funext_iff, H.deriv.eq_iff_zero_and_succ (isNormal_mul_right (opow_pos ω ha))]
  refine ⟨?_, fun c h => ?_⟩
  · rw [deriv_zero_right H, nfp_mul_zero, mul_zero]
  · rw [deriv_succ H, h]
    exact nfp_mul_opow_omega0_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))

end Ordinal
