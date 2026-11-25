/-
Copyright (c) 2026 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Algebra.Star.Pi

/-!
# Accretive Matrices

A matrix `M` is accretive if `xᴴMx` is non-negative for all `x`, and strictly accretive if `xᴴMx`
is positive for all non-zero `x`.

-/

@[expose] public section

namespace Matrix

variable {m n R R' : Type*}
variable [Ring R] [PartialOrder R] [StarRing R]
variable [CommRing R'] [PartialOrder R'] [StarRing R']

/-!
## Accretive matrices
-/

/-- A matrix `M` is accretive if `xᴴMx` is non-negative for all `x`. -/
def IsAccretive (M : Matrix n n R) : Prop :=
  ∀ x : n →₀ R, 0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

protected theorem IsAccretive.diagonal [StarOrderedRing R] [DecidableEq n] {d : n → R} (h : 0 ≤ d) :
    IsAccretive (diagonal d) :=
  -- TODO: positivity
  fun _ ↦ Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]

/-- A diagonal matrix is accretive iff its diagonal entries are non-negative. -/
@[simp] lemma isAccretive_diagonal_iff [StarOrderedRing R] [DecidableEq n] {d : n → R} :
    IsAccretive (diagonal d) ↔ ∀ i, 0 ≤ d i :=
  ⟨fun hP i ↦ by simpa using hP (.single i 1), .diagonal⟩

namespace IsAccretive

variable {M N : Matrix n n R}

theorem submatrix {M : Matrix n n R} (hM : M.IsAccretive) (e : m → n) :
    (M.submatrix e e).IsAccretive := by
  intro x
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM <| x.mapDomain e

theorem transpose {M : Matrix n n R'} (hM : M.IsAccretive) : Mᵀ.IsAccretive := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  intro x
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM (Finsupp.mapRange star (star_zero R') x)

@[simp]
theorem _root_.Matrix.isAccretive_transpose_iff {M : Matrix n n R'} :
    Mᵀ.IsAccretive ↔ M.IsAccretive :=
  ⟨.transpose, .transpose⟩

protected lemma add [AddLeftMono R] (hM : M.IsAccretive) (hN : N.IsAccretive) :
    (M + N).IsAccretive := by
  intro; simpa [mul_add, add_mul] using add_nonneg (hM _) (hN _)

protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [Algebra α R] [PosSMulMono α R]
    (hM : M.IsAccretive) {a : α} (ha : 0 ≤ a) : (a • M).IsAccretive := by
  intro; simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hM _)

protected lemma zero : IsAccretive (0 : Matrix n n R) := by
  intro; simp

protected lemma one [StarOrderedRing R] [DecidableEq n] : IsAccretive (1 : Matrix n n R) :=
  fun _ ↦ Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]

protected theorem natCast [StarOrderedRing R] [DecidableEq n] (d : ℕ) :
    IsAccretive (d : Matrix n n R) :=
  fun _ ↦ Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_natCast', star_left_conjugate_nonneg, *]

protected theorem ofNat [StarOrderedRing R] [DecidableEq n] (d : ℕ) [d.AtLeastTwo] :
    IsAccretive (ofNat(d) : Matrix n n R) :=
  .natCast d

protected theorem intCast [StarOrderedRing R] [DecidableEq n] (d : ℤ) (hd : 0 ≤ d) :
    IsAccretive (d : Matrix n n R) :=
  fun _ ↦ Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_intCast', star_left_conjugate_nonneg, *]

@[simp]
protected theorem _root_.Matrix.isAccretive_intCast_iff
    [StarOrderedRing R] [DecidableEq n] [Nonempty n] [Nontrivial R] (d : ℤ) :
    IsAccretive (d : Matrix n n R) ↔ 0 ≤ d := by simp [← diagonal_intCast']

lemma diag_nonneg (hM : M.IsAccretive) {i : n} : 0 ≤ M i i := by
  simpa using hM <| .single i 1

variable (n R) in
/-- The set of matrices that are accretive form an additive submonoid. -/
@[simps]
def addSubmonoid [AddLeftMono R] : AddSubmonoid (Matrix n n R) where
  carrier := .ofPred IsAccretive
  add_mem' := .add
  zero_mem' := .zero

@[simp]
theorem mem_addSubmonoid [AddLeftMono R] :
    M ∈ addSubmonoid n R ↔ M.IsAccretive :=
  Iff.rfl

end IsAccretive

@[simp]
theorem isAccretive_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).IsAccretive ↔ M.IsAccretive :=
  ⟨fun h ↦ by simpa using h.submatrix e.symm, fun h ↦ h.submatrix _⟩

theorem isAccretive_sum {ι : Type*} [AddLeftMono R]
    {x : ι → Matrix n n R} (s : Finset ι) (h : ∀ i ∈ s, IsAccretive (x i)) :
    IsAccretive (∑ i ∈ s, x i) := by
  intro
  simp [Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm, Finset.sum_nonneg
    fun _ hi ↦ h _ hi _]

/-!
## Strictly accretive matrices
-/

/-- A matrix `M` is strictly accretive if `xᴴMx` is positive for all non-zero `x`. -/
def IsStrictlyAccretive (M : Matrix n n R) : Prop :=
  ∀ ⦃x : n →₀ R⦄, x ≠ 0 → 0 < x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

namespace IsStrictlyAccretive

variable {M N : Matrix n n R}

lemma isAccretive (hM : M.IsStrictlyAccretive) :
    M.IsAccretive := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · exact (hM hx).le

theorem submatrix (hM : M.IsStrictlyAccretive) {e : m → n} (he : e.Injective) :
    (M.submatrix e e).IsStrictlyAccretive := by
  intro x hx
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
    hM <| Finsupp.mapDomain_injective he |>.ne_iff' Finsupp.mapDomain_zero |>.2 hx

theorem transpose {M : Matrix n n R'} (hM : M.IsStrictlyAccretive) :
    Mᵀ.IsStrictlyAccretive := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  intro x
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
    hM (x := x.mapRange star (star_zero R'))

@[simp]
theorem transpose_iff {M : Matrix n n R'} : Mᵀ.IsStrictlyAccretive ↔ M.IsStrictlyAccretive :=
  ⟨(by simpa using ·.transpose), .transpose⟩

protected theorem diagonal [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    {d : n → R} (h : ∀ i, 0 < d i) :
    IsStrictlyAccretive (diagonal d) := by
  intro x hx
  refine Finsupp.sum_pos' (fun _ _ ↦ Finsupp.sum_nonneg ?_) ?_
  · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
  obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
  refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
    apply_ite, star_left_conjugate_nonneg (h _).le,
    star_left_conjugate_pos (h i), IsRegular.of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

@[simp]
theorem _root_.Matrix.isStrictlyAccretive_diagonal_iff
    [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] [Nontrivial R] {d : n → R} :
    IsStrictlyAccretive (diagonal d) ↔ ∀ i, 0 < d i :=
  ⟨fun h i ↦ by simpa using h (x := .single i 1), .diagonal⟩

@[simp, nontriviality]
theorem of_subsingleton (h : Subsingleton R) (M : Matrix n n R) : M.IsStrictlyAccretive :=
  fun _ hx ↦ (hx <| Subsingleton.elim ..).elim

protected theorem one [StarOrderedRing R] [DecidableEq n] [IsProperStar R] :
    IsStrictlyAccretive (1 : Matrix n n R) :=
  fun x hx ↦ Finsupp.sum_pos (by aesop (add simp Matrix.one_apply)) hx

protected theorem natCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) (hd : d ≠ 0) :
    IsStrictlyAccretive (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

@[simp]
theorem _root_.Matrix.isStrictlyAccretive_natCast_iff [StarOrderedRing R] [DecidableEq n]
    [NoZeroDivisors R] [Nonempty n] [Nontrivial R] {d : ℕ} :
    IsStrictlyAccretive (d : Matrix n n R) ↔ 0 < d :=
  isStrictlyAccretive_diagonal_iff.trans <| by simp

protected theorem ofNat [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) [d.AtLeastTwo] :
    IsStrictlyAccretive (ofNat(d) : Matrix n n R) :=
  .natCast d (NeZero.ne _)

protected theorem intCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℤ) (hd : 0 < d) :
    IsStrictlyAccretive (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

@[simp]
theorem _root_.Matrix.isStrictlyAccretive_intCast_iff [StarOrderedRing R] [DecidableEq n]
    [NoZeroDivisors R] [Nonempty n] [Nontrivial R] {d : ℤ} :
    IsStrictlyAccretive (d : Matrix n n R) ↔ 0 < d :=
  isStrictlyAccretive_diagonal_iff.trans <| by simp

protected lemma add_isAccretive [AddLeftMono R] (hM : M.IsStrictlyAccretive) (hN : N.IsAccretive) :
    (M + N).IsStrictlyAccretive := by
  intro x hx
  simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hM (x := x) hx) (hN x)

protected lemma isAccretive_add [AddLeftMono R] (hM : M.IsAccretive) (hN : N.IsStrictlyAccretive) :
    (M + N).IsStrictlyAccretive :=
  add_comm M N ▸ hN.add_isAccretive hM

protected lemma add [AddLeftMono R] (hM : M.IsStrictlyAccretive) (hN : N.IsStrictlyAccretive) :
    (M + N).IsStrictlyAccretive :=
  hM.add_isAccretive hN.isAccretive

theorem _root_.Matrix.isStrictlyAccretive_sum {ι : Type*} [AddLeftMono R] {x : ι → Matrix m m R}
    {s : Finset ι} (hs : s.Nonempty) (hA : ∀ i ∈ s, (x i).IsStrictlyAccretive) :
    (∑ i ∈ s, x i).IsStrictlyAccretive := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i hi hins H =>
      rw [Finset.sum_insert hins]
      by_cases h : ¬ hi.Nonempty
      · simp_all
      · exact IsStrictlyAccretive.add (hA _ <| Finset.mem_insert_self i hi) <|
          H (not_not.mp h) fun _ _hi => hA _ (Finset.mem_insert_of_mem _hi)

protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [Algebra α R]
    [PosSMulStrictMono α R] (hM : M.IsStrictlyAccretive) {a : α} (ha : 0 < a) :
    (a • M).IsStrictlyAccretive := by
  intro _ h
  simpa [← Finsupp.smul_sum] using smul_pos ha (hM h)

lemma diag_pos [Nontrivial R] (hM : M.IsStrictlyAccretive) {i : n} : 0 < M i i := by
  simpa using hM (x := Finsupp.single i 1)

end IsStrictlyAccretive

/-!
## Finite accretive matrices
-/

variable [Fintype n] [Fintype m]

/-- A finite matrix `M : Matrix n n R` is accretive iff it is `xᴴ * M * x` is non-negative for
all `x`. -/
@[simp] theorem isAccretive_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.IsAccretive ↔ ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
  simp [IsAccretive, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc]

namespace IsAccretive

omit [Fintype n] in
/-- A matrix `M : Matrix n n R` is accretive iff every finite principal submatrix is accretive. -/
theorem _root_.Matrix.isAccretive_iff_submatrix_finset {M : Matrix n n R} :
    M.IsAccretive ↔ ∀ s : Finset n, (M.submatrix (↑) (↑) : Matrix s s R).IsAccretive := by
  refine ⟨fun hM s ↦ hM.submatrix _, fun h x ↦ ?_⟩
  classical
  simpa [Finsupp.sum, ← Finset.sum_attach x.support] using (h x.support) (x.subtypeDomain _)

omit [Fintype n] in
/-- A matrix `M : Matrix n n R` is accretive iff `M.submatrix (f i) (f i)` is accretive for a family
of maps `f` whose ranges cover every finite subset of `n`. -/
theorem _root_.Matrix.isAccretive_iff_submatrix_of_forall_finset {ι : Type*} {κ : ι → Type*}
    (f : ∀ i, κ i → n) (hf : ∀ s : Finset n, ∃ i, (s : Set n) ⊆ Set.range (f i))
    {M : Matrix n n R} :
    M.IsAccretive ↔ ∀ i, (M.submatrix (f i) (f i)).IsAccretive := by
  refine ⟨fun h i ↦ h.submatrix _, fun h ↦ isAccretive_iff_submatrix_finset.mpr fun s ↦ ?_⟩
  obtain ⟨i, hi⟩ := hf s
  choose g hg using fun x : s ↦ hi x.2
  exact funext hg ▸ (h i).submatrix g

protected lemma inv [DecidableEq n] [TrivialStar R'] {M : Matrix n n R'} (hM : M.IsAccretive) :
    M⁻¹.IsAccretive := by
  by_cases h : IsUnit M.det
  · rw [isAccretive_iff_dotProduct_mulVec]
    intro x
    let y : n → R' := M⁻¹ *ᵥ x
    have : x = M *ᵥ y := by rw [mulVec_mulVec, mul_nonsing_inv M h]; simp
    simp_all [dotProduct_comm]
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero

lemma trace_nonneg [AddLeftMono R] {M : Matrix n n R} (hM : M.IsAccretive) : 0 ≤ M.trace :=
  Fintype.sum_nonneg fun _ ↦ hM.diag_nonneg

end IsAccretive

/-!
## Finite strictly accretive matrices
-/

theorem isStrictlyAccretive_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.IsStrictlyAccretive ↔ ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x) := by
  have (x : n →₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 ↦ Finsupp.coe_eq_zero.mpr h1,fun h2 ↦ Finsupp.coe_eq_zero.mp h2⟩
  simp [IsStrictlyAccretive, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

namespace IsStrictlyAccretive

/-- A matrix `M : Matrix n n R` is strictly accretive if `xᴴMx` is greater than zero for all
non-zero `x`. -/
@[simp]
lemma dotProduct_mulVec_pos {M : Matrix n n R} (hM : M.IsStrictlyAccretive) {x} (hx : x ≠ 0) :
    0 < star x ⬝ᵥ (M *ᵥ x) := isStrictlyAccretive_iff_dotProduct_mulVec.mp hM hx

omit [Fintype n] in
/-- A matrix `M : Matrix n n R` is strictly accretive iff every finite principal submatrix is
strictly accretive. -/
theorem _root_.Matrix.isStrictlyAccretive_iff_submatrix_finset {M : Matrix n n R} :
    M.IsStrictlyAccretive
      ↔ ∀ s : Finset n, (M.submatrix (↑) (↑) : Matrix s s R).IsStrictlyAccretive := by
  classical
  refine ⟨fun hM s ↦ hM.submatrix Subtype.coe_injective, fun h x hx ↦ ?_⟩
  simp_rw [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]
  exact h x.support <| by simpa [← Finsupp.support_nonempty_iff] using hx

omit [Fintype n] in
/-- A matrix `M : Matrix n n R` is strictly accretive iff `M.submatrix (f i) (f i)` is strictly
accretive for a family of injective maps `f` whose ranges cover every finite subset of `n`. -/
theorem _root_.Matrix.isStrictlyAccretive_iff_submatrix_of_forall_finset {ι : Type*} {κ : ι → Type*}
    (f : ∀ i, κ i → n) (hf_inj : ∀ i, (f i).Injective)
    (hf : ∀ s : Finset n, ∃ i, (s : Set n) ⊆ Set.range (f i)) {M : Matrix n n R} :
    M.IsStrictlyAccretive ↔ ∀ i, (M.submatrix (f i) (f i)).IsStrictlyAccretive := by
  refine ⟨fun h i ↦ h.submatrix (hf_inj i), fun h ↦ ?_⟩
  apply isStrictlyAccretive_iff_submatrix_finset.mpr fun s ↦ ?_
  obtain ⟨i, hi⟩ := hf s
  choose g hg using fun x : s ↦ hi x.2
  have hfg : f i ∘ g = (↑) := funext hg
  exact hfg ▸ (h i).submatrix (.of_comp (hfg ▸ Subtype.coe_injective))

lemma mulVec_injective {M : Matrix n n R} (hM : M.IsStrictlyAccretive) :
    Function.Injective M.mulVec := by
  intro _ _ hxy; by_contra h
  simpa [mulVec_sub, hxy] using hM.dotProduct_mulVec_pos (sub_ne_zero_of_ne h)

lemma trace_pos [Nontrivial R] [IsOrderedCancelAddMonoid R] [Nonempty n] {M : Matrix n n R}
    (hA : M.IsStrictlyAccretive) : 0 < M.trace :=
  Finset.sum_pos (fun _ _ ↦ hA.diag_pos) Finset.univ_nonempty

theorem det_pos [DecidableEq n] [Nontrivial R'] [IsOrderedRing R'] [PosMulReflectLT R']
    {M : Matrix n n R'} (hA : M.IsStrictlyAccretive) :
    0 < M.det := by
  replace hM : ∀ ⦃x : n → R'⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x) := by
    intro x hx
    simpa [dotProduct, mulVec, Finsupp.sum_fintype, Finset.mul_sum, mul_assoc] using
      hA (x := Finsupp.equivFunOnFinite.symm x) fun h ↦ hx <| by ext i; simpa using congr($h i)
  suffices ∀ k (N : Matrix (Fin k) (Fin k) R'),
      (∀ ⦃x : Fin k → R'⦄, x ≠ 0 → 0 < star x ⬝ᵥ (N *ᵥ x)) → 0 < N.det by
    rw [← det_submatrix_equiv_self (Fintype.equivFin n).symm M]
    refine this _ _ fun x hx ↦ ?_
    have : star (x ∘ Fintype.equivFin n) = star x ∘ Fintype.equivFin n := rfl
    simpa [this, submatrix_mulVec_equiv, dotProduct_comp_equiv_symm] using
      hM (x := x ∘ Fintype.equivFin n) fun h ↦ hx <| by
        ext i; simpa using congr($h ((Fintype.equivFin n).symm i))
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro N hN
    set M := N.submatrix Fin.succ Fin.succ with M_def
    set v : Fin (k + 1) → R' := N.adjugate.col 0 with v_def
    have hM (x : Fin k → R') (hx : x ≠ 0) : 0 < star x ⬝ᵥ (M *ᵥ x) := by
      simpa [M_def, dotProduct, mulVec, Fin.sum_univ_succ] using
        hN (x := Fin.cons 0 x) fun h ↦ hx <| by ext i; simpa using congr($h i.succ)
    have hvM : v 0 = M.det := by simp [M_def, v_def, adjugate_fin_succ_eq_det_submatrix]
    replace ih : 0 < M.det := ih _ hM
    have hstar (c : R') (hc : c ≠ 0) : 0 < c * star c := by
      have h₁ : 0 < N 0 0 := by simpa using hN (x := Pi.single 0 1) (by simp)
      have h₂ : 0 < c * (star c * N 0 0) := by simpa using hN (x := Pi.single 0 c) (by simpa)
      exact pos_of_mul_pos_right (a := N 0 0) (by convert h₂ using 1; ring) h₁.le
    have hM_det : 0 < star M.det := pos_of_mul_pos_right (hstar _ ih.ne') ih.le
    have hNv : N *ᵥ v = fun i ↦ if i = 0 then N.det else 0 := by
      ext; simp [v_def, ← col_mul_eq_mulVec_col, mul_adjugate, Matrix.one_apply]
    have hv₀ : v ≠ 0 := fun contra ↦ ih.ne' <| by simp [← hvM, contra]
    refine pos_of_mul_pos_right (a := star M.det) ?_ hM_det.le
    simpa [hNv, dotProduct, hvM] using hN hv₀

end IsStrictlyAccretive

end Matrix
