/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Collatz–Wielandt function for matrices

The Collatz–Wielandt formula and the Perron root of a non-negative matrix.

## Main definitions

* `Matrix.collatzWielandtFn`: minimum ratio `(Ax)ᵢ / xᵢ` over positive coordinates.
* `Matrix.CollatzWielandt.nonnegNeZero`: non-negative non-zero vectors.
* `Matrix.CollatzWielandt.perronRoot`: supremum of `collatzWielandtFn` on `nonnegNeZero`.

## Main results

* `Matrix.CollatzWielandt.upperSemicontinuousOn` and `exists_maximizer`
* `Matrix.CollatzWielandt.eq_perron_root_of_positive_eigenvector`
* `Matrix.CollatzWielandt.collatzWielandtFn_le_perronRoot`
* `Matrix.CollatzWielandt.le_of_subinvariant`

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

Collatz–Wielandt, Perron root, non-negative matrix
-/

@[expose] public section

namespace Matrix

section PerronFrobenius

open Set Filter Topology Finset Matrix

open scoped Convex Pointwise

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

/-- Minimum ratio `(Ax)ᵢ / xᵢ` over `{i | xᵢ > 0}`; `0` if there is no positive coordinate. -/
noncomputable def collatzWielandtFn (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  let supp := {i | 0 < (x i)}.toFinset
  if h : supp.Nonempty then supp.inf' h fun i ↦ (A *ᵥ x) i / x i else 0

namespace CollatzWielandt

variable {A : Matrix n n ℝ}

/-- Non-negative non-zero vectors. -/
def nonnegNeZero : Set (n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}

lemma collatzWielandtFn_eq_inf' (A : Matrix n n ℝ) (x : n → ℝ)
    (h : ({i | 0 < (x i)}.toFinset).Nonempty) :
    collatzWielandtFn A x = ({i | 0 < (x i)}.toFinset).inf' h fun i => (A *ᵥ x) i / x i := by
  dsimp [collatzWielandtFn]
  exact dif_pos h

lemma stdSimplex_posSupport_nonempty [Nonempty n] {x : n → ℝ} (hx : x ∈ stdSimplex ℝ n) :
    ({i | 0 < (x i)}.toFinset).Nonempty :=
  let ⟨i, hi⟩ := exists_pos_of_mem_stdSimplex hx
  ⟨i, mem_toFinset.mpr hi⟩

/-- The Collatz–Wielandt function is upper semicontinuous on the standard simplex. -/
theorem upperSemicontinuousOn [Nonempty n] :
    UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) := by
  have hsupp {x : n → ℝ} (hx : x ∈ stdSimplex ℝ n) :
      ({i | 0 < (x i)}.toFinset).Nonempty :=
    stdSimplex_posSupport_nonempty hx
  intro x₀ hx₀ c hc
  have fn_eq := collatzWielandtFn_eq_inf' A x₀ (stdSimplex_posSupport_nonempty hx₀)
  set U := {y : n → ℝ | ∀ i, 0 < x₀ i → 0 < y i}
  have U_open : IsOpen U := by
    have h_eq : U = ⋂ i ∈ {j | 0 < (x₀ j)}.toFinset, {y : n → ℝ | 0 < y i} := by
      ext y
      simp [U]
    rw [h_eq]
    refine isOpen_biInter_finset fun i _ => isOpen_lt continuous_const (continuous_apply i)
  set f := fun y => ({i | 0 < (x₀ i)}.toFinset).inf' (hsupp hx₀) fun i => (A *ᵥ y) i / y i
  have f_cont : ContinuousOn f U := by
    refine ContinuousOn.finset_inf'_apply (hsupp hx₀) fun i hi => ?_
    refine ContinuousOn.div ?_ (continuous_apply i).continuousOn fun y hy => ?_
    · exact
        ((continuous_apply i).comp
          (Matrix.mulVecLin A).continuous_of_finiteDimensional).continuousOn
    · exact (hy i (by simpa using hi)).ne.symm
  have f_ge : ∀ y ∈ U ∩ stdSimplex ℝ n, collatzWielandtFn A y ≤ f y := by
    intro y ⟨hyU, hyS⟩
    have h_sub : {j | 0 < (x₀ j)}.toFinset ⊆ {j | 0 < (y j)}.toFinset := by
      intro j hj
      exact mem_toFinset.mpr (hyU j (by simpa using hj))
    rw [collatzWielandtFn_eq_inf' A y (stdSimplex_posSupport_nonempty hyS)]
    exact inf'_mono_subset h_sub fun j => (A *ᵥ y) j / y j
  rw [fn_eq] at hc
  have x₀_in_U : x₀ ∈ U := fun _ hi => hi
  have cont_at := f_cont.continuousAt (IsOpen.mem_nhds U_open x₀_in_U)
  rcases (eventually_nhds_iff).mp
      (cont_at.eventually_lt continuousAt_const hc) with
    ⟨V, hV, V_open, hx₀V⟩
  refine (mem_nhdsWithin_iff_exists_mem_nhds_inter).2 ?_
  refine ⟨V ∩ U, (V_open.inter U_open).mem_nhds ⟨hx₀V, x₀_in_U⟩, ?_⟩
  rintro y ⟨⟨hyV, hyU⟩, hyS⟩
  exact lt_of_le_of_lt (f_ge y ⟨hyU, hyS⟩) (hV y hyV)

/-- The Collatz–Wielandt function attains its maximum on the standard simplex. -/
theorem exists_maximizer [Nonempty n] :
    ∃ v ∈ stdSimplex ℝ n, IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  exact upperSemicontinuousOn.exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ i⟩ (isCompact_stdSimplex ℝ n)

/-- `collatzWielandtFn A v • v ≤ A *ᵥ v`. -/
lemma le_mulVec (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (hv_ne : v ≠ 0) : collatzWielandtFn A v • v ≤ A *ᵥ v := by
  intro i
  by_cases hi : 0 < v i
  · obtain ⟨j, hj⟩ := Function.exists_pos_of_nonneg_of_ne_zero hv_nonneg hv_ne
    have hle : collatzWielandtFn A v ≤ (A *ᵥ v) i / v i := by
      rw [collatzWielandtFn_eq_inf' A v ⟨j, mem_toFinset.mpr hj⟩]
      exact inf'_le (fun k => (A *ᵥ v) k / v k) (mem_toFinset.mpr hi)
    exact (le_div_iff₀ hi).mp hle
  · have : v i = 0 := le_antisymm (le_of_not_gt hi) (hv_nonneg i)
    simpa [Pi.smul_apply, smul_eq_mul, this, Matrix.mulVec, dotProduct] using
      sum_nonneg fun k _ => mul_nonneg (hA_nonneg i k) (hv_nonneg k)

/-- Values of `collatzWielandtFn A` are bounded by the maximum row sum. -/
lemma bddAbove [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' nonnegNeZero) := by
  use univ.sup' univ_nonempty fun i => ∑ j, A i j
  rintro _ ⟨x, ⟨hx_nonneg, hx_ne⟩, rfl⟩
  obtain ⟨m, _, hmax⟩ := exists_mem_eq_sup' univ_nonempty x
  have hxm_pos : 0 < x m := by
    obtain ⟨j, hj⟩ := Function.exists_pos_of_nonneg_of_ne_zero hx_nonneg hx_ne
    exact hmax ▸ lt_of_lt_of_le hj (le_sup' (f := x) (mem_univ j))
  have hsupp : ({i | 0 < (x i)}.toFinset).Nonempty := ⟨m, mem_toFinset.mpr hxm_pos⟩
  have h_ratio : collatzWielandtFn A x ≤ (A *ᵥ x) m / x m := by
    rw [collatzWielandtFn_eq_inf' A x hsupp]
    exact inf'_le (fun i => (A *ᵥ x) i / x i) (mem_toFinset.mpr hxm_pos)
  exact h_ratio.trans <|
    by
      rw [div_le_iff₀ hxm_pos, Matrix.mulVec, dotProduct]
      calc
        ∑ j, A m j * x j ≤ ∑ j, A m j * x m :=
          sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left
              (le_sup' (f := x) (mem_univ j) |>.trans_eq hmax) (hA_nonneg m j)
        _ = (∑ j, A m j) * x m := (sum_mul _ _ _).symm
        _ ≤ univ.sup' univ_nonempty (fun k => ∑ l, A k l) * x m :=
          mul_le_mul_of_nonneg_right
            (le_sup' (f := fun k => ∑ l, A k l) (mem_univ m)) hxm_pos.le

lemma smul_invariant [Nonempty n] {c : ℝ} (hc : 0 < c) (_ : ∀ i j, 0 ≤ A i j) {x : n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
    collatzWielandtFn A (c • x) = collatzWielandtFn A x := by
  obtain ⟨i₀, hi₀⟩ := Function.exists_pos_of_nonneg_of_ne_zero hx_nonneg hx_ne
  set S := {i | 0 < (x i)}.toFinset
  have hS : S.Nonempty := ⟨i₀, mem_toFinset.mpr hi₀⟩
  have h_supp : {i | 0 < ((c • x) i)}.toFinset = S := by
    ext i; simp [S, smul_eq_mul, mul_pos_iff_of_pos_left hc]
  dsimp [collatzWielandtFn]
  rw [dif_pos (h_supp.symm ▸ hS), dif_pos hS]
  refine Finset.inf'_congr (h_supp.symm ▸ hS) h_supp (fun i hi => ?_)
  simp [mulVec_smul, smul_eq_mul, Pi.smul_apply, mul_div_mul_left _ _ hc.ne']

/-- Supremum of `collatzWielandtFn A` over `nonnegNeZero` (Seneta's Perron root formula). -/
noncomputable def perronRoot (A : Matrix n n ℝ) : ℝ :=
  sSup (collatzWielandtFn A '' nonnegNeZero)

theorem eq_eigenvalue_of_positive_eigenvector [Nonempty n] {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) : collatzWielandtFn A v = r := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hsupp : ({i | 0 < v i}.toFinset).Nonempty :=
    ⟨i₀, mem_toFinset.mpr (hv_pos i₀)⟩
  rw [collatzWielandtFn_eq_inf' A v hsupp]
  refine inf'_eq_of_forall_le_of_exists_le hsupp (fun i => (A *ᵥ v) i / v i) r ?_ ?_
  · intro i _
    have hratio : (A *ᵥ v) i / v i = r := by
      simpa [Pi.smul_apply, smul_eq_mul, (hv_pos i).ne'] using
        congrArg (fun t => t i / v i) h_eig
    simp [hratio]
  · obtain ⟨i, hi⟩ := hsupp
    refine ⟨i, hi, ?_⟩
    simpa [Pi.smul_apply, smul_eq_mul, (hv_pos i).ne'] using
      congrArg (fun t => t i / v i) h_eig

theorem eigenvalue_le_perron_root_of_positive_eigenvector [Nonempty n] {r : ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (_ : 0 < r) (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    r ≤ perronRoot A := by
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  rw [← eq_eigenvalue_of_positive_eigenvector hv_pos h_eig]
  exact le_csSup (bddAbove hA_nonneg) <|
    mem_image_of_mem _ ⟨fun i => (hv_pos i).le, fun h =>
      (hv_pos i).ne' (congr_fun h i)⟩

lemma le_eigenvalue_of_left_eigenvector (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (_ : 0 < r)
    {u : n → ℝ} (hu_pos : ∀ i, 0 < u i) (hu : u ᵥ* A = r • u) {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_ne : w ≠ 0) : collatzWielandtFn A w ≤ r := by
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i => (hu_pos i).le
  have h_right : u ⬝ᵥ (A *ᵥ w) = r * (u ⬝ᵥ w) := by
    calc u ⬝ᵥ (A *ᵥ w) = (u ᵥ* A) ⬝ᵥ w := dotProduct_mulVec u A w
      _ = r * (u ⬝ᵥ w) := by simp [hu, smul_eq_mul]
  refine le_of_mul_le_mul_right ?_ (by
    obtain ⟨i, hi⟩ := Function.exists_pos_of_nonneg_of_ne_zero hw_nonneg hw_ne
    refine sum_pos' (fun j _ => mul_nonneg (hu_pos j).le (hw_nonneg j)) ⟨i, mem_univ _, ?_⟩
    exact mul_pos (hu_pos i) hi)
  have h_intermediate : u ⬝ᵥ (collatzWielandtFn A w • w) ≤ u ⬝ᵥ (A *ᵥ w) := by
    apply sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (le_mulVec hA_nonneg hw_nonneg hw_ne i) (hu_nonneg i)
  simpa [dotProduct_smul, smul_eq_mul, h_right] using h_intermediate

lemma perronRoot_le_eigenvalue_of_left_eigenvector [Nonempty n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (hr_pos : 0 < r) {u : n → ℝ} (hu_pos : ∀ i, 0 < u i)
    (hu : u ᵥ* A = r • u) : perronRoot A ≤ r := by
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  refine csSup_le ?_ ?_
  · exact ⟨collatzWielandtFn A (fun _ => 1), mem_image_of_mem _ ⟨fun _ => zero_le_one, by
      intro h; simpa using congr_fun h i⟩⟩
  rintro _ ⟨w, ⟨hw_nonneg, hw_ne⟩, rfl⟩
  exact le_eigenvalue_of_left_eigenvector hA_nonneg hr_pos hu_pos hu hw_nonneg hw_ne

/-- `1` is an eigenvector of `diagonal v⁻¹ * A * diagonal v` with eigenvalue `r`. -/
lemma ones_eigenvector_of_similarity_transform [DecidableEq n] {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i)
    (h_eig : A *ᵥ v = r • v) :
    (diagonal (v⁻¹) * A * diagonal v) *ᵥ 1 = fun _ => r := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  have hv : (diagonal v) *ᵥ 1 = v := funext fun i => by simp [mulVec_diagonal]
  rw [hv, h_eig, mulVec_smul]
  ext i
  simp [mulVec_diagonal, Pi.smul_apply, smul_eq_mul, (hv_pos i).ne']

/-- Row sums of `diagonal v⁻¹ * A * diagonal v` equal `r`. -/
lemma row_sum_of_similarity_transformed_matrix [DecidableEq n] [Nonempty n] {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) (i : n) :
    ∑ j, (diagonal (v⁻¹) * A * diagonal v) i j = r := by
  simpa [Matrix.mulVec, dotProduct, mul_one] using congrArg (· i) <|
    ones_eigenvector_of_similarity_transform hv_pos h_eig

/-- From `c • x ≤ B *ᵥ x` and constant row sums `r`, deduce `c ≤ r`. -/
lemma le_of_max_le_row_sum [Nonempty n] {B : Matrix n n ℝ} {x : n → ℝ} {c r : ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (h_row_sum : ∀ i, ∑ j, B i j = r) (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_ne : x ≠ 0) (hcx : c • x ≤ B *ᵥ x) : c ≤ r := by
  obtain ⟨m, _, hm⟩ := exists_mem_eq_sup' univ_nonempty x
  refine le_of_mul_le_mul_right (le_trans (by simpa using hcx m) ?_) ?_
  · calc (B *ᵥ x) m = ∑ j, B m j * x j := by simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, B m j * x m :=
        sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (le_sup' (f := x) (mem_univ j) |>.trans_eq hm) (hB_nonneg m j)
      _ = (∑ j, B m j) * x m := (sum_mul _ _ _).symm
      _ = r * x m := by rw [h_row_sum m]
  · obtain ⟨i, hi⟩ := Function.exists_pos_of_nonneg_of_ne_zero hx_nonneg hx_ne
    exact lt_of_lt_of_le hi (le_sup' (f := x) (mem_univ i) |>.trans_eq hm)

theorem le_eigenvalue_of_right_eigenvector [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ}
    (_ : 0 < r) {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) {w : n → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne : w ≠ 0) :
    collatzWielandtFn A w ≤ r := by
  classical
  let D := diagonal v
  let D_inv := diagonal (v⁻¹)
  let B := D_inv * A * D
  let x := D_inv *ᵥ w
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => by
    simpa [B, D, D_inv, Matrix.mul_apply, mul_assoc, diagonal] using
      mul_nonneg (mul_nonneg (inv_nonneg.2 (hv_pos i).le) (hA_nonneg i j)) (hv_pos j).le
  have h_row_sum := row_sum_of_similarity_transformed_matrix hv_pos h_eig
  have hx_nonneg : ∀ i, 0 ≤ x i := fun i => by
    simpa [x, D_inv, mulVec_diagonal] using
      mul_nonneg (inv_nonneg.2 (hv_pos i).le) (hw_nonneg i)
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hw_ne
    have hw_eq : w = D *ᵥ x := by ext i; simp [x, D, D_inv, mulVec_diagonal, (hv_pos i).ne']
    calc w = D *ᵥ x := hw_eq
      _ = 0 := by simp [hx]
  have h_le : collatzWielandtFn A w • x ≤ B *ᵥ x := by
    have h_mul := le_mulVec hA_nonneg hw_nonneg hw_ne
    have h1 : collatzWielandtFn A w • x = D_inv *ᵥ (collatzWielandtFn A w • w) := by
      ext i
      simp [x, D_inv, mulVec_diagonal, Pi.smul_apply]
      ring
    rw [h1]
    have hw_eq : w = D *ᵥ x := by ext i; simp [x, D, D_inv, mulVec_diagonal, (hv_pos i).ne']
    intro i
    have h_Dinv_nonneg : ∀ j k, 0 ≤ D_inv j k := fun j k => by
      by_cases h : j = k <;> simp [D_inv, h, inv_nonneg, (hv_pos _).le]
    have h_mono :
        (D_inv *ᵥ (collatzWielandtFn A w • w)) i ≤ (D_inv *ᵥ (A *ᵥ w)) i := by
      simpa [Matrix.mulVec, dotProduct, D_inv, mulVec_diagonal] using
        sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (h_mul j) (h_Dinv_nonneg i j)
    calc _ ≤ (D_inv *ᵥ (A *ᵥ w)) i := h_mono
      _ = (D_inv *ᵥ (A *ᵥ (D *ᵥ x))) i := by rw [hw_eq]
      _ = (B *ᵥ x) i := by simp [B, ← mulVec_mulVec, ← mulVec_mulVec]
  exact le_of_max_le_row_sum hB_nonneg h_row_sum hx_nonneg hx_ne h_le

theorem eigenvalue_is_ub_of_positive_eigenvector [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {r : ℝ} (hr_pos : 0 < r) {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    perronRoot A ≤ r := by
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  refine csSup_le ?_ ?_
  · exact ⟨collatzWielandtFn A (fun _ => 1), mem_image_of_mem _ ⟨fun _ => zero_le_one, by
      intro h; simpa using congr_fun h i⟩⟩
  rintro _ ⟨w, ⟨hw_nonneg, hw_ne⟩, rfl⟩
  exact le_eigenvalue_of_right_eigenvector hA_nonneg hr_pos hv_pos h_eig hw_nonneg hw_ne

theorem eq_perron_root_of_positive_eigenvector [Nonempty n] {r : ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv_pos : ∀ i, 0 < v i) (hr_pos : 0 < r)
    (h_eig : A *ᵥ v = r • v) : r = perronRoot A :=
  le_antisymm (eigenvalue_le_perron_root_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig)
    (eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig)

lemma collatzWielandtFn_le_perronRoot [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ}
    (hv : v ∈ stdSimplex ℝ n) (hv_ne : v ≠ 0) :
    collatzWielandtFn A v ≤ perronRoot A :=
  le_csSup (bddAbove hA_nonneg) (mem_image_of_mem _ ⟨hv.1, hv_ne⟩)

lemma perronRoot_nonneg [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) : 0 ≤ perronRoot A := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, ⟨hx_nonneg, hx_ne⟩, rfl⟩
  by_cases h : ({i | 0 < (x i)}.toFinset).Nonempty
  · rw [collatzWielandtFn_eq_inf' A x h]
    refine (le_inf'_iff h (fun j => (A *ᵥ x) j / x j)).mpr ?_
    intro j hj
    have hxj : 0 < x j := by simpa using hj
    have hmul_nonneg : 0 ≤ (A *ᵥ x) j := by
      simpa [Matrix.mulVec, dotProduct] using
        sum_nonneg fun k _ => mul_nonneg (hA_nonneg j k) (hx_nonneg k)
    exact div_nonneg hmul_nonneg hxj.le
  · exfalso
    obtain ⟨j, hj⟩ := Function.exists_pos_of_nonneg_of_ne_zero hx_nonneg hx_ne
    exact h ⟨j, mem_toFinset.mpr hj⟩

/-- Sub-invariance forces `μ ≤ collatzWielandtFn A w`. -/
theorem le_of_subinvariant (_ : ∀ i j, 0 ≤ A i j) {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_ne : w ≠ 0) {μ : ℝ} (hμ : μ • w ≤ A *ᵥ w) : μ ≤ collatzWielandtFn A w := by
  obtain ⟨i, hi⟩ := Function.exists_pos_of_nonneg_of_ne_zero hw_nonneg hw_ne
  have hsupp : ({i | 0 < (w i)}.toFinset).Nonempty := ⟨i, mem_toFinset.mpr hi⟩
  rw [collatzWielandtFn_eq_inf' A w hsupp]
  refine (le_inf'_iff hsupp (fun j => (A *ᵥ w) j / w j)).mpr ?_
  intro j hj
  have hwj : 0 < w j := by simpa using hj
  exact (le_div_iff₀ hwj).mpr (by simpa using hμ j)

end CollatzWielandt

end PerronFrobenius

end Matrix
