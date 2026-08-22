/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis

/-!
# Multiplication of a multiseries by a constant

## Main definitions

* `mulConst c ms` multiplies every coefficient of `ms` by the real constant `c`. It represents
  the function `c * f` where `f` is the function represented by `ms`.
* `neg ms` negates every coefficient of `ms`. It is defined as `ms.mulConst (-1)`.

For each operation, we provide two definitions: one for `Multiseries` and one for
`MultiseriesExpansion`. We then prove structural `simp`-lemmas describing their relationships with
`MultiseriesExpansion.seq` and `MultiseriesExpansion.toFun`. Finally, we prove that both operations
preserve `Sorted` and `Approximates`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

/-- Multiplies all coefficients of the multiseries by `c`. -/
def mulConst {basis : Basis} (c : ℝ) (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal (c * ms.toReal)
  | List.cons _ _ =>
    mk (ms.seq.map id (fun coef => coef.mulConst c)) (c • ms.toFun)

/-- Negates all coefficients of the multiseries. -/
def neg {basis : Basis} (ms : MultiseriesExpansion basis) : MultiseriesExpansion basis :=
  ms.mulConst (-1)

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
instance {basis : Basis} : Neg (MultiseriesExpansion basis) where
  neg := neg

/-- `Multiseries`-part of `MultiseriesExpansion.mulConst`. -/
def Multiseries.mulConst {basis_hd basis_tl} (c : ℝ) (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  ms.map id (fun coef => coef.mulConst c)

/-- `Multiseries`-part of `MultiseriesExpansion.neg`. -/
def Multiseries.neg {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  ms.mulConst (-1)

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
instance {basis_hd basis_tl} : Neg (Multiseries basis_hd basis_tl) where
  neg := Multiseries.neg

open Filter Asymptotics

@[simp]
theorem mulConst_toFun {basis : Basis} {ms : MultiseriesExpansion basis} {c : ℝ} :
    (ms.mulConst c).toFun = c • ms.toFun := by
  cases basis <;> rfl

@[simp]
theorem mulConst_seq {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    {c : ℝ} : (ms.mulConst c).seq = ms.seq.mulConst c :=
  rfl

@[simp]
theorem Multiseries.mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    @mulConst basis_hd basis_tl c nil = nil := by
  simp [mulConst]

@[simp]
theorem Multiseries.mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).mulConst c = cons exp (coef.mulConst c) (tl.mulConst c) := by
  simp [mulConst]

@[simp]
theorem Multiseries.mulConst_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : Multiseries basis_hd basis_tl} {c : ℝ} :
    (ms.mulConst c).leadingExp = ms.leadingExp := by
  cases ms <;> simp [mulConst]

mutual

@[simp]
theorem Multiseries.const_mulConst {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : ℝ} :
    (Multiseries.const basis_hd basis_tl x).mulConst y = Multiseries.const _ _ (y * x) := by
  simp [Multiseries.const, const_mulConst (basis := basis_tl)]

@[simp]
theorem const_mulConst {basis : Basis} {x y : ℝ} :
    (const basis x).mulConst y = const basis (y * x) := by
  cases basis with
  | nil => simp [mulConst, const]
  | cons =>
    rw [ext_iff]
    simp only [mulConst_seq, const_seq, mulConst_toFun, const_toFun']
    exact ⟨Multiseries.const_mulConst, rfl⟩

end

mutual

@[simp]
theorem Multiseries.mulConst_one {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl} :
    ms.mulConst 1 = ms := by
  simp [Multiseries.mulConst, mulConst_one (basis := basis_tl), Function.id_def]

@[simp]
theorem mulConst_one {basis} {ms : MultiseriesExpansion basis} :
    ms.mulConst 1 = ms := by
  cases basis with
  | nil => simp [mulConst]
  | cons =>
    simp only [ext_iff, mulConst_seq, mulConst_toFun, one_smul, and_true]
    rw [Multiseries.mulConst_one]

end

mutual

@[simp]
theorem Multiseries.mulConst_mulConst {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl}
    {x y : ℝ} :
    (ms.mulConst x).mulConst y = ms.mulConst (x * y) := by
  simp [Multiseries.mulConst, ← Multiseries.map_comp, CompTriple.comp_eq, Function.comp_def,
    mulConst_mulConst (basis := basis_tl)]

@[simp]
theorem mulConst_mulConst {basis : Basis} {ms : MultiseriesExpansion basis} {x y : ℝ} :
    (ms.mulConst x).mulConst y = ms.mulConst (x * y) := by
  cases basis with
  | nil => simp [mulConst, mul_assoc, mul_left_comm]
  | cons =>
    simp only [ext_iff, mulConst_seq, mulConst_toFun]
    exact ⟨by rw [Multiseries.mulConst_mulConst], by simp [smul_smul, mul_comm]⟩

end

mutual

theorem Multiseries.mulConst_sorted {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl} {c : ℝ}
    (h_sorted : ms.Sorted) : (ms.mulConst c).Sorted := by
  let motive (ms : Multiseries basis_hd basis_tl) : Prop :=
    ∃ X : Multiseries basis_hd basis_tl, ms = X.mulConst c ∧ X.Sorted
  refine Multiseries.Sorted.coind motive ⟨ms, rfl, h_sorted⟩ ?_
  rintro exp' coef' tl' ⟨X, h_ms_eq, hX_sorted⟩
  cases X with
  | nil => simp at h_ms_eq
  | cons exp coef tl =>
    obtain ⟨hX_coef_sorted, hX_comp, hX_tl_sorted⟩ := hX_sorted.elim_cons
    simp only [Multiseries.mulConst_cons, Multiseries.cons_eq_cons] at h_ms_eq
    obtain ⟨rfl, rfl, rfl⟩ := h_ms_eq
    exact ⟨mulConst_sorted hX_coef_sorted, by simpa using hX_comp, tl, rfl, hX_tl_sorted⟩

/-- Multiplication by a constant preserves `Sorted`. -/
theorem mulConst_sorted {basis : Basis} {ms : MultiseriesExpansion basis} {c : ℝ}
    (h_sorted : ms.Sorted) : (ms.mulConst c).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp only [sorted_iff_seq_sorted, mulConst_seq]
    apply Multiseries.mulConst_sorted
    simpa using h_sorted

end

/-- If `ms` approximates `ms.toFun`, then `ms.mulConst c` approximates `c • ms.toFun`. -/
theorem mulConst_approximates {basis : Basis} {ms : MultiseriesExpansion basis} {c : ℝ}
    (h_approx : ms.Approximates) :
    (ms.mulConst c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    let motive (ms' : MultiseriesExpansion (basis_hd :: basis_tl)) : Prop :=
      ∃ X : MultiseriesExpansion (basis_hd :: basis_tl), ms' = X.mulConst c ∧ X.Approximates
    refine Approximates.coind motive ⟨ms, rfl, h_approx⟩ ?_
    rintro _ ⟨X, rfl, hX_approx⟩
    cases X with
    | nil =>
      left
      simp only [mulConst_seq, mk_seq, Multiseries.mulConst_nil, mulConst_toFun, mk_toFun, true_and]
      exact (Approximates.elim_nil hX_approx).mono fun t h ↦ by simp [h]
    | cons X_exp X_coef X_tl fX =>
      obtain ⟨hX_coef, hX_maj, hX_tl⟩ := hX_approx.elim_cons
      right
      simp only [mulConst_seq, mk_seq, Multiseries.mulConst_cons, Multiseries.cons_eq_cons,
        mulConst_toFun, mk_toFun, ↓existsAndEq, and_true, mulConst_approximates hX_coef,
        Algebra.mul_smul_comm, true_and, exists_eq_left', hX_maj.smul]
      exact ⟨_, by simp [smul_sub], hX_tl⟩

@[simp]
theorem neg_toFun {basis : Basis} {ms : MultiseriesExpansion basis} :
    ms.neg.toFun = -ms.toFun := by
  simp [neg]

@[simp]
theorem neg_seq {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.neg.seq = ms.seq.neg :=
  rfl

@[simp]
theorem Multiseries.neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    @Multiseries.neg basis_hd basis_tl .nil = .nil := by
  simp [Multiseries.neg]

@[simp]
theorem Multiseries.neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).neg = cons exp coef.neg tl.neg := by
  simp [Multiseries.neg, MultiseriesExpansion.neg]

@[simp]
theorem Multiseries.neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X : Multiseries basis_hd basis_tl} :
    X.neg.leadingExp = X.leadingExp := by
  simp [neg]

@[simp]
theorem Multiseries.neg_neg {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl} :
    ms.neg.neg = ms := by
  simp [Multiseries.neg]

@[simp]
theorem neg_neg {basis : Basis} {ms : MultiseriesExpansion basis} : ms.neg.neg = ms := by
  cases basis <;> simp [neg]

theorem Multiseries.neg_sorted {basis_hd basis_tl} {ms : Multiseries basis_hd basis_tl}
    (h_sorted : ms.Sorted) : ms.neg.Sorted :=
  Multiseries.mulConst_sorted h_sorted

/-- Negation preserves `Sorted`. -/
theorem neg_sorted {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_sorted : ms.Sorted) : ms.neg.Sorted :=
  mulConst_sorted h_sorted

/-- If `ms` approximates `ms.toFun`, then `ms.neg` approximates `-ms.toFun`. -/
theorem neg_approximates {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_approx : ms.Approximates) : ms.neg.Approximates :=
  mulConst_approximates h_approx

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
