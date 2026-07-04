/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis

/-!
# Basic constructions for multiseries

## Main definitions

Let `[b₁, ..., bₙ]` be our basis.

* `const c` represents a constant multiseries `c • b₁⁰ ... bₙ⁰`.
  Then we define `zero` and `one` in terms of it.
* `monomial k` represents a monomial `bₖ`.
* `monomialRpow k r` represents a monomial `bₖʳ`.

For each construction, we provide two definitions: one for `Multiseries` and one for
`MultiseriesExpansion`. We then prove structural `simp`-lemmas describing their relationships with
`MultiseriesExpansion.seq` and `MultiseriesExpansion.toFun`. Finally, we prove that all
constructions are `Sorted` and `Approximates` their attached functions.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open Filter Stream' Topology

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.const`. -/
def Multiseries.const (basis_hd : ℝ → ℝ) (basis_tl : Basis) (c : ℝ) :
    Multiseries basis_hd basis_tl :=
  .cons 0 (const basis_tl c) .nil

/-- Multiseries representing a constant. -/
def const (basis : Basis) (c : ℝ) : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal c
  | List.cons basis_hd basis_tl => mk (Multiseries.const basis_hd basis_tl c) (fun _ ↦ c)

end

/-- Neutral element for addition. It is `0 : ℝ` for the empty basis and `[]` otherwise. -/
def zero {basis : Basis} : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ ↦ 0)

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
instance {basis : Basis} : Zero (MultiseriesExpansion basis) where
  zero := zero

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Zero (Multiseries basis_hd basis_tl) where
  zero := .nil

/-- `Multiseries`-part of `MultiseriesExpansion.one`. -/
def Multiseries.one {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Multiseries basis_hd basis_tl :=
  Multiseries.const _ _ 1

/-- Neutral element for multiplication. -/
def one {basis : Basis} : MultiseriesExpansion basis :=
  const basis 1

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.monomialRpow`. -/
noncomputable def Multiseries.monomialRpow (basis_hd : ℝ → ℝ) (basis_tl : Basis) (n : ℕ) (r : ℝ) :
    Multiseries basis_hd basis_tl :=
  match n with
  | 0 => .cons r one .nil
  | m + 1 => .cons 0 (monomialRpow _ m r) .nil

/-- Multiseries representing `basis[n] ^ r`. -/
noncomputable def monomialRpow (basis : Basis) (n : ℕ) (r : ℝ) : MultiseriesExpansion basis :=
  match basis with
  | [] => default
  | List.cons basis_hd basis_tl =>
    mk (Multiseries.monomialRpow _ _ n r) ((basis_hd :: basis_tl)[n]! ^ r)

end

/-- `Multiseries`-part of `MultiseriesExpansion.monomial`. -/
noncomputable def Multiseries.monomial (basis_hd : ℝ → ℝ) (basis_tl : Basis) (n : ℕ) :
    Multiseries basis_hd basis_tl :=
  Multiseries.monomialRpow _ _ n 1

/-- Multiseries representing `basis[n]`. -/
noncomputable def monomial (basis : Basis) (n : ℕ) : MultiseriesExpansion basis :=
  monomialRpow _ n 1

theorem zero_def {basis_hd basis_tl} :
    (0 : MultiseriesExpansion (basis_hd :: basis_tl)) = mk .nil (fun _ ↦ 0) :=
  rfl

@[simp]
theorem Multiseries.zero_def {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (0 : Multiseries basis_hd basis_tl) = .nil := rfl

theorem Multiseries.const_def {basis_hd basis_tl} (c : ℝ) :
    Multiseries.const basis_hd basis_tl c =
    Multiseries.cons 0 (MultiseriesExpansion.const basis_tl c) .nil := by
  simp [Multiseries.const]

@[simp]
theorem const_toFun' {basis : Basis} {c : ℝ} : (const basis c).toFun = fun _ ↦ c := by
  match basis with
  | [] => simp [const, ofReal, toReal]
  | List.cons _ _ => simp [const]

@[simp]
theorem const_seq {basis_hd basis_tl} {c : ℝ} :
    (const (basis_hd :: basis_tl) c).seq = Multiseries.const basis_hd basis_tl c := by
  simp [const, Multiseries.const]

@[simp]
theorem zero_toFun {basis : Basis} : (@zero basis).toFun = 0 := by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

theorem Multiseries.one_def {basis_hd basis_tl} :
    @Multiseries.one basis_hd basis_tl = Multiseries.cons 0 MultiseriesExpansion.one .nil := by
  simp [Multiseries.one, Multiseries.const_def, MultiseriesExpansion.one]

@[simp]
theorem one_toFun {basis : Basis} : (@one basis).toFun = 1 := by
  simp [one]
  rfl

@[simp]
theorem one_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (@one (basis_hd :: basis_tl)).seq = Multiseries.one := by
  simp [one, Multiseries.one, const]

mutual

theorem Multiseries.const_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    (Multiseries.const basis_hd basis_tl c).Sorted := by
  simp only [Multiseries.const]
  exact const_sorted.cons_nil

/-- Constants are well-ordered. -/
theorem const_sorted {basis : Basis} {c : ℝ} :
    (const basis c).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [const, sorted_iff_seq_sorted, mk_seq] using Multiseries.const_sorted

end

/-- Zero is well-ordered. -/
theorem zero_sorted {basis : Basis} : (0 : MultiseriesExpansion basis).Sorted := by
  cases basis with
  | nil => constructor
  | cons => apply Sorted.nil

theorem Multiseries.one_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (Multiseries.one : Multiseries basis_hd basis_tl).Sorted :=
  Multiseries.const_sorted

/-- `one` is Sorted. -/
theorem one_sorted {basis : Basis} : one.Sorted (basis := basis) :=
  const_sorted

/-- The constant multiseries approximates the constant function. -/
theorem const_approximates {c : ℝ} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [const, Multiseries.const]
    apply (const_approximates h_basis.tail).cons _ (by simp)
    exact Majorized.const <| h_basis.tendsto_atTop (by simp)

/-- `zero` approximates the zero function. -/
theorem zero_approximates {basis : Basis} :
    (@zero basis).Approximates := by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

/-- `one` approximates the unit function. -/
theorem one_approximates {basis : Basis} (h_basis : WellFormedBasis basis) :
    (@one basis).Approximates :=
  const_approximates h_basis

@[simp]
theorem monomialRpow_toFun {basis : Basis} {n : Fin (List.length basis)} {r : ℝ} :
    (monomialRpow basis n r).toFun = basis[n] ^ r := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomialRpow]

@[simp]
theorem monomialRpow_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ} :
    (monomialRpow (basis_hd :: basis_tl) n r).seq = Multiseries.monomialRpow _ _ n r := by
  simp [monomialRpow]

mutual

theorem Multiseries.monomialRpow_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ} :
    (@Multiseries.monomialRpow basis_hd basis_tl n r).Sorted := by
  cases n with
  | zero =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil const_sorted
  | succ m =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil monomialRpow_sorted

/-- `monomial` is well-ordered. -/
theorem monomialRpow_sorted {basis : Basis} {n : ℕ} {r : ℝ} :
    (monomialRpow basis n r).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [sorted_iff_seq_sorted, monomialRpow_seq] using Multiseries.monomialRpow_sorted

end

/-- `monomialRpow` approximates the monomial function. -/
theorem monomialRpow_approximates {basis : Basis} {n : Fin (List.length basis)} {r : ℝ}
    (h_basis : WellFormedBasis basis) :
    (monomialRpow basis n r).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [List.length_cons, monomialRpow, Fin.is_lt, getElem!_pos]
    cases n using Fin.cases with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Multiseries.monomialRpow,
        List.getElem_cons_zero]
      apply (one_approximates h_basis.tail).cons _ (by simp)
      exact Majorized.self <| h_basis.tendsto_atTop (by simp)
    | succ m =>
      simp only [Fin.val_succ, Multiseries.monomialRpow, List.getElem_cons_succ]
      apply (monomialRpow_approximates h_basis.tail).cons _ (by simp)
      apply h_basis.tail_pow_majorized_head (by simp)

@[simp]
theorem monomial_toFun {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (monomial basis n).toFun = basis[n] := by
  let n' : Fin basis.length := ⟨n, h⟩
  conv_lhs => rw [show n = n'.val by simp [n']]
  convert! monomialRpow_toFun
  simp
  grind

theorem monomial_toFun' {basis : Basis} {n : Fin basis.length} :
    (monomial basis n).toFun = basis[n] := by
  simp

@[simp]
theorem monomial_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    (monomial (basis_hd :: basis_tl) n).seq = Multiseries.monomial _ _ n :=
  monomialRpow_seq

theorem Multiseries.monomial_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    (@Multiseries.monomial basis_hd basis_tl n).Sorted :=
  Multiseries.monomialRpow_sorted

/-- `monomial` is well-ordered. -/
theorem monomial_sorted {basis : Basis} {n : ℕ} : (monomial basis n).Sorted :=
  monomialRpow_sorted

/-- `monomial` approximates the monomial function. -/
theorem monomial_approximates {basis : Basis} {n : Fin (List.length basis)}
    (h_basis : WellFormedBasis basis) : (monomial basis n).Approximates :=
  monomialRpow_approximates h_basis

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
