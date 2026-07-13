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

namespace Mathlib.Tactic.ComputeAsymptotics

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

section BasisOperations

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.updateBasis`. -/
def Multiseries.updateBasis {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ex : BasisExtension basis_tl)
    (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd ex.getBasis :=
  ms.map id (updateBasis ex ·)

/-- Given a basis extension `ex`, and a multiseries `ms`, immerses `ms` into the
basis `ex.getBasis`. -/
def updateBasis {basis : Basis} (ex : BasisExtension basis) (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion ex.getBasis :=
  match ex with
  | .nil => ms
  | .keep basis_hd ex_tl => mk (ms.seq.updateBasis ex_tl) ms.toFun
  | .insert _ ex_tl => mk (.cons 0 (ms.updateBasis ex_tl) .nil) ms.toFun

end

/-- Extends basis with `f` in the middle. -/
def extendBasisMiddle {left right : Basis} (f : ℝ → ℝ) (ms : MultiseriesExpansion (left ++ right)) :
    MultiseriesExpansion (left ++ f :: right) :=
  match left with
  | [] => mk (.cons 0 ms .nil) ms.toFun
  | List.cons _ _ => mk (ms.seq.map id (fun coef => extendBasisMiddle f coef)) ms.toFun

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.extendBasisEnd`. -/
def Multiseries.extendBasisEnd {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd (basis_tl ++ [f]) :=
  ms.map id (extendBasisEnd f ·)

/-- Extends basis with `f` at right end. -/
-- TODO: it's just extendMiddle with right = [].
def extendBasisEnd {basis : Basis} (f : ℝ → ℝ) (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion (basis ++ [f]) :=
  match basis with
  | [] => const [f] ms.toReal
  | List.cons _ _ => mk (ms.seq.extendBasisEnd f) ms.toFun

end

@[simp]
lemma Multiseries.map_leadingExp {basis_hd basis_hd' basis_tl basis_tl'}
    {ms : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    {g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl'} :
    (ms.map (basis_hd' := basis_hd') f g).leadingExp = ms.leadingExp.map f := by
  cases ms <;> simp

lemma Multiseries.map_id_sorted {basis_hd basis_hd' basis_tl basis_tl'}
    {f : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl'}
    {ms : Multiseries basis_hd basis_tl}
    (h_sorted : ms.Sorted)
    (hf : ∀ coef, coef.Sorted → (f coef).Sorted) :
    (ms.map (basis_hd' := basis_hd') id f).Sorted := by
  let motive (ms : Multiseries basis_hd' basis_tl') : Prop :=
    ∃ (ms' : Multiseries basis_hd basis_tl), ms = ms'.map id f ∧ ms'.Sorted
  apply Multiseries.Sorted.coind motive
  · use ms
  intro exp coef tl ⟨ms, h_eq, h_sorted⟩
  cases ms with
  | nil => simp at h_eq
  | cons exp' coef' tl' =>
  simp at h_eq
  obtain ⟨h_coef, h_comp, h_tl⟩ := h_sorted.elim_cons
  simp [h_eq, h_comp, motive]
  grind

lemma map_id_approximates {basis_hd basis_tl basis_tl'}
    {f : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl'}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (h_approx : ms.Approximates)
    (hf_approx : ∀ coef, coef.Approximates → (f coef).Approximates)
    (hf_toFun : ∀ coef, (f coef).toFun = coef.toFun) :
    (mk (ms.seq.map (basis_hd' := basis_hd) id f) ms.toFun).Approximates := by
  let motive (ms' : MultiseriesExpansion (basis_hd :: basis_tl')) : Prop :=
    ∃ (ms : MultiseriesExpansion (basis_hd :: basis_tl)),
      ms' = mk (ms.seq.map (basis_hd' := basis_hd) id f) ms.toFun ∧ ms.Approximates
  apply Approximates.coind motive
  · use ms
  rintro _ ⟨ms, rfl, h_approx⟩
  cases ms with
  | nil f => simpa using h_approx
  | cons exp coef tl g =>
  right
  obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
  simp only [mk_seq, Multiseries.map_cons, id_eq, mk_toFun, Multiseries.cons_eq_cons, ms_eq_mk_iff,
    ↓existsAndEq, and_true, hf_approx _ h_coef, hf_toFun, true_and, exists_eq_left', h_maj, motive]
  use mk tl (g - basis_hd ^ exp * coef.toFun)
  simp [h_tl]

@[simp]
theorem updateBasis_keep_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ex : BasisExtension basis_tl}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    (ms.updateBasis (.keep _ ex)).seq = ms.seq.updateBasis ex := by
  simp [MultiseriesExpansion.updateBasis]

@[simp]
theorem updateBasis_insert_seq {basis : Basis} {ex : BasisExtension basis}
    {ms : MultiseriesExpansion basis} {f : ℝ → ℝ} :
    (ms.updateBasis (.insert f ex)).seq = Multiseries.cons 0 (ms.updateBasis ex) .nil := by
  simp [MultiseriesExpansion.updateBasis]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem updateBasis_toFun {basis : Basis} {ex : BasisExtension basis}
    {ms : MultiseriesExpansion basis} :
    (ms.updateBasis ex).toFun = ms.toFun := by
  fun_cases updateBasis <;> simp [updateBasis]

theorem Multiseries.updateBasis_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ex : BasisExtension basis_tl} :
    (Multiseries.updateBasis (basis_hd := basis_hd) ex (.nil)) = .nil := by
  simp [Multiseries.updateBasis]

theorem Multiseries.updateBasis_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ex : BasisExtension basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (Multiseries.updateBasis ex (.cons exp coef tl)) =
    .cons exp (coef.updateBasis ex) (tl.updateBasis ex) := by
  simp [Multiseries.updateBasis]

set_option backward.isDefEq.respectTransparency false in
mutual

theorem Multiseries.updateBasis_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ex : BasisExtension basis_tl) {ms : Multiseries basis_hd basis_tl} (h_sorted : ms.Sorted) :
    (ms.updateBasis ex).Sorted := by
  simp only [Multiseries.updateBasis]
  apply Multiseries.map_id_sorted h_sorted
  apply updateBasis_sorted

theorem updateBasis_sorted {basis : Basis} {ex : BasisExtension basis}
    {ms : MultiseriesExpansion basis}
    (h_sorted : ms.Sorted) :
    (ms.updateBasis ex).Sorted := by
  cases ex with
  | nil => simpa [updateBasis]
  | insert f ex_tl =>
    simp only [updateBasis]
    apply Sorted.cons_nil
    exact updateBasis_sorted h_sorted
  | @keep basis_hd basis_tl ex_tl =>
    simp only [sorted_iff_seq_sorted, updateBasis, mk_seq] at h_sorted ⊢
    apply Multiseries.updateBasis_sorted ex_tl h_sorted

end

set_option backward.isDefEq.respectTransparency false in
theorem updateBasis_approximates {basis : Basis} {ex : BasisExtension basis}
    {ms : MultiseriesExpansion basis}
    (h_basis : WellFormedBasis ex.getBasis)
    (h_approx : ms.Approximates) :
    (ms.updateBasis ex).Approximates := by
  cases ex with
  | nil => simp
  | keep basis_hd ex_tl =>
    simp only [updateBasis, Multiseries.updateBasis]
    apply map_id_approximates h_approx
    · intro coef h_coef
      apply updateBasis_approximates h_basis.tail h_coef
    · simp
  | insert g ex_tl =>
    simp only [updateBasis]
    apply Approximates.cons
    · apply updateBasis_approximates _ h_approx
      exact BasisExtension.insert_tail_wellFormedBasis h_basis
    · simp only [BasisExtension.getBasis] at h_basis
      apply h_approx.coef_majorized_head
      apply WellFormedBasis.of_sublist _ h_basis
      simp only [List.cons_sublist_cons]
      apply BasisExtension.sublist_getBasis
    · apply Approximates.nil
      simp

@[simp]
theorem extendBasisMiddle_toFun {left right : Basis} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion (left ++ right)} :
    (ms.extendBasisMiddle b).toFun = ms.toFun := by
  fun_cases extendBasisMiddle <;> rfl

theorem extendBasisMiddle_sorted {left right : Basis} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion (left ++ right)}
    (h_sorted : ms.Sorted) : (ms.extendBasisMiddle b).Sorted := by
  cases left with
  | nil =>
    simp only [List.nil_append, extendBasisMiddle]
    apply Sorted.cons_nil
    assumption
  | cons left_hd left_tl =>
  simp only [List.cons_append, extendBasisMiddle, List.append_eq, sorted_iff_seq_sorted,
    mk_seq]
  apply Multiseries.map_id_sorted
  · simpa using h_sorted
  · apply extendBasisMiddle_sorted

theorem extendBasisMiddle_approximates {left right : Basis} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion (left ++ right)}
    (h_basis : WellFormedBasis (left ++ b :: right))
    (h_approx : ms.Approximates) :
    (ms.extendBasisMiddle b).Approximates := by
  cases left with
  | nil =>
    simp only [List.nil_append, extendBasisMiddle]
    apply Approximates.cons h_approx
    · exact h_approx.coef_majorized_head h_basis
    · apply Approximates.nil
      simp
  | cons left_hd left_tl =>
  simp only [List.cons_append, extendBasisMiddle, List.append_eq]
  apply map_id_approximates h_approx
  · intro coef h_coef
    apply extendBasisMiddle_approximates h_basis.tail h_coef
  · simp

@[simp]
theorem extendBasisEnd_toFun {basis : Basis} {b : ℝ → ℝ} {ms : MultiseriesExpansion basis} :
    (ms.extendBasisEnd b).toFun = ms.toFun := by
  cases basis with
  | nil => simp [extendBasisEnd, toReal]
  | cons => simp [extendBasisEnd]

@[simp]
theorem extendBasisEnd_seq {basis_hd basis_tl} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    (ms.extendBasisEnd b).seq = Multiseries.extendBasisEnd b ms.seq := by
  simp [extendBasisEnd]

theorem Multiseries.extendBasisEnd_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} :
    (Multiseries.extendBasisEnd (basis_hd := basis_hd) (basis_tl := basis_tl) f (.nil)) = .nil := by
  simp [Multiseries.extendBasisEnd]

theorem Multiseries.extendBasisEnd_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (Multiseries.extendBasisEnd f (.cons exp coef tl)) =
    .cons exp (coef.extendBasisEnd f) (tl.extendBasisEnd f) := by
  simp [Multiseries.extendBasisEnd]

mutual

theorem Multiseries.extendBasisEnd_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {ms : Multiseries basis_hd basis_tl} (h_sorted : ms.Sorted) :
    (ms.extendBasisEnd f).Sorted := by
  simp only [Multiseries.extendBasisEnd]
  apply Multiseries.map_id_sorted h_sorted
  apply extendBasisEnd_sorted

theorem extendBasisEnd_sorted {basis : Basis} {b : ℝ → ℝ} {ms : MultiseriesExpansion basis}
    (h_sorted : ms.Sorted) : (ms.extendBasisEnd b).Sorted := by
  cases basis with
  | nil =>
    simp only [extendBasisEnd]
    exact const_sorted
  | cons basis_hd basis_tl =>
    simp only [sorted_iff_seq_sorted, List.cons_append, List.append_eq,
      extendBasisEnd_seq] at *
    exact Multiseries.extendBasisEnd_sorted h_sorted

end

theorem extendBasisEnd_approximates {basis : Basis} {b : ℝ → ℝ} {ms : MultiseriesExpansion basis}
    (h_basis : WellFormedBasis (basis ++ [b]))
    (h_approx : ms.Approximates) :
    (ms.extendBasisEnd b).Approximates := by
  cases basis with
  | nil =>
    simp only [List.nil_append, extendBasisEnd]
    apply const_approximates h_basis
  | cons basis_hd basis_tl =>
  simp only [List.cons_append, extendBasisEnd, Multiseries.extendBasisEnd, List.append_eq]
  apply map_id_approximates h_approx
  · intro coef h_coef
    apply extendBasisEnd_approximates h_basis.tail h_coef
  · simp

end BasisOperations

end MultiseriesExpansion

end Mathlib.Tactic.ComputeAsymptotics
