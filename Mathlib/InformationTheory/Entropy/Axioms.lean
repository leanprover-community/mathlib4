/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Entropy.Shannon

@[expose] public section


/-!
# Axiomatic Entropy Properties

This file defines seven axiom structures for entropy functions on finite
`NNReal`-valued distributions, following Rota's characterisation of
Shannon entropy up to a positive scalar.

## Main definitions

* `IsEntropyNormalized`: entropy of a single certain outcome is `0`.
* `IsEntropySymmetric`: entropy is invariant under relabelling.
* `IsEntropyContinuous`: entropy is continuous in the distribution.
* `IsEntropyZeroInvariant`: appending a zero-probability outcome does
  not change entropy.
* `IsEntropyZeroOnEmpty`: entropy on the empty type is `0`.
* `IsEntropyMaxUniform`: the uniform distribution maximises entropy.
* `IsEntropyCondAddSigma`: conditional-additivity over sigma types.
* `HasRotaEntropyAxioms`: the conjunction of all seven axioms.
* `dependentPairDistSigma`: joint distribution over a sigma type.
* `productDist`: product distribution for independent distributions.
* `entropyUniform`: `H(uniform_n)` for `n > 0`.
* `entropyUniform₀`: extension of `entropyUniform` setting `f(0) = 0`.

## Main results

* `uniformDist_fin_one` -- the uniform distribution on `Fin 1` is the constant `1`.
* `sum_fin_one_eq_one` -- the uniform distribution on `Fin 1` sums to `1`.
* `sum_ext_zero_eq_one` -- extending a distribution by a zero-probability outcome preserves its sum.

## Tags

entropy, axioms, rota, information theory
-/

open Finset Real

namespace InformationTheory

/-- Entropy of a single certain outcome is `0`. -/
structure IsEntropyNormalized
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  normalized : ∀ (p : Fin 1 → NNReal), (∑ i, p i = 1) → H_func p = 0

/-- Entropy is invariant under relabelling of outcomes. -/
structure IsEntropySymmetric
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  symmetry :
    ∀ {α β : Type} [Fintype α] [Fintype β]
      (p_target : β → NNReal) (_hp : ∑ y, p_target y = 1)
      (e : α ≃ β),
      H_func (α := α) (fun x : α => p_target (e x)) =
      H_func (α := β) p_target

/-- Entropy is continuous in the distribution. -/
structure IsEntropyContinuous
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  continuity :
    ∀ {α : Type} [Fintype α] (p_center : α → NNReal)
      (_hp_sum_1 : ∑ i, p_center i = 1) (ε : ℝ), ε > 0 →
      ∃ δ > 0, ∀ (q : α → NNReal) (_hq_sum_1 : ∑ i, q i = 1),
        (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) →
          |((H_func q) : ℝ) - ((H_func p_center) : ℝ)| < ε

/-- Appending a zero-probability outcome does not change entropy. -/
structure IsEntropyZeroInvariant
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  zero_invariance :
    ∀ {n : ℕ} (p_orig : Fin n → NNReal)
      (_hp_sum_1 : ∑ i, p_orig i = 1),
      let p_ext := (fun (i : Fin (n + 1)) =>
        if h_lt : i.val < n then p_orig (Fin.castLT i h_lt) else 0)
      H_func p_ext = H_func p_orig

/-- Entropy on the empty type is `0`. -/
structure IsEntropyZeroOnEmpty
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) :
    Prop where
  apply_to_empty_domain : H_func Fin.elim0 = 0

/-- The uniform distribution maximises entropy. -/
structure IsEntropyMaxUniform
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) :
    Prop where
  max_uniform :
    ∀ {α : Type} [Fintype α] (h_card_pos : 0 < Fintype.card α)
      (p : α → NNReal) (_hp_sum_1 : (∑ x, p x) = 1),
      H_func p ≤ H_func (uniformDist h_card_pos)

/--
Generalized joint distribution (dependent pair distribution) over a
sigma type. `P(⟨i,j⟩) = prior(i) * P_cond(i)(j)`. The type of `j`
depends on `i` via `M_map i`. -/
noncomputable def dependentPairDistSigma {N : ℕ}
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π (i : Fin N), (Fin (M_map i) → NNReal)) :
    (Σ i : Fin N, Fin (M_map i)) → NNReal :=
  fun sigma_pair =>
    let i := sigma_pair.fst
    let j := sigma_pair.snd
    prior i * P_cond i j

/-- Conditional additivity of entropy over sigma types:
`H(P_joint) = H(P_prior) + ∑_i P_prior(i) * H(P_conditional_i)`. -/
structure IsEntropyCondAddSigma
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) :
    Prop where
  cond_add_sigma :
    ∀ {N : ℕ} [NeZero N]
      (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
      (P_cond : Π (i : Fin N), (Fin (M_map i) → NNReal))
      (_hprior_sum_1 : ∑ i, prior i = 1)
      (_hP_cond_props :
        ∀ i : Fin N, prior i > 0 →
          (M_map i > 0 ∧ ∑ j, P_cond i j = 1))
      (_hH_P_cond_M_map_zero_is_zero :
        ∀ i : Fin N, M_map i = 0 →
          @H_func (Fin (M_map i)) (Fin.fintype (M_map i))
            (P_cond i) = 0),
    H_func (dependentPairDistSigma prior M_map P_cond) =
      H_func prior + ∑ i, prior i * H_func (P_cond i)

/--
**Axiomatic Entropy Function — 7-axiom Lean formalisation of Rota's
entropy properties.**

`HasRotaEntropyAxioms H_func` bundles the seven properties that
uniquely characterise entropy up to a positive scalar (Rota's Entropy
Theorem). -/
structure HasRotaEntropyAxioms
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) :
    Prop
  extends IsEntropyZeroInvariant H_func,
          IsEntropyNormalized H_func,
          IsEntropySymmetric H_func,
          IsEntropyContinuous H_func,
          IsEntropyCondAddSigma H_func,
          IsEntropyMaxUniform H_func,
          IsEntropyZeroOnEmpty H_func

/-- Product distribution `P((i,j)) = p(i) * q(j)` for independent
`p` and `q`. -/
noncomputable def productDist {n m : ℕ} (p : Fin n → NNReal)
    (q : Fin m → NNReal) : Fin (n * m) → NNReal :=
  fun k =>
    let k' : Fin (m * n) :=
      Equiv.cast (congrArg Fin (Nat.mul_comm n m)) k
    let ji := finProdFinEquiv.symm k'
    p ji.2 * q ji.1

/-- The uniform distribution on `Fin 1` is `fun _ => 1`. -/
lemma uniformDist_fin_one :
    uniformDist (by rw [Fintype.card_fin]; exact Nat.one_pos :
      0 < Fintype.card (Fin 1)) =
    (fun (_ : Fin 1) => 1) := by
  funext x
  simp only [uniformDist, Fintype.card_fin, Nat.cast_one, inv_one]

/-- The distribution `fun (_ : Fin 1) => 1` sums to `1`. -/
lemma sum_fin_one_eq_one :
    (∑ (_ : Fin 1), (1 : NNReal)) = 1 := by
  simp [Finset.sum_const]

/-- If `p_orig` sums to `1` on `Fin n`, the extension that appends a
zero at index `n` still sums to `1`. -/
lemma sum_ext_zero_eq_one
    {n : ℕ} (p_orig : Fin n → NNReal)
    (hp : ∑ i, p_orig i = 1) :
    (∑ i : Fin (n + 1),
      (if h : (i : ℕ) < n then p_orig (Fin.castLT i h)
        else 0)) = 1 := by
  set p_ext : Fin (n + 1) → NNReal :=
    fun i => if h : (i : ℕ) < n then p_orig (Fin.castLT i h)
      else 0
  have h_split :
      (∑ i, p_ext i) =
        (∑ i : Fin n, p_ext i.castSucc) +
          p_ext (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]
  have h_last : p_ext (Fin.last n) = 0 := by
    simp [p_ext]
  have h_cast :
      (∑ i : Fin n, p_ext i.castSucc) =
        ∑ i : Fin n, p_orig i := by
    apply Finset.sum_congr rfl
    intro i _
    have : ((i.castSucc : Fin (n + 1)) : ℕ) < n := by
      rw [Fin.castSucc]
      exact i.is_lt
    simp [p_ext, Fin.castLT_castSucc]
  simp [h_split, h_last, hp, p_ext]

/-- `entropyUniform H n = H(uniform distribution on n outcomes)` for
`n > 0`. -/
noncomputable def entropyUniform
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (_hH_axioms : HasRotaEntropyAxioms H_func) {n : ℕ}
    (hn_pos : n > 0) : NNReal :=
  let α_n := Fin n
  have h_card_pos : 0 < Fintype.card α_n := by
    rw [Fintype.card_fin]
    exact hn_pos
  H_func (uniformDist h_card_pos)

/-- Extension of `entropyUniform` to all `ℕ` by setting
`entropyUniform₀ H 0 = 0`. -/
noncomputable def entropyUniform₀
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func) (n : ℕ) :
    NNReal :=
  if hn_pos : n > 0 then entropyUniform hH_axioms hn_pos
  else 0

end InformationTheory
