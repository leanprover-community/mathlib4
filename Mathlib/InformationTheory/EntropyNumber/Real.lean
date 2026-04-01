/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
import Mathlib.InformationTheory.EntropyNumber.Rat
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# EntropyReal: Information-Theoretic Reals

The reals viewed as Boolean-valued functions on `EntropyNat`, i.e. characteristic
functions `EntropyNat → Bool`. This gives a type `EntropyReal` with cardinality
`2 ^ ℵ₀ = 𝔠`, and we construct an equivalence `EntropyReal ≃ ℝ` via
cardinality arguments.

## Main definitions

* `EntropyReal` — the type `EntropyNat → Bool`.
* `entropyRealEquivFunNat` — the equivalence `EntropyReal ≃ (ℕ → Bool)`.
* `entropyRealEquivReal` — the equivalence `EntropyReal ≃ ℝ`.

## Main results

* `cardinal_entropyNat` — `#EntropyNat = ℵ₀`.
* `cardinal_entropyReal_eq_two_pow_aleph0` — `#EntropyReal = 2 ^ ℵ₀`.
* `cardinal_entropyReal` — `#EntropyReal = ℶ₁`.
-/

namespace InformationTheory

open Cardinal

/-- Emergent reals: the power set of `EntropyNat`, i.e. characteristic
functions `EntropyNat → Bool`. -/
abbrev EntropyReal := EntropyNat → Bool

/-- Transport along `entropyNatEquivNat`, giving
`(EntropyNat → Bool) ≃ (ℕ → Bool)`. -/
noncomputable def entropyRealEquivFunNat : EntropyReal ≃ (ℕ → Bool) :=
  Equiv.arrowCongr entropyNatEquivNat (Equiv.refl Bool)

/-- The cardinality of `EntropyNat` is `ℵ₀`. -/
lemma cardinal_entropyNat : Cardinal.mk EntropyNat = Cardinal.aleph0 :=
  Cardinal.mk_congr (entropyNatEquivNat.trans Equiv.ulift.{0,0}.symm)

/-- The cardinality of `EntropyReal` (functions from `EntropyNat` to `Bool`)
is `2 ^ ℵ₀`. -/
lemma cardinal_entropyReal_eq_two_pow_aleph0 :
    Cardinal.mk EntropyReal = 2 ^ Cardinal.aleph0 := by
  calc
    Cardinal.mk EntropyReal
      = Cardinal.mk (ℕ → Bool)             := Cardinal.mk_congr entropyRealEquivFunNat
    _ = Cardinal.mk Bool ^ Cardinal.mk ℕ   := by rw [Cardinal.power_def]
    _ = 2 ^ Cardinal.aleph0                := by aesop

/-- The emergent reals have exactly the same cardinality as `ℝ`
(the continuum). -/
noncomputable def entropyRealEquivReal : EntropyReal ≃ ℝ :=
  have h : mk EntropyReal = mk ℝ := by
    calc
      mk EntropyReal = 2 ^ aleph0 := cardinal_entropyReal_eq_two_pow_aleph0
      _           = #ℝ         := (Cardinal.mk_real).symm
  Classical.choice (Cardinal.eq.1 h)

/-- The cardinality of `EntropyReal` is `ℶ₁` (beth one). -/
lemma cardinal_entropyReal :
    Cardinal.mk EntropyReal = Cardinal.beth 1 := by
  rw [cardinal_entropyReal_eq_two_pow_aleph0]
  simp [Cardinal.beth_one]

end InformationTheory
