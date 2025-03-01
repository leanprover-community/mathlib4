/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jiedong Jiang
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

/-!
# The quotient map from `R ⧸ I ^ m` to `R ⧸ I ^ n` where `m ≥ n`
In this file we define the canonical quotient linear map from
`M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` and canonical quotient ring map from
`R ⧸ I ^ m` to `R ⧸ I ^ n`. These definitions will be used in theorems
related to `IsAdicComplete` to find a lift element from compatible sequences in the quotients.
We also include results about the relation between quotients of submodules and quotients of
ideals here.
## Main definitions
- `Submodule.factorPow`: the linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.
- `Ideal.Quotient.factorPow`: the ring homomorphism from `R ⧸ I ^ m`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.
## Main results
-/

--Since `Mathlib.LinearAlgebra.Quotient.Basic` and `Mathlib.RingTheory.Ideal.Quotient.Defs`
--do not import each other, and the first file that imports both of them is
--`Mathlib.RingTheory.Ideal.Quotient.Operations`,  which has already established
--the first isomophism theorem and Chinese remainder theorem, we put these pure technical lemmas
--that involves both `Submodule.mapQ` and `Ideal.Quotient.factor` in this file.

open Submodule Ideal Quotient

variable {R : Type*} [Ring R] {I J : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]

lemma Ideal.Quotient.factor_ker (H : I ≤ J) [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (factor H) = J.map (Ideal.Quotient.mk I) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factor, RingHom.mem_ker, lift_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases mem_image_of_mem_map_of_surjective _ Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

lemma Submodule.eq_factor_of_eq_factor_succ {p : ℕ → Submodule R M}
    (hp : Antitone p) (x : (n : ℕ) → M ⧸ (p n)) (h : ∀ m, x m = factor (hp m.le_succ) (x (m + 1)))
    (m n : ℕ) (g : m ≤ n) : x m = factor (hp g) (x n) := by
  induction' hmn : n - m with k ih generalizing m n <;>
  have : n = m + (n - m) := (Nat.add_sub_of_le g).symm
  · rw [hmn, Nat.add_zero] at this
    subst this
    simp
  · rw [hmn, ← add_assoc] at this
    subst this
    rw [ih m (m + k) (m.le_add_right k) (by simp), h]
    simp

lemma Ideal.Quotient.eq_factor_of_eq_factor_succ {I : ℕ → Ideal R} [∀ n, (I n).IsTwoSided]
    (hI : Antitone I) (x : (n : ℕ) → R ⧸ (I n)) (h : ∀ m, x m = factor (hI m.le_succ) (x (m + 1)))
    (m n : ℕ) (g : m ≤ n) : x m = factor (hI g) (x n) :=
  Submodule.eq_factor_of_eq_factor_succ hI x h m n g

namespace Submodule

section

@[simp]
theorem mapQ_eq_factor (h : I ≤ J) (x : R ⧸ I) :
    mapQ I J LinearMap.id h x = factor h x := rfl

@[simp]
theorem factor_eq_factor [I.IsTwoSided] [J.IsTwoSided] (h : I ≤ J) (x : R ⧸ I) :
    Submodule.factor h x = Ideal.Quotient.factor h x := rfl

end

variable (I M)

lemma pow_smul_top_le {m n : ℕ} (h : m ≤ n) : (I ^ n • ⊤ : Submodule R M) ≤ I ^ m • ⊤ :=
  smul_mono_left (Ideal.pow_le_pow_right h)

/--
The linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.

To future contributors: Before adding lemmas related to `Submodule.factorPow`, please
check whether it can be generalized to `Submodule.factor` and whether the
corresponding (more general) lemma for `Submodule.factor` already exists.
-/
abbrev factorPow {m n : ℕ} (le : m ≤ n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) :=
  factor (smul_mono_left (Ideal.pow_le_pow_right le))

/-- `factorPow` for `n = m + 1` -/
abbrev factorPowSucc (m : ℕ) : M ⧸ (I ^ (m + 1) • ⊤ : Submodule R M) →ₗ[R]
    M ⧸ (I ^ m • ⊤ : Submodule R M) := factorPow I M (Nat.le_succ m)

end Submodule

namespace Ideal

namespace Quotient

variable [I.IsTwoSided]

variable (I)

/--
The ring homomorphism from `R ⧸ I ^ m`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.

To future contributors: Before adding lemmas related to `Ideal.factorPow`, please
check whether it can be generalized to `Ideal.factor` and whether the corresponding
(more general) lemma for `Ideal.factor` already exists.
-/
abbrev factorPow {m n : ℕ} (le : n ≤ m) : R ⧸ I ^ m →+* R ⧸ I ^ n :=
  factor (pow_le_pow_right le)

/-- `factorPow` for `m = n + 1` -/
abbrev factorPowSucc (n : ℕ) : R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n :=
  factorPow I (Nat.le_succ n)

end Quotient

end Ideal
