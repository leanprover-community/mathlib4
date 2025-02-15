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
- `Submodule.mapQPow`: the linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
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

namespace Submodule

section

@[simp]
theorem mapQ_eq_factor [I.IsTwoSided] [J.IsTwoSided] (h : I ≤ J) (x : R ⧸ I) :
    mapQ I J LinearMap.id h x = factor I J h x := rfl

end

variable (I M)

/--
The linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.
-/
def mapQPow {m n : ℕ} (le : m ≤ n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) :=
  liftQ (I ^ n • ⊤ : Submodule R M) (mkQ (I ^ m • ⊤ : Submodule R M))
    ((ker_mkQ (I ^ m • ⊤ : Submodule R M)).symm ▸ (smul_mono_left (pow_le_pow_right le)))

@[simp]
theorem mapQPow_mk {m n : ℕ} (le : m ≤ n) (x : M) :
    mapQPow I M le (Quotient.mk x) = (Quotient.mk x : M ⧸ I ^ m • ⊤) :=
  rfl

@[simp]
theorem mapQPow_eq (n : ℕ) : mapQPow I M (Nat.le_refl n) = LinearMap.id := by
  ext
  simp

@[simp]
theorem mapQPow_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    mapQPow I M hmn ∘ₗ mapQPow I M hnk = mapQPow I M (hmn.trans hnk) := by
  ext
  simp

@[simp]
theorem mapQPow_comp_apply {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : M ⧸ (I ^ k • ⊤ : Submodule R M)) :
    mapQPow I M hmn (mapQPow I M hnk x) = mapQPow I M (hmn.trans hnk) x := by
  show (mapQPow I M hmn ∘ₗ mapQPow I M hnk) x = mapQPow I M (hmn.trans hnk) x
  simp

@[simp]
theorem mk_out_eq_mapQPow {m n : ℕ} (le : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    Quotient.mk x.out = mapQPow I M le x := by
  nth_rw 2 [← Quotient.out_eq x]
  rfl

lemma mapQPow_surjective {m n : ℕ} (le : m ≤ n): Function.Surjective (mapQPow I M le) := by
  intro x
  use Quotient.mk x.out
  exact Quotient.out_eq x

abbrev mapQPowSucc (n : ℕ) : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R]
    M ⧸ (I ^ n • ⊤ : Submodule R M) := mapQPow I M (Nat.le_succ n)

end Submodule

namespace Ideal

namespace Quotient

variable [I.IsTwoSided]

variable (I)

/--
The ring homomorphism from `R ⧸ I ^ m`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.
-/
def factorPow {m n : ℕ} (le : n ≤ m) : R ⧸ I ^ m →+* R ⧸ I ^ n :=
  factor _ _ (pow_le_pow_right le)

@[simp]
theorem factorPow_mk {m n : ℕ} (le : n ≤ m) (x : R) :
    factorPow I le (mk (I ^ m) x) = mk (I ^ n) x :=
  rfl

@[simp]
theorem factorPow_eq (n : ℕ) : factorPow I (Nat.le_refl n) = RingHom.id _ := by
  ext
  simp

@[simp]
theorem factorPow_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (factorPow I hmn).comp (factorPow I hnk) = factorPow I (hmn.trans hnk) := by
  ext
  simp

@[simp]
theorem factorPow_comp_apply {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : R ⧸ I ^ k) :
    factorPow I hmn (factorPow I hnk x) = factorPow I (hmn.trans hnk) x := by
  show ((factorPow I hmn).comp (factorPow I hnk)) x = factorPow I (hmn.trans hnk) x
  simp

@[simp]
theorem mk_out_eq_factorPow {m n : ℕ} (le : n ≤ m) (x : R ⧸ I ^ m) :
    mk (I ^ n) x.out = factorPow I le x := by
  nth_rw 2 [← Quotient.out_eq x]
  rfl

lemma factorPow_surjective {m n : ℕ} (le : n ≤ m): Function.Surjective (factorPow I le) :=
  factor_surjective (I ^ m) (I ^ n) (pow_le_pow_right le)

lemma factorPow_ker {m n : ℕ} (le : m ≤ n) : RingHom.ker (factorPow I le) =
    (I ^ m).map (Ideal.Quotient.mk (I ^ n)) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factorPow, RingHom.mem_ker, factor_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (I ^ n))
      Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [factorPow, ← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

abbrev factorPowSucc (n : ℕ) : R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n :=
  factorPow I (Nat.le_succ n)

end Quotient

end Ideal
