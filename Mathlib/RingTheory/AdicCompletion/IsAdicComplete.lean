
/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.AdicCompletion.Limit

/-!
# Universal property of I-adically complete rings and modules

- `IsAdicComplete.lift`: if `N` is `I`-adically complete, then a compatible family of
  linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤)` can be lifted to a unique linear map `M →ₗ[R] N`.
  Together with `mk_lift_apply` and `eq_lift`, it gives the universal property of being
  `I`-adically complete.
-/

namespace IsAdicComplete

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

open Submodule AdicCompletion

section lift

variable [IsAdicComplete I N]

variable {M}

/--
Universal property of `IsAdicComplete`.
The lift linear map `lift I f h : M →ₗ[R] N` of a sequence of compatible
linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    M →ₗ[R] N := (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]
theorem of_lift_apply (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (x : M) :
    of I N (lift I f h x) = AdicCompletion.lift I f h x := by
  simp [lift, ofLinearEquiv]

@[simp]
theorem of_comp_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    (of I N) ∘ₗ (lift I f h) = AdicCompletion.lift I f h := by
  ext1 x
  exact of_lift_apply I f h x

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `M →ₗ[R] N ⧸ (I ^ n • ⊤)` is `f n` .
-/
@[simp]
theorem mk_lift_apply {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) (x : M) :
    (Submodule.Quotient.mk (lift I f h x)) = f n x := by
  simp only [lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp


@[simp]
theorem mkQ_comp_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) :
    (mkQ (I ^ n • ⊤ : Submodule R N)) ∘ₗ (lift I f h) = f n := by
  ext
  exact mk_lift_apply I h n _

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
If `F : M →ₗ[R] N` makes the following diagram commutes
```
  N
  | \
 F|  \ f n
  |   \
  v    v
  M --> M ⧸ (I ^ a n • ⊤)
```
Then it is the map `IsAdicComplete.lift`.
-/
theorem eq_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) {F : M →ₗ[R] N}
    (hF : ∀ {m s}, Submodule.Quotient.mk (F s) = f m s) : F = lift I f h := by
  ext s
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simp [SModEq, hF, mk_lift_apply]

end lift

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ (a n) • ⊤ : Submodule R N))

variable {I M}
/--
Instead of providing all `M →ₗ[R] N ⧸ (I ^ n • ⊤)`, one can just provide
`M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)` for a strictly increasing sequence `a n` to recover all
`M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def extend (n : ℕ) :
    M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  (factorPow I N (ha.id_le n)) ∘ₗ f n

variable (hf : ∀ {m}, factorPow I N (ha.monotone m.le_succ) ∘ₗ (f (m + 1)) = f m)

include hf in
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq
    {m n : ℕ} (hle : m ≤ n) : factorPow I N (ha.monotone hle) ∘ₗ f n = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ m n hle
  · exact fun _ _ le ↦ smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in
theorem extend_eq (n : ℕ) : extend ha f (a n) = f n :=
  factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in
theorem factorPow_comp_extend {m n : ℕ} (hle : m ≤ n) :
    factorPow I N hle ∘ₗ extend ha f n = extend ha f m := by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

variable [IsAdicComplete I N]

variable (I)
/--
A variant of `IsAdicComplete.lift`. Only takes `f n : M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)`
from a strictly increasing sequence `a n`.
-/
def lift : M →ₗ[R] N :=
  IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)

theorem of_lift_apply (x : M) :
    of I N (lift I ha f hf x) =
    AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) x :=
  IsAdicComplete.of_lift_apply I (extend ha f) (factorPow_comp_extend ha f hf) x

theorem of_comp_lift :
    (of I N) ∘ₗ (lift I ha f hf) =
      AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) :=
  IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]
theorem mk_lift_apply {n : ℕ} (x : M) :
    (Submodule.Quotient.mk (lift I ha f hf x)) = f n x := by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp [extend_eq ha f hf]

@[simp]
theorem mkQ_comp_lift {n : ℕ} :
    mkQ (I ^ (a n) • ⊤ : Submodule R N) ∘ₗ (lift I ha f hf) = f n := by
  ext
  exact mk_lift_apply I ha f hf _

theorem eq_lift {F : M →ₗ[R] N}
    (hF : ∀ {m s}, Submodule.Quotient.mk (F s) = f m s) : F = lift I ha f hf := by
  ext s
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (smul_mono_left (Ideal.pow_le_pow_right (ha.id_le n)))
  simp [SModEq, hF, mk_lift_apply I ha f hf]

end StrictMono

end IsAdicComplete
