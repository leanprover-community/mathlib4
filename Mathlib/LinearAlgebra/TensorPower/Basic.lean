/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Tensor power of a semimodule over a commutative semiring

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `Fin n` of `M`,
`⨂[R] (i : Fin n), M`. This is a special case of `PiTensorProduct`.

This file introduces the notation `⨂[R]^n M` for `TensorPower R n M`, which in turn is an
abbreviation for `⨂[R] i : Fin n, M`.

## Main definitions:

* `TensorPower.gsemiring`: the tensor powers form a graded semiring.
* `TensorPower.galgebra`: the tensor powers form a graded algebra.

## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `GradedMonoid` should be preferred.
-/

@[expose] public section

open scoped TensorProduct

/-- Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : Fin n), M`. -/
abbrev TensorPower (R : Type*) (n : ℕ) (M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] : Type _ :=
  ⨂[R] _ : Fin n, M

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

@[inherit_doc] scoped[TensorProduct] notation:max "⨂[" R "]^" n:arg => TensorPower R n

namespace PiTensorProduct

/-- Two dependent pairs of tensor products are equal if their index is equal and the contents
are equal after a canonical reindexing. -/
@[ext (iff := false)]
theorem gradedMonoid_eq_of_reindex_cast {ιι : Type*} {ι : ιι → Type*} :
    ∀ {a b : GradedMonoid fun ii => ⨂[R] _ : ι ii, M} (h : a.fst = b.fst),
      reindex R (fun _ ↦ M) (Equiv.cast <| congr_arg ι h) a.snd = b.snd → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩ => fun (hi : ai = bi) (h : reindex R (fun _ ↦ M) _ a = b) => by
    subst hi
    simp_all

end PiTensorProduct

namespace TensorPower

open scoped TensorProduct DirectSum

open PiTensorProduct

/-- As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`. -/
instance gOne : GradedMonoid.GOne fun i => ⨂[R]^i M where one := tprod R <| @Fin.elim0 M

local notation "ₜ1" => @GradedMonoid.GOne.one ℕ (fun i => ⨂[R]^i M) _ _

theorem gOne_def : ₜ1 = tprod R (@Fin.elim0 M) :=
  rfl

/-- A variant of `PiTensorProduct.tmulEquiv` with the result indexed by `Fin (n + m)`. -/
def mulEquiv {n m : ℕ} : ⨂[R]^n M ⊗[R] (⨂[R]^m) M ≃ₗ[R] (⨂[R]^(n + m)) M :=
  (tmulEquiv R M).trans (reindex R (fun _ ↦ M) finSumFinEquiv)

/-- As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M`. -/
instance gMul : GradedMonoid.GMul fun i => ⨂[R]^i M where
  mul {i j} a b :=
    (TensorProduct.mk R _ _).compr₂ (↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M)) a b

local infixl:70 " ₜ* " => @GradedMonoid.GMul.mul ℕ (fun i => ⨂[R]^i M) _ _ _ _

theorem gMul_def {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) :
    a ₜ* b = @mulEquiv R M _ _ _ i j (a ⊗ₜ b) :=
  rfl

theorem gMul_eq_coe_linearMap {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) :
    a ₜ* b = ((TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M) :
      ⨂[R]^i M →ₗ[R] (⨂[R]^j) M →ₗ[R] (⨂[R]^(i + j)) M) a b :=
  rfl

variable (R M)

/-- Cast between "equal" tensor powers. -/
def cast {i j} (h : i = j) : ⨂[R]^i M ≃ₗ[R] (⨂[R]^j) M := reindex R (fun _ ↦ M) (finCongr h)

theorem cast_tprod {i j} (h : i = j) (a : Fin i → M) :
    cast R M h (tprod R a) = tprod R (a ∘ Fin.cast h.symm) :=
  reindex_tprod _ _

@[simp]
theorem cast_refl {i} (h : i = i) : cast R M h = LinearEquiv.refl _ _ :=
  (congr_arg (reindex R fun _ ↦ M) <| finCongr_refl h).trans reindex_refl

@[simp]
theorem cast_symm {i j} (h : i = j) : (cast R M h).symm = cast R M h.symm :=
  reindex_symm _

@[simp]
theorem cast_trans {i j k} (h : i = j) (h' : j = k) :
    (cast R M h).trans (cast R M h') = cast R M (h.trans h') :=
  reindex_trans _ _

variable {R M}

@[simp]
theorem cast_cast {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M) :
    cast R M h' (cast R M h a) = cast R M (h.trans h') a :=
  reindex_reindex _ _ _

@[ext (iff := false)]
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h : a.fst = b.fst)
    (h2 : cast R M h a.snd = b.snd) : a = b := by
  refine gradedMonoid_eq_of_reindex_cast h ?_
  rw [cast] at h2
  rw [← finCongr_eq_equivCast, ← h2]

theorem cast_eq_cast {i j} (h : i = j) :
    ⇑(cast R M h) = _root_.cast (congrArg (fun i => ⨂[R]^i M) h) := by
  subst h
  rw [cast_refl]
  rfl

variable (R) in
theorem tprod_mul_tprod {na nb} (a : Fin na → M) (b : Fin nb → M) :
    tprod R a ₜ* tprod R b = tprod R (Fin.append a b) := by
  dsimp [gMul_def, mulEquiv]
  rw [tmulEquiv_apply R M a b]
  refine (reindex_tprod _ _).trans ?_
  congr 1
  dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
  apply funext
  apply Fin.addCases <;> simp

theorem one_mul {n} (a : ⨂[R]^n M) : cast R M (zero_add n) (ₜ1 ₜ* a) = a := by
  rw [gMul_def, gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [TensorProduct.tmul_smul, map_smul, map_smul, ← gMul_def, tprod_mul_tprod, cast_tprod]
    congr 2 with i
    rw [Fin.elim0_append]
    refine congr_arg a (Fin.ext ?_)
    simp
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

theorem mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a := by
  rw [gMul_def, gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, ← gMul_def, tprod_mul_tprod R a _,
      cast_tprod]
    simp
  | add x y hx hy =>
    rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]

theorem mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M) :
    cast R M (add_assoc _ _ _) (a ₜ* b ₜ* c) = a ₜ* (b ₜ* c) := by
  let mul : ∀ n m : ℕ, ⨂[R]^n M →ₗ[R] (⨂[R]^m) M →ₗ[R] (⨂[R]^(n + m)) M := fun n m =>
    (TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(n + m)) M)
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : (⨂[R]^(na + nb + nc)) M ≃ₗ[R] (⨂[R]^(na + (nb + nc))) M := cast R M (add_assoc _ _ _)
  let lhs : (⨂[R]^na) M →ₗ[R] (⨂[R]^nb) M →ₗ[R] (⨂[R]^nc) M →ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ ((mul _ nc).compr₂ e.toLinearMap)).comp (mul na nb)
  have lhs_eq : ∀ a b c, lhs a b c = e (a ₜ* b ₜ* c) := fun _ _ _ => rfl
  let rhs : (⨂[R]^na) M →ₗ[R] (⨂[R]^nb) M →ₗ[R] (⨂[R]^nc) M →ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ (LinearMap.lflip (R := R)).toLinearMap <|
        (LinearMap.llcomp R _ _ _ (mul na _).flip).comp (mul nb nc)).flip
  have rhs_eq : ∀ a b c, rhs a b c = a ₜ* (b ₜ* c) := fun _ _ _ => rfl
  suffices lhs = rhs from
    LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun this a) b) c
  ext a b c
  -- clean up
  simp only [e, LinearMap.compMultilinearMap_apply, lhs_eq, rhs_eq, tprod_mul_tprod, cast_tprod]
  congr 1 with j
  rw [Fin.append_assoc]
  refine congr_arg (Fin.append a (Fin.append b c)) (Fin.ext ?_)
  rw [Fin.val_cast, Fin.val_cast]

-- for now we just use the default for the `gnpow` field as it's easier.
instance gmonoid : GradedMonoid.GMonoid fun i => ⨂[R]^i M :=
  { TensorPower.gMul, TensorPower.gOne with
    one_mul := fun _ => gradedMonoid_eq_of_cast (zero_add _) (one_mul _)
    mul_one := fun _ => gradedMonoid_eq_of_cast (add_zero _) (mul_one _)
    mul_assoc := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _) }

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the `algebraMap` of the tensor
algebra. -/
def algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M :=
  LinearEquiv.symm <| isEmptyEquiv (Fin 0)

theorem algebraMap₀_eq_smul_one (r : R) : (algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1 := by
  simp [algebraMap₀]; congr

theorem algebraMap₀_one : (algebraMap₀ 1 : (⨂[R]^0) M) = ₜ1 :=
  (algebraMap₀_eq_smul_one 1).trans (one_smul _ _)

theorem algebraMap₀_mul {n} (r : R) (a : ⨂[R]^n M) :
    cast R M (zero_add _) (algebraMap₀ r ₜ* a) = r • a := by
  rw [gMul_eq_coe_linearMap, algebraMap₀_eq_smul_one, LinearMap.map_smul₂, map_smul,
    ← gMul_eq_coe_linearMap, one_mul]

theorem mul_algebraMap₀ {n} (r : R) (a : ⨂[R]^n M) :
    cast R M (add_zero _) (a ₜ* algebraMap₀ r) = r • a := by
  rw [gMul_eq_coe_linearMap, algebraMap₀_eq_smul_one, map_smul, map_smul, ← gMul_eq_coe_linearMap,
    mul_one]

theorem algebraMap₀_mul_algebraMap₀ (r s : R) :
    cast R M (add_zero _) (algebraMap₀ r ₜ* algebraMap₀ s) = algebraMap₀ (r * s) := by
  rw [← smul_eq_mul, map_smul]
  exact algebraMap₀_mul r (@algebraMap₀ R M _ _ _ s)

set_option backward.isDefEq.respectTransparency false in
instance gsemiring : DirectSum.GSemiring fun i => ⨂[R]^i M :=
  { TensorPower.gmonoid with
    mul_zero := fun _ => map_zero _
    zero_mul := fun _ => LinearMap.map_zero₂ _ _
    mul_add := fun _ _ _ => map_add _ _ _
    add_mul := fun _ _ _ => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => algebraMap₀ (n : R)
    natCast_zero := by simp only [Nat.cast_zero, map_zero]
    natCast_succ := fun n => by simp only [Nat.cast_succ, map_add, algebraMap₀_one] }

example : Semiring (⨁ n : ℕ, ⨂[R]^n M) := by infer_instance

/-- The tensor powers form a graded algebra.

Note that this instance implies `Algebra R (⨁ n : ℕ, ⨂[R]^n M)` via `DirectSum.Algebra`. -/
instance galgebra : DirectSum.GAlgebra R fun i => ⨂[R]^i M where
  toFun := (algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M).toLinearMap.toAddMonoidHom
  map_one := algebraMap₀_one
  map_mul r s := gradedMonoid_eq_of_cast rfl (by
    rw [← LinearEquiv.eq_symm_apply]
    have := algebraMap₀_mul_algebraMap₀ (M := M) r s
    exact this.symm)
  commutes r x := gradedMonoid_eq_of_cast (add_comm _ _) (by
    have := (algebraMap₀_mul r x.snd).trans (mul_algebraMap₀ r x.snd).symm
    rw [← LinearEquiv.eq_symm_apply, cast_symm]
    rw [← LinearEquiv.eq_symm_apply, cast_symm, cast_cast] at this
    exact this)
  smul_def r x := gradedMonoid_eq_of_cast (zero_add x.fst).symm (by
    rw [← LinearEquiv.eq_symm_apply, cast_symm]
    exact (algebraMap₀_mul r x.snd).symm)

theorem galgebra_toFun_def (r : R) :
    DirectSum.GAlgebra.toFun (A := fun i ↦ ⨂[R]^i M) r = algebraMap₀ r :=
  rfl

example : Algebra R (⨁ n : ℕ, ⨂[R]^n M) := by infer_instance

end TensorPower
