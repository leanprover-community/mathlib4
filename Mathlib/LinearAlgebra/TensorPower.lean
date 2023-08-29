/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Logic.Equiv.Fin
import Mathlib.Algebra.DirectSum.Algebra

#align_import linear_algebra.tensor_power from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

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


open scoped TensorProduct

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : Fin n), M`. -/
@[reducible]
def TensorPower (R : Type*) (n : ℕ) (M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] : Type _ :=
  ⨂[R] _ : Fin n, M
#align tensor_power TensorPower

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

scoped[TensorProduct] notation:100 "⨂[" R "]^" n:arg => TensorPower R n

namespace PiTensorProduct

/-- Two dependent pairs of tensor products are equal if their index is equal and the contents
are equal after a canonical reindexing. -/
@[ext]
theorem gradedMonoid_eq_of_reindex_cast {ιι : Type*} {ι : ιι → Type*} :
    ∀ {a b : GradedMonoid fun ii => ⨂[R] _ : ι ii, M} (h : a.fst = b.fst),
      reindex R M (Equiv.cast <| congr_arg ι h) a.snd = b.snd → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩ => fun (hi : ai = bi) (h : reindex R M _ a = b) => by
    subst hi
    -- ⊢ { fst := ai, snd := a } = { fst := ai, snd := b }
    simp_all
    -- 🎉 no goals
#align pi_tensor_product.graded_monoid_eq_of_reindex_cast PiTensorProduct.gradedMonoid_eq_of_reindex_cast

end PiTensorProduct

namespace TensorPower

open scoped TensorProduct DirectSum

open PiTensorProduct

/-- As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`. -/
instance gOne : GradedMonoid.GOne fun i => (⨂[R]^i) M where one := tprod R <| @Fin.elim0' M
#align tensor_power.ghas_one TensorPower.gOne

local notation "ₜ1" => @GradedMonoid.GOne.one ℕ (fun i => (⨂[R]^i) M) _ _

theorem gOne_def : ₜ1 = tprod R (@Fin.elim0' M) :=
  rfl
#align tensor_power.ghas_one_def TensorPower.gOne_def

/-- A variant of `PiTensorProduct.tmulEquiv` with the result indexed by `Fin (n + m)`. -/
def mulEquiv {n m : ℕ} : (⨂[R]^n) M ⊗[R] (⨂[R]^m) M ≃ₗ[R] (⨂[R]^(n + m)) M :=
  (tmulEquiv R M).trans (reindex R M finSumFinEquiv)
#align tensor_power.mul_equiv TensorPower.mulEquiv

/-- As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M`. -/
instance gMul : GradedMonoid.GMul fun i => (⨂[R]^i) M where
  mul {i j} a b :=
    (TensorProduct.mk R _ _).compr₂ (↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M)) a b
#align tensor_power.ghas_mul TensorPower.gMul

local infixl:70 " ₜ* " => @GradedMonoid.GMul.mul ℕ (fun i => (⨂[R]^i) M) _ _ _ _

theorem gMul_def {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) :
    a ₜ* b = @mulEquiv R M _ _ _ i j (a ⊗ₜ b) :=
  rfl
#align tensor_power.ghas_mul_def TensorPower.gMul_def

theorem gMul_eq_coe_linearMap {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) :
    a ₜ* b = ((TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M) :
      (⨂[R]^i) M →ₗ[R] (⨂[R]^j) M →ₗ[R] (⨂[R]^(i + j)) M) a b :=
  rfl
#align tensor_power.ghas_mul_eq_coe_linear_map TensorPower.gMul_eq_coe_linearMap

variable (R M)

/-- Cast between "equal" tensor powers. -/
def cast {i j} (h : i = j) : (⨂[R]^i) M ≃ₗ[R] (⨂[R]^j) M :=
  reindex R M (Fin.castIso h).toEquiv
#align tensor_power.cast TensorPower.cast

theorem cast_tprod {i j} (h : i = j) (a : Fin i → M) :
    cast R M h (tprod R a) = tprod R (a ∘ Fin.castIso h.symm) :=
  reindex_tprod _ _
#align tensor_power.cast_tprod TensorPower.cast_tprod

@[simp]
theorem cast_refl {i} (h : i = i) : cast R M h = LinearEquiv.refl _ _ :=
  ((congr_arg fun f => reindex R M (RelIso.toEquiv f)) <| Fin.castIso_refl h).trans reindex_refl
#align tensor_power.cast_refl TensorPower.cast_refl

@[simp]
theorem cast_symm {i j} (h : i = j) : (cast R M h).symm = cast R M h.symm :=
  reindex_symm _
#align tensor_power.cast_symm TensorPower.cast_symm

@[simp]
theorem cast_trans {i j k} (h : i = j) (h' : j = k) :
    (cast R M h).trans (cast R M h') = cast R M (h.trans h') :=
  reindex_trans _ _
#align tensor_power.cast_trans TensorPower.cast_trans

variable {R M}

@[simp]
theorem cast_cast {i j k} (h : i = j) (h' : j = k) (a : (⨂[R]^i) M) :
    cast R M h' (cast R M h a) = cast R M (h.trans h') a :=
  reindex_reindex _ _ _
#align tensor_power.cast_cast TensorPower.cast_cast

@[ext]
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h : a.fst = b.fst)
    (h2 : cast R M h a.snd = b.snd) : a = b := by
  refine' gradedMonoid_eq_of_reindex_cast h _
  -- ⊢ ↑(reindex R M (Equiv.cast (_ : Fin a.fst = Fin b.fst))) a.snd = b.snd
  rw [cast] at h2
  -- ⊢ ↑(reindex R M (Equiv.cast (_ : Fin a.fst = Fin b.fst))) a.snd = b.snd
  rw [← Fin.castIso_to_equiv, ← h2]
  -- 🎉 no goals
#align tensor_power.graded_monoid_eq_of_cast TensorPower.gradedMonoid_eq_of_cast

-- named to match `Fin.cast_eq_cast`, which is now `Fin.castIso_eq_cast`
theorem cast_eq_cast {i j} (h : i = j) :
    ⇑(cast R M h) = _root_.cast (congrArg (fun i => (⨂[R]^i) M) h) := by
  subst h
  -- ⊢ ↑(cast R M (_ : i = i)) = _root_.cast (_ : (⨂[R]^i) M = (⨂[R]^i) M)
  rw [cast_refl]
  -- ⊢ ↑(LinearEquiv.refl R ((⨂[R]^i) M)) = _root_.cast (_ : (⨂[R]^i) M = (⨂[R]^i) M)
  rfl
  -- 🎉 no goals
#align tensor_power.cast_eq_cast TensorPower.cast_eq_cast

variable (R)

theorem tprod_mul_tprod {na nb} (a : Fin na → M) (b : Fin nb → M) :
    tprod R a ₜ* tprod R b = tprod R (Fin.append a b) := by
  dsimp [gMul_def, mulEquiv]
  -- ⊢ ↑(reindex R M finSumFinEquiv) (↑(tmulEquiv R M) (↑(tprod R) a ⊗ₜ[R] ↑(tprod  …
  rw [tmulEquiv_apply R M a b]
  -- ⊢ ↑(reindex R M finSumFinEquiv) (⨂ₜ[R] (i : Fin na ⊕ Fin nb), Sum.elim a b i)  …
  refine' (reindex_tprod _ _).trans _
  -- ⊢ (⨂ₜ[R] (i : Fin (na + nb)), Sum.elim a b (↑finSumFinEquiv.symm i)) = ↑(tprod …
  congr 1
  -- ⊢ (fun i => Sum.elim a b (↑finSumFinEquiv.symm i)) = Fin.append a b
  dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
  -- ⊢ (fun i => Sum.elim a b (Fin.addCases Sum.inl Sum.inr i)) = Fin.addCases a b
  apply funext
  -- ⊢ ∀ (x : Fin (na + nb)), Sum.elim a b (Fin.addCases Sum.inl Sum.inr x) = Fin.a …
  apply Fin.addCases <;> simp
  -- ⊢ ∀ (i : Fin na), Sum.elim a b (Fin.addCases Sum.inl Sum.inr (Fin.castAdd nb i …
                         -- 🎉 no goals
                         -- 🎉 no goals
#align tensor_power.tprod_mul_tprod TensorPower.tprod_mul_tprod

variable {R}

theorem one_mul {n} (a : (⨂[R]^n) M) : cast R M (zero_add n) (ₜ1 ₜ* a) = a := by
  rw [gMul_def, gOne_def]
  -- ⊢ ↑(cast R M (_ : 0 + n = n)) (↑mulEquiv (↑(tprod R) Fin.elim0' ⊗ₜ[R] a)) = a
  induction' a using PiTensorProduct.induction_on with r a x y hx hy
  -- ⊢ ↑(cast R M (_ : 0 + n = n)) (↑mulEquiv (↑(tprod R) Fin.elim0' ⊗ₜ[R] (r • ↑(t …
  · rw [TensorProduct.tmul_smul, LinearEquiv.map_smul, LinearEquiv.map_smul, ← gMul_def,
      tprod_mul_tprod, cast_tprod]
    congr 2 with i
    -- ⊢ (Fin.append Fin.elim0' a ∘ ↑(Fin.castIso (_ : n = 0 + n))) i = a i
    rw [Fin.elim0'_append]
    -- ⊢ ((a ∘ ↑(Fin.castIso (_ : 0 + n = n))) ∘ ↑(Fin.castIso (_ : n = 0 + n))) i =  …
    refine' congr_arg a (Fin.ext _)
    -- ⊢ ↑(↑(Fin.castIso (_ : 0 + n = n)) (↑(Fin.castIso (_ : n = 0 + n)) i)) = ↑i
    simp
    -- 🎉 no goals
  · rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    -- 🎉 no goals
#align tensor_power.one_mul TensorPower.one_mul

theorem mul_one {n} (a : (⨂[R]^n) M) : cast R M (add_zero _) (a ₜ* ₜ1) = a := by
  rw [gMul_def, gOne_def]
  -- ⊢ ↑(cast R M (_ : n + 0 = n)) (↑mulEquiv (a ⊗ₜ[R] ↑(tprod R) Fin.elim0')) = a
  induction' a using PiTensorProduct.induction_on with r a x y hx hy
  -- ⊢ ↑(cast R M (_ : n + 0 = n)) (↑mulEquiv ((r • ↑(tprod R) a) ⊗ₜ[R] ↑(tprod R)  …
  · rw [← TensorProduct.smul_tmul', LinearEquiv.map_smul, LinearEquiv.map_smul, ← gMul_def,
      tprod_mul_tprod R a _, cast_tprod]
    congr 2 with i
    -- ⊢ (Fin.append a Fin.elim0' ∘ ↑(Fin.castIso (_ : n = n + 0))) i = a i
    rw [Fin.append_elim0']
    -- ⊢ ((a ∘ ↑(Fin.castIso (_ : n + 0 = n))) ∘ ↑(Fin.castIso (_ : n = n + 0))) i =  …
    refine' congr_arg a (Fin.ext _)
    -- ⊢ ↑(↑(Fin.castIso (_ : n + 0 = n)) (↑(Fin.castIso (_ : n = n + 0)) i)) = ↑i
    simp
    -- 🎉 no goals
  · rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    -- 🎉 no goals
#align tensor_power.mul_one TensorPower.mul_one

theorem mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M) :
    cast R M (add_assoc _ _ _) (a ₜ* b ₜ* c) = a ₜ* (b ₜ* c) := by
  let mul : ∀ n m : ℕ, (⨂[R]^n) M →ₗ[R] (⨂[R]^m) M →ₗ[R] (⨂[R]^(n + m)) M := fun n m =>
    (TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(n + m)) M)
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : (⨂[R]^(na + nb + nc)) M ≃ₗ[R] (⨂[R]^(na + (nb + nc))) M := cast R M (add_assoc _ _ _)
  -- ⊢ ↑(cast R M (_ : na + nb + nc = na + (nb + nc))) (GradedMonoid.GMul.mul (Grad …
  let lhs : (⨂[R]^na) M →ₗ[R] (⨂[R]^nb) M →ₗ[R] (⨂[R]^nc) M →ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ ((mul _ nc).compr₂ e.toLinearMap)).comp (mul na nb)
  have lhs_eq : ∀ a b c, lhs a b c = e (a ₜ* b ₜ* c) := fun _ _ _ => rfl
  -- ⊢ ↑(cast R M (_ : na + nb + nc = na + (nb + nc))) (GradedMonoid.GMul.mul (Grad …
  let rhs : (⨂[R]^na) M →ₗ[R] (⨂[R]^nb) M →ₗ[R] (⨂[R]^nc) M →ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ (LinearMap.lflip (R := R)) <|
        (LinearMap.llcomp R _ _ _ (mul na _).flip).comp (mul nb nc)).flip
  have rhs_eq : ∀ a b c, rhs a b c = a ₜ* (b ₜ* c) := fun _ _ _ => rfl
  -- ⊢ ↑(cast R M (_ : na + nb + nc = na + (nb + nc))) (GradedMonoid.GMul.mul (Grad …
  suffices : lhs = rhs
  -- ⊢ ↑(cast R M (_ : na + nb + nc = na + (nb + nc))) (GradedMonoid.GMul.mul (Grad …
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun this a) b) c
  -- ⊢ lhs = rhs
  ext a b c
  -- ⊢ ↑(LinearMap.compMultilinearMap (↑(LinearMap.compMultilinearMap (↑(LinearMap. …
  -- clean up
  simp only [LinearMap.compMultilinearMap_apply, lhs_eq, rhs_eq, tprod_mul_tprod, cast_tprod]
  -- ⊢ ↑(tprod R) (Fin.append (Fin.append a b) c ∘ ↑(Fin.castIso (_ : na + (nb + nc …
  congr with j
  -- ⊢ (Fin.append (Fin.append a b) c ∘ ↑(Fin.castIso (_ : na + (nb + nc) = na + nb …
  rw [Fin.append_assoc]
  -- ⊢ ((Fin.append a (Fin.append b c) ∘ ↑(Fin.castIso (_ : na + nb + nc = na + (nb …
  refine' congr_arg (Fin.append a (Fin.append b c)) (Fin.ext _)
  -- ⊢ ↑(↑(Fin.castIso (_ : na + nb + nc = na + (nb + nc))) (↑(Fin.castIso (_ : na  …
  rw [Fin.coe_castIso, Fin.coe_castIso]
  -- 🎉 no goals
#align tensor_power.mul_assoc TensorPower.mul_assoc

-- for now we just use the default for the `gnpow` field as it's easier.
instance gmonoid : GradedMonoid.GMonoid fun i => (⨂[R]^i) M :=
  { TensorPower.gMul, TensorPower.gOne with
    one_mul := fun a => gradedMonoid_eq_of_cast (zero_add _) (one_mul _)
    mul_one := fun a => gradedMonoid_eq_of_cast (add_zero _) (mul_one _)
    mul_assoc := fun a b c => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _) }
#align tensor_power.gmonoid TensorPower.gmonoid

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the `algebraMap` of the tensor
algebra. -/
def algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M :=
  LinearEquiv.symm <| isEmptyEquiv (Fin 0)
#align tensor_power.algebra_map₀ TensorPower.algebraMap₀

theorem algebraMap₀_eq_smul_one (r : R) : (algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1 := by
  simp [algebraMap₀]; congr
  -- ⊢ r • ↑(tprod R) isEmptyElim = r • GradedMonoid.GOne.one
                      -- 🎉 no goals
#align tensor_power.algebra_map₀_eq_smul_one TensorPower.algebraMap₀_eq_smul_one

theorem algebraMap₀_one : (algebraMap₀ 1 : (⨂[R]^0) M) = ₜ1 :=
  (algebraMap₀_eq_smul_one 1).trans (one_smul _ _)
#align tensor_power.algebra_map₀_one TensorPower.algebraMap₀_one

theorem algebraMap₀_mul {n} (r : R) (a : (⨂[R]^n) M) :
    cast R M (zero_add _) (algebraMap₀ r ₜ* a) = r • a := by
  rw [gMul_eq_coe_linearMap, algebraMap₀_eq_smul_one, LinearMap.map_smul₂,
    LinearEquiv.map_smul, ← gMul_eq_coe_linearMap, one_mul]
#align tensor_power.algebra_map₀_mul TensorPower.algebraMap₀_mul

theorem mul_algebraMap₀ {n} (r : R) (a : (⨂[R]^n) M) :
    cast R M (add_zero _) (a ₜ* algebraMap₀ r) = r • a := by
  rw [gMul_eq_coe_linearMap, algebraMap₀_eq_smul_one, LinearMap.map_smul,
    LinearEquiv.map_smul, ← gMul_eq_coe_linearMap, mul_one]
#align tensor_power.mul_algebra_map₀ TensorPower.mul_algebraMap₀

theorem algebraMap₀_mul_algebraMap₀ (r s : R) :
    cast R M (add_zero _) (algebraMap₀ r ₜ* algebraMap₀ s) = algebraMap₀ (r * s) := by
  rw [← smul_eq_mul, LinearEquiv.map_smul]
  -- ⊢ ↑(cast R M (_ : 0 + 0 = 0)) (GradedMonoid.GMul.mul (↑algebraMap₀ r) (↑algebr …
  exact algebraMap₀_mul r (@algebraMap₀ R M _ _ _ s)
  -- 🎉 no goals
#align tensor_power.algebra_map₀_mul_algebra_map₀ TensorPower.algebraMap₀_mul_algebraMap₀

set_option maxHeartbeats 250000 in
instance gsemiring : DirectSum.GSemiring fun i => (⨂[R]^i) M :=
  { TensorPower.gmonoid with
    mul_zero := fun a => LinearMap.map_zero _
    zero_mul := fun b => LinearMap.map_zero₂ _ _
    mul_add := fun a b₁ b₂ => LinearMap.map_add _ _ _
    add_mul := fun a₁ a₂ b => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => algebraMap₀ (n : R)
    natCast_zero := by simp only [Nat.cast_zero, map_zero]
                       -- 🎉 no goals
    natCast_succ := fun n => by simp only [Nat.cast_succ, map_add, algebraMap₀_one] }
                                -- 🎉 no goals
#align tensor_power.gsemiring TensorPower.gsemiring

example : Semiring (⨁ n : ℕ, (⨂[R]^n) M) := by infer_instance
                                               -- 🎉 no goals

/-- The tensor powers form a graded algebra.

Note that this instance implies `Algebra R (⨁ n : ℕ, ⨂[R]^n M)` via `DirectSum.Algebra`. -/
instance galgebra : DirectSum.GAlgebra R fun i => (⨂[R]^i) M where
  toFun := (algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M).toLinearMap.toAddMonoidHom
  map_one := algebraMap₀_one
  map_mul r s := gradedMonoid_eq_of_cast rfl (by
    rw [← LinearEquiv.eq_symm_apply]
    -- ⊢ (GradedMonoid.mk 0 (↑(LinearMap.toAddMonoidHom ↑algebraMap₀) (r * s))).snd = …
    have := algebraMap₀_mul_algebraMap₀ (M := M) r s
    -- ⊢ (GradedMonoid.mk 0 (↑(LinearMap.toAddMonoidHom ↑algebraMap₀) (r * s))).snd = …
    exact this.symm)
    -- 🎉 no goals
  commutes r x := gradedMonoid_eq_of_cast (add_comm _ _) (by
    have := (algebraMap₀_mul r x.snd).trans (mul_algebraMap₀ r x.snd).symm
    -- ⊢ ↑(cast R M (_ : (GradedMonoid.mk 0 (↑(LinearMap.toAddMonoidHom ↑algebraMap₀) …
    rw [← LinearEquiv.eq_symm_apply, cast_symm]
    -- ⊢ (GradedMonoid.mk 0 (↑(LinearMap.toAddMonoidHom ↑algebraMap₀) r) * x).snd = ↑ …
    rw [← LinearEquiv.eq_symm_apply, cast_symm, cast_cast] at this
    -- ⊢ (GradedMonoid.mk 0 (↑(LinearMap.toAddMonoidHom ↑algebraMap₀) r) * x).snd = ↑ …
    exact this)
    -- 🎉 no goals
  smul_def r x := gradedMonoid_eq_of_cast (zero_add x.fst).symm (by
    rw [← LinearEquiv.eq_symm_apply, cast_symm]
    -- ⊢ (GradedMonoid.mk x.fst (r • x.snd)).snd = ↑(cast R M (_ : ({ fst := 0, snd : …
    exact (algebraMap₀_mul r x.snd).symm)
    -- 🎉 no goals
#align tensor_power.galgebra TensorPower.galgebra

theorem galgebra_toFun_def (r : R) :
    @DirectSum.GAlgebra.toFun ℕ R (fun i => (⨂[R]^i) M) _ _ _ _ _ _ _ r = algebraMap₀ r :=
  rfl
#align tensor_power.galgebra_to_fun_def TensorPower.galgebra_toFun_def

example : Algebra R (⨁ n : ℕ, (⨂[R]^n) M) := by infer_instance
                                                -- 🎉 no goals

end TensorPower
