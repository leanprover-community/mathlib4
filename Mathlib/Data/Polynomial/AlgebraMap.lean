/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Data.Polynomial.Eval

#align_import data.polynomial.algebra_map from "leanprover-community/mathlib"@"e064a7bf82ad94c3c17b5128bbd860d1ec34874e"

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/


noncomputable section

open Finset

open BigOperators Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B' : Type*} {a b : R} {n : ℕ}

variable [CommSemiring A'] [Semiring B']

section CommSemiring

variable [CommSemiring R] {p q r : R[X]}

variable [Semiring A] [Algebra R A]

/-- Note that this instance also provides `Algebra R R[X]`. -/
instance algebraOfAlgebra : Algebra R A[X]
    where
  smul_def' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      -- ⊢ (r • p).toFinsupp = (↑C (↑(algebraMap R A) r) * p).toFinsupp
      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]
      -- ⊢ r • p.toFinsupp = AddMonoidAlgebra.single 0 (↑(algebraMap R A) r) * p.toFins …
      exact Algebra.smul_def' _ _
      -- 🎉 no goals
      -- ⊢ (↑C (↑(algebraMap R A) r) * p).toFinsupp = (p * ↑C (↑(algebraMap R A) r)).to …
  commutes' r p :=
      -- ⊢ AddMonoidAlgebra.single 0 (↑(algebraMap R A) r) * p.toFinsupp = p.toFinsupp  …
    toFinsupp_injective <| by
      -- 🎉 no goals
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert Algebra.commutes' r p.toFinsupp
  toRingHom := C.comp (algebraMap R A)
#align polynomial.algebra_of_algebra Polynomial.algebraOfAlgebra

theorem algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r) :=
  rfl
#align polynomial.algebra_map_apply Polynomial.algebraMap_apply

@[simp]
theorem toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMap R _ r :=
  show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    -- ⊢ AddMonoidAlgebra.single 0 (↑(algebraMap R A) r) = ↑(algebraMap R (AddMonoidA …
    rfl
    -- 🎉 no goals
#align polynomial.to_finsupp_algebra_map Polynomial.toFinsupp_algebraMap

theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r :=
  toFinsupp_injective (toFinsupp_algebraMap _).symm
#align polynomial.of_finsupp_algebra_map Polynomial.ofFinsupp_algebraMap

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r :=
  rfl
set_option linter.uppercaseLean3 false in
#align polynomial.C_eq_algebra_map Polynomial.C_eq_algebraMap

-- porting note: removed `variable` because of redundant binder update annotation

/-- Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext 1100]
theorem algHom_ext' [Algebra R A'] [Algebra R B'] {f g : A'[X] →ₐ[R] B'}
    (h₁ : f.comp (IsScalarTower.toAlgHom R A' A'[X]) = g.comp (IsScalarTower.toAlgHom R A' A'[X]))
    (h₂ : f X = g X) : f = g :=
  AlgHom.coe_ringHom_injective (Polynomial.ringHom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)
#align polynomial.alg_hom_ext' Polynomial.algHom_ext'

variable (R)

/-- Algebra isomorphism between `R[X]` and `AddMonoidAlgebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
def toFinsuppIsoAlg : R[X] ≃ₐ[R] AddMonoidAlgebra R ℕ :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp
      -- ⊢ (↑(algebraMap R R[X]) r).toFinsupp = AddMonoidAlgebra.single 0 r
      exact toFinsupp_algebraMap _ }
      -- 🎉 no goals
#align polynomial.to_finsupp_iso_alg Polynomial.toFinsuppIsoAlg

variable {R}

instance subalgebraNontrivial [Nontrivial A] : Nontrivial (Subalgebra R A[X]) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      -- ⊢ ∃ x, ¬(x ∈ ⊥ ↔ x ∈ ⊤)
      refine' ⟨X, _⟩
      -- ⊢ ¬(X ∈ ⊥ ↔ X ∈ ⊤)
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top,
        algebraMap_apply, not_forall]
      intro x
      -- ⊢ ¬↑C (↑(algebraMap R A) x) = X
      rw [ext_iff, not_forall]
      -- ⊢ ∃ x_1, ¬coeff (↑C (↑(algebraMap R A) x)) x_1 = coeff X x_1
      refine' ⟨1, _⟩
      -- ⊢ ¬coeff (↑C (↑(algebraMap R A) x)) 1 = coeff X 1
      simp [coeff_C]⟩⟩
      -- 🎉 no goals

@[simp]
theorem algHom_eval₂_algebraMap {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (p : R[X]) (f : A →ₐ[R] B) (a : A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f a) p := by
  simp only [eval₂_eq_sum, sum_def]
  -- ⊢ ↑f (∑ n in support p, ↑(algebraMap R A) (coeff p n) * a ^ n) = ∑ n in suppor …
  simp only [f.map_sum, f.map_mul, f.map_pow, eq_intCast, map_intCast, AlgHom.commutes]
  -- 🎉 no goals
#align polynomial.alg_hom_eval₂_algebra_map Polynomial.algHom_eval₂_algebraMap

@[simp]
theorem eval₂_algebraMap_X {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (p : R[X])
    (f : R[X] →ₐ[R] A) : eval₂ (algebraMap R A) (f X) p = f p := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  -- ⊢ eval₂ (algebraMap R A) (↑f X) p = ↑f (sum p fun n a => ↑C a * X ^ n)
  simp only [eval₂_eq_sum, sum_def]
  -- ⊢ ∑ n in support p, ↑(algebraMap R A) (coeff p n) * ↑f X ^ n = ↑f (∑ n in supp …
  simp only [f.map_sum, f.map_mul, f.map_pow, eq_intCast, map_intCast]
  -- ⊢ ∑ n in support p, ↑(algebraMap R A) (coeff p n) * ↑f X ^ n = ∑ x in support  …
  simp [Polynomial.C_eq_algebraMap]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.eval₂_algebra_map_X Polynomial.eval₂_algebraMap_X

-- these used to be about `algebraMap ℤ R`, but now the simp-normal form is `Int.castRingHom R`.
@[simp]
theorem ringHom_eval₂_cast_int_ringHom {R S : Type*} [Ring R] [Ring S] (p : ℤ[X]) (f : R →+* S)
    (r : R) : f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  algHom_eval₂_algebraMap p f.toIntAlgHom r
#align polynomial.ring_hom_eval₂_cast_int_ring_hom Polynomial.ringHom_eval₂_cast_int_ringHom

@[simp]
theorem eval₂_int_castRingHom_X {R : Type*} [Ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f X) p = f p :=
  eval₂_algebraMap_X p f.toIntAlgHom
set_option linter.uppercaseLean3 false in
#align polynomial.eval₂_int_cast_ring_hom_X Polynomial.eval₂_int_castRingHom_X

end CommSemiring

section aeval

variable [CommSemiring R] {p q : R[X]}

variable [Semiring A] [Algebra R A]

variable {B : Type*} [Semiring B] [Algebra R B]

variable (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
  { eval₂RingHom' (algebraMap R A) x fun _a => Algebra.commutes _ _ with
    commutes' := fun _r => eval₂_C _ _ }
#align polynomial.aeval Polynomial.aeval

-- porting note: removed `variable` due to redundant binder annotation update

@[simp]
theorem adjoin_X : Algebra.adjoin R ({X} : Set R[X]) = ⊤ := by
  refine' top_unique fun p _hp => _
  -- ⊢ p ∈ Algebra.adjoin R {X}
  set S := Algebra.adjoin R ({X} : Set R[X])
  -- ⊢ p ∈ S
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial, Sum]
  -- ⊢ (sum p fun n a => ↑(monomial n) a) ∈ S
                            -- ⊢ (sum p fun n a => a • X ^ n) ∈ Algebra.adjoin R {X}
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (Algebra.subset_adjoin rfl) _) _
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.adjoin_X Polynomial.adjoin_X

@[ext 1200]
theorem algHom_ext {f g : R[X] →ₐ[R] A} (h : f X = g X) : f = g :=
  AlgHom.ext_of_adjoin_eq_top adjoin_X fun _p hp => (Set.mem_singleton_iff.1 hp).symm ▸ h
#align polynomial.alg_hom_ext Polynomial.algHom_ext

theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=
  rfl
#align polynomial.aeval_def Polynomial.aeval_def

-- porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_zero : aeval x (0 : R[X]) = 0 :=
  AlgHom.map_zero (aeval x)
#align polynomial.aeval_zero Polynomial.aeval_zero

@[simp]
theorem aeval_X : aeval x (X : R[X]) = x :=
  eval₂_X _ x
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_X Polynomial.aeval_X

@[simp]
theorem aeval_C (r : R) : aeval x (C r) = algebraMap R A r :=
  eval₂_C _ x
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_C Polynomial.aeval_C

@[simp]
theorem aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = algebraMap _ _ r * x ^ n :=
  eval₂_monomial _ _
#align polynomial.aeval_monomial Polynomial.aeval_monomial

-- porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_X_pow {n : ℕ} : aeval x ((X : R[X]) ^ n) = x ^ n :=
  eval₂_X_pow _ _
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_X_pow Polynomial.aeval_X_pow

-- porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
  AlgHom.map_add _ _ _
#align polynomial.aeval_add Polynomial.aeval_add

-- porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_one : aeval x (1 : R[X]) = 1 :=
  AlgHom.map_one _
#align polynomial.aeval_one Polynomial.aeval_one

section deprecated
set_option linter.deprecated false

-- porting note: removed `@[simp]` because `simp` can prove this
@[deprecated]
theorem aeval_bit0 : aeval x (bit0 p) = bit0 (aeval x p) :=
  AlgHom.map_bit0 _ _
#align polynomial.aeval_bit0 Polynomial.aeval_bit0

-- porting note: removed `@[simp]` because `simp` can prove this
@[deprecated]
theorem aeval_bit1 : aeval x (bit1 p) = bit1 (aeval x p) :=
  AlgHom.map_bit1 _ _
#align polynomial.aeval_bit1 Polynomial.aeval_bit1

end deprecated

-- porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_nat_cast (n : ℕ) : aeval x (n : R[X]) = n :=
  map_natCast _ _
#align polynomial.aeval_nat_cast Polynomial.aeval_nat_cast

theorem aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
  AlgHom.map_mul _ _ _
#align polynomial.aeval_mul Polynomial.aeval_mul

theorem aeval_comp {A : Type*} [CommSemiring A] [Algebra R A] (x : A) :
    aeval x (p.comp q) = aeval (aeval x q) p :=
  eval₂_comp (algebraMap R A)
#align polynomial.aeval_comp Polynomial.aeval_comp

theorem aeval_algHom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
  algHom_ext <| by simp only [aeval_X, AlgHom.comp_apply]
                   -- 🎉 no goals
#align polynomial.aeval_alg_hom Polynomial.aeval_algHom

@[simp]
theorem aeval_X_left : aeval (X : R[X]) = AlgHom.id R R[X] :=
  algHom_ext <| aeval_X X
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_X_left Polynomial.aeval_X_left

theorem aeval_X_left_apply (p : R[X]) : aeval X p = p :=
  AlgHom.congr_fun (@aeval_X_left R _) p
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_X_left_apply Polynomial.aeval_X_left_apply

theorem eval_unique (φ : R[X] →ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ X) p := by
  rw [← aeval_def, aeval_algHom, aeval_X_left, AlgHom.comp_id]
  -- 🎉 no goals
#align polynomial.eval_unique Polynomial.eval_unique

theorem aeval_algHom_apply {F : Type*} [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) :
    aeval (f x) p = f (aeval x p) := by
  refine' Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => _)
    (by simp [AlgHomClass.commutes])
  rw [map_add, hp, hq, ← map_add, ← map_add]
  -- 🎉 no goals
#align polynomial.aeval_alg_hom_apply Polynomial.aeval_algHom_apply

theorem aeval_algEquiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
  aeval_algHom (f : A →ₐ[R] B) x
#align polynomial.aeval_alg_equiv Polynomial.aeval_algEquiv

theorem aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) :
    aeval (algebraMap R A x) p = algebraMap R A (p.eval x) :=
  aeval_algHom_apply (Algebra.ofId R A) x p
#align polynomial.aeval_algebra_map_apply_eq_algebra_map_eval Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval

@[simp]
theorem coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r :=
  rfl
#align polynomial.coe_aeval_eq_eval Polynomial.coe_aeval_eq_eval

@[simp]
theorem coe_aeval_eq_evalRingHom (x : R) :
    ((aeval x : R[X] →ₐ[R] R) : R[X] →+* R) = evalRingHom x :=
  rfl
#align polynomial.coe_aeval_eq_eval_ring_hom Polynomial.coe_aeval_eq_evalRingHom

@[simp]
theorem aeval_fn_apply {X : Type*} (g : R[X]) (f : X → R) (x : X) :
    ((aeval f) g) x = aeval (f x) g :=
  (aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm
#align polynomial.aeval_fn_apply Polynomial.aeval_fn_apply

@[norm_cast]
theorem aeval_subalgebra_coe (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s : Subalgebra R A)
    (f : s) : (aeval f g : A) = aeval (f : A) g :=
  (aeval_algHom_apply s.val f g).symm
#align polynomial.aeval_subalgebra_coe Polynomial.aeval_subalgebra_coe

theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p := by
  simp [coeff_zero_eq_eval_zero]
  -- 🎉 no goals
#align polynomial.coeff_zero_eq_aeval_zero Polynomial.coeff_zero_eq_aeval_zero

theorem coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval (0 : A) p := by
  simp [aeval_def]
  -- 🎉 no goals
#align polynomial.coeff_zero_eq_aeval_zero' Polynomial.coeff_zero_eq_aeval_zero'

theorem map_aeval_eq_aeval_map {S T U : Type*} [CommSemiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra T U] {φ : R →+* T} {ψ : S →+* U}
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) (p : R[X]) (a : S) :
    ψ (aeval a p) = aeval (ψ a) (p.map φ) := by
  conv_rhs => rw [aeval_def, ← eval_map]
  -- ⊢ ↑ψ (↑(aeval a) p) = eval (↑ψ a) (map (algebraMap T ((fun x => U) a)) (map φ  …
  rw [map_map, h, ← map_map, eval_map, eval₂_at_apply, aeval_def, eval_map]
  -- 🎉 no goals
#align polynomial.map_aeval_eq_aeval_map Polynomial.map_aeval_eq_aeval_map

theorem aeval_eq_zero_of_dvd_aeval_eq_zero [CommSemiring S] [CommSemiring T] [Algebra S T]
    {p q : S[X]} (h₁ : p ∣ q) {a : T} (h₂ : aeval a p = 0) : aeval a q = 0 := by
  rw [aeval_def, ← eval_map] at h₂ ⊢
  -- ⊢ eval a (map (algebraMap S T) q) = 0
  exact eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd (algebraMap S T) h₁) h₂
  -- 🎉 no goals
#align polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero

variable (R)

theorem _root_.Algebra.adjoin_singleton_eq_range_aeval (x : A) :
    Algebra.adjoin R {x} = (Polynomial.aeval x).range := by
  rw [← Algebra.map_top, ← adjoin_X, AlgHom.map_adjoin, Set.image_singleton, aeval_X]
  -- 🎉 no goals
#align algebra.adjoin_singleton_eq_range_aeval Algebra.adjoin_singleton_eq_range_aeval

variable {R}

section Semiring

variable [Semiring S] {f : R →+* S}

theorem aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) :
    aeval x p = ∑ i in Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  -- ⊢ ↑(aeval x) p = ∑ x_1 in range (natDegree p + 1), ↑(algebraMap R S) (coeff p  …
  exact eval₂_eq_sum_range (algebraMap R S) x
  -- 🎉 no goals
#align polynomial.aeval_eq_sum_range Polynomial.aeval_eq_sum_range

theorem aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    aeval x p = ∑ i in Finset.range n, p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  -- ⊢ ↑(aeval x) p = ∑ x_1 in range n, ↑(algebraMap R S) (coeff p x_1) * x ^ x_1
  exact eval₂_eq_sum_range' (algebraMap R S) hn x
  -- 🎉 no goals
#align polynomial.aeval_eq_sum_range' Polynomial.aeval_eq_sum_range'

theorem isRoot_of_eval₂_map_eq_zero (hf : Function.Injective f) {r : R} :
    eval₂ f (f r) p = 0 → p.IsRoot r := by
  intro h
  -- ⊢ IsRoot p r
  apply hf
  -- ⊢ ↑f (eval r p) = ↑f 0
  rw [← eval₂_hom, h, f.map_zero]
  -- 🎉 no goals
#align polynomial.is_root_of_eval₂_map_eq_zero Polynomial.isRoot_of_eval₂_map_eq_zero

theorem isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] {p : R[X]}
    (inj : Function.Injective (algebraMap R S)) {r : R} (hr : aeval (algebraMap R S r) p = 0) :
    p.IsRoot r :=
  isRoot_of_eval₂_map_eq_zero inj hr
#align polynomial.is_root_of_aeval_algebra_map_eq_zero Polynomial.isRoot_of_aeval_algebraMap_eq_zero

end Semiring

section CommSemiring

section aevalTower

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B']

/-- Version of `aeval` for defining algebra homs out of `R[X]` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A') (x : A') : R[X] →ₐ[S] A' :=
  { eval₂RingHom (↑f) x with commutes' := fun r => by simp [algebraMap_apply] }
                                                      -- 🎉 no goals
#align polynomial.aeval_tower Polynomial.aevalTower

variable (g : R →ₐ[S] A') (y : A')

@[simp]
theorem aevalTower_X : aevalTower g y X = y :=
  eval₂_X _ _
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_tower_X Polynomial.aevalTower_X

@[simp]
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_tower_C Polynomial.aevalTower_C

@[simp]
theorem aevalTower_comp_C : (aevalTower g y : R[X] →+* A').comp C = g :=
  RingHom.ext <| aevalTower_C _ _
set_option linter.uppercaseLean3 false in
#align polynomial.aeval_tower_comp_C Polynomial.aevalTower_comp_C

@[simp]
theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R R[X] x) = g x :=
  eval₂_C _ _
#align polynomial.aeval_tower_algebra_map Polynomial.aevalTower_algebraMap

@[simp]
theorem aevalTower_comp_algebraMap : (aevalTower g y : R[X] →+* A').comp (algebraMap R R[X]) = g :=
  aevalTower_comp_C _ _
#align polynomial.aeval_tower_comp_algebra_map Polynomial.aevalTower_comp_algebraMap

theorem aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x :=
  aevalTower_algebraMap _ _ _
#align polynomial.aeval_tower_to_alg_hom Polynomial.aevalTower_toAlgHom

@[simp]
theorem aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g :=
  AlgHom.coe_ringHom_injective <| aevalTower_comp_algebraMap _ _
#align polynomial.aeval_tower_comp_to_alg_hom Polynomial.aevalTower_comp_toAlgHom

@[simp]
theorem aevalTower_id : aevalTower (AlgHom.id S S) = aeval := by
  ext s
  -- ⊢ ↑(aevalTower (AlgHom.id S S) s) X = ↑(aeval s) X
  simp only [eval_X, aevalTower_X, coe_aeval_eq_eval]
  -- 🎉 no goals
#align polynomial.aeval_tower_id Polynomial.aevalTower_id

@[simp]
theorem aevalTower_ofId : aevalTower (Algebra.ofId S A') = aeval := by
  ext
  -- ⊢ ↑(aevalTower (Algebra.ofId S A') x✝) X = ↑(aeval x✝) X
  simp only [aeval_X, aevalTower_X]
  -- 🎉 no goals
#align polynomial.aeval_tower_of_id Polynomial.aevalTower_ofId

end aevalTower

end CommSemiring

section CommRing

variable [CommRing S] {f : R →+* S}

theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : ∀ (j) (_ : j ≠ i), p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by
  by_cases hi : i ∈ f.support
  -- ⊢ p ∣ coeff f i * z ^ i
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    -- ⊢ p ∣ coeff f i * z ^ i
    rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.not_mem_erase _ _)] at dvd_eval
    -- ⊢ p ∣ coeff f i * z ^ i
    refine' (dvd_add_left _).mp dvd_eval
    -- ⊢ p ∣ ∑ x in Finset.erase (support f) i, ↑(RingHom.id S) (coeff f x) * z ^ x
    apply Finset.dvd_sum
    -- ⊢ ∀ (x : ℕ), x ∈ Finset.erase (support f) i → p ∣ ↑(RingHom.id S) (coeff f x)  …
    intro j hj
    -- ⊢ p ∣ ↑(RingHom.id S) (coeff f j) * z ^ j
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
    -- 🎉 no goals
  · convert dvd_zero p
    -- ⊢ coeff f i * z ^ i = 0
    rw [not_mem_support_iff] at hi
    -- ⊢ coeff f i * z ^ i = 0
    simp [hi]
    -- 🎉 no goals
#align polynomial.dvd_term_of_dvd_eval_of_dvd_terms Polynomial.dvd_term_of_dvd_eval_of_dvd_terms

theorem dvd_term_of_isRoot_of_dvd_terms {r p : S} {f : S[X]} (i : ℕ) (hr : f.IsRoot r)
    (h : ∀ (j) (_ : j ≠ i), p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
  dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h
#align polynomial.dvd_term_of_is_root_of_dvd_terms Polynomial.dvd_term_of_isRoot_of_dvd_terms

end CommRing

end aeval

section Ring

variable [Ring R]

/-- The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
theorem eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (X - C r)).eval r = 0 := by
  simp only [eval, eval₂_eq_sum, RingHom.id_apply]
  -- ⊢ (sum (p * (X - ↑C r)) fun e a => a * r ^ e) = 0
  have bound :=
    calc
      (p * (X - C r)).natDegree ≤ p.natDegree + (X - C r).natDegree := natDegree_mul_le
      _ ≤ p.natDegree + 1 := (add_le_add_left (natDegree_X_sub_C_le _) _)
      _ < p.natDegree + 2 := lt_add_one _
  rw [sum_over_range' _ _ (p.natDegree + 2) bound]
  -- ⊢ ∑ a in range (natDegree p + 2), coeff (p * (X - ↑C r)) a * r ^ a = 0
  swap
  -- ⊢ ∀ (n : ℕ), 0 * r ^ n = 0
  · simp
    -- 🎉 no goals
  rw [sum_range_succ']
  -- ⊢ ∑ k in range (natDegree p + 1), coeff (p * (X - ↑C r)) (k + 1) * r ^ (k + 1) …
  conv_lhs =>
    congr
    arg 2
    simp [coeff_mul_X_sub_C, sub_mul, mul_assoc, ← pow_succ]
  rw [sum_range_sub']
  -- ⊢ coeff p 0 * r ^ (0 + 1) - coeff p (natDegree p + 1) * r ^ (natDegree p + 1 + …
  simp [coeff_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.eval_mul_X_sub_C Polynomial.eval_mul_X_sub_C

theorem not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - C r) :=
  fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R <| by erw [← eval_mul_X_sub_C, hgf, eval_one]
                                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.not_is_unit_X_sub_C Polynomial.not_isUnit_X_sub_C

end Ring

theorem aeval_endomorphism {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (v : M) (p : R[X]) : aeval f p v = p.sum fun n b => b • (f ^ n) v := by
  rw [aeval_def, eval₂_eq_sum]
  -- ⊢ ↑(sum p fun e a => ↑(algebraMap R (M →ₗ[R] M)) a * f ^ e) v = sum p fun n b  …
  exact (LinearMap.applyₗ v).map_sum
  -- 🎉 no goals
#align polynomial.aeval_endomorphism Polynomial.aeval_endomorphism

end Polynomial
