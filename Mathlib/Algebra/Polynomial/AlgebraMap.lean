/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/


noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section CommSemiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable {p q r : R[X]}

/-- Note that this instance also provides `Algebra R R[X]`. -/
instance algebraOfAlgebra : Algebra R A[X] where
  smul_def' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert Algebra.commutes' r p.toFinsupp
  toRingHom := C.comp (algebraMap R A)

@[simp]
theorem algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r) :=
  rfl

@[simp]
theorem toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMap R _ r :=
  show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    rfl

theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r :=
  toFinsupp_injective (toFinsupp_algebraMap _).symm

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r :=
  rfl

@[simp]
theorem algebraMap_eq : algebraMap R R[X] = C :=
  rfl

/-- `Polynomial.C` as an `AlgHom`. -/
@[simps! apply]
def CAlgHom : A →ₐ[R] A[X] where
  toRingHom := C
  commutes' _ := rfl

/-- Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext 1100]
theorem algHom_ext' {f g : A[X] →ₐ[R] B}
    (hC : f.comp CAlgHom = g.comp CAlgHom)
    (hX : f X = g X) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

variable (R)

open AddMonoidAlgebra in
/-- Algebra isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
def toFinsuppIsoAlg : R[X] ≃ₐ[R] R[ℕ] :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }

variable {R}

instance subalgebraNontrivial [Nontrivial A] : Nontrivial (Subalgebra R A[X]) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne, SetLike.ext_iff, not_forall]
      refine ⟨X, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top,
        algebraMap_apply, not_forall]
      intro x
      rw [ext_iff, not_forall]
      refine ⟨1, ?_⟩
      simp [coeff_C]⟩⟩

@[simp]
theorem algHom_eval₂_algebraMap {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (p : R[X]) (f : A →ₐ[R] B) (a : A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f a) p := by
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, eq_intCast, map_intCast, AlgHom.commutes]

@[simp]
theorem eval₂_algebraMap_X {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (p : R[X])
    (f : R[X] →ₐ[R] A) : eval₂ (algebraMap R A) (f X) p = f p := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, eq_intCast, map_intCast]
  simp [Polynomial.C_eq_algebraMap]

-- these used to be about `algebraMap ℤ R`, but now the simp-normal form is `Int.castRingHom R`.
@[simp]
theorem ringHom_eval₂_intCastRingHom {R S : Type*} [Ring R] [Ring S] (p : ℤ[X]) (f : R →+* S)
    (r : R) : f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  algHom_eval₂_algebraMap p f.toIntAlgHom r

@[deprecated (since := "2024-05-27")]
alias ringHom_eval₂_cast_int_ringHom := ringHom_eval₂_intCastRingHom

@[simp]
theorem eval₂_intCastRingHom_X {R : Type*} [Ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f X) p = f p :=
  eval₂_algebraMap_X p f.toIntAlgHom

@[deprecated (since := "2024-04-17")]
alias eval₂_int_castRingHom_X := eval₂_intCastRingHom_X

/-- `Polynomial.eval₂` as an `AlgHom` for noncommutative algebras.

This is `Polynomial.eval₂RingHom'` for `AlgHom`s. -/
@[simps!]
def eval₂AlgHom' (f : A →ₐ[R] B) (b : B) (hf : ∀ a, Commute (f a) b) : A[X] →ₐ[R] B where
  toRingHom := eval₂RingHom' f b hf
  commutes' _ := (eval₂_C _ _).trans (f.commutes _)

section Map

/-- `Polynomial.map` as an `AlgHom` for noncommutative algebras.

  This is the algebra version of `Polynomial.mapRingHom`. -/
def mapAlgHom (f : A →ₐ[R] B) : Polynomial A →ₐ[R] Polynomial B where
  toRingHom := mapRingHom f.toRingHom
  commutes' := by simp

@[simp]
theorem coe_mapAlgHom (f : A →ₐ[R] B) : ⇑(mapAlgHom f) = map f :=
  rfl

@[simp]
theorem mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A) :=
  AlgHom.ext fun _x => map_id

@[simp]
theorem mapAlgHom_coe_ringHom (f : A →ₐ[R] B) :
    ↑(mapAlgHom f : _ →ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[simp]
theorem mapAlgHom_comp (C : Type z) [Semiring C] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g) := by
  apply AlgHom.ext
  intro x
  simp [AlgHom.comp_algebraMap, map_map]
  congr

theorem mapAlgHom_eq_eval₂AlgHom'_CAlgHom (f : A →ₐ[R] B) : mapAlgHom f = eval₂AlgHom'
    (CAlgHom.comp f) X (fun a => (commute_X (C (f a))).symm) := by
  apply AlgHom.ext
  intro x
  congr

/-- If `A` and `B` are isomorphic as `R`-algebras, then so are their polynomial rings -/
def mapAlgEquiv (f : A ≃ₐ[R] B) : Polynomial A ≃ₐ[R] Polynomial B :=
  AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

@[simp]
theorem coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEquiv f) = map f :=
  rfl

@[simp]
theorem mapAlgEquiv_id : mapAlgEquiv (@AlgEquiv.refl R A _ _ _) = AlgEquiv.refl :=
  AlgEquiv.ext fun _x => map_id

@[simp]
theorem mapAlgEquiv_coe_ringHom (f : A ≃ₐ[R] B) :
    ↑(mapAlgEquiv f : _ ≃ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[simp]
theorem mapAlgEquiv_comp (C : Type z) [Semiring C] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (mapAlgEquiv f).trans (mapAlgEquiv g) = mapAlgEquiv (f.trans g) := by
  apply AlgEquiv.ext
  intro x
  simp [AlgEquiv.trans_apply, map_map]
  congr

end Map

end CommSemiring

section aeval

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
  eval₂AlgHom' (Algebra.ofId _ _) x (Algebra.commutes · _)

@[simp]
theorem adjoin_X : Algebra.adjoin R ({X} : Set R[X]) = ⊤ := by
  refine top_unique fun p _hp => ?_
  set S := Algebra.adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial, Sum]
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (Algebra.subset_adjoin rfl) _) _

@[ext 1200]
theorem algHom_ext {f g : R[X] →ₐ[R] B} (hX : f X = g X) :
    f = g :=
  algHom_ext' (Subsingleton.elim _ _) hX

theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=
  rfl

-- Porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_zero : aeval x (0 : R[X]) = 0 :=
  map_zero (aeval x)

@[simp]
theorem aeval_X : aeval x (X : R[X]) = x :=
  eval₂_X _ x

@[simp]
theorem aeval_C (r : R) : aeval x (C r) = algebraMap R A r :=
  eval₂_C _ x

@[simp]
theorem aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = algebraMap _ _ r * x ^ n :=
  eval₂_monomial _ _

-- Porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_X_pow {n : ℕ} : aeval x ((X : R[X]) ^ n) = x ^ n :=
  eval₂_X_pow _ _

-- Porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
  map_add _ _ _

-- Porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_one : aeval x (1 : R[X]) = 1 :=
  map_one _

-- Porting note: removed `@[simp]` because `simp` can prove this
theorem aeval_natCast (n : ℕ) : aeval x (n : R[X]) = n :=
  map_natCast _ _

@[deprecated (since := "2024-04-17")]
alias aeval_nat_cast := aeval_natCast

theorem aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
  map_mul _ _ _

theorem comp_eq_aeval : p.comp q = aeval q p := rfl

theorem aeval_comp {A : Type*} [Semiring A] [Algebra R A] (x : A) :
    aeval x (p.comp q) = aeval (aeval x q) p :=
  eval₂_comp' x p q

/-- Two polynomials `p` and `q` such that `p(q(X))=X` and `q(p(X))=X`
  induces an automorphism of the polynomial algebra. -/
@[simps!]
def algEquivOfCompEqX (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) : R[X] ≃ₐ[R] R[X] := by
  refine AlgEquiv.ofAlgHom (aeval p) (aeval q) ?_ ?_ <;>
    exact AlgHom.ext fun _ ↦ by simp [← comp_eq_aeval, comp_assoc, hpq, hqp]

/-- The automorphism of the polynomial algebra given by `p(X) ↦ p(X+t)`,
  with inverse `p(X) ↦ p(X-t)`. -/
@[simps!]
def algEquivAevalXAddC {R} [CommRing R] (t : R) : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (X + C t) (X - C t) (by simp) (by simp)

theorem aeval_algHom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
  algHom_ext <| by simp only [aeval_X, AlgHom.comp_apply]

@[simp]
theorem aeval_X_left : aeval (X : R[X]) = AlgHom.id R R[X] :=
  algHom_ext <| aeval_X X

theorem aeval_X_left_apply (p : R[X]) : aeval X p = p :=
  AlgHom.congr_fun (@aeval_X_left R _) p

theorem eval_unique (φ : R[X] →ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ X) p := by
  rw [← aeval_def, aeval_algHom, aeval_X_left, AlgHom.comp_id]

theorem aeval_algHom_apply {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (x : A) (p : R[X]) :
    aeval (f x) p = f (aeval x p) := by
  refine Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => ?_)
    (by simp [AlgHomClass.commutes])
  rw [map_add, hp, hq, ← map_add, ← map_add]

@[simp]
lemma coe_aeval_mk_apply {S : Subalgebra R A} (h : x ∈ S) :
    (aeval (⟨x, h⟩ : S) p : A) = aeval x p :=
  (aeval_algHom_apply S.val (⟨x, h⟩ : S) p).symm

theorem aeval_algEquiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
  aeval_algHom (f : A →ₐ[R] B) x

theorem aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) :
    aeval (algebraMap R A x) p = algebraMap R A (p.eval x) :=
  aeval_algHom_apply (Algebra.ofId R A) x p

@[simp]
theorem coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r :=
  rfl

@[simp]
theorem coe_aeval_eq_evalRingHom (x : R) :
    ((aeval x : R[X] →ₐ[R] R) : R[X] →+* R) = evalRingHom x :=
  rfl

@[simp]
theorem aeval_fn_apply {X : Type*} (g : R[X]) (f : X → R) (x : X) :
    ((aeval f) g) x = aeval (f x) g :=
  (aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm

@[norm_cast]
theorem aeval_subalgebra_coe (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s : Subalgebra R A)
    (f : s) : (aeval f g : A) = aeval (f : A) g :=
  (aeval_algHom_apply s.val f g).symm

theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p := by
  simp [coeff_zero_eq_eval_zero]

theorem coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval (0 : A) p := by
  simp [aeval_def]

theorem map_aeval_eq_aeval_map {S T U : Type*} [Semiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra T U] {φ : R →+* T} {ψ : S →+* U}
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) (p : R[X]) (a : S) :
    ψ (aeval a p) = aeval (ψ a) (p.map φ) := by
  conv_rhs => rw [aeval_def, ← eval_map]
  rw [map_map, h, ← map_map, eval_map, eval₂_at_apply, aeval_def, eval_map]

theorem aeval_eq_zero_of_dvd_aeval_eq_zero [CommSemiring S] [CommSemiring T] [Algebra S T]
    {p q : S[X]} (h₁ : p ∣ q) {a : T} (h₂ : aeval a p = 0) : aeval a q = 0 := by
  rw [aeval_def, ← eval_map] at h₂ ⊢
  exact eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd (algebraMap S T) h₁) h₂

variable (R)

theorem _root_.Algebra.adjoin_singleton_eq_range_aeval (x : A) :
    Algebra.adjoin R {x} = (Polynomial.aeval x).range := by
  rw [← Algebra.map_top, ← adjoin_X, AlgHom.map_adjoin, Set.image_singleton, aeval_X]

@[simp]
theorem aeval_mem_adjoin_singleton :
    aeval x p ∈ Algebra.adjoin R {x} := by
  simpa only [Algebra.adjoin_singleton_eq_range_aeval] using Set.mem_range_self p

instance instCommSemiringAdjoinSingleton :
    CommSemiring <| Algebra.adjoin R {x} :=
  { mul_comm := fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ by
      obtain ⟨p', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hp
      obtain ⟨q', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MulMemClass.mk_mul_mk, ← map_mul,
        mul_comm p' q'] }

instance instCommRingAdjoinSingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) :
    CommRing <| Algebra.adjoin R {x} :=
  { mul_comm := mul_comm }

variable {R}

section Semiring

variable [Semiring S] {f : R →+* S}

theorem aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) :
    aeval x p = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x

theorem aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    aeval x p = ∑ i ∈ Finset.range n, p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x

theorem isRoot_of_eval₂_map_eq_zero (hf : Function.Injective f) {r : R} :
    eval₂ f (f r) p = 0 → p.IsRoot r := by
  intro h
  apply hf
  rw [← eval₂_hom, h, f.map_zero]

theorem isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] {p : R[X]}
    (inj : Function.Injective (algebraMap R S)) {r : R} (hr : aeval (algebraMap R S r) p = 0) :
    p.IsRoot r :=
  isRoot_of_eval₂_map_eq_zero inj hr

end Semiring

section CommSemiring

section aevalTower

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `R[X]` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A') (x : A') : R[X] →ₐ[S] A' :=
  eval₂AlgHom' f x fun _ => Commute.all _ _

variable (g : R →ₐ[S] A') (y : A')

@[simp]
theorem aevalTower_X : aevalTower g y X = y :=
  eval₂_X _ _

@[simp]
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _

@[simp]
theorem aevalTower_comp_C : (aevalTower g y : R[X] →+* A').comp C = g :=
  RingHom.ext <| aevalTower_C _ _

theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R R[X] x) = g x :=
  eval₂_C _ _

theorem aevalTower_comp_algebraMap : (aevalTower g y : R[X] →+* A').comp (algebraMap R R[X]) = g :=
  aevalTower_comp_C _ _

theorem aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
theorem aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g :=
  AlgHom.coe_ringHom_injective <| aevalTower_comp_algebraMap _ _

@[simp]
theorem aevalTower_id : aevalTower (AlgHom.id S S) = aeval := by
  ext s
  simp only [eval_X, aevalTower_X, coe_aeval_eq_eval]

@[simp]
theorem aevalTower_ofId : aevalTower (Algebra.ofId S A') = aeval := by
  ext
  simp only [aeval_X, aevalTower_X]

end aevalTower

end CommSemiring

section CommRing

variable [CommRing S] {f : R →+* S}

theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : ∀ j ≠ i, p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by
  by_cases hi : i ∈ f.support
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.not_mem_erase _ _)] at dvd_eval
    refine (dvd_add_left ?_).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
  · convert dvd_zero p
    rw [not_mem_support_iff] at hi
    simp [hi]

theorem dvd_term_of_isRoot_of_dvd_terms {r p : S} {f : S[X]} (i : ℕ) (hr : f.IsRoot r)
    (h : ∀ j ≠ i, p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
  dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

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
  have bound :=
    calc
      (p * (X - C r)).natDegree ≤ p.natDegree + (X - C r).natDegree := natDegree_mul_le
      _ ≤ p.natDegree + 1 := add_le_add_left (natDegree_X_sub_C_le _) _
      _ < p.natDegree + 2 := lt_add_one _
  rw [sum_over_range' _ _ (p.natDegree + 2) bound]
  swap
  · simp
  rw [sum_range_succ']
  conv_lhs =>
    congr
    arg 2
    simp [coeff_mul_X_sub_C, sub_mul, mul_assoc, ← pow_succ']
  rw [sum_range_sub']
  simp [coeff_monomial]

theorem not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - C r) :=
  fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R <| by erw [← eval_mul_X_sub_C, hgf, eval_one]

end Ring

theorem aeval_endomorphism {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (v : M) (p : R[X]) : aeval f p v = p.sum fun n b => b • (f ^ n) v := by
  rw [aeval_def, eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _

section StableSubmodule

variable {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {q : Submodule R M} {m : M}

lemma aeval_apply_smul_mem_of_le_comap'
    [Semiring A] [Algebra R A] [Module A M] [IsScalarTower R A M] (hm : m ∈ q) (p : R[X]) (a : A)
    (hq : q ≤ q.comap (Algebra.lsmul R R M a)) :
    aeval a p • m ∈ q := by
  refine p.induction_on (M := fun f ↦ aeval a f • m ∈ q) (by simpa) (fun f₁ f₂ h₁ h₂ ↦ ?_)
    (fun n t hmq ↦ ?_)
  · simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  · dsimp only at hmq ⊢
    rw [pow_succ', mul_left_comm, map_mul, aeval_X, mul_smul]
    rw [← q.map_le_iff_le_comap] at hq
    exact hq ⟨_, hmq, rfl⟩

lemma aeval_apply_smul_mem_of_le_comap
    (hm : m ∈ q) (p : R[X]) (f : Module.End R M) (hq : q ≤ q.comap f) :
    aeval f p m ∈ q :=
  aeval_apply_smul_mem_of_le_comap' hm p f hq

end StableSubmodule

end Polynomial
