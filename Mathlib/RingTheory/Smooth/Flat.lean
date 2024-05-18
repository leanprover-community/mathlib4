/-
Copyright (c) 2022 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Descent
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RingOfDefinition
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.AlgebraCat.Limits
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

universe u v

open TensorProduct

namespace Algebra

namespace Smooth

section

variable {R : Type*} [CommRing R]
variable (I : Ideal R) (J : Ideal R) (h : I ≤ J)

def Ideal.Quotient.factorₐ : R ⧸ I →ₐ[R] R ⧸ J := by
  fapply AlgHom.mk
  · exact Ideal.Quotient.factor I J h
  · intro r
    simp

end

section

variable (A : Type*) [CommRing A]
variable (B : Type*) [CommRing B] [Algebra A B]
variable (C : Type*) [CommRing C] [Algebra A C]

-- the unique algebra map to the zero algebra
def AlgHom.toTrivialAlgebra (h : Subsingleton C) : B →ₐ[A] C where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by
    intro _ _
    simp
  map_zero' := by
    simp
    symm
    rwa [subsingleton_iff_zero_eq_one]
  map_add' := by
    simp
    symm
    rwa [subsingleton_iff_zero_eq_one]
  commutes' := by
    intro r
    simp
    apply eq_of_zero_eq_one
    rwa [subsingleton_iff_zero_eq_one]

@[simp]
lemma AlgHom.toTrivialAlgebra_apply_eq_one (h : Subsingleton C) (b : B) :
    AlgHom.toTrivialAlgebra A B C h b = 1 :=
  rfl

end

section

variable {A : Type u} [CommRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [FormallySmooth A B]
variable {k : ℕ}

local notation "R" => MvPolynomial (Fin k) A

variable (f : MvPolynomial (Fin k) A →ₐ[A] B) (hf : Function.Surjective f)

local notation "I" => RingHom.ker f

--noncomputable def transitionMap (n m : ℕ) (h : n ≤ m) : R ⧸ (I ^ m) →ₐ[A] R ⧸ (I ^ n) := by
--  apply Ideal.quotientMapₐ (I ^ n) (AlgHom.id A _)
--  change I ^ m ≤ I ^ n
--  apply Ideal.pow_le_pow_right
--  exact h

--@[simp]
--lemma transitionMap_mk (n m : ℕ) (h : n ≤ m) (p : R) :
--    (transitionMap f n m h) p = p := by
--  simp [transitionMap]
--
--@[simp]
--lemma transitionMap_id (n : ℕ) :
--    transitionMap f n n (by omega) = AlgHom.id A (R ⧸ (I ^ n)) := by
--  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A (I ^ n))
--  · apply Ideal.Quotient.mkₐ_surjective
--  · ext
--    simp
--
--@[simp]
--lemma transitionMap_comp (n m k : ℕ) (h1 : n ≤ m) (h2 : m ≤ k) :
--    AlgHom.comp (transitionMap f n m h1) (transitionMap f m k h2)  = transitionMap f n k (by omega) := by
--  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A _)
--  · apply Ideal.Quotient.mkₐ_surjective
--  · ext
--    simp

noncomputable def sectionAuxEquiv (m : ℕ) :
    ((R ⧸ I ^ (m + 1)) ⧸ (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1)))) ≃ₐ[A] R ⧸ (I ^ m) := by
  apply DoubleQuot.quotQuotEquivQuotOfLEₐ _
  apply Ideal.pow_le_pow_right
  exact Nat.le_succ m

@[simp]
lemma sectionAuxEquiv_mk (m : ℕ) (p : R) :
    sectionAuxEquiv f m p = p := by
  simp only [sectionAuxEquiv]
  change (DoubleQuot.quotQuotEquivQuotOfLEₐ A _) (DoubleQuot.quotQuotMk _ _ p) = p
  simp

lemma sectionAuxEquiv_comp (m : ℕ) :
    AlgHom.comp (sectionAuxEquiv f m).toAlgHom
      (Ideal.Quotient.mkₐ A <| (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1))))
    = AdicCompletion.transitionMap'ₐ A I (Nat.le_succ m) := by
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A (I ^ (m + 1)))
  · apply Ideal.Quotient.mkₐ_surjective
  · ext; simp

/-- Lift `B →ₐ[A] R ⧸ I` inductively to `B →ₐ[A] R ⧸ (I ^ m)` using formal smoothness.

Note that, since `B ≃ₐ[A] R ⧸ I ≃ₐ[A] R ⧸ (I ^ m) ⧸ (I ⧸ (I ^ m))`, we could also
lift this directly, but then we don't have compatibility with the canonical transition maps.
-/
noncomputable def sectionAux' : (m : ℕ) → B →ₐ[A] R ⧸ (I ^ (m + 1))
  | Nat.zero => by
      letI e : (R ⧸ I) ≃ₐ[A] R ⧸ (I ^ 1) := by
        apply Ideal.quotientEquivAlgOfEq A
        simp
      letI f' : (R ⧸ I) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
      exact (AlgEquiv.trans f'.symm e).toAlgHom
  | Nat.succ m => by
      letI T := R ⧸ (I ^ (m + 2))
      letI J : Ideal T := Ideal.map (Ideal.Quotient.mk (I ^ (m + 2))) (I ^ (m + 1))
      letI q : B →ₐ[A] T ⧸ J := AlgHom.comp (sectionAuxEquiv f (m + 1)).symm (sectionAux' m)
      refine FormallySmooth.lift J ⟨m + 2, ?_⟩ q
      rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
      refine eq_bot_mono (Ideal.map_mono ?_) (Ideal.map_quotient_self _)
      apply Ideal.pow_le_pow_right
      simp

@[simp]
theorem sectionAux'_zero (p : R) : (sectionAux' f hf 0) (f p) = p := by
  simp only [sectionAux']
  simp only [Nat.reduceAdd, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.trans_apply]
  change (Ideal.quotientEquivAlgOfEq A _)
    ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (Ideal.quotientKerAlgEquivOfSurjective hf p)) = p
  erw [RingEquiv.symm_apply_apply]
  rfl

lemma sectionAux'_comp_transitionMap (m : ℕ) :
    AlgHom.comp (AdicCompletion.transitionMap'ₐ A I (Nat.le_succ (m + 1))) (sectionAux' f hf (m + 1))
      = sectionAux' f hf m := by
  cases m <;> (
    simp only [sectionAux', ← sectionAuxEquiv_comp]
    ext
    simp
  )

/-- Extends `sectionAux` with the zero map in degree zero. -/
noncomputable def sectionAux : (m : ℕ) → B →ₐ[A] R ⧸ (I ^ m)
  | Nat.zero => by
      apply AlgHom.toTrivialAlgebra
      rw [Ideal.Quotient.subsingleton_iff]
      simp
  | Nat.succ m => sectionAux' f hf m

@[simp]
lemma sectionAux_comp_transitionMap (m : ℕ) :
    AlgHom.comp (AdicCompletion.transitionMap'ₐ A I (Nat.le_succ m)) (sectionAux f hf (m + 1))
      = sectionAux f hf m := by
  cases m with
  | zero =>
      ext b
      apply eq_of_zero_eq_one
      rw [subsingleton_iff_zero_eq_one, Ideal.Quotient.subsingleton_iff]
      simp
  | succ m => exact sectionAux'_comp_transitionMap f hf m

@[simp]
lemma sectionAux_comp_transitionMap_of_le {m n : ℕ} (hn : m ≤ n) :
    AlgHom.comp (AdicCompletion.transitionMap'ₐ A I hn) (sectionAux f hf n)
      = sectionAux f hf m := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [← AdicCompletion.transitionMap'ₐ_comp A I hmn (by omega), AlgHom.comp_assoc]
      simpa

/-- The constructed section from `B` to the `I`-adic completion of `R`. -/
noncomputable def section' : B →ₐ[A] AdicCompletion I R :=
  AdicCompletion.liftₐ A I (sectionAux f hf) (sectionAux_comp_transitionMap_of_le f hf)

@[simp]
theorem section'_apply (p : R) :
    AdicCompletion.evalₐ I 1 (section' f hf (f p)) = p := by
  simp [section']
  simp only [sectionAux]
  simp

--@[simp]

--@[simp]
--lemma section'_π_apply (m : ℕ) (b : B) :
--    limit.π (sectionDiag f) ⟨m⟩ (section' f hf b) = sectionAux f hf m b := by
--  simp only [section']
--  change (limit.lift (sectionDiag f) (sectionDiagCone f hf) ≫ limit.π (sectionDiag f) ⟨m⟩) b = sectionAux f hf m b
--  simp
--  rfl

set_option synthInstance.maxHeartbeats 50000

instance : IsScalarTower A R (AdicCompletion I R) :=
  IsScalarTower.of_compHom A R (AdicCompletion I R)

/-- The canonical projection from the `I`-adic completion of `R` to `B`. -/
noncomputable def proj : AdicCompletion I R →ₐ[A] B :=
  let p : AdicCompletion I R →ₐ[A] (R ⧸ (I ^ 1)) :=
    AlgHom.restrictScalars A (AdicCompletion.evalₐ I 1)
  let e : (R ⧸ (I ^ 1)) ≃ₐ[A] R ⧸ I := by
    apply Ideal.quotientEquivAlgOfEq A
    simp
  let f' : (R ⧸ I) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
  AlgHom.comp f' (AlgHom.comp e.toAlgHom p)

/-- The constructed section is indeed a section for `proj`. -/
theorem section'_isSection :
    AlgHom.comp (proj f hf) (section' f hf) = AlgHom.id A B := by
  --simp only [proj]
  apply AlgHom.cancel_surjective (Ideal.quotientKerAlgEquivOfSurjective hf).toAlgHom
    (EquivLike.surjective (Ideal.quotientKerAlgEquivOfSurjective hf))
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ_surjective _ _)
  ext i
  simp
  change (proj f hf) ((section' f hf) (f (MvPolynomial.X i))) = f (MvPolynomial.X i)
  simp [proj]
  rfl

variable [IsNoetherianRing A]

instance : Algebra.Flat R (AdicCompletion I R) := AdicCompletion.flat I

/-- The polynomial ring is flat -/
instance : Module.Flat A R := inferInstance

instance : Module.Flat A (AdicCompletion I R) :=
  Module.Flat.comp A R (AdicCompletion I R)

instance flat_of_map : Algebra.Flat A B := by
  constructor
  apply Module.Flat.of_retract A (AdicCompletion I R) B (section' f hf) (proj f hf)
  ext b
  simp only [LinearMap.coe_comp, Function.comp_apply]
  change (AlgHom.comp (proj f hf) (section' f hf)) b = (AlgHom.id A B) b
  rw [section'_isSection f hf]

end

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A]
variable (B : Type u) [CommRing B] [Algebra A B]

variable [Algebra.FiniteType A B] [Algebra.FormallySmooth A B]

instance flat_of_noetherian : Algebra.Flat A B := by
  obtain ⟨k, f, hf⟩ :=
    (FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  exact flat_of_map f hf

end

section

variable (A : Type u) [CommRing A]
variable (B : Type u) [CommRing B] [Algebra A B]

variable [Algebra.FinitePresentation A B] [Algebra.FormallySmooth A B]

instance flat : Algebra.Flat A B where
  out := by
    obtain ⟨A₀, B₀, _, _, f, hfin, hfp, hfs⟩ := descent (R := A) B inferInstance
    have : IsNoetherianRing A₀ := FiniteType.isNoetherianRing ℤ A₀
    have : Flat A₀ B₀ := inferInstance
    have : Flat A (A ⊗[A₀] B₀) := inferInstance
    apply Module.Flat.of_linearEquiv A (A ⊗[A₀] B₀) B
    exact f.toLinearEquiv

end
