/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.ContinuousMap.Star

/-!
# Constructions relating multivariate polynomial functions and continuous functions.

## Main definitions

* `MvPolynomial.toContinuousMapOn p X`: for `X : Set (σ → R)`, interprets a multivariate polynomial
  `p` as a bundled continuous function in `C(X, R)`.
* `MvPolynomial.toContinuousMapOnAlgHom`: the same, as an `R`-algebra homomorphism.
* `mvPolynomialFunctions (X : Set (σ → R)) : Subalgebra R C(X, R)`: multivariate polynomial
  functions as a subalgebra.
* `mvPolynomialFunctions_separatesPoints (X : Set (σ → R)) :
  (mvPolynomialFunctions X).SeparatesPoints`:
  the multivariate polynomial functions separate points.

-/

variable {σ : Type*} {R : Type*}

open MvPolynomial

namespace MvPolynomial

section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/--
Every multivariate polynomial with coefficients in a topological semiring gives a (bundled)
continuous function.
-/
@[simps]
def toContinuousMap (p : MvPolynomial σ R) : C(σ → R, R) :=
  ⟨fun x => p.eval x, by continuity⟩

lemma toContinuousMap_X_eq_eval (n : σ) : (X n).toContinuousMap = .eval (X := fun _ => R) n := by
  ext; simp

/--
A multivariate polynomial as a continuous function, with domain restricted to some subset of
`σ → R`.
-/
@[simps]
def toContinuousMapOn (p : MvPolynomial σ R) (X : Set (σ → R)) : C(X, R) :=
  ⟨fun x => p.toContinuousMap x, by fun_prop⟩

lemma toContinuousMapOn_X_eq_restrict_eval (s : Set (σ → R)) (n : σ) : (X n).toContinuousMapOn s
    = ContinuousMap.restrict s (.eval (X := (fun _ => R)) n) := by
  ext; simp

end

section

variable {α : Type*} [TopologicalSpace α] [CommSemiring R] [TopologicalSpace R]
  [TopologicalSemiring R]

@[simp]
theorem aeval_continuousMap_apply (g : MvPolynomial σ R) (f : σ → C(α, R)) (x : α) :
    ((MvPolynomial.aeval f) g) x = g.eval (fun i => f i x) := by
  refine MvPolynomial.induction_on' g ?_ ?_
  · intro u a
    rw [eval_monomial, aeval_monomial]
    unfold Finsupp.prod
    simp [ContinuousMap.prod_apply]
  · intro p q hp hq
    simp [hp, hq]

end

noncomputable section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/-- The algebra map from `MvPolynomial σ R` to continuous functions `C(σ → R, R)`.
-/
@[simps]
def toContinuousMapAlgHom : MvPolynomial σ R →ₐ[R] C(σ → R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  commutes' _ := by ext; simp

/-- The algebra map from `MvPolynomial σ R` to continuous functions `C(X, R)`, for any subset `X` of
  `σ → R`.
-/
@[simps]
def toContinuousMapOnAlgHom (X : Set (σ → R)): MvPolynomial σ R →ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  commutes' _ := by ext; simp

end

end MvPolynomial

section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/--
The subalgebra of multivariate polynomial functions in `C(X, R)`, for `X` a subset of `σ → R`.
-/
noncomputable def mvPolynomialFunctions (X : Set (σ → R)) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R (MvPolynomial σ R)).map (MvPolynomial.toContinuousMapOnAlgHom X)

@[simp]
theorem mvPolynomialFunctions_coe (X : Set (σ → R)) :
    (mvPolynomialFunctions X) = Set.range (MvPolynomial.toContinuousMapOnAlgHom X) := by
  ext
  simp [mvPolynomialFunctions]

theorem mvPolynomialFunctions_separatesPoints (X : Set (σ → R)) :
    (mvPolynomialFunctions X).SeparatesPoints := by
  intro x y h
  obtain ⟨s, hs⟩ := Classical.exists_not_of_not_forall
    (not_imp_not.mpr funext_iff.mpr (Subtype.coe_ne_coe.mpr h))
  exact ⟨_, ⟨_, ⟨MvPolynomial.X s, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩, by simp [hs]⟩

theorem mvPolynomialFunctions.eq_adjoin_X (s : Set (σ → R)) :
    mvPolynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s (X i) | i : σ} := by
  refine le_antisymm ?_ (Algebra.adjoin_le fun _ ⟨i, h⟩ => ⟨X i, trivial, h⟩)
  rintro - ⟨p, -, rfl⟩
  rw [AlgHom.coe_toRingHom]
  induction' p using induction_on with r f g hf hg f n hf
  · simp only [toContinuousMapOnAlgHom_apply, algHom_C]
    exact Subalgebra.algebraMap_mem _ _
  · rw [map_add]
    exact add_mem hf hg
  · rw [map_mul]
    refine mul_mem hf (Algebra.subset_adjoin ⟨n, rfl⟩)

theorem mvPolynomialFunctions.le_equalizer {A : Type*} [Semiring A] [Algebra R A]
    (s : Set (σ → R)) (φ ψ : C(s, R) →ₐ[R] A)
    (h : ∀ i, φ (toContinuousMapOnAlgHom s (X i)) = ψ (toContinuousMapOnAlgHom s (X i))) :
    mvPolynomialFunctions s ≤ AlgHom.equalizer φ ψ := by
  rw [mvPolynomialFunctions.eq_adjoin_X s]
  exact φ.adjoin_le_equalizer ψ fun x ⟨i, hi⟩ => by simpa [hi] using h i

open StarAlgebra

theorem mvPolynomialFunctions.starClosure_eq_adjoin_X [StarRing R] [ContinuousStar R]
    (s : Set (σ → R)) :
    (mvPolynomialFunctions s).starClosure = adjoin R {toContinuousMapOnAlgHom s (X i) | i : σ} := by
  rw [mvPolynomialFunctions.eq_adjoin_X s, adjoin_eq_starClosure_adjoin]

theorem mvPolynomialFunctions.starClosure_le_equalizer {A : Type*} [StarRing R] [ContinuousStar R]
    [Semiring A] [StarRing A] [Algebra R A] (s : Set ( σ → R)) (φ ψ : C(s, R) →⋆ₐ[R] A)
    (h : ∀ i, φ (toContinuousMapOnAlgHom s (X i)) = ψ (toContinuousMapOnAlgHom s (X i))) :
    (mvPolynomialFunctions s).starClosure ≤ StarAlgHom.equalizer φ ψ := by
  rw [mvPolynomialFunctions.starClosure_eq_adjoin_X s]
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x ⟨i, hi⟩ => by simpa [hi] using h i

end
