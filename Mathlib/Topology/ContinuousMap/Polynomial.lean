/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Star.Subalgebra

/-!
# Constructions relating polynomial functions and continuous functions.

## Main definitions

* `Polynomial.toContinuousMapOn p X`: for `X : Set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `Polynomial.toContinuousMapOnAlgHom`: the same, as an `R`-algebra homomorphism.
* `polynomialFunctions (X : Set R) : Subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints`:
  the polynomial functions separate points.

-/


variable {R : Type*}

open Polynomial

namespace Polynomial

section

variable [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def toContinuousMap (p : R[X]) : C(R, R) :=
  ⟨fun x : R => p.eval x, by fun_prop⟩

open ContinuousMap in
lemma toContinuousMap_X_eq_id : X.toContinuousMap = .id R := by
  ext; simp

/-- A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R) :=
  ⟨fun x : X => p.toContinuousMap x, by fun_prop⟩

open ContinuousMap in
lemma toContinuousMapOn_X_eq_restrict_id (s : Set R) :
    X.toContinuousMapOn s = restrict s (.id R) := by
  ext; simp


-- TODO some lemmas about when `toContinuousMapOn` is injective?
end

section

variable {α : Type*} [TopologicalSpace α] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R]

@[simp]
theorem aeval_continuousMap_apply (g : R[X]) (f : C(α, R)) (x : α) :
    ((Polynomial.aeval f) g) x = g.eval (f x) := by
  refine Polynomial.induction_on' g ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp

end

noncomputable section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
@[simps]
def toContinuousMapAlgHom : R[X] →ₐ[R] C(R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

/-- The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def toContinuousMapOnAlgHom (X : Set R) : R[X] →ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]

end

end Polynomial

section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
noncomputable
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]
theorem polynomialFunctions_coe (X : Set R) :
    (polynomialFunctions X : Set C(X, R)) = Set.range (Polynomial.toContinuousMapOnAlgHom X) := by
  ext
  simp [polynomialFunctions]

-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomialFunctions X` and
-- `polynomialFunctions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.
theorem polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints :=
  fun x y h => by
  -- We use `Polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, ?_⟩⟩
  dsimp; simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')

open unitInterval

open ContinuousMap

/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
theorem polynomialFunctions.comap_compRightAlgHom_iccHomeoI (a b : ℝ) (h : a < b) :
    (polynomialFunctions I).comap (compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm) =
      polynomialFunctions (Set.Icc a b) := by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [DFunLike.ext_iff] at w
    dsimp at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp only [q, neg_mul, RingHom.map_neg, RingHom.map_mul, AlgHom.coe_toRingHom,
        Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_smul,
        smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_comp, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply]
      convert w ⟨_, _⟩
      · ext
        simp only [iccHomeoI_symm_apply_coe]
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm
        field_simp
        ring
      · change _ + _ ∈ I
        rw [mul_comm (b - a)⁻¹, ← neg_mul, ← add_mul, ← sub_eq_add_neg]
        have w₁ : 0 < (b - a)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a
        fconstructor
        · exact mul_nonneg w₂ (le_of_lt w₁)
        · rw [← div_eq_mul_inv, div_le_one (sub_pos.mpr h)]
          exact w₃
  · rintro ⟨p, ⟨-, rfl⟩⟩
    let q := p.comp ((b - a) • Polynomial.X + Polynomial.C a)
    refine ⟨q, ⟨?_, ?_⟩⟩
    · simp
    · ext x
      simp [q, mul_comm]

theorem polynomialFunctions.eq_adjoin_X (s : Set R) :
    polynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s X} := by
  refine le_antisymm ?_
    (Algebra.adjoin_le fun _ h => ⟨X, trivial, (Set.mem_singleton_iff.1 h).symm⟩)
  rintro - ⟨p, -, rfl⟩
  rw [AlgHom.coe_toRingHom]
  refine p.induction_on (fun r => ?_) (fun f g hf hg => ?_) fun n r hn => ?_
  · rw [Polynomial.C_eq_algebraMap, AlgHomClass.commutes]
    exact Subalgebra.algebraMap_mem _ r
  · rw [map_add]
    exact add_mem hf hg
  · rw [pow_succ, ← mul_assoc, map_mul]
    exact mul_mem hn (Algebra.subset_adjoin <| Set.mem_singleton _)

theorem polynomialFunctions.le_equalizer {A : Type*} [Semiring A] [Algebra R A] (s : Set R)
    (φ ψ : C(s, R) →ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    polynomialFunctions s ≤ AlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.eq_adjoin_X s]
  exact φ.adjoin_le_equalizer ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

open StarAlgebra

theorem polynomialFunctions.starClosure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) :
    (polynomialFunctions s).starClosure = adjoin R {toContinuousMapOnAlgHom s X} := by
  rw [polynomialFunctions.eq_adjoin_X s, adjoin_eq_starClosure_adjoin]

theorem polynomialFunctions.starClosure_le_equalizer {A : Type*} [StarRing R] [ContinuousStar R]
    [Semiring A] [StarRing A] [Algebra R A] (s : Set R) (φ ψ : C(s, R) →⋆ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    (polynomialFunctions s).starClosure ≤ StarAlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.starClosure_eq_adjoin_X s]
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h

end
