/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.UnitInterval

#align_import topology.continuous_function.polynomial from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

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

variable [Semiring R] [TopologicalSpace R] [TopologicalSemiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def toContinuousMap (p : R[X]) : C(R, R) :=
  ⟨fun x : R => p.eval x, by continuity⟩
                             -- 🎉 no goals
#align polynomial.to_continuous_map Polynomial.toContinuousMap

/-- A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R) :=
  -- Porting note: Old proof was `⟨fun x : X => p.toContinuousMap x, by continuity⟩`
  ⟨fun x : X => p.toContinuousMap x, Continuous.comp (by continuity) (by continuity)⟩
                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align polynomial.to_continuous_map_on Polynomial.toContinuousMapOn

-- TODO some lemmas about when `toContinuousMapOn` is injective?
end

section

variable {α : Type*} [TopologicalSpace α] [CommSemiring R] [TopologicalSpace R]
  [TopologicalSemiring R]

@[simp]
theorem aeval_continuousMap_apply (g : R[X]) (f : C(α, R)) (x : α) :
    ((Polynomial.aeval f) g) x = g.eval (f x) := by
  refine' Polynomial.induction_on' g _ _
  -- ⊢ ∀ (p q : R[X]), ↑(↑(aeval f) p) x = eval (↑f x) p → ↑(↑(aeval f) q) x = eval …
  · intro p q hp hq
    -- ⊢ ↑(↑(aeval f) (p + q)) x = eval (↑f x) (p + q)
    simp [hp, hq]
    -- 🎉 no goals
  · intro n a
    -- ⊢ ↑(↑(aeval f) (↑(monomial n) a)) x = eval (↑f x) (↑(monomial n) a)
    simp [Pi.pow_apply]
    -- 🎉 no goals
#align polynomial.aeval_continuous_map_apply Polynomial.aeval_continuousMap_apply

end

noncomputable section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/-- The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
@[simps]
def toContinuousMapAlgHom : R[X] →ₐ[R] C(R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑{ toOneHom := { toFun := fun p => toContinuousMap p, map_on …
    simp
    -- 🎉 no goals
  map_add' _ _ := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑{ toOneHom := { toFun := fun p => toContinuousMap p, map_on …
    -- ⊢ ↑((fun p => toContinuousMap p) 1) a✝ = ↑1 a✝
    simp
    -- 🎉 no goals
    -- 🎉 no goals
  map_one' := by
    -- ⊢ ↑(OneHom.toFun { toFun := fun p => toContinuousMap p, map_one' := (_ : (fun  …
    ext
    -- 🎉 no goals
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑↑{ toMonoidHom := { toOneHom := { toFun := fun p => toConti …
    simp [Algebra.algebraMap_eq_smul_one]
    -- 🎉 no goals
#align polynomial.to_continuous_map_alg_hom Polynomial.toContinuousMapAlgHom

/-- The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def toContinuousMapOnAlgHom (X : Set R) : R[X] →ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑{ toOneHom := { toFun := fun p => toContinuousMapOn p X, ma …
    simp
    -- 🎉 no goals
  map_add' _ _ := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑{ toOneHom := { toFun := fun p => toContinuousMapOn p X, ma …
    -- ⊢ ↑((fun p => toContinuousMapOn p X) 1) a✝ = ↑1 a✝
    simp
    -- 🎉 no goals
    -- 🎉 no goals
  map_one' := by
    -- ⊢ ↑(OneHom.toFun { toFun := fun p => toContinuousMapOn p X, map_one' := (_ : ( …
    ext
    -- 🎉 no goals
    simp
  map_mul' _ _ := by
    ext
    simp
  commutes' _ := by
    ext
    -- ⊢ ↑(OneHom.toFun (↑↑{ toMonoidHom := { toOneHom := { toFun := fun p => toConti …
    simp [Algebra.algebraMap_eq_smul_one]
    -- 🎉 no goals
#align polynomial.to_continuous_map_on_alg_hom Polynomial.toContinuousMapOnAlgHom

end

end Polynomial

section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
noncomputable -- Porting note: added noncomputable
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)
#align polynomial_functions polynomialFunctions

@[simp]
theorem polynomialFunctions_coe (X : Set R) :
    (polynomialFunctions X : Set C(X, R)) = Set.range (Polynomial.toContinuousMapOnAlgHom X) := by
  ext
  -- ⊢ x✝ ∈ ↑(polynomialFunctions X) ↔ x✝ ∈ Set.range ↑(toContinuousMapOnAlgHom X)
  simp [polynomialFunctions]
  -- 🎉 no goals
#align polynomial_functions_coe polynomialFunctions_coe

-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomialFunctions X` and
-- `polynomialFunctions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.
theorem polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints :=
  fun x y h => by
  -- We use `Polynomial.X`, then clean up.
  refine' ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩
  -- ⊢ (fun f => ↑f) (↑↑(toContinuousMapOnAlgHom X) Polynomial.X) x ≠ (fun f => ↑f) …
  dsimp; simp only [Polynomial.eval_X]
  -- ⊢ ¬eval (↑x) Polynomial.X = eval (↑y) Polynomial.X
         -- ⊢ ¬↑x = ↑y
  exact fun h' => h (Subtype.ext h')
  -- 🎉 no goals
#align polynomial_functions_separates_points polynomialFunctions_separatesPoints

open unitInterval

open ContinuousMap

/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
theorem polynomialFunctions.comap_compRightAlgHom_iccHomeoI (a b : ℝ) (h : a < b) :
    (polynomialFunctions I).comap (compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm.toContinuousMap) =
      polynomialFunctions (Set.Icc a b) := by
  ext f
  -- ⊢ f ∈ Subalgebra.comap (compRightAlgHom ℝ ℝ (Homeomorph.toContinuousMap (Homeo …
  fconstructor
  -- ⊢ f ∈ Subalgebra.comap (compRightAlgHom ℝ ℝ (Homeomorph.toContinuousMap (Homeo …
  · rintro ⟨p, ⟨-, w⟩⟩
    -- ⊢ f ∈ polynomialFunctions (Set.Icc a b)
    rw [FunLike.ext_iff] at w
    -- ⊢ f ∈ polynomialFunctions (Set.Icc a b)
    dsimp at w
    -- ⊢ f ∈ polynomialFunctions (Set.Icc a b)
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    -- ⊢ f ∈ polynomialFunctions (Set.Icc a b)
    refine' ⟨q, ⟨_, _⟩⟩
    -- ⊢ q ∈ ↑⊤.toSubsemiring
    · simp
      -- 🎉 no goals
    · ext x
      -- ⊢ ↑(↑↑(toContinuousMapOnAlgHom (Set.Icc a b)) q) x = ↑f x
      simp only [neg_mul, RingHom.map_neg, RingHom.map_mul, AlgHom.coe_toRingHom, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_smul, smul_eq_mul,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.coe_aeval_eq_eval,
        Polynomial.eval_comp, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply]
      convert w ⟨_, _⟩
      -- ⊢ x = ↑(Homeomorph.symm (iccHomeoI a b h)) { val := (b - a)⁻¹ * ↑x + -(a * (b  …
      · ext
        -- ⊢ ↑x = ↑(↑(Homeomorph.symm (iccHomeoI a b h)) { val := (b - a)⁻¹ * ↑x + -(a *  …
        simp only [iccHomeoI_symm_apply_coe, Subtype.coe_mk]
        -- ⊢ ↑x = (b - a) * ((b - a)⁻¹ * ↑x + -(a * (b - a)⁻¹)) + a
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm
        -- ⊢ ↑x = (b - a) * ((b - a)⁻¹ * ↑x + -(a * (b - a)⁻¹)) + a
        simp only [mul_add]
        -- ⊢ ↑x = (b - a) * ((b - a)⁻¹ * ↑x) + (b - a) * -(a * (b - a)⁻¹) + a
        field_simp
        -- ⊢ ↑x * (b - a) = (b - a) * ↑x + -((b - a) * a) + a * (b - a)
        ring
        -- 🎉 no goals
      · change _ + _ ∈ I
        -- ⊢ (b - a)⁻¹ * ↑x + -(a * (b - a)⁻¹) ∈ I
        rw [mul_comm (b - a)⁻¹, ← neg_mul, ← add_mul, ← sub_eq_add_neg]
        -- ⊢ (↑x - a) * (b - a)⁻¹ ∈ I
        have w₁ : 0 < (b - a)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
        -- ⊢ (↑x - a) * (b - a)⁻¹ ∈ I
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1
        -- ⊢ (↑x - a) * (b - a)⁻¹ ∈ I
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a
        -- ⊢ (↑x - a) * (b - a)⁻¹ ∈ I
        fconstructor
        -- ⊢ 0 ≤ (↑x - a) * (b - a)⁻¹
        · exact mul_nonneg w₂ (le_of_lt w₁)
          -- 🎉 no goals
        · rw [← div_eq_mul_inv, div_le_one (sub_pos.mpr h)]
          -- ⊢ ↑x - a ≤ b - a
          exact w₃
          -- 🎉 no goals
  · rintro ⟨p, ⟨-, rfl⟩⟩
    -- ⊢ ↑↑(toContinuousMapOnAlgHom (Set.Icc a b)) p ∈ Subalgebra.comap (compRightAlg …
    let q := p.comp ((b - a) • Polynomial.X + Polynomial.C a)
    -- ⊢ ↑↑(toContinuousMapOnAlgHom (Set.Icc a b)) p ∈ Subalgebra.comap (compRightAlg …
    refine' ⟨q, ⟨_, _⟩⟩
    -- ⊢ q ∈ ↑⊤.toSubsemiring
    · simp
      -- 🎉 no goals
    · ext x
      -- ⊢ ↑(↑↑(toContinuousMapOnAlgHom I) q) x = ↑(↑↑(compRightAlgHom ℝ ℝ (Homeomorph. …
      simp [mul_comm]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial_functions.comap_comp_right_alg_hom_Icc_homeo_I polynomialFunctions.comap_compRightAlgHom_iccHomeoI

theorem polynomialFunctions.eq_adjoin_X (s : Set R) :
    polynomialFunctions s = Algebra.adjoin R {toContinuousMapOnAlgHom s X} := by
  refine le_antisymm ?_
    (Algebra.adjoin_le fun _ h => ⟨X, trivial, (Set.mem_singleton_iff.1 h).symm⟩)
  rintro - ⟨p, -, rfl⟩
  -- ⊢ ↑↑(toContinuousMapOnAlgHom s) p ∈ Algebra.adjoin R {↑(toContinuousMapOnAlgHo …
  rw [AlgHom.coe_toRingHom]
  -- ⊢ ↑(toContinuousMapOnAlgHom s) p ∈ Algebra.adjoin R {↑(toContinuousMapOnAlgHom …
  refine p.induction_on (fun r => ?_) (fun f g hf hg => ?_) fun n r hn => ?_
  · rw [Polynomial.C_eq_algebraMap, AlgHomClass.commutes]
    -- ⊢ ↑(algebraMap R C(↑s, R)) r ∈ Algebra.adjoin R {↑(toContinuousMapOnAlgHom s) X}
    exact Subalgebra.algebraMap_mem _ r
    -- 🎉 no goals
  · rw [map_add]
    -- ⊢ ↑(toContinuousMapOnAlgHom s) f + ↑(toContinuousMapOnAlgHom s) g ∈ Algebra.ad …
    exact add_mem hf hg
    -- 🎉 no goals
  · rw [pow_succ', ← mul_assoc, map_mul]
    -- ⊢ ↑(toContinuousMapOnAlgHom s) (↑Polynomial.C r * X ^ n) * ↑(toContinuousMapOn …
    exact mul_mem hn (Algebra.subset_adjoin <| Set.mem_singleton _)
    -- 🎉 no goals

theorem polynomialFunctions.le_equalizer {A : Type*} [Semiring A] [Algebra R A] (s : Set R)
    (φ ψ : C(s, R) →ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    polynomialFunctions s ≤ φ.equalizer ψ := by
  rw [polynomialFunctions.eq_adjoin_X s]
  -- ⊢ Algebra.adjoin R {↑(toContinuousMapOnAlgHom s) X} ≤ AlgHom.equalizer φ ψ
  exact φ.adjoin_le_equalizer ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h
  -- 🎉 no goals

open StarSubalgebra

theorem polynomialFunctions.starClosure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) :
    (polynomialFunctions s).starClosure = adjoin R {toContinuousMapOnAlgHom s X} := by
  rw [polynomialFunctions.eq_adjoin_X s, adjoin_eq_starClosure_adjoin]
  -- 🎉 no goals

theorem polynomialFunctions.starClosure_le_equalizer {A : Type*} [StarRing R] [ContinuousStar R]
    [Semiring A] [StarRing A] [Algebra R A] (s : Set R) (φ ψ : C(s, R) →⋆ₐ[R] A)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) :
    (polynomialFunctions s).starClosure ≤ StarAlgHom.equalizer φ ψ := by
  rw [polynomialFunctions.starClosure_eq_adjoin_X s]
  -- ⊢ adjoin R {↑(toContinuousMapOnAlgHom s) X} ≤ StarAlgHom.equalizer φ ψ
  exact StarAlgHom.adjoin_le_equalizer φ ψ fun x hx => (Set.mem_singleton_iff.1 hx).symm ▸ h
  -- 🎉 no goals

end
