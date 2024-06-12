/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.Algebra.Algebra

#align_import topology.continuous_function.weierstrass from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# The Weierstrass approximation theorem for continuous functions on `[a,b]`

We've already proved the Weierstrass approximation theorem
in the sense that we've shown that the Bernstein approximations
to a continuous function on `[0,1]` converge uniformly.

Here we rephrase this more abstractly as
`polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤`
and then, by precomposing with suitable affine functions,
`polynomialFunctions_closure_eq_top : (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤`
-/


open ContinuousMap Filter

open scoped unitInterval

/-- The special case of the Weierstrass approximation theorem for the interval `[0,1]`.
This is just a matter of unravelling definitions and using the Bernstein approximations.
-/
theorem polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  refine Filter.Frequently.mem_closure ?_
  refine Filter.Tendsto.frequently (bernsteinApproximation_uniform f) ?_
  apply frequently_of_forall
  intro n
  simp only [SetLike.mem_coe]
  apply Subalgebra.sum_mem
  rintro n -
  apply Subalgebra.smul_mem
  dsimp [bernstein, polynomialFunctions]
  simp
#align polynomial_functions_closure_eq_top' polynomialFunctions_closure_eq_top'

/-- The **Weierstrass Approximation Theorem**:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`

(While we could deduce this as an application of the Stone-Weierstrass theorem,
our proof of that relies on the fact that `abs` is in the closure of polynomials on `[-M, M]`,
so we may as well get this done first.)
-/
theorem polynomialFunctions_closure_eq_top (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  cases' lt_or_le a b with h h
  -- (Otherwise it's easy; we'll deal with that later.)
  · -- We can pullback continuous functions on `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(Set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) :=
      compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm.toContinuousMap
    -- This operation is itself a homeomorphism
    -- (with respect to the norm topologies on continuous functions).
    let W' : C(Set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := compRightHomeomorph ℝ (iccHomeoI a b h).symm
    have w : (W : C(Set.Icc a b, ℝ) → C(I, ℝ)) = W' := rfl
    -- Thus we take the statement of the Weierstrass approximation theorem for `[0,1]`,
    have p := polynomialFunctions_closure_eq_top'
    -- and pullback both sides, obtaining an equation between subalgebras of `C([a,b], ℝ)`.
    apply_fun fun s => s.comap W at p
    simp only [Algebra.comap_top] at p
    -- Since the pullback operation is continuous, it commutes with taking `topologicalClosure`,
    rw [Subalgebra.topologicalClosure_comap_homeomorph _ W W' w] at p
    -- and precomposing with an affine map takes polynomial functions to polynomial functions.
    rw [polynomialFunctions.comap_compRightAlgHom_iccHomeoI] at p
    -- 🎉
    exact p
  · -- Otherwise, `b ≤ a`, and the interval is a subsingleton,
    have : Subsingleton (Set.Icc a b) := (Set.subsingleton_Icc_of_ge h).coe_sort
    apply Subsingleton.elim
#align polynomial_functions_closure_eq_top polynomialFunctions_closure_eq_top

/-- An alternative statement of Weierstrass' theorem.

Every real-valued continuous function on `[a,b]` is a uniform limit of polynomials.
-/
theorem continuousMap_mem_polynomialFunctions_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [polynomialFunctions_closure_eq_top _ _]
  simp
#align continuous_map_mem_polynomial_functions_closure continuousMap_mem_polynomialFunctions_closure

open scoped Polynomial

/-- An alternative statement of Weierstrass' theorem,
for those who like their epsilons.

Every real-valued continuous function on `[a,b]` is within any `ε > 0` of some polynomial.
-/
theorem exists_polynomial_near_continuousMap (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (ε : ℝ)
    (pos : 0 < ε) : ∃ p : ℝ[X], ‖p.toContinuousMapOn _ - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_polynomialFunctions_closure _ _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩
#align exists_polynomial_near_continuous_map exists_polynomial_near_continuousMap

/-- Another alternative statement of Weierstrass's theorem,
for those who like epsilons, but not bundled continuous functions.

Every real-valued function `ℝ → ℝ` which is continuous on `[a,b]`
can be approximated to within any `ε > 0` on `[a,b]` by some polynomial.
-/
theorem exists_polynomial_near_of_continuousOn (a b : ℝ) (f : ℝ → ℝ)
    (c : ContinuousOn f (Set.Icc a b)) (ε : ℝ) (pos : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuousMap a b f' ε pos
  use p
  rw [norm_lt_iff _ pos] at b
  intro x m
  exact b ⟨x, m⟩
#align exists_polynomial_near_of_continuous_on exists_polynomial_near_of_continuousOn
