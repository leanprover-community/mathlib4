/-
Copyright (c) 2025 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Zorn
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Maximal Solutions to Ordinary Differential Equations

This file defines the concept of a maximal solution to an ODE `x' = v(t, x)` with initial
condition `x(t₀) = x₀`. It proves that under the conditions of the Picard-Lindelöf theorem,
such a maximal solution exists.

The strategy involves using Zorn's Lemma on the set of all local ODE solutions, ordered by
extension. Picard-Lindelöf's theorem provides the existence of at least one local solution,
ensuring the set is non-empty. The core of the Zorn's Lemma application is showing that
every chain of solutions has an upper bound, constructed by "gluing" the solutions in the
chain together.

## Main Definitions

* `IsODESolution`: Predicate stating that a function `f` is a solution to the ODE `x' = v(t, x)`
  with initial value `(t₀, x₀)` on a given open connected domain `I`.
* `IsMaximalODESolution`: Predicate stating that an `IsODESolution` `(f, I)` cannot be extended
  to a solution on any strictly larger open connected domain.

## Main Theorem

* `exists_maximal_ode_solution`: Under Picard-Lindelöf conditions (ensuring local existence
  on an open interval around `t₀`), there exists a function `f` and an open connected set `I`
  (an open interval) such that `(f, I)` is a maximal solution.

## TODO

* Implement the compact exit lemma ("lemme des bouts").
* Connect to global existence theorems and criteria for when the maximal interval of existence
  is `(-∞, ∞)`.
-/

open Set Filter NNReal Topology TopologicalSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E)

/--
A function `f` is a solution to the ODE `x' = v(t, x)` with initial value `(t₀, x₀)` on an
open connected set `I` (which in `ℝ` implies `I` is an open interval).
-/
structure IsODESolution (f : ℝ → E) (I : Set ℝ) : Prop where
  /-- The domain `I` must be an open set. -/
  isOpen : IsOpen I
  /-- The domain `I` must be connected. Combined with `isOpen`, this ensures `I` is an
  open interval if non-empty. -/
  isConnected : IsConnected I
  /-- The initial time `t₀` must be in the domain `I`. -/
  t₀_mem : t₀ ∈ I
  /-- The solution must satisfy the initial condition `f(t₀) = x₀`. -/
  f_t₀ : f t₀ = x₀
  /-- The function `f` must have the derivative `v t (f t)` at every point `t` in `I`. -/
  deriv_eq : ∀ t ∈ I, HasDerivAt f (v t (f t)) t

lemma IsODESolution.continuousOn {f : ℝ → E} {I : Set ℝ} (h_sol : IsODESolution v t₀ x₀ f I) :
    ContinuousOn f I := by
  intro t ht
  exact (h_sol.deriv_eq t ht).continuousAt.continuousWithinAt

/--
If two solutions `f₁` and `f₂` to the ODE `y' = v(t,y)` pass through the same point `(t₀, x₀)`,
and `v(t,·)` is Lipschitz continuous with a uniform constant `K_const` for `x ∈ univ E`
for all `t` in the intersection of their domains `I₁ ∩ I₂`, then `f₁` and `f₂` agree on this
entire intersection. This is a standard uniqueness result derived from Gronwall's inequality.
-/
lemma IsODESolution.eqOn_of_agree_at_t₀_of_lipschitz
    {f₁ f₂ : ℝ → E} {I₁ I₂ : Set ℝ}
    (h₁ : IsODESolution v t₀ x₀ f₁ I₁)
    (h₂ : IsODESolution v t₀ x₀ f₂ I₂)
    (K_const : ℝ≥0)
    (h_lipschitz : ∀ (t_val : ℝ) (_ : t_val ∈ I₁ ∩ I₂), LipschitzWith K_const (v t_val)) :
    EqOn f₁ f₂ (I₁ ∩ I₂) := by
  -- Let K_int be the intersection of the solution domains.
  let K_int := I₁ ∩ I₂
  have ht₀_mem_K_int : t₀ ∈ K_int := ⟨h₁.t₀_mem, h₂.t₀_mem⟩
  have hK_int_nonempty : K_int.Nonempty := ⟨t₀, ht₀_mem_K_int⟩

  -- The intersection K_int is an open interval because I₁ and I₂ are open intervals containing t₀.
  have hK_int_conn : IsConnected K_int := by
    have h₁_ord : OrdConnected I₁ := h₁.isConnected.isPreconnected.ordConnected
    have h₂_ord : OrdConnected I₂ := h₂.isConnected.isPreconnected.ordConnected
    have hK_int_ord : OrdConnected K_int := OrdConnected.inter h₁_ord h₂_ord
    exact ⟨hK_int_nonempty, hK_int_ord.isPreconnected⟩

  -- Both solutions satisfy the same initial condition f(t₀) = x₀.
  have heq_at_t₀ : f₁ t₀ = f₂ t₀ := by rw [h₁.f_t₀, h₂.f_t₀]

  -- To show f₁ and f₂ agree on K_int, consider any point t' ∈ K_int.
  intro t' ht'_in_K_int
  -- The proof splits based on the order of t₀ and t'.
  rcases le_total t₀ t' with h_t₀_le_t' | h_t'_le_t₀

  · -- Case 1: t₀ ≤ t'. Apply uniqueness on the closed interval J = [t₀, t'].
    let J := Icc t₀ t'
    -- J is contained in K_int because K_int is an interval containing both t₀ and t'.
    have hJ_sub_K_int : J ⊆ K_int := by
      intro j hj_in_J
      exact hK_int_conn.isPreconnected.ordConnected.out ht₀_mem_K_int ht'_in_K_int hj_in_J

    -- The Lipschitz condition on v holds for t ∈ Ico t₀ t' (required by uniqueness theorem).
    have hv_J : ∀ (t_val : ℝ) (ht_val : t_val ∈ Ico t₀ t'),
        LipschitzOnWith K_const (v t_val) univ := by
      intro t_val ht_val_in_Ico
      exact (h_lipschitz t_val (hJ_sub_K_int (mem_Icc_of_Ico ht_val_in_Ico))).lipschitzOnWith

    -- Verify conditions for ODE_solution_unique_of_mem_Icc_right for f₁.
    have hf₁_cont_J : ContinuousOn f₁ J :=
      h₁.continuousOn.mono (Subset.trans hJ_sub_K_int inter_subset_left)
    have hf₁'_deriv_J : ∀ (t_val : ℝ) (ht_val : t_val ∈ Ico t₀ t'),
        HasDerivWithinAt f₁ (v t_val (f₁ t_val)) (Ici t_val) t_val := by
      intro t_val ht_val_in_Ico
      have deriv_at := h₁.deriv_eq t_val
        (Subset.trans hJ_sub_K_int inter_subset_left (mem_Icc_of_Ico ht_val_in_Ico))
      exact deriv_at.hasDerivWithinAt
    have hf₁s_univ_J :
      ∀ (t_val : ℝ) (ht_val : t_val ∈ Ico t₀ t'), f₁ t_val ∈ univ := fun _ _ => trivial

    -- Verify conditions for ODE_solution_unique_of_mem_Icc_right for f₂.
    have hf₂_cont_J : ContinuousOn f₂ J :=
      h₂.continuousOn.mono (Subset.trans hJ_sub_K_int inter_subset_right)
    have hf₂'_deriv_J : ∀ (t_val : ℝ) (ht_val : t_val ∈ Ico t₀ t'),
        HasDerivWithinAt f₂ (v t_val (f₂ t_val)) (Ici t_val) t_val := by
      intro t_val ht_val_in_Ico
      have deriv_at := h₂.deriv_eq t_val
        (Subset.trans hJ_sub_K_int inter_subset_right (mem_Icc_of_Ico ht_val_in_Ico))
      exact deriv_at.hasDerivWithinAt
    have hf₂s_univ_J :
      ∀ (t_val : ℝ) (ht_val : t_val ∈ Ico t₀ t'), f₂ t_val ∈ univ := fun _ _ => trivial

    -- Apply the uniqueness theorem.
    replace heq_at_t₀ : f₁ t₀ = f₂ t₀ := heq_at_t₀
    have eq_on_J := ODE_solution_unique_of_mem_Icc_right hv_J
                      hf₁_cont_J hf₁'_deriv_J hf₁s_univ_J
                      hf₂_cont_J hf₂'_deriv_J hf₂s_univ_J
                      heq_at_t₀
    -- Since t' ∈ J, f₁(t') = f₂(t').
    exact eq_on_J (right_mem_Icc.mpr h_t₀_le_t')

  · -- Case 2: t' < t₀. Apply uniqueness on the closed interval J = [t', t₀].
    let J := Icc t' t₀
    -- J is contained in K_int.
    have hJ_sub_K_int : J ⊆ K_int := by
      intro j hj_in_J
      exact hK_int_conn.isPreconnected.ordConnected.out ht'_in_K_int ht₀_mem_K_int hj_in_J

    -- The Lipschitz condition on v holds for t ∈ Ioc t' t₀.
    have hv_J : ∀ (t_val : ℝ) (ht_val : t_val ∈ Ioc t' t₀),
        LipschitzOnWith K_const (v t_val) univ := by
      intro t_val ht_val_in_Ioc
      exact (h_lipschitz t_val (hJ_sub_K_int (mem_Icc_of_Ioc ht_val_in_Ioc))).lipschitzOnWith

    -- Verify conditions for ODE_solution_unique_of_mem_Icc_left for f₁.
    have hf₁_cont_J : ContinuousOn f₁ J :=
      h₁.continuousOn.mono (Subset.trans hJ_sub_K_int inter_subset_left)
    have hf₁'_deriv_J : ∀ (t_val : ℝ) (ht_val : t_val ∈ Ioc t' t₀),
        HasDerivWithinAt f₁ (v t_val (f₁ t_val)) (Iic t_val) t_val := by
      intro t_val ht_val_in_Ioc
      have deriv_at := h₁.deriv_eq t_val
        (Subset.trans hJ_sub_K_int inter_subset_left (mem_Icc_of_Ioc ht_val_in_Ioc))
      exact deriv_at.hasDerivWithinAt
    have hf₁s_univ_J :
      ∀ (t_val : ℝ) (ht_val : t_val ∈ Ioc t' t₀), f₁ t_val ∈ univ := fun _ _ => trivial

    -- Verify conditions for ODE_solution_unique_of_mem_Icc_left for f₂.
    have hf₂_cont_J : ContinuousOn f₂ J :=
      h₂.continuousOn.mono (Subset.trans hJ_sub_K_int inter_subset_right)
    have hf₂'_deriv_J : ∀ (t_val : ℝ) (ht_val : t_val ∈ Ioc t' t₀),
        HasDerivWithinAt f₂ (v t_val (f₂ t_val)) (Iic t_val) t_val := by
      intro t_val ht_val_in_Ioc
      have deriv_at := h₂.deriv_eq t_val
        (Subset.trans hJ_sub_K_int inter_subset_right (mem_Icc_of_Ioc ht_val_in_Ioc))
      exact deriv_at.hasDerivWithinAt
    have hf₂s_univ_J :
      ∀ (t_val : ℝ) (ht_val : t_val ∈ Ioc t' t₀), f₂ t_val ∈ univ := fun _ _ => trivial

    -- Apply the uniqueness theorem (solutions agree at the right endpoint t₀).
    replace heq_at_t₀ : f₁ t₀ = f₂ t₀ := heq_at_t₀
    have eq_on_J := ODE_solution_unique_of_mem_Icc_left hv_J
                      hf₁_cont_J hf₁'_deriv_J hf₁s_univ_J
                      hf₂_cont_J hf₂'_deriv_J hf₂s_univ_J
                      heq_at_t₀
    -- Since t' ∈ J, f₁(t') = f₂(t').
    exact eq_on_J (left_mem_Icc.mpr h_t'_le_t₀)

/--
A solution `(f, I)` to the ODE `x' = v(t, x)` with initial value `(t₀, x₀)` is maximal if it
cannot be extended to a solution on any strictly larger open connected domain `J`.
-/
structure IsMaximalODESolution (f : ℝ → E) (I : Set ℝ) : Prop
  extends IsODESolution v t₀ x₀ f I where
  /-- The maximality condition: If `(g, J)` is another solution such that `I ⊆ J` and `f` agrees
  with `g` on `I`, then `I` must be equal to `J`. -/
  is_maximal : ∀ (g : ℝ → E) (J : Set ℝ), IsODESolution v t₀ x₀ g J → I ⊆ J → (EqOn f g I) → I = J

open Classical in
/--
If `h_loc` is any local solution to the ODE and `h_max` is a maximal solution,
then the domain of `h_loc` is a subset of the domain of `h_max`. This relies on the
uniqueness of solutions on the intersection of their domains, guaranteed by Lipschitz
conditions on `v`.
-/
lemma IsODESolution.subset_maximal_domain_with_lipschitz
    {f_loc} {I_loc} (h_loc : IsODESolution v t₀ x₀ f_loc I_loc)
    {f_max} {I_max} (h_max : IsMaximalODESolution v t₀ x₀ f_max I_max)
    (K_const : ℝ≥0) -- Uniform Lipschitz constant for v(t,·) on the intersection.
    (h_v_lipschitz : ∀ (t_val : ℝ) (_ : t_val ∈ I_loc ∩ I_max),
      LipschitzWith K_const (v t_val)) :
    I_loc ⊆ I_max := by
  -- Step 1: Show that f_loc and f_max agree on the intersection of their domains.
  -- This follows from the provided uniqueness lemma, given they start at (t₀, x₀)
  -- and v is Lipschitz on the intersection.
  have h_agree_on_inter : EqOn f_loc f_max (I_loc ∩ I_max) :=
    IsODESolution.eqOn_of_agree_at_t₀_of_lipschitz v t₀ x₀ h_loc h_max.toIsODESolution
      K_const h_v_lipschitz

  -- Step 2: Define a candidate solution f_union on the union of the domains I_union.
  let I_union := I_loc ∪ I_max
  -- f_union is defined to be f_max on I_max, and f_loc elsewhere (which means on I_loc \ I_max).
  -- This is well-defined due to h_agree_on_inter.
  let f_union (t : ℝ) : E := if t ∈ I_max then f_max t else f_loc t

  -- Step 3: Prove that (f_union, I_union) is an IsODESolution.
  have h_union_sol : IsODESolution v t₀ x₀ f_union I_union := by
    constructor
    · -- I_union is open as a union of open sets.
      exact h_loc.isOpen.union h_max.toIsODESolution.isOpen
    · -- I_union is connected because I_loc and I_max are connected
      -- and their intersection is non-empty (contains t₀).
      have h_inter_nonempty : (I_loc ∩ I_max).Nonempty :=
        ⟨t₀, ⟨h_loc.t₀_mem, h_max.toIsODESolution.t₀_mem⟩⟩
      exact IsConnected.union h_inter_nonempty h_loc.isConnected h_max.toIsODESolution.isConnected
    · -- t₀ is in I_union because it's in I_loc (and I_max).
      exact Or.inl h_loc.t₀_mem
    · -- f_union satisfies the initial condition at t₀.
      simp only [f_union, h_max.toIsODESolution.t₀_mem, ite_true, h_max.toIsODESolution.f_t₀]
    · -- f_union has the correct derivative at every point t in I_union.
      intro t ht_in_union
      if ht_in_I_max : t ∈ I_max then
        -- Case A: t ∈ I_max.
        -- Then f_union(t) = f_max(t), and f_max has the correct derivative.
        -- f_union agrees with f_max in the neighborhood I_max of t.
        have h_fmax_deriv : HasDerivAt f_max (v t (f_max t)) t :=
          h_max.toIsODESolution.deriv_eq t ht_in_I_max
        have heq_eventually : f_union =ᶠ[𝓝 t] f_max := by
          filter_upwards [h_max.toIsODESolution.isOpen.mem_nhds ht_in_I_max] with y hy_in_Imax
          simp [f_union, hy_in_Imax]
        rw [show f_union t = f_max t by simp [f_union, ht_in_I_max]]
        exact HasDerivAt.congr_of_eventuallyEq h_fmax_deriv heq_eventually
      else
        -- Case B: t ∉ I_max. Since t ∈ I_union, it must be that t ∈ I_loc.
        -- Then f_union(t) = f_loc(t), and f_loc has the correct derivative.
        have ht_in_I_loc : t ∈ I_loc := ht_in_union.resolve_right ht_in_I_max
        have h_floc_deriv : HasDerivAt f_loc (v t (f_loc t)) t :=
          h_loc.deriv_eq t ht_in_I_loc
        -- Define φ(y) = f_union(y) - f_loc(y).
        -- We show f_union = f_loc + φ and HasDerivAt φ 0 t.
        let φ y := if y ∈ I_max then f_max y - f_loc y else (0:E)
        have h_phi_t_is_zero : φ t = 0 := by simp [φ, ht_in_I_max]

        have h_phi_deriv_zero : HasDerivAt φ (0:E) t := by
            apply hasDerivAtFilter_iff_tendsto_slope.mpr
            -- The slope (y - t)¯¹ ⬝ (φ y - φ t) is (y - t)¯¹ ⬝ (φ y) since φ t = 0.
            -- This slope is 0 for y in (I_loc \ {t}) because:
            -- If y ∈ I_max (and y ∈ I_loc), then φ y = f_max y - f_loc y = 0 by h_agree_on_inter.
            -- If y ∉ I_max (and y ∈ I_loc), then φ y = 0 by definition of φ.
            have h_slope_eventually_zero : ∀ᶠ y in 𝓝[≠] t, slope φ t y = (0:E) := by
              have I_loc_mem_nhds_t : I_loc ∈ 𝓝 t := h_loc.isOpen.mem_nhds ht_in_I_loc
              filter_upwards [diff_mem_nhdsWithin_compl I_loc_mem_nhds_t {t}]
                with y hy_mem_Iloc_setminus_t
              rw [slope_def_module, h_phi_t_is_zero, sub_zero]
              simp only [φ]
              split_ifs with hy_in_Imax
              · rw [h_agree_on_inter ⟨hy_mem_Iloc_setminus_t.1, hy_in_Imax⟩, sub_self, smul_zero]
              · rw [smul_zero]
            exact (tendsto_congr' h_slope_eventually_zero).mpr tendsto_const_nhds

        -- Use f_union = f_loc + φ.
        have deriv_sum := HasDerivAt.add h_floc_deriv h_phi_deriv_zero
        rw [add_zero] at deriv_sum
        rw [show f_union t = f_loc t by simp [f_union, ht_in_I_max]]
        convert deriv_sum using 1
        · ext y
          simp only [f_union, Pi.add_apply, φ]
          split_ifs with hy_in_Imax
          · simp only [add_sub_cancel]
          · simp only [add_zero]

  -- Step 4: Apply the maximality property of (f_max, I_max).
  -- We have constructed a solution (f_union, I_union) where I_max ⊆ I_union
  -- and f_max agrees with f_union on I_max.
  have h_I_max_subset_I_union : I_max ⊆ I_union := subset_union_right
  have h_EqOn_f_max_f_union_on_I_max : EqOn f_max f_union I_max := by
    intro t' ht_in_I_max'
    simp [f_union, ht_in_I_max']

  -- By the maximality of (f_max, I_max), I_max must equal I_union.
  let h_maximal_implies_eq := h_max.is_maximal f_union I_union h_union_sol
                                h_I_max_subset_I_union h_EqOn_f_max_f_union_on_I_max
  -- So, I_max = I_loc ∪ I_max.

  -- Step 5: Conclude I_loc ⊆ I_max.
  -- If I_max = I_loc ∪ I_max, then I_loc must be a subset of I_max.
  rw [h_maximal_implies_eq]
  exact subset_union_left

/--
If `(f₁, I₁)` and `(f₂, I₂)` are two maximal solutions to the same ODE `y' = v(t,y)`
passing through `(t₀, x₀)`, and `v(t,·)` is Lipschitz continuous with a uniform constant `K_const`
on the union of their domains `I₁ ∪ I₂`, then the maximal solutions are identical:
their domains are equal (`I₁ = I₂`), and the functions agree on this common domain.
-/
theorem IsMaximalODESolution.unique
    {f₁ f₂ : ℝ → E} {I₁ I₂ : Set ℝ}
    (h₁_max : IsMaximalODESolution v t₀ x₀ f₁ I₁)
    (h₂_max : IsMaximalODESolution v t₀ x₀ f₂ I₂)
    (K_const : ℝ≥0)
    (h_v_lipschitz_on_union :
        ∀ (t_val : ℝ) (_ : t_val ∈ I₁ ∪ I₂), LipschitzWith K_const (v t_val)) :
    I₁ = I₂ ∧ EqOn f₁ f₂ I₁ := by
  -- The Lipschitz condition on `v` also holds on the intersection `I₁ ∩ I₂`,
  -- as `I₁ ∩ I₂ ⊆ I₁ ∪ I₂`.
  have h_v_lipschitz_on_inter :
      ∀ (t_val : ℝ) (_ : t_val ∈ I₁ ∩ I₂), LipschitzWith K_const (v t_val) := by
    intro t_val ht_in_inter
    exact h_v_lipschitz_on_union t_val (mem_union_left I₂ ht_in_inter.1)

  -- Show I₁ ⊆ I₂:
  -- `h₁_max.toIsODESolution` is a solution on `I₁`.
  -- `h₂_max` is a maximal solution on `I₂`.
  -- By `subset_maximal_domain_with_lipschitz`, the domain of any solution is a subset
  -- of the domain of a maximal solution, given Lipschitz continuity on the intersection.
  have h_I₁_subset_I₂ : I₁ ⊆ I₂ :=
    IsODESolution.subset_maximal_domain_with_lipschitz v t₀ x₀
      h₁_max.toIsODESolution h₂_max K_const h_v_lipschitz_on_inter

  -- Show I₂ ⊆ I₁ by a symmetric argument:
  -- `h₂_max.toIsODESolution` is a solution on `I₂`.
  -- `h₁_max` is a maximal solution on `I₁`.
  -- The Lipschitz condition on `I₂ ∩ I₁` is the same as on `I₁ ∩ I₂`.
  have h_v_lipschitz_on_inter_symm :
      ∀ (t_val : ℝ) (_ : t_val ∈ I₂ ∩ I₁), LipschitzWith K_const (v t_val) := by
    intro t_val ht_in_inter_symm
    rw [inter_comm] at ht_in_inter_symm
    exact h_v_lipschitz_on_inter t_val ht_in_inter_symm
  have h_I₂_subset_I₁ : I₂ ⊆ I₁ :=
    IsODESolution.subset_maximal_domain_with_lipschitz v t₀ x₀
      h₂_max.toIsODESolution h₁_max K_const h_v_lipschitz_on_inter_symm

  -- From `I₁ ⊆ I₂` and `I₂ ⊆ I₁`, conclude that the domains are equal.
  have h_I_eq : I₁ = I₂ := Set.Subset.antisymm h_I₁_subset_I₂ h_I₂_subset_I₁

  -- Now show that the functions `f₁` and `f₂` agree on this common domain `I₁`.
  -- The Lipschitz condition `h_v_lipschitz_on_union`
  -- implies Lipschitz on `I₁` (since `I₁ ⊆ I₁ ∪ I₂`).
  have h_v_lipschitz_on_I₁ : ∀ (t_val : ℝ) (_ : t_val ∈ I₁), LipschitzWith K_const (v t_val) := by
    intro t_val ht_in_I₁
    exact h_v_lipschitz_on_union t_val (mem_union_left I₂ ht_in_I₁)

  -- Apply `eqOn_of_agree_at_t₀_of_lipschitz` to solutions `h₁_max.toIsODESolution` (on `I₁`)
  -- and `(h_I_eq ▸ h₂_max.toIsODESolution)` (which is `h₂_max` viewed as a solution on `I₁`).
  -- The intersection of their domains is `I₁ ∩ I₁ = I₁`.
  -- The Lipschitz condition is needed on this intersection (`I₁`).
  have h_eq_on_I₁ : EqOn f₁ f₂ (I₁ ∩ I₁) :=
    IsODESolution.eqOn_of_agree_at_t₀_of_lipschitz v t₀ x₀
      h₁_max.toIsODESolution
      (h_I_eq ▸ h₂_max.toIsODESolution) -- Casts h₂_max to be a solution on I₁
      K_const
      (by -- Provides the Lipschitz hypothesis on I₁ ∩ I₁ (which is I₁)
        intro t_val ht_in_I₁_inter_I₁
        exact h_v_lipschitz_on_I₁ t_val ht_in_I₁_inter_I₁.1)
  rw [inter_self] at h_eq_on_I₁ -- Simplifies EqOn f₁ f₂ (I₁ ∩ I₁) to EqOn f₁ f₂ I₁

  -- Combine the equality of domains and the agreement of functions.
  exact ⟨h_I_eq, h_eq_on_I₁⟩

/-! ### Proof of Existence of Maximal Solutions -/

namespace MaximalSolutionExistence

/--
A local solution to the ODE, consisting of the function, its domain (an open interval),
and a proof that it satisfies the `IsODESolution` predicate.
-/
structure LocalODESolution where
  /-- The function `f` which locally solves the ODE. -/
  protected f : ℝ → E
  /-- The open interval `I` on which `f` solves the ODE. -/
  protected I : Set ℝ
  protected property : IsODESolution v t₀ x₀ f I

/--
The extension relation `p₁ ≤ p₂` for local ODE solutions `p₁` and `p₂`.
It means `p₂` is an extension of `p₁`, i.e., the domain of `p₁` is a subset of the domain
of `p₂`, and the functions agree on the smaller domain `p₁.I`.
-/
def ODESolutionExtends (p₁ p₂ : LocalODESolution v t₀ x₀) : Prop :=
  p₁.I ⊆ p₂.I ∧ (EqOn p₁.f p₂.f p₁.I)

-- Define LE instance using the extension relation
instance : LE (LocalODESolution v t₀ x₀) where
  le := ODESolutionExtends v t₀ x₀

-- Now define the Preorder instance. This is sufficient for `zorn_le_nonempty`.
instance : Preorder (LocalODESolution v t₀ x₀) where
  le := ODESolutionExtends v t₀ x₀
  le_refl := fun p => by
    constructor
    · exact Set.Subset.refl _
    · exact fun ⦃x⦄ ↦ congrFun rfl
  le_trans := fun p₁ p₂ p₃ h₁₂ h₂₃ => by
    constructor
    · exact Set.Subset.trans h₁₂.1 h₂₃.1
    · intro t ht
      have h_t_in_p₂I : t ∈ p₂.I := h₁₂.1 ht
      have eq₁₂ : p₁.f t = p₂.f t := h₁₂.2 ht
      have eq₂₃ : p₂.f t = p₃.f t := h₂₃.2 h_t_in_p₂I
      exact Eq.trans eq₁₂ eq₂₃

/--
The equivalence relation `≈` on local ODE solutions.
Two solutions are equivalent if they are extensions of each other, meaning
they have the same interval and agree on that interval.
This setoid structure is defined for completeness but not directly used by `zorn_le_nonempty`.
-/
instance LocalODESolutionSetoid : Setoid (LocalODESolution v t₀ x₀) where
  r p₁ p₂ := p₁ ≤ p₂ ∧ p₂ ≤ p₁
  iseqv := {
    refl := fun p => by
      constructor
      · exact le_refl p
      · exact le_refl p
    symm := fun {p₁ p₂} h => by
      exact And.symm h
    trans := fun {p₁ p₂ p₃} h₁₂ h₂₃ => by
      constructor
      · exact le_trans h₁₂.1 h₂₃.1
      · exact le_trans h₂₃.2 h₁₂.2
  }

/--
The quotient type of local ODE solutions, where solutions that are extensions
of each other are identified. This type carries the structure of a partial order.
This is defined for completeness but not directly used by `zorn_le_nonempty`.
-/
abbrev QuotientLocalODESolution := Quotient (LocalODESolutionSetoid (v:=v) (t₀:=t₀) (x₀:=x₀))

instance QuotientLocalODESolution.instLE : LE (QuotientLocalODESolution v t₀ x₀) where
  le := Quotient.lift₂
    (fun p₁ p₂ => p₁ ≤ p₂)
    (by
      intro a₁ a₂ b₁ b₂ hab hcd
      apply propext
      apply Iff.intro
      · intro h_a1_le_a2
        calc
          b₁ ≤ a₁ := hab.2
          _  ≤ a₂ := h_a1_le_a2
          _  ≤ b₂ := hcd.1
      · intro h_b1_le_b2
        calc
          a₁ ≤ b₁ := hab.1
          _  ≤ b₂ := h_b1_le_b2
          _  ≤ a₂ := hcd.2
    )

/--
The set of local ODE solutions modulo the extension equivalence relation forms a partial order.
The order `⟦p₁⟧ ≤ ⟦p₂⟧` is induced by the preorder relation `p₁ ≤ p₂` on the representatives.
This instance is defined for completeness; `zorn_le_nonempty` operates on the `Preorder`
of `LocalODESolution` directly.
-/
instance : PartialOrder (QuotientLocalODESolution v t₀ x₀) where
  le := (QuotientLocalODESolution.instLE v t₀ x₀).le
  le_refl := by
    intro q; rcases q with ⟨p⟩; exact le_refl p
  le_trans := by
    intro q₁ q₂ q₃; rcases q₁ with ⟨p₁⟩; rcases q₂ with ⟨p₂⟩; rcases q₃ with ⟨p₃⟩
    intro h₁₂ h₂₃; exact @Preorder.le_trans (LocalODESolution v t₀ x₀) _ p₁ p₂ p₃ h₁₂ h₂₃
  le_antisymm := by
    intro q₁ q₂; rcases q₁ with ⟨p₁⟩; rcases q₂ with ⟨p₂⟩
    intro h₁₂ h₂₁; exact Quotient.sound ⟨h₁₂, h₂₁⟩


open Classical in
/--
Constructs the supremum of a non-empty chain `C` of `LocalODESolution`s.
This supremum is itself a `LocalODESolution` and serves as an upper bound for `C`.
-/
def chainSup (C : Set (LocalODESolution v t₀ x₀)) (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
    LocalODESolution v t₀ x₀ := by
  -- The domain of the supremum solution is the union of the domains of solutions in the chain.
  let I_sup := ⋃ (p : LocalODESolution v t₀ x₀) (hp : p ∈ C), p.I
  -- The function of the supremum solution is defined by "gluing" the functions from the chain.
  -- For any t ∈ I_sup, pick any solution p ∈ C such that t ∈ p.I, and define f_sup(t) = p.f(t).
  -- This is well-defined because C is a chain.
  let f_sup : ℝ → E := fun t =>
    if ht : t ∈ I_sup then
      let p_data := Classical.choose (Set.mem_iUnion₂.mp ht)
      let _hp_proofs := Classical.choose_spec (Set.mem_iUnion₂.mp ht)
      p_data.f t
    else
      x₀ -- Arbitrary value for t ∉ I_sup.

  -- Prove I_sup is an open interval containing t₀
  have I_sup_isOpen : IsOpen I_sup :=
    isOpen_iUnion fun p => isOpen_iUnion fun _ => p.property.isOpen
  have I_sup_isConnected : IsConnected I_sup := by
      have hne : I_sup.Nonempty := by
        obtain ⟨p, hp⟩ := hCne
        exact ⟨t₀, Set.mem_biUnion hp p.property.t₀_mem⟩
      let c : Set (Set ℝ) := LocalODESolution.I '' C
      have h_common_pt : ∀ s ∈ c, t₀ ∈ s := by
        rintro s ⟨p, hp, rfl⟩; exact p.property.t₀_mem
      have h_preconn : ∀ s ∈ c, IsPreconnected s := by
        rintro s ⟨p, hp, rfl⟩; exact p.property.isConnected.isPreconnected
      have h_preconn_union : IsPreconnected I_sup := by
          have I_sup_eq_sUnion_c : I_sup = ⋃₀ c := by
            ext x; simp only [mem_iUnion, exists_prop, mem_sUnion, I_sup];
            constructor
            · rintro ⟨p, hp, hx⟩; use p.I; constructor; use p; exact hx
            · rintro ⟨s, ⟨p', hp', rfl⟩, hx_in_s⟩; use p'
          rw [I_sup_eq_sUnion_c]
          exact isPreconnected_sUnion t₀ c h_common_pt h_preconn
      exact ⟨hne, h_preconn_union⟩
  have I_sup_t₀_mem : t₀ ∈ I_sup := by
    obtain ⟨p, hp⟩ := hCne
    exact Set.mem_iUnion₂.mpr ⟨p, hp, p.property.t₀_mem⟩

  -- Prove f_sup is well-defined on I_sup.
  -- If t ∈ p₁.I and t ∈ p₂.I for p₁, p₂ ∈ C (a chain), then p₁.f(t) = p₂.f(t).
  -- This relies on C being a chain: either p₁ ≤ p₂ or p₂ ≤ p₁, and in both cases,
  -- the functions agree on the smaller domain.
  have f_sup_well_defined : ∀ (t : ℝ) (ht : t ∈ I_sup) (p₁ p₂ : LocalODESolution v t₀ x₀)
      (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) (ht₁ : t ∈ p₁.I) (ht₂ : t ∈ p₂.I),
      p₁.f t = p₂.f t := by
    intro t ht p₁ p₂ hp₁ hp₂ ht₁ ht₂
    rcases hC.total hp₁ hp₂ with h12 | h21
    · exact h12.2 ht₁
    · symm
      exact h21.2 ht₂

  -- Prove f_sup satisfies the initial condition
  have f_sup_t₀ : f_sup t₀ = x₀ := by
      have ht₀_mem : t₀ ∈ I_sup := I_sup_t₀_mem
      unfold f_sup
      rw [dif_pos ht₀_mem]
      let p := Classical.choose (Set.mem_iUnion₂.mp ht₀_mem)
      exact p.property.f_t₀

  -- Prove f_sup satisfies the derivative condition on I_sup
  have f_sup_deriv_eq : ∀ t ∈ I_sup, HasDerivAt f_sup (v t (f_sup t)) t := by
    intro t ht
    rw [Set.mem_iUnion₂] at ht; rcases ht with ⟨p, hp, htp⟩
    have p_deriv : HasDerivAt p.f (v t (p.f t)) t := p.property.deriv_eq t htp
    have I_nhds_t : p.I ∈ 𝓝 t := p.property.isOpen.mem_nhds htp
    have f_sup_eq_pf_eventually : f_sup =ᶠ[𝓝 t] p.f := by
      filter_upwards [I_nhds_t] with y hy_in_pI
      have hy_in_I_sup : y ∈ I_sup := by rw [Set.mem_iUnion₂]; exact ⟨p, hp, hy_in_pI⟩
      simp only [exists_prop, f_sup, I_sup]; rw [dif_pos hy_in_I_sup]
      let existence_prop_y : ∃ p', p' ∈ C ∧ y ∈ p'.I := by
        rw [Set.mem_iUnion₂] at hy_in_I_sup; exact bex_def.mp hy_in_I_sup
      let p'_chosen := Classical.choose existence_prop_y
      have hp'_chosen_spec : p'_chosen ∈ C ∧ y ∈ p'_chosen.I :=
        Classical.choose_spec existence_prop_y
      apply (f_sup_well_defined y hy_in_I_sup p p'_chosen hp
        hp'_chosen_spec.1 hy_in_pI hp'_chosen_spec.2).symm
    have h_deriv_f_sup_intermediate : HasDerivAt f_sup (v t (p.f t)) t := by
      exact HasDerivAt.congr_of_eventuallyEq p_deriv f_sup_eq_pf_eventually
    have f_sup_eq_pft_at_t : f_sup t = p.f t := by
      have ht_in_I_sup : t ∈ I_sup := by rw [Set.mem_iUnion₂]; exact ⟨p, hp, htp⟩
      simp only [exists_prop, f_sup, I_sup]; rw [dif_pos ht_in_I_sup]
      let existence_prop_t : ∃ p', p' ∈ C ∧ t ∈ p'.I := by
          rw [Set.mem_iUnion₂] at ht_in_I_sup; exact bex_def.mp ht_in_I_sup
      let p'_chosen := Classical.choose existence_prop_t
      have hp'_chosen_spec : p'_chosen ∈ C ∧ t ∈ p'_chosen.I :=
        Classical.choose_spec existence_prop_t
      apply (f_sup_well_defined t ht_in_I_sup p p'_chosen hp
        hp'_chosen_spec.1 htp hp'_chosen_spec.2).symm
    rw [← f_sup_eq_pft_at_t] at h_deriv_f_sup_intermediate
    exact h_deriv_f_sup_intermediate

  -- Construct the supremum `LocalODESolution`
  refine {
    f := f_sup,
    I := I_sup,
    property := {
      isOpen := I_sup_isOpen,
      isConnected := I_sup_isConnected,
      t₀_mem := I_sup_t₀_mem,
      f_t₀ := f_sup_t₀,
      deriv_eq := f_sup_deriv_eq
    }
  }

open Classical in
/--
The `chainSup` construction provides an upper bound for any element `hp` in a non-empty chain `C`.
-/
lemma chainSup_is_upper_bound (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : let p_sup := chainSup v t₀ x₀ C hC hCne
    ∀ hp ∈ C, hp ≤ p_sup := by
  intro p_sup hp hpC -- p_sup is the supremum solution; hp is an element from the chain C.
  constructor
  · -- Part 1: Prove hp.I ⊆ p_sup.I
    intro t ht_in_hpI
    simp only [chainSup, mem_iUnion, p_sup] -- p_sup.I is I_sup
    use hp
  · -- Part 2: Prove EqOn hp.f p_sup.f hp.I
    intro t ht_in_hpI
    let f_sup := p_sup.f
    let I_sup := p_sup.I
    have ht_in_I_sup : t ∈ I_sup := by
      simp only [chainSup, mem_iUnion, exists_prop, I_sup, p_sup]; use hp
    have f_sup_eval_eq : f_sup t = (Classical.choose (Set.mem_iUnion₂.mp ht_in_I_sup)).f t := by
      have f_def : p_sup.f = fun t_ =>
        if ht' : t_ ∈ I_sup then (Classical.choose (Set.mem_iUnion₂.mp ht')).f t_ else x₀ := rfl
      simp only [f_sup]; rw [f_def]; exact dif_pos ht_in_I_sup
    simp [f_sup] at f_sup_eval_eq; rw [f_sup_eval_eq]
    let existence_prop_t := Set.mem_iUnion₂.mp ht_in_I_sup
    let p_chosen_for_t := Classical.choose existence_prop_t
    have p_chosen_for_t_spec := Classical.choose_spec existence_prop_t
    have f_sup_well_defined_at_t : ∀ (t' : ℝ) (ht' : t' ∈ I_sup) (p₁ p₂ : LocalODESolution v t₀ x₀)
        (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) (ht₁ : t' ∈ p₁.I) (ht₂ : t' ∈ p₂.I),
        p₁.f t' = p₂.f t' := by -- Copied from chainSup for local access
      intro t' ht' p₁ p₂ hp₁ hp₂ ht₁ ht₂; rcases hC.total hp₁ hp₂ with h12 | h21;
      exact h12.2 ht₁; exact (h21.2 ht₂).symm
    have final_eq : hp.f t = p_chosen_for_t.f t :=
      f_sup_well_defined_at_t t ht_in_I_sup hp p_chosen_for_t hpC
        p_chosen_for_t_spec.1 ht_in_hpI p_chosen_for_t_spec.2
    simp only [exists_prop, p_chosen_for_t] at final_eq
    exact final_eq

/--
Helper lemma stating that any non-empty chain `C` has an upper bound.
This is equivalent to `BddAbove C`.
-/
lemma chain_has_upper_bound_explicit (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : ∃ ub, ∀ p ∈ C, p ≤ ub := by
  use chainSup v t₀ x₀ C hC hCne
  exact chainSup_is_upper_bound v t₀ x₀ C hC hCne

/--
Chains of local ODE solutions are bounded above. This is the condition required by
`zorn_le_nonempty`.
-/
lemma chain_is_bddAbove (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : BddAbove C := by
  -- `BddAbove C` means `∃ x, ∀ y ∈ C, y ≤ x`.
  -- This is exactly what `chain_has_upper_bound_explicit` provides.
  exact chain_has_upper_bound_explicit v t₀ x₀ C hC hCne

/--
The main existence theorem for maximal solutions within this namespace.
It asserts that if Picard-Lindelöf conditions guarantee a local solution on an
open interval `(tMin, tMax)` containing `t₀`, then a maximal solution exists.
-/
theorem exists_maximal_solution
    [CompleteSpace E] (hpl_two_sided : ∃ (tMin tMax : ℝ) (L : ℝ≥0) (R C : ℝ),
                        (tMin < t₀ ∧ t₀ < tMax) ∧ IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v t₀ x₀ f I := by

  let S := LocalODESolution v t₀ x₀

  -- 1. Show S is non-empty using the guaranteed local solution from Picard-Lindelöf.
  have S_nonempty_instance : Nonempty S := by
    obtain ⟨tMin, tMax, L, R, C, ⟨⟨htMin_lt_t₀, ht₀_lt_tMax⟩, hpl_instance⟩⟩ := hpl_two_sided
    -- Picard-Lindelöf gives a solution `f₀` on `Icc tMin tMax`.
    rcases hpl_instance.exists_forall_hasDerivWithinAt_Icc_eq x₀ with ⟨f₀, hf₀_t₀, hf₀_deriv_within⟩
    -- We use the open interval `Ioo tMin tMax` for our `LocalODESolution`.
    let I_local := Ioo tMin tMax
    have I_local_open : IsOpen I_local := isOpen_Ioo
    have I_local_conn : IsConnected I_local := isConnected_Ioo (htMin_lt_t₀.trans ht₀_lt_tMax)
    have I_local_t₀_mem : t₀ ∈ I_local := ⟨htMin_lt_t₀, ht₀_lt_tMax⟩
    -- Convert `HasDerivWithinAt` on `Icc` to `HasDerivAt` on `Ioo`.
    have hf₀_deriv_at : ∀ t ∈ I_local, HasDerivAt f₀ (v t (f₀ t)) t := by
      intro t_mem_I_local ht_local_prop
      have ht_in_Icc : t_mem_I_local ∈ Icc tMin tMax := Ioo_subset_Icc_self ht_local_prop
      specialize hf₀_deriv_within t_mem_I_local ht_in_Icc
      -- Since `t_mem_I_local` is in the interior `I_local` of `Icc tMin tMax`,
      -- `HasDerivWithinAt` implies `HasDerivAt`.
      apply hf₀_deriv_within.hasDerivAt (Icc_mem_nhds ht_local_prop.1 ht_local_prop.2)
    -- Construct the initial `LocalODESolution`.
    let p₀ : LocalODESolution v t₀ x₀ := {
      f := f₀, I := I_local,
      property := { isOpen := I_local_open, isConnected :=
        I_local_conn, t₀_mem := I_local_t₀_mem, f_t₀ := hf₀_t₀, deriv_eq := hf₀_deriv_at }}
    exact ⟨p₀⟩

  -- 2. Apply Zorn's Lemma for Preorders (`zorn_le_nonempty`).
  -- This requires that every non-empty chain has an upper bound (`BddAbove`).
  rcases zorn_le_nonempty (chain_is_bddAbove v t₀ x₀) with
    ⟨maximal_element, h_is_max_elem : IsMax maximal_element⟩
    -- `h_is_max_elem` means `∀ (x : S), maximal_element ≤ x → x ≤ maximal_element`.

  -- 3. Show this `maximal_element` corresponds to an `IsMaximalODESolution`.
  use maximal_element.f, maximal_element.I
  constructor
  · -- The `maximal_element` is a `LocalODESolution`, so it satisfies `IsODESolution`.
    exact maximal_element.property
  · -- Prove the maximality condition.
    intro g J hg_sol hIJ_subset h_eq_on_I
    -- Assume, for contradiction, that `I ≠ J`.
    by_contra h_I_ne_J
    -- Construct a `LocalODESolution` from `(g, J)`.
    let p_g : LocalODESolution v t₀ x₀ := { f := g, I := J, property := hg_sol }
    -- By assumption, `maximal_element ≤ p_g`.
    have h_maximal_le_pg : maximal_element ≤ p_g := ⟨hIJ_subset, h_eq_on_I⟩
    -- Since `maximal_element` is `IsMax`, `maximal_element ≤ p_g` implies `p_g ≤ maximal_element`.
    have h_pg_le_maximal : p_g ≤ maximal_element := h_is_max_elem h_maximal_le_pg
    -- `p_g ≤ maximal_element` means `p_g.I ⊆ maximal_element.I`, i.e., `J ⊆ maximal_element.I`.
    have hJ_subset_I : J ⊆ maximal_element.I := h_pg_le_maximal.1
    -- We have `maximal_element.I ⊆ J` (from `hIJ_subset`) and `J ⊆ maximal_element.I`.
    -- Thus, their domains are equal.
    have h_I_eq_J : maximal_element.I = J := Set.Subset.antisymm hIJ_subset hJ_subset_I
    -- This contradicts the assumption `h_I_ne_J`.
    exact h_I_ne_J h_I_eq_J

end MaximalSolutionExistence

/--
Under the conditions of the Picard-Lindelöf theorem (specifically, ensuring local existence
on an open interval around `t₀`), there exists a maximal solution to the ODE `x' = v(t, x)`
with initial condition `f(t₀) = x₀`.
-/
theorem exists_maximal_ode_solution [CompleteSpace E]
    (hpl : ∃ (tMin tMax : ℝ) (L : ℝ≥0) (R C : ℝ),
    (tMin < t₀ ∧ t₀ < tMax) ∧ IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v t₀ x₀ f I :=
  MaximalSolutionExistence.exists_maximal_solution v t₀ x₀ hpl

end noncomputable section
