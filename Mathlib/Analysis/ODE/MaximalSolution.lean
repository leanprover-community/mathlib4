/-
Copyright (c) 2025 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
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

* Tie to Grönwall's inequality for uniqueness arguments, particularly for showing that any two
  solutions (under appropriate Lipschitz conditions) must agree on the intersection of their
  domains. This underpins the coherence of extending solutions.
* Connect to global existence theorems and criteria for when the maximal interval of existence
  is `(-∞, ∞)`.
-/

open Set Filter Topology TopologicalSpace

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
A solution `(f, I)` to the ODE `x' = v(t, x)` with initial value `(t₀, x₀)` is maximal if it
cannot be extended to a solution on any strictly larger open connected domain `J`.
-/
structure IsMaximalODESolution (f : ℝ → E) (I : Set ℝ) : Prop
  extends IsODESolution v t₀ x₀ f I where
  /-- The maximality condition: If `(g, J)` is another solution such that `I ⊆ J` and `f` agrees
  with `g` on `I`, then `I` must be equal to `J`. -/
  is_maximal : ∀ (g : ℝ → E) (J : Set ℝ), IsODESolution v t₀ x₀ g J → I ⊆ J → (EqOn f g I) → I = J

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
    [CompleteSpace E] (hpl_two_sided : ∃ (tMin tMax : ℝ) (L : NNReal) (R C : ℝ),
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
    (hpl : ∃ (tMin tMax : ℝ) (L : NNReal) (R C : ℝ),
    (tMin < t₀ ∧ t₀ < tMax) ∧ IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v t₀ x₀ f I :=
  MaximalSolutionExistence.exists_maximal_solution v t₀ x₀ hpl

end noncomputable section
