/-
Copyright (c) 2025 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Zorn -- For Zorn's Lemma
import Mathlib.Topology.Connected.Basic -- For interval properties
import Mathlib.Topology.Instances.Real.Lemmas -- For properties of intervals

/-!
# Maximal Solutions to Ordinary Differential Equations

This file defines the concept of a maximal solution to an ODE `x' = v(t, x)` with initial
condition `x(t₀) = x₀`. It proves that under the conditions of the Picard-Lindelöf theorem,
such a maximal solution exists.

The strategy involves using Zorn's Lemma on the set of all local solutions extending the initial
condition. Picard-Lindelöf provides the existence of at least one local solution, making the set
non-empty.

## Main Definitions

* `IsODESolution`: Predicate stating that a function `f` is a solution to the ODE on an open
  interval `I`.
* `IsMaximalODESolution`: Predicate stating that a solution `(f, I)` cannot be extended to a
  strictly larger open interval.

## Main Theorem

* `exists_maximal_solution`: Under Picard-Lindelöf conditions, there exists a function `f` and an
  open interval `I` such that `(f, I)` is a maximal solution.

## TODO

* Tie to Grönwall for uniqueness.
* Connect to global existence theorems.
-/

open Set Filter Topology TopologicalSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E)

/--
A function `f` is a solution to the ODE `x' = v(t, x)` with initial value `(t₀, x₀)` on an
open interval `I`.
-/
structure IsODESolution (f : ℝ → E) (I : Set ℝ) : Prop where
  /-- The domain `I` must be an open set. -/
  isOpen : IsOpen I
  /-- The domain `I` must be connected (ensuring it's an interval). -/
  isConnected : IsConnected I
  /-- The initial time `t₀` must be in the interval `I`. -/
  t₀_mem : t₀ ∈ I
  /-- The solution must satisfy the initial condition `f(t₀) = x₀`. -/
  f_t₀ : f t₀ = x₀
  /-- The function `f` must have the derivative `v(t, f(t))` at every point `t` in `I`. -/
  deriv_eq : ∀ t ∈ I, HasDerivAt f (v t (f t)) t

lemma IsODESolution.continuousOn {f : ℝ → E} {I : Set ℝ} (h_sol : IsODESolution v t₀ x₀ f I) :
    ContinuousOn f I := by
  intro t ht
  exact (h_sol.deriv_eq t ht).continuousAt.continuousWithinAt

/--
A solution `(f, I)` to the ODE `x' = v(t, x)` with initial value `(t₀, x₀)` is maximal if it
cannot be extended to a strictly larger open interval.
-/
structure IsMaximalODESolution (f : ℝ → E) (I : Set ℝ) : Prop
  extends IsODESolution v t₀ x₀ f I where
  /-- The maximality condition: No other solution `(g, J)` extends `(f, I)` to a strictly larger
  interval `J`. -/
  is_maximal : ∀ (g : ℝ → E) (J : Set ℝ), IsODESolution v t₀ x₀ g J → I ⊆ J → (EqOn f g I) → I = J

/-! ### Proof of Existence of Maximal Solutions -/

namespace MaximalSolutionExistence

-- Define the type of local solutions
structure LocalODESolution where
  protected f : ℝ → E
  protected I : Set ℝ
  protected property : IsODESolution v t₀ x₀ f I

-- Define the extension relation (≤)
def ODESolutionExtends (p₁ p₂ : LocalODESolution v t₀ x₀) : Prop :=
  p₁.I ⊆ p₂.I ∧ (EqOn p₁.f p₂.f p₁.I)

-- Define LE instance using the extension relation
instance : LE (LocalODESolution v t₀ x₀) where
  le := ODESolutionExtends v t₀ x₀

-- Now define the Preorder instance
instance : Preorder (LocalODESolution v t₀ x₀) where
  le := ODESolutionExtends v t₀ x₀ -- Explicitly state which relation is '≤'
  le_refl := fun p => by
    -- Goal: p ≤ p, which means ODESolutionExtends p p
    -- Definition: p.I ⊆ p.I ∧ EqOn p.f p.f p.I
    constructor
    · -- Prove p.I ⊆ p.I
      exact Set.Subset.refl _ -- Use reflexivity of subset relation
    · -- Prove EqOn p.f p.f p.I
      exact fun ⦃x⦄ ↦ congrFun rfl
  le_trans := fun p₁ p₂ p₃ h₁₂ h₂₃ => by
    -- Goal: p₁ ≤ p₃, which means ODESolutionExtends p₁ p₃
    -- Definition: p₁.I ⊆ p₃.I ∧ EqOn p₁.f p₃.f p₁.I
    -- h₁₂ : p₁ ≤ p₂ means h₁₂.1 : p₁.I ⊆ p₂.I and h₁₂.2 : EqOn p₁.f p₂.f p₁.I
    -- h₂₃ : p₂ ≤ p₃ means h₂₃.1 : p₂.I ⊆ p₃.I and h₂₃.2 : EqOn p₂.f p₃.f p₂.I
    constructor
    · -- Prove p₁.I ⊆ p₃.I
      exact Set.Subset.trans h₁₂.1 h₂₃.1 -- Use transitivity of subset relation
    · -- Prove EqOn p₁.f p₃.f p₁.I
      intro t ht -- Take an arbitrary t in p₁.I
      -- Goal: p₁.f t = p₃.f t
      have h_t_in_p₂I : t ∈ p₂.I := h₁₂.1 ht -- Since p₁.I ⊆ p₂.I
      have eq₁₂ : p₁.f t = p₂.f t := h₁₂.2 ht -- Apply EqOn from h₁₂
      have eq₂₃ : p₂.f t = p₃.f t := h₂₃.2 h_t_in_p₂I -- Apply EqOn from h₂₃
      exact Eq.trans eq₁₂ eq₂₃ -- Use transitivity of equality
  -- lt and lt_iff_le_not_le will use the default definitions based on the provided 'le'

/--
The equivalence relation `≈` on local ODE solutions.
Two solutions are equivalent if they are extensions of each other, meaning
they have the same interval and agree on that interval.
-/
instance LocalODESolutionSetoid : Setoid (LocalODESolution v t₀ x₀) where
  r p₁ p₂ := p₁ ≤ p₂ ∧ p₂ ≤ p₁ -- Two solutions are related if p₁ ≤ p₂ and p₂ ≤ p₁
  iseqv := {
    refl := fun p => by
      -- Goal: p ≈ p, which means p ≤ p ∧ p ≤ p
      constructor
      · exact le_refl p -- from the Preorder instance
      · exact le_refl p
    symm := fun {p₁ p₂} h => by
      -- Goal: p₂ ≈ p₁ given h : p₁ ≈ p₂
      -- h is p₁ ≤ p₂ ∧ p₂ ≤ p₁
      -- Goal is p₂ ≤ p₁ ∧ p₁ ≤ p₂
      exact And.symm h -- The definition is symmetric
    trans := fun {p₁ p₂ p₃} h₁₂ h₂₃ => by
      -- Goal: p₁ ≈ p₃ given h₁₂ : p₁ ≈ p₂ and h₂₃ : p₂ ≈ p₃
      -- h₁₂ : p₁ ≤ p₂ ∧ p₂ ≤ p₁
      -- h₂₃ : p₂ ≤ p₃ ∧ p₃ ≤ p₂
      -- Goal: p₁ ≤ p₃ ∧ p₃ ≤ p₁
      constructor
      · -- Prove p₁ ≤ p₃
        exact le_trans h₁₂.1 h₂₃.1 -- Uses transitivity from Preorder
      · -- Prove p₃ ≤ p₁
        exact le_trans h₂₃.2 h₁₂.2 -- Uses transitivity from Preorder
  }

/--
The quotient type of local ODE solutions, where solutions that are extensions
of each other are identified. This type carries the structure of a partial order.
-/
abbrev QuotientLocalODESolution := Quotient (LocalODESolutionSetoid (v:=v) (t₀:=t₀) (x₀:=x₀))

instance QuotientLocalODESolution.instLE : LE (QuotientLocalODESolution v t₀ x₀) where
  le := Quotient.lift₂
    (fun p₁ p₂ => p₁ ≤ p₂) -- The underlying relation on representatives
    (by -- Proof that the relation is well-defined on equivalence classes
      intro a₁ a₂ b₁ b₂ hab hcd
      -- Goal: (a₁ ≤ a₂) ↔ (b₁ ≤ b₂)
      -- hab : a₁ ≈ b₁  (i.e., a₁ ≤ b₁ ∧ b₁ ≤ a₁)
      -- hcd : a₂ ≈ b₂  (i.e., a₂ ≤ b₂ ∧ b₂ ≤ a₂)

      -- Use Iff.intro to prove both directions
      apply propext
      apply Iff.intro

      · -- Prove (a₁ ≤ a₂) → (b₁ ≤ b₂)
        intro h_a1_le_a2 -- Assume a₁ ≤ a₂
        -- We want to show b₁ ≤ b₂.
        -- We know b₁ ≤ a₁ (from hab.2)
        -- We know a₁ ≤ a₂ (assumption h_a1_le_a2)
        -- We know a₂ ≤ b₂ (from hcd.1)
        -- Chain these: b₁ ≤ a₁ ≤ a₂ ≤ b₂
        calc
          b₁ ≤ a₁ := hab.2
          _  ≤ a₂ := h_a1_le_a2
          _  ≤ b₂ := hcd.1

      · -- Prove (b₁ ≤ b₂) → (a₁ ≤ a₂)
        intro h_b1_le_b2 -- Assume b₁ ≤ b₂
        -- We want to show a₁ ≤ a₂.
        -- We know a₁ ≤ b₁ (from hab.1)
        -- We know b₁ ≤ b₂ (assumption h_b1_le_b2)
        -- We know b₂ ≤ a₂ (from hcd.2)
        -- Chain these: a₁ ≤ b₁ ≤ b₂ ≤ a₂
        calc
          a₁ ≤ b₁ := hab.1
          _  ≤ b₂ := h_b1_le_b2
          _  ≤ a₂ := hcd.2
    )

/--
The set of local ODE solutions modulo the extension equivalence relation forms a partial order.
The order `⟦p₁⟧ ≤ ⟦p₂⟧` is induced by the preorder relation `p₁ ≤ p₂` on the representatives.
Mathlib provides the construction `Quotient.instPartialOrderLe` which is found automatically.
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


-- Key step: Show chains have upper bounds
-- Let C be a chain of LocalODESolution
open Classical in
def chainSup (C : Set (LocalODESolution v t₀ x₀)) (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
    LocalODESolution v t₀ x₀ := by
  -- Define the union interval
  let I_sup := ⋃ (p : LocalODESolution v t₀ x₀) (hp : p ∈ C), p.I
  -- Define the glued function
  let f_sup : ℝ → E := fun t =>
    -- Find some element p in the chain C whose interval I contains t
    -- and return p.f t. This needs to be well-defined.
    if ht : t ∈ I_sup then
      let p_data := Classical.choose (Set.mem_iUnion₂.mp ht) -- p : LocalODESolution...
      let hp_proofs := Classical.choose_spec (Set.mem_iUnion₂.mp ht) -- ⟨hp : p ∈ C, htp : t ∈ p.I⟩
      p_data.f t
    else
      -- Arbitrary value outside the domain, x₀ is a reasonable choice
      x₀

  -- Prove I_sup is an open interval containing t₀
  have I_sup_isOpen : IsOpen I_sup :=
    isOpen_iUnion fun p => isOpen_iUnion fun _ => p.property.isOpen
  have I_sup_isConnected : IsConnected I_sup := by
      -- 1. Prove Nonempty
      have hne : I_sup.Nonempty := by
        obtain ⟨p, hp⟩ := hCne
        exact ⟨t₀, Set.mem_biUnion hp p.property.t₀_mem⟩

      -- 2. Prove Preconnected using common point t₀
      -- Let c be the collection of intervals directly via image
      let c : Set (Set ℝ) := LocalODESolution.I '' C
      have h_common_pt : ∀ s ∈ c, t₀ ∈ s := by
        rintro s ⟨p, hp, rfl⟩ -- s takes the form p.I for some p ∈ C
        exact p.property.t₀_mem
      have h_preconn : ∀ s ∈ c, IsPreconnected s := by
        rintro s ⟨p, hp, rfl⟩ -- s takes the form p.I for some p ∈ C
        exact p.property.isConnected.isPreconnected -- Each p.I is connected, hence preconnected

      have h_preconn_union : IsPreconnected I_sup := by
          -- Prove that I_sup is the sUnion of the image collection c
          have I_sup_eq_sUnion_c : I_sup = ⋃₀ c := by
            ext x
            -- Show (∃ p ∈ C, x ∈ p.I) ↔ (∃ s ∈ c, x ∈ s)
            -- Using c = LocalODESolution.I '' C
            -- Show (∃ p ∈ C, x ∈ p.I) ↔ (∃ s ∈ LocalODESolution.I '' C, x ∈ s)
            simp only [mem_iUnion, exists_prop, mem_sUnion, I_sup]
            -- Goal is now: (∃ p, p ∈ C ∧ x ∈ p.I) ↔ (∃ s, (∃ p', p' ∈ C ∧ p'.I = s) ∧ x ∈ s)
            constructor
            · rintro ⟨p, hp, hx⟩
              -- Need: ∃ s, (∃ p', p' ∈ C ∧ p'.I = s) ∧ x ∈ s
              use p.I -- Witness for s is p.I
              constructor
              · -- Prove p.I is in the image (witness is p itself)
                use p
              · -- Prove x ∈ p.I
                exact hx
            · rintro ⟨s, ⟨p', hp', rfl⟩, hx_in_s⟩ -- Here s = p'.I
              -- Need: ∃ p, p ∈ C ∧ x ∈ p.I
              use p' -- hx_in_s is x ∈ p'.I
          rw [I_sup_eq_sUnion_c]
          exact isPreconnected_sUnion t₀ c h_common_pt h_preconn

      -- Combine non-empty and preconnected
      exact ⟨hne, h_preconn_union⟩

  have I_sup_t₀_mem : t₀ ∈ I_sup := by
    obtain ⟨p, hp⟩ := hCne
    exact Set.mem_iUnion₂.mpr ⟨p, hp, p.property.t₀_mem⟩

  -- Prove f_sup is well-defined on I_sup
  -- This requires uniqueness (Grönwall)
  -- Need a lemma: If (f₁, I₁) ≤ (f₂, I₂) and t ∈ I₁, then f₁(t) = f₂(t) -- True by definition
  -- Need a lemma: If t ∈ I₁ and t ∈ I₂, then for p₁, p₂ ∈ C, f₁(t) = f₂(t)
  -- Because C is a chain, either p₁ ≤ p₂ or p₂ ≤ p₁.
  -- Assume p₁ ≤ p₂, then I₁ ⊆ I₂ and f₁ = f₂ on I₁.
  -- So f₁(t) = f₂(t).
  have f_sup_well_defined : ∀ (t : ℝ) (ht : t ∈ I_sup) (p₁ p₂ : LocalODESolution v t₀ x₀)
      (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) (ht₁ : t ∈ p₁.I) (ht₂ : t ∈ p₂.I),
      p₁.f t = p₂.f t := by
    intro t ht p₁ p₂ hp₁ hp₂ ht₁ ht₂
    rcases hC.total hp₁ hp₂ with h12 | h21
    · exact h12.2 ht₁
    · symm
      exact h21.2 ht₂ -- Apply symmetry here

  -- Prove f_sup satisfies the initial condition
  have f_sup_t₀ : f_sup t₀ = x₀ := by
      have ht₀_mem : t₀ ∈ I_sup := I_sup_t₀_mem
      -- Manually unfold the definition of f_sup at the specific point t₀
      unfold f_sup
      -- Simplify the 'if' expression using the known condition ht₀_mem.
      -- 'dif_pos' requires the condition directly.
      rw [dif_pos ht₀_mem]
      -- The goal is now the body of the 'then' branch:
      -- (let p_data := Classical.choose (Set.mem_iUnion₂.mp ht₀_mem);
      --  let hp_proofs := Classical.choose_spec (Set.mem_iUnion₂.mp ht₀_mem);
      --  p_data.f t₀) = x₀

      -- Use the definition of the 'let' bindings.
      -- The expression is definitionally equal to p.f t₀ where p is the element chosen.
      -- We can directly use the properties of the chosen element.
      let p := Classical.choose (Set.mem_iUnion₂.mp ht₀_mem)
      -- 'p' is the chosen LocalODESolution.
      -- The proof 'hp_spec' (which we don't explicitly need here) confirms
      -- p satisfies the existence property (p ∈ C ∧ t₀ ∈ p.I).

      -- We need to show p.f t₀ = x₀.
      -- This holds because p is a LocalODESolution, and its 'property' field
      -- includes 'f_t₀ : p.f t₀ = x₀'.
      exact p.property.f_t₀


  -- Prove f_sup satisfies the derivative condition
  have f_sup_deriv_eq : ∀ t ∈ I_sup, HasDerivAt f_sup (v t (f_sup t)) t := by
    intro t ht -- ht : t ∈ ⋃ (p : LocalODESolution v t₀ x₀) (_hp : p ∈ C), p.I
    -- 1. Get p, hp, htp from ht
    -- We use Set.mem_iUnion₂ which is the underlying iff lemma for the structure of I_sup
    rw [Set.mem_iUnion₂] at ht -- ht : ∃ p (_ : p ∈ C), t ∈ p.I
    rcases ht with ⟨p, hp, htp⟩ -- p: Local..., hp: p ∈ C, htp: t ∈ p.I

    -- 2. State the derivative property of p.f (this comes from p being a LocalODESolution)
    have p_deriv : HasDerivAt p.f (v t (p.f t)) t := p.property.deriv_eq t htp

    -- 3. Show f_sup agrees with p.f in a neighborhood of t
    -- Since p.I is open (by p.property.isOpen) and contains t (by htp), p.I is a neighborhood of t.
    have I_nhds_t : p.I ∈ 𝓝 t := p.property.isOpen.mem_nhds htp

    -- We want to show f_sup y = p.f y for y in a neighborhood of t (specifically, for y ∈ p.I)
    have f_sup_eq_pf_eventually : f_sup =ᶠ[𝓝 t] p.f := by
      filter_upwards [I_nhds_t] with y hy_in_pI
      -- First, establish y ∈ I_sup since y ∈ p.I and p ∈ C
      have hy_in_I_sup : y ∈ I_sup := by rw [Set.mem_iUnion₂]; exact ⟨p, hp, hy_in_pI⟩

      -- Now, unfold the definition of f_sup y using the `if ht : t ∈ I_sup` structure
      simp only [exists_prop, f_sup, I_sup]
      rw [dif_pos hy_in_I_sup]

      -- Inside the `if`, f_sup y is defined as:
      -- let existence_prop_y : ∃ p', p' ∈ C ∧ y ∈ p'.I :=
      --   by { rw [Set.mem_iUnion₂] at hy_in_I_sup; exact hy_in_I_sup }
      -- let p'_chosen := Classical.choose existence_prop_y
      -- p'_chosen.f y
      -- We need to show this value equals p.f y.

      -- Let's formally define p'_chosen based on the definition of f_sup applied to y
      let existence_prop_y : ∃ p', p' ∈ C ∧ y ∈ p'.I := by
        rw [Set.mem_iUnion₂] at hy_in_I_sup; exact bex_def.mp hy_in_I_sup
      let p'_chosen := Classical.choose existence_prop_y
      have hp'_chosen_spec : p'_chosen ∈ C ∧ y ∈ p'_chosen.I :=
        Classical.choose_spec existence_prop_y

      -- The term computed by f_sup is p'_chosen.f y.
      -- We use f_sup_well_defined to show this equals p.f y.
      -- Arguments for f_sup_well_defined: y, hy_in_I_sup, p, p'_chosen, hp,
      -- hp'_chosen_spec.1, hy_in_pI, hp'_chosen_spec.2
      apply (f_sup_well_defined y hy_in_I_sup p p'_chosen hp
        hp'_chosen_spec.1 hy_in_pI hp'_chosen_spec.2).symm

    -- 4. Apply the congruence lemma for derivatives
    -- HasDerivAt.congr_of_eventuallyEq : HasDerivAt g g' x → f =ᶠ[𝓝 x] g → HasDerivAt f g' x
    -- Here g = p.f, g' = v t (p.f t), f = f_sup
    have h_deriv_f_sup_intermediate : HasDerivAt f_sup (v t (p.f t)) t := by
      exact HasDerivAt.congr_of_eventuallyEq p_deriv f_sup_eq_pf_eventually

    -- 5. Show f_sup t = p.f t
    -- This is needed to substitute inside the derivative expression v t (...)
    have f_sup_eq_pft_at_t : f_sup t = p.f t := by
      -- First, re-establish t ∈ I_sup for the context of the `dif_pos`
      have ht_in_I_sup : t ∈ I_sup := by rw [Set.mem_iUnion₂]; exact ⟨p, hp, htp⟩
      simp only [exists_prop, f_sup, I_sup]
      rw [dif_pos ht_in_I_sup]
      -- Mirror the logic from f_sup_eq_pf_eventually, but for the specific point t
      let existence_prop_t : ∃ p', p' ∈ C ∧ t ∈ p'.I := by
          rw [Set.mem_iUnion₂] at ht_in_I_sup; exact bex_def.mp ht_in_I_sup
      let p'_chosen := Classical.choose existence_prop_t
      have hp'_chosen_spec : p'_chosen ∈ C ∧ t ∈ p'_chosen.I :=
        Classical.choose_spec existence_prop_t
      -- Show the chosen value p'_chosen.f t equals p.f t using well-definedness
      apply (f_sup_well_defined t ht_in_I_sup p p'_chosen hp
        hp'_chosen_spec.1 htp hp'_chosen_spec.2).symm

    -- 6. Rewrite the result from step 4 using the equality from step 5
    -- We have HasDerivAt f_sup (v t (p.f t)) t and f_sup t = p.f t
    -- We want HasDerivAt f_sup (v t (f_sup t)) t
    rw [← f_sup_eq_pft_at_t] at h_deriv_f_sup_intermediate
    exact h_deriv_f_sup_intermediate

  -- Construct the supremum element
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
The `chainSup` construction provides an upper bound for any non-empty chain
of local ODE solutions.
-/
lemma chainSup_is_upper_bound (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : let p := chainSup v t₀ x₀ C hC hCne
    ∀ hp ∈ C, hp ≤ p := by
  -- Introduce the upper bound candidate explicitly
  intro p hp hpC
  -- Goal: Show hp ≤ p, which means ODESolutionExtends hp p
  -- Definition: hp.I ⊆ p.I ∧ EqOn hp.f p.f p.I

  constructor -- Need to prove both parts of the conjunction

  · -- Part 1: Prove hp.I ⊆ p.I
    show hp.I ⊆ p.I -- p.I is I_sup by definition of chainSup
    intro t ht_in_pI -- Take an arbitrary t in p.I
    -- Goal: Show t ∈ p.I = ⋃ (q) (hq : q ∈ C), q.I
    simp only [chainSup, mem_iUnion, p]
    -- Goal: ∃ q, q ∈ C ∧ t ∈ q.I
    use hp -- Choose q = p

  · -- Part 2: Prove EqOn hp.f p.f hp.I
    show EqOn hp.f p.f hp.I
    intro t ht_in_pI -- Take an arbitrary t in hp.I
    -- Goal: hp.f t = p.f t

    -- Get p.f (which is f_sup) and p.I (which is I_sup)
    let f_sup := p.f
    let I_sup := p.I

    -- Establish t ∈ I_sup
    have ht_in_I_sup : t ∈ I_sup := by
      -- Reuse the logic from Part 1: Since t ∈ p.I and p ∈ C, t is in the union I_sup
      simp only [chainSup, mem_iUnion, exists_prop, I_sup, p]
      use hp

    -- Apply the definition of f_sup t. We need to access how f_sup was defined inside chainSup.
    -- This requires reasoning about the definition 'ub.f t' based on its construction.
    -- Let's repeat the definition logic for clarity:
    -- ub.f t = if ht' : t ∈ I_sup then (Classical.choose ...).f t else x₀
    have f_sup_eval_eq : f_sup t = (Classical.choose (Set.mem_iUnion₂.mp ht_in_I_sup)).f t := by
      -- This follows from the definition of f_sup in chainSup and using dif_pos
      simp only [f_sup] -- Unfold f_sup definitionally if possible or use helper lemma
      -- Need to refer back to the structure of `chainSup`.
      -- Let's state the definition property more directly
      have f_def : p.f = fun t_ =>
        if ht' : t_ ∈ I_sup then (Classical.choose (Set.mem_iUnion₂.mp ht')).f t_ else x₀ := rfl
      rw [f_def]
      exact dif_pos ht_in_I_sup

    simp [f_sup] at f_sup_eval_eq
    rw [f_sup_eval_eq]

    -- Let hp_chosen be the element chosen by Classical.choose for this t
    let existence_prop_t := Set.mem_iUnion₂.mp ht_in_I_sup
    let hp_chosen := Classical.choose existence_prop_t
    -- hp_chosen_spec is the proof that hp_chosen satisfies the property:
    -- hp_chosen_spec : hp_chosen ∈ C ∧ t ∈ hp_chosen.I
    have hp_chosen_spec := Classical.choose_spec existence_prop_t

    -- We need the well-definedness proof again here.
    have f_sup_well_defined : ∀ (t' : ℝ) (ht' : t' ∈ I_sup) (p₁ p₂ : LocalODESolution v t₀ x₀)
        (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) (ht₁ : t' ∈ p₁.I) (ht₂ : t' ∈ p₂.I),
        p₁.f t' = p₂.f t' := by
      intro t' ht' p₁ p₂ hp₁ hp₂ ht₁ ht₂; rcases hC.total hp₁ hp₂ with h12 | h21;
      exact h12.2 ht₁; exact (h21.2 ht₂).symm

    -- Use f_sup_well_defined to show hp.f t = hp_chosen.f t
    -- Arguments: t, ht_in_I_sup, p₁=hp, p₂=hp_chosen,
    -- hp₁=hpC, hp₂=hp_chosen_spec.1 (proof that hp_chosen ∈ C)
    -- ht₁=ht_in_pI, ht₂=hp_chosen_spec.2 (proof that t ∈ hp_chosen.I)
    have final_eq : hp.f t = hp_chosen.f t :=
      f_sup_well_defined t ht_in_I_sup hp hp_chosen hpC hp_chosen_spec.1 ht_in_pI hp_chosen_spec.2

    -- The goal is hp.f t = (choose existence_prop_t).f t
    -- Since hp_chosen := choose existence_prop_t, the equality `final_eq` is exactly the goal.
    simp only [exists_prop, hp_chosen] at final_eq
    exact final_eq

/--
Helper lemma providing the existence of an upper bound for any non-empty chain,
formatted for use with `zorn_partialOrder_of_nonempty_chains`.
-/
lemma chain_has_upper_bound (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : ∃ ub, ∀ p ∈ C, p ≤ ub := by
  use chainSup v t₀ x₀ C hC hCne -- Use the constructed supremum
  -- Apply the proof that it is indeed an upper bound
  exact chainSup_is_upper_bound v t₀ x₀ C hC hCne

/-- Chains of local ODE solutions are bounded above. -/
lemma chain_is_bddAbove (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : BddAbove C := by
  use chainSup v t₀ x₀ C hC hCne
  exact chainSup_is_upper_bound v t₀ x₀ C hC hCne

-- The main existence theorem
/--
Under the conditions of the Picard-Lindelöf theorem, there exists a maximal solution
to the ODE `x' = v(t, x)` with initial condition `f(t₀) = x₀`.
-/
theorem exists_maximal_solution
    [CompleteSpace E] (hpl_two_sided : ∃ (tMin tMax : ℝ) (L : NNReal) (R C : ℝ),
                        (tMin < t₀ ∧ t₀ < tMax) ∧ IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v t₀ x₀ f I := by

  -- Define the set of local solutions
  let S := LocalODESolution v t₀ x₀

  have S_nonempty_instance : Nonempty S := by
    obtain ⟨tMin, tMax, L, R, C, ⟨⟨htMin_lt_t₀, ht₀_lt_tMax⟩, hpl_instance⟩⟩ := hpl_two_sided
    rcases hpl_instance.exists_forall_hasDerivWithinAt_Icc_eq x₀ with ⟨f₀, hf₀_t₀, hf₀_deriv_within⟩
    let I_local := Ioo tMin tMax
    have I_local_open : IsOpen I_local := isOpen_Ioo
    have I_local_conn : IsConnected I_local := isConnected_Ioo (htMin_lt_t₀.trans ht₀_lt_tMax)
    have I_local_t₀_mem : t₀ ∈ I_local := ⟨htMin_lt_t₀, ht₀_lt_tMax⟩
    have hf₀_deriv_at : ∀ t ∈ I_local, HasDerivAt f₀ (v t (f₀ t)) t := by
      intro t_mem_I_local ht_local_prop
      have ht_in_Icc : t_mem_I_local ∈ Icc tMin tMax := Ioo_subset_Icc_self ht_local_prop
      specialize hf₀_deriv_within t_mem_I_local ht_in_Icc
      apply hf₀_deriv_within.hasDerivAt (Icc_mem_nhds ht_local_prop.1 ht_local_prop.2)
    let p₀ : LocalODESolution v t₀ x₀ := {
      f := f₀, I := I_local,
      property := { isOpen := I_local_open, isConnected :=
        I_local_conn, t₀_mem := I_local_t₀_mem, f_t₀ := hf₀_t₀, deriv_eq := hf₀_deriv_at }}
    exact ⟨p₀⟩

  -- Apply Zorn's Lemma for Preorders
  -- zorn_le_nonempty needs [Nonempty S] and (∀ c, IsChain c → c.Nonempty → BddAbove c)
  -- h_maximal will be of type IsMax maximal_element
  rcases zorn_le_nonempty (chain_is_bddAbove v t₀ x₀) with
    ⟨maximal_element, h_is_max_elem : IsMax maximal_element⟩

  use maximal_element.f, maximal_element.I
  constructor
  · exact maximal_element.property
  · intro g J hg_sol hIJ_subset h_eq_on_I
    by_contra h_I_ne_J
    let p_g : LocalODESolution v t₀ x₀ := { f := g, I := J, property := hg_sol }
    have h_maximal_le_pg : maximal_element ≤ p_g := ⟨hIJ_subset, h_eq_on_I⟩
    -- From IsMax: maximal_element ≤ p_g → p_g ≤ maximal_element
    have h_pg_le_maximal : p_g ≤ maximal_element := h_is_max_elem h_maximal_le_pg
    -- p_g ≤ maximal_element means p_g.I ⊆ maximal_element.I (i.e., J ⊆ I)
    have hJ_subset_I : J ⊆ maximal_element.I := h_pg_le_maximal.1
    -- We have I ⊆ J (hIJ_subset) and J ⊆ I (hJ_subset_I)
    have h_I_eq_J : maximal_element.I = J := Set.Subset.antisymm hIJ_subset hJ_subset_I
    exact h_I_ne_J h_I_eq_J

end MaximalSolutionExistence

-- Export the main theorem
theorem exists_maximal_ode_solution [CompleteSpace E]
    (hpl : ∃ (tMin tMax : ℝ) (L : NNReal) (R C : ℝ),
    (tMin < t₀ ∧ t₀ < tMax) ∧ IsPicardLindelof v tMin t₀ tMax x₀ L R C) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v t₀ x₀ f I :=
  MaximalSolutionExistence.exists_maximal_solution v t₀ x₀ hpl

end noncomputable section
