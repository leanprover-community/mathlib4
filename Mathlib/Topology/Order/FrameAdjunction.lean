import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sober

import Mathlib.Tactic

universe u
variable (X : Type u)

open Set
open TopologicalSpace
/- For any point x of the space, we get a frame homomorphism χ x : Ω X -> 2. -/

@[reducible]
def pt (L : Type _) [Order.Frame L] := FrameHom L Prop

def χ {τ : TopologicalSpace X}  : X → pt τ.Opens :=
by {
  intro x
  refine { toFun := fun U ↦ x ∈ U, map_inf' := ?_, map_top' := ?_, map_sSup' := ?_ }
  all_goals try { intros ; simp ; try rfl }
  simp
  intro S; apply Iff.intro
  intro h; exists true; simp; assumption
  tauto
}

/- We record the definition of χ as a theorem. -/
theorem χ_ext {τ : TopologicalSpace X} {U : τ.Opens} : (χ X x) U = (x ∈ U) := rfl

/- Inseparability means equality of χ. -/
theorem inseparable_iff_χ_equal {τ : TopologicalSpace X} : 
  ∀ x y : X, (Inseparable x y ↔ (@χ X τ x = @χ X τ y)) := by
{ 
  intros x y
  rw [inseparable_iff_forall_open]
  apply Iff.intro; intro h; ext U; apply h U.1 U.2
  intro h U hU
  let Uo : τ.Opens := TopologicalSpace.Opens.mk U hU
  have heq : χ X x Uo = χ X y Uo := by rw [h]
  rw [χ_ext, χ_ext] at heq; simp at heq; exact heq
}

/- A space is T0 if and only if χ is an injective function. -/
theorem T0_iff_χInjective {τ : TopologicalSpace X } : (T0Space X ↔ Function.Injective (@χ X τ)) := by
{
  rw [t0Space_iff_inseparable, Function.Injective]
  have h := @inseparable_iff_χ_equal X τ 
  simp_all only
}


-- question: how to make the intersection of a finite collection of opens?
theorem isIrreducible_iff_sInf_Opens [α: TopologicalSpace X] {s : Set X} :
    IsIrreducible s ↔
      ∀ (U : Finset (Opens X)), (∀ u ∈ U, (s ∩ u).Nonempty) →
        (s ⊓ ((sInf U) : Opens X)).Nonempty := sorry

/- A space is sober if and only if χ is a surjective function. -/
theorem QuasiSober_iff_χSurjective {τ : TopologicalSpace X} : 
  (QuasiSober X ↔ Function.Surjective (@χ X τ)) := by
  {
    rw [quasiSober_iff]
    rw [Function.Surjective]
    constructor
    intros h b
    -- the point b will give us ⋂ { U^comp | U open, b(U) = false }, which is closed clearly and
    -- irreducible because b is a frame homomorphism. Then the hypothesis h gives us that we have a point, and this will be the point a that we're looking for.
    let C := (sSup (b⁻¹'({False}))).1ᶜ 
    have h1 : IsIrreducible C := by 
      rw [isIrreducible_iff_sInf_Opens]
      -- intros Us Usopen hMeetsAllUs
      -- by_contra hisempty
      -- have inclusion : ⋂₀ Us ⊆ (sSup (b⁻¹'({False}))).1 := by 
      --   rwa [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, disjoint_compl_left_iff_subset] at hisempty
      -- sorry
    have h2 : IsClosed C := by
      constructor
      rw [compl_compl]
      exact (sSup (↑b ⁻¹' {False})).is_open'

    specialize h h1 h2
    obtain ⟨a, ha⟩ := h
    use a 
    ext U
    constructor
    intro hU

    sorry
  }



