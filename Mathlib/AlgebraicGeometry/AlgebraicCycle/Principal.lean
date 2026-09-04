/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.NoetherianSpace

/-!
# Principal divisors

In this file we develop the notion of a principal Weil divisor associated with an element of the
function field of a locally noetherian integral scheme.
-/

@[expose] public section

open AlgebraicGeometry Order TopologicalSpace Set Topology

universe u
variable {X : Scheme.{u}}

namespace AlgebraicGeometry.AlgebraicCycle

open Multiplicative WithZero Scheme

/--
The principal Weil divisor `divisor f` of an element `f` of the function field of a locally
Noetherian integral scheme, as an algebraic cycle with coefficients in `ℤ`.

This has a junk value of `0` when `f = 0`, inherited from `AlgebraicGeometry.ord`.
-/
noncomputable
def divisor [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField) :
    AlgebraicCycle X ℤ where
  toFun z := ord f z
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := by
    by_cases hf : f = 0
    · use ⊤
      simp [hf]
    obtain ⟨U, hU, g, (hUne : Nonempty U), hgf, hg⟩ := exists_isUnit_germ_eq X f hf
    obtain ⟨W, hWa, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) (by simp)
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
    have : NoetherianSpace W.1 := noetherianSpace_of_isAffineOpen W hWa
    have : QuasiSober W.1 := W.isOpenEmbedding'.quasiSober
    have : QuasiSober (W.1 ∩ (U : Set X)ᶜ : Set X) :=
      QuasiSober.inter_of_isClosed_of_quasiSober_left W.1 U.2.isClosed_compl
    have : NoetherianSpace (W.1 ∩ (U : Set X)ᶜ : Set X) :=
      NoetherianSpace.inter_of_left W.1 _
    have hne : closure (W.1 ∩ (U : Set X)ᶜ) ≠ univ := by
      intro h
      have := (closure_mono (inter_subset_right (s := W.carrier) (t := (↑U)ᶜ))).trans
          U.2.isClosed_compl.closure_eq.le
      rw [h] at this
      exact compl_ne_univ.mpr ((Scheme.Opens.nonempty_iff _).mp hUne) <| univ_subset_iff.mp <| this
    refine ⟨W, W.2.mem_nhds hzW,
      (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hne).subset ?_⟩
    intro x ⟨hxW, hxsup⟩
    have : coheight x = 1 := by
      by_contra!
      have := ord_eq_zero_of_coheight_neq_one this f
      contradiction
    refine ⟨⟨hxW, fun a ↦ hxsup ?_⟩, this⟩
    rw [← hgf]
    exact ord_of_isUnit hg a

@[simp]
lemma divisor_apply [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (z : X) : divisor f z = ord f z := rfl

@[simp]
theorem divisor_mul [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
    divisor (f * g) = divisor f + divisor g := by
  ext a
  by_cases ha : coheight a = 1 <;> simp_all

/--
The `divisor` construction gives a Weil divisor: its support consists of points of coheight one.
-/
theorem divisor_support [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField} :
    (divisor f).support ⊆ {x : X | coheight x = 1} := by
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  contrapose hz
  simp_all

theorem divisor_eq_zero_of_isUnit [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens} [Nonempty U]
    {g : Γ(X, U)} (hg : IsUnit g) : (divisor (X.germToFunctionField U g)).filter U = 0 := by
  ext z
  by_cases hz : z ∈ (U : Set X)
  · simp [hz, ord_of_isUnit hg hz]
  · simp [hz]

lemma divisor_eq_zero_of_isUnit_top
    [IsIntegral X] [IsLocallyNoetherian X] {g : Γ(X, ⊤)} (hg : IsUnit g) :
    divisor (X.germToFunctionField ⊤ g) = 0 := by
  ext z
  simp [hg]

@[simp]
theorem divisor_neg [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField) :
    divisor (- f) = divisor f := by
  ext z
  simp

end AlgebraicGeometry.AlgebraicCycle
