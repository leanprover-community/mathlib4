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

namespace AlgebraicGeometry

open Multiplicative WithZero Scheme

/--
A principal divisor on a locally noetherian integral scheme is locally finite (and hence a divisor)
-/
lemma div_locally_finite [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (z : X) : ∃ t ∈ 𝓝 z, (t ∩ Function.support (ord f)).Finite := by
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
  exact ord_of_isUnit hg this a

/--
On an locally Noetherian integral scheme, given `f : X.functionField` and `hf : x ≠ 0`,
we define the principal Weil divisor `div f hf` as an algebraic cycle with coefficients in `ℤ`.
-/
noncomputable
def div [IsIntegral X] [nt : IsLocallyNoetherian X] (f : X.functionField) :
    AlgebraicCycle X ℤ where
  toFun z := ord f z
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := div_locally_finite f z

@[simp]
lemma div_eq_ord [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (z : X) : div f z = ord f z := rfl

@[simp]
theorem div_mul [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
    div (f * g) = div f + div g := by
  ext a
  by_cases ha : coheight a = 1 <;> simp_all

/--
The `div` construction gives a Weil divisor.
-/
theorem div_support [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField} :
    (div f).support ⊆ {x : X | coheight x = 1} := by
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  contrapose hz
  simp_all

theorem div_eq_zero_of_isUnit [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens} [Nonempty U]
    {g : Γ(X, U)} (hg : IsUnit g) : (div (X.germToFunctionField U g)).restrict U = 0 := by
  ext z hz
  have : coheight z = 1 := by
    apply div_support (f := (X.germToFunctionField U g))
    simp_all
  simp_all only [AlgebraicCycle.restrict_support, mem_union, mem_inter_iff, Function.mem_support,
    div_eq_ord, ne_eq, SetLike.mem_coe, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
    not_true_eq_false, or_false, AlgebraicCycle.restrict_eq_of_mem]
  have := ord_of_isUnit hg this hz.2
  exact hz.1 this

lemma div_eq_zero_of_isUnit_top
    [IsIntegral X] [IsLocallyNoetherian X] {g : Γ(X, ⊤)} (hg : IsUnit g) :
    haveI : Nonempty (⊤ : X.Opens) := (Opens.nonempty_iff ⊤).mpr univ_nonempty
    div (X.germToFunctionField ⊤ g) = 0 := by
  classical
  have : Nonempty (⊤ : X.Opens) := (Opens.nonempty_iff ⊤).mpr univ_nonempty
  simp [← div_eq_zero_of_isUnit hg]

@[simp]
theorem div_neg [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField) :
    div (- f) = div f := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  simp_rw [neg_eq_neg_one_mul f]
  rw [div_mul _ (by simp) _ hf, add_eq_right]
  have : IsUnit (-1 : Γ(X, ⊤)) := by simp
  simp [← div_eq_zero_of_isUnit_top this]

end AlgebraicGeometry
