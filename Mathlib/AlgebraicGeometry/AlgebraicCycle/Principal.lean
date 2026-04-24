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
namespace Scheme
namespace functionField

open Multiplicative WithZero

/--
A principal divisor on a locally noetherian integral scheme is locally finite (and hence a divisor).
-/
lemma div_locally_finite [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (z : X) : ∃ t ∈ 𝓝 z,
    (t ∩ Function.support fun Z : X ↦ if h : coheight Z = 1
      then toAdd <| WithZero.unzero (Scheme.ord_ne_zero h hf) else 0).Finite := by
  obtain ⟨U, f', (hUne : Nonempty U), hgf, hu⟩ := Scheme.exists_isUnit_germ_eq f hf
  obtain ⟨W, hWa, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) (by simp)
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
  have : NoetherianSpace W.1 := noetherianSpace_of_isAffineOpen W hWa
  have : QuasiSober W.1 := W.isOpenEmbedding'.quasiSober
  have : QuasiSober (W.1 ∩ (U : Set X)ᶜ : Set X) :=
    quasiSober_of_quasisober_inter_isClosed_right W.1 U.2.isClosed_compl
  have : NoetherianSpace (W.1 ∩ (U : Set X)ᶜ : Set X) :=
    NoetherianSpace.noetherian_inter_left W.1 _
  have hne : closure (W.1 ∩ (U : Set X)ᶜ) ≠ univ := by
    intro h
    have := (closure_mono (inter_subset_right (s := W.carrier) (t := (↑U)ᶜ))).trans
        U.2.isClosed_compl.closure_eq.le
    rw [h] at this
    exact compl_ne_univ.mpr ((Scheme.Opens.nonempty_iff _).mp hUne) <| univ_subset_iff.mp <| this
  refine ⟨W, W.2.mem_nhds hzW,
    (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hne).subset ?_⟩
  intro x ⟨hxW, hxsup⟩
  simp only [Function.mem_support, ne_eq, dite_eq_right_iff, toAdd_eq_zero, not_forall] at hxsup
  obtain ⟨hx1, hxne⟩ := hxsup
  have : Scheme.ord x hx1 f ≠ 1 := fun h =>
    hxne <| coe_inj.mp <| by rw [coe_one, coe_unzero, h]
  exact ⟨⟨hxW, Scheme.not_mem_of_ord_neq_one f hu hgf this⟩, hx1⟩

/--
On an locally Noetherian integral scheme, given `f : X.functionField` and `hf : x ≠ 0`,
we define the principal Weil divisor `div f hf` as an algebraic cycle with coefficients in `ℤ`.
-/
noncomputable
def div [IsIntegral X] [nt : IsLocallyNoetherian X] (f : X.functionField) (hf : f ≠ 0) :
    AlgebraicCycle X ℤ where
  toFun Z := if h : Order.coheight Z = 1
              then Multiplicative.toAdd <| WithZero.unzero (Scheme.ord_ne_zero h hf)
              else 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := div_locally_finite f hf z

@[simp]
lemma div_eq_zero_of_coheight_ne_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z ≠ 1) : div f hf Z = 0 := dif_neg hZ

@[simp]
lemma div_eq_ord_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z = 1) :
    div f hf Z = Multiplicative.toAdd (WithZero.unzero (Scheme.ord_ne_zero hZ hf)) := dif_pos hZ

@[simp]
theorem div_mul [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
    div (f * g) ((mul_ne_zero_iff_right hg).mpr hf) = div f hf + div g hg := by
  ext a
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a from this
  simp only [div, map_mul]
  split_ifs <;> simp_all [unzero_mul]

/--
The `div` construction gives a Weil divisor.
-/
theorem div_support [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField} {hf : f ≠ 0} :
    (div f hf).support ⊆ {x : X | coheight x = 1} := by
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  contrapose hz
  exact div_eq_zero_of_coheight_ne_one f hf z hz

theorem div_eq_zero_of_isUnit [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens} [Nonempty U]
    [DecidablePred (· ∈ U)] {g : Γ(X, U)} (hg : IsUnit g) : (div (X.germToFunctionField U g)
    ((map_ne_zero_iff _ (germToFunctionField_injective X U)).mpr hg.ne_zero)).restrict U = 0 := by
  apply AlgebraicCycle.homgeneous_ext (AlgebraicCycle.restrict_support_subset_inter div_support)
    (by simp)
  intro z hz
  simp_all only [mem_inter_iff, mem_setOf_eq, SetLike.mem_coe, AlgebraicCycle.restrict_eq_of_mem,
    div_eq_ord_of_coheight_eq_one, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
    toAdd_eq_zero]
  change _ = unzero (by simp : (1 : WithZero (Multiplicative ℤ)) ≠ 0)
  apply unzero.congr_simp
  apply ord_of_isUnit hg _ hz.2

lemma div_eq_zero_of_isUnit_top
    [IsIntegral X] [IsLocallyNoetherian X] {g : Γ(X, ⊤)} (hg : IsUnit g) :
    haveI : Nonempty (⊤ : X.Opens) := (Opens.nonempty_iff ⊤).mpr univ_nonempty
    div (X.germToFunctionField ⊤ g)
    ((map_ne_zero_iff _ (germToFunctionField_injective X ⊤)).mpr hg.ne_zero) = 0 := by
  classical
  have : Nonempty (⊤ : X.Opens) := (Opens.nonempty_iff ⊤).mpr univ_nonempty
  simp [← div_eq_zero_of_isUnit hg]

@[simp]
theorem div_neg [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField) (hf : f ≠ 0) :
    div (- f) (neg_ne_zero.mpr hf) = div f hf := by
  classical
  simp_rw [neg_eq_neg_one_mul f]
  rw [div_mul _ (by simp) _ hf, add_eq_right]
  have : IsUnit (-1 : Γ(X, ⊤)) := by simp
  simp [← div_eq_zero_of_isUnit_top this]

end functionField
end Scheme
end AlgebraicGeometry
