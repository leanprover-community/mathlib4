module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.NoetherianSpace

/-!
# Principal divisors

In this file we develop the notion of a principal divisor associated with an element of the function
field of a locally noetherian integral scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace Set Topology

universe u
variable {X : Scheme.{u}}

namespace AlgebraicGeometry
namespace Scheme
namespace functionField

open Multiplicative WithZero

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
  have hne : closure (W.1 ∩ (U : Set X)ᶜ) ≠ univ := fun h =>
    compl_ne_univ.mpr ((Scheme.Opens.nonempty_iff _).mp hUne) <| univ_subset_iff.mp <|
      h ▸ (closure_mono inter_subset_right).trans U.2.isClosed_compl.closure_eq.le
  refine ⟨W, W.2.mem_nhds hzW,
    (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hne).subset ?_⟩
  intro x ⟨hxW, hxsup⟩
  simp only [Function.mem_support, ne_eq, dite_eq_right_iff, toAdd_eq_zero, not_forall] at hxsup
  obtain ⟨hx1, hxne⟩ := hxsup
  have hord : Scheme.ord x hx1 f ≠ 1 := fun h =>
    hxne <| coe_inj.mp <| by rw [coe_one, coe_unzero]; exact h
  exact ⟨⟨hxW, Scheme.not_mem_of_ord_neq_one f hu hgf hord⟩, hx1⟩

/--
On an locally Noetherian integral scheme, given `f : X.functionField` and `hf : x ≠ 0`,
we define the principal Weil divisor `f.divisor hf` as an algebraic cycle with coefficients in `ℤ`.
-/
noncomputable
def div [IsIntegral X] [nt : IsLocallyNoetherian X] (f : X.functionField) (hf : f ≠ 0) :
    AlgebraicCycle X ℤ where
  toFun Z := if h : Order.coheight Z = 1
              then Multiplicative.toAdd <| WithZero.unzero (Scheme.ord_ne_zero h hf)
              else 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := div_locally_finite f hf z

lemma div_ext₁ [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField} {hf : f ≠ 0}
    {D : AlgebraicCycle X ℤ} (h : ∀ (a : X) (ha : coheight a = 1), div f hf a = D a) :
    div f hf = D := by
  ext x
  simp [div]

  sorry

lemma div_ext₂ [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField} {hf : f ≠ 0}
    {D : AlgebraicCycle X ℤ} (h : ∀ (a : X) (ha : coheight a = 1), D a = div f hf a) : D = div f hf := sorry

@[simp]
lemma div_eq_zero_of_coheight_ne_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z ≠ 1) : div f hf Z = 0 := dif_neg hZ

@[simp]
lemma div_eq_ord_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z = 1) :
    div f hf Z = Multiplicative.toAdd (WithZero.unzero (Scheme.ord_ne_zero hZ hf)) := dif_pos hZ

/--
TODO: Generlize this beyond just being about cycles with coefficients in `ℤ`.
-/
lemma div_le_iff [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) {D : AlgebraicCycle X ℤ} (hD : ∀ z : X, coheight z ≠ 1 → D z ≥ 0):
    div f hf ≤ D ↔ ∀ z : X, coheight z = 1 → div f hf z ≤ D z :=
  ⟨fun h z _ ↦ h z, fun h z ↦ if hz : coheight z = 1
                              then h z hz
                              else (by simp [div_eq_zero_of_coheight_ne_one _ _ _ hz, hD z hz])⟩

@[simp]
theorem div_homomorphism [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
    div (f * g) ((mul_ne_zero_iff_right hg).mpr hf) = div f hf + div g hg := by
  ext a
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a from this
  simp only [div, map_mul]
  split_ifs <;> simp_all [unzero_mul]

theorem div_of_isUnit [IsIntegral X] [IsNoetherian X] {U : X.Opens} [Nonempty U] (g : Γ(X, U))
    (hg : IsUnit g) : div (X.germToFunctionField U g)
    ((map_ne_zero_iff _ (germToFunctionField_injective X U)).mpr hg.ne_zero) = 0 := by
  ext z
  simp [div]
  sorry


@[simp]
theorem div_neg [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) :
    div (- f) (neg_ne_zero.mpr hf) = div f hf := by
  have : -f = -1 * f := neg_eq_neg_one_mul f
  simp_rw [this]
  rw [div_homomorphism (-1) (by simp) f hf]
  simp

  sorry

end functionField
end Scheme
end AlgebraicGeometry
