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

open Set in
/--
TODO: Move this lemma
-/
lemma ne_univ_of_sdiff_nonempty {α : Type*} {s u : Set α} (hu : u.Nonempty) : s \ u ≠ univ := by
  rw [ne_univ_iff_exists_notMem]
  use hu.some
  simp [hu.some_mem]

lemma div_locally_finite [IsIntegral X] [nt : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) (z : X) : ∃ t ∈ 𝓝 z,
  (t ∩ Function.support fun Z : X ↦ if h : coheight Z = 1
                                    then Multiplicative.toAdd <|
                                         WithZero.unzero (Scheme.ord_ne_zero h hf)
                                    else 0).Finite := by
    -- Take `U` to be an open on which `f ∈ 𝒪(U)ˣ`
    obtain ⟨U, f', hU, hf'⟩ := Scheme.exists_isUnit_germ_eq f hf
    by_cases h : z ∈ U
    · /-
      By assumption, the order of vanishing at every point of `U` is trivial.
      Hence, if `z ∈ U`, we can take our neighbourhood to be `U`, where the support will be empty
      and hence clearly finite.

      Note: This proof should be trivial, so we should make it so.
      -/
      --use U
      refine ⟨U, IsOpen.mem_nhds U.2 h, ?_⟩

      convert finite_empty
      ext a
      simp only [mem_inter_iff, SetLike.mem_coe, Function.mem_support, ne_eq, dite_eq_right_iff,
        toAdd_eq_zero, not_forall, mem_empty_iff_false, iff_false, not_and, not_exists,
        Decidable.not_not]
      intro ha ha'
      suffices Scheme.ord a ha' f = 1 by aesop
      rw [← hf'.1]
      exact AlgebraicGeometry.Scheme.ord_of_isUnit hf'.2 ha' ha

    · let XU := (univ : Set X) \ U
      have properClosed : XU ≠ univ ∧ IsClosed XU :=
        ⟨ne_univ_of_sdiff_nonempty ((Scheme.Opens.nonempty_iff _).mp hU),
          IsClosed.sdiff isClosed_univ (Opens.isOpen U)⟩

      /-
      All points where `f` has nontrivial vanishing must lie outside `U` (i.e. inside `XU`).

      !! Should be its own lemma !!
      -/
      have imp (y : X) (h : Order.coheight y = 1)
          (hy : Scheme.ord y h f ≠ 1) : y ∈ XU := by
        simp only [mem_diff, mem_univ, SetLike.mem_coe, true_and, XU]
        exact fun a ↦ hy (hf'.1 ▸ AlgebraicGeometry.Scheme.ord_of_isUnit hf'.2 h a)

      obtain ⟨W, hW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
        (x := z) (U := ⊤) (by simp)
      refine ⟨W, ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2.1, ?_⟩⟩

      /-
      Our strategy is to show that the points intersecting `W` of codimension `1` are just the
      irreducible components of `WXU`. Then, we show `WXU` is Noetherian and hence has finitely
      many irreducible components.
      -/
      let WXU := W.1 ∩ XU

      -- This should probably be an instance
      /-
      I.e. an affine subset of a locally noetherian space is a notherian space

      !! Should be its own lemma !!
      -/
      have ntW : NoetherianSpace W :=
        have : IsAffine W := hW.1
        have : IsNoetherianRing ↑Γ(↑W, ⊤) :=
          have := nt.1 ⟨W, hW.1⟩
          isNoetherianRing_of_ringEquiv Γ(X, W) W.topIso.commRingCatIsoToRingEquiv.symm
        AlgebraicGeometry.noetherianSpace_of_isAffine


      suffices {z ∈ WXU | coheight z = 1}.Finite by
          apply Finite.subset (by exact this : (WXU ∩ {z : X | coheight z = 1}).Finite)
          simp_all only [ne_eq, Opens.carrier_eq_coe, Opens.coe_top,
            subset_univ, and_true, subset_inter_iff]
          constructor
          · simp only [subset_def, mem_inter_iff, SetLike.mem_coe, Function.mem_support, ne_eq,
            dite_eq_right_iff, toAdd_eq_zero, not_forall, and_imp, forall_exists_index, WXU]
            intro a ha ha' _
            have : ¬(Scheme.ord a ha') f = 1 := by
              rwa [← coe_unzero (Scheme.ord_ne_zero ha' hf), ← coe_one, coe_inj]
            exact ⟨ha, imp a ha' this⟩
          · simp only [subset_def, mem_inter_iff, SetLike.mem_coe, Function.mem_support, ne_eq,
            dite_eq_right_iff, toAdd_eq_zero, not_forall, mem_setOf_eq, and_imp,
            forall_exists_index]
            exact fun _ _ c _ ↦ c

      have : closure WXU ≠ univ := by
        have ans : closure WXU ⊆ closure XU := closure_mono <| by simp [WXU]
        aesop
      refine Finite.subset (Finite.image Subtype.val ?_)
        (QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one this)
      have qsW : QuasiSober W := instQuasiSoberCarrierCarrierCommRingCat W
      have : QuasiSober ↑WXU :=
          @quasiSober_of_quasisober_inter_isClosed_right _ _ XU W.1 qsW properClosed.2
      have : NoetherianSpace WXU := @NoetherianSpace.noetherian_inter_left _ _ W.1 XU ntW
      have := (Equiv.finite_iff
        (coheightZeroSetOrderIsoIrreducibleComponents (α := WXU)).toEquiv).mpr
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      simp only [finite_coe_iff] at this
      convert this
      ext a b
      exact (subtype_specializes_iff b a).symm

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
