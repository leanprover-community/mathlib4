/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.Localization.Additive

/-!
# Additive localization and strong rank condition

We show that a commutative semiring with cancellative addition satisfies the strong rank condition,
by embedding it into its additive localization ("Grothendieck ring").
-/

namespace AddSubmonoid

variable {R S : Type*} [Semiring R] [Semiring S] [Module R S] [IsScalarTower R S S]

section AddSubmonoid

variable {M : AddSubmonoid R} (h : IsLocalizationMap M fun r ↦ r • (1 : S))

private def localizationMap (ι : Type*) :
    LocalizationMap (pi Set.univ fun _ : ι ↦ M) (ι → S) where
  toFun := Pi.map fun i ↦ ringHomEquivModuleIsScalarTower.symm ⟨‹_›, ‹_›⟩
  map_add' _ _ := funext fun i ↦ by simp
  toIsLocalizationMap := .pi _ fun i ↦ by exact h

lemma localizationMap_smul {ι : Type*} {r : R} {x : ι → R} :
    localizationMap h ι (r • x) = r • localizationMap h ι x :=
  funext fun i ↦ smul_assoc r (x i) 1

end AddSubmonoid

variable {M : Submodule Rᵐᵒᵖ R} (h : IsLocalizationMap M.toAddSubmonoid fun r ↦ r • (1 : S))

private noncomputable def mapFun {α β} [Finite α] (f : (α → R) →ₗ[R] β → R) :
    (α → S) →+ β → S := by
  refine (localizationMap h α).map (g := f) ?_ (localizationMap h β)
  intro x i _
  have := Fintype.ofFinite α
  let e := Finsupp.linearEquivFunOnFinite R R α
  rw [← e.apply_symm_apply x.1, ← (e.symm x).univ_sum_single, map_sum, map_sum, Finset.sum_apply]
  refine sum_mem _ fun i _ ↦ ?_
  rw [← Finsupp.smul_single_one, map_smul, AddMonoidHom.coe_coe, map_smul]
  exact M.smul_mem _ (x.2 _ ⟨⟩)

private noncomputable def lmapFun' {α β : Type} [Finite α] (f : (α → R) →ₗ[R] β → R) :
    (α → S) →ₗ[R] β → S where
  toFun := mapFun h f
  map_add' := map_add _
  map_smul' r x := by
    let g α := DistribSMul.toAddMonoidHom (α → S) r
    suffices (mapFun h f).comp (g α) = (g β).comp (mapFun h f) from congr($this x)
    refine (localizationMap h _).epic_of_localizationMap fun y ↦ ?_
    simp [mapFun, g, ← localizationMap_smul h, -AddMonoidHom.coe_mk]

private noncomputable def lmapFun {α β : Type} [Finite α] (f : (α → R) →ₗ[R] β → R) :
    (α → S) →ₗ[S] β → S :=
  have := h.linearMapCompatibleSMul (α → S) (β → S)
  (lmapFun' h f).restrictScalars S

include h in
theorem IsLocalizationMap.strongRankCondition_of_faithfulSMul [FaithfulSMul R S]
    [StrongRankCondition S] : StrongRankCondition R where
  le_of_fin_injective {n m} l hl := le_of_fin_injective S (lmapFun h l) <| by
    simpa [lmapFun, lmapFun', mapFun] using LocalizationMap.map_injective_of_surjOn_or_injective _ _
      (.inr (Pi.map_injective.mpr <| fun _ ↦ (faithfulSMul_iff_injective_smul_one ..).mp ‹_›)) hl

theorem IsLocalizationMap.strongRankCondition_of_isCancelAdd [IsCancelAdd R]
    (h : IsLocalizationMap ⊤ fun r : R ↦ r • (1 : S))
    [StrongRankCondition S] : StrongRankCondition R :=
  have : FaithfulSMul R S := (faithfulSMul_iff_injective_smul_one ..).mpr <|
    (LocalizationMap.top_injective_iff ⟨⟨_, fun _ _ ↦ add_smul ..⟩, h⟩).mpr ‹_›
  h.strongRankCondition_of_faithfulSMul (M := ⊤)

end AddSubmonoid

instance (priority := 100) (R) [CommSemiring R] [IsCancelAdd R] [Nontrivial R] :
    StrongRankCondition R :=
  (Algebra.GrothendieckAddGroup.isLocalizationMap_smul_one R).strongRankCondition_of_isCancelAdd

example : StrongRankCondition ℕ := inferInstance

example : StrongRankCondition ℚ≥0 :=
  have : IsCancelAdd ℚ≥0 := inferInstanceAs (IsCancelAdd {q : ℚ // 0 ≤ q})
  inferInstance
