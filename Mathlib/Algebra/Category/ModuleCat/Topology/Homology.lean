/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!

# `TopModuleCat` is a `CategoryWithHomology`

`TopModuleCat R`, the category of topological `R`-modules, is not an abelian category.
But since the topology on subquotients is well-defined, we can still talk about homology in this
category. See the `CategoryWithHomology (TopModuleCat R)` instance in this file.

-/

universe v u

open CategoryTheory Limits

namespace TopModuleCat

variable {R : Type u} [Ring R] [TopologicalSpace R]

variable {M N : TopModuleCat.{v} R} (φ : M ⟶ N)

section kernel

/-- Kernel in `TopModuleCat R` is the kernel of the linear map with the subspace topology. -/
abbrev ker : TopModuleCat R := .of R (LinearMap.ker φ.hom)

/-- The inclusion map from the kernel in `TopModuleCat R`. -/
def kerι : ker φ ⟶ M := ofHom ⟨Submodule.subtype _, continuous_subtype_val⟩

instance : Mono (kerι φ) := ConcreteCategory.mono_of_injective (kerι φ) <| Subtype.val_injective

@[simp] lemma kerι_comp : kerι φ ≫ φ = 0 := by ext ⟨_, hm⟩; exact hm

@[simp] lemma kerι_apply (x) : kerι φ x = x.1 := rfl

/-- `TopModuleCat.ker` is indeed the kernel in `TopModuleCat R`. -/
def isLimitKer : IsLimit (KernelFork.ofι (kerι φ) (kerι_comp φ)) :=
  isLimitAux (KernelFork.ofι (kerι φ) (kerι_comp φ))
    (fun s ↦ ofHom <| (Fork.ι s).hom.codRestrict (LinearMap.ker φ.hom) fun m ↦ by
      rw [LinearMap.mem_ker, ← ConcreteCategory.comp_apply (Fork.ι s) φ,
        KernelFork.condition, hom_zero_apply])
    (fun s ↦ rfl)
    (fun s m h ↦ by dsimp at h ⊢; rw [← cancel_mono (kerι φ), h]; rfl)

end kernel

section cokernel

/-- Cokernel in `TopModuleCat R` is the cokernel of the linear map with the quotient topology. -/
abbrev coker : TopModuleCat R := .of R (N ⧸ LinearMap.range φ.hom)

/-- The projection map to the cokernel in `TopModuleCat R`. -/
def cokerπ : N ⟶ coker φ := ofHom <| ⟨Submodule.mkQ _, by tauto⟩

@[simp]
lemma hom_cokerπ (x) : (cokerπ φ).hom x = Submodule.mkQ _ x := rfl

lemma cokerπ_surjective : Function.Surjective (cokerπ φ).hom := Submodule.mkQ_surjective _

instance : Epi (cokerπ φ) := ConcreteCategory.epi_of_surjective (cokerπ φ) (cokerπ_surjective φ)

@[simp] lemma comp_cokerπ : φ ≫ cokerπ φ = 0 := by
  ext m
  change Submodule.mkQ _ (φ m) = 0
  simp

/-- `TopModuleCat.coker` is indeed the cokernel in `TopModuleCat R`. -/
def isColimitCoker : IsColimit (CokernelCofork.ofπ (cokerπ φ) (comp_cokerπ φ)) :=
  isColimitAux (.ofπ (cokerπ φ) (comp_cokerπ φ))
  (fun s ↦ ofHom <|
    { toLinearMap := (LinearMap.range φ.hom).liftQ s.π.hom.toLinearMap
        (LinearMap.range_le_ker_iff.mpr <| show (φ ≫ s.π).hom.toLinearMap = 0 by
          rw [s.condition, hom_zero, ContinuousLinearMap.coe_zero])
      cont := Continuous.quotient_lift s.π.hom.2 _ })
  (fun s ↦ rfl)
  (fun s m h ↦ by dsimp at h ⊢; rw [← cancel_epi (cokerπ φ), h]; rfl)

end cokernel

instance : CategoryWithHomology (TopModuleCat R) := by
  constructor
  intro S
  let D₁ : S.LeftHomologyData := ⟨_, _, _, _, _, isLimitKer _, by simp, isColimitCoker _⟩
  let D₂ : S.RightHomologyData := ⟨_, _, _, _, by simp, isColimitCoker _, _, isLimitKer _⟩
  let F := ShortComplex.leftRightHomologyComparison' D₁ D₂
  suffices IsIso F from ⟨⟨.ofIsIsoLeftRightHomologyComparison' D₁ D₂⟩⟩
  have hF : Function.Bijective F := by
    change Function.Bijective ((forget₂ _ (ModuleCat R)).map F)
    rw [← ConcreteCategory.isIso_iff_bijective, ShortComplex.map_leftRightHomologyComparison']
    infer_instance
  have hF' : Topology.IsEmbedding F := by
    refine .of_comp F.1.2 D₂.ι.1.2 ?_
    -- `isEmbedding_of_isOpenQuotientMap_of_isInducing` is the key lemma that shows the two
    -- definitions of homology give the same topology.
    refine isEmbedding_of_isOpenQuotientMap_of_isInducing
      D₁.i (F ≫ D₂.ι) D₁.π D₂.p ?_ .subtypeVal
      (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap
      (Submodule.isOpenQuotientMap_mkQ _)
      (Subtype.val_injective.comp hF.1) ?_
    · rw [← ContinuousLinearMap.coe_comp', ← ContinuousLinearMap.coe_comp',
        ← hom_comp, ← hom_comp, ShortComplex.π_leftRightHomologyComparison'_ι]
    · suffices ∀ x y, S.g y = 0 → D₂.p y = D₂.p x → S.g x = 0 by
        simpa [Set.subset_def, D₁, kerι_apply S.g] using this
      intro x y hy e
      obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp e
      obtain rfl := eq_sub_iff_add_eq.mp hz
      simpa [show S.g (S.f z) = 0 from ConcreteCategory.congr_hom S.zero z] using hy
  rw [← isIso_iff_of_reflects_iso _ (forget₂ (TopModuleCat R) TopCat),
    TopCat.isIso_iff_isHomeomorph, isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨hF', hF.2⟩

end TopModuleCat
