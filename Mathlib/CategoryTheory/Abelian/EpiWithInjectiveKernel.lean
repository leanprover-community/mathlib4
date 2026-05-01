/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Epimorphisms with an injective kernel

In this file, we define the class of morphisms `epiWithInjectiveKernel` in an
abelian category. We show that this property of morphisms is multiplicative.

This shall be used in the file `Mathlib/Algebra/Homology/Factorizations/Basic.lean` in
order to define morphisms of cochain complexes which satisfy this property
degreewise.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace Abelian

/-- The class of morphisms in an abelian category that are epimorphisms
and have an injective kernel. -/
def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ Injective (kernel f)

/-- The class of morphisms in an abelian category that are monomorphisms
and have a projective kernel. -/
def monoWithProjectiveCokernel : MorphismProperty C :=
  fun _ _ f => Mono f ∧ Projective (cokernel f)

set_option backward.isDefEq.respectTransparency false in
lemma monoWithProjectiveCokernel_eq_unop :
    monoWithProjectiveCokernel (C := C) =
      epiWithInjectiveKernel.unop := by
  ext X Y f
  dsimp [monoWithProjectiveCokernel, epiWithInjectiveKernel]
  apply and_congr (by simp)
  rw [Injective.projective_iff_injective_op, Injective.iso_iff (kernelOpOp f).symm]

/-- A morphism `g : X ⟶ Y` is epi with an injective kernel iff there exists a morphism
`f : I ⟶ X` with `I` injective such that `f ≫ g = 0` and
the short complex `I ⟶ X ⟶ Y` has a splitting. -/
lemma epiWithInjectiveKernel_iff {X Y : C} (g : X ⟶ Y) :
    epiWithInjectiveKernel g ↔ ∃ (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0),
      Nonempty (ShortComplex.mk f g w).Splitting := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inferInstance⟩⟩
  · rintro ⟨I, _, f, w, ⟨σ⟩⟩
    have : IsSplitEpi g := ⟨σ.s, σ.s_g⟩
    let e : I ≅ kernel g :=
      IsLimit.conePointUniqueUpToIso σ.shortExact.fIsKernel (limit.isLimit _)
    exact ⟨inferInstance, Injective.of_iso e inferInstance⟩

lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by assumption)⟩⟩

instance : (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative where
  id_mem _ := epiWithInjectiveKernel_of_iso _
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    refine ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, ?_, ⟨?_⟩⟩
    · ext
      · simp [reassoc_of% w₁]
      · simp [reassoc_of% σ₁.s_g, w₂]
    · exact
        { r := σ₁.r ≫ biprod.inl + g₁ ≫ σ₂.r ≫ biprod.inr
          s := σ₂.s ≫ σ₁.s
          f_r := by
            ext
            · simp [σ₁.f_r]
            · simp [reassoc_of% w₁]
            · simp
            · simp [reassoc_of% σ₁.s_g, σ₂.f_r]
          s_g := by simp [reassoc_of% σ₁.s_g, σ₂.s_g]
          id := by
            dsimp
            have h := g₁ ≫= σ₂.id =≫ σ₁.s
            simp only [add_comp, assoc, comp_add, id_comp] at h
            rw [← σ₁.id, ← h]
            simp only [comp_add, add_comp, assoc, BinaryBicone.inl_fst_assoc,
              BinaryBicone.inr_fst_assoc, zero_comp, comp_zero, add_zero,
              BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_add]
            abel }

set_option backward.isDefEq.respectTransparency false in
instance : (epiWithInjectiveKernel (C := C)).IsStableUnderRetracts where
  of_retract := by
    rintro X' Y' X Y f' f r ⟨_, hf⟩
    have : Epi f' :=
      (MorphismProperty.epimorphisms C).of_retract r (.infer_property _)
    let r' : Retract (kernel f') (kernel f) :=
      { i := kernel.map _ _ r.left.i r.right.i (by simp)
        r := kernel.map _ _ r.left.r r.right.r (by simp) }
    exact ⟨inferInstance, r'.injective⟩

lemma epiWithInjectiveKernel.hasLiftingProperty
    {X Y : C} {p : X ⟶ Y} (hp : epiWithInjectiveKernel p)
    {A B : C} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i p := by
  suffices (MorphismProperty.monomorphisms C).rlp p from this _ (.infer_property _)
  rw [epiWithInjectiveKernel_iff] at hp
  obtain ⟨I, _, s, hs, ⟨σ⟩⟩ := hp
  have hI : (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) := by
    intro A B i (hi : Mono i)
    exact Injective.hasLiftingProperty_of_isZero _ _ (isZero_zero C)
  refine MorphismProperty.of_isPullback (f' := σ.r) (f := 0) ⟨by simp, ⟨?_⟩⟩ hI
  refine PullbackCone.IsLimit.mk _ (fun t ↦ t.fst ≫ s + t.snd ≫ σ.s)
    (fun t ↦ ?_) (fun t ↦ ?_) (fun t m hm₁ hm₂ ↦ ?_)
  · have := σ.f_r
    dsimp at this ⊢
    simp [this]
  · have := σ.s_g
    dsimp
    simp [hs, this]
  · have := σ.id
    dsimp at this ⊢
    simp only [← hm₁, ← hm₂, Category.assoc, ← Preadditive.comp_add, this, comp_id]

instance : (monoWithProjectiveCokernel : MorphismProperty C).IsMultiplicative := by
  rw [monoWithProjectiveCokernel_eq_unop]
  infer_instance

instance : (monoWithProjectiveCokernel : MorphismProperty C).IsStableUnderRetracts := by
  rw [monoWithProjectiveCokernel_eq_unop]
  infer_instance

lemma monoWithProjectiveCokernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    monoWithProjectiveCokernel f ↔ Projective Y := by
  simp only [monoWithProjectiveCokernel, hX.mono f, true_and]
  exact Projective.iso_iff
    { hom := cokernel.desc _ (𝟙 Y) (hX.eq_of_src _ _)
      inv := cokernel.π f }

lemma epiWithInjectiveKernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) :
    epiWithInjectiveKernel f ↔ Injective X := by
  simp only [epiWithInjectiveKernel, hY.epi f, true_and]
  exact Injective.iso_iff
    { hom := kernel.ι f
      inv := kernel.lift _ (𝟙 X) (hY.eq_of_tgt _ _) }

end Abelian

end CategoryTheory
