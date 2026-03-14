/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The colimit module of a presheaf of module on a cofiltered category is monoidal


-/

@[expose] public section

universe w v u

open CategoryTheory ModuleCat MonoidalCategory Limits
  Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} (cR : Cocone R)

noncomputable abbrev constFunctorOfCommRing :
    ModuleCat.{w} cR.pt ⥤ PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) :=
  (constFunctor.{w} ((forget₂ _ RingCat).mapCocone cR))

open TensorProduct in
noncomputable instance : (constFunctorOfCommRing.{w} cR).LaxMonoidal where
  ε :=
    { app U := ε (restrictScalars (cR.ι.app U).hom)
      naturality {V U} f := by
        ext
        change (cR.ι.app U (R.map f 1) : cR.pt) * 1 = (cR.ι.app V 1 * 1 :)
        rw [mul_one, mul_one, ← cR.w f]
        rfl }
  μ F₁ F₂ :=
    { app U := μ (restrictScalars (cR.ι.app U).hom) _ _
      naturality {V U} f := by
        ext : 1
        letI aV : R.obj V →+* cR.pt := (cR.ι.app V).hom
        letI aU : R.obj U →+* cR.pt := (cR.ι.app U).hom
        letI := Module.compHom F₁ aV
        letI := Module.compHom F₂ aV
        letI := Module.compHom (F₁ ⊗[cR.pt] F₂) aU
        letI := Module.compHom (F₁ ⊗[cR.pt] F₂) (R.map f).hom
        apply TensorProduct.ext' (σ₁₂ := .id (R.obj V)) (P₂ := F₁ ⊗[cR.pt] F₂)
        intro (m₁ : F₁) (m₂ : F₂)
        change μ (restrictScalars (cR.ι.app U).hom) F₁ F₂ (m₁ ⊗ₜ m₂) =
          μ (restrictScalars (cR.ι.app V).hom) F₁ F₂ (m₁ ⊗ₜ m₂)
        rw [restrictScalars_μ_tmul, restrictScalars_μ_tmul]
        rfl }
  μ_natural_left _ _ := by
    ext U : 1
    apply μ_natural_left (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  μ_natural_right _ _ := by
    ext U : 1
    apply μ_natural_right (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  associativity _ _ _ := by
    ext U : 1
    apply associativity (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  left_unitality _ := by
    ext U : 1
    apply left_unitality (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)
  right_unitality _ := by
    ext U : 1
    apply right_unitality (ModuleCat.restrictScalars.{w} (cR.ι.app U).hom)

lemma constFunctorOfCommRing_ε_app_apply {X : Cᵒᵖ} (x : R.obj X) :
    (ε (constFunctorOfCommRing.{w} cR)).app X x = cR.ι.app X x :=
  ModuleCat.restrictScalars_ε ..

lemma constFunctorOfCommRing_μ_app_apply {M₁ M₂ : ModuleCat.{w} cR.pt}
    (X : Cᵒᵖ) (m₁ : M₁) (m₂ : M₂) :
    (μ (constFunctorOfCommRing.{w} cR) M₁ M₂).app X (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂ :=
  ModuleCat.restrictScalars_μ_tmul ..

variable {cR} (hcR : IsColimit cR) [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered


noncomputable def colimitFunctorOfCommRing :
    PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) ⥤ ModuleCat.{w} cR.pt :=
  colimitFunctor (isColimitOfPreserves (forget₂ _ RingCat) hcR)

noncomputable def colimitAdjunctionOfCommRing :
    colimitFunctorOfCommRing.{w} hcR ⊣ constFunctorOfCommRing.{w} cR :=
  colimitAdjunction _

noncomputable def ιColimitFunctorOfCommRing
    (F : PresheafOfModules.{w} (R ⋙ forget₂ _ _)) (U : Cᵒᵖ) :
    F.obj U →+ (colimitFunctorOfCommRing hcR).obj F :=
  (colimit.ι F.presheaf U).hom

@[simp]
lemma ιColimitFunctorOfCommRing_w (F : PresheafOfModules.{w} (R ⋙ forget₂ _ _)) {V U : Cᵒᵖ}
    (f : V ⟶ U) (v : F.obj V) :
    dsimp% ιColimitFunctorOfCommRing hcR F U (F.map f v) =
      ιColimitFunctorOfCommRing hcR F V v :=
  ConcreteCategory.congr_hom (colimit.w F.presheaf f) v

noncomputable def coconeColimitFunctorOfCommRing (F : PresheafOfModules.{w} (R ⋙ forget₂ _ _)) :
    Cocone F.presheaf where
  pt := (forget₂ _ _).obj ((colimitFunctorOfCommRing hcR).obj F)
  ι.app U := AddCommGrpCat.ofHom (ιColimitFunctorOfCommRing hcR F U)
  ι.naturality V U f := by ext v; exact ιColimitFunctorOfCommRing_w hcR F f v

noncomputable def isColimitCoconeColimitFunctorOfCommRing
    (F : PresheafOfModules.{w} (R ⋙ forget₂ _ _)) :
    IsColimit (coconeColimitFunctorOfCommRing hcR F) :=
  colimit.isColimit F.presheaf

lemma ιColimitFunctorOfCommRing_jointly_surjective
    {F : PresheafOfModules.{w} (R ⋙ forget₂ _ _)} (x : (colimitFunctorOfCommRing hcR).obj F) :
    ∃ (U : Cᵒᵖ) (u : F.obj U), ιColimitFunctorOfCommRing hcR F U u = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget _) (isColimitCoconeColimitFunctorOfCommRing hcR F)) _

lemma ιColimitFunctorOfCommRing_jointly_surjective₂
    {F₁ F₂ : PresheafOfModules.{w} (R ⋙ forget₂ _ _)}
    (x₁ : (colimitFunctorOfCommRing hcR).obj F₁)
    (x₂ : (colimitFunctorOfCommRing hcR).obj F₂) :
    ∃ (U : Cᵒᵖ) (u₁ : F₁.obj U) (u₂ : F₂.obj U),
      ιColimitFunctorOfCommRing hcR F₁ U u₁ = x₁ ∧
        ιColimitFunctorOfCommRing hcR F₂ U u₂ = x₂ := by
  obtain ⟨U, ⟨u₁, u₂⟩, hu⟩ := Types.jointly_surjective_of_isColimit
    (((isColimitOfPreserves (forget _) (isColimitCoconeColimitFunctorOfCommRing
    hcR F₁))).tensor ((isColimitOfPreserves (forget _)
      (isColimitCoconeColimitFunctorOfCommRing hcR F₂)))) (by exact ⟨x₁, x₂⟩)
  exact ⟨U, u₁, u₂, _root_.Prod.ext_iff.1 hu⟩

noncomputable instance : (colimitFunctorOfCommRing hcR).OplaxMonoidal :=
  (colimitAdjunctionOfCommRing hcR).leftAdjointOplaxMonoidal

lemma colimitFunctorOfCommRing_η_apply
    {U : Cᵒᵖ} (x : R.obj U) :
    η (colimitFunctorOfCommRing hcR) (ιColimitFunctorOfCommRing hcR (𝟙_ _) U x) =
      cR.ι.app U x := by
  dsimp [Adjunction.leftAdjointOplaxMonoidal_η]
  erw [PresheafOfModules.colimitAdjunction_homEquiv_symm_apply]
  rw [constFunctorOfCommRing_ε_app_apply]
  dsimp

open ModuleColimit in
instance : IsIso (η (colimitFunctorOfCommRing hcR)) := by
  let h₁ := isColimitCoconeColimitFunctorOfCommRing hcR (unit _)
  let h₂ := isColimitOfPreserves (forget₂ _ AddCommGrpCat)
    (isColimitOfPreserves (forget₂ _ RingCat) hcR)
  have : (forget₂ _ AddCommGrpCat).map (η (colimitFunctorOfCommRing hcR)) =
    (IsColimit.coconePointUniqueUpToIso h₁ h₂).hom := by
    ext x
    obtain ⟨U, u, rfl⟩ := ιColimitFunctorOfCommRing_jointly_surjective hcR x
    dsimp
    rw [colimitFunctorOfCommRing_η_apply]
    exact ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom h₁ h₂ U).symm _
  rw [← isIso_iff_of_reflects_iso _ (forget₂ _ AddCommGrpCat), this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma colimitFunctorOfCommRing_δ_apply
    {F₁ F₂ : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}
    {U : Cᵒᵖ} (m₁ : F₁.obj U) (m₂ : F₂.obj U) :
    dsimp% δ (colimitFunctorOfCommRing hcR) F₁ F₂
        (ιColimitFunctorOfCommRing hcR _ U (m₁ ⊗ₜ m₂)) =
      ιColimitFunctorOfCommRing hcR _ U m₁ ⊗ₜ
        ιColimitFunctorOfCommRing hcR _ U m₂ := by
  dsimp [Adjunction.leftAdjointOplaxMonoidal_δ]
  erw [PresheafOfModules.colimitAdjunction_homEquiv_symm_apply]
  dsimp
  let adj := colimitAdjunctionOfCommRing hcR
  change (μ (constFunctorOfCommRing cR) _ _).app U
    (((adj.unit.app F₁).app U ⊗ₘ (adj.unit.app F₂).app U) (m₁ ⊗ₜ m₂)) = _
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul,
    constFunctorOfCommRing_μ_app_apply]
  rfl

namespace isIso_colimitFunctorOfCommRing_δ

variable (F₁ F₂ : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))

def μ : (colimitFunctorOfCommRing hcR).obj F₁ ⊗ (colimitFunctorOfCommRing hcR).obj F₂ ⟶
    (colimitFunctorOfCommRing hcR).obj (F₁ ⊗ F₂) := sorry

@[simp]
lemma μ_apply {X : Cᵒᵖ} (m₁ : F₁.obj X) (m₂ : F₂.obj X) :
    dsimp% μ hcR F₁ F₂ (ιColimitFunctorOfCommRing hcR F₁ X m₁ ⊗ₜ
        ιColimitFunctorOfCommRing hcR F₂ X m₂) =
      ιColimitFunctorOfCommRing hcR (F₁ ⊗ F₂) X (m₁ ⊗ₜ m₂) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma μ_δ : μ hcR F₁ F₂ ≫ δ (colimitFunctorOfCommRing hcR) F₁ F₂ = 𝟙 _ :=
  ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₂ ↦ by
    obtain ⟨U, m₁, m₂, rfl, rfl⟩ := ιColimitFunctorOfCommRing_jointly_surjective₂ hcR m₁ m₂
    simp)

set_option backward.isDefEq.respectTransparency false in
instance : Epi (μ hcR F₁ F₂) := by
  suffices ∀ (U : Cᵒᵖ) (m : (F₁ ⊗ F₂).obj U),
      ∃ z, μ hcR F₁ F₂ z = ιColimitFunctorOfCommRing hcR (F₁ ⊗ F₂) U m from
    ConcreteCategory.epi_of_surjective _ (fun m ↦ by
      obtain ⟨U, m, rfl⟩ := ιColimitFunctorOfCommRing_jointly_surjective hcR m
      exact this U m)
  intro U (m : TensorProduct (R.obj U) (F₁.obj U) (F₂.obj U))
  induction m with
  | zero => exact ⟨0, by simp⟩
  | add => sorry
  | tmul => sorry

@[reassoc (attr := simp)]
lemma δ_μ : δ (colimitFunctorOfCommRing hcR) F₁ F₂ ≫ μ hcR F₁ F₂ = 𝟙 _ := by
  simp [← cancel_epi (μ hcR F₁ F₂)]

end isIso_colimitFunctorOfCommRing_δ

open isIso_colimitFunctorOfCommRing_δ in
instance (F₁ F₂ : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (δ (colimitFunctorOfCommRing hcR) F₁ F₂) :=
  ⟨μ hcR F₁ F₂, by simp⟩

noncomputable instance : (colimitFunctorOfCommRing hcR).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

end PresheafOfModules
