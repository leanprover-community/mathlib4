/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Stalks

/-!

# Module structure on stalks
Let `M` be a presheaf of `R`-modules on a topological space. We endow `M.presheaf.stalk x` with
an `R.stalk x`-module structure.

The key characterizing lemma is `PresheafOfModules.germ_smul`, which describes the compatibility
of the scalar action and `TopCat.Presheaf.germ`.

-/

@[expose] public section

open CategoryTheory LinearMap Opposite TopologicalSpace

universe w₀ w u v

namespace CategoryTheory.Limits

open IsFiltered

variable {C : Type*} [SmallCategory C] [IsFiltered C] (R : C ⥤ RingCat) (M : C ⥤ Ab)
    [∀ i, Module (R.obj i) (M.obj i)]
    (H : ∀ {i j} (f : i ⟶ j) r m, M.map f (r • m) = R.map f r • M.map f m)

/-- (Implementation). The scalar multiplication function on `ColimitType`. -/
protected noncomputable
def colimit.smul (r : (R ⋙ forget _).ColimitType) (m : (M ⋙ forget _).ColimitType) :
    (M ⋙ forget _).ColimitType := by
  refine Quot.liftOn₂ r m (fun Ua Vb ↦ Functor.ιColimitType _ (max Ua.1 Vb.1) <|
    letI a : R.obj (max Ua.1 Vb.1) := R.map (leftToMax Ua.1 Vb.1) Ua.2
    letI b : M.obj (max Ua.1 Vb.1) := M.map (rightToMax Ua.1 Vb.1) Vb.2
    a • b) ?_ ?_
  · rintro ⟨U, a⟩ ⟨V₁, b₁⟩ ⟨V₂, b₂⟩ ⟨f : V₁ ⟶ V₂, rfl : b₂ = M.map _ b₁⟩
    obtain ⟨s, α, β, h₁, h₂⟩ :=
      bowtie (leftToMax U V₁) (leftToMax U V₂)
        (rightToMax U V₁) (f ≫ rightToMax U V₂)
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ α β ?_
    simp [*, ← elementwise_of% R.map_comp, ← elementwise_of% M.map_comp, -Functor.map_comp]
  · rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩ ⟨f : U₁ ⟶ U₂, rfl : a₂ = R.map _ a₁⟩
    obtain ⟨s, α, β, h₁, h₂⟩ :=
      bowtie (leftToMax U₁ V) (f ≫ leftToMax U₂ V)
        (rightToMax U₁ V) (rightToMax U₂ V)
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ α β ?_
    simp [*, ← elementwise_of% R.map_comp, ← elementwise_of% M.map_comp, -Functor.map_comp]

#adaptation_note /-- As of nightly-2026-02-10, we need to increase the maxHeartbeats limits here -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in --
set_option synthInstance.maxHeartbeats 40000 in
/-- (Implementation). The module structure on `AddCommGrpCat.FilteredColimits.colimit`. -/
noncomputable abbrev filteredColimitsModule : Module (RingCat.FilteredColimits.colimit R)
    (AddCommGrpCat.FilteredColimits.colimit M) where
  smul := colimit.smul R M H
  mul_smul r s m := Quot.induction_on₃ r s m <| by
    rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩
    obtain ⟨s, α, β, h₁, h₂, h₃⟩ := crown₃
      (leftToMax U₁ U₂ ≫ leftToMax (max U₁ U₂) V) (leftToMax U₁ (max U₂ V))
      (rightToMax U₁ U₂ ≫ leftToMax (max U₁ U₂) V) (leftToMax U₂ V ≫ rightToMax U₁ (max U₂ V))
      (rightToMax (max U₁ U₂) V) (rightToMax U₂ V ≫ rightToMax U₁ (max U₂ V))
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ α β ?_
    dsimp
    simp only [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, mul_smul, *]
  one_smul m := Quot.induction_on m <| by
    rintro ⟨V, b⟩
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ (𝟙 _) (rightToMax _ _) ?_
    dsimp
    simp only [map_one, ← ConcreteCategory.comp_apply, ← Functor.map_comp, one_smul,
      Category.comp_id]
  smul_zero r := Quot.induction_on r <| by
    rintro ⟨U, a⟩
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ (𝟙 _) (rightToMax _ _) ?_
    dsimp
    simp only [map_zero, smul_zero]
  smul_add r m n := Quot.induction_on₃ r m n <| by
    rintro ⟨U, a⟩ ⟨V₁, b₁⟩ ⟨V₂, b₂⟩
    obtain ⟨s, α, β, h₁, h₂, h₃, h₄⟩ := crown₄
      (leftToMax U V₁ ≫ leftToMax (max U V₁) (max U V₂)) (leftToMax U (max V₁ V₂))
      (leftToMax U V₂ ≫ rightToMax (max U V₁) (max U V₂)) (leftToMax U (max V₁ V₂))
      (rightToMax U V₁ ≫ leftToMax (max U V₁) (max U V₂))
      (leftToMax V₁ V₂ ≫ rightToMax U (max V₁ V₂))
      (rightToMax U V₂ ≫ rightToMax (max U V₁) (max U V₂))
      (rightToMax V₁ V₂ ≫ rightToMax U (max V₁ V₂))
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ β α ?_
    dsimp
    simp only [*, ← ConcreteCategory.comp_apply, ← Functor.map_comp, map_add, smul_add]
  add_smul r s m := Quot.induction_on₃ r s m <| by
    rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩
    obtain ⟨s, α, β, h₁, h₂, h₃, h₄⟩ := crown₄
      (rightToMax U₁ V ≫ leftToMax (max U₁ V) (max U₂ V)) (rightToMax (max U₁ U₂) V)
      (rightToMax U₂ V ≫ rightToMax (max U₁ V) (max U₂ V)) (rightToMax (max U₁ U₂) V)
      (leftToMax U₁ V ≫ leftToMax (max U₁ V) (max U₂ V))
      (leftToMax U₁ U₂ ≫ leftToMax (max U₁ U₂) V)
      (leftToMax U₂ V ≫ rightToMax (max U₁ V) (max U₂ V))
      (rightToMax U₁ U₂ ≫ leftToMax (max U₁ U₂) V)
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ β α ?_
    dsimp
    simp only [add_smul, map_add, ← ConcreteCategory.comp_apply, ← Functor.map_comp, *]
  zero_smul m := Quot.induction_on m <| by
    rintro ⟨V, b⟩
    refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ (𝟙 _) (leftToMax _ _) ?_
    dsimp
    simp only [map_zero, zero_smul, *]

/-- Given a cofiltered diagram of rings `R`, and a module `M` over `R`,
this is the `colim R`-module structure of `colim M`. -/
noncomputable abbrev IsColimit.module {cR : Cocone R} (hcR : IsColimit cR) {cM : Cocone M}
    (hcM : IsColimit cM) : Module cR.pt cM.pt :=
  letI := filteredColimitsModule R M H
  letI : Module (RingCat.FilteredColimits.colimit R) cM.pt :=
    AddEquiv.module (β := AddCommGrpCat.FilteredColimits.colimit M) _
        (IsColimit.coconePointUniqueUpToIso hcM
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit M)).addCommGroupIsoToAddEquiv
  .compHom (R := RingCat.FilteredColimits.colimit R) _
    (IsColimit.coconePointUniqueUpToIso hcR
          (RingCat.FilteredColimits.colimitCoconeIsColimit R)).ringCatIsoToRingEquiv.toRingHom

set_option backward.isDefEq.respectTransparency false in
lemma IsColimit.ι_smul {cR : Cocone R} (hcR : IsColimit cR) {cM : Cocone M}
    (hcM : IsColimit cM) (i : C) (r : R.obj i) (m : M.obj i) :
    letI := IsColimit.module R M H hcR hcM
    cM.ι.app i (r • m) =
      HSMul.hSMul (α := cR.pt) (β := cM.pt) (cR.ι.app i r) (cM.ι.app i m) := by
  letI := filteredColimitsModule R M H
  let α := IsColimit.coconePointUniqueUpToIso hcM
    (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit M)
  let β := IsColimit.coconePointUniqueUpToIso hcR
    (RingCat.FilteredColimits.colimitCoconeIsColimit R)
  apply α.addCommGroupIsoToAddEquiv.eq_symm_apply.mpr ?_
  change (cM.ι.app i ≫ α.hom) _ = (HSMul.hSMul (α := RingCat.FilteredColimits.colimit R)
    (β := AddCommGrpCat.FilteredColimits.colimit M)
    ((cR.ι.app i ≫ β.hom) r) ((cM.ι.app i ≫ α.hom) m))
  simp only [Functor.const_obj_obj, comp_coconePointUniqueUpToIso_hom, α, β]
  obtain ⟨s, α, H⟩ :=  IsFilteredOrEmpty.cocone_maps (leftToMax i i) (rightToMax i i)
  refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ (leftToMax _ _ ≫ α) α ?_
  dsimp
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, *]

end CategoryTheory.Limits

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R)

variable (x : X)

set_option backward.isDefEq.respectTransparency false in
noncomputable
instance : Module (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.module ((OpenNhds.inclusion x).op ⋙ R) ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _) (Limits.colimit.isColimit _) (Limits.colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
lemma germ_ringCat_smul (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.ι_smul ((OpenNhds.inclusion x).op ⋙ R) ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _)
      (Limits.colimit.isColimit _) (Limits.colimit.isColimit _) ⟨_, _⟩ _ _

section CommRingCat

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in
noncomputable
instance (x : X) : Module (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ RingCat).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.module ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ _)
    ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _) (Limits.isColimitOfPreserves (forget₂ _ _)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))) (Limits.colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
lemma germ_smul (x : X) (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ RingCat).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.ι_smul ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ _)
    ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _) (Limits.isColimitOfPreserves (forget₂ _ _)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))) (Limits.colimit.isColimit _)
      ⟨_, _⟩ _ _

end CommRingCat

end PresheafOfModules
