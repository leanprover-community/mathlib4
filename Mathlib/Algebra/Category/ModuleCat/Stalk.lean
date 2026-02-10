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

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R)

variable (x : X)

/-- (Implementation). The action of `Rₓ` on `Mₓ` of `M`, a presheaf of `R`-modules. -/
protected noncomputable
def smul (r : ((OpenNhds.inclusion x).op ⋙ R ⋙ forget _).ColimitType)
    (m : ((OpenNhds.inclusion x).op ⋙ M.presheaf ⋙ forget _).ColimitType) :
    ((OpenNhds.inclusion x).op ⋙ M.presheaf ⋙ forget _).ColimitType := by
  refine Quot.liftOn₂ r m (fun Ua Vb ↦ Functor.ιColimitType _ (.op <| Ua.1.unop ⊓ Vb.1.unop) <|
    letI a : R.obj (op <| Ua.1.unop.1 ⊓ Vb.1.unop.1) := R.map (homOfLE inf_le_left).op Ua.2
    letI b : M.obj (op <| Ua.1.unop.1 ⊓ Vb.1.unop.1) := M.map (homOfLE inf_le_right).op Vb.2
    a • b) ?_ ?_
  · rintro ⟨U, a⟩ ⟨V₁, b₁⟩ ⟨V₂, b₂⟩ ⟨f : V₁ ⟶ V₂,
      rfl : b₂ = M.presheaf.map (homOfLE f.unop.le).op b₁⟩
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr
      (.rel _ _ ⟨(homOfLE (inf_le_inf_left _ f.unop.le)).op, ((M.map_smul ..).trans ?_).symm⟩)
    dsimp only
    congr 1
    · exact congr($(R.map_comp _ _) _).symm
    · change (M.presheaf.map _ ≫ M.presheaf.map _) _ = (M.presheaf.map _ ≫ M.presheaf.map _) _
      simp_rw [← Functor.map_comp]; rfl
  · rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩ ⟨f : U₁ ⟶ U₂, rfl : a₂ = R.map (homOfLE f.unop.le).op a₁⟩
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr
      (.rel _ _ ⟨(homOfLE (inf_le_inf_right _ f.unop.le)).op, ((M.map_smul ..).trans ?_).symm⟩)
    dsimp only
    congr 1
    · change (R.map _ ≫ R.map _) _ = (R.map _ ≫ R.map _) _
      simp_rw [← Functor.map_comp]; rfl
    · change (M.presheaf.map _ ≫ M.presheaf.map _) _ = M.presheaf.map _ _
      simp_rw [← Functor.map_comp]; rfl

noncomputable
instance : Module (RingCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ R))
    (AddCommGrpCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ M.presheaf)) where
  smul := M.smul x
  mul_smul r s m := Quot.induction_on₃ r s m <| by
    rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩
    change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
    dsimp [PresheafOfModules.smul]
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr (.symm _ _ <| .rel _ _ ⟨(homOfLE ?_).op, ?_⟩)
    · simp only [le_inf_iff, inf_le_right, and_true]
      exact ⟨by grw [(IsFiltered.leftToMax U₁ U₂).unop.le]; simp,
        by grw [(IsFiltered.rightToMax U₁ U₂).unop.le]; simp⟩
    · simp [(presheaf_map_apply_coe), OpenNhds.inclusion, ← elementwise_of% R.map_comp,
        -Functor.map_comp, ← M.map_comp_apply, - map_comp, mul_smul]
      rfl
  one_smul m := Quot.induction_on m <| by
    rintro ⟨V, b⟩
    change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
    dsimp [PresheafOfModules.smul]
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr (.symm _ _ <| .rel _ _ ⟨(homOfLE ?_).op, ?_⟩)
    · simp
    · simp; rfl
  smul_zero r := Quot.induction_on r <| by
    rintro ⟨U, a⟩
    change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
    dsimp [PresheafOfModules.smul]
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr (.symm _ _ <| .rel _ _ ⟨(homOfLE ?_).op, ?_⟩)
    · simp
    · simp
  smul_add r m n := Quot.induction_on₃ r m n <| by
    rintro ⟨U, a⟩ ⟨V₁, b₁⟩ ⟨V₂, b₂⟩
    change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
    dsimp [PresheafOfModules.smul]
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr ?_
    let W := (unop U ⊓ unop (IsFiltered.max V₁ V₂)) ⊓
      (unop (IsFiltered.max (op (unop U ⊓ unop V₁)) (op (unop U ⊓ unop V₂))))
    refine .trans _ _ _ (.rel _ (Sigma.mk (op W) ?_) ⟨(homOfLE inf_le_left).op, ?_⟩) ?_
    swap; · dsimp only; rfl
    refine (.symm _ _ <| .rel _ _ ⟨(homOfLE inf_le_right).op, ?_⟩)
    simp [(presheaf_map_apply_coe), OpenNhds.inclusion, ← elementwise_of% R.map_comp,
        -Functor.map_comp, ← M.map_comp_apply, - map_comp]
    rfl
  add_smul r s m := Quot.induction_on₃ r s m <| by
    rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩
    change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
    dsimp [PresheafOfModules.smul]
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr ?_
    let W := (IsFiltered.max (op (unop U₁ ⊓ unop V)) (op (unop U₂ ⊓ unop V))).unop ⊓
      (unop (IsFiltered.max U₁ U₂) ⊓ unop V)
    refine .trans _ _ _ (.rel _ (Sigma.mk (op W) ?_) ⟨(homOfLE inf_le_right).op, ?_⟩) ?_
    swap; · dsimp only; rfl
    refine (.symm _ _ <| .rel _ _ ⟨(homOfLE inf_le_left).op, ?_⟩)
    simp [(presheaf_map_apply_coe), OpenNhds.inclusion, ← elementwise_of% R.map_comp,
        -Functor.map_comp, ← M.map_comp_apply, - map_comp, add_smul]
    rfl
  zero_smul m := Quot.induction_on m <| by
    rintro ⟨V, b⟩
    change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
    dsimp [PresheafOfModules.smul]
    refine (Functor.ιColimitType_eq_iff _ _ _).mpr (.symm _ _ <| .rel _ _ ⟨(homOfLE ?_).op, ?_⟩)
    · simp
    dsimp
    simp

noncomputable
instance : Module (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  letI : Module (RingCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ R))
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
    AddEquiv.module (β := (AddCommGrpCat.FilteredColimits.colimit
      ((OpenNhds.inclusion x).op ⋙ M.presheaf))) _ (Limits.colimit.isoColimitCocone
        ⟨_, (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
          ((OpenNhds.inclusion x).op ⋙ M.presheaf))⟩).addCommGroupIsoToAddEquiv
  .compHom (R := (RingCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ R))) _
    (Limits.colimit.isoColimitCocone
        ⟨_, (RingCat.FilteredColimits.colimitCoconeIsColimit
          ((OpenNhds.inclusion x).op ⋙ R))⟩).ringCatIsoToRingEquiv.toRingHom

lemma germ_ringCat_smul (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m := by
  let α : R.stalk x ≅ RingCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ R) :=
    Limits.colimit.isoColimitCocone ⟨_, (RingCat.FilteredColimits.colimitCoconeIsColimit
      ((OpenNhds.inclusion x).op ⋙ R))⟩
  have hα (a : _) : (R.germ U x hx ≫ α.hom) a =
      ((OpenNhds.inclusion x).op ⋙ R ⋙ forget _).ιColimitType (.op ⟨U, hx⟩) a := by
    simp only [TopCat.Presheaf.germ, Limits.colimit.isoColimitCocone_ι_hom, α]; rfl
  let β : ↑(TopCat.Presheaf.stalk M.presheaf x) ≅
    AddCommGrpCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ M.presheaf) :=
    Limits.colimit.isoColimitCocone
        ⟨_, (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
          ((OpenNhds.inclusion x).op ⋙ M.presheaf))⟩
  have hβ (a : _) : (TopCat.Presheaf.germ M.presheaf U x hx ≫ β.hom) a =
      ((OpenNhds.inclusion x).op ⋙ M.presheaf ⋙ forget _).ιColimitType (.op ⟨U, hx⟩) a := by
    simp only [TopCat.Presheaf.germ, Limits.colimit.isoColimitCocone_ι_hom, β]; rfl
  change _ = β.inv (α.hom (R.germ U x hx r) • β.hom (TopCat.Presheaf.germ M.presheaf U x hx m))
  refine β.addCommGroupIsoToAddEquiv.eq_symm_apply.mpr ?_
  dsimp only [Iso.addCommGroupIsoToAddEquiv_apply, AddCommGrpCat.Hom.hom]
  simp_rw [← ConcreteCategory.comp_apply, hα, hβ]
  change Functor.ιColimitType _ _ _ = Functor.ιColimitType _ _ _
  dsimp [PresheafOfModules.smul]
  refine (Functor.ιColimitType_eq_iff _ _ _).mpr (.rel _ _ ⟨eqToHom (by simp), ?_⟩)
  simp [(presheaf_map_apply_coe)]
  rfl

section CommRingCat

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

noncomputable
instance (x : X) : Module (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  .compHom _ (R := ↑(TopCat.Presheaf.stalk (R ⋙ forget₂ _ RingCat) x)) <|
    (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (Limits.colimit.isColimit
      ((OpenNhds.inclusion x).op ⋙ R))⟩).ringCatIsoToRingEquiv.symm.toRingHom

lemma germ_smul (x : X) (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m := by
  let α : (TopCat.Presheaf.stalk (R ⋙ forget₂ _ RingCat) x) ≅
      (forget₂ _ _).obj (R.stalk x) :=
    Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))⟩
  change _ = ((forget₂ CommRingCat RingCat).map (R.germ U x hx) ≫ α.inv) r •
    TopCat.Presheaf.germ M.presheaf U x hx m
  refine (germ_ringCat_smul M x U hx r m).trans ?_
  congr 3
  rw [Iso.eq_comp_inv]
  simp [α, TopCat.Presheaf.germ]

end CommRingCat

end PresheafOfModules
