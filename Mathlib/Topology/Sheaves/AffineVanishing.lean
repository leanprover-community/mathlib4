/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable (U X : Scheme.{u}) (f : U ⟶ X) [hf : IsOpenImmersion f] (M : X.Modules)

variable {X} in
noncomputable abbrev sheaf : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf _).obj M

variable {X} in
noncomputable abbrev Hom.sheafhom {F G : X.Modules} (φ : F ⟶ G) : F.sheaf ⟶ G.sheaf := (SheafOfModules.toSheaf _).map φ

variable {F G : X.Modules} (φ : F ⟶ G)

/-
#check ((restrictAdjunction f).unit.app M)
#check M.sheaf
#check (SheafOfModules.toSheaf _).obj ((restrictFunctor f ⋙ pushforward f).obj M)
#check hf.base_open
#check M.presheaf
#check (TopCat.Sheaf.restrict _ hf.base_open ⋙ TopCat.Sheaf.pushforward _ f.base).obj M.sheaf
-/

#check TopCat.Sheaf.toRestrict

example : ((restrictFunctor f ⋙ pushforward f).obj M).sheaf =
  (TopCat.Sheaf.restrict _ hf.base_open ⋙ TopCat.Sheaf.pushforward _ f.base).obj M.sheaf := rfl

lemma restrictAdjunction_sheafhom : ((restrictAdjunction f).unit.app M).sheafhom =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ hf.base_open).unit.app M.sheaf := rfl

lemma restrictAdjunction_toSheaf_map : (SheafOfModules.toSheaf X.ringCatSheaf).map ((restrictAdjunction f).unit.app M) =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ hf.base_open).unit.app M.sheaf := rfl

lemma restrictAdjunction_toRestrict (U : X.Opens) : ((restrictAdjunction U.ι).unit.app M).sheafhom =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ U.instIsOpenImmersionι.base_open).unit.app M.sheaf := by
  apply restrictAdjunction_sheafhom

end AlgebraicGeometry.Scheme.Modules

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    Subsingleton (H ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) r))
    (c : H F (n + 1)) : ∃ (I : Type u) (U : I → Opens X) (_ : IsOpenCover U),
    (∀ i, U i ∈ B ∧ TopCat.Sheaf.H.map ((toRestrict _ (U i)).app F) (n + 1) c = 0) := sorry

end TopCat.Sheaf

#check IsCompact.elim_finite_subcover
#check Finset.restrict

lemma CompactSpace.elim_finite_isOpenCover {X : Type u} [TopologicalSpace X] {I : Type v}
    {U : I → Opens X} (h : IsOpenCover U) : ∃ ι : Finset I, IsOpenCover <| Finset.restrict ι U :=
  sorry

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf Limits Opposite

variable {X : Scheme.{u}} [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]

theorem base : Subsingleton (H F.sheaf 1) := by

  sorry

example (r : ℕ) (hr : 1 ≤ r) : r - 1 + 1 = r := Nat.sub_add_cancel hr

open ConcreteCategory

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem induct (n : ℕ) (hi : ∀ m ≤ n, ∀ {X : Scheme.{u}} [IsAffine X] (F : X.Modules) [F.IsQuasicoherent],
    Subsingleton (H F.sheaf (m + 1))) : ∀ {X : Scheme.{u}} [IsAffine X] (F : X.Modules) [F.IsQuasicoherent],
      Subsingleton (H F.sheaf (n + 1 + 1)) := by
  intro X _ F _
  apply subsingleton_of_forall_eq 0
  intro c
  obtain ⟨I, ⟨(U : I → X.Opens) , ⟨hU, vanish⟩⟩⟩ := Sheaf.prop1 F.sheaf (n + 1) (isBasis_affineOpens X)
    sorry (by
      intro r (U : X.Opens) hr1 hr2 hU
      haveI : IsAffine U := hU
      haveI : ((restrictFunctor U.ι).obj F).IsQuasicoherent := sorry
      have v := hi (r - 1) (by lia) ((restrictFunctor U.ι).obj F)
      rw [Nat.sub_add_cancel hr1] at v
      exact v) c
  haveI : Finite I := sorry
  let j (i : I) : X.Modules := (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F
  let G : X.Modules := ∏ᶜ j
  let res : F ⟶ G := Pi.lift (fun i => ((restrictAdjunction (U i).ι).unit.app F))
  haveI : Mono res.sheafhom := by
    apply Sheaf.mono_of_injective
    intro W
    rw [injective_iff_map_eq_zero]
    intro s hs
    apply TopCat.Presheaf.IsSheaf.section_ext
    · exact F.sheaf.property
    intro x hx
    obtain ⟨i, hi⟩ := hU.exists_mem x
    use (unop W) ⊓ (U i)
    use inf_le_left
    refine ⟨by rw[Opens.mem_inf]; exact ⟨hx, hi⟩, ?_⟩
    rw [map_zero]
    have reszero : ((restrictAdjunction (U i).ι).unit.app F).sheafhom.hom.app W s = 0 := sorry
    rw [restrictAdjunction_sheafhom] at reszero
    simp only [Functor.comp_obj, SheafOfModules.toSheaf_obj_obj, sheafCompose_obj_obj,
      PresheafOfModules.presheaf_obj_coe, CommRingCat.forgetToRingCat_obj, Functor.id_obj,
      InducedCategory.homMk_hom, Adjunction.sheafPushforwardContinuous_unit_app_hom_app] at reszero
    have : ((unop W) ⊓ (U i)) ≤ ((U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj
      (unop W))) := by aesop
    convert DFunLike.congr_arg (ConcreteCategory.hom (F.sheaf.obj.map (homOfLE this).op)) reszero
    · erw [← ConcreteCategory.comp_apply]
      congr
      dsimp [sheaf]
      rw [← Functor.map_comp]
      congr
    simp only [map_zero]
  haveI : Mono res := Functor.mono_of_mono_map (SheafOfModules.toSheaf X.ringCatSheaf) this
  let S := ShortComplex.mk res (cokernel.π res) (by cat_disch)
  have : Function.Injective (H.map res.sheafhom (n + 1 + 1)) := by
    haveI : S.X₃.IsQuasicoherent := sorry
    have := hi n (le_refl n) S.X₃
    rw [injective_iff_map_eq_zero]
    intro c hc
    sorry
  apply this
  change ((SheafOfModules.toSheaf _) ⋙ (functorH X (n + 1 + 1))).map res c =
    ((SheafOfModules.toSheaf _) ⋙ (functorH X (n + 1 + 1))).map res 0
  haveI : (SheafOfModules.toSheaf X.ringCatSheaf ⋙ functorH X (n + 1 + 1)).Additive := inferInstance
  apply Limits.Concrete.Pi.map_ext j ((SheafOfModules.toSheaf X.ringCatSheaf ⋙ functorH X (n + 1 + 1)))
  intro i
  simp only [map_zero]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have : (res ≫ Pi.π j i) = (restrictAdjunction (U i).ι).unit.app F := by simp [G, j, res]
  rw [this]
  simp only [Functor.comp_obj, CategoryTheory.Sheaf.functorH_obj_coe, Functor.comp_map,
    Sheaf.functorH_map, AddCommGrpCat.hom_ofHom]
  conv => lhs; left; arg 1; rw [restrictAdjunction_toSheaf_map]
  exact (vanish i).right

end AlgebraicGeometry.Scheme.Modules
