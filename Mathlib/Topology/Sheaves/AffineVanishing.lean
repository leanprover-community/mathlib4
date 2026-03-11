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

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    Subsingleton (H ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) r))
    (c : H F (n + 1)) : ∃ (I : Type u) (U : I → Opens X) (_ : IsOpenCover U),
    (∀ i, U i ∈ B ∧ H.map ((toRestrict _ (U i)).app F) (n + 1) c = 0) := sorry

end TopCat.Sheaf

namespace CompactSpace

lemma isOpenCover_elim_finite_subcover {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {ι : Type v} {U : ι → Opens X} (h : IsOpenCover U) :
    ∃ t : Finset ι, IsOpenCover (Finset.restrict t U) := by
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := X)) (fun i => U i)
    (fun i => (U i).2) (by rw [IsOpenCover.iSup_set_eq_univ h])
  use t
  apply IsOpenCover.of_sets
  rw [Set.univ_subset_iff] at ht
  rw [← ht, Set.iUnion_subtype]
  rfl

end CompactSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

section

variable (X) in
@[simps!]
noncomputable def toSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance : (toSheaf X).Additive := inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance : Limits.PreservesFiniteLimits (toSheaf X) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

instance : Limits.PreservesFiniteColimits (toSheaf X) := sorry

noncomputable abbrev sheaf : TopCat.Sheaf AddCommGrpCat X := (toSheaf X).obj F

noncomputable abbrev Hom.sheafHom {F G : X.Modules} (φ : F ⟶ G) : F.sheaf ⟶ G.sheaf :=
  (toSheaf X).map φ

variable {U : Scheme.{u}} (f : U ⟶ X) [hf : IsOpenImmersion f]

example : ((restrictFunctor f ⋙ pushforward f).obj F).sheaf =
  (TopCat.Sheaf.restrict _ hf.base_open ⋙ TopCat.Sheaf.pushforward _ f.base).obj F.sheaf := rfl

lemma restrictAdjunction_sheafHom : ((restrictAdjunction f).unit.app F).sheafHom =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ hf.base_open).unit.app F.sheaf := rfl

lemma restrictAdjunction_toSheaf_map : (SheafOfModules.toSheaf X.ringCatSheaf).map
    ((restrictAdjunction f).unit.app F) =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ hf.base_open).unit.app F.sheaf := rfl

lemma restrictAdjunction_toRestrict (U : X.Opens) : ((restrictAdjunction U.ι).unit.app F).sheafHom =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ U.instIsOpenImmersionι.base_open).unit.app
    F.sheaf := by
  apply restrictAdjunction_sheafHom

end

open TopCat TopCat.Sheaf Limits Opposite

section

variable {I : Type u} (U : I → X.Opens)

noncomputable def CoverSheaf : X.Modules :=
  ∏ᶜ (fun i => (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F)

noncomputable def toCoverSheaf : F ⟶ F.CoverSheaf U :=
  Pi.lift (fun i => ((restrictAdjunction (U i).ι).unit.app F))

lemma toCoverSheaf_comp_pi (i : I) : (F.toCoverSheaf U) ≫
    (Pi.π (fun i => (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i)
    = (restrictAdjunction (U i).ι).unit.app F := by
  delta toCoverSheaf CoverSheaf
  simp [Pi.lift_π]

lemma toCoverSheaf_comp_pi_sheafHom_hom_app {V : X.Opens} (s : F.sheaf.obj.obj (op V)) (i : I)
    : (Pi.π (fun i => (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom.hom.app
      (op V) ((F.toCoverSheaf U).sheafHom.hom.app (op V) s)
    = ((restrictAdjunction (U i).ι).unit.app F).sheafHom.hom.app (op V) s := by
  have : ((F.toCoverSheaf U) ≫ (Pi.π (fun i =>
      (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i)).sheafHom.hom.app (op V) s
      = ((restrictAdjunction (U i).ι).unit.app F).sheafHom.hom.app (op V) s := by
    rw [toCoverSheaf_comp_pi]
    rfl
  simpa using this

set_option backward.isDefEq.respectTransparency false in
variable {U} in
theorem toCoverSheaf_mono (h : IsOpenCover U) : Mono (F.toCoverSheaf U) := by
  haveI : Mono (F.toCoverSheaf U).sheafHom := by
    apply Sheaf.mono_of_injective
    intro W
    rw [injective_iff_map_eq_zero]
    refine fun s hs => TopCat.Presheaf.IsSheaf.section_ext F.sheaf.property (fun x hx => ?_)
    obtain ⟨i, hi⟩ := h.exists_mem x
    use (unop W) ⊓ (U i), inf_le_left
    refine ⟨by rw [Opens.mem_inf]; exact ⟨hx, hi⟩, ?_⟩
    rw [map_zero]
    have reszero : ((restrictAdjunction (U i).ι).unit.app F).sheafHom.hom.app W s = 0 := by
      have := DFunLike.congr_arg (ConcreteCategory.hom ((Pi.π (fun i =>
        (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom.hom.app W)) hs
      erw [toCoverSheaf_comp_pi_sheafHom_hom_app, map_zero] at this
      simpa using this
    rw [restrictAdjunction_sheafHom] at reszero
    simp only [Functor.comp_obj, Functor.id_obj,
      InducedCategory.homMk_hom, Adjunction.sheafPushforwardContinuous_unit_app_hom_app] at reszero
    have : ((unop W) ⊓ (U i)) ≤ ((U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj
      (unop W))) := by aesop
    convert DFunLike.congr_arg (ConcreteCategory.hom (F.sheaf.obj.map (homOfLE this).op)) reszero
    · erw [← ConcreteCategory.comp_apply]
      congr
      dsimp [sheaf]
      erw [← Functor.map_comp]
      congr
    erw [map_zero]
  exact Functor.mono_of_mono_map (SheafOfModules.toSheaf X.ringCatSheaf) this

set_option backward.isDefEq.respectTransparency false in
theorem toCoverSheaf_H_map_zero (n : ℕ) (c : H F.sheaf n) [Finite I]
    (h : (∀ i, H.map ((toRestrict _ (U i)).app F.sheaf) n c = 0)) :
    H.map (F.toCoverSheaf U).sheafHom n c = 0 := by
  haveI : (SheafOfModules.toSheaf X.ringCatSheaf ⋙ functorH X n).Additive := inferInstance
  conv_lhs => change (SheafOfModules.toSheaf _ ⋙ functorH X n).map (F.toCoverSheaf U) c
  conv_rhs => equals (SheafOfModules.toSheaf _ ⋙ functorH X n).map (F.toCoverSheaf U) 0 =>
    rw [map_zero]
  delta toCoverSheaf CoverSheaf
  apply Limits.Concrete.Pi.map_ext
  intro i
  simp only [map_zero]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [Functor.comp_obj, CategoryTheory.Sheaf.functorH_obj_coe, Functor.comp_map,
    Sheaf.functorH_map, AddCommGrpCat.hom_ofHom, Pi.lift_π]
  rw [restrictAdjunction_toSheaf_map, ← h i]
  rfl

end

theorem base [IsAffine X] [F.IsQuasicoherent] : Subsingleton (H F.sheaf 1) := by
  apply subsingleton_of_forall_eq 0
  intro c
  obtain ⟨I, ⟨(U' : I → X.Opens) , ⟨hU', vanish⟩⟩⟩ := Sheaf.prop1 F.sheaf 0
    (isBasis_affineOpens X) sorry (by intros; lia) c
  obtain ⟨ι, hU⟩ := CompactSpace.isOpenCover_elim_finite_subcover hU'
  let U : ι → X.Opens := ι.restrict U'
  haveI : Mono (F.toCoverSheaf U) := F.toCoverSheaf_mono hU
  let S := ShortComplex.mk (F.toCoverSheaf U) (cokernel.π (F.toCoverSheaf U)) (by cat_disch)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (F.toCoverSheaf U))
  let Ssheaf := S.map (toSheaf X)
  have hSsheaf : Ssheaf.ShortExact := ShortComplex.ShortExact.map_of_exact hS (toSheaf X)
  have : Function.Surjective (H.map Ssheaf.g 0) := by
    rw [← Equiv.comp_surjective (H.map Ssheaf.g 0) (H.equiv₀ Ssheaf.X₃).toEquiv]
    conv => arg 1; equals (Ssheaf.g.hom.app (op ⊤)) ∘ (H.equiv₀ Ssheaf.X₂).toEquiv =>
      ext
      simp [H.equiv₀_naturality]
    rw [Equiv.surjective_comp (H.equiv₀ Ssheaf.X₂).toEquiv (Ssheaf.g.hom.app (op ⊤))]
    conv => arg 1; arg 1; arg 1; change S.g.sheafHom.hom.app (op ⊤)
    sorry
  obtain ⟨x₃, hx₃⟩ := Sheaf.H.longSequence_exact₁ hSsheaf 0 1 rfl c <|
    F.toCoverSheaf_H_map_zero U 1 c (fun i => (vanish i).right)
  obtain ⟨x₂, hx₂⟩ := this x₃
  simpa [← hx₃, ← hx₂] using Sheaf.H.map_comp_connectingHom_zero hSsheaf 0 1 rfl x₂

instance [IsAffine X] [F.IsQuasicoherent] (n : ℕ) : Subsingleton (H F.sheaf (n + 1)) := by
  revert F X
  refine Nat.case_strong_induction_on (p := fun n => ∀ {X : Scheme.{u}} (F : X.Modules)
    [IsAffine X] [F.IsQuasicoherent], Subsingleton (F.sheaf.H (n + 1))) n base ?_
  refine fun n hi X F _ _ => subsingleton_of_forall_eq 0 (fun c => ?_)
  obtain ⟨I, ⟨(U' : I → X.Opens) , ⟨hU', vanish⟩⟩⟩ := Sheaf.prop1 F.sheaf (n + 1)
    (isBasis_affineOpens X) sorry (by
      intro r (U : X.Opens) hr1 hr2 hU
      haveI : IsAffine U := hU
      haveI : ((restrictFunctor U.ι).obj F).IsQuasicoherent := sorry
      have v := hi (r - 1) (by lia) ((restrictFunctor U.ι).obj F)
      rw [Nat.sub_add_cancel hr1] at v
      exact v) c
  obtain ⟨ι, hU⟩ := CompactSpace.isOpenCover_elim_finite_subcover hU'
  let U : ι → X.Opens := ι.restrict U'
  haveI : Mono (F.toCoverSheaf U) := F.toCoverSheaf_mono hU
  let S := ShortComplex.mk (F.toCoverSheaf U) (cokernel.π (F.toCoverSheaf U)) (by cat_disch)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (F.toCoverSheaf U))
  let Ssheaf := S.map (toSheaf X)
  have hSsheaf : Ssheaf.ShortExact := ShortComplex.ShortExact.map_of_exact hS (toSheaf X)
  have : Function.Injective (H.map (F.toCoverSheaf U).sheafHom (n + 1 + 1)) := by
    haveI : S.X₃.IsQuasicoherent := sorry
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x₃, hx₃⟩ := Sheaf.H.longSequence_exact₁ hSsheaf (n + 1) (n + 1 + 1) rfl c hc
    haveI : Subsingleton (H Ssheaf.X₃ (n + 1)) := hi n (le_refl n) S.X₃
    rw [← hx₃, Subsingleton.elim x₃ 0, map_zero]
    rfl
  apply this
  rw [map_zero]
  exact F.toCoverSheaf_H_map_zero U (n + 1 + 1) c (fun i => (vanish i).right)

end AlgebraicGeometry.Scheme.Modules
