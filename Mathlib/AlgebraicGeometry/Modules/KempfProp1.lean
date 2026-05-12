/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Restrict

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

open Topology

theorem IsFlasue.of_restrict (C : Type*) [Category* C] {Y : TopCat.{u}} {f : Y ⟶ X}
    (F : TopCat.Sheaf C X) [F.IsFlasque] (hf : IsOpenEmbedding f) :
    ((restrict C hf).obj F).IsFlasque where
  epi i := by
    dsimp
    exact IsFlasque.epi' F _

section

attribute [local instance] Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
  Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

instance {Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    (restrict AddCommGrpCat.{u} hf).Additive := Functor.additive_of_preservesBinaryBiproducts _

instance {Y : TopCat.{u}} {f : Y ⟶ X} :
    (pushforward AddCommGrpCat.{u} f).Additive := Functor.additive_of_preservesBinaryBiproducts _

instance (U : Opens X) : (restrict AddCommGrpCat.{u} U.isOpenEmbedding).IsRightAdjoint := sorry

end

lemma _root_.TopologicalSpace.IsOpenCover.def {ι X : Type*} [TopologicalSpace X] (U : ι → Opens X) :
    IsOpenCover U ↔ ∀ x, ∃ i, x ∈ U i := by
  refine ⟨fun hU x => hU.exists_mem x, fun hU => ?_⟩
  rw [IsOpenCover, ← SetLike.coe_set_eq, Opens.coe_iSup]
  ext
  simp [hU]

set_option backward.isDefEq.respectTransparency false in
lemma base (F : TopCat.Sheaf AddCommGrpCat.{u} X) {B : Set (Opens X)}
    (hB : Opens.IsBasis B) (c : H F 1) (x : X) : ∃ (U : Opens X),
    (x ∈ U ∧ U ∈ B ∧ H.map ((toRestrict _ U).app F) 1 c = 0) := by
  let pres := (EnoughInjectives.presentation F).some.shortComplex
  have presEx : pres.ShortExact := (EnoughInjectives.presentation F).some.shortExact_shortComplex
  obtain ⟨b, hb⟩ :=
    Sheaf.H.longSequence_equiv₀_exact₁ presEx Limits.isTerminalTop c (Subsingleton.elim _ _)
  have := presEx.3
  rw [← isLocallySurjective_iff_epi, Presheaf.isLocallySurjective_iff] at this
  obtain ⟨V', ⟨hV'₁, ⟨⟨s', hs'⟩, hV'₃⟩⟩⟩ := this ⊤ b x (Opens.mem_top x)
  obtain ⟨V, ⟨hV₁, ⟨hV₂, hV₃⟩⟩⟩ := Opens.isBasis_iff_nbhd.mp hB hV'₃
  refine ⟨V, ⟨hV₂, ⟨hV₁, ?_⟩⟩⟩
  let s := pres.X₂.obj.map (homOfLE hV₃).op s'
  have hs : pres.g.hom.app (op V) s = pres.X₃.obj.map V.leTop.op b := sorry
  clear_value s
  clear V' hV'₁ hV'₃ s' hs' hV₃ hV₁ hV₂ this

  sorry

set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    Subsingleton (H ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) r))
    (c : H F (n + 1)) : ∃ (I : Type u) (U : I → Opens X), (IsOpenCover U) ∧
    (∀ i, U i ∈ B ∧ H.map ((toRestrict _ (U i)).app F) (n + 1) c = 0) := by
  induction n generalizing F with
  | zero =>
    use X, (fun x => (base F hB c x).choose)
    refine ⟨?_, fun x => (base F hB c x).choose_spec.2⟩
    rw [IsOpenCover.def]
    exact fun x => ⟨x, (base F hB c x).choose_spec.1⟩
  | succ n hn =>
    let pres := (EnoughInjectives.presentation F).some.shortComplex
    have presEx : pres.ShortExact := (EnoughInjectives.presentation F).some.shortExact_shortComplex
    obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁ presEx (n + 1) (n + 1 + 1) rfl c
      (Subsingleton.elim _ _)
    obtain ⟨I, ⟨U, ⟨hU₁, hU₂⟩⟩⟩ := hn pres.X₃ (by
      intro r U hr₁ hr₂ hU
      refine subsingleton_of_forall_eq 0 (fun x => ?_)
      let presᵤ := pres.map (restrict _ U.isOpenEmbedding)
      have presᵤEx : presᵤ.ShortExact := presEx.map_of_exact _
      have : Subsingleton (presᵤ.X₁.H (r + 1)) := vanish (r + 1) U (by omega) (by omega) hU
      obtain ⟨x₂, rfl⟩ :=
        Sheaf.H.longSequence_exact₃ presᵤEx r (r + 1) rfl x (Subsingleton.elim _ _)
      have : Subsingleton (presᵤ.X₂.H r) := by
        have : presᵤ.X₂.IsFlasque := IsFlasue.of_restrict _ pres.X₂ U.isOpenEmbedding
        rw [(Nat.sub_eq_iff_eq_add hr₁).mp rfl]
        infer_instance
      rw [Subsingleton.elim x₂ 0]
      simp) b
    use I, U, hU₁
    refine fun i => ⟨(hU₂ i).left, ?_⟩
    have : (pres.map (restrict AddCommGrpCat (U i).isOpenEmbedding ⋙ pushforward AddCommGrpCat
        (U i).inclusion')).ShortExact := by
      have := ((restrict AddCommGrpCat (U i).isOpenEmbedding ⋙ pushforward AddCommGrpCat
          (U i).inclusion').preservesFiniteLimits_tfae.out 3 1 rfl rfl).mp inferInstance pres
          ⟨presEx.1, presEx.2⟩
      refine ShortComplex.ShortExact.mk' this.1 this.2 ?_
      dsimp
      rw [← isLocallySurjective_iff_epi, Presheaf.isLocallySurjective_iff]
      intro V s x hx
      obtain ⟨W, hW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
      use W, hW.2.2
      refine ⟨?_, hW.2.1⟩
      have fs {V : Opens X} (hV : V ∈ B) : Function.Surjective (pres.g.hom.app (op V)) := by
        erw [← Opens.isOpenEmbedding_obj_top V]
        let presᵥ := pres.map (restrict _ V.isOpenEmbedding)
        have presᵥEx : presᵥ.ShortExact := presEx.map_of_exact _
        have : Subsingleton (presᵥ.X₁.H 1) := vanish 1 V (le_refl 1) (by omega) hV
        exact Sheaf.H.longSequence_surjective_of_subsingleton_H presᵥEx Limits.isTerminalTop
      have : (U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj W) ∈ B := by
        rw [func_inc]
        exact hinter _ _ (hU₂ i).1 hW.1
      apply fs this
    have r₁ := Sheaf.H.connectingHom_naturality (n + 1) (n + 1 + 1) rfl presEx this
      (pres.mapNatTrans (toRestrict AddCommGrpCat (U i))) b
    have r₂ := (hU₂ i).right
    dsimp [pres] at r₁ r₂ ⊢
    rw [← hb, ← r₁, r₂]
    erw [map_zero]

end TopCat.Sheaf
#min_imports
