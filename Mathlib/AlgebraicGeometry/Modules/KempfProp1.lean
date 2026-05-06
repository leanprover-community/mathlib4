/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib
public import Mathlib.AlgebraicGeometry.Modules.Quasicoherent

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace

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

end

set_option backward.isDefEq.respectTransparency false in
theorem prop1 (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ (U V : Opens X), U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X), 1 ≤ r → r ≤ n → U ∈ B →
    Subsingleton (H ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) r))
    (c : H F (n + 1)) : ∃ (I : Type u) (U : I → Opens X) (_ : IsOpenCover U),
    (∀ i, U i ∈ B ∧ H.map ((toRestrict _ (U i)).app F) (n + 1) c = 0) := by
  induction n generalizing F with
  | zero => sorry
  | succ n hn =>
    let pres := (EnoughInjectives.presentation F).some.shortComplex
    have presEx : pres.ShortExact := (EnoughInjectives.presentation F).some.shortExact_shortComplex
    obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁ presEx (n + 1) (n + 1 + 1) rfl c
      (Subsingleton.elim _ _)
    obtain ⟨I, ⟨U, ⟨hU₁, hU₂⟩⟩⟩ := hn pres.X₃ (by
      intro r U hr₁ hr₂ hU
      refine subsingleton_of_forall_eq 0 (fun x => ?_)
      let presᵤ := pres.map (restrict _ U.isOpenEmbedding)
      have : (restrict AddCommGrpCat.{u} U.isOpenEmbedding).IsRightAdjoint := sorry
      have presᵤEx : presᵤ.ShortExact := presEx.map_of_exact _
      have : Subsingleton (presᵤ.X₁.H (r + 1)) := vanish (r + 1) U sorry sorry hU
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
    rw [← hb]
    let φ := pres.mapNatTrans (toRestrict AddCommGrpCat (U i))
    dsimp at φ
    
    sorry

end TopCat.Sheaf
