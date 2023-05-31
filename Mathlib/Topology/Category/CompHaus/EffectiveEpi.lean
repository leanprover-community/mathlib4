/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.ExplicitLimits

/-!

# Effective epimorphic families in `CompHaus`

Let `π a : X a ⟶ B` be a family of morphisms in `CompHaus` indexed by a finite type `α`.
In this file, we show that the following are all equivalent:
- The family `π` is effective epimorphic.
- The induced map `∐ X ⟶ B` is epimorphic.
- The family `π` is jointly surjective.
This is the main result of this file, which can be found in `CompHaus.effectiveEpiFamily_tfae`

As a consequence, we also show that `CompHaus` is precoherent.

# Projects

- Define regular categories, and show that `CompHaus` is regular.
- Define coherent categories, and show that `CompHaus` is actually coherent.

-/

open CategoryTheory Limits

namespace CompHaus

namespace EffectiveEpiFamily

universe u

variable {α : Type} [Fintype α] {B : CompHaus.{u}}
  {X : α → CompHaus.{u}} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

def relation : Setoid (FiniteCoproduct X) where
  r a b := ∃ (Z : CompHaus.{u}) (z : Z)
    (fst : Z ⟶ X a.fst) (snd : Z ⟶ X b.fst),
    fst ≫ π _ = snd ≫ π _ ∧ fst z = a.snd ∧ snd z = b.snd
  iseqv := by
    constructor
    · rintro ⟨a,x⟩
      refine ⟨X a, x, 𝟙 _, 𝟙 _, by simp, rfl, rfl⟩
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,w,h1,h2⟩
      exact ⟨Z,z,snd,fst,w.symm,h2,h1⟩
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨z,c⟩ ⟨Z,z,fstZ,sndZ,hZ,hZ1,hZ2⟩ ⟨W,w,fstW,sndW,hW,hW1,hW2⟩
      refine ⟨Pullback sndZ fstW, ⟨⟨z,w⟩, by simp [hZ2, hW1]⟩,
        Pullback.fst _ _ ≫ fstZ, Pullback.snd _ _ ≫ sndW, ?_, hZ1, hW2⟩
      dsimp at *
      simp only [Category.assoc, hZ, ← hW]
      apply ContinuousMap.ext
      rintro ⟨⟨u,v⟩,h⟩
      change π b (sndZ u) = π b (fstW v)
      rw [h]

def ι_fun : Quotient (relation π) → B :=
  Quotient.lift (fun ⟨a,x⟩ => π a x) <| by
    rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,h,hx,hy⟩
    dsimp at *
    rw [← hx, ← hy]
    apply_fun (fun t => t z) at h
    exact h

lemma ι_fun_continuous : Continuous (ι_fun π) := by
  apply Continuous.quotient_lift
  apply continuous_sigma
  intro a
  exact (π a).continuous

lemma ι_fun_injective : (ι_fun π).Injective := by
  rintro ⟨⟨a,x⟩⟩ ⟨⟨b,y⟩⟩ (h : π _ _ = π _ _)
  apply Quotient.sound'
  refine ⟨Pullback (π a) (π b), ⟨⟨x,y⟩,h⟩, Pullback.fst _ _, Pullback.snd _ _, ?_, rfl, rfl⟩
  ext ⟨_, h⟩ ; exact h

def QB : CompHaus.{u} :=
  haveI : T2Space (Quotient <| relation π) :=
    ⟨fun _ _ h => separated_by_continuous (ι_fun_continuous π) <| (ι_fun_injective π).ne h ⟩
  CompHaus.of (Quotient <| relation π)

def ι_hom : (QB π) ⟶ B := ⟨ι_fun π, ι_fun_continuous π⟩

noncomputable
def ι : (QB π) ≅ B :=
  haveI : IsIso (ι_hom π) := by
    apply isIso_of_bijective
    refine ⟨ι_fun_injective _, ?_⟩
    intro b
    obtain ⟨a,x,h⟩ := surj b
    refine ⟨Quotient.mk _ ⟨a,x⟩, h⟩
  asIso (ι_hom π)

def π' : (a : α) → (X a ⟶ QB π) := fun a =>
  { toFun := fun x => Quotient.mk _ ⟨a, x⟩
    continuous_toFun := by
      apply Continuous.comp
      apply continuous_quot_mk
      apply continuous_sigmaMk (σ := fun a => X a) }

def struct_aux : EffectiveEpiFamilyStruct X (π' π) where
  desc := fun {W} e h => {
    toFun := Quotient.lift (fun ⟨a,x⟩ => e a x) <| by
      rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,hh,hx,hy⟩ ; dsimp at *
      rw [← hx, ← hy]
      specialize h _ _ fst snd ?_
      · ext z
        apply ι_fun_injective
        apply_fun (fun q => q z) at hh
        exact hh
      apply_fun (fun q => q z) at h
      exact h
    continuous_toFun := by
      apply Continuous.quotient_lift
      apply continuous_sigma
      intro a
      exact (e a).continuous }
  fac := by intro Z e h a ; ext ; rfl
  uniq := by
    intro Z e h m hm
    ext ⟨⟨a,x⟩⟩
    specialize hm a
    apply_fun (fun q => q x) at hm
    exact hm

@[reassoc (attr := simp)]
lemma π'_comp_ι_hom (a : α) : π' π a ≫ (ι _ surj).hom = π a := by ext ; rfl

@[reassoc (attr := simp)]
lemma π_comp_ι_inv (a : α) : π a ≫ (ι _ surj).inv = π' π a :=  by
  rw [Iso.comp_inv_eq]
  exact π'_comp_ι_hom _ surj _

-- TODO: Make a general construction for transferring such structs along isomorphisms.
noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => (ι π surj).inv ≫ (struct_aux π).desc e (fun {Z} a₁ a₂ g₁ g₂ hh => by
      apply h
      rw [← cancel_mono (ι _ surj).inv]
      simpa only [Category.assoc, π_comp_ι_inv])
  fac := by
    intro W e h a
    simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, π_comp_ι_inv_assoc, (struct_aux π).fac]
  uniq := by
    intro W e h m hm
    dsimp
    rw [Iso.eq_inv_comp]
    apply (struct_aux π).uniq
    intro a
    simpa using hm a

end EffectiveEpiFamily

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨CompHaus.EffectiveEpiFamily.struct π surj⟩⟩

open EffectiveEpiFamily

theorem effectiveEpiFamily_tfae
    {α : Type} [Fintype α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B)) :
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ].TFAE := by
  tfae_have 1 → 2
  · intro ; infer_instance
  tfae_have 2 → 3
  · intro e ; rw [epi_iff_surjective] at e
    let i : ∐ X ≅ FiniteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (FiniteCoproduct.isColimit _)
    intro b
    obtain ⟨t,rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id] ; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = FiniteCoproduct.desc X π by
      rw [this] ; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext ; rfl
  tfae_have 3 → 1
  · apply effectiveEpiFamily_of_jointly_surjective
  tfae_finish

instance Precoherent : Precoherent CompHaus.{u} := by
  constructor
  intro B₁ B₂ f α _ X₁ π₁ h₁
  refine ⟨α, inferInstance, fun a => Pullback f (π₁ a), fun a => Pullback.fst _ _, ?_,
    id, fun a => Pullback.snd _ _, ?_⟩
  · have := (effectiveEpiFamily_tfae _ π₁).out 0 2 ; rw [this] at h₁ ; clear this
    have := (effectiveEpiFamily_tfae _ (fun a => Pullback.fst f (π₁ a))).out 0 2
    rw [this] ; clear this
    intro b₂
    obtain ⟨a,x,h⟩ := h₁ (f b₂)
    refine ⟨a, ⟨⟨b₂, x⟩, h.symm⟩, rfl⟩
  · intro a
    dsimp
    ext ⟨⟨_,_⟩,h⟩
    exact h.symm

end CompHaus
