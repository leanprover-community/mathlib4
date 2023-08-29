/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Limits

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

set_option autoImplicit true

open CategoryTheory Limits

namespace CompHaus

namespace EffectiveEpiFamily

universe u

variable {α : Type} [Fintype α] {B : CompHaus.{u}}
  {X : α → CompHaus.{u}} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/--
Implementation: This is a setoid on the explicit finite coproduct of `X` whose quotient
will be isomorphic to `B` provided that `X a → B` is an effective epi family.
-/
def relation : Setoid (finiteCoproduct X) where
  r a b := ∃ (Z : CompHaus.{u}) (z : Z)
    (fst : Z ⟶ X a.fst) (snd : Z ⟶ X b.fst),
    fst ≫ π _ = snd ≫ π _ ∧ fst z = a.snd ∧ snd z = b.snd
  iseqv := by
    constructor
    · rintro ⟨a,x⟩
      -- ⊢ ∃ Z z fst snd, fst ≫ π { fst := a, snd := x }.fst = snd ≫ π { fst := a, snd  …
      refine ⟨X a, x, 𝟙 _, 𝟙 _, by simp, rfl, rfl⟩
      -- 🎉 no goals
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,w,h1,h2⟩
      -- ⊢ ∃ Z z fst snd, fst ≫ π { fst := b, snd := y }.fst = snd ≫ π { fst := a, snd  …
      exact ⟨Z,z,snd,fst,w.symm,h2,h1⟩
      -- 🎉 no goals
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨z,c⟩ ⟨Z,z,fstZ,sndZ,hZ,hZ1,hZ2⟩ ⟨W,w,fstW,sndW,hW,hW1,hW2⟩
      -- ⊢ ∃ Z z fst snd, fst ≫ π { fst := a, snd := x }.fst = snd ≫ π { fst := z✝, snd …
      refine ⟨pullback sndZ fstW, ⟨⟨z,w⟩, by dsimp; rw [hZ2, hW1]⟩,
        pullback.fst _ _ ≫ fstZ, pullback.snd _ _ ≫ sndW, ?_, hZ1, hW2⟩
      dsimp at *
      -- ⊢ (pullback.fst sndZ fstW ≫ fstZ) ≫ π a = (pullback.snd sndZ fstW ≫ sndW) ≫ π z✝
      simp only [Category.assoc, hZ, ← hW]
      -- ⊢ pullback.fst sndZ fstW ≫ sndZ ≫ π b = pullback.snd sndZ fstW ≫ fstW ≫ π b
      apply ContinuousMap.ext
      -- ⊢ ∀ (a : ↑(pullback sndZ fstW).toTop), ↑(pullback.fst sndZ fstW ≫ sndZ ≫ π b)  …
      rintro ⟨⟨u,v⟩,h⟩
      -- ⊢ ↑(pullback.fst sndZ fstW ≫ sndZ ≫ π b) { val := (u, v), property := h } = ↑( …
      change π b (sndZ u) = π b (fstW v)
      -- ⊢ ↑(π b) (↑sndZ u) = ↑(π b) (↑fstW v)
      rw [h]
      -- 🎉 no goals

/--
Implementation: the map from the quotient of `relation π` to `B`, which will eventually
become the function underlying an isomorphism, provided that `X a → B` is an effective epi family.
-/
def ιFun : Quotient (relation π) → B :=
  Quotient.lift (fun ⟨a,x⟩ => π a x) <| by
    rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,h,hx,hy⟩
    -- ⊢ (fun x =>
    dsimp at *
    -- ⊢ ↑(π a) x = ↑(π b) y
    rw [← hx, ← hy]
    -- ⊢ ↑(π a) (↑fst z) = ↑(π b) (↑snd z)
    apply_fun (fun t => t z) at h
    -- ⊢ ↑(π a) (↑fst z) = ↑(π b) (↑snd z)
    exact h
    -- 🎉 no goals

lemma ιFun_continuous : Continuous (ιFun π) := by
  apply Continuous.quotient_lift
  -- ⊢ Continuous fun x =>
  apply continuous_sigma
  -- ⊢ ∀ (i : α),
  intro a
  -- ⊢ Continuous fun a_1 =>
  exact (π a).continuous
  -- 🎉 no goals

lemma ιFun_injective : (ιFun π).Injective := by
  rintro ⟨⟨a,x⟩⟩ ⟨⟨b,y⟩⟩ (h : π _ _ = π _ _)
  -- ⊢ Quot.mk Setoid.r { fst := a, snd := x } = Quot.mk Setoid.r { fst := b, snd : …
  apply Quotient.sound'
  -- ⊢ Setoid.r { fst := a, snd := x } { fst := b, snd := y }
  refine ⟨pullback (π a) (π b), ⟨⟨x,y⟩,h⟩, pullback.fst _ _, pullback.snd _ _, ?_, rfl, rfl⟩
  -- ⊢ pullback.fst (π a) (π b) ≫ π { fst := a, snd := x }.fst = pullback.snd (π a) …
  ext ⟨_, h⟩; exact h
  -- ⊢ ↑(pullback.fst (π a) (π b) ≫ π { fst := a, snd := x }.fst) { val := val✝, pr …
              -- 🎉 no goals

/--
Implementation: The quotient of `relation π`, considered as an object of `CompHaus`.
-/
def QB : CompHaus.{u} :=
  haveI : T2Space (Quotient <| relation π) :=
    ⟨fun _ _ h => separated_by_continuous (ιFun_continuous π) <| (ιFun_injective π).ne h ⟩
  CompHaus.of (Quotient <| relation π)

/-- The function `ι_fun`, considered as a morphism. -/
def ιHom : (QB π) ⟶ B := ⟨ιFun π, ιFun_continuous π⟩

/--
Implementation: The promised isomorphism between `QB` and `B`.
-/
noncomputable
def ι : (QB π) ≅ B :=
  haveI : IsIso (ιHom π) := by
    apply isIso_of_bijective
    -- ⊢ Function.Bijective ↑(ιHom π)
    refine ⟨ιFun_injective _, ?_⟩
    -- ⊢ Function.Surjective ↑(ιHom π)
    intro b
    -- ⊢ ∃ a, ↑(ιHom π) a = b
    obtain ⟨a,x,h⟩ := surj b
    -- ⊢ ∃ a, ↑(ιHom π) a = b
    refine ⟨Quotient.mk _ ⟨a,x⟩, h⟩
    -- 🎉 no goals
  asIso (ιHom π)

/--
Implementation: The family of morphisms `X a ⟶ QB` which will be shown to be effective epi.
-/
def π' : (a : α) → (X a ⟶ QB π) := fun a =>
  { toFun := fun x => Quotient.mk _ ⟨a, x⟩
    continuous_toFun := by
      apply Continuous.comp
      -- ⊢ Continuous (Quot.mk Setoid.r)
      apply continuous_quot_mk
      -- ⊢ Continuous fun x => { fst := a, snd := x }
      apply continuous_sigmaMk (σ := fun a => X a) }
      -- 🎉 no goals

/--
Implementation: The family of morphisms `X a ⟶ QB` is an effective epi.
-/
def structAux : EffectiveEpiFamilyStruct X (π' π) where
  desc := fun {W} e h => {
    toFun := Quotient.lift (fun ⟨a,x⟩ => e a x) <| by
      rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,hh,hx,hy⟩; dsimp at *
      -- ⊢ (fun x =>
                                                 -- ⊢ ↑(e a) x = ↑(e b) y
      rw [← hx, ← hy]
      -- ⊢ ↑(e a) (↑fst z) = ↑(e b) (↑snd z)
      specialize h _ _ fst snd ?_
      -- ⊢ fst ≫ π' π { fst := a, snd := x }.fst = snd ≫ π' π { fst := b, snd := y }.fst
      · ext z
        -- ⊢ ↑(fst ≫ π' π { fst := a, snd := x }.fst) z = ↑(snd ≫ π' π { fst := b, snd := …
        apply ιFun_injective
        -- ⊢ ιFun π (↑(fst ≫ π' π { fst := a, snd := x }.fst) z) = ιFun π (↑(snd ≫ π' π { …
        apply_fun (fun q => q z) at hh
        -- ⊢ ιFun π (↑(fst ≫ π' π { fst := a, snd := x }.fst) z) = ιFun π (↑(snd ≫ π' π { …
        exact hh
        -- 🎉 no goals
      apply_fun (fun q => q z) at h
      -- ⊢ ↑(e a) (↑fst z) = ↑(e b) (↑snd z)
      exact h
      -- 🎉 no goals
    continuous_toFun := by
      apply Continuous.quotient_lift
      -- ⊢ Continuous fun x =>
      apply continuous_sigma
      -- ⊢ ∀ (i : α),
      intro a
      -- ⊢ Continuous fun a_1 =>
      exact (e a).continuous }
      -- 🎉 no goals
  fac := by intro Z e h a; ext; rfl
            -- ⊢ π' π a ≫
                           -- ⊢ ↑(π' π a ≫
                                -- 🎉 no goals
  uniq := by
    intro Z e h m hm
    -- ⊢ m =
    ext ⟨⟨a,x⟩⟩
    -- ⊢ ↑m (Quot.mk Setoid.r { fst := a, snd := x }) =
    specialize hm a
    -- ⊢ ↑m (Quot.mk Setoid.r { fst := a, snd := x }) =
    apply_fun (fun q => q x) at hm
    -- ⊢ ↑m (Quot.mk Setoid.r { fst := a, snd := x }) =
    exact hm
    -- 🎉 no goals

@[reassoc]
lemma π'_comp_ι_hom (a : α) : π' π a ≫ (ι _ surj).hom = π a := by ext; rfl
                                                                  -- ⊢ ↑(π' π a ≫ (ι (fun a => π a) surj).hom) x✝ = ↑(π a) x✝
                                                                       -- 🎉 no goals

@[reassoc]
lemma π_comp_ι_inv (a : α) : π a ≫ (ι _ surj).inv = π' π a := by
  rw [Iso.comp_inv_eq]
  -- ⊢ π a = π' π a ≫ (ι (fun a => π a) surj).hom
  exact π'_comp_ι_hom _ surj _
  -- 🎉 no goals

-- TODO: Make a general construction for transferring such structs along isomorphisms.
/--
Implementation: The family `X` is an effective epi, provided that `π` are jointly surjective.
The theorem `CompHaus.effectiveEpiFamily_tfae` should be used instead.
-/
noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => (ι π surj).inv ≫ (structAux π).desc e (fun {Z} a₁ a₂ g₁ g₂ hh => by
      apply h
      -- ⊢ g₁ ≫ π a₁ = g₂ ≫ π a₂
      rw [← cancel_mono (ι _ surj).inv]
      -- ⊢ (g₁ ≫ π a₁) ≫ (ι (fun a => π a) surj).inv = (g₂ ≫ π a₂) ≫ (ι (fun a => π a)  …
      simpa only [Category.assoc, π_comp_ι_inv])
      -- 🎉 no goals
  fac := by
    intro W e h a
    -- ⊢ π a ≫ (fun {W} e h => (ι π surj).inv ≫ EffectiveEpiFamilyStruct.desc (struct …
    simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, π_comp_ι_inv_assoc, (structAux π).fac]
    -- 🎉 no goals
  uniq := by
    intro W e h m hm
    -- ⊢ m = (fun {W} e h => (ι π surj).inv ≫ EffectiveEpiFamilyStruct.desc (structAu …
    dsimp
    -- ⊢ m = (ι π surj).inv ≫ EffectiveEpiFamilyStruct.desc (structAux π) e (_ : ∀ {Z …
    rw [Iso.eq_inv_comp]
    -- ⊢ (ι π surj).hom ≫ m = EffectiveEpiFamilyStruct.desc (structAux π) e (_ : ∀ {Z …
    apply (structAux π).uniq
    -- ⊢ ∀ (a : α), π' π a ≫ (ι π surj).hom ≫ m = e a
    intro a
    -- ⊢ π' π a ≫ (ι π surj).hom ≫ m = e a
    simpa using hm a
    -- 🎉 no goals

end EffectiveEpiFamily

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨CompHaus.EffectiveEpiFamily.struct π surj⟩⟩

open EffectiveEpiFamily

open List in
theorem effectiveEpiFamily_tfae
    {α : Type} [Fintype α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 1 → 2
  -- ⊢ EffectiveEpiFamily X π → Epi (Sigma.desc π)
  · intro; infer_instance
    -- ⊢ Epi (Sigma.desc π)
           -- 🎉 no goals
  tfae_have 2 → 3
  -- ⊢ Epi (Sigma.desc π) → ∀ (b : ↑B.toTop), ∃ a x, ↑(π a) x = b
  · intro e; rw [epi_iff_surjective] at e
    -- ⊢ ∀ (b : ↑B.toTop), ∃ a x, ↑(π a) x = b
             -- ⊢ ∀ (b : ↑B.toTop), ∃ a x, ↑(π a) x = b
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    -- ⊢ ∃ a x, ↑(π a) x = b
    obtain ⟨t,rfl⟩ := e b
    -- ⊢ ∃ a x, ↑(π a) x = ↑(Sigma.desc π) t
    let q := i.hom t
    -- ⊢ ∃ a x, ↑(π a) x = ↑(Sigma.desc π) t
    refine ⟨q.1,q.2,?_⟩
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) t
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) t
    rw [this]
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) (↑i.inv (↑i.hom t))
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    -- ⊢ ↑(π q.fst) q.snd = ↑(i.inv ≫ Sigma.desc π) (↑i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    -- ⊢ Sigma.desc π = i.hom ≫ finiteCoproduct.desc X π
    apply colimit.hom_ext
    -- ⊢ ∀ (j : Discrete α), colimit.ι (Discrete.functor X) j ≫ Sigma.desc π = colimi …
    rintro ⟨a⟩
    -- ⊢ colimit.ι (Discrete.functor X) { as := a } ≫ Sigma.desc π = colimit.ι (Discr …
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
    -- ⊢ ↑(π a) x✝ = ↑(NatTrans.app (finiteCoproduct.cocone X).ι { as := a } ≫ finite …
         -- 🎉 no goals
  tfae_have 3 → 1
  -- ⊢ (∀ (b : ↑B.toTop), ∃ a x, ↑(π a) x = b) → EffectiveEpiFamily X π
  · apply effectiveEpiFamily_of_jointly_surjective
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals

instance precoherent : Precoherent CompHaus.{u} := by
  constructor
  -- ⊢ ∀ {B₁ B₂ : CompHaus} (f : B₂ ⟶ B₁) (α : Type) [inst : Fintype α] (X₁ : α → C …
  intro B₁ B₂ f α _ X₁ π₁ h₁
  -- ⊢ ∃ β x X₂ π₂, EffectiveEpiFamily X₂ π₂ ∧ ∃ i ι, ∀ (b : β), ι b ≫ π₁ (i b) = π …
  refine ⟨α, inferInstance, fun a => pullback f (π₁ a), fun a => pullback.fst _ _, ?_,
    id, fun a => pullback.snd _ _, ?_⟩
  · have := (effectiveEpiFamily_tfae _ π₁).out 0 2; rw [this] at h₁; clear this
    -- ⊢ EffectiveEpiFamily (fun a => pullback f (π₁ a)) fun a => pullback.fst f (π₁ a)
                                                    -- ⊢ EffectiveEpiFamily (fun a => pullback f (π₁ a)) fun a => pullback.fst f (π₁ a)
                                                                     -- ⊢ EffectiveEpiFamily (fun a => pullback f (π₁ a)) fun a => pullback.fst f (π₁ a)
    have := (effectiveEpiFamily_tfae _ (fun a => pullback.fst f (π₁ a))).out 0 2
    -- ⊢ EffectiveEpiFamily (fun a => pullback f (π₁ a)) fun a => pullback.fst f (π₁ a)
    rw [this]; clear this
    -- ⊢ ∀ (b : ↑B₂.toTop), ∃ a x, ↑(pullback.fst f (π₁ a)) x = b
               -- ⊢ ∀ (b : ↑B₂.toTop), ∃ a x, ↑(pullback.fst f (π₁ a)) x = b
    intro b₂
    -- ⊢ ∃ a x, ↑(pullback.fst f (π₁ a)) x = b₂
    obtain ⟨a,x,h⟩ := h₁ (f b₂)
    -- ⊢ ∃ a x, ↑(pullback.fst f (π₁ a)) x = b₂
    refine ⟨a, ⟨⟨b₂, x⟩, h.symm⟩, rfl⟩
    -- 🎉 no goals
  · intro a
    -- ⊢ (fun a => pullback.snd f (π₁ a)) a ≫ π₁ (id a) = (fun a => pullback.fst f (π …
    dsimp
    -- ⊢ pullback.snd f (π₁ a) ≫ π₁ a = pullback.fst f (π₁ a) ≫ f
    ext ⟨⟨_,_⟩,h⟩
    -- ⊢ ↑(pullback.snd f (π₁ a) ≫ π₁ a) { val := (fst✝, snd✝), property := h } = ↑(p …
    exact h.symm
    -- 🎉 no goals

end CompHaus
