/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.Profinite.Limits

/-!
# Effective epimorphic families in `Profinite`

Let `π a : X a ⟶ B` be a family of morphisms in `Profinite` indexed by a finite type `α`.
In this file, we show that the following are all equivalent:
- The family `π` is effective epimorphic.
- The induced map `∐ X ⟶ B` is epimorphic.
- The family `π` is jointly surjective.

## Main results

- `Profinite.effectiveEpiFamily_tfae`: characterise being an effective epimorphic family.
- `Profinite.instPrecoherent`: `Profinite` is precoherent.

## Implementation notes

The entire section `EffectiveEpiFamily` comprises exclusively a technical construction for
the main proof and does not contain any statements that would be useful in other contexts.
-/

open CategoryTheory Limits

namespace Profinite

/-!
This section contains exclusively technical definitions and results that are used
in the proof of `Profinite.effectiveEpiFamily_of_jointly_surjective`.

The construction of `QB` as a quotient of the maps `X a → B` is analoguous to the
construction in the file `CompHaus.EffectiveEpi`,
but one has to start with an equivalence relation on `Profinite` instead.
-/
namespace EffectiveEpiFamily

/- Assume we have a family `X a → B` which is jointly surjective. -/
variable {α : Type} [Fintype α] {B : Profinite}
  {X : α → Profinite} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/--
Implementation: This is a setoid on the explicit finite coproduct of `X` whose quotient
will be isomorphic to `B` provided that `X a → B` is an effective epi family.
-/
def relation : Setoid (finiteCoproduct X) where
  r a b := ∃ (Z : Profinite) (z : Z) (fst : Z ⟶ X a.fst) (snd : Z ⟶ X b.fst),
    fst ≫ π _ = snd ≫ π _ ∧ fst z = a.snd ∧ snd z = b.snd
  iseqv := by
    constructor
    · rintro ⟨a, x⟩
      -- ⊢ ∃ Z z fst snd, fst ≫ π { fst := a, snd := x }.fst = snd ≫ π { fst := a, snd  …
      exact ⟨X a, x, 𝟙 _, 𝟙 _, by simp, rfl, rfl⟩
      -- 🎉 no goals
    · rintro ⟨a, x⟩ ⟨b, y⟩ ⟨Z, z, fst, snd, w, h1, h2⟩
      -- ⊢ ∃ Z z fst snd, fst ≫ π { fst := b, snd := y }.fst = snd ≫ π { fst := a, snd  …
      exact ⟨Z, z, snd, fst, w.symm, h2, h1⟩
      -- 🎉 no goals
    · rintro ⟨a, x⟩ ⟨b, y⟩ ⟨z, c⟩ ⟨Z, z, fstZ, sndZ, hZ, hZ1, hZ2⟩
      -- ⊢ (∃ Z z fst snd, fst ≫ π { fst := b, snd := y }.fst = snd ≫ π { fst := z✝, sn …
      rintro ⟨W, w, fstW, sndW, hW, hW1, hW2⟩
      -- ⊢ ∃ Z z fst snd, fst ≫ π { fst := a, snd := x }.fst = snd ≫ π { fst := z✝, snd …
      refine ⟨pullback sndZ fstW, ⟨⟨z, w⟩, by dsimp; rw [hZ2, hW1]⟩,
        pullback.fst _ _ ≫ fstZ, pullback.snd _ _ ≫ sndW, ?_, hZ1, hW2⟩
      dsimp only at *
      -- ⊢ (pullback.fst sndZ fstW ≫ fstZ) ≫ π a = (pullback.snd sndZ fstW ≫ sndW) ≫ π z✝
      simp only [Category.assoc, hZ, ← hW]
      -- ⊢ pullback.fst sndZ fstW ≫ sndZ ≫ π b = pullback.snd sndZ fstW ≫ fstW ≫ π b
      apply ContinuousMap.ext
      -- ⊢ ∀ (a : ↑(pullback sndZ fstW).toCompHaus.toTop), ↑(pullback.fst sndZ fstW ≫ s …
      rintro ⟨⟨u, v⟩, h⟩
      -- ⊢ ↑(pullback.fst sndZ fstW ≫ sndZ ≫ π b) { val := (u, v), property := h } = ↑( …
      change π b (sndZ u) = π b (fstW v)
      -- ⊢ ↑(π b) (↑sndZ u) = ↑(π b) (↑fstW v)
      rw [h]
      -- 🎉 no goals

/--
Implementation: The map from the quotient of `relation π` to `B`, which will eventually
become the function underlying an isomorphism, provided that `X a → B` is an effective epi family.
-/
def ιFun : Quotient (relation π) → B :=
  Quotient.lift (fun ⟨a, x⟩ => π a x) <| by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨Z, z, fst, snd, h, hx, hy⟩
    -- ⊢ (fun x =>
    dsimp only at *
    -- ⊢ ↑(π a) x = ↑(π b) y
    rw [← hx, ← hy]
    -- ⊢ ↑(π a) (↑fst z) = ↑(π b) (↑snd z)
    apply_fun (· z) at h
    -- ⊢ ↑(π a) (↑fst z) = ↑(π b) (↑snd z)
    exact h
    -- 🎉 no goals

/-- Implementation: `ιFun` is continous. -/
lemma ιFun_continuous : Continuous (ιFun π) := by
  apply Continuous.quotient_lift
  -- ⊢ Continuous fun x =>
  apply continuous_sigma
  -- ⊢ ∀ (i : α),
  intro a
  -- ⊢ Continuous fun a_1 =>
  exact (π a).continuous
  -- 🎉 no goals

/-- Implementation: `ιFun` is injective. -/
lemma ιFun_injective : (ιFun π).Injective := by
  rintro ⟨⟨a, x⟩⟩ ⟨⟨b, y⟩⟩ (h : π _ _ = π _ _)
  -- ⊢ Quot.mk Setoid.r { fst := a, snd := x } = Quot.mk Setoid.r { fst := b, snd : …
  apply Quotient.sound'
  -- ⊢ Setoid.r { fst := a, snd := x } { fst := b, snd := y }
  refine ⟨pullback (π a) (π b), ⟨⟨x, y⟩, h⟩, pullback.fst _ _, pullback.snd _ _, ?_, rfl, rfl⟩
  -- ⊢ pullback.fst (π a) (π b) ≫ π { fst := a, snd := x }.fst = pullback.snd (π a) …
  ext ⟨_, h⟩
  -- ⊢ ↑(pullback.fst (π a) (π b) ≫ π { fst := a, snd := x }.fst) { val := val✝, pr …
  exact h
  -- 🎉 no goals

/-- Implementation: The quotient of `relation π`, considered as an object of `CompHaus`. -/
def QB' : CompHaus :=
  haveI : T2Space (Quotient <| relation π) :=
    ⟨fun _ _ h => separated_by_continuous (ιFun_continuous π) <| (ιFun_injective π).ne h ⟩
  CompHaus.of (Quotient <| relation π)

/-- Implementation: The function `ιFun`, considered as a morphism in `CompHaus`. -/
def ιHom' : (QB' π) ⟶ B.toCompHaus := ⟨ιFun π, ιFun_continuous π⟩

/-- Implementation: `ιFun` as isomorphism in `CompHaus`. -/
noncomputable
def ιIso' : (QB' π) ≅ B.toCompHaus :=
  have : IsIso (ιHom' π) := by
    apply CompHaus.isIso_of_bijective
    -- ⊢ Function.Bijective ↑(ιHom' π)
    refine ⟨ιFun_injective _, ?_⟩
    -- ⊢ Function.Surjective ↑(ιHom' π)
    intro b
    -- ⊢ ∃ a, ↑(ιHom' π) a = b
    obtain ⟨a, x, h⟩ := surj b
    -- ⊢ ∃ a, ↑(ιHom' π) a = b
    exact ⟨Quotient.mk _ ⟨a, x⟩, h⟩
    -- 🎉 no goals
  asIso (ιHom' π)

/-- Implementation: The quotient of `relation π`, considered as an object of `Profinite`. -/
def QB : Profinite where
  toCompHaus := QB' π
  IsTotallyDisconnected := ⟨(CompHaus.homeoOfIso (ιIso' π surj)).embedding.isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- Implementation: The function `ιFun`, considered as a morphism in `Profinite`. -/
def ιHom : (QB π surj) ⟶ B := ⟨ιFun π, ιFun_continuous π⟩

/-- Implementation: `ιFun` as an isomorphism in `Profinite`. -/
noncomputable
def ιIso : (QB π surj) ≅ B :=
  have : IsIso (ιHom π surj) := by
    apply Profinite.isIso_of_bijective
    -- ⊢ Function.Bijective ↑(ιHom π surj)
    refine ⟨ιFun_injective _, ?_⟩
    -- ⊢ Function.Surjective ↑(ιHom π surj)
    intro b
    -- ⊢ ∃ a, ↑(ιHom π surj) a = b
    obtain ⟨a, x, h⟩ := surj b
    -- ⊢ ∃ a, ↑(ιHom π surj) a = b
    exact ⟨Quotient.mk _ ⟨a, x⟩, h⟩
    -- 🎉 no goals
  asIso (ιHom π surj)

/-- Implementation: The family of morphisms `X a ⟶ QB` which will be shown to be effective epi. -/
def π' : (a : α) → (X a ⟶ QB π surj) := fun a =>
  { toFun := fun x => Quotient.mk _ ⟨a, x⟩
    continuous_toFun := by
      apply Continuous.comp
      -- ⊢ Continuous (Quot.mk Setoid.r)
      apply continuous_quot_mk
      -- ⊢ Continuous fun x => { fst := a, snd := x }
      apply continuous_sigmaMk (σ := (X ·)) }
      -- 🎉 no goals

/-- Implementation: The family of morphisms `π' a : X a ⟶ QB` is an effective epi. -/
def structAux : EffectiveEpiFamilyStruct X (π' π surj) where
  desc := fun e h => {
    toFun := Quotient.lift (fun ⟨a, x⟩ => e a x) <| by
      rintro ⟨a, x⟩ ⟨b, y⟩ ⟨Z, z, fst, snd, hh, hx, hy⟩
      -- ⊢ (fun x =>
      dsimp at *
      -- ⊢ ↑(e a) x = ↑(e b) y
      rw [← hx, ← hy]
      -- ⊢ ↑(e a) (↑fst z) = ↑(e b) (↑snd z)
      specialize h _ _ fst snd ?_
      -- ⊢ fst ≫ π' π surj { fst := a, snd := x }.fst = snd ≫ π' π surj { fst := b, snd …
      · ext z
        -- ⊢ ↑(fst ≫ π' π surj { fst := a, snd := x }.fst) z = ↑(snd ≫ π' π surj { fst := …
        apply ιFun_injective
        -- ⊢ ιFun π (↑(fst ≫ π' π surj { fst := a, snd := x }.fst) z) = ιFun π (↑(snd ≫ π …
        apply_fun (· z) at hh
        -- ⊢ ιFun π (↑(fst ≫ π' π surj { fst := a, snd := x }.fst) z) = ιFun π (↑(snd ≫ π …
        exact hh
        -- 🎉 no goals
      apply_fun (· z) at h
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
  fac := by
    intro Z e h a
    -- ⊢ π' π surj a ≫
    ext
    -- ⊢ ↑(π' π surj a ≫
    rfl
    -- 🎉 no goals
  uniq := by
    intro Z e h m hm
    -- ⊢ m =
    ext ⟨⟨a, x⟩⟩
    -- ⊢ ↑m (Quot.mk Setoid.r { fst := a, snd := x }) =
    specialize hm a
    -- ⊢ ↑m (Quot.mk Setoid.r { fst := a, snd := x }) =
    apply_fun (· x) at hm
    -- ⊢ ↑m (Quot.mk Setoid.r { fst := a, snd := x }) =
    exact hm
    -- 🎉 no goals

/-- Implementation: `ιIso ∘ (π' a) : X a → QB → B` is exactly `π a`. -/
@[reassoc]
lemma π'_comp_ι_hom (a : α) : π' π surj a ≫ (ιIso π surj).hom = π a := by
  ext
  -- ⊢ ↑(π' π surj a ≫ (ιIso π surj).hom) x✝ = ↑(π a) x✝
  rfl
  -- 🎉 no goals

/-- Implementation: `ιIso⁻¹ ∘ (π a) : X a → B → QB` is exactly `π' a`. -/
@[reassoc]
lemma π_comp_ι_inv (a : α) : π a ≫ (ιIso π surj).inv = π' π surj a := by
  rw [Iso.comp_inv_eq]
  -- ⊢ π a = π' π surj a ≫ (ιIso π surj).hom
  exact π'_comp_ι_hom _ surj _
  -- 🎉 no goals

/--
Implementation: The family `X` is an effective epi, provided that `π` are jointly surjective.
The theorem `Profinite.effectiveEpiFamily_tfae` should be used instead.
-/
noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun e h => (ιIso π surj).inv ≫ (structAux π surj).desc e (fun a₁ a₂ g₁ g₂ hh => by
    apply h
    -- ⊢ g₁ ≫ π a₁ = g₂ ≫ π a₂
    rw [← cancel_mono (ιIso _ surj).inv]
    -- ⊢ (g₁ ≫ π a₁) ≫ (ιIso (fun a => π a) surj).inv = (g₂ ≫ π a₂) ≫ (ιIso (fun a => …
    simpa only [Category.assoc, π_comp_ι_inv])
    -- 🎉 no goals
  fac := by
    intro W e h a
    -- ⊢ π a ≫ (fun {W} e h => (ιIso π surj).inv ≫ EffectiveEpiFamilyStruct.desc (str …
    simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, π_comp_ι_inv_assoc, (structAux π surj).fac]
    -- 🎉 no goals
  uniq := by
    intro W e h m hm
    -- ⊢ m = (fun {W} e h => (ιIso π surj).inv ≫ EffectiveEpiFamilyStruct.desc (struc …
    dsimp
    -- ⊢ m = (ιIso π surj).inv ≫ EffectiveEpiFamilyStruct.desc (structAux π surj) e ( …
    rw [Iso.eq_inv_comp]
    -- ⊢ (ιIso π surj).hom ≫ m = EffectiveEpiFamilyStruct.desc (structAux π surj) e ( …
    apply (structAux π surj).uniq
    -- ⊢ ∀ (a : α), π' π surj a ≫ (ιIso π surj).hom ≫ m = e a
    intro a
    -- ⊢ π' π surj a ≫ (ιIso π surj).hom ≫ m = e a
    simpa using hm a
    -- 🎉 no goals

end EffectiveEpiFamily

section JointlySurjective

/-- One direction of `Profinite.effectiveEpiFamily_tfae` -/
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : Profinite}
    (X : α → Profinite) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨Profinite.EffectiveEpiFamily.struct π surj⟩⟩

open List in
/--
For a finite family of profinite spaces `π a : X a → B` the following are equivalent:
* `π` is an effective epimorphic family
* the map `∐ π a ⟶ B` is an epimorphism
* `π` is jointly surjective
-/
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : Profinite}
    (X : α → Profinite) (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b ] := by
  tfae_have 1 → 2
  -- ⊢ EffectiveEpiFamily X π → Epi (Sigma.desc π)
  · intro
    -- ⊢ Epi (Sigma.desc π)
    infer_instance
    -- 🎉 no goals
  tfae_have 2 → 3
  -- ⊢ Epi (Sigma.desc π) → ∀ (b : ↑B.toCompHaus.toTop), ∃ a x, ↑(π a) x = b
  · intro e
    -- ⊢ ∀ (b : ↑B.toCompHaus.toTop), ∃ a x, ↑(π a) x = b
    rw [epi_iff_surjective] at e
    -- ⊢ ∀ (b : ↑B.toCompHaus.toTop), ∃ a x, ↑(π a) x = b
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    -- ⊢ ∃ a x, ↑(π a) x = b
    obtain ⟨t, rfl⟩ := e b
    -- ⊢ ∃ a x, ↑(π a) x = ↑(Sigma.desc π) t
    let q := i.hom t
    -- ⊢ ∃ a x, ↑(π a) x = ↑(Sigma.desc π) t
    refine ⟨q.1, q.2, ?_⟩
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) t
    have : t = i.inv (i.hom t)
    -- ⊢ t = ↑i.inv (↑i.hom t)
    · show t = (i.hom ≫ i.inv) t
      -- ⊢ t = ↑(i.hom ≫ i.inv) t
      simp only [i.hom_inv_id]
      -- ⊢ t = ↑(𝟙 (∐ X)) t
      rfl
      -- 🎉 no goals
    rw [this]
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) (↑i.inv (↑i.hom t))
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    -- ⊢ ↑(π q.fst) q.snd = ↑(i.inv ≫ Sigma.desc π) (↑i.hom t)
    suffices : i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π
    -- ⊢ ↑(π q.fst) q.snd = ↑(i.inv ≫ Sigma.desc π) (↑i.hom t)
    · rw [this]
      -- ⊢ ↑(π q.fst) q.snd = ↑(finiteCoproduct.desc X π) (↑i.hom t)
      rfl
      -- 🎉 no goals
    rw [Iso.inv_comp_eq]
    -- ⊢ Sigma.desc π = i.hom ≫ finiteCoproduct.desc X π
    apply colimit.hom_ext
    -- ⊢ ∀ (j : Discrete α), colimit.ι (Discrete.functor X) j ≫ Sigma.desc π = colimi …
    rintro ⟨a⟩
    -- ⊢ colimit.ι (Discrete.functor X) { as := a } ≫ Sigma.desc π = colimit.ι (Discr …
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext
    -- ⊢ ↑(π a) x✝ = ↑(NatTrans.app (finiteCoproduct.cocone X).ι { as := a } ≫ finite …
    rfl
    -- 🎉 no goals
  tfae_have 3 → 1
  -- ⊢ (∀ (b : ↑B.toCompHaus.toTop), ∃ a x, ↑(π a) x = b) → EffectiveEpiFamily X π
  · apply effectiveEpiFamily_of_jointly_surjective
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals

end JointlySurjective

section Coherent

/-- The category of profinite spaces is precoherent -/
instance instPrecoherent : Precoherent Profinite := by
  constructor
  -- ⊢ ∀ {B₁ B₂ : Profinite} (f : B₂ ⟶ B₁) (α : Type) [inst : Fintype α] (X₁ : α →  …
  intro B₁ B₂ f α _ X₁ π₁ h₁
  -- ⊢ ∃ β x X₂ π₂, EffectiveEpiFamily X₂ π₂ ∧ ∃ i ι, ∀ (b : β), ι b ≫ π₁ (i b) = π …
  refine ⟨α, inferInstance, (pullback f <| π₁ ·), fun a => pullback.fst _ _, ?_,
    id, fun a => pullback.snd _ _, ?_⟩
  · have := (effectiveEpiFamily_tfae _ π₁).out 0 2
    -- ⊢ EffectiveEpiFamily (fun x => pullback f (π₁ x)) fun a => pullback.fst f (π₁ a)
    rw [this] at h₁
    -- ⊢ EffectiveEpiFamily (fun x => pullback f (π₁ x)) fun a => pullback.fst f (π₁ a)
    clear this
    -- ⊢ EffectiveEpiFamily (fun x => pullback f (π₁ x)) fun a => pullback.fst f (π₁ a)
    have := (effectiveEpiFamily_tfae _ (fun a => pullback.fst f (π₁ a))).out 0 2
    -- ⊢ EffectiveEpiFamily (fun x => pullback f (π₁ x)) fun a => pullback.fst f (π₁ a)
    rw [this]
    -- ⊢ ∀ (b : ↑B₂.toCompHaus.toTop), ∃ a x, ↑(pullback.fst f (π₁ a)) x = b
    clear this
    -- ⊢ ∀ (b : ↑B₂.toCompHaus.toTop), ∃ a x, ↑(pullback.fst f (π₁ a)) x = b
    intro b₂
    -- ⊢ ∃ a x, ↑(pullback.fst f (π₁ a)) x = b₂
    obtain ⟨a, x, h⟩ := h₁ (f b₂)
    -- ⊢ ∃ a x, ↑(pullback.fst f (π₁ a)) x = b₂
    exact ⟨a, ⟨⟨b₂, x⟩, h.symm⟩, rfl⟩
    -- 🎉 no goals
  · intro a
    -- ⊢ (fun a => pullback.snd f (π₁ a)) a ≫ π₁ (id a) = (fun a => pullback.fst f (π …
    dsimp
    -- ⊢ pullback.snd f (π₁ a) ≫ π₁ a = pullback.fst f (π₁ a) ≫ f
    ext ⟨⟨_, _⟩, h⟩
    -- ⊢ ↑(pullback.snd f (π₁ a) ≫ π₁ a) { val := (fst✝, snd✝), property := h } = ↑(p …
    exact h.symm
    -- 🎉 no goals

end Coherent

end Profinite
