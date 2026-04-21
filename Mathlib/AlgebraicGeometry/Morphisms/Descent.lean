/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Descent of morphism properties

Let `P` and `P'` be morphism properties. In this file we show some results to deduce
that `P` descends along `P'` from a codescent property of ring homomorphisms.

## Main results

- `HasRingHomProperty.descendsAlong`: if `P` is a local property induced by `Q`, `P'` implies
  `Q'` on global sections of affines and `Q` codescends along `Q'`, then `P` descends along `P'`.
- `HasAffineProperty.descendsAlong_of_affineAnd`: if `P` is given by `affineAnd Q`, `P'` implies
  `Q'` on global sections of affines and `Q` codescends along `Q'`, then `P` descends along `P'`
  (see TODOs).

## TODO

- Show that affine morphisms descend along faithfully-flat morphisms. This will make
  `HasAffineProperty.descendsAlong_of_affineAnd` useful.

-/
set_option backward.defeqAttrib.useBackward true

public section

universe u v

open TensorProduct CategoryTheory Limits

namespace AlgebraicGeometry

variable (P P' : MorphismProperty Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/--
If `P` is local at the source, every quasi-compact scheme is dominated by an
affine scheme via `p : Y ⟶ X` such that `p` satisfies `P`.
-/
lemma Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource (X : Scheme.{u}) [CompactSpace X]
    [IsZariskiLocalAtSource P] [P.ContainsIdentities] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X), Surjective p ∧ P p ∧ IsAffine Y := by
  let 𝒰 := X.affineCover.finiteSubcover
  let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
  refine ⟨_, p, ⟨fun x ↦ ?_⟩, ?_, inferInstance⟩
  · obtain ⟨i, x, rfl⟩ := X.affineCover.finiteSubcover.exists_eq x
    use Sigma.ι X.affineCover.finiteSubcover.X i x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (sigmaOpenCover _)]
    exact fun i ↦ by simpa [p] using IsZariskiLocalAtSource.of_isOpenImmersion _

set_option backward.isDefEq.respectTransparency false in
/-- If `P` is local at the target, to show `P` descends along `P'` we may assume
the base to be affine. -/
lemma IsZariskiLocalAtTarget.descendsAlong [IsZariskiLocalAtTarget P] [P'.IsStableUnderBaseChange]
    (H : ∀ {R : CommRingCat.{u}} {X Y : Scheme.{u}} (f : X ⟶ Spec R) (g : Y ⟶ Spec R),
      P' f → P (pullback.fst f g) → P g) :
    P.DescendsAlong P' := by
  apply MorphismProperty.DescendsAlong.mk'
  introv h hf
  wlog hZ : ∃ R, Z = Spec R generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) Z.affineCover]
    intro i
    let ι := Z.affineCover.f i
    let e : pullback (pullback.snd f ι) (pullback.snd g ι) ≅
        pullback (pullback.fst f g) (pullback.fst f ι) :=
      pullbackLeftPullbackSndIso f ι (pullback.snd g ι) ≪≫
        pullback.congrHom rfl pullback.condition.symm ≪≫
        (pullbackAssoc f g g ι).symm ≪≫ pullback.congrHom pullback.condition.symm rfl ≪≫
        (pullbackRightPullbackFstIso f ι (pullback.fst f g)).symm
    have heq : e.hom ≫ pullback.snd (pullback.fst f g) (pullback.fst f ι) =
        pullback.fst (pullback.snd f ι) (pullback.snd g ι) := by
      apply pullback.hom_ext <;> simp [e, pullback.condition]
    refine this (f := pullback.snd f ι) ?_ ?_ ⟨_, rfl⟩
    · exact P'.pullback_snd _ _ h
    · change P (pullback.fst (pullback.snd f ι) (pullback.snd g ι))
      rw [← heq, P.cancel_left_of_respectsIso]
      exact AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback (iY := pullback.fst f ι)
        (CategoryTheory.IsPullback.of_hasPullback _ _) hf
  obtain ⟨R, rfl⟩ := hZ
  exact H f g h hf

variable (Q Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable {Q Q'} in
lemma of_pullback_fst_Spec_of_codescendsAlong [P.RespectsIso]
    (hQQ' : RingHom.CodescendsAlong Q Q')
    (H₁ : ∀ {R S : CommRingCat.{u}} {f : R ⟶ S}, P' (Spec.map f) → Q' f.hom)
    (H₂ : ∀ {R S : CommRingCat.{u}} {f : R ⟶ S}, P (Spec.map f) ↔ Q f.hom)
    {R S T : CommRingCat.{u}}
    {f : Spec T ⟶ Spec R} {g : Spec S ⟶ Spec R} (h : P' f) (hf : P (pullback.fst f g)) :
    P g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom, ψ.hom]
  replace hf : P (pullback.fst (Spec.map <| CommRingCat.ofHom <| algebraMap R T)
    (Spec.map <| CommRingCat.ofHom <| algebraMap R S)) := hf
  rw [H₂]
  refine hQQ'.algebraMap_tensorProduct (R := R) (S := T) (T := S) _ (H₁ h) ?_
  rwa [← pullbackSpecIso_hom_fst R T S, P.cancel_left_of_respectsIso, H₂] at hf

/-- If `X` admits a morphism `p : T ⟶ X` from an affine scheme satisfying `P'`, to
show a property descends along a morphism `f : X ⟶ Z` satisfying `P'`, `X` may assumed to
be affine. -/
lemma IsStableUnderBaseChange.of_pullback_fst_of_isAffine [P'.RespectsIso]
    [P'.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (H : ∀ {R : CommRingCat.{u}} {S X : Scheme.{u}} (f : Spec R ⟶ S) (g : X ⟶ S),
      P' f → P (pullback.fst f g) → P g) {X Y Z T : Scheme.{u}} [IsAffine T] (p : T ⟶ X)
    (hp : P' p) (f : X ⟶ Z) (g : Y ⟶ Z) (h : P' f) (hf : P (pullback.fst f g)) : P g := by
  apply H ((T.isoSpec.inv ≫ p) ≫ f)
  · rw [Category.assoc, P'.cancel_left_of_respectsIso]
    exact P'.comp_mem _ _ hp h
  · rw [← pullbackRightPullbackFstIso_inv_fst f g (T.isoSpec.inv ≫ p),
        P.cancel_left_of_respectsIso]
    exact P.pullback_fst _ _ hf

open Opposite

variable [P'.IsStableUnderBaseChange] [P'.IsStableUnderComposition] [P.IsStableUnderBaseChange]
variable
  (H₁ : (@IsLocalIso ⊓ @Surjective : MorphismProperty Scheme) ≤ P')
  (H₂ : ∀ {R S : CommRingCat.{u}} {f : R ⟶ S}, P' (Spec.map f) → Q' f.hom)

include H₁ in
lemma IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact [IsZariskiLocalAtTarget P]
    (H : ∀ {R S : CommRingCat.{u}} {Y : Scheme.{u}} (φ : R ⟶ S) (g : Y ⟶ Spec R),
      P' (Spec.map φ) → P (pullback.fst (Spec.map φ) g) → P g) :
    P.DescendsAlong (P' ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong
  intro R X Y f g hf h
  wlog hX : ∃ T, X = Spec T generalizing X
  · have _ : CompactSpace X := by simpa [← quasiCompact_iff_compactSpace f] using hf.2
    obtain ⟨Y, p, hsurj, hP', hY⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
    refine this (f := (Y.isoSpec.inv ≫ p) ≫ f) ?_ ?_ ⟨_, rfl⟩
    · rw [Category.assoc, (P' ⊓ @QuasiCompact).cancel_left_of_respectsIso]
      exact ⟨P'.comp_mem _ _ (H₁ _ ⟨hP', hsurj⟩) hf.1, inferInstance⟩
    · rw [← pullbackRightPullbackFstIso_inv_fst f g _, P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ h
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  exact H φ g hf.1 h

include H₁ H₂ in
/--
Let `P` be the morphism property associated to the ring hom property `Q`. Suppose

- `P'` implies `Q'` on global sections for affine schemes,
- `P'` is satisfied for all surjective, local isomorphisms, and
- `Q` codescend along `Q'`.

Then `P` descends along quasi-compact morphisms satisfying `P'`.

Note: The second condition is in particular satisfied for faithfully flat morphisms.
-/
nonrec lemma HasRingHomProperty.descendsAlong [HasRingHomProperty P Q]
    (hQQ' : RingHom.CodescendsAlong Q Q') :
    P.DescendsAlong (P' ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ H₁
  introv h hf
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) Y.affineCover]
    intro i
    have heq : pullback.fst (Spec.map φ) (Y.affineCover.f i ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.affineCover.f i) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    exact this _ (heq ▸ AlgebraicGeometry.IsZariskiLocalAtSource.comp hf _) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ hQQ' H₂ _ h hf
  simp [HasRingHomProperty.Spec_iff (P := P)]

include H₁ H₂ in
/--
Let `P` be a morphism property associated with `affineAnd Q`. Suppose

- `P'` implies `Q'` on global sections on affine schemes,
- `P'` is satisfied for surjective, local isomorphisms,
- affine morphisms descend along `P''`, and
- `Q` codescends along `Q'`,

Then `P` descends along quasi-compact morphisms satisfying `P'`.

Note: The second condition is in particular satisfied for faithfully flat morphisms.
-/
nonrec lemma HasAffineProperty.descendsAlong_of_affineAnd
    (hP : HasAffineProperty P (affineAnd Q)) [MorphismProperty.DescendsAlong @IsAffineHom P']
    (hQ : RingHom.RespectsIso Q) (hQQ' : RingHom.CodescendsAlong Q Q') :
    P.DescendsAlong (P' ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ H₁
  introv h hf
  have : IsAffine Y := by
    convert isAffine_of_isAffineHom g
    exact MorphismProperty.of_pullback_fst_of_descendsAlong h <|
      AlgebraicGeometry.HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ hf
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [← P.cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, P.cancel_left_of_respectsIso]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ hQQ' H₂ _ h hf
  simp [SpecMap_iff_of_affineAnd _ hQ]

end AlgebraicGeometry
