/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Locality conditions on morphism properties

In this file we define locality conditions on morphism properties in a category. Let `K` be a
precoverage in a category `C` and `P` be a morphism property on `C` that respects isomorphisms.

We say that

- `P` is local at the target if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `Y`.
- `P` is local at the source if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a `K`-cover `{Uᵢ}` of `X`.

## TODOs

- Define source and target local closure of a morphism property.
-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (K : Precoverage C)

/--
A property of morphisms `P` in `C` is local at the target with respect to the precoverage `K` if
it respects isomorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `Y` in the precoverage `K`.
-/
class IsLocalAtTarget (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `f` restricted to `Uᵢ` for any
  `K`-cover `R` of `Y`. -/
  pullbackSnd {X Y : C} {f : Y ⟶ X} {R : Presieve X} {U : C} {g : U ⟶ X} (hR : R ∈ K X)
    (hg : R g) (hf : P f) [HasPullback f g] :
    P (pullback.snd f g)
  /-- If `P` holds for `f` restricted to `Uᵢ` for all `i`, it also holds for `f : X ⟶ Y` for any
  `K`-cover `R` of `Y`. -/
  of_forall_pullbackSnd {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hR : R ∈ K X)
    (h : ∀ {U : C} {g : U ⟶ X} [HasPullback f g], R g → P (pullback.snd f g)) :
    P f

namespace IsLocalAtTarget

variable {P : MorphismProperty C} {K L : Precoverage C}

lemma mk_of_iff [P.RespectsIso]
    (H : ∀ ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄ ⦃R : Presieve Y⦄, R ∈ K Y →
      (P f ↔ ∀ {U : C} (g : U ⟶ Y) [HasPullback f g], R g → P (pullback.snd f g))) :
    P.IsLocalAtTarget K where
  pullbackSnd := by grind
  of_forall_pullbackSnd := by grind

lemma iff_of_forall_pullbackSnd [P.IsLocalAtTarget K] {X Y : C} {R : Presieve Y} (hR : R ∈ K Y)
    {f : X ⟶ Y} :
    P f ↔ ∀ {U : C} (g : U ⟶ Y) [HasPullback f g], R g → P (pullback.snd f g) := by
  grind [IsLocalAtTarget]

lemma mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
      P f ↔ ∀ i, P (pullback.snd f (𝒰.f i))) :
    P.IsLocalAtTarget K := by
  refine mk_of_iff fun X Y f R hR ↦ ?_
  obtain ⟨𝒰, rfl⟩ := R.exists_eq_preZeroHypercover
  rw [H _ ⟨𝒰, hR⟩]
  have _ (i) : HasPullback (𝒰.f i) f := (Precoverage.hasPullbacks_of_mem _ hR).hasPullback ⟨i⟩
  refine ⟨fun h U g hfg ↦ ?_, fun h i ↦ h _ ⟨i⟩⟩
  rintro ⟨i⟩
  exact h i

lemma mk_of_small [K.HasPullbacks] [P.RespectsIso] [Precoverage.Small.{w} K]
    (h₁ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
        P f → ∀ i, P (pullback.snd f (𝒰.f i)))
    (h₂ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y),
        (∀ i, P (pullback.snd f (𝒰.f i))) → P f) :
    P.IsLocalAtTarget K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 ↦ ⟨fun hf _ ↦ h₁ 𝒰 hf _,
    fun h ↦ h₂ 𝒰.restrictIndexOfSmall fun _ ↦ h _⟩

lemma mk_of_isStableUnderBaseChange [K.HasPullbacks] [P.IsStableUnderBaseChange]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
      (∀ (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) → P f) :
    P.IsLocalAtTarget K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 ↦ ⟨fun hf _ ↦ P.pullback_snd _ _ hf, fun h ↦ H _ 𝒰 h⟩

lemma of_le [IsLocalAtTarget P L] (hle : K ≤ L) : IsLocalAtTarget P K where
  pullbackSnd h i hf := pullbackSnd (hle _ h) i hf
  of_forall_pullbackSnd hR h := of_forall_pullbackSnd (hle _ hR) h

instance top : IsLocalAtTarget (⊤ : MorphismProperty C) K where
  pullbackSnd := by simp
  of_forall_pullbackSnd := by simp

variable [IsLocalAtTarget P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)

lemma of_isPullback {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
    (h : IsPullback fst snd f (𝒰.f i)) (hf : P f) :
    P snd := by
  have : HasPullback f (𝒰.f i) := h.hasPullback
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact pullbackSnd 𝒰.mem₀ ⟨i⟩ hf

lemma of_zeroHypercover [K.HasPullbacks] (h : ∀ (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) :
    P f :=
  of_forall_pullbackSnd 𝒰.mem₀ (by rintro _ _ _ ⟨i⟩; exact h _)

lemma iff_of_zeroHypercover [K.HasPullbacks] : P f ↔ ∀ i, P (pullback.snd f (𝒰.f i)) :=
  ⟨fun hf _ ↦ pullbackSnd 𝒰.mem₀ ⟨_⟩ hf, fun h ↦ of_zeroHypercover _ h⟩

instance inf (P Q : MorphismProperty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K] :
    IsLocalAtTarget (P ⊓ Q) K where
  pullbackSnd hR i h := ⟨pullbackSnd hR i h.1, pullbackSnd hR i h.2⟩
  of_forall_pullbackSnd hR h :=
    ⟨of_forall_pullbackSnd hR fun i ↦ (h i).1, of_forall_pullbackSnd hR fun i ↦ (h i).2⟩

end IsLocalAtTarget

set_option backward.defeqAttrib.useBackward true in
lemma of_zeroHypercover_target {P : MorphismProperty C} {K : Precoverage C} [K.HasPullbacks]
    [P.IsLocalAtTarget K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (pullback.snd f (𝒰.f i))) :
    P f := by
  rw [IsLocalAtTarget.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

/--
A property of morphisms `P` in `C` is local at the source with respect to the precoverage `K` if
it respects isomorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `X` in the precoverage `K`.
-/
class IsLocalAtSource (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `𝒰.f i ≫ f` for any `K`-cover `R` of `X`. -/
  comp {X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R ∈ K X) {U : C} (g : U ⟶ X) (hg : R g)
    (hf : P f) : P (g ≫ f)
  /-- If `P` holds for `𝒰.f i ≫ f` for all `i`, it holds for `f : X ⟶ Y` for any `K`-cover
  `R` of X. -/
  of_forall_comp {X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R ∈ K X) :
    (∀ ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g → P (g ≫ f)) → P f

namespace IsLocalAtSource

variable {P : MorphismProperty C} {K L : Precoverage C}

lemma mk_of_iff [P.RespectsIso]
    (H : ∀ {X Y : C} {f : X ⟶ Y} {R : Presieve X}, R ∈ K X →
      (P f ↔ ∀ ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g → P (g ≫ f))) :
    P.IsLocalAtSource K where
  comp hR _ _ hg hf := by grind
  of_forall_comp hR h := by grind

lemma mk_of_iff_of_zeroHypercover [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f ↔ ∀ i, P (𝒰.f i ≫ f)) :
    P.IsLocalAtSource K := by
  refine .mk_of_iff fun {X Y} f R hR ↦ ?_
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  rw [H _ 𝒰]
  refine ⟨fun h U g ↦ ?_, fun h i ↦ h ⟨i⟩⟩
  rintro ⟨i⟩
  apply h

lemma mk_of_small [P.RespectsIso] [Precoverage.Small.{w} K]
    (h₁ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f → ∀ i, P (𝒰.f i ≫ f))
    (h₂ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X),
        (∀ i, P (𝒰.f i ≫ f)) → P f) :
    P.IsLocalAtSource K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 ↦ ⟨fun hf _ ↦ h₁ 𝒰 hf _,
    fun h ↦ h₂ 𝒰.restrictIndexOfSmall fun _ ↦ h _⟩

lemma of_le [IsLocalAtSource P L] (hle : K ≤ L) : IsLocalAtSource P K where
  comp hR _ _ := comp (hle _ hR) _
  of_forall_comp hR h := of_forall_comp (hle _ hR) h

instance top : IsLocalAtSource (⊤ : MorphismProperty C) K where
  comp := by simp
  of_forall_comp := by simp

variable [IsLocalAtSource P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)

lemma of_zeroHypercover (h : ∀ i, P (𝒰.f i ≫ f)) : P f :=
  of_forall_comp 𝒰.mem₀ fun U g ↦ by rintro ⟨i⟩; exact h _

lemma iff_of_zeroHypercover : P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun hf i ↦ comp 𝒰.mem₀ _ ⟨i⟩ hf,
    fun h ↦ of_forall_comp 𝒰.mem₀ fun U g ↦ by rintro ⟨i⟩; exact h _⟩

instance inf (P Q : MorphismProperty C) [IsLocalAtSource P K] [IsLocalAtSource Q K] :
    IsLocalAtSource (P ⊓ Q) K where
  comp hR _ _ hg hf := ⟨comp hR _ hg hf.left, comp hR _ hg hf.right⟩
  of_forall_comp hR h :=
    ⟨of_forall_comp hR fun _ _ hg ↦ (h hg).1, of_forall_comp hR fun _ _ hg ↦ (h hg).2⟩

end IsLocalAtSource

set_option backward.defeqAttrib.useBackward true in
lemma of_zeroHypercover_source {P : MorphismProperty C} {K : Precoverage C}
    [P.IsLocalAtSource K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (𝒰.f i ≫ f)) :
    P f := by
  rw [IsLocalAtSource.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

end MorphismProperty

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Let `J` be a precoverage for which isomorphisms are local at the target. Let
`f, g : X ⟶ Y` be two morphisms over `S` and `𝒰` a `J`-cover of `S`.
If for all `i`, the maps `X ×[S] Uᵢ ⟶ Y ×[S] Uᵢ` are equal, then
`f` and `g` are equal. -/
lemma eq_of_zeroHypercover_target [HasEqualizers C] [HasPullbacks C] {X Y S : C} {f g : X ⟶ Y}
    {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) {J : Precoverage C}
    (𝒰 : Precoverage.ZeroHypercover.{w} J S) [J.IsStableUnderBaseChange]
    [(MorphismProperty.isomorphisms C).IsLocalAtTarget J]
    (H : ∀ i,
      pullback.map s (𝒰.f i) t (𝒰.f i) f (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s (𝒰.f i) t (𝒰.f i) g (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  rw [(MorphismProperty.isomorphisms C).iff_of_zeroHypercover_target (𝒰.pullback₁ s)]
  intro i
  have : pullback.snd (equalizer.ι f g) (pullback.fst s (𝒰.f i)) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq (H i)

end CategoryTheory
