/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Data.Set.Opposite

/-!
# Separating and detecting sets

There are several non-equivalent notions of a generator of a category. Here, we consider two of
them:

* We say that `𝒢` is a separating set if the functors `C(G, -)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`.
* We say that `𝒢` is a detecting set if the functors `C(G, -)` collectively reflect isomorphisms,
    i.e., if any `h` with domain in `𝒢` uniquely factors through `f`, then `f` is an isomorphism.

There are, of course, also the dual notions of coseparating and codetecting sets.

## Main results

We
* define predicates `IsSeparating`, `IsCoseparating`, `IsDetecting` and `IsCodetecting` on
  sets of objects;
* show that equivalences of categories preserves these notions;
* show that separating and coseparating are dual notions;
* show that detecting and codetecting are dual notions;
* show that if `C` has equalizers, then detecting implies separating;
* show that if `C` has coequalizers, then codetecting implies coseparating;
* show that if `C` is balanced, then separating implies detecting and coseparating implies
  codetecting;
* show that `∅` is separating if and only if `∅` is coseparating if and only if `C` is thin;
* show that `∅` is detecting if and only if `∅` is codetecting if and only if `C` is a groupoid;
* define predicates `IsSeparator`, `IsCoseparator`, `IsDetector` and `IsCodetector` as the
  singleton counterparts to the definitions for sets above and restate the above results in this
  situation;
* show that `G` is a separator if and only if `coyoneda.obj (op G)` is faithful (and the dual);
* show that `G` is a detector if and only if `coyoneda.obj (op G)` reflects isomorphisms (and the
  dual);
* show that `C` is `WellPowered` if it admits small pullbacks and a detector;
* define corresponding typeclasses `HasSeparator`, `HasCoseparator`, `HasDetector`
  and `HasCodetector` on categories and prove analogous results for these.

## Future work

* We currently don't have any examples yet.

-/


universe w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- We say that `𝒢` is a separating set if the functors `C(G, -)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`. -/
def IsSeparating (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : G ⟶ X), h ≫ f = h ≫ g) → f = g

/-- We say that `𝒢` is a coseparating set if the functors `C(-, G)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `f ≫ h = g ≫ h` for all `h` with codomain in `𝒢` implies `f = g`. -/
def IsCoseparating (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : Y ⟶ G), f ≫ h = g ≫ h) → f = g

/-- We say that `𝒢` is a detecting set if the functors `C(G, -)` collectively reflect isomorphisms,
    i.e., if any `h` with domain in `𝒢` uniquely factors through `f`, then `f` is an isomorphism. -/
def IsDetecting (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : G ⟶ Y), ∃! h' : G ⟶ X, h' ≫ f = h) → IsIso f

/-- We say that `𝒢` is a codetecting set if the functors `C(-, G)` collectively reflect
    isomorphisms, i.e., if any `h` with codomain in `G` uniquely factors through `f`, then `f` is
    an isomorphism. -/
def IsCodetecting (𝒢 : Set C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : X ⟶ G), ∃! h' : Y ⟶ G, f ≫ h' = h) → IsIso f

section Equivalence

lemma IsSeparating.of_equivalence
    {𝒢 : Set C} (h : IsSeparating 𝒢) {D : Type*} [Category D] (α : C ≌ D) :
    IsSeparating (α.functor.obj '' 𝒢) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.toAdjunction.homEquiv _ _).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      H (α.functor.obj Z) (Set.mem_image_of_mem _ hZ) h']))

lemma IsCoseparating.of_equivalence
    {𝒢 : Set C} (h : IsCoseparating 𝒢) {D : Type*} [Category D] (α : C ≌ D) :
    IsCoseparating (α.functor.obj '' 𝒢) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.symm.toAdjunction.homEquiv _ _).symm.surjective h
    simp only [Adjunction.homEquiv_symm_apply, ← Category.assoc, ← Functor.map_comp,
      Equivalence.symm_functor, H (α.functor.obj Z) (Set.mem_image_of_mem _ hZ) h']))

end Equivalence

section Dual

theorem isSeparating_op_iff (𝒢 : Set C) : IsSeparating 𝒢.op ↔ IsCoseparating 𝒢 := by
  refine ⟨fun h𝒢 X Y f g hfg => ?_, fun h𝒢 X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ (Set.mem_op.1 hG) _
  · refine Quiver.Hom.unop_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ (Set.op_mem_op.2 hG) _

theorem isCoseparating_op_iff (𝒢 : Set C) : IsCoseparating 𝒢.op ↔ IsSeparating 𝒢 := by
  refine ⟨fun h𝒢 X Y f g hfg => ?_, fun h𝒢 X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ (Set.mem_op.1 hG) _
  · refine Quiver.Hom.unop_inj (h𝒢 _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ (Set.op_mem_op.2 hG) _

theorem isCoseparating_unop_iff (𝒢 : Set Cᵒᵖ) : IsCoseparating 𝒢.unop ↔ IsSeparating 𝒢 := by
  rw [← isSeparating_op_iff, Set.unop_op]

theorem isSeparating_unop_iff (𝒢 : Set Cᵒᵖ) : IsSeparating 𝒢.unop ↔ IsCoseparating 𝒢 := by
  rw [← isCoseparating_op_iff, Set.unop_op]

theorem isDetecting_op_iff (𝒢 : Set C) : IsDetecting 𝒢.op ↔ IsCodetecting 𝒢 := by
  refine ⟨fun h𝒢 X Y f hf => ?_, fun h𝒢 X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (h𝒢 _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) (Set.mem_op.1 hG) h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (h𝒢 _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) (Set.op_mem_op.2 hG) h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using hy)

theorem isCodetecting_op_iff (𝒢 : Set C) : IsCodetecting 𝒢.op ↔ IsDetecting 𝒢 := by
  refine ⟨fun h𝒢 X Y f hf => ?_, fun h𝒢 X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (h𝒢 _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) (Set.mem_op.1 hG) h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (h𝒢 _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) (Set.op_mem_op.2 hG) h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using hy)

theorem isDetecting_unop_iff (𝒢 : Set Cᵒᵖ) : IsDetecting 𝒢.unop ↔ IsCodetecting 𝒢 := by
  rw [← isCodetecting_op_iff, Set.unop_op]

theorem isCodetecting_unop_iff {𝒢 : Set Cᵒᵖ} : IsCodetecting 𝒢.unop ↔ IsDetecting 𝒢 := by
  rw [← isDetecting_op_iff, Set.unop_op]

end Dual

theorem IsDetecting.isSeparating [HasEqualizers C] {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) :
    IsSeparating 𝒢 := fun _ _ f g hfg =>
  have : IsIso (equalizer.ι f g) := h𝒢 _ fun _ hG _ => equalizer.existsUnique _ (hfg _ hG _)
  eq_of_epi_equalizer

theorem IsCodetecting.isCoseparating [HasCoequalizers C] {𝒢 : Set C} :
    IsCodetecting 𝒢 → IsCoseparating 𝒢 := by
  simpa only [← isSeparating_op_iff, ← isDetecting_op_iff] using IsDetecting.isSeparating

theorem IsSeparating.isDetecting [Balanced C] {𝒢 : Set C} (h𝒢 : IsSeparating 𝒢) :
    IsDetecting 𝒢 := by
  intro X Y f hf
  refine
    (isIso_iff_mono_and_epi _).2 ⟨⟨fun g h hgh => h𝒢 _ _ fun G hG i => ?_⟩, ⟨fun g h hgh => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (Category.assoc _ _ _), ht (i ≫ h) (hgh.symm ▸ Category.assoc _ _ _)]
  · refine h𝒢 _ _ fun G hG i => ?_
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [Category.assoc, hgh, Category.assoc]

lemma IsDetecting.isIso_iff_of_mono {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ ∀ s ∈ 𝒢, Function.Surjective ((coyoneda.obj (op s)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine h𝒢 _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f, h₁, h₂]

lemma IsCodetecting.isIso_iff_of_epi {𝒢 : Set C} (h𝒢 : IsCodetecting 𝒢)
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsIso f ↔ ∀ s ∈ 𝒢, Function.Surjective ((yoneda.obj s).map f.op) := by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine h𝒢 _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f, h₁, h₂]

section

attribute [local instance] balanced_opposite

theorem IsCoseparating.isCodetecting [Balanced C] {𝒢 : Set C} :
    IsCoseparating 𝒢 → IsCodetecting 𝒢 := by
  simpa only [← isDetecting_op_iff, ← isSeparating_op_iff] using IsSeparating.isDetecting

end

theorem isDetecting_iff_isSeparating [HasEqualizers C] [Balanced C] (𝒢 : Set C) :
    IsDetecting 𝒢 ↔ IsSeparating 𝒢 :=
  ⟨IsDetecting.isSeparating, IsSeparating.isDetecting⟩

theorem isCodetecting_iff_isCoseparating [HasCoequalizers C] [Balanced C] {𝒢 : Set C} :
    IsCodetecting 𝒢 ↔ IsCoseparating 𝒢 :=
  ⟨IsCodetecting.isCoseparating, IsCoseparating.isCodetecting⟩

section Mono

theorem IsSeparating.mono {𝒢 : Set C} (h𝒢 : IsSeparating 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
    IsSeparating ℋ := fun _ _ _ _ hfg => h𝒢 _ _ fun _ hG _ => hfg _ (h𝒢ℋ hG) _

theorem IsCoseparating.mono {𝒢 : Set C} (h𝒢 : IsCoseparating 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
    IsCoseparating ℋ := fun _ _ _ _ hfg => h𝒢 _ _ fun _ hG _ => hfg _ (h𝒢ℋ hG) _

theorem IsDetecting.mono {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
    IsDetecting ℋ := fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h𝒢ℋ hG) _

theorem IsCodetecting.mono {𝒢 : Set C} (h𝒢 : IsCodetecting 𝒢) {ℋ : Set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
    IsCodetecting ℋ := fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h𝒢ℋ hG) _

end Mono

section Empty

theorem thin_of_isSeparating_empty (h : IsSeparating (∅ : Set C)) : Quiver.IsThin C := fun _ _ =>
  ⟨fun _ _ => h _ _ fun _ => False.elim⟩

theorem isSeparating_empty_of_thin [Quiver.IsThin C] : IsSeparating (∅ : Set C) :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

theorem thin_of_isCoseparating_empty (h : IsCoseparating (∅ : Set C)) : Quiver.IsThin C :=
  fun _ _ => ⟨fun _ _ => h _ _ fun _ => False.elim⟩

theorem isCoseparating_empty_of_thin [Quiver.IsThin C] : IsCoseparating (∅ : Set C) :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

theorem groupoid_of_isDetecting_empty (h : IsDetecting (∅ : Set C)) {X Y : C} (f : X ⟶ Y) :
    IsIso f :=
  h _ fun _ => False.elim

theorem isDetecting_empty_of_groupoid [∀ {X Y : C} (f : X ⟶ Y), IsIso f] :
    IsDetecting (∅ : Set C) := fun _ _ _ _ => inferInstance

theorem groupoid_of_isCodetecting_empty (h : IsCodetecting (∅ : Set C)) {X Y : C} (f : X ⟶ Y) :
    IsIso f :=
  h _ fun _ => False.elim

theorem isCodetecting_empty_of_groupoid [∀ {X Y : C} (f : X ⟶ Y), IsIso f] :
    IsCodetecting (∅ : Set C) := fun _ _ _ _ => inferInstance

end Empty

theorem isSeparating_iff_epi (𝒢 : Set C)
    [∀ A : C, HasCoproduct fun f : Σ G : 𝒢, (G : C) ⟶ A => (f.1 : C)] :
    IsSeparating 𝒢 ↔ ∀ A : C, Epi (Sigma.desc (@Sigma.snd 𝒢 fun G => (G : C) ⟶ A)) := by
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun G hG f => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι (fun f : Σ G : 𝒢, (G : C) ⟶ A => (f.1 : C)) ⟨⟨G, hG⟩, f⟩ ≫= huv
  · haveI := h X
    refine
      (cancel_epi (Sigma.desc (@Sigma.snd 𝒢 fun G => (G : C) ⟶ X))).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as.1.1 j.as.1.2 j.as.2

theorem isCoseparating_iff_mono (𝒢 : Set C)
    [∀ A : C, HasProduct fun f : Σ G : 𝒢, A ⟶ (G : C) => (f.1 : C)] :
    IsCoseparating 𝒢 ↔ ∀ A : C, Mono (Pi.lift (@Sigma.snd 𝒢 fun G => A ⟶ (G : C))) := by
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun G hG f => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using huv =≫ Pi.π (fun f : Σ G : 𝒢, A ⟶ (G : C) => (f.1 : C)) ⟨⟨G, hG⟩, f⟩
  · haveI := h Y
    refine (cancel_mono (Pi.lift (@Sigma.snd 𝒢 fun G => Y ⟶ (G : C)))).1 (limit.hom_ext fun j => ?_)
    simpa using hh j.as.1.1 j.as.1.2 j.as.2

/-- An ingredient of the proof of the Special Adjoint Functor Theorem: a complete well-powered
    category with a small coseparating set has an initial object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is already cocomplete,
    see `hasColimits_of_hasLimits_of_isCoseparating`. -/
theorem hasInitial_of_isCoseparating [LocallySmall.{w} C] [WellPowered.{w} C]
    [HasLimitsOfSize.{w, w} C] {𝒢 : Set C} [Small.{w} 𝒢]
    (h𝒢 : IsCoseparating 𝒢) : HasInitial C := by
  have := hasFiniteLimits_of_hasLimitsOfSize C
  haveI : HasProductsOfShape 𝒢 C := hasProductsOfShape_of_small C 𝒢
  haveI := fun A => hasProductsOfShape_of_small.{w} C (Σ G : 𝒢, A ⟶ (G : C))
  letI := completeLatticeOfCompleteSemilatticeInf (Subobject (piObj (Subtype.val : 𝒢 → C)))
  suffices ∀ A : C, Unique (((⊥ : Subobject (piObj (Subtype.val : 𝒢 → C))) : C) ⟶ A) by
    exact hasInitial_of_unique ((⊥ : Subobject (piObj (Subtype.val : 𝒢 → C))) : C)
  refine fun A => ⟨⟨?_⟩, fun f => ?_⟩
  · let s := Pi.lift fun f : Σ G : 𝒢, A ⟶ (G : C) => id (Pi.π (Subtype.val : 𝒢 → C)) f.1
    let t := Pi.lift (@Sigma.snd 𝒢 fun G => A ⟶ (G : C))
    haveI : Mono t := (isCoseparating_iff_mono 𝒢).1 h𝒢 A
    exact Subobject.ofLEMk _ (pullback.fst _ _ : pullback s t ⟶ _) bot_le ≫ pullback.snd _ _
  · suffices ∀ (g : Subobject.underlying.obj ⊥ ⟶ A), f = g by
      apply this
    intro g
    suffices IsSplitEpi (equalizer.ι f g) by exact eq_of_epi_equalizer
    exact IsSplitEpi.mk' ⟨Subobject.ofLEMk _ (equalizer.ι f g ≫ Subobject.arrow _) bot_le, by
      ext
      simp⟩

/-- An ingredient of the proof of the Special Adjoint Functor Theorem: a cocomplete well-copowered
    category with a small separating set has a terminal object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is already complete, see
    `hasLimits_of_hasColimits_of_isSeparating`. -/
theorem hasTerminal_of_isSeparating [LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ]
    [HasColimitsOfSize.{w, w} C] {𝒢 : Set C} [Small.{w} 𝒢]
    (h𝒢 : IsSeparating 𝒢) : HasTerminal C := by
  haveI : Small.{w} 𝒢.op := small_of_injective (Set.opEquiv_self 𝒢).injective
  haveI : HasInitial Cᵒᵖ := hasInitial_of_isCoseparating ((isCoseparating_op_iff _).2 h𝒢)
  exact hasTerminal_of_hasInitial_op

section WellPowered

namespace Subobject

theorem eq_of_le_of_isDetecting {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) {X : C} (P Q : Subobject X)
    (h₁ : P ≤ Q) (h₂ : ∀ G ∈ 𝒢, ∀ {f : G ⟶ X}, Q.Factors f → P.Factors f) : P = Q := by
  suffices IsIso (ofLE _ _ h₁) by exact le_antisymm h₁ (le_of_comm (inv (ofLE _ _ h₁)) (by simp))
  refine h𝒢 _ fun G hG f => ?_
  have : P.Factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩)
  refine ⟨factorThru _ _ this, ?_, fun g (hg : g ≫ _ = f) => ?_⟩
  · simp only [← cancel_mono Q.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  · simp only [← cancel_mono (Subobject.ofLE _ _ h₁), ← cancel_mono Q.arrow, hg, Category.assoc,
      ofLE_arrow, factorThru_arrow]

theorem inf_eq_of_isDetecting [HasPullbacks C] {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) {X : C}
    (P Q : Subobject X) (h : ∀ G ∈ 𝒢, ∀ {f : G ⟶ X}, P.Factors f → Q.Factors f) : P ⊓ Q = P :=
  eq_of_le_of_isDetecting h𝒢 _ _ _root_.inf_le_left
    fun _ hG _ hf => (inf_factors _).2 ⟨hf, h _ hG hf⟩

theorem eq_of_isDetecting [HasPullbacks C] {𝒢 : Set C} (h𝒢 : IsDetecting 𝒢) {X : C}
    (P Q : Subobject X) (h : ∀ G ∈ 𝒢, ∀ {f : G ⟶ X}, P.Factors f ↔ Q.Factors f) : P = Q :=
  calc
    P = P ⊓ Q := Eq.symm <| inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).1 hf
    _ = Q ⊓ P := inf_comm ..
    _ = Q := inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).2 hf

end Subobject

/-- A category with pullbacks and a small detecting set is well-powered. -/
theorem wellPowered_of_isDetecting [HasPullbacks C] {𝒢 : Set C} [Small.{w} 𝒢]
    [LocallySmall.{w} C] (h𝒢 : IsDetecting 𝒢) : WellPowered.{w} C :=
  ⟨fun X =>
    @small_of_injective _ _ _ (fun P : Subobject X => { f : Σ G : 𝒢, G.1 ⟶ X | P.Factors f.2 })
      fun P Q h => Subobject.eq_of_isDetecting h𝒢 _ _
        (by simpa [Set.ext_iff, Sigma.forall] using h)⟩

end WellPowered

namespace StructuredArrow

variable (S : D) (T : C ⥤ D)

theorem isCoseparating_proj_preimage {𝒢 : Set C} (h𝒢 : IsCoseparating 𝒢) :
    IsCoseparating ((proj S T).obj ⁻¹' 𝒢) := by
  refine fun X Y f g hfg => ext _ _ (h𝒢 _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.right (hfg (mk (Y.hom ≫ T.map h)) hG (homMk h rfl))

end StructuredArrow

namespace CostructuredArrow

variable (S : C ⥤ D) (T : D)

theorem isSeparating_proj_preimage {𝒢 : Set C} (h𝒢 : IsSeparating 𝒢) :
    IsSeparating ((proj S T).obj ⁻¹' 𝒢) := by
  refine fun X Y f g hfg => ext _ _ (h𝒢 _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.left (hfg (mk (S.map h ≫ X.hom)) hG (homMk h rfl))

end CostructuredArrow

/-- We say that `G` is a separator if the functor `C(G, -)` is faithful. -/
def IsSeparator (G : C) : Prop :=
  IsSeparating ({G} : Set C)

/-- We say that `G` is a coseparator if the functor `C(-, G)` is faithful. -/
def IsCoseparator (G : C) : Prop :=
  IsCoseparating ({G} : Set C)

/-- We say that `G` is a detector if the functor `C(G, -)` reflects isomorphisms. -/
def IsDetector (G : C) : Prop :=
  IsDetecting ({G} : Set C)

/-- We say that `G` is a codetector if the functor `C(-, G)` reflects isomorphisms. -/
def IsCodetector (G : C) : Prop :=
  IsCodetecting ({G} : Set C)


section Equivalence

theorem IsSeparator.of_equivalence {G : C} (h : IsSeparator G) (α : C ≌ D) :
    IsSeparator (α.functor.obj G) := by simpa using IsSeparating.of_equivalence h α

theorem IsCoseparator.of_equivalence {G : C} (h : IsCoseparator G) (α : C ≌ D) :
    IsCoseparator (α.functor.obj G) := by simpa using IsCoseparating.of_equivalence h α

end Equivalence

section Dual

theorem isSeparator_op_iff (G : C) : IsSeparator (op G) ↔ IsCoseparator G := by
  rw [IsSeparator, IsCoseparator, ← isSeparating_op_iff, Set.singleton_op]

theorem isCoseparator_op_iff (G : C) : IsCoseparator (op G) ↔ IsSeparator G := by
  rw [IsSeparator, IsCoseparator, ← isCoseparating_op_iff, Set.singleton_op]

theorem isCoseparator_unop_iff (G : Cᵒᵖ) : IsCoseparator (unop G) ↔ IsSeparator G := by
  rw [IsSeparator, IsCoseparator, ← isCoseparating_unop_iff, Set.singleton_unop]

theorem isSeparator_unop_iff (G : Cᵒᵖ) : IsSeparator (unop G) ↔ IsCoseparator G := by
  rw [IsSeparator, IsCoseparator, ← isSeparating_unop_iff, Set.singleton_unop]

theorem isDetector_op_iff (G : C) : IsDetector (op G) ↔ IsCodetector G := by
  rw [IsDetector, IsCodetector, ← isDetecting_op_iff, Set.singleton_op]

theorem isCodetector_op_iff (G : C) : IsCodetector (op G) ↔ IsDetector G := by
  rw [IsDetector, IsCodetector, ← isCodetecting_op_iff, Set.singleton_op]

theorem isCodetector_unop_iff (G : Cᵒᵖ) : IsCodetector (unop G) ↔ IsDetector G := by
  rw [IsDetector, IsCodetector, ← isCodetecting_unop_iff, Set.singleton_unop]

theorem isDetector_unop_iff (G : Cᵒᵖ) : IsDetector (unop G) ↔ IsCodetector G := by
  rw [IsDetector, IsCodetector, ← isDetecting_unop_iff, Set.singleton_unop]

end Dual

theorem IsDetector.isSeparator [HasEqualizers C] {G : C} : IsDetector G → IsSeparator G :=
  IsDetecting.isSeparating

theorem IsCodetector.isCoseparator [HasCoequalizers C] {G : C} : IsCodetector G → IsCoseparator G :=
  IsCodetecting.isCoseparating

theorem IsSeparator.isDetector [Balanced C] {G : C} : IsSeparator G → IsDetector G :=
  IsSeparating.isDetecting

theorem IsCoseparator.isCodetector [Balanced C] {G : C} : IsCoseparator G → IsCodetector G :=
  IsCoseparating.isCodetecting

theorem isSeparator_def (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (Set.mem_singleton _) _⟩

theorem IsSeparator.def {G : C} :
    IsSeparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  (isSeparator_def _).1

theorem isCoseparator_def (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (Set.mem_singleton _) _⟩

theorem IsCoseparator.def {G : C} :
    IsCoseparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  (isCoseparator_def _).1

theorem isDetector_def (G : C) :
    IsDetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (Set.mem_singleton _) _⟩

theorem IsDetector.def {G : C} :
    IsDetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  (isDetector_def _).1

theorem isCodetector_def (G : C) :
    IsCodetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := Set.mem_singleton_iff.1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (Set.mem_singleton _) _⟩

theorem IsCodetector.def {G : C} :
    IsCodetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  (isCodetector_def _).1

theorem isSeparator_iff_faithful_coyoneda_obj (G : C) :
    IsSeparator G ↔ (coyoneda.obj (op G)).Faithful :=
  ⟨fun hG => ⟨fun hfg => hG.def _ _ (congr_fun hfg)⟩, fun _ =>
    (isSeparator_def _).2 fun _ _ _ _ hfg => (coyoneda.obj (op G)).map_injective (funext hfg)⟩

theorem isCoseparator_iff_faithful_yoneda_obj (G : C) : IsCoseparator G ↔ (yoneda.obj G).Faithful :=
  ⟨fun hG => ⟨fun hfg => Quiver.Hom.unop_inj (hG.def _ _ (congr_fun hfg))⟩, fun _ =>
    (isCoseparator_def _).2 fun _ _ _ _ hfg =>
      Quiver.Hom.op_inj <| (yoneda.obj G).map_injective (funext hfg)⟩

theorem isSeparator_iff_epi (G : C) [∀ A : C, HasCoproduct fun _ : G ⟶ A => G] :
    IsSeparator G ↔ ∀ A : C, Epi (Sigma.desc fun f : G ⟶ A => f) := by
  rw [isSeparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι _ i ≫= huv
  · haveI := h X
    refine (cancel_epi (Sigma.desc fun f : G ⟶ X => f)).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as

theorem isCoseparator_iff_mono (G : C) [∀ A : C, HasProduct fun _ : A ⟶ G => G] :
    IsCoseparator G ↔ ∀ A : C, Mono (Pi.lift fun f : A ⟶ G => f) := by
  rw [isCoseparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using huv =≫ Pi.π _ i
  · haveI := h Y
    refine (cancel_mono (Pi.lift fun f : Y ⟶ G => f)).1 (limit.hom_ext fun j => ?_)
    simpa using hh j.as

section ZeroMorphisms

variable [HasZeroMorphisms C]

theorem isSeparator_coprod (G H : C) [HasBinaryCoproduct G H] :
    IsSeparator (G ⨿ H) ↔ IsSeparating ({G, H} : Set C) := by
  refine
    ⟨fun h X Y u v huv => ?_, fun h =>
      (isSeparator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => ?_⟩
  · refine h.def _ _ fun g => coprod.hom_ext ?_ ?_
    · simpa using huv G (by simp) (coprod.inl ≫ g)
    · simpa using huv H (by simp) (coprod.inr ≫ g)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with (rfl | rfl)
    · simpa using coprod.inl ≫= huv (coprod.desc g 0)
    · simpa using coprod.inr ≫= huv (coprod.desc 0 g)

theorem isSeparator_coprod_of_isSeparator_left (G H : C) [HasBinaryCoproduct G H]
    (hG : IsSeparator G) : IsSeparator (G ⨿ H) :=
  (isSeparator_coprod _ _).2 <| IsSeparating.mono hG <| by simp

theorem isSeparator_coprod_of_isSeparator_right (G H : C) [HasBinaryCoproduct G H]
    (hH : IsSeparator H) : IsSeparator (G ⨿ H) :=
  (isSeparator_coprod _ _).2 <| IsSeparating.mono hH <| by simp

lemma isSeparator_of_isColimit_cofan {β : Type w} {f : β → C}
    (hf : IsSeparating (Set.range f)) {c : Cofan f} (hc : IsColimit c) : IsSeparator c.pt := by
  refine (isSeparator_def _).2 fun X Y u v huv => hf _ _ fun Z hZ g => ?_
  obtain ⟨b, rfl⟩ := Set.mem_range.1 hZ
  classical simpa using c.ι.app ⟨b⟩ ≫= huv (hc.desc (Cofan.mk _ (Pi.single b g)))

theorem isSeparator_sigma {β : Type w} (f : β → C) [HasCoproduct f] :
    IsSeparator (∐ f) ↔ IsSeparating (Set.range f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isSeparator_of_isColimit_cofan h (colimit.isColimit _)⟩
  refine h.def _ _ fun g => colimit.hom_ext fun b => ?_
  simpa using huv (f b.as) (by simp) (colimit.ι (Discrete.functor f) _ ≫ g)

theorem IsSeparating.isSeparator_coproduct {β : Type w} {f : β → C} [HasCoproduct f]
    (hS : IsSeparating (Set.range f)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 hS

theorem isSeparator_sigma_of_isSeparator {β : Type w} (f : β → C) [HasCoproduct f] (b : β)
    (hb : IsSeparator (f b)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 <| IsSeparating.mono hb <| by simp

theorem isCoseparator_prod (G H : C) [HasBinaryProduct G H] :
    IsCoseparator (G ⨯ H) ↔ IsCoseparating ({G, H} : Set C) := by
  refine
    ⟨fun h X Y u v huv => ?_, fun h =>
      (isCoseparator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => ?_⟩
  · refine h.def _ _ fun g => Limits.prod.hom_ext ?_ ?_
    · simpa using huv G (by simp) (g ≫ Limits.prod.fst)
    · simpa using huv H (by simp) (g ≫ Limits.prod.snd)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with (rfl | rfl)
    · simpa using huv (prod.lift g 0) =≫ Limits.prod.fst
    · simpa using huv (prod.lift 0 g) =≫ Limits.prod.snd

theorem isCoseparator_prod_of_isCoseparator_left (G H : C) [HasBinaryProduct G H]
    (hG : IsCoseparator G) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| IsCoseparating.mono hG <| by simp

theorem isCoseparator_prod_of_isCoseparator_right (G H : C) [HasBinaryProduct G H]
    (hH : IsCoseparator H) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| IsCoseparating.mono hH <| by simp

theorem isCoseparator_pi {β : Type w} (f : β → C) [HasProduct f] :
    IsCoseparator (∏ᶜ f) ↔ IsCoseparating (Set.range f) := by
  refine
    ⟨fun h X Y u v huv => ?_, fun h =>
      (isCoseparator_def _).2 fun X Y u v huv => h _ _ fun Z hZ g => ?_⟩
  · refine h.def _ _ fun g => limit.hom_ext fun b => ?_
    simpa using huv (f b.as) (by simp) (g ≫ limit.π (Discrete.functor f) _)
  · obtain ⟨b, rfl⟩ := Set.mem_range.1 hZ
    classical simpa using huv (Pi.lift (Pi.single b g)) =≫ Pi.π f b

theorem isCoseparator_pi_of_isCoseparator {β : Type w} (f : β → C) [HasProduct f] (b : β)
    (hb : IsCoseparator (f b)) : IsCoseparator (∏ᶜ f) :=
  (isCoseparator_pi _).2 <| IsCoseparating.mono hb <| by simp

end ZeroMorphisms

theorem isDetector_iff_reflectsIsomorphisms_coyoneda_obj (G : C) :
    IsDetector G ↔ (coyoneda.obj (op G)).ReflectsIsomorphisms := by
  refine
    ⟨fun hG => ⟨fun f hf => hG.def _ fun h => ?_⟩, fun h =>
      (isDetector_def _).2 fun X Y f hf => ?_⟩
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
    exact hf h
  · suffices IsIso ((coyoneda.obj (op G)).map f) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

theorem isCodetector_iff_reflectsIsomorphisms_yoneda_obj (G : C) :
    IsCodetector G ↔ (yoneda.obj G).ReflectsIsomorphisms := by
  refine ⟨fun hG => ⟨fun f hf => ?_⟩, fun h => (isCodetector_def _).2 fun X Y f hf => ?_⟩
  · refine (isIso_unop_iff _).1 (hG.def _ ?_)
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
  · rw [← isIso_op_iff]
    suffices IsIso ((yoneda.obj G).map f.op) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

theorem wellPowered_of_isDetector [HasPullbacks C] (G : C) (hG : IsDetector G) :
    WellPowered.{v₁} C :=
  wellPowered_of_isDetecting hG

theorem wellPowered_of_isSeparator [HasPullbacks C] [Balanced C] (G : C) (hG : IsSeparator G) :
    WellPowered.{v₁} C := wellPowered_of_isDetecting hG.isDetector

section HasGenerator

section Definitions

variable (C)

/--
For a category `C` and an object `G : C`, `G` is a separator of `C` if
the functor `C(G, -)` is faithful.

While `IsSeparator G : Prop` is the proposition that `G` is a separator of `C`,
an `HasSeparator C : Prop` is the proposition that such a separator exists.
Note that `HasSeparator C` is a proposition. It does not designate a favored separator
and merely asserts the existence of one.
-/
class HasSeparator : Prop where
  hasSeparator : ∃ G : C, IsSeparator G

/--
For a category `C` and an object `G : C`, `G` is a coseparator of `C` if
the functor `C(-, G)` is faithful.

While `IsCoseparator G : Prop` is the proposition that `G` is a coseparator of `C`,
an `HasCoseparator C : Prop` is the proposition that such a coseparator exists.
Note that `HasCoseparator C` is a proposition. It does not designate a favored coseparator
and merely asserts the existence of one.
-/
class HasCoseparator : Prop where
  hasCoseparator : ∃ G : C, IsCoseparator G

/--
For a category `C` and an object `G : C`, `G` is a detector of `C` if
the functor `C(G, -)` reflects isomorphisms.

While `IsDetector G : Prop` is the proposition that `G` is a detector of `C`,
an `HasDetector C : Prop` is the proposition that such a detector exists.
Note that `HasDetector C` is a proposition. It does not designate a favored detector
and merely asserts the existence of one.
-/
class HasDetector : Prop where
  hasDetector : ∃ G : C, IsDetector G

/--
For a category `C` and an object `G : C`, `G` is a codetector of `C` if
the functor `C(-, G)` reflects isomorphisms.

While `IsCodetector G : Prop` is the proposition that `G` is a codetector of `C`,
an `HasCodetector C : Prop` is the proposition that such a codetector exists.
Note that `HasCodetector C` is a proposition. It does not designate a favored codetector
and merely asserts the existence of one.
-/
class HasCodetector : Prop where
  hasCodetector : ∃ G : C, IsCodetector G

end Definitions

section Choice

variable (C)

/--
Given a category `C` that has a separator (`HasSeparator C`), `separator C` is an arbitrarily
chosen separator of `C`.
-/
noncomputable def separator [HasSeparator C] : C := HasSeparator.hasSeparator.choose

/--
Given a category `C` that has a coseparator (`HasCoseparator C`), `coseparator C` is an arbitrarily
chosen coseparator of `C`.
-/
noncomputable def coseparator [HasCoseparator C] : C := HasCoseparator.hasCoseparator.choose

/--
Given a category `C` that has a detector (`HasDetector C`), `detector C` is an arbitrarily
chosen detector of `C`.
-/
noncomputable def detector [HasDetector C] : C := HasDetector.hasDetector.choose

/--
Given a category `C` that has a codetector (`HasCodetector C`), `codetector C` is an arbitrarily
chosen codetector of `C`.
-/
noncomputable def codetector [HasCodetector C] : C := HasCodetector.hasCodetector.choose

theorem isSeparator_separator [HasSeparator C] : IsSeparator (separator C) :=
  HasSeparator.hasSeparator.choose_spec

theorem isDetector_separator [Balanced C] [HasSeparator C] : IsDetector (separator C) :=
  isSeparator_separator C |>.isDetector

theorem isCoseparator_coseparator [HasCoseparator C] : IsCoseparator (coseparator C) :=
  HasCoseparator.hasCoseparator.choose_spec

theorem isCodetector_coseparator [Balanced C] [HasCoseparator C] : IsCodetector (coseparator C) :=
  isCoseparator_coseparator C |>.isCodetector

theorem isDetector_detector [HasDetector C] : IsDetector (detector C) :=
  HasDetector.hasDetector.choose_spec

theorem isSeparator_detector [HasEqualizers C] [HasDetector C] : IsSeparator (detector C) :=
  isDetector_detector C |>.isSeparator

theorem isCodetector_codetector [HasCodetector C] : IsCodetector (codetector C) :=
  HasCodetector.hasCodetector.choose_spec

theorem isCoseparator_codetector [HasCoequalizers C] [HasCodetector C] :
    IsCoseparator (codetector C) := isCodetector_codetector C |>.isCoseparator

end Choice

section Instances

theorem HasSeparator.hasDetector [Balanced C] [HasSeparator C] : HasDetector C :=
  ⟨_, isDetector_separator C⟩

theorem HasDetector.hasSeparator [HasEqualizers C] [HasDetector C] : HasSeparator C :=
  ⟨_, isSeparator_detector C⟩

theorem HasCoseparator.hasCodetector [Balanced C] [HasCoseparator C] : HasCodetector C :=
  ⟨_, isCodetector_coseparator C⟩

theorem HasCodetector.hasCoseparator [HasCoequalizers C] [HasCodetector C] : HasCoseparator C :=
  ⟨_, isCoseparator_codetector C⟩

instance HasDetector.wellPowered [HasPullbacks C] [HasDetector C] : WellPowered.{v₁} C :=
  isDetector_detector C |> wellPowered_of_isDetector _

instance HasSeparator.wellPowered [HasPullbacks C] [Balanced C] [HasSeparator C] :
    WellPowered.{v₁} C := HasSeparator.hasDetector.wellPowered

end Instances

section Equivalence

theorem HasSeparator.of_equivalence [HasSeparator C] (α : C ≌ D) : HasSeparator D :=
  ⟨α.functor.obj (separator C), isSeparator_separator C |>.of_equivalence α⟩

theorem HasCoseparator.of_equivalence [HasCoseparator C] (α : C ≌ D) : HasCoseparator D :=
  ⟨α.functor.obj (coseparator C), isCoseparator_coseparator C |>.of_equivalence α⟩

end Equivalence

section Dual

@[simp]
theorem hasSeparator_op_iff : HasSeparator Cᵒᵖ ↔ HasCoseparator C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCoseparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isSeparator_op_iff G).mpr hG⟩⟩

@[simp]
theorem hasCoseparator_op_iff : HasCoseparator Cᵒᵖ ↔ HasSeparator C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isSeparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCoseparator_op_iff G).mpr hG⟩⟩

@[simp]
theorem hasDetector_op_iff : HasDetector Cᵒᵖ ↔ HasCodetector C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCodetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isDetector_op_iff G).mpr hG⟩⟩

@[simp]
theorem hasCodetector_op_iff : HasCodetector Cᵒᵖ ↔ HasDetector C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isDetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCodetector_op_iff G).mpr hG⟩⟩

instance HasSeparator.hasCoseparator_op [HasSeparator C] : HasCoseparator Cᵒᵖ := by simp [*]
theorem HasSeparator.hasCoseparator_of_hasSeparator_op [h : HasSeparator Cᵒᵖ] :
    HasCoseparator C := by simp_all

instance HasCoseparator.hasSeparator_op [HasCoseparator C] : HasSeparator Cᵒᵖ := by simp [*]
theorem HasCoseparator.hasSeparator_of_hasCoseparator_op [HasCoseparator Cᵒᵖ] :
    HasSeparator C := by simp_all

instance HasDetector.hasCodetector_op [HasDetector C] : HasCodetector Cᵒᵖ := by simp [*]
theorem HasDetector.hasCodetector_of_hasDetector_op [HasDetector Cᵒᵖ] :
    HasCodetector C := by simp_all

instance HasCodetector.hasDetector_op [HasCodetector C] : HasDetector Cᵒᵖ := by simp [*]
theorem HasCodetector.hasDetector_of_hasCodetector_op [HasCodetector Cᵒᵖ] :
    HasDetector C := by simp_all

end Dual

end HasGenerator

end CategoryTheory
