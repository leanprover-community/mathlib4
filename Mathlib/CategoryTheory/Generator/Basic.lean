/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Separating and detecting sets

There are several non-equivalent notions of a generator of a category. Here, we consider two of
them:

* We say that `P : ObjectProperty C` is a separating set if the functors `C(G, -)`
    for `G` such that `P G` are collectively faithful, i.e., if
    `h ≫ f = h ≫ g` for all `h` with domain satisfying `P` implies `f = g`.
* We say that `P : ObjectProperty C` is a detecting set if the functors `C(G, -)`
    collectively reflect isomorphisms, i.e., if any `h` with domain satisfying `P`
    uniquely factors through `f`, then `f` is an isomorphism.

There are, of course, also the dual notions of coseparating and codetecting sets.

## Main results

We
* define predicates `IsSeparating`, `IsCoseparating`, `IsDetecting` and `IsCodetecting` on
  `ObjectProperty C`;
* show that equivalences of categories preserve these notions;
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

## Examples

See the files `CategoryTheory.Generator.Presheaf` and `CategoryTheory.Generator.Sheaf`.

-/

@[expose] public section


universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- We say that `P : ObjectProperty C` is separating if the functors `C(G, -)`
for `G : C` such that `P G` are collectively faithful,
i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`. -/
def IsSeparating : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G : C) (_ : P G) (h : G ⟶ X), h ≫ f = h ≫ g) → f = g

/-- We say that `P : ObjectProperty C` is coseparating if the functors `C(-, G)`
for `G : C` such that `P G` are collectively faithful,
i.e., if `f ≫ h = g ≫ h` for all `h` with codomain in `𝒢` implies `f = g`. -/
def IsCoseparating : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G : C) (_ : P G) (h : Y ⟶ G), f ≫ h = g ≫ h) → f = g

/-- We say that `P : ObjectProperty C` is detecting if the functors `C(G, -)`
for `G : C` such that `P G` collectively reflect isomorphisms,
i.e., if any `h` with domain `G` that `P G` uniquely factors through `f`,
then `f` is an isomorphism. -/
def IsDetecting : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C) (_ : P G),
    ∀ (h : G ⟶ Y), ∃! h' : G ⟶ X, h' ≫ f = h) → IsIso f

/-- We say that `P : ObjectProperty C` is codetecting if the functors `C(-, G)`
for `G : C` such that `P G` collectively reflect isomorphisms,
i.e., if any `h` with codomain `G` such that `P G` uniquely factors through `f`,
then `f` is an isomorphism. -/
def IsCodetecting : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C) (_ : P G),
    ∀ (h : X ⟶ G), ∃! h' : Y ⟶ G, f ≫ h' = h) → IsIso f

section Equivalence

variable {P}

set_option backward.isDefEq.respectTransparency false in
lemma IsSeparating.of_equivalence
    (h : IsSeparating P) {D : Type*} [Category* D] (α : C ≌ D) :
    IsSeparating (P.strictMap α.functor) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h ↦ by
    obtain ⟨h', rfl⟩ := (α.toAdjunction.homEquiv _ _).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      H _ (P.strictMap_obj _ hZ) h']))

set_option backward.isDefEq.respectTransparency false in
lemma IsCoseparating.of_equivalence
    (h : IsCoseparating P) {D : Type*} [Category* D] (α : C ≌ D) :
    IsCoseparating (P.strictMap α.functor) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h ↦ by
    obtain ⟨h', rfl⟩ := (α.symm.toAdjunction.homEquiv _ _).symm.surjective h
    simp only [Equivalence.symm_inverse, Equivalence.symm_functor,
      Adjunction.homEquiv_counit, ← Functor.map_comp_assoc,
      H _ (P.strictMap_obj _ hZ) h']))

end Equivalence

section Dual

theorem isSeparating_op_iff : IsSeparating P.op ↔ IsCoseparating P := by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

theorem isCoseparating_op_iff : IsCoseparating P.op ↔ IsSeparating P := by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

theorem isCoseparating_unop_iff (P : ObjectProperty Cᵒᵖ) :
    IsCoseparating P.unop ↔ IsSeparating P :=
  P.unop.isSeparating_op_iff.symm

theorem isSeparating_unop_iff (P : ObjectProperty Cᵒᵖ) :
    IsSeparating P.unop ↔ IsCoseparating P :=
  P.unop.isCoseparating_op_iff.symm

theorem isDetecting_op_iff : IsDetecting P.op ↔ IsCodetecting P := by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using hy)

theorem isCodetecting_op_iff : IsCodetecting P.op ↔ IsDetecting P := by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using hy)

theorem isDetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsDetecting P.unop ↔ IsCodetecting P :=
  P.unop.isCodetecting_op_iff.symm

theorem isCodetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsCodetecting P.unop ↔ IsDetecting P :=
  P.unop.isDetecting_op_iff.symm

end Dual

variable {P}

theorem IsDetecting.isSeparating [HasEqualizers C] (hP : IsDetecting P) :
    IsSeparating P := fun _ _ f g hfg =>
  have : IsIso (equalizer.ι f g) := hP _ fun _ hG _ => equalizer.existsUnique _ (hfg _ hG _)
  eq_of_epi_equalizer

theorem IsCodetecting.isCoseparating [HasCoequalizers C] :
    IsCodetecting P → IsCoseparating P := by
  simpa only [← isSeparating_op_iff, ← isDetecting_op_iff] using IsDetecting.isSeparating

lemma IsSeparating.mono_iff (hP : IsSeparating P) {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ (G : C) (_ : P G), ∀ (g₁ g₂ : G ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ = g₂ :=
  ⟨fun _ _ _ _ _ h ↦ by simpa [cancel_mono] using h,
    fun hf ↦ ⟨fun g₁ g₂ h ↦ hP _ _  (fun G hG h' ↦ hf _ hG _ _ (by simp [h]))⟩⟩

lemma IsCoseparating.epi_iff (hP : IsCoseparating P) {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ (G : C) (_ : P G), ∀ (g₁ g₂ : Y ⟶ G), f ≫ g₁ = f ≫ g₂ → g₁ = g₂ :=
  ⟨fun _ _ _ _ _ h ↦ by simpa [cancel_epi] using h,
    fun hf ↦ ⟨fun g₁ g₂ h ↦ hP _ _  (fun G hG h' ↦ hf _ hG _ _ (by simp [reassoc_of% h]))⟩⟩

theorem IsSeparating.isDetecting [Balanced C] (hP : IsSeparating P) :
    IsDetecting P := by
  intro X Y f hf
  refine
    (isIso_iff_mono_and_epi _).2 ⟨⟨fun g h hgh => hP _ _ fun G hG i => ?_⟩, ⟨fun g h hgh => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (Category.assoc _ _ _), ht (i ≫ h) (hgh.symm ▸ Category.assoc _ _ _)]
  · refine hP _ _ fun G hG i => ?_
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [Category.assoc, hgh, Category.assoc]

lemma IsDetecting.isIso_iff_of_mono (hP : IsDetecting P)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ ∀ (G : C) (_ : P G), Function.Surjective ((coyoneda.obj (op G)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f, h₁, h₂]

lemma IsCodetecting.isIso_iff_of_epi (hP : IsCodetecting P)
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsIso f ↔ ∀ (G : C) (_ : P G), Function.Surjective ((yoneda.obj G).map f.op) := by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f, h₁, h₂]

section

attribute [local instance] balanced_opposite

theorem IsCoseparating.isCodetecting [Balanced C] :
    IsCoseparating P → IsCodetecting P := by
  simpa only [← isDetecting_op_iff, ← isSeparating_op_iff] using IsSeparating.isDetecting

end

theorem isDetecting_iff_isSeparating [HasEqualizers C] [Balanced C] :
    IsDetecting P ↔ IsSeparating P :=
  ⟨IsDetecting.isSeparating, IsSeparating.isDetecting⟩

theorem isCodetecting_iff_isCoseparating [HasCoequalizers C] [Balanced C] :
    IsCodetecting P ↔ IsCoseparating P :=
  ⟨IsCodetecting.isCoseparating, IsCoseparating.isCodetecting⟩

section Mono

theorem IsSeparating.of_le (hP : IsSeparating P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsSeparating Q := fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _

theorem IsCoseparating.of_le (hP : IsCoseparating P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsCoseparating Q := fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _

theorem IsDetecting.of_le (hP : IsDetecting P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsDetecting Q := fun _ _ _ hf => hP _ fun _ hG _ => hf _ (h _ hG) _

theorem IsCodetecting.of_le (h𝒢 : IsCodetecting P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsCodetecting Q := fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h _ hG) _

end Mono

section Empty

lemma isThin_of_isSeparating_bot (h : IsSeparating (⊥ : ObjectProperty C)) :
    Quiver.IsThin C := fun _ _ ↦ ⟨fun _ _ ↦ h _ _ (by simp)⟩

lemma isSeparating_bot_of_isThin [Quiver.IsThin C] : IsSeparating (⊥ : ObjectProperty C) :=
  fun _ _ _ _ _ ↦ Subsingleton.elim _ _

lemma isThin_of_isCoseparating_bot (h : IsCoseparating (⊥ : ObjectProperty C)) :
    Quiver.IsThin C := fun _ _ ↦ ⟨fun _ _ ↦ h _ _ (by simp)⟩

lemma isCoseparating_bot_of_isThin [Quiver.IsThin C] : IsCoseparating (⊥ : ObjectProperty C) :=
  fun _ _ _ _ _ ↦ Subsingleton.elim _ _

lemma isGroupoid_of_isDetecting_bot (h : IsDetecting (⊥ : ObjectProperty C)) :
    IsGroupoid C where
  all_isIso f := h _ (by simp)

lemma isDetecting_bot_of_isGroupoid [IsGroupoid C] :
    IsDetecting (⊥ : ObjectProperty C) :=
  fun _ _ _ _ ↦ inferInstance

lemma isGroupoid_of_isCodetecting_bot (h : IsCodetecting (⊥ : ObjectProperty C)) :
    IsGroupoid C where
  all_isIso f := h _ (by simp)

lemma isCodetecting_bot_of_isGroupoid [IsGroupoid C] :
    IsCodetecting (⊥ : ObjectProperty C) :=
  fun _ _ _ _ ↦ inferInstance

end Empty

lemma IsSeparating.mk_of_exists_epi
    (hP : ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Cofan s) (_ : IsColimit c)
      (p : c.pt ⟶ X), Epi p) :
    P.IsSeparating := by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, p, _⟩ := hP X
  rw [← cancel_epi p]
  exact Cofan.IsColimit.hom_ext hc _ _
    (fun i ↦ by simpa using h _ (hs i) (c.inj i ≫ p))

lemma IsCoseparating.mk_of_exists_mono
    (hP : ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Fan s) (_ : IsLimit c)
      (j : X ⟶ c.pt), Mono j) :
    P.IsCoseparating := by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, j, _⟩ := hP Y
  rw [← cancel_mono j]
  exact Fan.IsLimit.hom_ext hc _ _
    (fun i ↦ by simpa using h _ (hs i) (j ≫ c.proj i))

lemma IsSeparating.mk_of_exists_colimitsOfShape
    (hP : ∀ (X : C), ∃ (J : Type w) (_ : Category.{w'} J), P.colimitsOfShape J X) :
    P.IsSeparating := by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP X
  exact p.isColimit.hom_ext (fun j ↦ h _ (p.prop_diag_obj _) _)

lemma IsCoseparating.mk_of_exists_limitsOfShape
    (hP : ∀ (X : C), ∃ (J : Type w) (_ : Category.{w'} J), P.limitsOfShape J X) :
    P.IsCoseparating := by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  exact p.isLimit.hom_ext (fun j ↦ h _ (p.prop_diag_obj _) _)

variable (P)

section

/-- Given `P : ObjectProperty C` and `X : C`, this is the map which
sends `i : CostructuredArrow P.ι X` to `i.left.obj : C`. The coproduct
of this family is the source of the morphism `P.coproductFrom X`. -/
abbrev coproductFromFamily (X : C) (i : CostructuredArrow P.ι X) : C := i.left.obj

variable (X : C)

variable [HasCoproduct (P.coproductFromFamily X)]

/-- Given `P : ObjectProperty C` and `X : C`, this is the coproduct of
all the morphisms `Y ⟶ X` such that `P Y` holds. -/
noncomputable abbrev coproductFrom : ∐ (P.coproductFromFamily X) ⟶ X :=
  Sigma.desc (fun i ↦ i.hom)

variable {X} in
/-- The inclusion morphisms to `∐ (P.coproductFromFamily X)`. -/
noncomputable abbrev ιCoproductFrom {Y : C} (f : Y ⟶ X) (hY : P Y) :
    Y ⟶ ∐ (P.coproductFromFamily X) := by
  exact Sigma.ι (P.coproductFromFamily X) (CostructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

end

set_option backward.isDefEq.respectTransparency false in
variable {P} in
lemma IsSeparating.epi_coproductFrom (hP : P.IsSeparating)
    (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    Epi (P.coproductFrom X) where
  left_cancellation u v huv :=
    hP _ _ (fun G hG h ↦ by simpa using P.ιCoproductFrom h hG ≫= huv)

theorem isSeparating_iff_epi
    [∀ (X : C), HasCoproduct (P.coproductFromFamily X)] :
    IsSeparating P ↔ ∀ X : C, Epi (P.coproductFrom X) :=
  ⟨fun hP X ↦ hP.epi_coproductFrom X,
    fun hP ↦ IsSeparating.mk_of_exists_epi (fun X ↦ ⟨_, P.coproductFromFamily X,
      fun i ↦ i.left.2, _, colimit.isColimit _, _, hP X⟩)⟩

section

/-- Given `P : ObjectProperty C` and `X : C`, this is the map which
sends `i : StructuredArrow P.ι X` to `i.right.obj : C`. The product
of this family is the target of the morphism `P.productTo X`. -/
abbrev productToFamily (X : C) (i : StructuredArrow X P.ι) : C := i.right.obj

variable (X : C)

variable [HasProduct (P.productToFamily X)]

/-- Given `P : ObjectProperty C` and `X : C`, this is the product of
all the morphisms `X ⟶ Y` such that `P Y` holds. -/
noncomputable abbrev productTo : X ⟶ ∏ᶜ (P.productToFamily X) :=
  Pi.lift (fun i ↦ i.hom)

variable {X} in
/-- The projection morphisms from `∏ᶜ (P.productToFamily X)`. -/
noncomputable abbrev πProductTo {Y : C} (f : X ⟶ Y) (hY : P Y) :
    ∏ᶜ (P.productToFamily X) ⟶ Y := by
  exact Pi.π (P.productToFamily X) (StructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

end

set_option backward.isDefEq.respectTransparency false in
variable {P} in
lemma IsCoseparating.mono_productTo (hP : P.IsCoseparating)
    (X : C) [HasProduct (P.productToFamily X)] :
    Mono (P.productTo X) where
  right_cancellation u v huv :=
    hP _ _ (fun G hG h ↦ by simpa using huv =≫ P.πProductTo h hG)

theorem isCoseparating_iff_mono
    [∀ (X : C), HasProduct (P.productToFamily X)] :
    IsCoseparating P ↔ ∀ X : C, Mono (P.productTo X) :=
  ⟨fun hP X ↦ hP.mono_productTo X,
    fun hP ↦ IsCoseparating.mk_of_exists_mono (fun X ↦ ⟨_, P.productToFamily X,
      fun i ↦ i.right.2, _, limit.isLimit _, _, hP X⟩)⟩

end ObjectProperty

/-- An ingredient of the proof of the Special Adjoint Functor Theorem: a complete well-powered
    category with a small coseparating set has an initial object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is already cocomplete,
    see `hasColimits_of_hasLimits_of_isCoseparating`. -/
theorem hasInitial_of_isCoseparating [LocallySmall.{w} C] [WellPowered.{w} C]
    [HasLimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (hP : P.IsCoseparating) : HasInitial C := by
  have := hasFiniteLimits_of_hasLimitsOfSize C
  haveI := hasProductsOfShape_of_small C (Subtype P)
  haveI := fun A => hasProductsOfShape_of_small.{w} C (StructuredArrow A P.ι)
  letI := completeLatticeOfCompleteSemilatticeInf (Subobject (piObj (Subtype.val : Subtype P → C)))
  suffices ∀ A : C, Unique (((⊥ : Subobject (piObj (Subtype.val : Subtype P → C))) : C) ⟶ A) by
    exact hasInitial_of_unique ((⊥ : Subobject (piObj (Subtype.val : Subtype P → C))) : C)
  have := hP.mono_productTo
  refine fun A => ⟨⟨?_⟩, fun f => ?_⟩
  · let s : ∏ᶜ (Subtype.val (p := P)) ⟶ ∏ᶜ P.productToFamily A :=
      Pi.lift (fun f ↦ Pi.π Subtype.val ⟨f.right.obj, f.right.property⟩)
    exact Subobject.ofLEMk _
      (pullback.fst _ _ : pullback s (P.productTo A) ⟶ _) bot_le ≫ pullback.snd _ _
  · suffices ∀ (g : Subobject.underlying.obj ⊥ ⟶ A), f = g by
      apply this
    intro g
    suffices IsSplitEpi (equalizer.ι f g) by exact eq_of_epi_equalizer
    exact IsSplitEpi.mk' ⟨Subobject.ofLEMk _ (equalizer.ι f g ≫ Subobject.arrow _) bot_le, by
      ext b
      have := Subobject.ofLEMk_comp (X := ⊥) (f := equalizer.ι f g ≫ (⊥ : Subobject _).arrow)
      simp [reassoc_of% this] ⟩

/-- An ingredient of the proof of the Special Adjoint Functor Theorem: a cocomplete well-copowered
    category with a small separating set has a terminal object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is already complete, see
    `hasLimits_of_hasColimits_of_isSeparating`. -/
theorem hasTerminal_of_isSeparating [LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ]
    [HasColimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (hP : P.IsSeparating) : HasTerminal C := by
  haveI : HasInitial Cᵒᵖ := hasInitial_of_isCoseparating (P.isCoseparating_op_iff.2 hP)
  exact hasTerminal_of_hasInitial_op

section WellPowered

namespace Subobject

theorem eq_of_le_of_isDetecting {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h₁ : P ≤ Q)
    (h₂ : ∀ (G : C) (_ : 𝒢 G), ∀ {f : G ⟶ X}, Q.Factors f → P.Factors f) : P = Q := by
  suffices IsIso (ofLE _ _ h₁) by exact le_antisymm h₁ (le_of_comm (inv (ofLE _ _ h₁)) (by simp))
  refine h𝒢 _ fun G hG f => ?_
  have : P.Factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩)
  refine ⟨factorThru _ _ this, ?_, fun g (hg : g ≫ _ = f) => ?_⟩
  · simp only [← cancel_mono Q.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  · simp only [← cancel_mono (Subobject.ofLE _ _ h₁), ← cancel_mono Q.arrow, hg, Category.assoc,
      ofLE_arrow, factorThru_arrow]

theorem inf_eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h : ∀ (G : C) (_ : 𝒢 G), ∀ {f : G ⟶ X}, P.Factors f → Q.Factors f) :
    P ⊓ Q = P :=
  eq_of_le_of_isDetecting h𝒢 _ _ _root_.inf_le_left
    fun _ hG _ hf => (inf_factors _).2 ⟨hf, h _ hG hf⟩

theorem eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h : ∀ (G : C) (_ : 𝒢 G),
      ∀ {f : G ⟶ X}, P.Factors f ↔ Q.Factors f) : P = Q :=
  calc
    P = P ⊓ Q := Eq.symm <| inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).1 hf
    _ = Q ⊓ P := inf_comm ..
    _ = Q := inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).2 hf

end Subobject

/-- A category with pullbacks and a small detecting set is well-powered. -/
theorem wellPowered_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C}
    [ObjectProperty.Small.{w} 𝒢] [LocallySmall.{w} C]
    (h𝒢 : 𝒢.IsDetecting) : WellPowered.{w} C where
  subobject_small X := small_of_injective
    (f := fun P : Subobject X => { f : Σ G : Subtype 𝒢, G.1 ⟶ X | P.Factors f.2 })
      fun P Q h => Subobject.eq_of_isDetecting h𝒢 _ _
        (by simpa [Set.ext_iff, Sigma.forall] using h)

end WellPowered

namespace StructuredArrow

variable (S : D) (T : C ⥤ D)

theorem isCoseparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsCoseparating) :
    (P.inverseImage (proj S T)).IsCoseparating := by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.right (hfg (mk (Y.hom ≫ T.map h)) hG (homMk h rfl))

end StructuredArrow

namespace CostructuredArrow

variable (S : C ⥤ D) (T : D)

theorem isSeparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsSeparating) :
    (P.inverseImage (proj S T)).IsSeparating := by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.left (hfg (mk (S.map h ≫ X.hom)) hG (homMk h rfl))

end CostructuredArrow

/-- We say that `G` is a separator if the functor `C(G, -)` is faithful. -/
def IsSeparator (G : C) : Prop :=
  ObjectProperty.IsSeparating (.singleton G)

/-- We say that `G` is a coseparator if the functor `C(-, G)` is faithful. -/
def IsCoseparator (G : C) : Prop :=
  ObjectProperty.IsCoseparating (.singleton G)

/-- We say that `G` is a detector if the functor `C(G, -)` reflects isomorphisms. -/
def IsDetector (G : C) : Prop :=
  ObjectProperty.IsDetecting (.singleton G)

/-- We say that `G` is a codetector if the functor `C(-, G)` reflects isomorphisms. -/
def IsCodetector (G : C) : Prop :=
  ObjectProperty.IsCodetecting (.singleton G)

section Equivalence

theorem IsSeparator.of_equivalence {G : C} (h : IsSeparator G) (α : C ≌ D) :
    IsSeparator (α.functor.obj G) := by
  simpa using ObjectProperty.IsSeparating.of_equivalence h α

theorem IsCoseparator.of_equivalence {G : C} (h : IsCoseparator G) (α : C ≌ D) :
    IsCoseparator (α.functor.obj G) := by
 simpa using ObjectProperty.IsCoseparating.of_equivalence h α

end Equivalence

section Dual

open ObjectProperty

theorem isSeparator_op_iff (G : C) : IsSeparator (op G) ↔ IsCoseparator G := by
  rw [IsSeparator, IsCoseparator, ← isSeparating_op_iff, op_singleton]

theorem isCoseparator_op_iff (G : C) : IsCoseparator (op G) ↔ IsSeparator G := by
  rw [IsSeparator, IsCoseparator, ← isCoseparating_op_iff, op_singleton]

theorem isCoseparator_unop_iff (G : Cᵒᵖ) : IsCoseparator (unop G) ↔ IsSeparator G := by
  rw [IsSeparator, IsCoseparator, ← isCoseparating_unop_iff, unop_singleton]

theorem isSeparator_unop_iff (G : Cᵒᵖ) : IsSeparator (unop G) ↔ IsCoseparator G := by
  rw [IsSeparator, IsCoseparator, ← isSeparating_unop_iff, unop_singleton]

theorem isDetector_op_iff (G : C) : IsDetector (op G) ↔ IsCodetector G := by
  rw [IsDetector, IsCodetector, ← isDetecting_op_iff, op_singleton]

theorem isCodetector_op_iff (G : C) : IsCodetector (op G) ↔ IsDetector G := by
  rw [IsDetector, IsCodetector, ← isCodetecting_op_iff, op_singleton]

theorem isCodetector_unop_iff (G : Cᵒᵖ) : IsCodetector (unop G) ↔ IsDetector G := by
  rw [IsDetector, IsCodetector, ← isCodetecting_unop_iff, unop_singleton]

theorem isDetector_unop_iff (G : Cᵒᵖ) : IsDetector (unop G) ↔ IsCodetector G := by
  rw [IsDetector, IsCodetector, ← isDetecting_unop_iff, unop_singleton]

end Dual

theorem IsDetector.isSeparator [HasEqualizers C] {G : C} : IsDetector G → IsSeparator G :=
  ObjectProperty.IsDetecting.isSeparating

theorem IsCodetector.isCoseparator [HasCoequalizers C] {G : C} : IsCodetector G → IsCoseparator G :=
  ObjectProperty.IsCodetecting.isCoseparating

theorem IsSeparator.isDetector [Balanced C] {G : C} : IsSeparator G → IsDetector G :=
  ObjectProperty.IsSeparating.isDetecting

theorem IsCoseparator.isCodetector [Balanced C] {G : C} : IsCoseparator G → IsCodetector G :=
  ObjectProperty.IsCoseparating.isCodetecting

theorem isSeparator_def (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

theorem IsSeparator.def {G : C} :
    IsSeparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  (isSeparator_def _).1

theorem isCoseparator_def (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

theorem IsCoseparator.def {G : C} :
    IsCoseparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  (isCoseparator_def _).1

theorem isDetector_def (G : C) :
    IsDetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

theorem IsDetector.def {G : C} :
    IsDetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  (isDetector_def _).1

theorem isCodetector_def (G : C) :
    IsCodetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

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

set_option backward.isDefEq.respectTransparency false in
theorem isSeparator_iff_epi (G : C) [∀ A : C, HasCoproduct fun _ : G ⟶ A => G] :
    IsSeparator G ↔ ∀ A : C, Epi (Sigma.desc fun f : G ⟶ A => f) := by
  rw [isSeparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι _ i ≫= huv
  · haveI := h X
    refine (cancel_epi (Sigma.desc fun f : G ⟶ X => f)).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
lemma isSeparator_of_isColimit_cofan {β : Type w} {f : β → C}
    (hf : ObjectProperty.IsSeparating (.ofObj f)) {c : Cofan f} (hc : IsColimit c) :
    IsSeparator c.pt := by
  rw [isSeparator_def]
  refine fun _ _ _ _ huv ↦ hf _ _ (fun _ h g ↦ ?_)
  obtain ⟨b⟩ := h
  classical simpa using c.inj b ≫= huv (hc.desc (Cofan.mk _ (Pi.single b g)))

lemma isSeparator_iff_of_isColimit_cofan {β : Type w} {f : β → C}
    {c : Cofan f} (hc : IsColimit c) :
    IsSeparator c.pt ↔ ObjectProperty.IsSeparating (.ofObj f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isSeparator_of_isColimit_cofan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using huv (f b.as) (by simp) (c.inj _ ≫ g)

theorem isSeparator_sigma {β : Type w} (f : β → C) [HasCoproduct f] :
    IsSeparator (∐ f) ↔ ObjectProperty.IsSeparating (.ofObj f) :=
  isSeparator_iff_of_isColimit_cofan (hc := colimit.isColimit _)

theorem isSeparator_coprod (G H : C) [HasBinaryCoproduct G H] :
    IsSeparator (G ⨿ H) ↔ ObjectProperty.IsSeparating (.pair G H) := by
  refine (isSeparator_iff_of_isColimit_cofan (coprodIsCoprod G H)).trans ?_
  convert Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

theorem isSeparator_coprod_of_isSeparator_left (G H : C) [HasBinaryCoproduct G H]
    (hG : IsSeparator G) : IsSeparator (G ⨿ H) :=
  (isSeparator_coprod _ _).2 <| ObjectProperty.IsSeparating.of_le hG <| by simp

theorem isSeparator_coprod_of_isSeparator_right (G H : C) [HasBinaryCoproduct G H]
    (hH : IsSeparator H) : IsSeparator (G ⨿ H) :=
  (isSeparator_coprod _ _).2 <| ObjectProperty.IsSeparating.of_le hH <| by simp

theorem ObjectProperty.IsSeparating.isSeparator_coproduct
    {β : Type w} {f : β → C} [HasCoproduct f]
    (hS : ObjectProperty.IsSeparating (.ofObj f)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 hS

theorem isSeparator_sigma_of_isSeparator {β : Type w} (f : β → C) [HasCoproduct f] (b : β)
    (hb : IsSeparator (f b)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 <| ObjectProperty.IsSeparating.of_le hb <| by simp

set_option backward.isDefEq.respectTransparency false in
lemma isCoseparator_of_isLimit_fan {β : Type w} {f : β → C}
    (hf : ObjectProperty.IsCoseparating (.ofObj f)) {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt := by
  rw [isCoseparator_def]
  refine fun _ _ _ _ huv ↦ hf _ _ (fun _ h g ↦ ?_)
  obtain ⟨b⟩ := h
  classical simpa using huv (hc.lift (Fan.mk _ (Pi.single b g))) =≫ c.proj b

lemma isCoseparator_iff_of_isLimit_fan {β : Type w} {f : β → C}
    {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt ↔ ObjectProperty.IsCoseparating (.ofObj f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isCoseparator_of_isLimit_fan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using huv (f b.as) (by simp) (g ≫ c.proj _)

theorem isCoseparator_pi {β : Type w} (f : β → C) [HasProduct f] :
    IsCoseparator (∏ᶜ f) ↔ ObjectProperty.IsCoseparating (.ofObj f) :=
  isCoseparator_iff_of_isLimit_fan (hc := limit.isLimit _)

theorem isCoseparator_prod (G H : C) [HasBinaryProduct G H] :
    IsCoseparator (G ⨯ H) ↔ ObjectProperty.IsCoseparating (.pair G H) := by
  refine (isCoseparator_iff_of_isLimit_fan (prodIsProd G H)).trans ?_
  convert Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

theorem isCoseparator_prod_of_isCoseparator_left (G H : C) [HasBinaryProduct G H]
    (hG : IsCoseparator G) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| ObjectProperty.IsCoseparating.of_le hG <| by simp

theorem isCoseparator_prod_of_isCoseparator_right (G H : C) [HasBinaryProduct G H]
    (hH : IsCoseparator H) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| ObjectProperty.IsCoseparating.of_le hH <| by simp

theorem isCoseparator_pi_of_isCoseparator {β : Type w} (f : β → C) [HasProduct f] (b : β)
    (hb : IsCoseparator (f b)) : IsCoseparator (∏ᶜ f) :=
  (isCoseparator_pi _).2 <| ObjectProperty.IsCoseparating.of_le hb <| by simp

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

@[deprecated (since := "2025-10-06")] alias IsSeparating := ObjectProperty.IsSeparating
@[deprecated (since := "2025-10-06")] alias IsCoseparating := ObjectProperty.IsCoseparating
@[deprecated (since := "2025-10-06")] alias IsDetecting := ObjectProperty.IsDetecting
@[deprecated (since := "2025-10-06")] alias IsCodetecting := ObjectProperty.IsCodetecting
@[deprecated (since := "2025-10-06")] alias IsSeparating.of_equivalence :=
  ObjectProperty.IsSeparating.of_equivalence
@[deprecated (since := "2025-10-06")] alias IsCoseparating.of_equivalence :=
  ObjectProperty.IsCoseparating.of_equivalence
@[deprecated (since := "2025-10-06")] alias isSeparating_op_iff :=
  ObjectProperty.isSeparating_op_iff
@[deprecated (since := "2025-10-06")] alias isCoseparating_op_iff :=
  ObjectProperty.isCoseparating_op_iff
@[deprecated (since := "2025-10-06")] alias isSeparating_unop_iff :=
  ObjectProperty.isSeparating_op_iff
@[deprecated (since := "2025-10-06")] alias isCoseparating_unop_iff :=
  ObjectProperty.isCoseparating_op_iff
@[deprecated (since := "2025-10-06")] alias isDetecting_op_iff :=
  ObjectProperty.isDetecting_op_iff
@[deprecated (since := "2025-10-06")] alias isCodetecting_op_iff :=
  ObjectProperty.isCodetecting_op_iff
@[deprecated (since := "2025-10-06")] alias isDetecting_unop_iff :=
  ObjectProperty.isDetecting_op_iff
@[deprecated (since := "2025-10-06")] alias isCodetecting_unop_iff :=
  ObjectProperty.isCodetecting_op_iff
@[deprecated (since := "2025-10-06")] alias IsDetecting.isSeparating :=
  ObjectProperty.IsDetecting.isSeparating
@[deprecated (since := "2025-10-06")] alias IsCodetecting.isCoseparating :=
  ObjectProperty.IsCodetecting.isCoseparating
@[deprecated (since := "2025-10-06")] alias IsSeparating.isDetecting :=
  ObjectProperty.IsSeparating.isDetecting
@[deprecated (since := "2025-10-06")] alias IsDetecting.isIso_iff_of_mono :=
  ObjectProperty.IsDetecting.isIso_iff_of_mono
@[deprecated (since := "2025-10-06")] alias IsCodetecting.isIso_iff_of_epi :=
  ObjectProperty.IsCodetecting.isIso_iff_of_epi
@[deprecated (since := "2025-10-06")] alias IsCoseparating.isCodetecting :=
  ObjectProperty.IsCoseparating.isCodetecting
@[deprecated (since := "2025-10-06")] alias isDetecting_iff_isSeparating :=
  ObjectProperty.isDetecting_iff_isSeparating
@[deprecated (since := "2025-10-06")] alias isCodetecting_iff_isCoseparating :=
  ObjectProperty.isCodetecting_iff_isCoseparating
@[deprecated (since := "2025-10-06")] alias IsSeparating.mono :=
  ObjectProperty.IsSeparating.of_le
@[deprecated (since := "2025-10-06")] alias IsCoseparating.mono :=
  ObjectProperty.IsCoseparating.of_le
@[deprecated (since := "2025-10-06")] alias IsDetecting.mono :=
  ObjectProperty.IsDetecting.of_le
@[deprecated (since := "2025-10-06")] alias IsCodetecting.mono :=
  ObjectProperty.IsCodetecting.of_le
@[deprecated (since := "2025-10-06")] alias thin_of_isSeparating_empty :=
  ObjectProperty.isThin_of_isSeparating_bot
@[deprecated (since := "2025-10-06")] alias isSeparating_empty_of_thin :=
  ObjectProperty.isSeparating_bot_of_isThin
@[deprecated (since := "2025-10-06")] alias thin_of_isCoseparating_empty :=
  ObjectProperty.isThin_of_isCoseparating_bot
@[deprecated (since := "2025-10-06")] alias isCoseparating_empty_of_thin :=
  ObjectProperty.isCoseparating_bot_of_isThin
@[deprecated (since := "2025-10-06")] alias groupoid_of_isDetecting_empty :=
  ObjectProperty.isGroupoid_of_isDetecting_bot
@[deprecated (since := "2025-10-06")] alias isDetecting_empty_of_groupoid :=
  ObjectProperty.isDetecting_bot_of_isGroupoid
@[deprecated (since := "2025-10-06")] alias groupoid_of_isCodetecting_empty :=
  ObjectProperty.isGroupoid_of_isCodetecting_bot
@[deprecated (since := "2025-10-06")] alias isCodetecting_empty_of_groupoid :=
  ObjectProperty.isCodetecting_bot_of_isGroupoid
@[deprecated (since := "2025-10-07")] alias isSeparating_iff_epi :=
  ObjectProperty.isSeparating_iff_epi
@[deprecated (since := "2025-10-07")] alias isCoseparating_iff_mono :=
  ObjectProperty.isCoseparating_iff_mono
@[deprecated (since := "2025-10-07")] alias IsSeparating.isSeparator_coproduct :=
  ObjectProperty.IsSeparating.isSeparator_coproduct
@[deprecated (since := "2025-10-07")] alias StructuredArrow.isCoseparating_proj_preimage :=
  StructuredArrow.isCoseparating_inverseImage_proj
@[deprecated (since := "2025-10-07")] alias CostructuredArrow.isSeparating_proj_preimage :=
  CostructuredArrow.isSeparating_inverseImage_proj

end CategoryTheory
