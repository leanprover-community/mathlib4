/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Subobject.Classifier.Defs
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!

# (Elementary) Sheaf Topos

We define a subobject classifier for categories of sheaves of (large enough) types.

## Main definitions

Let `C` refer to a category with (when relevant) Grothendieck topology `J`.

* `Presheaf.classifier C` is a construction of a subobject classifier in `Cᵒᵖ ⥤ Type (max u v)`.
* `Sheaf.classifier J` is a construction of a subobject classifier in `Sheaf J (Type (max u v))`.
* `inferInstance : HasClassifier (Cᵒᵖ ⥤ Type w)` says that `Cᵒᵖ ⥤ Type w` has a subobject
  classifier if `C` is `w`-essentially small.
* `inferInstance : HasClassifier (Sheaf J (Type w))` says that `Sheaf J (Type w)` has a
  subobject classifier if `C` is `w`-essentially small.

## Main results

* Any category of sheaves of types has a subobject classifier if the site is essentially small.
* As a consequence, (because categories of sheaves are cartesian monoidal and have finite limits,)
  such categories are Elementary Topoi.

## TODOS:

* generalize `Presheaf.isClosed_χ_app_apply_of` to only assuming `G` is separated

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
open Limits

section presheaf

variable (C) in
/-- The truth morphism in the category of presheaves. At each component `X : C`, it is the constant
map returning `⊤ : Sieve X`. -/
@[simps]
def Presheaf.truth : (Functor.const _).obj PUnit ⟶ Functor.sieves C where
  app X _ := (⊤ : Sieve X.unop)

variable {F G : Cᵒᵖ ⥤ Type (max u v)}

/--
The characteristic map of an inclusion of presheaves.
Given a monomorphism of sheaves `m : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  `∃ a ∈ F(Y), G(f)(x) = m_Y(a)`
-/
@[simps app]
def Presheaf.χ (m : F ⟶ G) : G ⟶ Functor.sieves C where
  app X x := ⟨fun Y f => ∃ a, G.map f.op x = m.app (.op Y) a, by
    intro Y Z f ⟨a, ha⟩ g
    use F.map g.op a
    simp [ha, FunctorToTypes.naturality]⟩

lemma Presheaf.comp_χ_eq (m : F ⟶ G) : m ≫ Presheaf.χ m =
    (Functor.isTerminalConst _ Types.isTerminalPUnit).from F ≫ Presheaf.truth C := by
  ext
  apply Sieve.ext
  simp [← FunctorToTypes.naturality F G m]

lemma Presheaf.isPullback_χ_truth (m : F ⟶ G) [Mono m] :
    IsPullback m ((Functor.isTerminalConst _ Types.isTerminalPUnit).from F) (χ m) (truth C) := by
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr(($(comp_χ_eq m)).app X), ?_, ?_⟩
  · simpa using (mono_iff_injective (m.app X)).mp (inferInstance)
  · simp only [Functor.const_obj_obj, Functor.sieves_obj, χ_app, Opposite.op_unop, truth_app,
    Functor.isTerminalConst_from_app, Types.isTerminalPUnit_from_apply, and_true, forall_const]
    intro p hp
    simpa [eq_comm] using congr($(hp).arrows (𝟙 _))

lemma Presheaf.χ_unique (m : F ⟶ G) (χ' : G ⟶ Functor.sieves C)
    (hχ' : IsPullback m ((Functor.isTerminalConst _ Types.isTerminalPUnit).from _) χ' (truth C)) :
    χ' = χ m := by
  ext X x
  simp only [IsPullback.iff_app, Functor.const_obj_obj, Functor.sieves_obj,
    Functor.isTerminalConst_from_app, Types.isPullback_iff, and_true, truth_app, forall_const,
    forall_and] at hχ'
  obtain ⟨h₁, h₂, h₃⟩ := hχ'
  refine Sieve.ext fun Y f => ?_
  simp only [χ_app, Opposite.op_unop]
  rw [Sieve.mem_iff_pullback_eq_top, ← Quiver.Hom.unop_op f,
    ← Functor.sieves_map C (f.op) (χ'.app X x),
    ← FunctorToTypes.naturality G (Functor.sieves C) χ' f.op x, Quiver.Hom.unop_op]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h₃ _ _ h
    use z, hz.symm
  · rintro ⟨a, h⟩
    rw [h, ← FunctorToTypes.comp, NatTrans.comp_app]
    simpa using congr($(h₁ (.op Y)) a)

variable (C) in
/-- A construction of a subject classifier in a category of presheaves. -/
@[simps! Ω truth Ω₀ χ χ₀]
def Presheaf.classifier : Subobject.Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  .mkOfTerminalΩ₀ ((Functor.const Cᵒᵖ).obj PUnit)
    (Functor.isTerminalConst _ (Types.isTerminalPUnit)) (Functor.sieves C) (Presheaf.truth C)
    (Presheaf.χ ·) Presheaf.isPullback_χ_truth (Presheaf.χ_unique ·)

/-- Presheaf categories on an essentially small domain have a subobject classifier. -/
instance [EssentiallySmall.{w} C] : HasSubobjectClassifier (Cᵒᵖ ⥤ Type w) where
  exists_classifier := ⟨(Presheaf.classifier (SmallModel C)).ofEquivalence
    (Equivalence.congrLeft (E := Type w) (equivSmallModel C).op).symm⟩

end presheaf

variable {J : GrothendieckTopology C}

open Presheaf in
lemma GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated
    {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) [Mono m] (hF : Presieve.IsSheaf J F)
    (hG : Presieve.IsSeparated J G) (X : Cᵒᵖ) (x : G.obj X) :
    J.IsClosed ((Presheaf.χ m).app X x) := by
  intro Y f hf
  simp only [Presheaf.χ_app, Opposite.op_unop] at hf ⊢
  choose a ha using fun Z (g : Z ⟶ Y) (hg : (Sieve.pullback f ((χ m).app X x)).arrows g) => hg
  refine ⟨(hF _ hf).amalgamate a ?_, ?_⟩
  · introv Y₁ h
    apply (mono_iff_injective (m.app (.op Z))).mp inferInstance
    simp_rw [FunctorToTypes.naturality, ← ha, ← FunctorToTypes.map_comp_apply, ← op_comp,
      reassoc_of% h]
  · refine (hG _ hf).ext fun Z f' hf' => ?_
    rw [← FunctorToTypes.naturality, (hF _ hf).valid_glue _ _ hf', ← (ha _ _ _),
      op_comp, FunctorToTypes.map_comp_apply]

namespace Sheaf
open Functor
variable {F G : Sheaf J (Type max u v)}

/-- The sheaf of closed sieves w/r/t `J`. See also `Functor.closedSieves` and `Sheaf.classifier` -/
@[simps]
def Ω (J : GrothendieckTopology C) : Sheaf J (Type max u v) where
  obj := (Functor.closedSieves J).toFunctor
  property := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `t : 1 ⟶ Ω` which picks out the maximal sieve -/
@[simps]
def truth (J : GrothendieckTopology C) :
    Sheaf.terminal J (Types.isTerminalPUnit) ⟶ Sheaf.Ω J where
  hom := (Functor.closedSieves J).lift (Presheaf.truth C) fun {X} x => by cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
Given a monomorphism of sheaves `η : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  `∃ a ∈ F(Y), G(f)(x) = η_Y(a)`
-/
@[simps]
def χ (m : F ⟶ G) [Mono m] : G ⟶ Sheaf.Ω J where
  hom := (closedSieves J).lift (Presheaf.χ m.hom) (by
    intro X
    simp only [sieves_obj, Subfunctor.range_obj, closedSieves_obj, Set.le_iff_subset,
      Set.range_subset_iff, Set.mem_setOf_eq]
    exact J.isClosed_χ_app_apply_of_isSheaf_of_isSeparated m.hom
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)
      ((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated _)

lemma isPullback_χ_truth (m : F ⟶ G) [Mono m] :
    IsPullback m ((isTerminalTerminal J _).from F) (Sheaf.χ m) (Sheaf.truth J) := by
  apply IsPullback.of_map (sheafToPresheaf J _)
  · ext : 1
    simp only [Ω_obj, ObjectProperty.FullSubcategory.comp_hom, χ_hom, terminal_obj, truth_hom,
      ← cancel_mono (closedSieves J).ι, Category.assoc, Subfunctor.lift_ι]
    exact Presheaf.comp_χ_eq m.hom
  · simp only [ObjectProperty.ι_obj, terminal_obj, Ω_obj, ObjectProperty.ι_map, χ_hom, truth_hom]
    apply IsPullback.of_right _
      ((cancel_mono ((closedSieves J).ι)).mp (by simpa using Presheaf.comp_χ_eq _))
      (.of_horiz_isIso_mono ⟨_⟩ : IsPullback (𝟙 _) _ (Presheaf.χ m.hom) (closedSieves J).ι)
    · simp only [Category.comp_id]
      exact Presheaf.isPullback_χ_truth m.hom
    · simp_all

set_option backward.isDefEq.respectTransparency false in
lemma χ_unique (m : F ⟶ G) [Mono m] (χ' : G ⟶ Sheaf.Ω J)
    (hχ' : IsPullback m ((isTerminalTerminal J _).from F) χ' (Sheaf.truth J)) :
    χ' = Sheaf.χ m := by
  ext : 1
  rw [← cancel_mono (closedSieves J).ι,χ_hom, Subfunctor.lift_ι]
  apply Presheaf.χ_unique _
  have pb : IsPullback (𝟙 G.obj) χ'.hom (χ'.hom ≫ (closedSieves J).ι)
    (closedSieves J).ι := IsPullback.of_horiz_isIso_mono (by simp)
  have : IsPullback m.hom ?_ χ'.hom <| (truth J).hom := by
    simpa using hχ'.map (sheafToPresheaf J _)
  simpa using this.paste_horiz pb

/--
A construction of a subobject classifier for sheaf categories. `Ω` is the sheaf of closed sieves,
and `truth` maps for each object `X : C`, an element of `PUnit` to the maximal `Sieve X`, which is
always closed.
-/
@[simps! Ω truth Ω₀ χ χ₀]
def classifier (J : GrothendieckTopology C) : Subobject.Classifier (Sheaf J (Type max u v)) :=
  .mkOfTerminalΩ₀ (.terminal J Types.isTerminalPUnit) (isTerminalTerminal _ _) (Sheaf.Ω J)
    (Sheaf.truth J) Sheaf.χ Sheaf.isPullback_χ_truth Sheaf.χ_unique

/-- Sheaf categories on essentially small sites have a subobject classifier. -/
instance [EssentiallySmall.{w} C] : HasSubobjectClassifier (Sheaf J (Type w)) where
  exists_classifier := ⟨Sheaf.classifier ((equivSmallModel C).inverse.inducedTopology J)
    |>.ofEquivalence (Equivalence.sheafCongr _ _ (equivSmallModel C) _).symm⟩

end Sheaf

end CategoryTheory

end
