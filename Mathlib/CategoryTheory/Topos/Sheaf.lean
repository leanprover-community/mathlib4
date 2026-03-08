/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Topos.Classifier

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
/--
The presheaf sending each object to the set of sieves on it.
This presheaf will turn out to be a subobject classifier for the category of presheaves -/
@[simps]
def Functor.sieves : Cᵒᵖ ⥤ Type (max u v) where
  obj X := Sieve X.unop
  map f := fun s => s.pullback f.unop

/-- The natural inclusion of the `Functor.closedSieves` presheaf in the `Functor.sieves` presheaf -/
@[simps]
def Functor.closedSievesInclusion (J : GrothendieckTopology C) :
    Functor.closedSieves J ⟶ Functor.sieves C where
  app X := Subtype.val

instance {J : GrothendieckTopology C} : Mono (Functor.closedSievesInclusion J) := by
  simp [NatTrans.mono_iff_mono_app, mono_iff_injective, Functor.closedSievesInclusion]

/-- Given a natural transformation into `Functor.sieves`, it factors through `Functor.closedSieves`
when at each component `X : C`, the range is contained in `{s : Sieve X | J.IsClosed s}`. -/
@[simps app]
def Functor.closedSievesFactorization (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type (max u v)}
    (f : F ⟶ Functor.sieves C)
    (hf : ∀ ⦃X : Cᵒᵖ⦄ (x : F.obj X), J.IsClosed (f.app X x)) : F ⟶ Functor.closedSieves J where
  app X x := ⟨f.app X x, hf x⟩
  naturality {X Y} g := by
    dsimp
    ext
    simp [FunctorToTypes.naturality]

@[reassoc (attr := simp)]
lemma Functor.closedSievesFactorization_comp_closedSievesInclusion (J : GrothendieckTopology C)
    {F : Cᵒᵖ ⥤ Type (max u v)} (f : F ⟶ Functor.sieves C)
    (hf : ∀ (X : Cᵒᵖ) (x : F.obj X), J.IsClosed (f.app X x)) :
    closedSievesFactorization J f hf ≫ closedSievesInclusion J = f := by
  ext
  simp

variable (C) in
/-- The truth morphism in the category of presheaves. At each component `X : C`, it is the constant
map returning `⊤ : Sieve X`. -/
@[simps]
def Presheaf.truth : Functor.terminal _ (Types.isTerminalPUnit) ⟶ Functor.sieves C where
  app X _ := (⊤ : Sieve X.unop)

/--
The characteristic map of an inclusion of presheaves.
Given a monomorphism of sheaves `m : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  `∃ a ∈ F(Y), G(f)(x) = m_Y(a)`
-/
@[simps app]
def Presheaf.χ {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) :
    G ⟶ Functor.sieves C where
  app X x := ⟨fun Y f => ∃ a, G.map f.op x = m.app (.op Y) a, by
    intro Y Z f ⟨a, ha⟩ g
    use F.map g.op a
    simp [ha, FunctorToTypes.naturality]⟩

lemma Presheaf.comp_χ_eq {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) :
    m ≫ Presheaf.χ m = (Functor.isTerminalTerminal _ Types.isTerminalPUnit).from F ≫
      Presheaf.truth C := by
  ext
  apply Sieve.ext
  simp [← FunctorToTypes.naturality F G m]

lemma Presheaf.isPullback_χ_truth {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) [Mono m] :
    IsPullback m ((Functor.isTerminalTerminal _ Types.isTerminalPUnit).from F)
      (χ m) (truth C) := by
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr(($(comp_χ_eq m)).app X), ?_, ?_⟩
  · simpa using (mono_iff_injective (m.app X)).mp (inferInstance)
  · simp only [Functor.terminal_obj, Functor.sieves_obj, χ_app, Opposite.op_unop, truth_app,
      Functor.isTerminalTerminal_from_app, and_true, forall_const]
    intro p hp
    simpa [eq_comm] using congr($(hp).arrows (𝟙 _))

lemma Presheaf.χ_unique {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) (χ' : G ⟶ Functor.sieves C)
    (hχ' : IsPullback m ((Functor.isTerminalTerminal _ _).from _) χ' (truth C)) : χ' = χ m := by
  ext X x
  simp only [IsPullback.iff_app, Functor.terminal_obj, Functor.sieves_obj,
    Functor.isTerminalTerminal_from_app, Types.isPullback_iff, Types.isTerminalPUnit_from_apply,
    and_true, truth_app, forall_const, forall_and] at hχ'
  obtain ⟨h₁, h₂, h₃⟩ := hχ'
  refine Sieve.ext fun Y f => ?_
  simp only [χ_app, Opposite.op_unop]
  rw [Sieve.mem_iff_pullback_eq_top,← Quiver.Hom.unop_op f,
    ← Functor.sieves_map C (f.op) (χ'.app X x),
    ← FunctorToTypes.naturality G (Functor.sieves C) χ' f.op x, Quiver.Hom.unop_op]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h₃ _ _ h
    use z, hz.symm
  · rintro ⟨a, h⟩
    rw [h,← FunctorToTypes.comp, NatTrans.comp_app]
    simpa using congr($(h₁ (.op Y)) a)

-- note: the argument `hG` uses `Presieve.IsSeparated` rather than `Presheaf.IsSeparated`,
-- for lack of API relating them
lemma Presheaf.isClosed_χ_app_apply_of_isSheaf_of_isSeparated (J : GrothendieckTopology C)
    {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) [Mono m] (hF : IsSheaf J F)
    (hG : Presieve.IsSeparated J G) (X : Cᵒᵖ) (x : G.obj X) :
    J.IsClosed ((Presheaf.χ m).app X x) := by
  intro Y f hf
  simp only [χ_app, Opposite.op_unop]
  refine ⟨(hF.isSheafFor _ hf).amalgamate (fun Z g hg => hg.choose) ?_, ?_⟩
  · introv Y₁ h
    simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
    have : (m.app (.op Z)).Injective := by
      rw [← mono_iff_injective]
      infer_instance
    apply this
    simp_rw [FunctorToTypes.naturality]
    generalize_proofs h1 h2
    rw [← h1.choose_spec,← h2.choose_spec]
    simp_rw [← FunctorToTypes.map_comp_apply,← op_comp, reassoc_of% h]
  · simp only [χ_app, Opposite.op_unop, Sieve.pullback_apply, op_comp,
      FunctorToTypes.map_comp_apply]
    refine (hG _ hf).ext (fun Z f' hf' => ?_)
    generalize_proofs h1 h2 h3
    rw [← FunctorToTypes.naturality, h2.valid_glue _ _ hf',← (h3 _ _ _).choose_spec]
    exact hf'

variable (C) in
/-- A construction of a subject classifier in a category of presheaves. -/
@[simps! Ω truth Ω₀ χ χ₀]
def Presheaf.classifier : Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  .mkOfTerminalΩ₀ (Functor.terminal _ (Types.isTerminalPUnit))
    (Functor.isTerminalTerminal _ (Types.isTerminalPUnit)) (Functor.sieves C) (Presheaf.truth C)
    (Presheaf.χ ·) Presheaf.isPullback_χ_truth (Presheaf.χ_unique ·)

/-- Presheaf categories on an essentially small domain have a subobject classifier. -/
instance [EssentiallySmall.{w} C] : HasClassifier (Cᵒᵖ ⥤ Type w) where
  exists_classifier := ⟨(Presheaf.classifier (SmallModel C)).ofEquivalence
    (Equivalence.congrLeft (E := Type w) (equivSmallModel C).op).symm⟩

end presheaf

section sheaf
open Functor

/-- The sheaf of closed sieves w/r/t `J`. See also `Functor.closedSieves` and `Sheaf.classifier` -/
@[simps]
def Sheaf.Ω {J : GrothendieckTopology C} : Sheaf J (Type max u v) where
  obj := .closedSieves J
  property := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

/-- The morphism `t : 1 ⟶ Ω` which picks out the maximal sieve -/
@[simps]
def Sheaf.truth {J : GrothendieckTopology C} :
    Sheaf.terminal J (Types.isTerminalPUnit) ⟶ Sheaf.Ω where
  hom := closedSievesFactorization J (Presheaf.truth C) (fun {X} x => by cat_disch)

/--
Given a monomorphism of sheaves `η : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  ∃ a ∈ F(Y), G(f)(x) = η_Y(a)
-/
@[simps]
def Sheaf.χ {J : GrothendieckTopology C} {F G : Sheaf J (Type max u v)} (m : F ⟶ G) [Mono m] :
    G ⟶ Sheaf.Ω where
  hom := closedSievesFactorization J (Presheaf.χ m.hom)
    (Presheaf.isClosed_χ_app_apply_of_isSheaf_of_isSeparated J m.hom F.property
      ((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated)

lemma Sheaf.isPullback_χ_truth {J : GrothendieckTopology C} {F G : Sheaf J (Type max u v)}
    (m : F ⟶ G) [Mono m] : IsPullback m ((isTerminalTerminal J _).from F) (Sheaf.χ m)
      (Sheaf.truth) := by
  apply IsPullback.of_map (sheafToPresheaf J _)
  · ext : 1
    simp only [Ω_obj, ObjectProperty.FullSubcategory.comp_hom, χ_hom, terminal_obj, truth_hom,
      ← cancel_mono (closedSievesInclusion J), Category.assoc]
    rw [closedSievesFactorization_comp_closedSievesInclusion J (Presheaf.χ m.hom)]
    exact Presheaf.comp_χ_eq m.hom
  · rw [sheafToPresheaf, ObjectProperty.ι_map]
    simp only [ObjectProperty.ι_obj, terminal_obj, Ω_obj, ObjectProperty.ι_map, χ_hom, truth_hom]
    apply IsPullback.of_right _
      ((cancel_mono (closedSievesInclusion _)).mp (by simpa using Presheaf.comp_χ_eq _))
      (.of_horiz_isIso_mono ⟨_⟩ : IsPullback (𝟙 _) _ (Presheaf.χ m.hom) (closedSievesInclusion J))
    · simp only [Category.comp_id, closedSievesFactorization_comp_closedSievesInclusion]
      exact Presheaf.isPullback_χ_truth m.hom
    · simp_all [closedSievesFactorization_comp_closedSievesInclusion]

lemma Sheaf.χ_unique {J : GrothendieckTopology C} {F G : Sheaf J (Type max u v)} (m : F ⟶ G)
    [Mono m] (χ' : G ⟶ Sheaf.Ω)
    (hχ' : IsPullback m ((isTerminalTerminal J _).from F) χ' (Sheaf.truth)) :
    χ' = Sheaf.χ m := by
  ext : 1
  apply (cancel_mono (closedSievesInclusion J)).mp
  simp only [χ_hom, closedSievesFactorization_comp_closedSievesInclusion]
  apply Presheaf.χ_unique _
  · have pb : IsPullback (𝟙 G.obj) χ'.hom (χ'.hom ≫ closedSievesInclusion J)
      (closedSievesInclusion J) := @IsPullback.of_horiz_isIso_mono
        _ _ _ _ _ _ _ _ _ _ _ (inferInstanceAs (Mono (closedSievesInclusion J))) (by simp)
    have : IsPullback m.hom ?_ χ'.hom (truth.hom) := by
      simpa using hχ'.map (sheafToPresheaf J _)
    simpa using this.paste_horiz pb

/--
A construction of a subobject classifier for sheaf categories. `Ω` is the sheaf of closed sieves,
and `truth` maps for each object `X : C`, an element of `PUnit` to the maximal `Sieve X`, which is
always closed.
-/
@[simps! Ω truth Ω₀ χ χ₀]
def Sheaf.classifier (J : GrothendieckTopology C) :
    Classifier (Sheaf J (Type max u v)) :=
  .mkOfTerminalΩ₀ (.terminal J Types.isTerminalPUnit) (isTerminalTerminal _ _) Sheaf.Ω
    Sheaf.truth Sheaf.χ Sheaf.isPullback_χ_truth Sheaf.χ_unique

/-- Sheaf categories on essentially small sites have a subobject classifier. -/
instance [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    HasClassifier (Sheaf J (Type w)) where
  exists_classifier := ⟨Sheaf.classifier ((equivSmallModel C).inverse.inducedTopology J)
    |>.ofEquivalence (Equivalence.sheafCongr _ _ (equivSmallModel C) _).symm⟩
end sheaf

end CategoryTheory

end
