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

Let `C` refer to a category with (when relevant) grothendieck topology `J`.

* `Presheaf.classifier C` is a construction of a subobject classifier in `Cᵒᵖ ⥤ (Type (max u v))`.

* `Sheaf.classifier J` is a construction of a subobject classifier in `Sheaf J (Type (max u v))`.

* `HasClassifier.instPresheaf C` says that `Cᵒᵖ ⥤ (Type (max u v))` has a subobject classifier.

* `Sheaf.instHasClassifier J` says that `Sheaf J (Type (max u v))` has a subobject classifier.

## Main results

* Any category of sheaves of (large enough) types has a subobject classifier.

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

/-- The natural inclusion of the `closedSieves` presheaf in the `sieves` presheaf -/
@[simps]
def closedSievesInclusion (J : GrothendieckTopology C) :
    Functor.closedSieves J ⟶ Functor.sieves C where
  app X := Subtype.val

instance {J : GrothendieckTopology C} : Mono (closedSievesInclusion J) := by
  refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ ?_
  intro X
  rw [mono_iff_injective]
  exact Subtype.val_injective

/-- given a natural transformation into `sieves`, it factors through `closedSieves` when at each
component `X : Cᵒᵖ`, the range lands within {s : Sieve X.unop | J.IsClosed s} -/
@[simps]
def closedSievesFactorization (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type (max u v)}
    (f : F ⟶ Functor.sieves C)
    (hf : ∀ ⦃X : Cᵒᵖ⦄ (x : F.obj X), J.IsClosed (f.app X x)) : F ⟶ Functor.closedSieves J where
  app X := fun x => ⟨f.app X x, hf x⟩
  naturality := by
    intro X Y g
    ext x
    simp only [Functor.closedSieves_obj, types_comp_apply]
    ext : 1
    simpa using (FunctorToTypes.naturality _ _ f g x)

@[reassoc (attr := simp)]
lemma closedSievesFactorization_comp_closedSievesInclusion (J : GrothendieckTopology C)
    {F : Cᵒᵖ ⥤ Type (max u v)} (f : F ⟶ Functor.sieves C)
    (hf : ∀ (X : Cᵒᵖ) (x : F.obj X), J.IsClosed (f.app X x)) :
    closedSievesFactorization J f hf ≫ closedSievesInclusion J = f := by
  ext X x
  simp

variable (C) in
/-- The truth morphism in the category of presheaves. At each component `X : C`, it is the constant
map returning `⊤ : Sieve X.unop`. -/
@[simps]
def Presheaf.truth : ((CategoryTheory.Functor.const _).obj PUnit) ⟶ Functor.sieves C where
  app X := fun _ => (⊤ : Sieve X.unop)

/--
The characteristic map of an inclusion of presheaves.
Given a monomorphism of sheaves `η : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  "∃ a ∈ F(Y), G(f)(x) = η_Y(a)"
-/
@[simps]
def Presheaf.χ {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) :
    G ⟶ Functor.sieves C where
  app X := fun x => ⟨fun Y f => ∃ a, (G.map f.op) x = m.app (.op Y) a, by
    intro Y Z f ⟨a,ha⟩ g
    simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
    rw [ha]
    use F.map g.op a
    rw [FunctorToTypes.naturality]⟩

lemma Presheaf.comp_χ_eq {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) :
    m ≫ Presheaf.χ m = ({app X := fun _ => PUnit.unit} : F ⟶ _) ≫ Presheaf.truth C := by
  ext X x
  simp only [Functor.sieves_obj, FunctorToTypes.comp]
  apply Sieve.ext
  simp [← FunctorToTypes.naturality F G m]

lemma Presheaf.classifier_isPullback {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) [Mono m] :
    IsPullback m ({app X := fun _ => PUnit.unit}) (χ m) (truth C) := by
  apply IsPullback.of_forall_isPullback_app
  intro X
  rw [Types.isPullback_iff]
  constructorm* _ ∧ _
  · simpa using congr(($(comp_χ_eq m)).app X)
  · simp only [and_true]
    exact (mono_iff_injective _).mp inferInstance
  · simp only [Functor.const_obj_obj, Functor.sieves_obj, truth_app, and_true, forall_const]
    intro p hp
    simp_rw [eq_comm]
    simpa using congr($(hp).arrows (𝟙 _))

lemma Presheaf.χ_unique {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G)
    {χ₀' : F ⟶ ((Functor.const _).obj PUnit)} (χ' : G ⟶ Functor.sieves C) :
    IsPullback m χ₀' χ' (truth C) → χ' = χ m := by
  intro h
  ext X x
  have h' (Y : Cᵒᵖ) : IsPullback (m.app Y) (fun _ => PUnit.unit) (χ'.app Y) ((truth C).app Y) := by
    simpa using h.app Y
  simp_rw [Types.isPullback_iff] at h'
  simp only [Functor.sieves_obj, and_true, truth_app, forall_const, forall_and] at h'
  obtain ⟨h₁,h₂,h₃⟩ := h'
  apply Sieve.ext
  intro Y f
  simp only [χ_app_apply, Opposite.op_unop]
  rw [Sieve.mem_iff_pullback_eq_top,← Quiver.Hom.unop_op f,
    ← Functor.sieves_map C (f.op) (χ'.app X x),
    ← FunctorToTypes.naturality G (Functor.sieves C) χ' f.op x,Quiver.Hom.unop_op]
  constructor
  · intro h
    obtain ⟨z,hz⟩:= h₃ _ _ h
    use z, hz.symm
  · rintro ⟨a,h⟩
    rw [h, ← FunctorToTypes.comp, NatTrans.comp_app]
    simpa using congr($(h₁ (.op Y)) a)

-- TODO: weaken `hG` to `Presieve.IsSeparated J G` (or Presheaf.IsSeparated, if possible)
lemma Presheaf.isClosed_χ_app_apply_of (J : GrothendieckTopology C)
    {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) [Mono m]
    (hF : IsSheaf J F) (hG : IsSheaf J G) :
    ∀ ⦃X : Cᵒᵖ⦄ (x : G.obj X), J.IsClosed ((Presheaf.χ m).app X x) := by
  intro X x Y f hf
  simp only [χ_app_apply, Opposite.op_unop]
  have foo : Presieve.IsSheafFor F (((χ m).app X x).pullback f).arrows := by
    exact hF.isSheafFor _ hf
  have foo₂ : Presieve.IsSheafFor G (((χ m).app X x).pullback f).arrows := by
    exact hG.isSheafFor _ hf
  refine ⟨?_,?_⟩
  · refine foo.amalgamate (fun Z g hg => hg.choose) ?_
    introv Y₁ h
    simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
    have : (m.app (.op Z)).Injective := by
      rw [← mono_iff_injective]
      infer_instance
    apply this
    simp_rw [FunctorToTypes.naturality]
    generalize_proofs h1 h2
    rw [← h1.choose_spec, ← h2.choose_spec]
    simp_rw [← FunctorToTypes.map_comp_apply, ← op_comp,reassoc_of% h]
  · simp only [Sieve.pullback_apply, Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
    generalize_proofs h1 h2 h3
    refine (foo₂.isSeparatedFor).ext ?_
    intro Z f' hf'
    rw [← FunctorToTypes.naturality, foo.valid_glue _ _ hf', ← (h1 _ _ _).choose_spec]
    exact hf'

variable (C) in
/-- A construction of a subject classifier in a category of presheaves. -/
@[simps! Ω truth Ω₀ χ χ₀]
def Presheaf.classifier : Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  .mkOfTerminalΩ₀ ((Functor.const _).obj PUnit)
    (.ofUniqueHom (fun _ => {app _ := fun _ => .unit}) (by aesop)) (Functor.sieves C)
    (Presheaf.truth C) (Presheaf.χ ·) Presheaf.classifier_isPullback
      (Presheaf.χ_unique ·)

/-- Sheaf categories have a subobject classifier. -/
instance HasClassifier.instPresheaf [EssentiallySmall.{w} C] : HasClassifier (Cᵒᵖ ⥤ Type w) where
  exists_classifier := ⟨(Presheaf.classifier (SmallModel C)).ofEquivalence
    (Equivalence.congrLeft (E := Type w) (equivSmallModel C).op).symm⟩

end presheaf

section sheaf

/-- The sheaf of closed sieves w/r/t `J`. See also `Functor.closedSieves` -/
@[simps obj]
def Sheaf.Ω {J : GrothendieckTopology C} : Sheaf J (Type (max u v)) where
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
def Sheaf.χ {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G) [Mono m] :
    G ⟶ Sheaf.Ω where
  hom := closedSievesFactorization J (Presheaf.χ m.hom)
    (Presheaf.isClosed_χ_app_apply_of J m.hom F.property G.property)

lemma Sheaf.classifier_isPullback {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))}
    (m : F ⟶ G) [Mono m] : IsPullback m ((Sheaf.terminal_isTerminal J _).from F) (Sheaf.χ m)
      (Sheaf.truth) := by
  apply IsPullback.of_map (sheafToPresheaf J _)
  · ext : 1
    simp only [Ω_obj, ObjectProperty.FullSubcategory.comp_hom, χ_hom, terminal_obj, truth_hom,
      ← cancel_mono (closedSievesInclusion J), Category.assoc]
    rw [closedSievesFactorization_comp_closedSievesInclusion J (Presheaf.χ m.hom)]
    exact Presheaf.comp_χ_eq m.hom
  · rw [sheafToPresheaf,ObjectProperty.ι_map]
    simp only [ObjectProperty.ι_obj, terminal_obj, Ω_obj, ObjectProperty.ι_map, χ_hom, truth_hom]
    apply IsPullback.of_right _
      ((cancel_mono (closedSievesInclusion _)).mp (by simpa using Presheaf.comp_χ_eq _))
      (.of_horiz_isIso_mono ⟨_⟩ : IsPullback (𝟙 _) _ (Presheaf.χ m.hom) (closedSievesInclusion J))
    · simp only [Category.comp_id, closedSievesFactorization_comp_closedSievesInclusion]
      exact Presheaf.classifier_isPullback m.hom
    · simp_all [closedSievesFactorization_comp_closedSievesInclusion]

lemma Sheaf.χ_unique {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G)
    [Mono m] (χ' : G ⟶ Sheaf.Ω)
    (hχ' : IsPullback m ((Sheaf.terminal_isTerminal J _).from F) χ' (Sheaf.truth)) :
    χ' = Sheaf.χ m := by
  ext : 1
  apply (cancel_mono (closedSievesInclusion J)).mp
  simp only [χ_hom, closedSievesFactorization_comp_closedSievesInclusion]
  apply Presheaf.χ_unique _
  · have pb: IsPullback (𝟙 G.obj) χ'.hom (χ'.hom ≫ closedSievesInclusion J)
      (closedSievesInclusion J) := @IsPullback.of_horiz_isIso_mono
        _ _ _ _ _ _ _ _ _ _ _ (inferInstanceAs (Mono (closedSievesInclusion J))) (by simp)
    have : IsPullback m.hom ?_ χ'.hom (truth.hom) := by
      simpa using hχ'.map (sheafToPresheaf J _)
    simpa using this.paste_horiz pb

/--
A construction of a subobject classifier for sheaf categories. `Ω` is the sheaf of closed sieves,
and `truth` maps for each object `X : C`, an element of `PUnit` to the maximal `Sieve X`.
-/
@[simps! Ω truth Ω₀ χ χ₀]
noncomputable def Sheaf.classifier (J : GrothendieckTopology C) :
    Classifier (Sheaf J (Type (max u v))) :=
  .mkOfTerminalΩ₀ (.terminal J Types.isTerminalPUnit) (Sheaf.terminal_isTerminal _ _) Sheaf.Ω
    Sheaf.truth Sheaf.χ Sheaf.classifier_isPullback Sheaf.χ_unique

/-- Sheaf categories have a subobject classifier. -/
instance HasClassifier.instSheaf [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    HasClassifier (Sheaf J (Type w)) where
  exists_classifier := ⟨Sheaf.classifier (Functor.inducedTopology (equivSmallModel C).inverse J)
    |>.ofEquivalence (Equivalence.sheafCongr _ _ (equivSmallModel C) _).symm⟩
end sheaf

end CategoryTheory

end
