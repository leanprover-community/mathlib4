/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen, Robert Maxton
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Subobject.Presheaf
import Mathlib.CategoryTheory.Yoneda.ULift

import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!

# Subobject Classifier

We define what it means for a morphism in a category to be a subobject classifier
as `CategoryTheory.HasClassifier`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Classifier C` is the data of a subobject classifier in `C`.

* `CategoryTheory.HasClassifier C` says that there is at least one subobject classifier.
  `Ω C` denotes a choice of subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and
  therefore regular) monomorphism, simply because its source is the terminal object.

* In fact, by slightly strengthening the uniqueness property, we can derive that the source
  of the truth morphism is a terminal object. This provides an alternative constructor
  `Classifier.mk'` which avoids explicit reference to limits.

* An instance of `IsRegularMonoCategory C` is exhibited for any category with
  a subobject classifier.

* When a category has all pullbacks, the type of subobject classifiers is equivalent to the
  type of representing objects for the functor `B => Subobject B`, and the proposition of
  having a subobject classifier is equivalent to the proposition that this functor is representable.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

## TODO

* Refactor the `HasClassifier` API to use `Classifier.mk'`, so that talking about
  an abstract subobject classifier doesn't require `HasTerminal`.

-/

universe u v u₀ v₀

open CategoryTheory Category Limits Functor

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory
section variable [HasTerminal C]

/-- A morphism `truth : ⊤_ C ⟶ Ω` from the terminal object of a category `C`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
terminal.from U               χ
      |                       |
      v                       v
    ⊤_ C ------truth--------> Ω
```
An equivalent formulation replaces the object `⊤_ C` with an arbitrary object, and instead
includes the assumption that `truth` is a monomorphism.
-/
@[ext]
structure Classifier where
  /-- The target of the truth morphism -/
  Ω : C
  /-- the truth morphism for a subobject classifier -/
  truth : ⊤_ C ⟶ Ω
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  χ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `χ m` forms the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (terminal.from U) (χ m) truth
  /-- `χ m` is the only map `X ⟶ Ω` which forms the appropriate pullback square. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω)
      (hχ' : IsPullback m (terminal.from U) χ' truth) :
    χ' = χ m

/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
class HasClassifier : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Classifier C)

namespace HasClassifier

variable [HasClassifier C]

noncomputable section

/-- Notation for the object in an arbitrary choice of a subobject classifier -/
abbrev Ω : C := HasClassifier.exists_classifier.some.Ω

/-- Notation for the "truth arrow" in an arbitrary choice of a subobject classifier -/
abbrev truth : ⊤_ C ⟶ Ω C := HasClassifier.exists_classifier.some.truth

variable {C}
variable {U X : C} (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
def χ : X ⟶ Ω C :=
  HasClassifier.exists_classifier.some.χ m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
is a pullback square.
-/
lemma isPullback_χ : IsPullback m (terminal.from U) (χ m) (truth C) :=
  HasClassifier.exists_classifier.some.isPullback m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
commutes.
-/
@[reassoc]
lemma comm : m ≫ χ m = terminal.from _ ≫ truth C := (isPullback_χ m).w

/-- `χ m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (terminal.from _) χ' (truth C)) : χ' = χ m :=
  HasClassifier.exists_classifier.some.uniq m χ' hχ'

lemma χ_id (X : C) : χ (𝟙 X) = terminal.from X ≫ truth C := by
  rw [← Category.id_comp (χ _), comm]

@[simp]
lemma χ_comp_id {X Y : C} (f : X ⟶ Y) : f ≫ χ (𝟙 Y) = χ (𝟙 X) := by
  simp [χ_id]

@[simp]
lemma χ_naturality [HasPullbacks C] {X Y Z : C} (g : X ⟶ Z) (f : Y ⟶ Z) [Mono f] :
    g ≫ χ f = χ (pullback.snd f g) := by
  apply unique
  rw [IsPullback.flip_iff, ← terminal.comp_from (pullback.fst f g)]
  exact IsPullback.paste_horiz (IsPullback.of_hasPullback f g) (isPullback_χ f).flip

/-- `truth C` is a regular monomorphism (because it is split). -/
noncomputable instance truthIsRegularMono : RegularMono (truth C) :=
  RegularMono.ofIsSplitMono (truth C)

/-- The following diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
Hence, `C` is a regular mono category.
It also follows that `C` is a balanced category.
-/
instance isRegularMonoCategory : IsRegularMonoCategory C where
  regularMonoOfMono :=
    fun m => ⟨regularOfIsPullbackFstOfRegular (isPullback_χ m).w (isPullback_χ m).isLimit⟩

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
instance reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
    [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

#check IsPullback.isoPullback

end
end HasClassifier
open HasClassifier Opposite
variable {C}
variable [HasClassifier C]


/-- For any `X : C` when `C` has a subobject classifier, subobjects of `X` are in bijection with
morphisms `X ⟶ Ω C` s.t. the pullback along `truth C` exists.

This version takes an arbitrary choice of subobject classifier. -/
@[simps]
noncomputable def subobjectEquivClassifying' (Ω : Classifier C) (X : C) :
    Subobject X ≃ {χ : X ⟶ Ω.Ω // HasPullback (Ω.truth) χ} where
  toFun m := ⟨Ω.χ m.arrow, (Ω.isPullback m.arrow).flip.hasPullback⟩
  invFun | ⟨χₘ, _⟩ => Subobject.mk (pullback.snd (Ω.truth) χₘ)
  left_inv m := by
    have := (Ω.isPullback m.arrow).flip.hasPullback
    fapply Subobject.mk_eq_of_comm
    · exact IsPullback.isoPullback (Ω.isPullback m.arrow).flip |>.symm
    · simp
  right_inv
  | ⟨χₘ, _⟩ => by
    ext
    symm
    apply Ω.uniq
    rw [← Subobject.underlyingIso_hom_comp_eq_mk,
      ← terminal.comp_from (Subobject.underlyingIso _).hom]
    apply IsPullback.extendIso
    apply IsPullback.flip
    convert IsPullback.of_hasPullback _ _
    exact terminal.hom_ext _ _

/-- For any `X : C` when `C` has a subobject classifier, subobjects of `X` are in bijection with
morphisms `X ⟶ Ω C` s.t. the pullback along `truth C` exists.

This version uses the `HasClassifier` API. -/
@[simps!]
noncomputable def subobjectEquivClassifying (X : C) :
    Subobject X ≃ {χ : X ⟶ Ω C // HasPullback (truth C) χ} :=
  subobjectEquivClassifying' (HasClassifier.exists_classifier.some) X


/-- A monic morphism `truth : Ω₀ ⟶ Ω`  of a category `C` from an arbitrary object `Ω₀`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following diagram can be completed to a pullback
square:
```
      U ---------m----------> X
                              |
                              χ
                              |
                              v
      Ω₀ ------truth--------> Ω
```
In this case, `Ω₀` is a terminal object. -/
noncomputable def truthSrcIsTerminal (Ω : C) {Ω₀ : C} (truth : Ω₀ ⟶ Ω) [Mono truth]
    («from» : ∀ U : C, U ⟶ Ω₀) (χ : ∀ {U X : C} (m : U ⟶ X) [Mono m], X ⟶ Ω)
    (isPullback : ∀ {U X : C} (m : U ⟶ X) [Mono m], IsPullback m («from» U) (χ m) truth)
    (uniq : ∀ {U X : C} (m : U ⟶ X) [Mono m] (from' : U ⟶ Ω₀) (χ' : X ⟶ Ω) ,
      IsPullback m from' χ' truth → χ' = χ m) : IsTerminal Ω₀ where
  lift X := «from» X.pt
  uniq X from' _ := by
    have h_from' : IsPullback (𝟙 X.pt) from' (from' ≫ truth) truth := by
      convert IsPullback.of_isPullback_comp_mono (m := truth) IsPullback.of_id_fst
      simp
    have isPullback_X := isPullback (𝟙 X.pt)
    apply Mono.right_cancellation (f := truth)
    simp_rw [← isPullback_X.w, Category.id_comp]
    exact uniq (𝟙 X.pt) from' _ h_from'

omit [HasTerminal C] [HasClassifier C] in
lemma truthSrcIsTerminal_from {Ω : C} {Ω₀ : C} {truth : Ω₀ ⟶ Ω} [Mono truth]
    («from» : ∀ U : C, U ⟶ Ω₀) (χ : ∀ {U X : C} (m : U ⟶ X) [Mono m], X ⟶ Ω)
    (isPullback : ∀ {U X : C} (m : U ⟶ X) [Mono m], IsPullback m («from» U) (χ m) truth)
    (uniq : ∀ {U X : C} (m : U ⟶ X) [Mono m] (from' : U ⟶ Ω₀) (χ' : X ⟶ Ω) ,
      IsPullback m from' χ' truth → χ' = χ m) :
    (truthSrcIsTerminal Ω truth «from» χ isPullback uniq).from = «from» := rfl

omit [HasTerminal C] in
/-- A monic morphism `truth : Ω₀ ⟶ Ω`  of a category `C` from an arbitrary object `Ω₀`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following diagram can be completed to a pullback
square:
```
      U ---------m----------> X
                              |
                              χ
                              |
                              v
      Ω₀ ------truth--------> Ω
```
It can be shown that `Ω₀` is isomorphic to the terminal object, and thus that this construction
is equivalent to the main constructor. -/
@[simps]
noncomputable def Classifier.mk' (Ω : C) {Ω₀ : C} (truth : Ω₀ ⟶ Ω) [Mono truth]
    («from» : ∀ U : C, U ⟶ Ω₀) (χ : ∀ {U X : C} (m : U ⟶ X) [Mono m], X ⟶ Ω)
    (isPullback : ∀ {U X : C} (m : U ⟶ X) [Mono m], IsPullback m («from» U) (χ m) truth)
    (uniq : ∀ {U X : C} (m : U ⟶ X) [Mono m] (from' : U ⟶ Ω₀) (χ' : X ⟶ Ω) ,
      IsPullback m from' χ' truth → χ' = χ m) :
    @Classifier C _ (truthSrcIsTerminal Ω truth «from» χ isPullback uniq).hasTerminal := by
  let term := truthSrcIsTerminal Ω truth «from» χ isPullback uniq
  exact
  { Ω := Ω
    truth := (terminalIsoIsTerminal term).hom ≫ truth
    χ := χ
    isPullback {U X} m [_] := by
      have paste_left {U X} (m : U ⟶ X) [Mono m] :
          IsPullback (𝟙 U) (terminal.from U) («from» U) (terminalIsoIsTerminal term).hom :=
        IsPullback.of_horiz_isIso ⟨by simpa using term.hom_ext _ _⟩
      convert paste_left m |>.paste_horiz (isPullback m)
      simp
    uniq {U X} m [_] χ' hχ' := by
      have paste_left {U X} (m : U ⟶ X) [Mono m] :
          IsPullback (𝟙 U) («from» U) (terminal.from U) (terminalIsoIsTerminal term).inv :=
        IsPullback.of_horiz_isIso ⟨by simpa using terminal.hom_ext _ _⟩
      replace hχ' := paste_left m |>.paste_horiz hχ'
      simp_rw [Category.id_comp, Iso.inv_hom_id_assoc] at hχ'
      exact uniq m _ _ hχ' }


section variable [HasPullbacks C]

/-- For any `X : C` when `C` has all pullbacks and a subobject classifier, subobjects of `X` are in
bijection with morphisms `X ⟶ Ω C`.

This version takes an arbitrary choice of subobject classifier. -/
@[simps!]
noncomputable def subobjectEquivClassifying_ofPullbacks' (Ω : Classifier C) (X : C) :
    Subobject X ≃ (X ⟶ Ω.Ω) :=
  subobjectEquivClassifying' Ω X |>.trans <| Equiv.subtypeUnivEquiv fun (χ : X ⟶ Ω.Ω) ↦
    inferInstanceAs (HasPullback (Ω.truth) χ)

omit [HasPullbacks C] [HasClassifier C] in
/-- Two characteristic maps `χ m₁`, `χ m₂` are equal if and only if the subobjects
`Subobject.mk m₁`, `Subobject.mk m₂` are equal.

This version takes an arbitrary choice of subobject classifier. -/
lemma χ_ext_iff' (cls : Classifier C) {U₁ U₂ X : C}
    {m₁ : U₁ ⟶ X} {m₂ : U₂ ⟶ X} [Mono m₁] [Mono m₂] :
    cls.χ m₁ = cls.χ m₂ ↔ Subobject.mk m₁ = Subobject.mk m₂ := by
  -- let ⟨Ω, truth, χ, isPullback, uniq⟩ := cls
  -- simp only
  constructor <;> intro h'
  · let ι : U₁ ≅ U₂ := IsPullback.isoIsPullback _ _ (cls.isPullback m₁) (h' ▸ cls.isPullback m₂)
    fapply Subobject.mk_eq_mk_of_comm _ _ ι
    simp [ι]
  · let ι := Subobject.isoOfMkEqMk _ _ h'
    have uniq := @cls.uniq
    apply cls.uniq
    convert IsPullback.extendIso (cls.isPullback m₁) ι.symm
    · simp [ι]
    · simp

omit [HasClassifier C] in
lemma subobjectEquivClassifying_ofPullbacks'_apply_mk
    (Ω : Classifier C) (X : C) {U : C} (m : U ⟶ X) [Mono m] :
    subobjectEquivClassifying_ofPullbacks' Ω X (Subobject.mk m) = Ω.χ m := by
  simp [χ_ext_iff']

/-- For any `X : C` when `C` has all pullbacks and a subobject classifier, subobjects of `X` are in
bijection with morphisms `X ⟶ Ω C`.

This version uses the `HasClassifier` API. -/
noncomputable def subobjectEquivClassifying_ofPullbacks (X : C) :
    Subobject X ≃ (X ⟶ Ω C) :=
  subobjectEquivClassifying_ofPullbacks' (HasClassifier.exists_classifier.some) X

@[simp]
lemma subobjectEquivClassifying_ofPullbacks_apply (X : C) (a : Subobject X) :
    (subobjectEquivClassifying_ofPullbacks X) a = χ a.arrow := by
  simp [subobjectEquivClassifying_ofPullbacks, χ]

@[simp]
lemma subobjectEquivClassifying_ofPullbacks_symm_apply (X : C) (a : X ⟶ Ω C) :
    (subobjectEquivClassifying_ofPullbacks X).symm a =
      Subobject.mk (pullback.snd (truth C) a) := by
  simp [subobjectEquivClassifying_ofPullbacks]

omit [HasPullbacks C] in
/-- Two characteristic maps `χ m₁`, `χ m₂` are equal if and only if the subobjects
`Subobject.mk m₁`, `Subobject.mk m₂` are equal.

This version uses the `HasClassifier` API. -/
lemma χ_ext_iff {U₁ U₂ X : C} {m₁ : U₁ ⟶ X} {m₂ : U₂ ⟶ X} [Mono m₁] [Mono m₂] :
    χ m₁ = χ m₂ ↔ Subobject.mk m₁ = Subobject.mk m₂ := by
  simp_rw [χ.eq_def]
  simp [χ_ext_iff' (HasClassifier.exists_classifier.some)]

lemma χ_comp_eq_iff_isPullback {A X Y Z : C}
    (g : X ⟶ Z) (f : Y ⟶ Z) [Mono f] (r : A ⟶ X) [Mono r] :
    g ≫ χ f = χ r ↔ ∃ s, IsPullback r s g f := by
  simp_rw [χ_naturality, χ_ext_iff]
  constructor <;> intro h
  · let ι := Subobject.isoOfMkEqMk _ _ h
    exact ⟨ι.inv ≫ pullback.fst f g,
      (IsPullback.of_iso_pullback
        ⟨by simp [ι, pullback.condition, reassoc_of% Subobject.ofMkLEMk_comp (f := r)]⟩
        ι.symm (by simp) (by simp [ι])).flip⟩
  · obtain ⟨s, h⟩ := h
    fapply Subobject.mk_eq_mk_of_comm
    · exact h.flip.isoPullback.symm
    · simp

lemma subobjectEquivClassifying_ofPullbacks_apply_mk (X : C) {U : C} (m : U ⟶ X) [Mono m] :
    subobjectEquivClassifying_ofPullbacks X (Subobject.mk m) = χ m := by
  simp [χ_ext_iff]

noncomputable instance
    isTerminal_ofPresheafRepresentableBy {Ω : C} (hΩ : RepresentableBy (Subobject.presheaf C) Ω) :
    IsTerminal (Subobject.underlying.obj (hΩ.homEquiv (𝟙 Ω))) :=
  let truth := (hΩ.homEquiv (𝟙 Ω)).arrow
  let top U := hΩ.homEquiv.symm (Subobject.mk (𝟙 U))
  { lift
    | ⟨U, _⟩ => show U ⟶ Subobject.underlying.obj (hΩ.homEquiv (𝟙 Ω)) from
      (Subobject.isoOfMkEqMk (𝟙 U) (pullback.snd truth (top U)) (by
        have := hΩ.homEquiv_eq (hΩ.homEquiv.symm (Subobject.mk (𝟙 U)))
        erw [hΩ.homEquiv.apply_symm_apply] at this
        simpa [Subobject.pullback_obj] using this
      )).hom ≫ pullback.fst truth (top U)
    uniq := by
      rintro ⟨U, -⟩ (from' : U ⟶ (Subobject.underlying.obj (hΩ.homEquiv (𝟙 Ω)))) -
      simp only [Subobject.presheaf_obj, asEmptyCone_pt, Subobject.isoOfMkEqMk_hom]
      apply Mono.right_cancellation (f := truth)
      rw [Category.assoc, pullback.condition, reassoc_of% Subobject.ofMkLEMk_comp (f := 𝟙 U)]
      unfold top truth
      have {A X} (f : A ⟶ X) := @hΩ.comp_homEquiv_symm _ _ _ _ A X (Subobject.mk (𝟙 X)) f
      simp only [Subobject.presheaf_obj, Subobject.presheaf_map, Quiver.Hom.unop_op,
        Subobject.pullback_obj_mk (IsPullback.of_id_snd)] at this
      convert this from'
      erw [← hΩ.homEquiv.apply_eq_iff_eq_symm_apply, hΩ.homEquiv_eq (Subobject.arrow _)]
      simp [Subobject.pullback_obj] }

instance (priority := 100) hasTerminal_ofPresheafRepresentable
    [inst : (Subobject.presheaf C).IsRepresentable] : HasTerminal C :=
  isTerminal_ofPresheafRepresentableBy inst.has_representation.choose_spec.some |>.hasTerminal

@[simps!? Ω χ]
noncomputable def Classifier.ofPresheafRepresentableBy
    (Ω : C) (hΩ : RepresentableBy (Subobject.presheaf C) Ω) : Classifier C := by
  let χ {X} : Subobject X ≃ (X ⟶ Ω) := hΩ.homEquiv.symm
  have χ_def {X} : @χ X = hΩ.homEquiv.symm := rfl
  have hχ_comp'_mk {U P X X'} {f : U ⟶ X'} [Mono f] {g : X ⟶ X'}
      {fst : P ⟶ U} {snd : P ⟶ X} [Mono snd] (h : IsPullback fst snd f g) :
      g ≫ χ (Subobject.mk f) = χ (Subobject.mk snd) := by
    unfold χ
    erw [hΩ.comp_homEquiv_symm]
    simp [Subobject.pullback_obj_mk h]
  have hχ_comp'_mk_id {X X'} {g : X ⟶ X'} :=
    hχ_comp'_mk (g := g) (IsPullback.of_id_snd)
  let truth := (χ.symm (𝟙 Ω)).arrow
  -- let top U := χ (Subobject.mk (𝟙 U))
  -- have top_def U : top U = χ (Subobject.mk (𝟙 U)) := rfl
  let term := isTerminal_ofPresheafRepresentableBy hΩ
  let ι {U X} (f : U ⟶ X) [Mono f] :=
    (Subobject.isoOfMkEqMk f (pullback.snd truth (χ (Subobject.mk f))) (by
        have := hΩ.homEquiv_eq (χ (Subobject.mk f))
        erw [hΩ.homEquiv.apply_symm_apply] at this
        simpa [Subobject.pullback_obj] using this )) ≪≫ pullbackSymmetry _ _
  refine Classifier.mk' Ω truth
    (fun U ↦ (ι (𝟙 U)).hom ≫ pullback.snd (χ (Subobject.mk (𝟙 U))) truth)
    (fun {U X} f [_] ↦ χ (Subobject.mk f))
    (fun {U X} f [_] ↦ ?_)
    (fun {U X} f [_] from' χ' hχ' ↦ ?_)
  · convert IsPullback.of_iso_pullback ⟨?w⟩ (ι f) ?h₁ ?h₂
    · simp [Category.assoc, hχ_comp'_mk (IsPullback.of_hasPullback f f), ι, pullback.condition,
      reassoc_of% Subobject.ofMkLEMk_comp (f := 𝟙 U)]
    · rw [← Iso.eq_inv_comp]
      simp [ι, hχ_comp'_mk_id]
    · apply Mono.right_cancellation (f := truth)
      simp [ι, pullback.condition, reassoc_of% Subobject.ofMkLEMk_comp (C := C),
      hχ_comp'_mk (IsPullback.of_hasPullback f f)]
  · rw [← Equiv.symm_apply_eq]
    fapply Subobject.eq_mk_of_comm
    · have hχ {X} (χ_f : X ⟶ Ω) := hΩ.homEquiv_eq χ_f
      simp_rw [Subobject.presheaf_obj, Subobject.presheaf_map, Quiver.Hom.unop_op,
      Subobject.pullback_obj] at hχ
      exact Subobject.isoOfEqMk _ _ (hχ _) ≪≫ pullbackSymmetry _ _ ≪≫ hχ'.isoPullback.symm
    · refold_let truth
      simp only [Subobject.presheaf_obj, Iso.trans_hom, Iso.symm_hom, assoc,
      IsPullback.isoPullback_inv_fst]
      rw [← Iso.eq_inv_comp]
      simp [ι]

omit [HasClassifier C] in
@[simp]
lemma Classifier.ofPresheafRepresentableBy_truth
    (Ω : C) (hΩ : RepresentableBy (Subobject.presheaf C) Ω) :
    (Classifier.ofPresheafRepresentableBy Ω hΩ).truth =
      (isTerminal_ofPresheafRepresentableBy hΩ).from _ ≫ (hΩ.homEquiv (𝟙 Ω)).arrow := by
  simp [Classifier.ofPresheafRepresentableBy]; rfl


#check terminalIsoIsTerminal

@[simps]
noncomputable def classifierEquivPresheafRepresentableBy :
    Classifier C ≃ (Ω : C) × RepresentableBy (Subobject.presheaf C) Ω where
  toFun ω := ⟨ω.Ω, {
    homEquiv {X} := (subobjectEquivClassifying_ofPullbacks' ω X).symm
    homEquiv_comp {X X'} f χ := by
      simpa [Subobject.pullback_obj_mk (IsPullback.of_hasPullback _ _)] using
        Subobject.mk_eq_mk_of_comm _ _ (pullbackLeftPullbackSndIso _ _ _ |>.symm) (by simp) }⟩
  invFun | ⟨Ω, hΩ⟩ => Classifier.ofPresheafRepresentableBy Ω hΩ
  left_inv cls := by
      simp only
      ext
      · simp
      · simp only [Subobject.presheaf_obj, subobjectEquivClassifying_ofPullbacks'_symm_apply,
        Subobject.presheaf_map, Quiver.Hom.unop_op, id_eq, eq_mpr_eq_cast, cast_eq,
        Classifier.ofPresheafRepresentableBy_Ω, Classifier.ofPresheafRepresentableBy_truth,
        Equiv.symm_symm, subobjectEquivClassifying_ofPullbacks'_apply, heq_eq_eq]
        rcases cls with ⟨Ω, truth, χ, isPullback, uniq⟩
        rw [← IsTerminal.uniqueUpToIso_inv _ terminalIsTerminal, Iso.inv_comp_eq]
        simp only [terminalIsTerminal, IsTerminal.uniqueUpToIso_hom, IsTerminal.from,
          asEmptyCone_pt]
        simp_rw [← (Subobject.underlyingIso _).cancel_iso_inv_left]
        simp only [Subobject.underlyingIso_arrow, terminal.comp_from_assoc]
        nth_rw 1 [← Category.comp_id (pullback.snd _ _)]
        rw [← pullback.condition, terminal.hom_ext (pullback.fst _ _)]
      · rcases cls with ⟨Ω, truth, χ, isPullback, uniq⟩
        simp [Classifier.ofPresheafRepresentableBy, Classifier.mk']
        ext U X f _
        erw [subobjectEquivClassifying_ofPullbacks'_apply_mk]
  right_inv
  | ⟨Ω, hΩ⟩ => by
      simp only [Classifier.ofPresheafRepresentableBy_Ω, Sigma.mk.injEq, heq_eq_eq, true_and]
      ext
      simp only [Subobject.presheaf_obj]
      erw [subobjectEquivClassifying_ofPullbacks'_symm_apply]
      fapply Subobject.mk_eq_of_comm
      · exact (IsPullback.isoPullback (IsPullback.of_id_fst)).symm ≪≫
          terminalIsoIsTerminal (isTerminal_ofPresheafRepresentableBy hΩ)
      · simp only [Iso.trans_hom, Iso.symm_hom, assoc]
        rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd]
        simp

omit [HasClassifier C] in
lemma HasClassifier.iff_presheaf_representable :
    HasClassifier C ↔ IsRepresentable (Subobject.presheaf C) where
  mp | ⟨⟨cls⟩⟩ => ⟨⟨cls.Ω, ⟨classifierEquivPresheafRepresentableBy cls |>.2⟩⟩⟩
  mpr | ⟨⟨Ω, ⟨repr⟩⟩⟩ => ⟨⟨classifierEquivPresheafRepresentableBy.symm ⟨Ω, repr⟩⟩⟩

instance [IsRepresentable (Subobject.presheaf C)] : HasClassifier C :=
  HasClassifier.iff_presheaf_representable.mpr inferInstance

/-- An arbitrary choice of subobject classifier is isomorphic to any other. -/
@[simps!]
noncomputable def IsClassifier.uniqueUpToIso (Ω₁ Ω₂ : Classifier C) : Ω₁.Ω ≅ Ω₂.Ω :=
  RepresentableBy.uniqueUpToIso
    (classifierEquivPresheafRepresentableBy Ω₁).2
    (classifierEquivPresheafRepresentableBy Ω₂).2

/-- An arbitrary choice of subobject classifier is isomorphic to the one provided by the
`HasClassifier` API. -/
@[simps!]
noncomputable def IsClassifier.isoClassifier (Ω' : Classifier C) : Ω'.Ω ≅ Ω C :=
  IsClassifier.uniqueUpToIso Ω' (HasClassifier.exists_classifier.some)

end
end


open Function Classical in

/-- The classifying object of `Type u` is `ULift Bool`. -/
noncomputable def classifierType : Classifier (Type u) where
  Ω := ULift Bool
  truth := fun _ ↦ ⟨true⟩
  χ {α β} f [_] := extend f (fun _ ↦ ⟨true⟩) (fun _ ↦ ⟨false⟩)
  isPullback {α β} f hf := by
    rw [mono_iff_injective] at hf
    refine IsPullback.of_iso_pullback ⟨by ext a; simp [hf.extend_apply]⟩
        (?iso ≪≫ (Types.pullbackIsoPullback _ _).symm) ?h₁ (by ext x ⟨⟨⟩⟩)
    case iso =>
      · exact {
          hom a := ⟨⟨f a, default⟩, by simp [hf.extend_apply]⟩
          inv | ⟨⟨b, _⟩, hb⟩ => Exists.choose (by simpa [extend] using hb)
          hom_inv_id := by
            ext a
            simp only [types_comp_apply, types_id_apply]
            generalize_proofs h
            exact hf h.choose_spec
          inv_hom_id := by
            ext ⟨⟨b, -⟩, hb⟩ ⟨⟨⟩⟩
            simp only [types_comp_apply, types_id_apply]
            generalize_proofs h
            exact h.choose_spec }
    case h₁ => ext x; simp
  uniq {α β} f hf χ' hχ' := by
    rw [mono_iff_injective] at hf
    ext1 b
    have hχ'_w a : χ' (f a) = ⟨true⟩ := congrFun hχ'.w a
    simp_rw [extend]
    split <;> rename_i hb
    · obtain ⟨a, rfl⟩ := hb
      simp [hχ'_w]
    · push_neg at hb
      by_contra hχ'_b
      simp_rw [ULift.ext_iff, Bool.not_eq_false] at hχ'_b
      have := hχ'.isLimit.fac ⟨Option α,
      { app | .left => (Option.map f · |>.getD b)
            | .right => terminal.from _
            | .one => fun _ ↦ ⟨true⟩,
        naturality := by
          rintro _ _ (I | L | R) <;> {ext (none | a) <;> simp [hχ'_w, ← hχ'_b]} }⟩
      simp only at this
      have uniq_term := inferInstanceAs (Unique (⊤_ (Type u)))
      have all_eq (x y : ⊤_ (Type u)) : x = y :=
        uniq_term.eq_default _ |>.trans <| uniq_term.default_eq _
      replace this := congrFun (this .left) none
      simpa using hb _ this

instance : HasClassifier (Type u) := ⟨⟨classifierType⟩⟩

-- #synth HasClassifier (Type u)

-- section variable {C : Type u₀} [Category.{v₀} C] {D : Type u} [Category.{v} D]

-- def Functor.emptyFlipIsoConst : (empty (C ⥤ D)).flip ≅ (const C).obj (empty D) :=
--   NatIso.ofComponents (fun _ ↦ emptyExt _ _)

-- open HasClassifier in
-- /-- Subfunctors are classified pointwise. -/
-- noncomputable instance
--     -- {C : Type u₀} [Category.{v₀} C] {D : Type u} [Category.{v} D]
--     [HasPullbacks D] [HasTerminal D] [HasClassifier D] : Classifier (C ⥤ D) where
--   Ω := (const C).obj (Ω D)
--   truth :=
--     let termIsTerm : ⊤_ (C ⥤ D) ≅ (const C).obj (⊤_ D) :=
--       limitIsoFlipCompLim _ ≪≫ isoWhiskerRight Functor.emptyFlipIsoConst _
--         ≪≫ NatIso.ofComponents (fun _ ↦ Iso.refl _)
--     termIsTerm.hom ≫ (const C).map (truth D)
--   χ {F G} ϑ hϑ :=
--     have hϑ' := NatTrans.mono_iff_mono_app _ |>.mp hϑ
--     { app X := χ (ϑ.app X)
--       naturality ⦃X Y⦄ f := by
--         simp [-χ_naturality, χ_comp_eq_iff_isPullback]
--         have := ϑ.naturality f
--         use F.map f
--         -- refine ⟨F.map f, IsPullback.of_iso_pullback ⟨by simp⟩ ?ι ?h₁ ?h₂⟩
--      }
--   isPullback := _
--   uniq := _
    -- let F_const : (C ⥤ D) ⥤ (C ⥤ (Ω D)) :=
    --   Functor.const C ⋙ (HasClassifier.exists_classifier.some.map F)



end CategoryTheory
