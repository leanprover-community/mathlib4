/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Disjoint coproducts

Defines disjoint coproducts: coproducts where the intersection is initial and the coprojections
are monic.
Shows that a category with disjoint coproducts is `InitialMonoClass`.

## TODO

* Adapt this to the infinitary (small) version: This is one of the conditions in Giraud's theorem
  characterising sheaf topoi.
* Construct examples (and counterexamples?), eg Type, Vec.
* Define extensive categories, and show every extensive category has disjoint coproducts.
* Define coherent categories and use this to define positive coherent categories.
-/


universe v u u₂

namespace CategoryTheory

section

open Opposite Limits

variable {C : Type*} [Category C]

instance {X Y : C} [HasBinaryCoproduct X Y] :
    HasCoproduct (fun j : WalkingPair ↦ (j.casesOn X Y : C)) := ‹_›

@[reassoc (attr := simp)]
lemma Limits.ConeMorphism.hom_inv_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F}
    (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[reassoc (attr := simp)]
lemma Limits.ConeMorphism.inv_hom_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F}
    (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F} (f : c ≅ d) :
    IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F} (f : c ≅ d) :
    IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[reassoc (attr := simp)]
lemma Limits.CoconeMorphism.hom_inv_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F}
    (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cocone.category_comp_hom]

@[reassoc (attr := simp)]
lemma Limits.CoconeMorphism.inv_hom_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F}
    (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cocone.category_comp_hom]

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F} (f : c ≅ d) :
    IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F} (f : c ≅ d) :
    IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[reassoc (attr := simp)]
lemma Limits.Cofan.IsColimit.inj_desc {ι : Type*} {X : ι → C} (c d : Cofan X) (hc : IsColimit c)
    (i : ι) : c.inj i ≫ hc.desc d = d.inj i :=
  hc.fac _ _

@[reassoc (attr := simp)]
lemma Limits.Fan.IsLimit.lift_proj {ι : Type*} {X : ι → C} (c d : Fan X) (hc : IsLimit c)
    (i : ι) : hc.lift d ≫ c.proj i = d.proj i :=
  hc.fac _ _

end

namespace Limits

open Category

variable {C : Type u} [Category.{v} C]

/--
We say the coproduct of the family `Xᵢ` is disjoint, if whenever we have a pullback diagram of the
form
```
Z  ⟶ X₁
↓    ↓
X₂ ⟶ ∐ X
```,
`Z` is initial.
-/
class CoproductDisjoint {ι : Type*} (X : ι → C) : Prop where
  nonempty_isInitial_of_ne {c : Cofan X} (hc : IsColimit c) {i j : ι} (_ : i ≠ j)
    (s : PullbackCone (c.inj i) (c.inj j)) :
    IsLimit s → Nonempty (IsInitial s.pt)
  mono_inj {c : Cofan X} (hc : IsColimit c) (i : ι) : Mono (c.inj i)

section

variable {ι : Type*} {X : ι → C}

lemma CoproductDisjoint.of_cofan {c : Cofan X} (hc : IsColimit c)
    [∀ i, Mono (c.inj i)]
    (s : ∀ {i j : ι} (_ : i ≠ j), PullbackCone (c.inj i) (c.inj j))
    (hs : ∀ {i j : ι} (hij : i ≠ j), IsLimit (s hij))
    (H : ∀ {i j : ι} (hij : i ≠ j), IsInitial (s hij).pt) :
    CoproductDisjoint X where
  nonempty_isInitial_of_ne {d} hd {i j} hij t ht := by
    let e := hd.uniqueUpToIso hc
    have heq (i) : d.inj i ≫ e.hom.hom = c.inj i := e.hom.w ⟨i⟩
    let u : t.pt ⟶ (s hij).pt := by
      refine PullbackCone.IsLimit.lift (hs hij) t.fst t.snd ?_
      simp [← heq, t.condition_assoc]
    refine ⟨(H hij).ofIso ⟨(H hij).to t.pt, u, (H hij).hom_ext _ _, ?_⟩⟩
    refine PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [show (H hij).to (X i) = (s hij).fst from (H hij).hom_ext _ _, u]
    · simp [show (H hij).to (X j) = (s hij).snd from (H hij).hom_ext _ _, u]
  mono_inj {d} hd i := by
    rw [show d.inj i = c.inj i ≫ (hd.uniqueUpToIso hc).inv.hom by simp]
    infer_instance

variable [CoproductDisjoint X]

lemma _root_.CategoryTheory.Mono.of_coproductDisjoint {c : Cofan X} (hc : IsColimit c) (i : ι) :
    Mono (c.inj i) :=
  CoproductDisjoint.mono_inj hc i

instance [HasCoproduct X] (i : ι) : Mono (Sigma.ι X i) :=
  CoproductDisjoint.mono_inj (colimit.isColimit _) i

/-- If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `Z`, where `Z` is the
coproduct of the `Xᵢ`, then `Y` is initial. -/
noncomputable def IsInitial.ofCoproductDisjointOfIsColimitOfIsLimit {i j : ι} (hij : i ≠ j)
    {c : Cofan X} (hc : IsColimit c)
    {s : PullbackCone (c.inj i) (c.inj j)} (hs : IsLimit s) :
    IsInitial s.pt :=
  (CoproductDisjoint.nonempty_isInitial_of_ne hc hij _ hs).some

/-- If `i ≠ j`, the pullback `Xᵢ ×[∐ X] Xⱼ` is initial. -/
noncomputable def IsInitial.ofCoproductDisjoint {i j : ι} (hij : i ≠ j)
    [HasCoproduct X] [HasPullback (Sigma.ι X i) (Sigma.ι X j)] :
    IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)) :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _)
    (pullback.isLimit (Sigma.ι X i) (Sigma.ι X j))

/-- If `i ≠ j`, the pullback `Xᵢ ×[Z] Xⱼ` is initial, if `Z` is the coproduct of the `Xᵢ`. -/
noncomputable def IsInitial.ofCoproductDisjointOfIsColimit {i j : ι} (hij : i ≠ j)
    {Z : C} {f : ∀ i, X i ⟶ Z} [HasPullback (f i) (f j)]
    (hc : IsColimit (Cofan.mk _ f)) :
    IsInitial (pullback (f i) (f j)) :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij hc (pullback.isLimit (f i) (f j))

/-- If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `∐ X`, `Y` is initial. -/
noncomputable def IsInitial.ofCoproductDisjointOfIsLimit {i j : ι} (hij : i ≠ j)
    [HasCoproduct X] (s : PullbackCone (Sigma.ι X i) (Sigma.ι X j))
    (hs : IsLimit s) : IsInitial s.pt :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _) hs

end

/-- The binary coproduct of `X` and `Y` is disjoint if the coproduct of the family `{X, Y}` is
disjoint. -/
abbrev BinaryCoproductDisjoint (X Y : C) :=
  CoproductDisjoint (fun j : WalkingPair ↦ (j.casesOn X Y : C))

section

variable {X Y : C}

lemma BinaryCoproductDisjoint.of_binaryCofan {c : BinaryCofan X Y} (hc : IsColimit c)
    [Mono c.inl] [Mono c.inr] (s : PullbackCone c.inl c.inr)
    (hs : IsLimit s) (H : IsInitial s.pt) :
    BinaryCoproductDisjoint X Y := by
  have (i : WalkingPair) : Mono (Cofan.inj c i) := by
    cases i
    exact inferInstanceAs <| Mono c.inl
    exact inferInstanceAs <| Mono c.inr
  refine .of_cofan hc (fun {i j} hij ↦ ?_) (fun {i j} hij ↦ ?_) (fun {i j} hij ↦ ?_)
  · match i, j with
    | .left, .right => exact s
    | .right, .left => exact s.flip
  · dsimp
    split
    · exact hs
    · exact PullbackCone.flipIsLimit hs
  · dsimp; split <;> exact H

variable [BinaryCoproductDisjoint X Y]

lemma _root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDisjoint {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  .of_coproductDisjoint hc .left

lemma _root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDisjoint {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  .of_coproductDisjoint hc .right

lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_left {Z : C}
    {f : X ⟶ Z} (g : Y ⟶ Z) (hc : IsColimit <| BinaryCofan.mk f g) : Mono f :=
  .of_coproductDisjoint hc .left

lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_right {Z : C}
    (f : X ⟶ Z) {g : Y ⟶ Z} (hc : IsColimit <| BinaryCofan.mk f g) : Mono g :=
  .of_coproductDisjoint hc .right

instance [HasBinaryCoproduct X Y] : Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  inferInstanceAs <| Mono (Sigma.ι _ _)

instance [HasBinaryCoproduct X Y] : Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  inferInstanceAs <| Mono (Sigma.ι _ _)

/-- If `X ← Z → Y` is a pullback diagram over `W`, where `W` is the
coproduct of `X` and `Y`, then `Z` is initial. -/
noncomputable def IsInitial.ofBinaryCoproductDisjointOfIsColimitOfIsLimit
    {c : BinaryCofan X Y} (hc : IsColimit c)
    {s : PullbackCone c.inl c.inr} (hs : IsLimit s) :
    IsInitial s.pt :=
  (CoproductDisjoint.nonempty_isInitial_of_ne hc (by simp) _ hs).some

/-- `X ×[X ⨿ Y] Y` is initial. -/
noncomputable
def IsInitial.ofBinaryCoproductDisjoint [HasBinaryCoproduct X Y]
    [HasPullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr] :
    IsInitial (pullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) (pullback.isLimit _ _)

/-- If `i ≠ j`, the pullback `Xᵢ ×[Z] Xⱼ` is initial, if `Z` is the coproduct of the `Xᵢ`. -/
noncomputable def IsInitial.ofBinaryCoproductDisjointOfIsColimit {Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (hc : IsColimit (BinaryCofan.mk f g)) :
    IsInitial (pullback f g) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit hc (pullback.isLimit f g)

/-- If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `∐ X`, `Y` is initial. -/
noncomputable def IsInitial.ofBinaryCoproductDisjointOfIsLimit
    [HasBinaryCoproduct X Y] (s : PullbackCone (coprod.inl : X ⟶ X ⨿ Y) coprod.inr)
    (hs : IsLimit s) : IsInitial s.pt :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) hs

@[deprecated (since := "2025-06-18")]
alias isInitialOfIsPullbackOfIsCoproduct :=
  IsInitial.ofBinaryCoproductDisjointOfIsColimitOfIsLimit

@[deprecated (since := "2025-06-18")]
alias isInitialOfIsPullbackOfCoproduct := IsInitial.ofBinaryCoproductDisjointOfIsLimit

@[deprecated (since := "2025-06-18")]
alias isInitialOfPullbackOfIsCoproduct := IsInitial.ofBinaryCoproductDisjointOfIsColimit

@[deprecated (since := "2025-06-18")]
alias isInitialOfPullbackOfCoproduct := IsInitial.ofBinaryCoproductDisjoint

@[deprecated (since := "2025-06-18")]
alias CoproductDisjoint.mono_inl := CategoryTheory.Mono.of_binaryCoproductDisjoint_left

@[deprecated (since := "2025-06-18")]
alias CoproductDisjoint.mono_inr := CategoryTheory.Mono.of_binaryCoproductDisjoint_right

end

/-- `C` has disjoint coproducts if every coproduct is disjoint. -/
class CoproductsOfShapeDisjoint (C : Type u) [Category.{v} C] (ι : Type*) : Prop where
  coproductDisjoint (X : ι → C) : CoproductDisjoint X

/-- `C` has disjoint binary coproducts if every coproduct is disjoint. -/
abbrev BinaryCoproductsDisjoint (C : Type u) [Category.{v} C] : Prop :=
  CoproductsOfShapeDisjoint C WalkingPair

attribute [instance 999] CoproductsOfShapeDisjoint.coproductDisjoint

lemma BinaryCoproductsDisjoint.mk (H : ∀ (X Y : C), BinaryCoproductDisjoint X Y) :
    BinaryCoproductsDisjoint C where
  coproductDisjoint X := by
    convert H (X .left) (X .right) using 1
    ext x
    cases x <;> simp

/-- If `C` has disjoint coproducts, any morphism out of initial is mono. Note it isn't true in
general that `C` has strict initial objects, for instance consider the category of types and
partial functions. -/
theorem initialMonoClass_of_coproductsDisjoint [BinaryCoproductsDisjoint C] :
    InitialMonoClass C where
  isInitial_mono_from X hI :=
    .of_binaryCoproductDisjoint_left (CategoryTheory.CategoryStruct.id X)
      { desc := fun s : BinaryCofan _ _ => s.inr
        fac := fun _s j =>
          Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
        uniq := fun (_s : BinaryCofan _ _) _m w =>
          (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) }

@[deprecated (since := "2025-06-18")]
alias initialMonoClass_of_disjoint_coproducts := initialMonoClass_of_coproductsDisjoint

end Limits

end CategoryTheory
