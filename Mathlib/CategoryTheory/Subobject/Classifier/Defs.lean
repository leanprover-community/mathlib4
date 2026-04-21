/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen, Pablo Donato, Klaus Gy
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Subobject.Presheaf

/-!

# Subobject Classifier

We define a structure containing the data of a subobject classifier in a category `C` as
`CategoryTheory.Subobject.Classifier C`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Subobject.Classifier C` is the data of a subobject classifier in `C`.

* `CategoryTheory.HasSubobjectClassifier C` says that there is at least one subobject classifier.
  `Ω C` denotes a choice of subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and therefore regular)
  monomorphism, simply because its source is the terminal object.

* An instance of `IsRegularMonoCategory C` is exhibited for any category with a subobject
  classifier.

* `CategoryTheory.Subobject.Classifier.representableBy`: any subobject classifier `Ω` in `C`
  represents the subobjects functor `CategoryTheory.Subobject.presheaf C`, assuming `C` has
  pullbacks.

* `CategoryTheory.SubobjectRepresentableBy.classifier`: any representation `Ω` of
  `CategoryTheory.Subobject.presheaf C` is a subobject classifier in `C`.

* `CategoryTheory.hasClassifier_isRepresentable_iff`: from the two above mappings, we get that a
  category `C` with pullbacks has a subobject classifier if and only if the subobjects presheaf
  `CategoryTheory.Subobject.presheaf C` is representable (Proposition 1 in Section I.3 of [MM92]).

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v v₀ u u₀

namespace CategoryTheory

open Category Limits Functor IsPullback

variable {C : Type u} [Category.{v} C]

namespace Subobject

/-- A monomorphism `truth : Ω₀ ⟶ Ω` is a subobject classifier if, for every monomorphism
`m : U ⟶ X` in `C`, there is a unique map `χ : X ⟶ Ω` such that for some (necessarily unique)
`χ₀ : U ⟶ Ω₀` the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
An equivalent formulation replaces `Ω₀` with the terminal object.
-/
structure Classifier (C : Type u) [Category.{v} C] where
  /-- The domain of the truth morphism -/
  Ω₀ : C
  /-- The codomain of the truth morphism -/
  Ω : C
  /-- The truth morphism of the subobject classifier -/
  truth : Ω₀ ⟶ Ω
  /-- The truth morphism is a monomorphism -/
  mono_truth : Mono truth := by infer_instance
  /-- The top arrow in the pullback square -/
  χ₀ (U : C) : U ⟶ Ω₀
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  χ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `χ₀ U` and `χ m` form the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (χ₀ U) (χ m) truth
  /-- `χ m` is the only map `X ⟶ Ω` which forms the appropriate pullback square for any `χ₀'`. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] {χ₀' : U ⟶ Ω₀} {χ' : X ⟶ Ω}
    (hχ' : IsPullback m χ₀' χ' truth) : χ' = χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier := Classifier

namespace Classifier

attribute [instance] mono_truth

/-- More explicit constructor in case `Ω₀` is already known to be a terminal object. -/
@[simps]
def mkOfTerminalΩ₀
    (Ω₀ : C)
    (t : IsTerminal Ω₀)
    (Ω : C)
    (truth : Ω₀ ⟶ Ω)
    (χ : ∀ {U X : C} (m : U ⟶ X) [Mono m], X ⟶ Ω)
    (isPullback : ∀ {U X : C} (m : U ⟶ X) [Mono m],
      IsPullback m (t.from U) (χ m) truth)
    (uniq : ∀ {U X : C} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω)
      (_ : IsPullback m (t.from U) χ' truth), χ' = χ m) : Classifier C where
  Ω₀ := Ω₀
  Ω := Ω
  truth := truth
  mono_truth := t.mono_from _
  χ₀ := t.from
  χ m _ := χ m
  isPullback m _ := isPullback m
  uniq m _ χ₀' χ' hχ' := uniq m χ' ((t.hom_ext χ₀' (t.from _)) ▸ hχ')

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.mkOfTerminalΩ₀ := mkOfTerminalΩ₀

instance {c : Classifier C} : ∀ Y : C, Unique (Y ⟶ c.Ω₀) := fun Y =>
  { default := c.χ₀ Y,
    uniq f :=
      have : f ≫ c.truth = c.χ₀ Y ≫ c.truth := calc
          _ = c.χ (𝟙 Y) := c.uniq (𝟙 Y) (of_horiz_isIso_mono { })
          _ = c.χ₀ Y ≫ c.truth := by simp [← (c.isPullback (𝟙 Y)).w]
      Mono.right_cancellation _ _ this }

/-- Given `c : Classifier C`, `c.Ω₀` is a terminal object.
Prefer `c.χ₀` over `c.isTerminalΩ₀.from`. -/
def isTerminalΩ₀ {c : Classifier C} : IsTerminal c.Ω₀ := IsTerminal.ofUnique c.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalΩ₀ := isTerminalΩ₀

@[simp]
lemma isTerminalFrom_eq_χ₀ (c : Classifier C) : c.isTerminalΩ₀.from = c.χ₀ := rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalFrom_eq_χ₀ := isTerminalFrom_eq_χ₀

end Subobject.Classifier

open Subobject
/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
class HasSubobjectClassifier (C : Type u) [Category.{v} C] : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Subobject.Classifier C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier := HasSubobjectClassifier

namespace HasSubobjectClassifier

variable [HasSubobjectClassifier C]

noncomputable section
variable (C)

/-- Notation for the `Ω₀` in an arbitrary choice of a subobject classifier -/
abbrev Ω₀ : C := HasSubobjectClassifier.exists_classifier.some.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω₀ := Ω₀

/-- Notation for the `Ω` in an arbitrary choice of a subobject classifier -/
abbrev Ω : C := HasSubobjectClassifier.exists_classifier.some.Ω

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω := Ω

/-- Notation for the "truth arrow" in an arbitrary choice of a subobject classifier -/
abbrev truth : Ω₀ C ⟶ Ω C := HasSubobjectClassifier.exists_classifier.some.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truth := truth

variable {C} {U X : C} (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
def χ : X ⟶ Ω C :=
  HasSubobjectClassifier.exists_classifier.some.χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.χ := χ

/-- The diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
is a pullback square.
-/
lemma isPullback_χ : IsPullback m (Classifier.χ₀ _ U) (χ m) (truth C) :=
  Classifier.isPullback _ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isPullback_χ := isPullback_χ

/-- The diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
commutes.
-/
@[reassoc]
lemma comm : m ≫ χ m = Classifier.χ₀ _ U ≫ truth C := (isPullback_χ m).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.comm := comm

/-- `χ m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (Classifier.χ₀ _ U) χ' (truth C)) : χ' = χ m :=
  Classifier.uniq _ m hχ'

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.unique := unique

instance truthIsSplitMono : IsSplitMono (truth C) :=
  Subobject.Classifier.isTerminalΩ₀.isSplitMono_from _

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsSplitMono := truthIsSplitMono

/-- `truth C` is a regular monomorphism (because it is split). -/
noncomputable def truthIsRegularMono : RegularMono (truth C) :=
  RegularMono.ofIsSplitMono (truth C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsRegularMono := truthIsRegularMono

instance : IsRegularMono (truth C) := ⟨⟨truthIsRegularMono⟩⟩

/-- The following diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
Hence, `C` is a regular mono category.
It also follows that `C` is a balanced category.
-/
instance isRegularMonoCategory : IsRegularMonoCategory C where
  regularMonoOfMono :=
    fun m => ⟨⟨regularOfIsPullbackFstOfRegular truthIsRegularMono
      (isPullback_χ m).w (isPullback_χ m).isLimit⟩⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isRegularMonoCategory := isRegularMonoCategory

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphisms := reflectsIsomorphisms

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
instance reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
    [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphismsOp := reflectsIsomorphismsOp

end
end HasSubobjectClassifier

/-! ### The representability theorem of subobject classifiers -/

section Representability

namespace Subobject.Classifier

/-! #### From classifiers to representations -/

section RepresentableBy

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (𝒞 : Classifier C)

/-- The subobject of `𝒞.Ω` corresponding to the `truth` morphism. -/
abbrev truth_as_subobject : Subobject 𝒞.Ω :=
  Subobject.mk 𝒞.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_as_subobject := truth_as_subobject

lemma surjective_χ {X : C} (φ : X ⟶ 𝒞.Ω) :
    ∃ (Z : C) (i : Z ⟶ X) (_ : Mono i), φ = 𝒞.χ i :=
  ⟨Limits.pullback φ 𝒞.truth, pullback.fst _ _, inferInstance, 𝒞.uniq _ (by
    convert IsPullback.of_hasPullback φ 𝒞.truth)⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.surjective_χ := surjective_χ

@[simp]
lemma pullback_χ_obj_mk_truth {Z X : C} (i : Z ⟶ X) [Mono i] :
    (Subobject.pullback (𝒞.χ i)).obj 𝒞.truth_as_subobject = .mk i :=
  Subobject.pullback_obj_mk (𝒞.isPullback i).flip

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.pullback_χ_obj_mk_truth := pullback_χ_obj_mk_truth

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma χ_pullback_obj_mk_truth_arrow {X : C} (φ : X ⟶ 𝒞.Ω) :
    𝒞.χ ((Subobject.pullback φ).obj 𝒞.truth_as_subobject).arrow = φ := by
  obtain ⟨Z, i, _, rfl⟩ := 𝒞.surjective_χ φ
  refine (𝒞.uniq _ (?_ : IsPullback _ (𝒞.χ₀ _) _ _)).symm
  refine (IsPullback.of_hasPullback 𝒞.truth (𝒞.χ i)).flip.of_iso
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (𝒞.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
  dsimp
  rw [Iso.eq_inv_comp, comp_id, underlyingIso_hom_comp_eq_mk]
  rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_pullback_obj_mk_truth_arrow :=
  χ_pullback_obj_mk_truth_arrow

set_option backward.isDefEq.respectTransparency false in
/-- Any subobject classifier `Ω` represents the subobjects functor `Subobject.presheaf`. -/
noncomputable def representableBy :
    (Subobject.presheaf C).RepresentableBy 𝒞.Ω where
  homEquiv := {
    toFun φ := (Subobject.pullback φ).obj 𝒞.truth_as_subobject
    invFun x := 𝒞.χ x.arrow
    left_inv φ := by simp
    right_inv x := by simp
  }
  homEquiv_comp _ _ := by simp [pullback_comp]

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.representableBy :=
  representableBy

end RepresentableBy
end Subobject.Classifier

/-! #### From representations to classifiers -/

section FromRepresentation

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (Ω : C)

/-- Abbreviation to enable dot notation on the hypothesis `h` stating that the subobjects presheaf
is representable by some object `Ω`. -/
abbrev SubobjectRepresentableBy := (Subobject.presheaf C).RepresentableBy Ω

@[deprecated (since := "2026-03-06")]
alias Classifier.SubobjectRepresentableBy := SubobjectRepresentableBy

variable {Ω} (h : SubobjectRepresentableBy Ω)

namespace SubobjectRepresentableBy

/-- `h.Ω₀` is the subobject of `Ω` which corresponds to the identity `𝟙 Ω`,
given `h : SubobjectRepresentableBy Ω`. -/
def Ω₀ : Subobject Ω := h.homEquiv (𝟙 Ω)

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.Ω₀ := Ω₀

/-- `h.homEquiv` acts like an "object comprehension" operator: it maps any characteristic map
`f : X ⟶ Ω` to the associated subobject of `X`, obtained by pulling back `h.Ω₀` along `f`. -/
lemma homEquiv_eq {X : C} (f : X ⟶ Ω) :
    h.homEquiv f = (Subobject.pullback f).obj h.Ω₀ := by
  simpa using h.homEquiv_comp f (𝟙 _)

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.homEquiv_eq := homEquiv_eq

/-- For any subobject `x`, the pullback of `h.Ω₀` along the characteristic map of `x`
given by `h.homEquiv` is `x` itself. -/
lemma pullback_homEquiv_symm_obj_Ω₀ {X : C} (x : Subobject X) :
    (Subobject.pullback (h.homEquiv.symm x)).obj h.Ω₀ = x := by
  rw [← homEquiv_eq, Equiv.apply_symm_apply]

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.pullback_homEquiv_symm_obj_Ω₀ :=
  pullback_homEquiv_symm_obj_Ω₀

section

variable {U X : C} (m : U ⟶ X) [Mono m]

/-- `h.χ m` is the characteristic map of monomorphism `m` given by the bijection `h.homEquiv`. -/
def χ : X ⟶ Ω := h.homEquiv.symm (Subobject.mk m)

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.χ := χ

/-- `h.iso m` is the isomorphism between `m` and the pullback of `Ω₀`
    along the characteristic map of `m`. -/
noncomputable def iso : MonoOver.mk m ≅
    Subobject.representative.obj ((Subobject.pullback (h.χ m)).obj h.Ω₀) :=
  (Subobject.representativeIso (.mk m)).symm ≪≫ Subobject.representative.mapIso
    (eqToIso (h.pullback_homEquiv_symm_obj_Ω₀ (.mk m)).symm)

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso := iso

/-- `h.π m` is the first projection in the following pullback square:

    ```
    U --h.π m--> (Ω₀ : C)
    |                |
    m             Ω₀.arrow
    |                |
    v                v
    X -----h.χ m---> Ω
    ```
-/
noncomputable def π : U ⟶ Subobject.underlying.obj h.Ω₀ :=
  (h.iso m).hom.hom.left ≫ Subobject.pullbackπ (h.χ m) h.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.π := π

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma iso_inv_left_π :
    (h.iso m).inv.hom.left ≫ h.π m = Subobject.pullbackπ (h.χ m) h.Ω₀ := by
  dsimp only [π]
  rw [← Over.comp_left_assoc]
  convert Category.id_comp _ using 2
  exact (MonoOver.forget _ ⋙ Over.forget _).congr_map (h.iso m).inv_hom_id

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_left_π := iso_inv_left_π

@[reassoc (attr := simp)]
lemma iso_inv_hom_left_comp :
    (h.iso m).inv.hom.left ≫ m =
      ((Subobject.pullback (h.χ m)).obj h.Ω₀).arrow :=
  MonoOver.w (h.iso m).inv

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_hom_left_comp :=
  iso_inv_hom_left_comp

@[deprecated (since := "2025-12-18")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_left_comp :=
  iso_inv_hom_left_comp

set_option backward.isDefEq.respectTransparency false in
lemma isPullback {U X : C} (m : U ⟶ X) [Mono m] :
    IsPullback m (h.π m) (h.χ m) h.Ω₀.arrow := by
  fapply (Subobject.isPullback (h.χ m) h.Ω₀).flip.of_iso
    (((MonoOver.forget _ ⋙ Over.forget _).mapIso (h.iso m)).symm) (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
  all_goals simp [MonoOver.forget]

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isPullback := isPullback

variable {m}
lemma uniq {χ' : X ⟶ Ω} {π : U ⟶ h.Ω₀}
    (sq : IsPullback m π χ' h.Ω₀.arrow) : χ' = h.χ m := by
  apply h.homEquiv.injective
  simp only [χ, Equiv.apply_symm_apply, homEquiv_eq]
  simpa using Subobject.pullback_obj_mk sq.flip

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.uniq := uniq

end

/-- The main non-trivial result: `h.Ω₀` is actually a terminal object. -/
noncomputable def isTerminalΩ₀ : IsTerminal (h.Ω₀ : C) :=
  IsTerminal.ofUniqueHom (fun X ↦ h.π (𝟙 X)) (fun X π' ↦ by
    have : IsPullback (𝟙 X) π' (π' ≫ h.Ω₀.arrow) h.Ω₀.arrow :=
      { isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst) (by simp)
          (fun s ↦ by rw [← cancel_mono h.Ω₀.arrow, ← s.condition, Category.assoc])
          (fun s m hm _ ↦ by simpa using hm) ⟩ }
    rw [← cancel_mono h.Ω₀.arrow, h.uniq this,
      ← (h.isPullback (𝟙 X)).w, Category.id_comp])

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isTerminalΩ₀ := isTerminalΩ₀

/-- The unique map to the terminal object. -/
noncomputable def χ₀ (U : C) : U ⟶ h.Ω₀ := h.isTerminalΩ₀.from U

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.χ₀ := χ₀

include h in
lemma hasTerminal : HasTerminal C := h.isTerminalΩ₀.hasTerminal

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.hasTerminal := hasTerminal

variable [HasTerminal C]

/-- `h.isoΩ₀` is the unique isomorphism from `h.Ω₀` to the canonical terminal object `⊤_ C`. -/
noncomputable def isoΩ₀ : (h.Ω₀ : C) ≅ ⊤_ C :=
  h.isTerminalΩ₀.conePointUniqueUpToIso (limit.isLimit _)

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isoΩ₀ := isoΩ₀

/-- Any representation `Ω` of `Subobject.presheaf C` gives a subobject classifier with truth values
object `Ω`. -/
noncomputable def classifier : Subobject.Classifier C where
  Ω₀ := ⊤_ C
  Ω := Ω
  truth := h.isoΩ₀.inv ≫ h.Ω₀.arrow
  mono_truth := terminalIsTerminal.mono_from _
  χ₀ := terminalIsTerminal.from
  χ m _ := h.χ m
  isPullback m _ :=
    (h.isPullback m).of_iso (Iso.refl _) (Iso.refl _) h.isoΩ₀ (Iso.refl _)
      (by simp) (Subsingleton.elim _ _) (by simp) (by simp)
  uniq {U X} m _ χ₀ χ' sq := by
    have : IsPullback m (h.χ₀ U) χ' h.Ω₀.arrow :=
      sq.of_iso (Iso.refl _) (Iso.refl _) (h.isoΩ₀.symm) (Iso.refl _)
        (by simp) (h.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
    exact h.uniq this

@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.classifier := classifier

end SubobjectRepresentableBy
end FromRepresentation

variable [HasTerminal C]

/-- A category has a subobject classifier if and only if the subobjects functor is representable. -/
theorem hasSubobjectClassifier_iff_isRepresentable [HasPullbacks C] :
    HasSubobjectClassifier C ↔ (Subobject.presheaf C).IsRepresentable := by
  constructor <;> intro h
  · obtain ⟨⟨𝒞⟩⟩ := h
    apply RepresentableBy.isRepresentable
    exact 𝒞.representableBy
  · obtain ⟨Ω, ⟨h⟩⟩ := h
    constructor; constructor
    exact SubobjectRepresentableBy.classifier h

@[deprecated (since := "2026-03-06")]
alias isRepresentable_hasClassifier_iff := hasSubobjectClassifier_iff_isRepresentable

end Representability

namespace Subobject.Classifier
section Iso

/-- The unique morphism between classifiers mapping each others characteristic maps -/
def hom (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ⟶ 𝒞₂.Ω := 𝒞₂.χ 𝒞₁.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom := hom

@[reassoc (attr := simp)]
lemma hom_comp_hom (𝒞₁ 𝒞₂ 𝒞₃ : Classifier C) : 𝒞₁.hom 𝒞₂ ≫ 𝒞₂.hom 𝒞₃ = 𝒞₁.hom 𝒞₃ :=
  𝒞₃.uniq _ <| (𝒞₂.isPullback _).paste_vert (𝒞₃.isPullback _)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_comp_hom := hom_comp_hom

@[simp]
lemma hom_refl (𝒞₁ : Classifier C) : 𝒞₁.hom 𝒞₁ = 𝟙 _ :=
  (𝒞₁.uniq (χ₀' := 𝟙 _) 𝒞₁.truth IsPullback.of_id_snd).symm

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_refl := hom_refl

@[reassoc (attr := simp)]
lemma χ_comp_hom {𝒞₁ 𝒞₂ : Classifier C} {X Y : C} (m : X ⟶ Y) [Mono m] :
    𝒞₁.χ m ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ m :=
  𝒞₂.uniq m ((𝒞₁.isPullback m).paste_vert (𝒞₂.isPullback 𝒞₁.truth))

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_comp_hom := χ_comp_hom

@[reassoc (attr := simp)]
lemma truth_comp_hom {𝒞₁ 𝒞₂ : Classifier C} :
  𝒞₁.truth ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ₀ _ ≫ 𝒞₂.truth := (𝒞₂.isPullback _).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_comp_hom := truth_comp_hom

/-- a concrete equivalence of any two subobject classifiers -/
@[simps]
def uniqueUpToIso (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ≅ 𝒞₂.Ω where
  hom := 𝒞₁.hom 𝒞₂
  inv := 𝒞₂.hom 𝒞₁

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.uniqueUpToIso := uniqueUpToIso

instance (𝒞₁ 𝒞₂ : Classifier C) : IsIso (𝒞₁.hom 𝒞₂) := (𝒞₁.uniqueUpToIso 𝒞₂).isIso_hom

/-- Being a subobject classifier is preserved under isomorphism. -/
@[simps]
def ofIso (𝒞 : Classifier C) {Ω₀ Ω : C} (eΩ : 𝒞.Ω ≅ Ω) (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀)
    (from' : ∀ C, C ⟶ Ω₀) (t : Ω₀ ⟶ Ω) (ht : t = eΩ₀.inv ≫ 𝒞.truth ≫ eΩ.hom := by cat_disch) :
    Classifier C where
  Ω₀ := Ω₀
  Ω := Ω
  truth := t
  mono_truth := ht ▸ inferInstance
  χ₀ := from'
  χ {F G} m _ := 𝒞.χ m ≫ eΩ.hom
  isPullback {F G} m _ := by
    rw [eΩ₀.comp_inv_eq.mp (Subsingleton.elim (from' F ≫ eΩ₀.inv) (𝒞.χ₀ F))]
    exact (𝒞.isPullback m).paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
  uniq {F G} m _ := by
    intro χ₀' χ' hχ'
    have : χ' ≫ eΩ.inv = 𝒞.χ m := by
      apply 𝒞.uniq m (χ₀' := χ₀' ≫ eΩ₀.inv)
      exact hχ'.paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
    simpa using this =≫ eΩ.hom

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.ofIso := ofIso

end Iso

section Equivalence

variable {D : Type*} [Category* D]

set_option backward.isDefEq.respectTransparency false in
/--
The image of a subobject classifier under an equivalence of categories is a subobject classifier.
-/
@[simps]
def ofEquivalence (𝒞₁ : Classifier C) (e : C ≌ D) : Classifier D where
  Ω₀ := e.functor.obj 𝒞₁.Ω₀
  Ω := e.functor.obj 𝒞₁.Ω
  truth := e.functor.map 𝒞₁.truth
  χ₀ Y := e.counitInv.app Y ≫ e.functor.map (𝒞₁.χ₀ (e.inverse.obj Y))
  χ m := e.counitInv.app _ ≫ e.functor.map (𝒞₁.χ (e.inverse.map m))
  isPullback {F G} m _ := by
    apply ((𝒞₁.isPullback (e.inverse.map m)).map e.functor).of_iso (e.counitIso.app _)
      (e.counitIso.app _) (.refl _) (.refl _) <;> simp
  uniq {F G} m _ := by
    intro χ₀' χ' hχ'
    have : e.inverse.map χ' ≫ e.unitInv.app _ = 𝒞₁.χ (e.inverse.map m) := by
      apply 𝒞₁.uniq (e.inverse.map m) (χ₀' := e.inverse.map χ₀' ≫ e.unitInv.app _)
      exact (hχ'.map e.inverse).paste_vert <| IsPullback.of_vert_isIso_mono .mk
    simpa using congr(e.counitInv.app G ≫ e.functor.map $this)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.ofEquivalence := ofEquivalence

end Equivalence

end CategoryTheory.Subobject.Classifier
