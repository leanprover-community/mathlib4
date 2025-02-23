/-
Copyright (c) 2025 Grothendieck Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Donato
-/

import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Subobject classifier

Following Section I.3 of [Sheaves in Geometry and Logic][MM92], we introduce the notion
`CategoryTheory.Subobject.Classifier C` of subobject classifier in a category `C`.

## Main definitions

Let `C` refer to a category with a terminal object, denoted by `⊤_ C`.

* `CategoryTheory.Subobject.IsClassifier t` describes what it means for a morphism `t : ⊤_ C ⟶ Ω`
  (called "true" in [MM92]) to be a subobject classifier for `C`.

* `CategoryTheory.Subobject.Classifier C` is the data of such an `Ω` and `t` together with a proof
  that `t` is a subobject classifier for `C`.

* `CategoryTheory.Subobject.HasClassifier C` is the mere existence of a subobject classifier for
  `C`.

* `CategoryTheory.Subobject.cmap` uses the `IsClassifier` property to send every subobject `x` of
  `X` to its characteristic map `χ_ x : X ⟶ Ω`.

* `CategoryTheory.Subobject.compr` sends every map `φ : X ⟶ Ω` to the subobject of `X` whose
  characteristic map is `φ` by pulling back `t` along `φ`. This generalizes the construction of a
  subset "by comprehension" from its characteristic function in set theory.

* `CategoryTheory.Subobject.sub C` is the presheaf that sends every object `X : C` to its category
  of subobjects `Subobject X`, and every morphism `f : X ⟶ Y` to the function
  `Subobject Y → Subobject X` that maps every subobject of `Y` to its pullback along `f`.

## Main statements

* `CategoryTheory.Subobject.hasClassifier_isRepresentable_iff` : a category `C` has a subobject
  classifier `Ω` if and only if the subobjects presheaf `CategoryTheory.Subobject.sub C` is
  representable by `Ω` (Proposition 1 in Section I.3 of [MM92]).

## Notation

* If `x` is a subobject, `χ_ x` denotes the characteristic map of `x` given by the subobject
  classifier.

## Implementation notes

* **TODO**: add a uniqueness theorem for subobject classifiers (up to isomorphism)
* **TODO**: add comments to explain the different steps in the long proof of the "only if" direction
  of `CategoryTheory.Subobject.hasClassifier_isRepresentable_iff`

## References

* [S. MacLane and I. Moerdijk, *Sheaves in geometry and logic: A first introduction to topos
  theory*][MM92]

## Tags

subobject, subobject classifier, representable functor, presheaf, topos theory
-/

universe u v

/-! ### Some general lemmas -/

lemma unique_eq {α : Type u} (h : Unique α) (x y : α) : x = y := by
  simp [Unique.uniq h x, Unique.uniq h y]

namespace CategoryTheory

open CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]

namespace IsPullback

lemma of_iso1 {P P' X Y Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y}
    {fst' : P' ⟶ X} {snd' : P' ⟶ Y}
    (h : IsPullback fst snd f g) (i : P ≅ P')
    (commfst : fst = i.hom ≫ fst')
    (commsnd : snd = i.hom ≫ snd') :
    IsPullback fst' snd' f g := by
  apply IsPullback.of_iso h i (Iso.refl _) (Iso.refl _) (Iso.refl _) <;> aesop_cat

lemma of_iso3 {P X X' Y Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f' : X' ⟶ Z} {fst' : P ⟶ X'}
    (h : IsPullback fst snd f g) (i : X ≅ X')
    (commfst : fst ≫ i.hom = fst')
    (commf : f = i.hom ≫ f') :
    IsPullback fst' snd f' g := by
  apply IsPullback.of_iso h (Iso.refl _) i (Iso.refl _) (Iso.refl _) <;> aesop_cat

end IsPullback

namespace Subobject

/-! ### Additional lemmas about pullbacks and subobjects -/

open Subobject

@[simp]
lemma mk_arrow_mk {X : C} (m : MonoOver X) :
    mk m.arrow = ⟦m⟧ :=
  rfl

section Pullback

lemma isPullback_eq {X Y Z : C} {x x' : Subobject X}
    {f : X ⟶ Z} {g : Y ⟶ Z} {k : (x : C) ⟶ Y} {k' : (x' : C) ⟶ Y}
    (h : IsPullback k x.arrow g f) (h' : IsPullback k' x'.arrow g f) :
    x = x' := by
  let i := @IsPullback.isoIsPullback _ _ _ _ _ _ _ _ _ _ _ _ _ h h'
  apply eq_of_comm i
  simp [i]

lemma isPullback_mk {X Y Z : C}
    (f : Y ⟶ Z) (g : X ⟶ Z) [HasPullback f g] [Mono f] :
    let π₁ := pullback.fst f g;
    let π₂ := pullback.snd f g;
    IsPullback ((underlyingIso π₂).hom ≫ π₁) (mk π₂).arrow f g := by
  intro π₁ π₂
  apply IsPullback.of_iso1 (IsPullback.of_hasPullback f g) (underlyingIso π₂).symm <;> simp [π₁, π₂]

lemma isPullback_eq_mk {X Y Z : C} {x : Subobject X}
    {f : Y ⟶ Z} {g : X ⟶ Z} [HasPullback f g] [Mono f]
    {fst : (x : C) ⟶ Y}
    (h : IsPullback fst x.arrow f g) :
    x = mk (pullback.snd f g) := by
  have h' := isPullback_mk f g
  apply isPullback_eq h h'

variable [HasPullbacks C]

lemma pullback_obj_representative {X Y : C} (f : Y ⟶ X) (x : Subobject X) :
    (pullback f).obj x = mk ((MonoOver.pullback f).obj (representative.obj x)).arrow := by
  induction' x using Quotient.inductionOn' with m
  unfold pullback lower
  rw [mk_arrow_mk]
  dsimp
  apply Quotient.sound
  constructor
  apply Functor.mapIso
  symm
  exact (representativeIso _)

@[simp]
lemma pullback_obj {X Y : C} (f : Y ⟶ X) (x : Subobject X) :
    (pullback f).obj x = mk (pullback.snd x.arrow f) := by
  rw [pullback_obj_representative]
  rfl

end Pullback

/-! ### The notion of subobject classifier -/

section SubobjectClassifier

/-- A monomorphism `f` from the terminal object `⊤_ C` is a subobject classifier when it satisfies
    the universal property that every subobject is uniquely a pullback of `f`.
-/
def IsClassifier [HasTerminal C] {Ω : C} (f : ⊤_ C ⟶ Ω) :=
  Π {X : C} (x : Subobject X),
  Unique {φ : X ⟶ Ω // IsPullback (terminal.from (x : C)) x.arrow f φ}

variable (C : Type u) [Category.{v} C] [HasTerminal C]

/-- The data for a subobject classifier consists of an object `Ω` of "truth values", together with a
    morphism `t : ⊤_ C ⟶ Ω` and a proof that `t` is a subobject classifier.
-/
class Classifier where
  /-- The object of "truth values". -/
  Ω : C
  /-- The subobject classifier, which is a generalized element of `Ω` denoting the truth value that
      is "always true". -/
  t : ⊤_ C ⟶ Ω
  /-- A proof that `t` satisfies the property of being a subobject classifier. -/
  is_classifier : IsClassifier t

/-- The mere existence of a subobject classifier. -/
class HasClassifier : Prop where
  has_classifier : Nonempty (Classifier C)

open Classifier

variable {C : Type u} [Category.{v} C] [HasTerminal C] [Classifier C]

/-- `truth` is the subobject associated to the subobject classifier `t`. -/
noncomputable def truth : Subobject (C := C) Ω := Subobject.mk t

/-- `x.cmap` is the unique characteristic map of subobject `x` given by the `IsClassifier` property.
-/
def cmap {X : C} (x : Subobject X) : X ⟶ Ω :=
  (is_classifier x).default.val

/-- `χ_ x` is short for `x.cmap`. -/
abbrev χ_ {X : C} (x : Subobject X) := x.cmap

variable [HasPullbacks C]

/-- `compr χ` builds the subobject whose characteristic map is `χ` by pulling back `truth` along
    `χ`. This generalizes the construction of a subset "by comprehension" from its characteristic
    function in set theory. -/
noncomputable def compr {X : C} (χ : X ⟶ Ω) : Subobject X :=
  (pullback χ).obj truth

lemma compr_isPullback {X : C} (χ : X ⟶ Ω) :
    IsPullback (terminal.from (compr χ : C)) (compr χ).arrow t χ := by
  have h := IsPullback.of_hasPullback t χ
  let i : (compr χ : C) ≅ Limits.pullback t χ := underlyingIso _
  apply IsPullback.of_iso1 h i.symm _ _ <;> try aesop_cat
  have heq : (compr χ).arrow = (mk (pullback.snd t χ)).arrow := by rfl
  simp [heq, i]

lemma compr_cmap {X : C} (x : Subobject X) :
    compr (χ_ x) = x := by
  have h : IsPullback (terminal.from (x : C)) x.arrow t (χ_ x) :=
    (is_classifier x).default.property
  have h' : IsPullback (terminal.from (compr (χ_ x) : C)) (compr (χ_ x)).arrow t (χ_ x) := by
    apply compr_isPullback
  apply isPullback_eq h' h

lemma cmap_compr {X : C} (φ : X ⟶ Ω) :
    χ_ (compr φ) = φ := by
  have h := compr_isPullback φ
  have h' := compr_isPullback (χ_ (compr φ))
  rw [compr_cmap] at h'
  have heq := unique_eq (is_classifier (compr φ)) ⟨φ, h⟩ ⟨χ_ (compr φ), h'⟩
  simp [← Subtype.mk_eq_mk.1 heq]

end SubobjectClassifier

/-! ### The subobjects presheaf `sub` -/

section SubPresheaf

variable [HasPullbacks C]

/-- `sub` is the presheaf that sends every object `X : C` to its category of subobjects
    `Subobject X`, and every morphism `f : X ⟶ Y` to the function `Subobject Y → Subobject X`
    that maps every subobject of `Y` to its pullback along `f`. -/
noncomputable def sub : Cᵒᵖ ⥤ Type (max u v) where
  obj X := (@Subobject C _ X.unop)

  map f := (pullback f.unop).obj

  map_id := by
    simp only
    intro X
    funext
    rw [unop_id, pullback_id]
    simp

  map_comp := by
    simp only
    intro X Y Z f g
    funext
    rw [unop_comp, pullback_comp]
    simp

end SubPresheaf

/-! ### The representability theorem of subobject classifiers -/

open Classifier

variable [HasTerminal C] [HasPullbacks C]

/-- A category has a subobject classifier if and only if the subobjects functor is representable. -/
theorem isRepresentable_hasClassifier_iff : HasClassifier C ↔ (@sub C).IsRepresentable := by
  constructor <;> intro h

  · obtain ⟨⟨𝒞⟩⟩ := h
    exists Ω
    constructor
    exact {
      /- The correspondence `compr` sending each map `φ : X ⟶ Ω` to the corresponding subobject is a
         bijection with `cmap` as inverse. -/
      homEquiv := {
        toFun := compr
        invFun := cmap
        left_inv := cmap_compr
        right_inv := compr_cmap
      }
      /- Furthermore, this bijection is natural by the fact that two pullback squares placed side by
         side yield a pullback rectangle (lemma `Subobject.pullback_comp`). -/
      homEquiv_comp := by
        intro X X' f g
        simp only [sub, Equiv.coe_fn_mk, compr, Quiver.Hom.unop_op, pullback_comp]
    }

  · obtain ⟨Ω, ⟨⟨θ, hθ⟩⟩⟩ := h

    let φ := fun {X} (x : Subobject X) ↦ θ.symm x
    have hφ : ∀ {X} (χ : X ⟶ Ω), χ = φ (θ χ) := by simp [φ]

    let Ω₀ : Subobject Ω := θ (𝟙 _)
    let t₀ := Ω₀.arrow
    have t₀_mono : Mono t₀ := inferInstance

    have hx_pullback : ∀ {X} (x : Subobject X), x = (pullback (φ x)).obj Ω₀ := by
      intro X x
      have := hθ (θ.symm x) (𝟙 _)
      simp only [Category.comp_id, Equiv.apply_symm_apply] at this
      rw (occs := .pos [1]) [this]
      simp [sub, φ, Ω₀]

    have hx_mk : ∀ {X} (x : Subobject X), x = Subobject.mk (pullback.snd t₀ (φ x)) := by
      intro X x
      rw (occs := .pos [1]) [hx_pullback x, pullback_obj]

    let ι : ∀ {X} (x : Subobject X), (x : C) ≅ Limits.pullback t₀ (φ x) := by
      intro X x
      rw (occs := .pos [1]) [hx_mk x]
      exact (underlyingIso (pullback.snd t₀ (φ x)))

    let π₁ := fun {X} (x : Subobject X) ↦ (ι x).hom ≫ pullback.fst t₀ (φ x)

    have isPullback_φ : ∀ {X} (x : Subobject X), IsPullback (π₁ x) x.arrow t₀ (φ x) := by
      intro X x
      have h := isPullback_mk t₀ (φ x)
      have hx := hx_mk x
      dsimp at h
      rw (occs := .pos [1,2,3]) [hx]
      have h1 : ((underlyingIso (pullback.snd t₀ (φ x))).hom ≫ pullback.fst t₀ (φ x)) =
                (π₁ (Subobject.mk (pullback.snd t₀ (φ x)))) := by
        congr; try exact hx
        dsimp [ι]
        set hc := Eq.symm (congrArg (fun _a ↦ underlying.obj _a ≅ Limits.pullback t₀
                                              (φ (Subobject.mk (pullback.snd t₀ (φ x)))))
                                    (hx_mk (Subobject.mk (pullback.snd t₀ (φ x)))))
        have := cast_heq hc ((underlyingIso (pullback.snd t₀
                                             (φ (Subobject.mk (pullback.snd t₀ (φ x)))))))
        symm
        apply HEq.trans this
        symm
        congr
      rw [← h1]
      exact h

    have isPullback_uniq : ∀ {X} (x : Subobject X) ψ χ, IsPullback ψ x.arrow t₀ χ → χ = φ x := by
      intro X x ψ χ hχ
      rw [hφ χ]
      congr
      specialize hθ χ (𝟙 _)
      rw [Category.comp_id] at hθ
      rw [hθ]
      dsimp [sub]
      rw [pullback_obj, isPullback_eq_mk hχ]
      rfl

    let classifier : ∀ {X} (x : Subobject X), Unique {χ // IsPullback (π₁ x) x.arrow t₀ χ} := by
      intro X x
      refine ⟨⟨φ x, isPullback_φ x⟩, ?uniq⟩
      intro h
      obtain ⟨χ, hχ⟩ := h
      congr
      exact (isPullback_uniq _ _ _ hχ)

    have isTerminal_Ω₀ : IsTerminal (Ω₀ : C) := by
      have : (X : C) → Unique (X ⟶ Ω₀) := by
        intro X
        let s := Subobject.mk (𝟙 X)
        let φ' := π₁ s
        let i : X ≅ s := by dsimp [s]; exact (underlyingIso (𝟙 X)).symm
        let φX := (i.hom ≫ φ')
        refine { default := φX, uniq := ?_ }
        intro φX'
        dsimp [default]
        have hψ : ∀ ψ, IsPullback ψ (𝟙 X) t₀ (ψ ≫ t₀) := by
          intro ψ
          constructor
          · constructor
            apply PullbackCone.IsLimit.mk (lift := fun c ↦ c.snd) <;> intro c
            · apply Mono.right_cancellation (f := t₀)
              rw [c.condition]
              simp
            · simp
            · intro m hm1 hm2
              rw [← hm2]
              simp
          · simp
        have hX := hψ φX
        have hX' := hψ φX'
        have hφX := isPullback_uniq s (π₁ s) (φX ≫ t₀)
        have hφX' := isPullback_uniq s (i.inv ≫ φX') (φX' ≫ t₀)
        have h : φX ≫ t₀ = φX' ≫ t₀ := by
          rw [hφX, hφX']
          · apply IsPullback.of_iso1 hX' i
            · simp
            · simp [i, s]
          · apply IsPullback.of_iso1 hX i
            · simp only [φX, φ']
            · simp [i, s]
        exact Mono.right_cancellation _ _ h.symm
      apply IsTerminal.ofUnique

    have i : ⊤_ C ≅ Ω₀ := by
      apply IsTerminal.uniqueUpToIso
      exact terminalIsTerminal
      exact isTerminal_Ω₀

    constructor; constructor
    exact {
      Ω := Ω
      t := i.hom ≫ t₀
      is_classifier := by
        intro X x
        refine { default := ⟨φ x, ?_⟩, uniq := ?_ }
        · apply IsPullback.of_iso3 (isPullback_φ x) i.symm
          · apply unique_eq (uniqueToTerminal _)
          · simp
        · simp only [Subtype.forall, Subtype.mk.injEq]
          intro χ hχ
          apply isPullback_uniq x (terminal.from (x : C) ≫ i.hom) χ
          apply IsPullback.of_iso3 hχ i <;> rfl
    }

end Subobject
end CategoryTheory
