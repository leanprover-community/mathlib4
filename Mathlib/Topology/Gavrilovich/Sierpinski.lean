/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.CategoryTheory.ChosenRepresentation
public import Mathlib.CategoryTheory.ConcreteCategory.Representable
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.Subobject
public import Mathlib.Order.OrdContinuous
public import Mathlib.Tactic.Gavrilovich.Elab.Full
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology
public import Mathlib.Topology.Category.TopCat.Limits.AlexandrovDiscrete
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Gavrilovich.Model
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Sets.Closeds


/-!
# The Sierpinski space `⌜T → F⌟` and the frame `X ⟶ ⌜T → F⌟`

The Sierpinski space is the diagram space `⌜T → F⌟` itself (not `↧(ULift Prop)`), so that
`decide`, `pt_cases` and `cbv` keep working on it, and so that lemmas about morphisms into it are
keyed on `↑⌜T → F⌟`, which `simp` never rewrites (unlike `↑(TopCat.of (ULift Prop))`, which
`TopCat.coe_of` rewrites, so that every such lemma needs a `dsimp`-normalised left-hand side).

## Points

`⌜T → F⌟` is a `BooleanAlgebra` (`Space.lean`, given the `BoundedOrder` here). The `simp` normal
forms push connectives down to atoms `a = pt(T)` and `a = pt(F)` (`sup_eq_T`, `inf_eq_F`, ...).
For the *value* `f x` of a morphism, `f x = pt(F)` further becomes `¬f x = pt(T)` (`apply_eq_F`),
so that statements about morphisms become formulas of `Prop` over atoms `f x = pt(T)`, for `simp`,
`tauto` and `grind`. (This is why `Space.not_eq_iff_eq_hnot`, which rewrites the other way, is not
a `simp` lemma.) Bare points keep `a = pt(F)`, an equation to substitute, so that enumerations over
points (`Space.forall_or_eq_imp'`, `pt_cases`) still work.

## Morphisms

`X ⟶ ⌜T → F⌟` is `Opens X` (`Sierpinski.equivOpens`, `Sierpinski.orderIso`; also
`Sierpinski.equivCloseds`); `Opens.functor` is represented by `⌜T → F⌟`, with universal element
`{pt(T)}`. It is an `Order.Frame`, with
* `f ⊔ g` and `f ⊓ g` *defined* as `lift f g ≫ Space.orHom` and `lift f g ≫ Space.andHom`, so that
  the equalizer condition of `O2C1` is `Disjoint f g` and the pullback condition of `O1C2` is
  `Codisjoint f g`, by `rfl`;
* `⊤`, `⊥` constant, and `sSup` pointwise;
* `sInf`, `ᶜ` and `⇨` the interiors of the pointwise operations, through `Opens X`.

Precomposition preserves `⊔`, `⊓`, `⊤`, `⊥` and `⨆` (but not `ᶜ` or `⇨`).

## Implementation notes

Don't write `simp [eq_bot_iff]` or `simp [eq_top_iff]`: they loop against `le_bot_iff` and
`top_le_iff`, which is reported as a failure to synthesize `OrderBot`/`OrderTop`. Use
`Sierpinski.eq_bot_iff_apply` and `Sierpinski.eq_top_iff_apply`, or `rw`.

This file and `Mathlib.Tactic.Gavrilovich.Lemmas2` (the same API on `↧(ULift Prop)`) declare the
same names and can't be imported together. `Mathlib.Tactic.Gavrilovich.Cbv` imports this file, for
`IsOpen.indicatorHom_apply` and `IsClosed.indicatorHom_apply`.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open ConcreteCategory renaming ofHom → CCofHom
open TopCat Topology TopologicalSpace Set Gavrilovich

@[expose] public section

--Mathlib.Data.Set.UnionLift


-- TODO: upstream to `Mathlib.Topology.Category.TopCat.Opens`


namespace Sierpinski

/-! ### Points -/

@[simps -isSimp top bot]
instance : BoundedOrder.{u} ⌜T → F⌟ where
  top := pt(T)
  le_top := by intro x; pt_cases x <;> decide
  bot := pt(F)
  bot_le := by intro x; pt_cases x <;> decide

instance : IsPartialOrder ⌜T → F⌟.{u} (· ≤ ·) where
  antisymm a b h₁ h₂ := by pt_cases a <;> pt_cases b <;> simp +decide at h₁ h₂ ⊢

@[simp] lemma top_eq : (⊤ : ⌜T → F⌟.{u}) = pt(T) := rfl
@[simp] lemma bot_eq : (⊥ : ⌜T → F⌟.{u}) = pt(F) := rfl

lemma isOpen_singleton_T : IsOpen ({pt(T)} : Set ⌜T → F⌟.{u}) := by decide
lemma isClosed_singleton_F : IsClosed ({pt(F)} : Set ⌜T → F⌟.{u}) := by decide

@[simp] lemma nhds_F : 𝓝 (pt(F) : ⌜T → F⌟.{u}) = ⊤ := by
  ext s
  have : Ici (pt(F) : ⌜T → F⌟.{u}) = univ := by ext x; pt_cases x <;> simp +decide
  rw [IsUpperSet.nhds_eq_principal_Ici, Filter.mem_principal, this]; simp

@[simp] lemma nhds_T : 𝓝 (pt(T) : ⌜T → F⌟.{u}) = Filter.principal {pt(T)} := by
  rw [IsUpperSet.nhds_eq_principal_Ici]; congr 1; ext x; pt_cases x <;> simp +decide

/-- `Space.andHom` on the Sierpinski space. -/
abbrev andHom : ⌜T → F⌟.{u} ⊗ ⌜T → F⌟.{u} ⟶ ⌜T → F⌟.{u} := Space.andHom
/-- `Space.orHom` on the Sierpinski space. -/
abbrev orHom : ⌜T → F⌟.{u} ⊗ ⌜T → F⌟.{u} ⟶ ⌜T → F⌟.{u} := Space.orHom

variable {a b : ⌜T → F⌟.{u}}

lemma eq_T_or_eq_F (a : ⌜T → F⌟.{u}) : a = pt(T) ∨ a = pt(F) := by pt_cases a <;> simp

lemma eq_F_iff : a = pt(F) ↔ ¬a = pt(T) := by pt_cases a <;> simp +decide
lemma F_eq_iff : pt(F) = a ↔ ¬a = pt(T) := by pt_cases a <;> simp +decide
lemma ne_T_iff : a ≠ pt(T) ↔ a = pt(F) := eq_F_iff.symm
@[simp] lemma sup_eq_T : a ⊔ b = pt(T) ↔ a = pt(T) ∨ b = pt(T) := by
  pt_cases a <;> pt_cases b <;> simp +decide
@[simp] lemma inf_eq_T : a ⊓ b = pt(T) ↔ a = pt(T) ∧ b = pt(T) := by
  pt_cases a <;> pt_cases b <;> simp +decide
@[simp] lemma compl_eq_T : aᶜ = pt(T) ↔ a = pt(F) := by pt_cases a <;> simp +decide
@[simp] lemma sup_eq_F : a ⊔ b = pt(F) ↔ a = pt(F) ∧ b = pt(F) := by
  pt_cases a <;> pt_cases b <;> simp +decide
@[simp] lemma inf_eq_F : a ⊓ b = pt(F) ↔ a = pt(F) ∨ b = pt(F) := by
  pt_cases a <;> pt_cases b <;> simp +decide
@[simp] lemma compl_eq_F : aᶜ = pt(F) ↔ a = pt(T) := by pt_cases a <;> simp +decide
@[simp] lemma compl_T : (pt(T) : ⌜T → F⌟.{u})ᶜ = pt(F) := by decide
@[simp] lemma compl_F : (pt(F) : ⌜T → F⌟.{u})ᶜ = pt(T) := by decide

@[simp] lemma inf_T : a ⊓ pt(T) = a := inf_top_eq a
@[simp] lemma T_inf : pt(T) ⊓ a = a := top_inf_eq a
@[simp] lemma inf_F : a ⊓ pt(F) = pt(F) := inf_bot_eq a
@[simp] lemma F_inf : pt(F) ⊓ a = pt(F) := bot_inf_eq a
@[simp] lemma sup_T : a ⊔ pt(T) = pt(T) := sup_top_eq a
@[simp] lemma T_sup : pt(T) ⊔ a = pt(T) := top_sup_eq a
@[simp] lemma sup_F : a ⊔ pt(F) = a := sup_bot_eq a
@[simp] lemma F_sup : pt(F) ⊔ a = a := bot_sup_eq a

lemma le_iff : a ≤ b ↔ (a = pt(T) → b = pt(T)) := by
  pt_cases a <;> pt_cases b <;> simp +decide

/-- The model `ULift Prop ≃ₜ ⌜T → F⌟`. -/
noncomputable abbrev toSpace : ULift.{u} Prop ≃ₜ ⌜T → F⌟.{u} := Model.homeo

@[simp] lemma toSpace_eq_T {p : ULift.{u} Prop} : toSpace p = pt(T) ↔ p.down := by
  obtain ⟨p⟩ := p; by_cases hp : p <;> simp [toSpace, hp]

open Classical in
/-- `⌜T → F⌟` is homeomorphic to `Prop`. -/
@[simps!]
noncomputable def homeoProp : (⌜T → F⌟ : Type u) ≃ₜ Prop :=
  toSpace.symm.trans Homeomorph.ulift

/-! ### Morphisms as open sets -/

variable {X Y : TopCat.{u}}

/-- The open set classified by `f`: the preimage of `pt(T)`. -/
def asOpen (f : X ⟶ ⌜T → F⌟) : Opens X :=
  ⟨f ⁻¹' {pt(T)}, isOpen_singleton_T.preimage f.hom.continuous⟩

@[simp] lemma mem_asOpen {f : X ⟶ ⌜T → F⌟} {x : X} : x ∈ asOpen f ↔ f x = pt(T) := .rfl

/-! The values `f x` of a morphism are read as propositions `f x = pt(T)`. (Bare points `a` are
not: there, `a = pt(F)` is an equation to substitute, as in `Space.forall_or_eq_imp'`.) -/

@[simp] lemma apply_eq_F {f : X ⟶ ⌜T → F⌟} {x : X} : f x = pt(F) ↔ ¬f x = pt(T) := eq_F_iff
@[simp] lemma F_eq_apply {f : X ⟶ ⌜T → F⌟} {x : X} : pt(F) = f x ↔ ¬f x = pt(T) := F_eq_iff
@[simp] lemma T_eq_apply {f : X ⟶ ⌜T → F⌟} {x : X} : pt(T) = f x ↔ f x = pt(T) := eq_comm
@[simp] lemma apply_eq_apply_iff {f : X ⟶ ⌜T → F⌟} {g : Y ⟶ ⌜T → F⌟} {x : X} {y : Y} :
    f x = g y ↔ (f x = pt(T) ↔ g y = pt(T)) := by
  rcases eq_T_or_eq_F (f x) with h₁ | h₁ <;> rcases eq_T_or_eq_F (g y) with h₂ | h₂ <;>
    simp [h₁, h₂]

end Sierpinski

/-! ### `Closeds` as a functor -/


/-! ### The representations -/

namespace Sierpinski

variable {X Y : TopCat.{u}}

/-- The generic open subobject of the Sierpinski space. Every open embedding is a pullback of
`truth` along the `indicatorHom` of its range. -/
@[simps! +dsimpLhs hom_apply]
def truth : 𝟙_ TopCat.{u} ⟶ ⌜T → F⌟ := ConcreteCategory.homOfElement pt(T)

/-- The generic closed subobject of the Sierpinski space. Every closed embedding is a pullback of
`untruth` along the `indicatorHom` of its range. -/
@[simps! +dsimpLhs hom_apply]
def untruth : 𝟙_ TopCat.{u} ⟶ ⌜T → F⌟ := ConcreteCategory.homOfElement pt(F)

/-- The classifying map of `U`, which is `pt(T)` on `U` and `pt(F)` off it. This is only used to
construct the chosen representations; use `Opens.indicatorHom` and `Closeds.indicatorHom`. -/
@[no_expose]
noncomputable def classify (U : Opens X) : X ⟶ ⌜T → F⌟ :=
  CCofHom <| (toSpace : C(ULift.{u} Prop, ⌜T → F⌟.{u})).comp
    ⟨fun x ↦ ULift.up (x ∈ U), continuous_uliftUp.comp (continuous_Prop.mpr U.isOpen)⟩

@[simp] lemma classify_apply_eq_T {U : Opens X} {x : X} : classify U x = pt(T) ↔ x ∈ U := by
  simp [classify]

@[ext] lemma hom_ext {f g : X ⟶ ⌜T → F⌟} (h : ∀ x, f x = pt(T) ↔ g x = pt(T)) : f = g := by
  ext x; specialize h x
  rcases eq_T_or_eq_F (f x) with h₁ | h₁ <;> rcases eq_T_or_eq_F (g x) with h₂ | h₂ <;>
    simp_all [-apply_eq_F]

/-- The closed set classified by `f`: the preimage of `pt(F)`. -/
def asClosed (f : X ⟶ ⌜T → F⌟) : Closeds X :=
  ⟨f ⁻¹' {pt(F)}, isClosed_singleton_F.preimage f.continuous⟩

@[simp] lemma mem_asClosed {f : X ⟶ ⌜T → F⌟} {x : X} : x ∈ asClosed f ↔ f x = pt(F) := .rfl

/-- `X ⟶ ⌜T → F⌟` is `Opens X`, by preimages of `pt(T)`. -/
@[simps]
noncomputable def equivOpens : (X ⟶ ⌜T → F⌟) ≃ Opens X where
  toFun := asOpen
  invFun := classify
  left_inv f := by ext; simp
  right_inv U := by ext; simp

/-- `X ⟶ ⌜T → F⌟` is `Closeds X`, by preimages of `pt(F)`. -/
@[simps]
noncomputable def equivCloseds : (X ⟶ ⌜T → F⌟) ≃ Closeds X where
  toFun := asClosed
  invFun C := classify C.compl
  left_inv f := by ext; simp [Closeds.compl]
  right_inv C := by ext; simp [Closeds.compl]

/-- `Opens.functor` is represented by `⌜T → F⌟`, with universal element `{pt(T)}`. -/
noncomputable instance : Opens.functor.ChosenRepresentation where
  obj := ⌜T → F⌟
  reprBy :=
  { homEquiv := equivOpens
    homEquiv_comp _ _ := rfl }

/-- `Closeds.functor` is represented by `⌜T → F⌟`, with universal element `{pt(F)}`. -/
noncomputable instance : Closeds.functor.ChosenRepresentation where
  obj := ⌜T → F⌟
  reprBy :=
  { homEquiv := equivCloseds
    homEquiv_comp _ _ := rfl }

end Sierpinski

/-- The classifying map of `U`, which is `pt(T)` on `U` and `pt(F)` off it: the morphism that
`Opens.functor`'s chosen representation assigns to `U`. -/
noncomputable def TopologicalSpace.Opens.indicatorHom {X : TopCat.{u}} (U : Opens X) :
    X ⟶ ⌜T → F⌟ :=
  Opens.functor.homFromElement U

/-- The classifying map of the open set `U`. -/
noncomputable abbrev IsOpen.indicatorHom {X : TopCat.{u}} {U : Set X} (hU : IsOpen U) :
    X ⟶ ⌜T → F⌟ :=
  Opens.indicatorHom ⟨U, hU⟩

/-- The classifying map of the complement of `C`, which is `pt(F)` on `C` and `pt(T)` off it: the
morphism that `Closeds.functor`'s chosen representation assigns to `C`. -/
noncomputable def TopologicalSpace.Closeds.indicatorHom {X : TopCat.{u}} (C : Closeds X) :
    X ⟶ ⌜T → F⌟ :=
  Closeds.functor.homFromElement C

/-- The classifying map of the complement of the closed set `C`. -/
noncomputable abbrev IsClosed.indicatorHom {X : TopCat.{u}} {C : Set X} (hC : IsClosed C) :
    X ⟶ ⌜T → F⌟ :=
  Closeds.indicatorHom ⟨C, hC⟩

namespace Sierpinski

variable {X Y : TopCat.{u}}

lemma indicatorHom_eq_classify (U : Opens X) : U.indicatorHom = classify U := rfl
lemma closeds_indicatorHom_eq (C : Closeds X) : C.indicatorHom = C.compl.indicatorHom := rfl

@[simp] lemma homFromElement_eq (U : Opens X) :
    Opens.functor.homFromElement U = U.indicatorHom := rfl
@[simp] lemma closeds_homFromElement_eq (C : Closeds X) :
    Closeds.functor.homFromElement C = C.indicatorHom := rfl

@[simp] lemma indicatorHom_apply_eq_T {U : Opens X} {x : X} :
    U.indicatorHom x = pt(T) ↔ x ∈ U :=
  classify_apply_eq_T

@[simp] lemma closeds_indicatorHom_apply_eq_T {C : Closeds X} {x : X} :
    C.indicatorHom x = pt(T) ↔ x ∉ C :=
  classify_apply_eq_T

@[simp] lemma asOpen_indicatorHom (U : Opens X) : asOpen U.indicatorHom = U :=
  equivOpens.right_inv U
@[simp] lemma indicatorHom_asOpen (f : X ⟶ ⌜T → F⌟) : (asOpen f).indicatorHom = f :=
  equivOpens.left_inv f
@[simp] lemma asClosed_indicatorHom (C : Closeds X) : asClosed C.indicatorHom = C :=
  equivCloseds.right_inv C
@[simp] lemma closeds_indicatorHom_asClosed (f : X ⟶ ⌜T → F⌟) : (asClosed f).indicatorHom = f :=
  equivCloseds.left_inv f
@[simp] lemma asOpen_closeds_indicatorHom (C : Closeds X) : asOpen C.indicatorHom = C.compl :=
  asOpen_indicatorHom C.compl
@[simp] lemma asClosed_opens_indicatorHom (U : Opens X) : asClosed U.indicatorHom = U.compl := by
  ext; simp [Opens.compl]

/-- The same map classifies both `U : Opens X` and its complement as a closed set.
(Not to be confused with the complement of the map, which classifies the interior of the
complement.) -/
@[simp]
lemma compl_indicatorHom (U : Opens X) : U.compl.indicatorHom = U.indicatorHom := by
  ext; simp [Opens.compl]

/-- The same map classifies both `C : Closeds X` and its complement as an open set.
(Not to be confused with the complement of the map, which classifies the interior of the
complement.) -/
@[simp]
lemma closeds_compl_indicatorHom (C : Closeds X) : C.compl.indicatorHom = C.indicatorHom := by
  ext; simp [Closeds.compl]

@[simp] lemma comp_apply_eq_T {f : Y ⟶ X} {g : X ⟶ ⌜T → F⌟} {y : Y} :
    (f ≫ g) y = pt(T) ↔ g (f y) = pt(T) := .rfl

/-! The rest of the API comes from the chosen representations. -/

@[reassoc (attr := simp)]
lemma comp_indicatorHom (f : Y ⟶ X) (U : Opens X) :
    f ≫ U.indicatorHom = Opens.indicatorHom ⟨f ⁻¹' U, U.isOpen.preimage f.hom.continuous⟩ :=
  Opens.functor.homFromElement_comp U f

@[reassoc (attr := simp)]
lemma comp_closeds_indicatorHom (f : Y ⟶ X) (C : Closeds X) :
    f ≫ C.indicatorHom = Closeds.indicatorHom ⟨f ⁻¹' C, C.isClosed.preimage f.hom.continuous⟩ :=
  Closeds.functor.homFromElement_comp C f

lemma indicatorHom_injective :
    Function.Injective (Opens.indicatorHom : Opens X → (X ⟶ ⌜T → F⌟)) :=
  Opens.functor.homFromElement_injective

lemma closeds_indicatorHom_injective :
    Function.Injective (Closeds.indicatorHom : Closeds X → (X ⟶ ⌜T → F⌟)) :=
  Closeds.functor.homFromElement_injective

@[simp] lemma indicatorHom_inj {U V : Opens X} : U.indicatorHom = V.indicatorHom ↔ U = V :=
  Opens.functor.homFromElement_inj ..

@[simp] lemma closeds_indicatorHom_inj {C D : Closeds X} :
    C.indicatorHom = D.indicatorHom ↔ C = D :=
  Closeds.functor.homFromElement_inj ..

lemma asOpen_injective : Function.Injective (asOpen : (X ⟶ ⌜T → F⌟) → _) :=
  equivOpens.injective

lemma eq_indicatorHom_iff (f : X ⟶ ⌜T → F⌟) (U : Opens X) :
    f = U.indicatorHom ↔ asOpen f = U := by
  rw [← equivOpens.injective.eq_iff]; simp

lemma eq_closeds_indicatorHom_iff (f : X ⟶ ⌜T → F⌟) (C : Closeds X) :
    f = C.indicatorHom ↔ asClosed f = C := by
  rw [← equivCloseds.injective.eq_iff]; simp

/-- The universal open set is `{pt(T)}`, ... -/
lemma functor_univ : Opens.functor.univ = (⟨{pt(T)}, isOpen_singleton_T⟩ : Opens ⌜T → F⌟.{u}) :=
  rfl

/-- ... whose classifying map is the identity. -/
@[simp] lemma indicatorHom_functor_univ : Opens.functor.univ.indicatorHom = 𝟙 ⌜T → F⌟.{u} :=
  Opens.functor.homFromElement_univ

/-- The universal closed set is `{pt(F)}`, ... -/
lemma closeds_functor_univ :
    Closeds.functor.univ = (⟨{pt(F)}, isClosed_singleton_F⟩ : Closeds ⌜T → F⌟.{u}) :=
  rfl

/-- ... whose classifying map is the identity. -/
@[simp] lemma closeds_indicatorHom_functor_univ :
    Closeds.functor.univ.indicatorHom = 𝟙 ⌜T → F⌟.{u} :=
  Closeds.functor.homFromElement_univ

/-- Every open set is the pullback of the universal open set along its classifying map. -/
lemma asOpen_eq_comap_univ (f : X ⟶ ⌜T → F⌟) : asOpen f = Opens.comap f.hom Opens.functor.univ :=
  rfl

/-- Every open set is the pullback of the universal open set along its classifying map. -/
lemma inclusion'_isPullback (U : Opens X) :
    IsPullback U.inclusion' (isTerminalTensorUnit.from _) U.indicatorHom truth := by
  fapply IsPullback.mk'
  · ext x; simp [-Opens.coe_inclusion', truth]; simp [x.property]
  · rintro Y v₁ v₂ hv -; exact Mono.right_cancellation _ _ hv
  · intro T v _ hv
    have hv' x := by simpa [truth] using TopCat.ext_iff.mp hv x
    use ConcreteCategory.ofHom ⟨_, Continuous.subtype_coind v.continuous hv'⟩, by ext x; simp
    exact isTerminalTensorUnit.hom_ext ..

/-- Every closed set is the pullback of the universal closed set along its classifying map. -/
lemma closeds_inclusion'_isPullback (U : Closeds X) :
    IsPullback U.inclusion' (isTerminalTensorUnit.from _) U.indicatorHom untruth := by
  fapply IsPullback.mk'
  · ext x; simp [-Closeds.coe_inclusion', untruth]; simp [x.property]
  · rintro Y v₁ v₂ hv -; exact Mono.right_cancellation _ _ hv
  · intro T v _ hv
    have hv' x := by simpa [untruth] using TopCat.ext_iff.mp hv x
    use ConcreteCategory.ofHom ⟨_, Continuous.subtype_coind v.continuous hv'⟩,
      by ext x; simp
    exact isTerminalTensorUnit.hom_ext ..

end Sierpinski

open Classical in
/-- `hU.indicatorHom x` as an `if`; used by `Gavrilovich.Space.cbvIndicatorHom`. -/
lemma IsOpen.indicatorHom_apply {X : TopCat.{u}} {U : Set X} (hU : IsOpen U) (x : X) :
    hU.indicatorHom x = if x ∈ U then pt(T) else pt(F) := by
  by_cases hx : x ∈ U <;> simp [hx]

open Classical in
/-- `hC.indicatorHom x` as an `if`; used by `Gavrilovich.Space.cbvIndicatorHom`. -/
lemma IsClosed.indicatorHom_apply {X : TopCat.{u}} {C : Set X} (hC : IsClosed C) (x : X) :
    hC.indicatorHom x = if x ∈ C then pt(F) else pt(T) := by
  by_cases hx : x ∈ C <;> simp [hx]

namespace Sierpinski

variable {X Y : TopCat.{u}}

/-- Quantifying over `X ⟶ ⌜T → F⌟` is quantifying over open sets. -/
lemma exists_hom {P : (X ⟶ ⌜T → F⌟.{u}) → Prop} :
    (∃ f, P f) ↔ ∃ (U : Set X) (hU : IsOpen U), P hU.indicatorHom :=
  ⟨fun ⟨f, hf⟩ ↦ ⟨_, (asOpen f).isOpen, by convert hf; exact indicatorHom_asOpen f⟩,
    fun ⟨_, _, h⟩ ↦ ⟨_, h⟩⟩

/-- Quantifying over `X ⟶ ⌜T → F⌟` is quantifying over open sets. -/
lemma forall_hom {P : (X ⟶ ⌜T → F⌟.{u}) → Prop} :
    (∀ f, P f) ↔ ∀ (U : Set X) (hU : IsOpen U), P hU.indicatorHom :=
  ⟨fun h _ _ ↦ h _, fun h f ↦ by convert h _ (asOpen f).isOpen; exact (indicatorHom_asOpen f).symm⟩

/-! ### The frame `X ⟶ ⌜T → F⌟` -/


instance : Max (X ⟶ ⌜T → F⌟) := ⟨fun f g ↦ lift f g ≫ orHom⟩
instance : Min (X ⟶ ⌜T → F⌟) := ⟨fun f g ↦ lift f g ≫ andHom⟩
instance : Top (X ⟶ ⌜T → F⌟) := ⟨CCofHom (.const _ pt(T))⟩
instance : Bot (X ⟶ ⌜T → F⌟) := ⟨CCofHom (.const _ pt(F))⟩
noncomputable instance : SupSet (X ⟶ ⌜T → F⌟) :=
  ⟨fun s ↦ Opens.indicatorHom (⨆ f ∈ s, asOpen f)⟩
noncomputable instance : InfSet (X ⟶ ⌜T → F⌟) :=
  ⟨fun s ↦ Opens.indicatorHom (⨅ f ∈ s, asOpen f)⟩
noncomputable instance : HImp (X ⟶ ⌜T → F⌟) :=
  ⟨fun f g ↦ Opens.indicatorHom (asOpen f ⇨ asOpen g)⟩
noncomputable instance : Compl (X ⟶ ⌜T → F⌟) := ⟨fun f ↦ Opens.indicatorHom (asOpen f)ᶜ⟩
instance : LE (X ⟶ ⌜T → F⌟) := ⟨fun f g ↦ ∀ x, f x ≤ g x⟩
instance : LT (X ⟶ ⌜T → F⌟) := ⟨fun f g ↦ f ≤ g ∧ ¬g ≤ f⟩

@[simp] lemma lift_comp_orHom (f g : X ⟶ ⌜T → F⌟) : lift f g ≫ orHom = f ⊔ g := rfl
@[simp] lemma lift_comp_andHom (f g : X ⟶ ⌜T → F⌟) : lift f g ≫ andHom = f ⊓ g := rfl

variable {f g : X ⟶ ⌜T → F⌟} {x : X}

/-! These hold by `rfl`, but are deliberately not proved by `rfl`, so that they are not `dsimp`
lemmas: `simp` would otherwise also use them to `dsimp` implicit type arguments, such as the
codomain `{y // f y = ⊥ y}` of an equivalence onto an equalizer, rewriting some occurrences of a
type but not others, after which lemmas like `Equiv.coe_fn_mk` no longer match. -/

@[simp] lemma sup_apply : (f ⊔ g) x = f x ⊔ g x := Space.orHom_apply_prod (f x) (g x)
@[simp] lemma inf_apply : (f ⊓ g) x = f x ⊓ g x := Space.andHom_apply_prod (f x) (g x)
@[simp] lemma top_apply : (⊤ : X ⟶ ⌜T → F⌟) x = pt(T) := ContinuousMap.const_apply _ x
@[simp] lemma bot_apply : (⊥ : X ⟶ ⌜T → F⌟) x = pt(F) := ContinuousMap.const_apply _ x
@[simp] lemma sSup_apply_eq_T {s : Set (X ⟶ ⌜T → F⌟)} :
    sSup s x = pt(T) ↔ ∃ f ∈ s, f x = pt(T) := by
  simp [SupSet.sSup]

lemma le_def : f ≤ g ↔ ∀ x, f x = pt(T) → g x = pt(T) := by
  change (∀ x, f x ≤ g x) ↔ _; simp only [le_iff]

@[mono, gcongr]
lemma asOpen_le : asOpen f ≤ asOpen g ↔ f ≤ g := by
  change (∀ x, x ∈ asOpen f → x ∈ asOpen g) ↔ _; simp [le_def]

noncomputable instance instFrame : Order.Frame (X ⟶ ⌜T → F⌟) :=
  asOpen_injective.frame _ asOpen_le (by simp [asOpen_le, LT.lt])
    (fun _ _ ↦ by ext; simp) (fun _ _ ↦ by ext; simp)
    (fun _ ↦ asOpen_indicatorHom _) (fun _ ↦ asOpen_indicatorHom _)
    (by ext; simp) (by ext; simp) (fun _ ↦ asOpen_indicatorHom _)
    (fun _ _ ↦ asOpen_indicatorHom _)

/-- `asOpen` as an order isomorphism. -/
@[simps! apply symm_apply]
noncomputable def orderIso : (X ⟶ ⌜T → F⌟) ≃o Opens X where
  toEquiv := equivOpens
  map_rel_iff' := asOpen_le

lemma coe_orderIso : (orderIso : (X ⟶ ⌜T → F⌟) → Opens X) = asOpen := rfl
lemma coe_orderIso_symm : (orderIso.symm : Opens X → (X ⟶ ⌜T → F⌟)) = Opens.indicatorHom := rfl

@[simp] lemma asOpen_sup : asOpen (f ⊔ g) = asOpen f ⊔ asOpen g := orderIso.map_sup f g
@[simp] lemma asOpen_inf : asOpen (f ⊓ g) = asOpen f ⊓ asOpen g := orderIso.map_inf f g
@[simp] lemma asOpen_sSup (s : Set (X ⟶ ⌜T → F⌟)) : asOpen (sSup s) = ⨆ f ∈ s, asOpen f :=
  orderIso.map_sSup s
@[simp] lemma asOpen_iSup {ι} (f : ι → (X ⟶ ⌜T → F⌟)) : asOpen (⨆ i, f i) = ⨆ i, asOpen (f i) :=
  orderIso.map_iSup f
@[simp] lemma asOpen_sInf (s : Set (X ⟶ ⌜T → F⌟)) : asOpen (sInf s) = ⨅ f ∈ s, asOpen f :=
  orderIso.map_sInf s
@[simp] lemma asOpen_iInf {ι} (f : ι → (X ⟶ ⌜T → F⌟)) : asOpen (⨅ i, f i) = ⨅ i, asOpen (f i) :=
  orderIso.map_iInf f

@[simp] lemma indicatorHom_top : (⊤ : Opens X).indicatorHom = ⊤ := by ext; simp
@[simp] lemma indicatorHom_bot : (⊥ : Opens X).indicatorHom = ⊥ := by ext; simp
lemma indicatorHom_sup (U V : Opens X) :
    (U ⊔ V).indicatorHom = U.indicatorHom ⊔ V.indicatorHom :=
  orderIso.symm.map_sup U V
lemma indicatorHom_inf (U V : Opens X) :
    (U ⊓ V).indicatorHom = U.indicatorHom ⊓ V.indicatorHom :=
  orderIso.symm.map_inf U V

@[simp] lemma asClosed_sup : asClosed (f ⊔ g) = asClosed f ⊓ asClosed g := by
  ext; simp [asClosed]
@[simp] lemma asClosed_inf : asClosed (f ⊓ g) = asClosed f ⊔ asClosed g := by
  ext; simp [asClosed]
lemma closeds_indicatorHom_sup (C D : Closeds X) :
    (C ⊔ D).indicatorHom = C.indicatorHom ⊓ D.indicatorHom := by
  ext; simp
lemma closeds_indicatorHom_inf (C D : Closeds X) :
    (C ⊓ D).indicatorHom = C.indicatorHom ⊔ D.indicatorHom := by
  ext; simp [-not_and, not_and_or]

@[simp] lemma iSup_apply_eq_T {ι} {f : ι → (X ⟶ ⌜T → F⌟)} :
    (⨆ i, f i) x = pt(T) ↔ ∃ i, f i x = pt(T) := by
  simp [iSup]

/-- `ᶜ` is not pointwise: it is the interior of the pointwise complement. -/
lemma compl_apply_eq_T : fᶜ x = pt(T) ↔ x ∈ interior {x | ¬f x = pt(T)} := by
  change (asOpen f)ᶜ.indicatorHom x = pt(T) ↔ _
  rw [indicatorHom_apply_eq_T, ← SetLike.mem_coe, Opens.coe_compl_eq_interior_compl]; rfl

lemma eq_bot_iff_apply : f = ⊥ ↔ ∀ x, ¬f x = pt(T) := by
  rw [eq_bot_iff, le_def]; simp

lemma eq_top_iff_apply : f = ⊤ ↔ ∀ x, f x = pt(T) := by
  rw [eq_top_iff, le_def]; simp

lemma disjoint_iff_apply : Disjoint f g ↔ ∀ x, ¬(f x = pt(T) ∧ g x = pt(T)) := by
  simp [disjoint_iff, eq_bot_iff_apply]

lemma codisjoint_iff_apply : Codisjoint f g ↔ ∀ x, f x = pt(T) ∨ g x = pt(T) := by
  simp [codisjoint_iff, eq_top_iff_apply]

@[simp] lemma disjoint_indicatorHom {U V : Opens X} :
    Disjoint U.indicatorHom V.indicatorHom ↔ Disjoint (U : Set X) V := by
  simp [disjoint_iff_apply, Set.disjoint_left]

@[simp] lemma codisjoint_closeds_indicatorHom {C D : Closeds X} :
    Codisjoint C.indicatorHom D.indicatorHom ↔ Disjoint (C : Set X) D := by
  simp [codisjoint_iff_apply, Set.disjoint_left, imp_iff_not_or]


/-! ### Precomposition -/

variable (h : Y ⟶ X)

@[simp] lemma comp_sup : h ≫ (f ⊔ g) = h ≫ f ⊔ h ≫ g := rfl
@[simp] lemma comp_inf : h ≫ (f ⊓ g) = h ≫ f ⊓ h ≫ g := rfl
@[simp] lemma comp_top : h ≫ (⊤ : X ⟶ ⌜T → F⌟) = ⊤ := rfl
@[simp] lemma comp_bot : h ≫ (⊥ : X ⟶ ⌜T → F⌟) = ⊥ := rfl
@[simp] lemma comp_iSup {ι} (f : ι → (X ⟶ ⌜T → F⌟)) : h ≫ (⨆ i, f i) = ⨆ i, h ≫ f i := by
  ext; simp

/-- The constant map to `pt(T)` is `⊤`. -/
@[simp] lemma ofHom_const_T : (ConcreteCategory.ofHom (.const X pt(T)) : X ⟶ ⌜T → F⌟) = ⊤ := rfl

/-- The constant map to `pt(F)` is `⊥`. -/
@[simp] lemma ofHom_const_F : (ConcreteCategory.ofHom (.const X pt(F)) : X ⟶ ⌜T → F⌟) = ⊥ := rfl

/-- The constant maps, as composites through the terminal object. -/
@[simp] lemma from_comp_homOfElement_T (f : X ⟶ 𝟙_ TopCat) :
    f ≫ ConcreteCategory.homOfElement (pt(T) : ⌜T → F⌟) = ⊤ := rfl

/-- The constant maps, as composites through the terminal object. -/
@[simp] lemma from_comp_homOfElement_F (f : X ⟶ 𝟙_ TopCat) :
    f ≫ ConcreteCategory.homOfElement (pt(F) : ⌜T → F⌟) = ⊥ := rfl


@[reassoc (attr := simp), elementwise (attr := simp)]
lemma asOpen_inclusion'_comp (f : X ⟶ ⌜T → F⌟) : (asOpen f).inclusion' ≫ f = ⊤ := by
  ext ⟨x, hx⟩; simpa using hx

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma asClosed_inclusion'_comp (f : X ⟶ ⌜T → F⌟) : (asClosed f).inclusion' ≫ f = ⊥ := by
  ext ⟨x, hx⟩; simpa using hx

/-! ### Compatibility with the `Subobject` lattice -/

section subobject
open Set.Notation
variable (f : X ⟶ ⌜T → F⌟.{u}) (Q : Subobject X)


-- Mathlib.Order.CompleteLattice.Basic

open Set.Notation Filter


--TODO when we eventually update Mathlib for PR, all these need to reference `.ofClass` instead of
-- `toContinuousMap`
-- should probably upstream to `TopCat`
attribute [local pp_with_univ] TopCat


-- TODO upstream `Mathlib.Topology.Bases`

end subobject
end Sierpinski


