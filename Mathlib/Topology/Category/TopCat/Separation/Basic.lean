/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.Tactic.Gavrilovich.Relabel
public import Mathlib.Topology.Gavrilovich.Sierpinski


/-!
# Separation

The standard separation axioms in topology can be represented categorically as lifting properties.

Here, we provide the implementations. We provide a systematic `llp`/`rlp` lemma for each separation
axiom, stating that a space satisfies the axiom iff it has the corresponding lifting property,
together with both its directions. If necessary, we then provide simplified versions of one or both
directions, abandoning the explicit lifting property in order to remove redundant hypotheses.

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

Finite topological spaces, and continuous maps between them, can be written inline as diagrams,
in the style of Gavrilovich's papers on lifting properties:
```
def q :=
    ⌜a   b⌝      ⌜ a=b ⌝
      ↘ ↙    ⇢      ↓
    ⌞  c  ⌟      ⌞  c  ⌟
```

See Mathlib.Tactic.Gavrilovich.Elab for details.

## Implementation details


## References

* https://ncatlab.org/nlab/show/separation+axioms+in+terms+of+lifting+properties

## Tags

Foobars, barfoos
-/

@[expose] public section

-- TODO switch to DomMulAction?

universe w v u
open CategoryTheory MonoidalCategory SemiCartesianMonoidalCategory CartesianMonoidalCategory
open TopCat hiding uliftFunctor
open TopCat renaming uliftFunctor → topUliftFunctor
open Limits Topology TopologicalSpace Set
open ConcreteCategory renaming ofHom → CCofHom

open Gavrilovich
open Space (relabel)

variable {X : TopCat.{u}} --[DecidableEq X] --[∀ (s : Set X) x, Decidable (x ∈ s)]






attribute [local simp] Function.comp Pts.equivFin

/-- Two inseparable points `x, y : X` define a canonical morphism from the codiscrete two-point
space to `X`. -/
def Inseparable.desc {x y : X} (hxy : Inseparable x y) : ⌜x ↔ y⌟ ⟶ X :=
  letI fn | pt(x) => x | pt(y) => y
  CCofHom ⟨fn, ⟨fun s hs ↦ by
    by_cases h : x ∈ s
    · have : y ∈ s := hxy.mem_open_iff hs |>.mp h
      have : fn ⁻¹' s = univ := by ext z; fin_cases z; all_goals simp [fn, h, this]
      rw [this]; exact isOpen_univ
    · have : y ∉ s := by rwa [hxy.mem_open_iff hs] at h
      have : fn ⁻¹' s = ∅ := by ext z; fin_cases z; all_goals simp [fn, h, this]
      rw [this]; exact isOpen_empty⟩⟩

@[simp] lemma Inseparable.desc_app_x {x y : X} (hxy : Inseparable x y) :
    Inseparable.desc hxy pt(x) = x := by rfl

@[simp] lemma Inseparable.desc_app_y {x y : X} (hxy : Inseparable x y) :
    Inseparable.desc hxy pt(y) = y := by rfl

/-- A morphism from the codiscrete two-point space implies that its two image points are
inseparable. -/
lemma Inseparable.of_desc (f : ⌜x ↔ y⌟ ⟶ X) : Inseparable (f pt(x)) (f pt(y)) :=
  inseparable_iff_specializes_and.mpr
    ⟨f.hom.map_specializes (by decide), f.hom.map_specializes (by decide)⟩

/-- `x ⤳ y` for `x, y : X` implies a canonical morphism from the Sierpinski space to `X`. -/
def Specializes.desc {x y : X} (hxy : x ⤳ y) : ⌜T → F⌟ ⟶ X :=
  letI fn | pt(T) => x | pt(F) => y
  CCofHom ⟨fn, AlexandrovDiscrete.continuous_iff_spec_monotone.mpr fun x y h ↦ by
      pt_cases h <;> simp [fn, hxy, specializes_rfl]⟩

@[simp] lemma Specializes.desc_app_o {x y : X} (hxy : x ⤳ y) :
    Specializes.desc hxy pt(T) = x := rfl

@[simp] lemma Specializes.desc_app_c {x y : X} (hxy : x ⤳ y) :
    Specializes.desc hxy pt(F) = y := rfl


namespace TopCat

attribute [-simp] hnot_eq_compl


namespace T0Space

/-- A space `X` is `T0` iff the morphism `isTerminalTensorUnit.from X` has the right lifting
property against `isTerminalTensorUnit.from ⌜x ↔ y⌟`. -/
theorem rlp : T0Space X ↔ isTerminalTensorUnit.from.{u} ⌜x ↔ y⌟ ⧄ isTerminalTensorUnit.from X where
  mp h :=
  { sq_hasLift {χ _} _ := by
      have hχ : χ pt(x) = χ pt(y) := by
        by_contra! h!
        obtain ⟨U, Uo, ⟨hxU, hyU⟩ | ⟨hxU, hyU⟩⟩ := exists_isOpen_xor_mem h!
        all_goals
            obtain ⟨U', U'o, hU'⟩ := Space.isOpen_iff.mp <| Uo.preimage χ.continuous
            rw [← mem_preimage] at hxU hyU
            fin_cases U'o
            · simp [hU'] at hxU hyU
            · rw [hU'] at hxU hyU; revert hxU hyU; decide
      apply CommSq.HasLift.mk'; use ConcreteCategory.homOfElement (χ pt(x))
      · ext z; pt_cases z <;> [simp; simpa]
      · exact isTerminalTensorUnit.hom_ext _ _ }
  mpr h :=
  { t0 x y hxy := by
      let f : ⌜x ↔ y⌟ ⟶ X := hxy.desc
      have hχ := by
        simpa [Space.hom_ext_iff, -CommSq.fac_left, Unique.eq_default (α := 𝟙_ TopCat.{u}), f]
          using CommSq.fac_left (hsq := h.sq_hasLift (f := f) (g := 𝟙 _) ⟨by simp⟩)
      exact (hχ pt(x) (by decide)).symm.trans <| hχ pt(y) (by decide) }


instance [T0Space X] :
    HasLiftingProperty (isTerminalTensorUnit.from.{u} ⌜x ↔ y⌟) (isTerminalTensorUnit.from X) :=
  rlp.mp ‹_›

/-- A `T0` space `X` descends every morphism from-⌜x ↔ y⌟ into one from `𝟙_ TopCat.{u}`. -/
noncomputable def desc [T0Space X] (χ : ⌜x ↔ y⌟ ⟶ X) : 𝟙_ TopCat.{u} ⟶ X :=
  CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := χ) (g := 𝟙 _) ⟨by simp⟩)

@[reassoc (attr := simp)]
lemma desc_fac [T0Space X] (χ : ⌜x ↔ y⌟ ⟶ X) :
    isTerminalTensorUnit.from.{u} ⌜x ↔ y⌟ ≫ desc χ = χ :=
  CommSq.fac_left (hsq := (rlp.mp ‹_›).sq_hasLift _)

/-- If every morphism from ⌜x ↔ y⌟ to a space `X` descends to a morphism from
`𝟙_ TopCat.{u}`, then `X` is `T0`. -/
theorem of_desc (lift : (⌜x ↔ y⌟ ⟶ X) → (𝟙_ TopCat.{u} ⟶ X))
    (fac : ∀ χ : ⌜x ↔ y⌟ ⟶ X, isTerminalTensorUnit.from.{u} ⌜x ↔ y⌟ ≫ lift χ = χ) : T0Space X :=
  rlp.mpr { sq_hasLift {f _} _ :=
    CommSq.HasLift.mk' ⟨lift f, fac f, isTerminalTensorUnit.hom_ext _ _⟩ }
end T0Space

namespace R0Space

/-- A space `X` is `R0` iff the morphism `isTerminalTensorUnit.from X` has the right lifting
property against ⌜T → F⌟ ⇢ ⌜o ↔ c⌟. -/
theorem rlp : R0Space X ↔ (⌜x → y⌟ ⇢ ⌜x ↔ y⌟ : ⌜T → F⌟ ⟶ _) ⧄ isTerminalTensorUnit.from X where
  mp _ :=
  { sq_hasLift {ι τ} sq := by
      have := ι.hom.map_specializes <| show pt(T) ⤳ pt(F) by decide
      apply CommSq.HasLift.mk'; use this.inseparable.desc
      · ext x hx; fin_cases hx <;> simp
      · exact isTerminalTensorUnit.hom_ext _ _ }
  mpr h := {
    specializes_symm.symm {x y} hxy := by
      obtain ⟨hy, hx⟩ := by
        simpa [Space.hom_ext_iff, -CommSq.fac_left, Space.all, forall_or_eq_imp',
          Unique.eq_default (α := 𝟙_ TopCat.{u})]
        using CommSq.fac_left
          (hsq := h.sq_hasLift (f := hxy.desc) (g := isTerminalTensorUnit.from _) ⟨by simp⟩)
      conv =>
        args
        · rw [← hy]
        · rw [← hx]
      exact Inseparable.of_desc (CommSq.lift (hsq := h.sq_hasLift
            (f := hxy.desc) (g := isTerminalTensorUnit.from _) ⟨by simp⟩)) |>.specializes' }

instance [R0Space X] : (⌜x → y⌟ ⇢ ⌜x ↔ y⌟ : ⌜T → F⌟ ⟶ _) ⧄ (isTerminalTensorUnit.from X) :=
  rlp.mp ‹_›

/-- An `R0` space `X` descends every morphism from the Sierpinski space `⌜T → F⌟` into one
from `⌜x ↔ y⌟`. -/
noncomputable def desc [R0Space X] (χ : ⌜T → F⌟ ⟶ X) : ⌜x ↔ y⌟ ⟶ X :=
  CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := χ) (g := isTerminalTensorUnit.from _) ⟨by simp⟩)

@[reassoc (attr := simp)]
lemma desc_fac [R0Space X] (f : ⌜T → F⌟ ⟶ X) : (⌜x → y⌟ ⇢ ⌜x ↔ y⌟ : ⌜T → F⌟ ⟶ _) ≫ desc f = f :=
  CommSq.fac_left (hsq := (rlp.mp ‹_›).sq_hasLift _)

/- If every morphism from `⌜T → F⌟` to a space `X` descends to a morphism from `⌜x ↔ y⌟`,
then `X` is `R0`. -/
theorem of_desc (desc : (⌜T → F⌟ ⟶ X) → (⌜x ↔ y⌟ ⟶ X))
    (fac : ∀ χ : ⌜T → F⌟ ⟶ X, (⌜x → y⌟ ⇢ ⌜x ↔ y⌟ : ⌜T → F⌟ ⟶ _) ≫ desc χ = χ) : R0Space X :=
  rlp.mpr { sq_hasLift {f _} _ :=
    CommSq.HasLift.mk' ⟨desc f, fac f, isTerminalTensorUnit.hom_ext _ _⟩ }

end R0Space


namespace T1Space

/-- A space `X` is `T1` iff the morphism `isTerminalTensorUnit.from X` has the right lifting
property against `isTerminalTensorUnit.from ⌜T → F⌟`. -/
theorem rlp : T1Space X ↔
    isTerminalTensorUnit.from.{u} ⌜T → F⌟ ⧄ isTerminalTensorUnit.from X where
  mp _ :=
  { sq_hasLift {χ _} _ := by
      have hf : χ pt(T) = χ pt(F) := by
        by_contra! h!
        obtain ⟨U, Uo, hU₁, hU₀⟩ := t1Space_iff_exists_open.mp ‹_› h!
        obtain ⟨V, Vo, hV₀, hV₁⟩ := t1Space_iff_exists_open.mp ‹_› h!.symm
        replace Uo : IsOpen (χ ⁻¹' U) := Uo.preimage χ.continuous
        replace Vo : IsOpen (χ ⁻¹' V) := Vo.preimage χ.continuous
        have : χ ⁻¹' V = univ := by
          have : χ ⁻¹' V ∈ 𝓝 pt(F) := by
            rw [isOpen_iff_mem_nhds] at Vo; exact Vo _ hV₀
          rw [preimage_eq_univ_iff]; simpa [-EquivLike.range_comp] using this
        exact ne_univ_of_notMem (by simpa using hV₁) this
      apply CommSq.HasLift.mk'; use ConcreteCategory.homOfElement (χ pt(F))
      · symm_saturate; ext x; pt_cases x <;> [simp; simpa]
      · exact isTerminalTensorUnit.hom_ext _ _ }
  mpr h := by
    rw [t1Space_iff_specializes_imp_eq]
    intro x y hxy
    obtain ⟨hy, hx⟩ := by simpa [Space.hom_ext_iff, -CommSq.fac_left, Space.all, forall_or_eq_imp',
          Unique.eq_default (α := 𝟙_ TopCat.{u})]
        using CommSq.fac_left (hsq := h.sq_hasLift (f := hxy.desc) (g := 𝟙 _) ⟨by simp⟩)
    exact hx.symm.trans hy

instance [T1Space X] : isTerminalTensorUnit.from.{u} ⌜T → F⌟ ⧄ (isTerminalTensorUnit.from X) :=
  rlp.mp ‹_›

/-- If every mono `χ : ⌜x y⌟ ⟶ X` can be extended to meet `⌜x y⌟ ⇢ ⌜x → y⌟`, then `X` is `T1. -/
lemma of_extend (extend : ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ], X ⟶ ⌜T → F⌟)
    (fac : ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ], χ ≫ extend χ = (⌜x y⌟ ⇢ ⌜x → y⌟ : _ ⟶ ⌜T → F⌟)) :
    T1Space X :=
  t1Space_iff_exists_open.mpr fun x y hxy ↦ by
    let χ : ⌜x y⌟ ⟶ X := CCofHom ⟨fun | pt(x) => x | pt(y) => y, by continuity⟩
    have : Mono χ := TopCat.mono_iff_injective χ |>.mpr fun x y hxy' ↦ by
      pt_cases x <;> pt_cases y <;> simp [χ] at hxy' <;> simp [hxy'] at hxy ⊢
    use (extend χ ⁻¹' {pt(T)}), (extend χ).continuous.isOpen_preimage _ (by decide),
     by simp [show x = χ pt(x) by rfl, elementwise_of% fac],
     by simp [show y = χ pt(y) by rfl, elementwise_of% fac]

/-- A space `X` is `T1` iff every mono `χ : ⌜x y⌟ ⟶ X` has the left lifting property against
`isTerminalTensorUnit.from ⌜T → F⌟`.

(In fact it suffices to consider only the top-left half of the lifting square, see
`T1Space.of_extend`). -/
theorem llp :
    T1Space X ↔ ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ], χ ⧄ isTerminalTensorUnit.from.{u} ⌜T → F⌟ where
  mp h χ hχ :=
  { sq_hasLift {η _} sq := by
      rw [t1Space_iff_exists_open] at h
      rw [TopCat.mono_iff_injective, ← pairwise_ne_iff_injective] at hχ
      by_cases hxy : η pt(x) = η pt(y)
      · refine ⟨CCofHom <| .const _ (η pt(x)), ?_, ?_⟩
        · ext x hx; pt_cases hx <;> simp [hxy]
        · exact isTerminalTensorUnit.hom_ext ..
      have hT : pt(T) ∈ range η := by
        rw [mem_range]; by_contra!
        conv at this => enter [z]; rw [Space.ne_iff_eq_hnot]
        exact hxy (this pt(x) |>.trans (this pt(y)).symm)
      obtain ⟨o, ho⟩ := hT
      have hη : η (￢o) = pt(F) := by
        pt_cases o <;>
          simp only [ho, ← ne_eq, Space.hnot_mk, tsub_zero] at hxy ⊢
        · symm at hxy; rw [Space.ne_iff_eq_hnot] at hxy; simp [hxy]
        · rw [Space.ne_iff_eq_hnot] at hxy; simp [hxy]
      specialize @hχ o (￢o) (Space.ne_hnot o)
      obtain ⟨U, Uo, hxU, hyU⟩ := h hχ
      refine ⟨Uo.indicatorHom, ?_, ?_⟩
      · ext x
        rcases hx : (Space.hnot_total o x) with (rfl | rfl)
        all_goals simp at hxU hyU; simp [hxU, hyU, ho, hη]
      · exact isTerminalTensorUnit.hom_ext .. }
  mpr hχ := by
    let extend χ [Mono χ] :=
      CommSq.lift (f := (⌜x y⌟ ⇢ ⌜x → y⌟ : _ ⟶ ⌜T → F⌟)) (g := isTerminalTensorUnit.from X)
      ⟨isTerminalTensorUnit.hom_ext ..⟩ (hsq := hχ χ |>.sq_hasLift _)
    fapply of_extend extend (fun χ [_] ↦ CommSq.fac_left _ (hsq := hχ χ |>.sq_hasLift _))


/-- A `T1` space `X` lifts every morphism from-the Sierpinski space `⌜T → F⌟` into one from
`𝟙_ TopCat.{u}`. -/
noncomputable def lift [T1Space X] (χ : ⌜T → F⌟ ⟶ X) : 𝟙_ TopCat.{u} ⟶ X :=
  CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := χ) (g := 𝟙 _) ⟨by simp⟩)

@[reassoc (attr := simp)]
lemma lift_fac [T1Space X] (χ : ⌜T → F⌟ ⟶ X) : isTerminalTensorUnit.from.{u} ⌜T → F⌟ ≫ lift χ = χ :=
  CommSq.fac_left (hsq := (rlp.mp ‹_›).sq_hasLift _)

/-- If every morphism from the Sierpinski space ⌜T → F⌟ to a space `X` lifts to a morphism
from `𝟙_ TopCat.{u}`, then `X` is `T1`. -/
theorem of_lift (lift : (⌜T → F⌟ ⟶ X) → (𝟙_ TopCat.{u} ⟶ X))
    (fac : ∀ χ : ⌜T → F⌟ ⟶ X, isTerminalTensorUnit.from.{u} ⌜T → F⌟ ≫ lift χ = χ) : T1Space X :=
  rlp.mpr { sq_hasLift {χ _} _ :=
    CommSq.HasLift.mk' ⟨lift χ, fac χ, isTerminalTensorUnit.hom_ext _ _⟩ }

/-- A `T1` space `X` extends every mono arrow from the discrete space `⌜x y⌟` to meet
`⌜x y⌟ ⇢ ⌜x → y⌟ : ⌜x y⌟ ⟶ ⌜T → F⌟)`. -/
noncomputable def extend [T1Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] : X ⟶ ⌜T → F⌟ :=
  CommSq.lift (hsq := (llp.mp ‹_› χ).sq_hasLift (f := (⌜x y⌟ ⇢ ⌜x → y⌟ : _ ⟶ ⌜T → F⌟))
    (g := isTerminalTensorUnit.from X) ⟨isTerminalTensorUnit.hom_ext ..⟩)

@[reassoc (attr := simp)]
lemma comp_extend [T1Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] :
    χ ≫ extend χ = (⌜x y⌟ ⇢ ⌜x → y⌟ : _ ⟶ ⌜T → F⌟) :=
  CommSq.fac_left (hsq := (llp.mp ‹_› χ).sq_hasLift _)

end T1Space

end TopCat
