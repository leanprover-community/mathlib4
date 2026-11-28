/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public meta import Mathlib.CategoryTheory.Endomorphism.FinEnum
public meta import Mathlib.Tactic.OrbitCases
public meta import Mathlib.Topology.Category.TopCat.Basic
public meta import Mathlib.Topology.Gavrilovich.Relabel
public import Mathlib.Topology.Category.TopCat.Separation.Basic

/-!
# Hausdorff-type separation axioms as lifting properties

TODO(docstring)
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

namespace TopCat

instance O2C1.partialOrder : PartialOrder ⌜o₁ → c ← o₂⌟ where
  le_antisymm x y h := by pt_cases h <;> gav_decide


namespace O2C1
open CartesianMonoidalCategory renaming lift → cartesianLift

@[simps! cone_pt]
noncomputable def asEqualizer :
    LimitCone (parallelPair (Y := ⌜T → F⌟.{u}) Sierpinski.andHom ⊥) where
  cone := Fork.ofι (lift ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c=o₂⌟ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂ → c=o₁⌟) <| by
    ext x; pt_cases x <;> simp
  isLimit := by
    fapply isEqualizer_of_alexandrovDiscrete _
    · exact {
      toFun
      | pt(o₁) => ⟨(pt(T), pt(F)), by simp⟩
      | pt(o₂) => ⟨(pt(F), pt(T)), by simp⟩
      | pt(c) => ⟨(pt(F), pt(F)), by simp⟩
      invFun
      | ⟨⟨pt(T), pt(F)⟩, _⟩ => pt(o₁)
      | ⟨⟨pt(F), pt(T)⟩, _⟩ => pt(o₂)
      | ⟨⟨pt(F), pt(F)⟩, _⟩ => pt(c)
      | ⟨⟨pt(T), pt(T)⟩, h⟩ => by simp at h
      left_inv x := by pt_cases x <;> simp
      right_inv | ⟨⟨x, y⟩, h⟩ => by pt_cases x <;> pt_cases y <;> simp at h ⊢ }
    · intro x; pt_cases x <;> simp
    · intro x y h; pt_cases x <;> pt_cases y <;> simp +decide at h ⊢

variable (u v : X ⟶ ⌜T → F⌟) (w : Disjoint u v)

noncomputable def lift : X ⟶ ⌜o₁ → c ← o₂⌟ :=
  Fork.IsLimit.lift O2C1.asEqualizer.isLimit (cartesianLift u v) w.eq_bot

variable {u v w}

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_ι : lift u v w ≫ cartesianLift ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c=o₂⌟ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂ → c=o₁⌟
    = cartesianLift u v :=
  Fork.IsLimit.lift_ι ..

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_fst : lift u v w ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c=o₂⌟ = u := by
  conv_rhs => rw [← CartesianMonoidalCategory.lift_fst u v, ← lift_ι (w := w)]
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_snd : lift u v w ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂ → c=o₁⌟ = v := by
  conv_rhs => rw [← CartesianMonoidalCategory.lift_snd u v, ← lift_ι (w := w)]
  simp

lemma hom_ext {f g : X ⟶ ⌜o₁ → c ← o₂⌟}
    (h₁ : f ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁(=T) → c=o₂(=F)⌟ = g ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c=o₂⌟)
    (h₂ : f ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂(=T) → c=o₁(=F)⌟ = g ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂ → c=o₁⌟) : f = g := by
  apply Fork.IsLimit.hom_ext O2C1.asEqualizer.isLimit
  apply CartesianMonoidalCategory.hom_ext <;> simpa

lemma hom_ext_iff {f g : X ⟶ ⌜o₁ → c ← o₂⌟} :
    f = g ↔ f ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁(=T) → c=o₂(=F)⌟ = g ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c=o₂⌟ ∧
          f ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂(=T) → c=o₁(=F)⌟ = g ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₂ → c=o₁⌟ where
  mp h := by simp [h]
  mpr | ⟨h₁, h₂⟩ => hom_ext h₁ h₂

end O2C1


lemma O2C1.isPushout :
    IsPushout (⌜*⌟ ⇢ ⌜T → *⌟ : _ ⟶ ⌜T → F⌟) (⌜*⌟ ⇢ ⌜T → *⌟ : _ ⟶ ⌜T → F⌟)
      (⌜T → F⌟ ⇢ ⌜T(=o₁) → F ← o₂⌟ : _ ⟶ ⌜o₁ → c ← o₂⌟) (⌜T → F⌟ ⇢ ⌜o₁ → F ← T(=o₂)⌟) := by
  fapply IsPushout.mk'
  · simp
  · intro X φ₁ φ₂ hφ₁ hφ₂; ext z hz
    simp_rw [Space.hom_ext_iff] at hφ₁ hφ₂; pt_cases hz
    · specialize hφ₁ pt(F) (by decide); simpa using hφ₁
    all_goals
      specialize hφ₁ pt(T); specialize hφ₂ pt(T)
      simp [Space.all] at hφ₁ hφ₂; simp [hφ₁, hφ₂]
  · intro X ι₁ ι₂ hι
    use CCofHom
      ⟨fun | pt(o₁) => ι₁ pt(T) | pt(o₂) => ι₂ pt(T) | pt(c) => ι₁ pt(F), ?_⟩, ?_, ?_
    · rw [AlexandrovDiscrete.continuous_iff_spec_monotone]
      have hι₁ := ι₁.hom.map_specializes (show pt(T) ⤳ pt(F) from by decide)
      have hι₂ := ι₂.hom.map_specializes (show pt(T) ⤳ pt(F) from by decide)
      simp only [Space.hom_ext_iff, Space.all, List.length_cons, List.length_nil, Nat.reduceAdd,
        Fin.val_eq_zero, List.mem_map, List.mem_finRange, true_and, Fin.exists_fin_one, hom_comp,
        ↓Space.reduceTableHom, ContinuousMap.comp_apply, ↓Space.reduceTableApply, forall_eq'] at hι
      intro x y hxy; pt_cases hxy <;> first | simp [hι₁, specializes_refl] | simp [hι, hι₂]
    all_goals ext x hx; pt_cases hx <;> simp [Space.hom_ext_iff, Space.all] at hι <;> simp [hι]


namespace T2Space

/-- If every mono `χ : ⌜x y⌟ ⟶ X` can be extended to meet
`⌜x y⌟ ⇢ ⌜x(=o₁) → c ← y⌟ : ⌜x y⌟ ⟶ ⌜o₁ → c ← o₂⌟`, then `X` is T2. -/
theorem of_extend (extend : ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ], X ⟶ ⌜o₁ → c ← o₂⌟)
    (fac : ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ],
        χ ≫ extend χ = (⌜x y⌟ ⇢ ⌜x(=o₁) → c ← y⌟ : ⌜x y⌟ ⟶ ⌜o₁ → c ← o₂⌟)) :
    T2Space X where
  t2 x y hxy := by
    let χ : ⌜x y⌟ ⟶ X := CCofHom ⟨fun | pt(x) => x | pt(y) => y, by continuity⟩
    have : Mono χ := TopCat.mono_iff_injective χ |>.mpr fun ⦃x y⦄ h ↦ by
      pt_cases x <;> pt_cases y <;> simp [χ, hxy, hxy.symm] at h <;> simp
    have hx : x = χ (pt(x)) := by simp [χ]
    have hy : y = χ (pt(y)) := by simp [χ]
    existsi (extend χ) ⁻¹' {pt(o₁)}, (extend χ) ⁻¹' {pt(o₂)},
      IsOpen.preimage (extend χ).continuous (by decide),
      IsOpen.preimage (extend χ).continuous (by decide),
      (by simp [hx, elementwise_of% fac]), (by simp [hy, elementwise_of% fac])
    apply Disjoint.preimage; simp


example {p : Fin 3 → Prop} :
    (p 0 ∧ p 1 ∧ p 2) ↔ (List.finRange 3).Forall p := by rfl

open MulOpposite in
/-- A space `X` is `T2` iff every mono from `⌜x y⌟` to `X` has the left lifting property
against `isTerminalTensorUnit.from ⌜o₁ → c ← o₂⌟`.

(In fact, it is sufficient to consider only a specific top morphism in the lifting square;
see `T2Space.of_extend`.) -/
theorem llp : T2Space X ↔ ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ],
    χ ⧄ isTerminalTensorUnit.from.{u} (⌜o₁ → c ← o₂⌟) where
  mp _ χ _ :=
{ sq_hasLift {ι _} sq := by
    orbit_cases hι : ι using (Aut.{u} ⌜x y⌟)ᵐᵒᵖ × Aut.{u} ⌜o₁ → c ← o₂⌟ generalizing χ
    case inv =>
      rintro ⟨g₁, g₂⟩ ι hι χ sq hχ; cases g₁ with | _ g₁ =>
      rw [CommSq.HasLift.iff_of_iso_nw g₁⁻¹.asIso sq, CommSq.HasLift.iff_of_iso_ne g₂⁻¹.asIso]
      rw [CommSq.iff_of_iso_nw g₁⁻¹.asIso, CommSq.iff_of_iso_ne g₂⁻¹.asIso] at sq
      specialize hι _ (by simpa using sq) (mono_comp ..)
      convert hι <;> simp
    case rep_0 | rep_2 => -- single point, trivial case
      exact .mk' { l := CCofHom (.const _ (ι pt(x)))
                   fac_left := by subst hι; ext z hz; pt_cases hz <;> simp }
    case rep_1 => -- reduces to T1
      let ι' : _ ⟶ ⌜T → F⌟  := ι ≫ ⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁=o₂(=T) → c⌟
      let η : ⌜T → F⌟ ⟶ ⌜o₁ → c ← o₂⌟ := ⌜T → F⌟ ⇢ ⌜T(=o₁) → F ← o₂⌟
      · have ι_fac : ι' ≫ η = ι := by
          cases hι; simp [ι', η]
        have sq' :
            CommSq ι' χ (isTerminalTensorUnit.from.{u} ⌜T → F⌟) (isTerminalTensorUnit.from X) :=
          ⟨isTerminalTensorUnit.hom_ext _ _⟩
        have := T1Space.llp.mp T2Space.t1Space χ |>.sq_hasLift sq'
        refine ⟨sq'.lift ≫ η, ?_, ?_⟩
        · rw [sq'.fac_left_assoc, ι_fac]
        · exact isTerminalTensorUnit.hom_ext ..
    case rep_3 => -- T2 proper
      cases hι
      have : χ pt(x) ≠ χ pt(y) := Function.injective_iff_pairwise_ne.mp
          (TopCat.mono_iff_injective χ |>.mp ‹_›) (show pt(x) ≠ pt(y) by rintro ⟨⟩)
      obtain ⟨U, V, Uo, Vo, hxU, hyV, hUV⟩ := T2Space.t2 this
      refine ⟨O2C1.lift Uo.indicatorHom Vo.indicatorHom ?_, ?_, ?_⟩
      · simpa using hUV
      · fapply O2C1.hom_ext
        · simp [TopCat.ext_iff, Space.forallPts, hxU, hUV.notMem_of_mem_right hyV]
        · simp [TopCat.ext_iff, Space.forallPts, hyV, hUV.notMem_of_mem_left hxU]
      · exact isTerminalTensorUnit.hom_ext .. }
  mpr h := of_extend (fun χ [_] ↦ CommSq.lift (hsq := h χ |>.sq_hasLift
    (f := ⌜x y⌟ ⇢ ⌜x(=o₁) → c ← y⌟) (g := isTerminalTensorUnit.from _) ⟨by simp⟩ ))
    (fun χ [_] ↦ CommSq.fac_left ⟨by simp⟩)

instance [T2Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] :
    HasLiftingProperty χ (isTerminalTensorUnit.from ⌜o₁ → c ← o₂⌟) :=
  llp.mp ‹_› χ

/-- A `T2` space `X` extends every mono from `⌜x y⌟` into one to `⌜o₁ → c ← o₂⌟`. -/
noncomputable def extend [T2Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] : X ⟶ ⌜o₁ → c ← o₂⌟ :=
  CommSq.lift (hsq := (llp.mp ‹_› χ).sq_hasLift
    (f := ⌜x y⌟ ⇢ ⌜x(=o₁) → c ← y⌟) (g := isTerminalTensorUnit.from _) ⟨by simp⟩)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma extend_fac [T2Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] :
    χ ≫ extend χ = ⌜x y⌟ ⇢ ⌜x(=o₁) → c ← y⌟ :=
  CommSq.fac_left (hsq := (llp.mp ‹_› χ).sq_hasLift _)


end T2Space

instance : PartialOrder.{u} ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ where
  le_antisymm := by simp +decide

namespace O1C2
open CartesianMonoidalCategory renaming lift → cartesianLift

@[simps! cone_pt]
noncomputable def asEqualizer :
    LimitCone (parallelPair (Y := ⌜T → F⌟.{u}) Sierpinski.orHom ⊤) where
  cone := Fork.ofι (cartesianLift ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₂=o → c₁⌟ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₁=o → c₂⌟) <| by
    ext x; pt_cases x <;> simp
  isLimit := by
    fapply isEqualizer_of_alexandrovDiscrete _
    · exact {
      toFun
      | pt(c₁) => ⟨(pt(F), pt(T)), by simp⟩
      | pt(c₂) => ⟨(pt(T), pt(F)), by simp⟩
      | pt(o) => ⟨(pt(T), pt(T)), by simp⟩
      invFun
      | ⟨⟨pt(F), pt(T)⟩, _⟩ => pt(c₁)
      | ⟨⟨pt(T), pt(F)⟩, _⟩ => pt(c₂)
      | ⟨⟨pt(T), pt(T)⟩, _⟩ => pt(o)
      | ⟨⟨pt(F), pt(F)⟩, h⟩ => by simp at h
      left_inv x := by pt_cases x <;> simp
      right_inv | ⟨⟨x, y⟩, h⟩ => by pt_cases x <;> pt_cases y <;> simp at h ⊢ }
    · intro x; pt_cases x <;> simp
    · intro x y h; pt_cases x <;> pt_cases y <;> simp +decide at h ⊢

variable (u v : X ⟶ ⌜T → F⌟) (w : Codisjoint u v)

noncomputable def lift : X ⟶ ⌜c₁ ← o → c₂⌟ :=
  Fork.IsLimit.lift asEqualizer.isLimit (cartesianLift u v) w.eq_top

variable {u v w}

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_ι : lift u v w ≫ cartesianLift ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₂=o → c₁⌟ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₁=o → c₂⌟
    = cartesianLift u v :=
  Fork.IsLimit.lift_ι ..


@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_fst : lift u v w ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₂=o → c₁⌟ = u := by
  conv_rhs => rw [← CartesianMonoidalCategory.lift_fst u v, ← lift_ι (w := w)]
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_snd : lift u v w ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₁=o → c₂⌟ = v := by
  conv_rhs => rw [← CartesianMonoidalCategory.lift_snd u v, ← lift_ι (w := w)]
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_mid : lift u v w ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜o(=T) → c₁=c₂(=F)⌟ = u ⊓ v := by
  conv_rhs =>
    congr
    · rw [← lift_fst (w := w)]
    · rw [← lift_snd (w := w)]
  rw [← Sierpinski.comp_inf]; congr; decide

@[ext]
lemma hom_ext {f g : X ⟶ ⌜c₁ ← o → c₂⌟}
    (h₁ : f ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₂=o(=T) → c₁(=F)⌟ = g ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₂=o → c₁⌟)
    (h₂ : f ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₁=o(=T) → c₂(=F)⌟ = g ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₁=o → c₂⌟) : f = g := by
  apply Fork.IsLimit.hom_ext asEqualizer.isLimit
  apply CartesianMonoidalCategory.hom_ext <;> simpa

open Sierpinski Classical ConcreteCategory in
lemma lift_apply (x : X) : lift u v w x =
  if x ∈ asClosed u then pt(c₁) else if x ∈ asClosed v then pt(c₂) else pt(o) := by
  rw [codisjoint_iff_apply] at w; specialize w x
  apply homOfElement_injective; rw [← homOfElement_comp]
  split_ifs with h₁ h₂ <;> ext1 <;> simp only [Category.assoc, lift_fst, lift_snd] <;>
  simp_all [homOfElement_inj]

end O1C2


namespace O3C2
open CartesianMonoidalCategory renaming lift → cartesianLift

@[simps! cone_pt]
noncomputable def asEqualizer :
    LimitCone (parallelPair (X := ⌜c₁ ← o → c₂⌟ ⊗ ⌜T → F⌟.{u}) (Y := ⌜T → F⌟)
        (⌜c₁ ← o → c₂⌟ ⇢ ⌜o → c₁=c₂⌟ ▷ ⌜T → F⌟.{u} ≫ Sierpinski.andHom) ⊥) where
  cone := Fork.ofι (cartesianLift ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀ ← o₁ → c₁=o₂(=c₂)⌟
      ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂ → c₀=o₁=c₁⌟) <| by ext x; pt_cases x <;> simp
  isLimit := by
    fapply isEqualizer_of_alexandrovDiscrete _
    · exact {
      toFun
      | pt(o₀) => ⟨(pt(c₁), pt(T)), by simp⟩
      | pt(c₀) => ⟨(pt(c₁), pt(F)), by simp⟩
      | pt(o₁) => ⟨(pt(o), pt(F)), by simp⟩
      | pt(c₁) => ⟨(pt(c₂), pt(F)), by simp⟩
      | pt(o₂) => ⟨(pt(c₂), pt(T)), by simp⟩
      invFun
      | ⟨⟨pt(c₁), pt(T)⟩, _⟩ => pt(o₀)
      | ⟨⟨pt(c₁), pt(F)⟩, _⟩ => pt(c₀)
      | ⟨⟨pt(o), pt(F)⟩, _⟩ => pt(o₁)
      | ⟨⟨pt(c₂), pt(F)⟩, _⟩ => pt(c₁)
      | ⟨⟨pt(c₂), pt(T)⟩, _⟩ => pt(o₂)
      | ⟨⟨pt(o), pt(T)⟩, h⟩ => by simp +decide at h
      left_inv x := by pt_cases x <;> simp
      right_inv | ⟨⟨x, y⟩, h⟩ => by pt_cases x <;> pt_cases y <;> simp at h ⊢ }
    · intro x; ext <;> pt_cases x <;> cbv
    · intro x y h; pt_cases x <;> pt_cases y <;> simp +decide at h ⊢

variable (u : X ⟶ ⌜c₁ ← o → c₂⌟) (uₗ uᵣ v : X ⟶ ⌜T → F⌟)
  (w : Disjoint (u ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜o(=T) → c₁=c₂(=F)⌟) v)
  (w₀ : Codisjoint uₗ uᵣ) (w₁ : Disjoint (uₗ ⊓ uᵣ) v)

noncomputable def lift : X ⟶ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ :=
  Fork.IsLimit.lift asEqualizer.isLimit (cartesianLift u v) w.eq_bot

@[simp]
noncomputable def lift3 : X ⟶ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ :=
  lift (O1C2.lift uₗ uᵣ w₀) v <| by rwa [O1C2.lift_mid]

variable {u v w uₗ uᵣ w₀ w₁}

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_ι : lift u v w ≫ (cartesianLift ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀ ← o₁ → c₁=o₂(=c₂)⌟
      ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂ → c₀=o₁=c₁⌟) = cartesianLift u v :=
  Fork.IsLimit.lift_ι ..

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_fst : lift u v w ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀ ← o₁ → c₁=o₂(=c₂)⌟ = u := by
  conv_rhs => rw [← CartesianMonoidalCategory.lift_fst u v, ← lift_ι (w := w)]
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_left : lift u v w ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₁=c₁=o₂(=T) → c₀=o₀(=F)⌟ =
    u ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₂=o → c₁⌟ := by
  conv_rhs => rw [← @lift_fst _ u v w, Category.assoc]
  congr; simp

@[reassoc, elementwise nosimp]
lemma lift3_left : lift3 uₗ uᵣ v w₀ w₁ ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₁=c₁=o₂ → c₀=o₀⌟ = uₗ := by
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_mid : lift u v w ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂ → c₀=o₁=c₁⌟ = v := by
  conv_rhs => rw [← CartesianMonoidalCategory.lift_snd u v, ← lift_ι (w := w)]
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_right : lift u v w ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀=o₁(=T) → c₁=o₂(=F)⌟ =
    u ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜c₁=o → c₂⌟ := by
  conv_rhs => rw [← @lift_fst _ u v w, Category.assoc]
  congr; simp

@[reassoc, elementwise nosimp]
lemma lift3_right : lift3 uₗ uᵣ v w₀ w₁ ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀=o₁ → c₁=o₂⌟ = uᵣ := by
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift3_o₀ : lift3 uₗ uᵣ v w₀ w₁ ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀ → c₀=o₁=c₁=o₂⌟ = uᵣ ⊓ v := by
  have : ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀(=T) → c₀=o₁=c₁=o₂(=F)⌟ =
      ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₁=c₀=o₀ → c₁=o₂⌟ ⊓
      ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂ → c₀=o₁=c₁⌟ := by
    ext x; pt_cases x <;> simp
  rw [this]; simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift3_o₂ : lift3 uₗ uᵣ v w₀ w₁ ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₂ → o₀=c₀=o₁=c₁⌟ = uₗ ⊓ v := by
  have : ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₂(=T) → o₀=c₀=o₁=c₁(=F)⌟ =
      ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₁=c₁=o₂ → c₀=o₀⌟ ⊓
      ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂ → c₀=o₁=c₁⌟ := by
    ext x; pt_cases x <;> simp
  rw [this]; simp

@[ext]
lemma hom_ext {f g : X ⟶ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟}
    (hₗ : f ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₁=c₁=o₂(=T) → c₀=o₀(=F)⌟ =
      g ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₁=c₁=o₂(=T) → c₀=o₀(=F)⌟)
    (hᵣ : f ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀=o₁(=T) → c₁=o₂(=F)⌟ =
      g ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=c₀=o₁(=T) → c₁=o₂(=F)⌟)
    (h₀ : f ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂(=T) → c₀=o₁=c₁(=F)⌟ =
      g ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀=o₂(=T) → c₀=o₁=c₁(=F)⌟) : f = g := by
  apply Fork.IsLimit.hom_ext asEqualizer.isLimit; apply CartesianMonoidalCategory.hom_ext
  · ext1 <;> simpa [asEqualizer]
  · simpa


end O3C2


namespace T25Space

/-- If every mono `⌜x y⌟ ⟶ X` can be extended to meet
`⌜x y⌟ ⇢ ⌜x(=o₀) → c₀ ← o₁ → c₁ ← y(=o₂)⌟`, then `X` is `T2.5`. -/
lemma of_extend
    (extend : (χ : ⌜x y⌟ ⟶ X) → [Mono χ] → X ⟶ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟)
    (fac : ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ],
      χ ≫ extend χ = ⌜x y⌟ ⇢ ⌜x(=o₀) → c₀ ← o₁ → c₁ ← y(=o₂)⌟) : T25Space X where
  t2_5 {x y} hxy := by
    rw [Filter.disjoint_iff]
    let χ : ⌜x y⌟ ⟶ X := CCofHom { toFun | pt(x) => x | pt(y) => y }
    have : Mono χ := by
      rw [mono_iff_injective, Function.injective_iff_pairwise_ne]
      intro z w h; pt_cases z <;> pt_cases w <;> simp at h hxy <;>
        simp [Function.onFun, hxy, ne_comm.mp hxy, χ]
    let «λ» := Hom.hom <| extend χ
    use «λ» ⁻¹' (closure {pt(o₀)}), ?hL, «λ» ⁻¹' (closure {pt(o₂)}), ?hR
    case hL | hR =>
      apply Filter.mem_of_superset _ («λ».continuous.closure_preimage_subset _)
      apply Filter.mem_lift' (IsOpen.preimage «λ».continuous _ |>.mem_nhds _)
      · decide
      · simp [«λ», show x = χ pt(x) by rfl, show y = χ pt(y) by rfl, elementwise_of% fac χ]
    apply Disjoint.preimage
    grw [closure_minimal (t := {pt(o₀), pt(c₀)}) (by simp),
    closure_minimal (t := {pt(o₂), pt(c₁)}) (by simp)]
    all_goals simp +decide


open MulOpposite Equiv Sierpinski in
theorem llp : T25Space X ↔
    ∀ (χ : ⌜x y⌟ ⟶ X) [Mono χ], χ ⧄ isTerminalTensorUnit.from  ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ where
  mp h χ _ :=
{ sq_hasLift {ι τ} sq := by
    have hne : χ pt(x) ≠ χ pt(y) := by
      rename_i hχ; rw [TopCat.mono_iff_injective] at hχ
      exact hχ.pairwise_ne (show pt(x) ≠ pt(y) by decide)
    orbit_cases hι : ι using (Aut.{u} ⌜x y⌟)ᵐᵒᵖ × (Aut.{u} ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟)
      generated_by [(op <| Aut.of relabelIso[x ↦ y], 1), (op 1, Aut.of relabelIso[o₀ ↦ o₂])]
      generalizing χ with
    | inv =>
      rintro ⟨g₁, g₂⟩ - ι hι χ sq _ hχ; cases g₁ with | _ g₁ =>
      rw [CommSq.HasLift.iff_of_iso_nw g₁⁻¹.asIso sq, CommSq.HasLift.iff_of_iso_ne g₂⁻¹.asIso]
      rw [CommSq.iff_of_iso_nw g₁⁻¹.asIso, CommSq.iff_of_iso_ne g₂⁻¹.asIso] at sq
      specialize hι _ (by simpa using sq) (mono_comp ..) fun h ↦ by
        simp_rw [ConcreteCategory.apply_eq_iff_homOfElement_comp] at h
        replace h := Mono.right_cancellation _ _ h
        simp +decide [ConcreteCategory.homOfElement_inj] at h
      convert hι <;> simp
    | rep ⌜x  y⌟ ⇢ ⌜o₀ → x(=c₀) ← o₁ → y(=c₁) ← o₂⌟
    | rep ⌜x  y⌟ ⇢ ⌜o₀ → x(=c₀) ← o₁ → c₁ ← y(=o₂)⌟
    | rep ⌜x  y⌟ ⇢ ⌜x(=o₀) → c₀ ← o₁ → c₁ ← y(=o₂)⌟ =>
      obtain ⟨u, hxu, uO, v, hyv, vO, huv⟩ := exists_open_nhds_disjoint_closure hne
      let os := ((if ι pt(x) = pt(o₀) then uO.indicatorHom else ⊥) ⊔
          if ι pt(y) = pt(o₂) then vO.indicatorHom else ⊥)
      have hos :
          Disjoint ((Closeds.closure u).indicatorHom ⊓ (Closeds.closure v).indicatorHom) os := by
        suffices h₁ : os ≤ (uO.indicatorHom ⊔ vO.indicatorHom) by
          suffices Disjoint
              ((Closeds.closure u).compl ⊓ (Closeds.closure v).compl) (⟨u, uO⟩ ⊔ ⟨v, vO⟩) by
            grw [h₁, ← closeds_indicatorHom_sup, ← indicatorHom_sup, ← closeds_compl_indicatorHom]
            simp [← disjoint_map_orderIso_iff Sierpinski.orderIso, Closeds.compl_sup, this]
          convert disjoint_compl_left; ext1
          simp_rw [compl_sup, Opens.coe_inf, Opens.coe_compl_eq_interior_compl]
          congr <;> simp
        unfold os; apply sup_le_sup <;> rw [apply_ite (· ≤ _)] <;> simp
      use O3C2.lift3 (Closeds.closure u).indicatorHom (Closeds.closure v).indicatorHom
        os (by simp [huv]) hos
      · have hxu' := subset_closure hxu; have hyv' := subset_closure hyv
        have huv' : Disjoint u v := by
          grw [← subset_closure, ← subset_closure] at huv; exact huv
        subst hι
        fapply O3C2.hom_ext <;> ext x
        · pt_cases x <;> simp [huv.notMem_of_mem_right hyv', hxu']
        · pt_cases x <;> simp [huv.notMem_of_mem_left hxu', hyv']
        · pt_cases x <;> simp [os, huv'.notMem_of_mem_left hxu, huv'.notMem_of_mem_right hyv,
            hxu, hyv]
      · exact isTerminalTensorUnit.hom_ext ..
    all_goals
      revert sq
      let ι' := ι ≫ (⌜L → c₀ ← M → c₁ ← R⌟ ⇢ ⌜L=R(=o₁) → c₁=c₀ ← M⌟ : _ ⟶ ⌜o₁ → c ← o₂⌟)
      have hι' : ι' ≫ (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁(=o₀) → c(=c₀) ← o₂(=o₁) → c₁ ← _(=o₂)⌟) = ι := by
        simp [ι', hι]
      rw [← hι', ← Category.comp_id τ]
      intro sq
      have left : CommSq ι' χ (isTerminalTensorUnit.from ⌜o₁ → c ← o₂⌟) τ := ⟨by cat_disch⟩
      exact CommSq.HasLift.whiskerRight left ⟨by simp⟩ }
  mpr h :=
    let extend χ [Mono χ] :=
      CommSq.lift (f := ⌜x y⌟ ⇢ ⌜x(=o₀) → c₀ ← o₁ → c₁ ← y⌟) (g := isTerminalTensorUnit.from _)
        ⟨isTerminalTensorUnit.hom_ext ..⟩ (hsq := h χ |>.sq_hasLift _)
    of_extend extend fun χ [_] ↦ by simp [extend]


instance [T25Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] :
    HasLiftingProperty χ (isTerminalTensorUnit.from ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟) :=
  llp.mp ‹_› χ

/-- A `T2.5` space `X` extends every mono from `⌜x y⌟` into one to `⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟`. -/
noncomputable def extend [T25Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] : X ⟶ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ :=
  CommSq.lift (hsq := (llp.mp ‹_› χ).sq_hasLift
    (f := ⌜x y⌟ ⇢ ⌜x(=o₀) → c₀ ← o₁ → c₁ ← y⌟) (g := isTerminalTensorUnit.from _) ⟨by simp⟩)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma extend_fac [T25Space X] (χ : ⌜x y⌟ ⟶ X) [Mono χ] :
    χ ≫ extend χ = ⌜x y⌟ ⇢ ⌜x(=o₀) → c₀ ← o₁ → c₁ ← y⌟ :=
  CommSq.fac_left (hsq := (llp.mp ‹_› χ).sq_hasLift _)

end T25Space

namespace RegularSpace


instance : Model (𝟙_ TopCat.{u}) [["*"]] [] :=
  .ofList [⟨⟩] (by simp) (by simp) (by simp [Unique.forall_iff]; rfl) (by simp)

open Sierpinski in
theorem llp : RegularSpace X ↔ ∀ (χ : 𝟙_ TopCat ⟶ X),
    χ ⧄ ⌜o₁ → c₁ ← o₂ → c₂⌟ ⇢ ⌜o₁=c₁=o₂(=T) → c₂(=F)⌟ where
  mp h χ :=
{ sq_hasLift {ι C} sq := by
    generalize hi : ι ⟨⟩ = i, hx : χ ⟨⟩ = x
    obtain rfl : χ = ConcreteCategory.homOfElement x := by ext ⟨⟩; simp [hx]
    obtain rfl : ι = ConcreteCategory.homOfElement i := by ext ⟨⟩; simp [hi]
    pt_cases i
    case «1» => -- i = pt(c₂), so the only map with x ∈ asClosed C
      use C ≫ ⌜T → F⌟ ⇢ ⌜o₁ → c₁ ← T → F⌟
      · ext ⟨⟩; rw [← sq.w_assoc]; simp [hi]
      · apply TopCat.ext; intro y; simp
    all_goals
      have : x ∉ asClosed C := by
        have := (elementwise_of% sq.w) ⟨⟩
        rw [hx, hi] at this
        simpa using this
      obtain ⟨s, ⟨u, hus, uO, hCu⟩, t, ⟨v, hvt, vO, hxv⟩, hst⟩ := by
        simpa [Filter.disjoint_iff, mem_nhdsSet, mem_nhds_iff] using
          RegularSpace.regular (asClosed C).isClosed this
      grw [← hus, ← hvt] at hst; clear s t hus hvt; rename Disjoint _ _ => huv
      have hxC : C x = pt(T) := by
        grw [← hCu] at huv; simpa using huv.notMem_of_mem_right hxv
      have hxu : x ∉ u := huv.notMem_of_mem_right hxv
    · use O1C2.lift (Closeds.closure v).indicatorHom C (by
        grw [disjoint_comm] at huv
        rw [← closeds_indicatorHom_asClosed C, codisjoint_closeds_indicatorHom]
        grw [hCu]; exact huv.closure_left uO) ≫ ⌜c₁ ← o → c₂⌟ ⇢ ⌜_(=o₁) → c₁ ← o → c₂⌟
      · rw [← Category.assoc,
        show ConcreteCategory.homOfElement pt(c₁) = ConcreteCategory.homOfElement pt(c₁) ≫
          ⌜c₁ ← o → c₂⌟ ⇢ ⌜o₁ → c₁ ← o(=o₂) → c₂⌟ by ext ⟨⟩; simp [hi]]
        congr 1; ext ⟨⟩ <;> simp [subset_closure hxv, hxC]
      · simp
    · use O3C2.lift3 (Opens.compl ⟨u, uO⟩).indicatorHom C vO.indicatorHom
        (by
          rw [← closeds_indicatorHom_asClosed C, codisjoint_closeds_indicatorHom]
          grw [hCu]; simp [disjoint_compl_left])
        (by
          apply_rw [← Disjoint.inf_left]; rwa [compl_indicatorHom, disjoint_indicatorHom])
        ≫ ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀ → c₀ ← o₁(=o₂) → c₁=o₂(=c₂)⌟
      · apply Mono.right_cancellation (Y := ⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟)
          (f := ⌜o₁ → c₁ ← o₂ → c₂⌟ ⇢ ⌜o₁ → c₁ ← o₂ → c₂ ← _(=o₂)⌟) (self := ?_)
        · simp only [O3C2.lift3, compl_indicatorHom, ConcreteCategory.homOfElement_comp, hom_comp,
          ↓Space.reduceTableHom, ContinuousMap.comp_apply, ↓Space.reduceTableApply]
          ext ⟨⟩
          · simp [hxu]
          · simp [hxC]
          · have : Disjoint ((Opens.mk u uO).indicatorHom ⊓ C) vO.indicatorHom := by
              grw [inf_le_left]; simp [huv]
            simp [this, hxC, hxv]
        · rw [TopCat.mono_iff_injective]; intro x y hxy
          pt_cases x <;> pt_cases y <;> simp at hxy ⊢
      · simp
    · use C ≫ ⌜T → F⌟ ⇢ ⌜_ → _ ← T → F⌟
      · ext ⟨⟩; simp [hxC]
      · simp }
  mpr h := by
    constructor
    intro s x sC hxs
    have sq : CommSq (W := 𝟙_ _) (⌜*⌟ ⇢ ⌜*(=o₁) → _ ← _ → _⌟) (ConcreteCategory.homOfElement x)
        ⌜o₁ → c₁ ← o₂ → c₂⌟ ⇢ ⌜c₁=o₁=o₂(=T) → c₂(=F)⌟ sC.indicatorHom :=
      { w := by ext ⟨⟩; simp [hxs] }
    let ι := CommSq.lift _ (hsq := h (ConcreteCategory.homOfElement x) |>.sq_hasLift sq)
    have hι₁ : _ ≫ ι = _ := sq.fac_left; have hι₂ : ι ≫ _ = _ := sq.fac_right
    rw [TopCat.ext_iff] at hι₁ hι₂; specialize hι₁ ⟨⟩
    rw [Filter.disjoint_iff]
    use ι ⁻¹' {pt(o₂), pt(c₂)}, by
      rw [IsOpen.mem_nhdsSet]
      · intro x hx;
        have := by simpa [hx] using hι₂ x
        generalize hi : ι x = i at this
        pt_cases i <;> simp at this; simp [hi]
      · exact IsOpen.preimage ι.continuous (by decide)
    use ι ⁻¹' {pt(o₁)}, by
      apply IsOpen.mem_nhds
      · exact IsOpen.preimage ι.continuous (by decide)
      · simp at hι₁; simp [hι₁]
    apply Disjoint.preimage; rw [← disjoint_toFinset]; decide

end RegularSpace

end TopCat
