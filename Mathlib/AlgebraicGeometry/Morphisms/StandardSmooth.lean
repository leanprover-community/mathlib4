/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.RingHom.StandardSmooth

#align_import algebraic_geometry.morphisms.finite_type from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Standard smooth morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is locally standard-smooth if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism of schemes `f : X ⟶ Y` is standard smooth if for every
`x : X` there exists an affine open neighbourhood `V` of `x` and an affine open `U ⊆ Y` such that
`V ⊆ f ⁻¹' U` and induced map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.
-/
@[mk_iff]
class IsStandardSmooth : Prop where
  locally_standardSmooth :
    ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).IsStandardSmooth
/--
A morphism of schemes `f : X ⟶ Y` is standard smooth of relative dimension `n` if for every
`x : X` there exists an affine open neighbourhood `V` of `x` and an affine open `U ⊆ Y` such that
`V ⊆ f ⁻¹' U` and induced map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth of relative dimension `n`.
-/
@[mk_iff]
class IsStandardSmoothOfRelativeDimension (n : ℕ) (f : X ⟶ Y) : Prop where
  locally_standardSmooth_of_relativeDimension :
    ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).IsStandardSmoothOfRelativeDimension n

/--
A morphism of schemes `f : X ⟶ Y` is a smooth curve if it is smooth
of relative dimension one and separated.
-/
class IsSmoothCurve (f : X ⟶ Y) : Prop where
  /-- `f` is smooth of rel. dimension one. -/
  smooth_of_relativeDimension_one : IsStandardSmoothOfRelativeDimension 1 f
  /-- `f` is separated. -/
  isSeparated : IsSeparated f

def standardSmoothAffineTarget : AffineTargetMorphismProperty := fun _ _ f _ ↦
  IsStandardSmooth f

lemma standardSmooth_iff' :
    IsStandardSmooth f ↔ ∀ (x : X) (V : Opens X) (_ : x ∈ V),
      ∃ (V' : X.affineOpens) (_ : V' ≤ V) (_ : x ∈ V'.1) (U : Y.affineOpens) (e : V'.1 ≤ f ⁻¹ᵁ U.1),
        (f.appLE U V' e).IsStandardSmooth := by
  rw [isStandardSmooth_iff]
  constructor
  · intro hf x V hx
    obtain ⟨U', V', hx', e, hUV'⟩ := hf x
    have hx_mem_inter : x ∈ V ⊓ V'.1 := ⟨hx, hx'⟩
    obtain ⟨r', hBr', hBx⟩ := V'.2.exists_basicOpen_le ⟨x, hx_mem_inter⟩ hx'
    have hBr'_isAffine : IsAffineOpen (X.basicOpen r') := V'.2.basicOpen r'
    let bV' : X.affineOpens := ⟨X.basicOpen r', hBr'_isAffine⟩
    have hBr'' : bV' ≤ V'.1 := hBr'.trans inf_le_right
    have e' : bV' ≤ f ⁻¹ᵁ U'.1 := hBr''.trans e
    refine ⟨bV', hBr'.trans inf_le_left, hBx, U', e', ?_⟩
    · have : Scheme.Hom.appLE f U' bV' e' =
          Scheme.Hom.appLE f U' V' e ≫ (X.presheaf.map (homOfLE hBr'').op) := by
        simp
      rw [this]
      apply RingHom.IsStandardSmooth.comp
      · have : IsLocalization.Away r' Γ(X, X.basicOpen r') := V'.2.isLocalization_basicOpen r'
        rw [RingHom.IsStandardSmooth]
        exact Algebra.IsStandardSmooth.of_isLocalizationAway _ _ r'
      · exact hUV'
  · intro h x
    obtain ⟨V, _, hx, U, e, hUV⟩ := h x ⊤ trivial
    use U, V, hx, e

lemma standardSmooth_iff'' :
    IsStandardSmooth f ↔
      ∀ (x : X) (V : Opens X) (_ : x ∈ V) (U : Opens Y) (_ : f.val.base x ∈ U),
      ∃ (V' : X.affineOpens) (_ : V' ≤ V) (_ : x ∈ V'.1)
        (U' : Y.affineOpens) (_ : U' ≤ U) (e : V'.1 ≤ f ⁻¹ᵁ U'.1),
        (f.appLE U' V' e).IsStandardSmooth := by
  rw [standardSmooth_iff']
  constructor
  · intro h x V hxV U hfxU
    let W := V ⊓ f ⁻¹ᵁ U
    have hxW : x ∈ W := ⟨hxV, hfxU⟩
    obtain ⟨V', hV'W, hxV', U', e, hVU'⟩ := h x W hxW
    let y : Y := f.val.base x
    have hy_mem_inter : y ∈ U ⊓ U'.1 := ⟨hfxU, e hxV'⟩
    obtain ⟨r', hBr', hBy⟩ := U'.2.exists_basicOpen_le ⟨y, hy_mem_inter⟩ (e hxV')
    let s : Γ(X, V') := Scheme.Hom.appLE f U' V' e r'
    let bV' : X.affineOpens := ⟨X.basicOpen s, V'.2.basicOpen s⟩
    let bU' : Y.affineOpens := ⟨Y.basicOpen r', U'.2.basicOpen r'⟩
    have e' : bV' ≤ f ⁻¹ᵁ bU' := by
      simpa [Scheme.Hom.appLE] using X.basicOpen_restrict _ _
    refine ⟨bV', ?_, ?_, bU', ?_, e', ?_⟩
    · trans
      · exact X.basicOpen_le s
      · exact hV'W.trans inf_le_left
    · simp [s]
      show x ∈ X.basicOpen ((Scheme.Hom.appLE f U' V' e) r')
      let x' : V'.1 := ⟨x, hxV'⟩
      show x'.val ∈ _
      rw [X.mem_basicOpen]
      simp [Scheme.Hom.appLE]
      show IsUnit ((X.presheaf.germ x') ((X.presheaf.map (homOfLE e).op) ((Scheme.Hom.app f ↑U') r')))
      rw [X.presheaf.germ_res_apply]
      simp
      rw [← X.mem_basicOpen]
      simp
      rw [← Scheme.preimage_basicOpen]
      show f.val.base x ∈ Y.basicOpen r'
      show y ∈ Y.basicOpen r'
      exact hBy
    · exact hBr'.trans inf_le_left
    · letI := U'.2.isLocalization_basicOpen r'
      letI := V'.2.isLocalization_basicOpen s
      show RingHom.IsStandardSmooth (f.appLE (Y.basicOpen r') (X.basicOpen (f.appLE U' V' e r')) e')
      rw [U'.2.appLE_eq_away_map _ V'.2]
      apply RingHom.IsStandardSmooth.isLocalizationAway_map
      exact hVU'
  · intro h x V hxV
    obtain ⟨V', hV'V, hxV', U', _, e, hUV'⟩ := h x V hxV ⊤ trivial
    use V', hV'V, hxV', U', e

lemma standardSmooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [hf : IsStandardSmooth f]
    [hg : IsStandardSmooth g] : IsStandardSmooth (f ≫ g) := by
  constructor
  intro x
  sorry

lemma standardSmoothAffineTarget_isLocal :
    standardSmoothAffineTarget.IsLocal where
  RespectsIso := sorry
  toBasicOpen {X Y} _ f a hf := by
    dsimp only [standardSmoothAffineTarget] at hf ⊢
    rw [standardSmooth_iff''] at hf
    constructor
    intro x
    replace hf := hf x.val (f ⁻¹ᵁ Y.basicOpen a) x.property (Y.basicOpen a) x.property
    obtain ⟨U, hU, hxU, V, hV, e, hUV⟩ := hf
    let V' : Opens (Y ∣_ᵤ Y.basicOpen a) :=
      Scheme.ιOpens (Y.basicOpen a) ⁻¹ᵁ V.1
    have hV' : IsAffineOpen V' := by
      apply V.2.ιOpens_basicOpen_preimage
    let U' : Opens (X ∣_ᵤ f ⁻¹ᵁ Y.basicOpen a) :=
      Scheme.ιOpens (f ⁻¹ᵁ Y.basicOpen a) ⁻¹ᵁ U.1
    have hU' : IsAffineOpen U' := by
      simp [U']
      rw [Scheme.preimage_basicOpen]
      apply U.2.ιOpens_basicOpen_preimage
    refine ⟨⟨V', hV'⟩, ⟨U', hU'⟩, ?_, ?_, ?_⟩
    · simpa
    · simp
      intro y hy
      simp [V']
      simp [U'] at hy
      sorry
    · simp [U', V']
      have e₁ : Scheme.ιOpens (Y.basicOpen a) ''ᵁ
        (Opens.map (Y.basicOpen a).inclusion).obj ↑V = V := by
        simpa
      have e₂ : Scheme.ιOpens (f ⁻¹ᵁ Y.basicOpen a) ''ᵁ
          (Opens.map (f ⁻¹ᵁ Y.basicOpen a).inclusion).obj ↑U = U := by
        simp only [Opens.functor_map_eq_inf, Scheme.preimage_basicOpen, Opens.map_top, inf_eq_left]
        erw [← Scheme.preimage_basicOpen f a]
        assumption
      rw [Scheme.Hom.appLE_congr f _ e₁ e₂ RingHom.IsStandardSmooth]
      exact hUV
  ofBasicOpenCover {X Y} _ f s hs hf := by
    sorry
/-
    intro y
    let U : Opens Y := ⊤
    have hU : IsAffineOpen U := isAffineOpen_top Y
    rw [← hU.basicOpen_union_eq_self_iff] at hs
    have : y ∈ ⨆ (f : s), Y.basicOpen f.val := by erw [hs]; trivial
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion, SetLike.mem_coe] at this
    obtain ⟨i, hy⟩ := this
    clear hs hU U
    have hi := hf i ⟨y, hy⟩
    obtain ⟨U, hy', V, e, hUV⟩ := hi
    let U' : Opens Y := Scheme.ιOpens (Y.basicOpen i.val) ''ᵁ U.val
    have hU' : IsAffineOpen U' := sorry
    let V' : Opens X := Scheme.ιOpens _ ''ᵁ V.val
    let hV' : IsAffineOpen V' := sorry
    refine ⟨⟨U', hU'⟩, ?_, ⟨V', hV'⟩, ?_, ?_⟩
    · exact ⟨⟨y, hy⟩, hy', rfl⟩
    · simp only [ge_iff_le, V', U']
      rintro x ⟨x, hx, rfl⟩
      simp
      refine ⟨(f ∣_ Y.basicOpen i.val).val.base x, e hx, ?_⟩
      rw [morphismRestrict_val_base]
      rfl
    · rw [morphismRestrict_appLE] at hUV
      exact hUV
-/

end

end AlgebraicGeometry
