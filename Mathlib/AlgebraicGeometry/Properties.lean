/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `AlgebraicGeometry.IsIntegral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `AlgebraicGeometry.IsReduced`: A scheme is reduced if all the components of the structure sheaf
  are reduced.
-/


-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat Topology

namespace AlgebraicGeometry

variable (X : Scheme)

instance : T0Space X :=
  T0Space.of_open_cover fun x => ⟨_, X.affineCover.covers x,
    (X.affineCover.f x).opensRange.2, IsEmbedding.t0Space (Y := PrimeSpectrum _)
    (isAffineOpen_opensRange (X.affineCover.f x)).isoSpec.schemeIsoToHomeo.isEmbedding⟩

instance : QuasiSober X := by
  apply (config := { allowSynthFailures := true })
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.f x).base)
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.map_prop i).base_open.isOpen_range
  · rintro ⟨_, i, rfl⟩
    exact @IsOpenEmbedding.quasiSober _ _ _ _ _
      (X.affineCover.map_prop i).base_open.isEmbedding.toHomeomorph.symm.isOpenEmbedding
        PrimeSpectrum.quasiSober
  · rw [Set.top_eq_univ, Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x; exact ⟨_, ⟨_, rfl⟩, X.affineCover.covers x⟩

instance {X : Scheme.{u}} : PrespectralSpace X :=
  have (Y : Scheme.{u}) (_ : IsAffine Y) : PrespectralSpace Y :=
    .of_isClosedEmbedding (Y := PrimeSpectrum _) _
      Y.isoSpec.hom.homeomorph.isClosedEmbedding
  have (i : _) : PrespectralSpace (X.affineCover.f i).opensRange.1 :=
    this (X.affineCover.f i).opensRange (isAffineOpen_opensRange (X.affineCover.f i))
  .of_isOpenCover X.affineCover.isOpenCover_opensRange

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
class IsReduced : Prop where
  component_reduced : ∀ U, _root_.IsReduced Γ(X, U) := by infer_instance

attribute [instance] IsReduced.component_reduced

theorem isReduced_of_isReduced_stalk [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [RingHom.map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero

instance isReduced_stalk_of_isReduced [IsReduced X] (x : X) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, (rfl : (X.presheaf.germ U x hxU) s = g)⟩ := X.presheaf.germ_exist x g
  rw [← map_pow, ← map_zero (X.presheaf.germ _ x hxU).hom] at e
  obtain ⟨V, hxV, iU, iV, (e' : (X.presheaf.map iU.op) (s ^ n) = (X.presheaf.map iV.op) 0)⟩ :=
    X.presheaf.germ_eq x hxU hxU _ 0 e
  rw [map_pow, map_zero] at e'
  replace e' := (IsNilpotent.mk _ _ e').eq_zero (R := Γ(X, V))
  rw [← X.presheaf.germ_res iU x hxV, CommRingCat.comp_apply, e', map_zero]

theorem isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  intro U
  have : U = f ⁻¹ᵁ f ''ᵁ U := by
    ext1; exact (Set.preimage_image_eq _ H.base_open.injective).symm
  rw [this]
  exact isReduced_of_injective (inv <| f.app (f ''ᵁ U)).hom
    (asIso <| f.app (f ''ᵁ U) : Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective

instance {R : CommRingCat.{u}} [H : _root_.IsReduced R] : IsReduced (Spec R) := by
  apply (config := { allowSynthFailures := true }) isReduced_of_isReduced_stalk
  intro x; dsimp
  have : _root_.IsReduced (CommRingCat.of <| Localization.AtPrime (PrimeSpectrum.asIdeal x)) := by
    dsimp; infer_instance
  exact isReduced_of_injective (StructureSheaf.stalkIso R x).hom.hom
    (StructureSheaf.stalkIso R x).commRingCatIsoToRingEquiv.injective

theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (Spec R) ↔ _root_.IsReduced R := by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_isAffine_isReduced [IsAffine X] [_root_.IsReduced Γ(X, ⊤)] :
    IsReduced X :=
  isReduced_of_isOpenImmersion X.isoSpec.hom

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immersion `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
@[elab_as_elim]
theorem reduce_to_affine_global (P : ∀ {X : Scheme} (_ : X.Opens), Prop)
    {X : Scheme} (U : X.Opens)
    (h₁ : ∀ (X : Scheme) (U : X.Opens),
      (∀ x : U, ∃ (V : _) (_ : x.1 ∈ V) (_ : V ⟶ U), P V) → P U)
    (h₂ : ∀ (X Y) (f : X ⟶ Y) [IsOpenImmersion f],
      ∃ (U : X.Opens) (V : Y.Opens), U = ⊤ ∧ V = f.opensRange ∧ (P U → P V))
    (h₃ : ∀ R : CommRingCat, P (X := Spec R) ⊤) : P U := by
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.map_prop j).base_open.isOpen_range⟩
  let i' : U' ⟶ U := homOfLE i
  refine ⟨U', hx, i', ?_⟩
  obtain ⟨_, _, rfl, rfl, h₂'⟩ := h₂ _ _ (X.affineBasisCover.f j)
  apply h₂'
  apply h₃

theorem reduce_to_affine_nbhd (P : ∀ (X : Scheme) (_ : X), Prop)
    (h₁ : ∀ R x, P (Spec R) x)
    (h₂ : ∀ {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X), P X x → P Y (f.base x)) :
    ∀ (X : Scheme) (x : X), P X x := by
  intro X x
  obtain ⟨y, e⟩ := X.affineCover.covers x
  convert h₂ (X.affineCover.f (X.affineCover.idx x)) y _
  · rw [e]
  apply h₁

theorem eq_zero_of_basicOpen_eq_bot {X : Scheme} [hX : IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) (hs : X.basicOpen s = ⊥) : s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [RingHom.map_zero]
  induction U using reduce_to_affine_global generalizing hX with
  | h₁ X U H =>
    obtain ⟨V, hx, i, H⟩ := H ⟨x, hx⟩
    specialize H (X.presheaf.map i.op s)
    rw [Scheme.basicOpen_res, hs] at H
    specialize H (inf_bot_eq _) x hx
    rw [← X.sheaf.presheaf.germ_res_apply i x hx s]
    exact H
  | h₂ X Y f =>
    refine ⟨f ⁻¹ᵁ f.opensRange, f.opensRange, by simp, rfl, ?_⟩
    rintro H hX s hs _ ⟨x, rfl⟩
    haveI := isReduced_of_isOpenImmersion f
    specialize H (f.app _ s) _ x ⟨x, rfl⟩
    · rw [← Scheme.preimage_basicOpen, hs]; ext1; simp [Opens.map]
    · have H : (X.presheaf.germ _ x _).hom _ = 0 := H
      rw [← Scheme.stalkMap_germ_apply f ⟨_, _⟩ x] at H
      apply_fun inv <| f.stalkMap x at H
      rw [← CommRingCat.comp_apply, CategoryTheory.IsIso.hom_inv_id, map_zero] at H
      exact H
  | h₃ R =>
    rw [basicOpen_eq_of_affine', PrimeSpectrum.basicOpen_eq_bot_iff] at hs
    replace hs := (hs.map (Scheme.ΓSpecIso R).inv.hom).eq_zero
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hs
    rw [hs, map_zero]

@[simp]
theorem basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) : X.basicOpen s = ⊥ ↔ s = 0 := by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp

/-- A scheme `X` is integral if its is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class IsIntegral : Prop where
  nonempty : Nonempty X := by infer_instance
  component_integral : ∀ (U : X.Opens) [Nonempty U], IsDomain Γ(X, U) := by infer_instance

attribute [instance] IsIntegral.component_integral IsIntegral.nonempty

instance [IsIntegral X] : IsDomain Γ(X, ⊤) :=
  @IsIntegral.component_integral _ _ _ ⟨Nonempty.some inferInstance, trivial⟩

instance (priority := 900) isReduced_of_isIntegral [IsIntegral X] : IsReduced X := by
  constructor
  intro U
  rcases U.1.eq_empty_or_nonempty with h | h
  · have : U = ⊥ := SetLike.ext' h
    haveI : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty this)
    infer_instance
  · haveI : Nonempty U := by simpa
    infer_instance

instance Scheme.component_nontrivial (X : Scheme.{u}) (U : X.Opens) [Nonempty U] :
    Nontrivial Γ(X, U) :=
  LocallyRingedSpace.component_nontrivial (hU := ‹_›)

instance irreducibleSpace_of_isIntegral [IsIntegral X] : IrreducibleSpace X := by
  by_contra H
  replace H : ¬IsPreirreducible (⊤ : Set X) := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  rw [Set.not_top_subset] at h₂ h₃
  haveI : Nonempty (⟨Sᶜ, hS.1⟩ : X.Opens) := ⟨⟨_, h₂.choose_spec⟩⟩
  haveI : Nonempty (⟨Tᶜ, hT.1⟩ : X.Opens) := ⟨⟨_, h₃.choose_spec⟩⟩
  haveI : Nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : X.Opens) := ⟨⟨_, Or.inl h₂.choose_spec⟩⟩
  let e : Γ(X, _) ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ ?_).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  · have : IsDomain (Γ(X, ⟨Sᶜ, hS.1⟩) × Γ(X, ⟨Tᶜ, hT.1⟩)) :=
      e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    exact false_of_nontrivial_of_product_domain Γ(X, ⟨Sᶜ, hS.1⟩) Γ(X, ⟨Tᶜ, hT.1⟩)
  · ext x
    constructor
    · rintro ⟨hS, hT⟩
      rcases h₁ (show x ∈ ⊤ by trivial) with h | h
      exacts [hS h, hT h]
    · simp

theorem isIntegral_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X] :
    IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  haveI := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine ⟨fun {a b} e => ?_⟩
    simp_rw [← basicOpen_eq_bot_iff, ← Opens.not_nonempty_iff_eq_bot]
    by_contra! h
    obtain ⟨x, ⟨hxU, hx₁⟩, _, hx₂⟩ :=
      nonempty_preirreducible_inter (X.basicOpen a).2 (X.basicOpen b).2 h.1 h.2
    replace e := congr_arg (X.presheaf.germ U x hxU) e
    rw [RingHom.map_mul, RingHom.map_zero] at e
    refine zero_ne_one' (X.presheaf.stalk x) (isUnit_zero_iff.1 ?_)
    convert hx₁.mul hx₂
    exact e.symm
  exact NoZeroDivisors.to_isDomain _

theorem isIntegral_iff_irreducibleSpace_and_isReduced :
    IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩

theorem isIntegral_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsIntegral Y] [Nonempty X] : IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  have : U = f ⁻¹ᵁ f ''ᵁ U := by ext1; exact (Set.preimage_image_eq _ H.base_open.injective).symm
  rw [this]
  have : IsDomain Γ(Y, f ''ᵁ U) := by
    apply (config := { allowSynthFailures := true }) IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.app (f ''ᵁ U) :
    Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

instance {R : CommRingCat} [IsDomain R] : IrreducibleSpace (Spec R) := by
  convert PrimeSpectrum.irreducibleSpace (R := R)

instance {R : CommRingCat} [IsDomain R] : IsIntegral (Spec R) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

theorem affine_isIntegral_iff (R : CommRingCat) :
    IsIntegral (Spec R) ↔ IsDomain R :=
  ⟨fun _ => MulEquiv.isDomain Γ(Spec R, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩

theorem isIntegral_of_isAffine_of_isDomain [IsAffine X] [Nonempty X] [IsDomain Γ(X, ⊤)] :
    IsIntegral X :=
  isIntegral_of_isOpenImmersion X.isoSpec.hom

theorem map_injective_of_isIntegral [IsIntegral X] {U V : X.Opens} (i : U ⟶ V)
    [H : Nonempty U] : Function.Injective (X.presheaf.map i.op) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← basicOpen_eq_bot_iff] at hx ⊢
  rw [Scheme.basicOpen_res] at hx
  revert hx
  contrapose!
  simp_rw [Ne, ← Opens.not_nonempty_iff_eq_bot, Classical.not_not]
  apply nonempty_preirreducible_inter U.isOpen (RingedSpace.basicOpen _ _).isOpen
  simpa using H

noncomputable
instance [IsIntegral X] : OrderTop X where
  top := genericPoint X
  le_top a := genericPoint_specializes a

end AlgebraicGeometry
