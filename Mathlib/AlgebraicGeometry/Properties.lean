/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.LocalProperties

#align_import algebraic_geometry.properties from "leanprover-community/mathlib"@"88474d1b5af6d37c2ab728b757771bced7f5194c"

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `AlgebraicGeometry.IsIntegral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `AlgebraicGeometry.IsReduced`: A scheme is reduced if all the components of the structure sheaf
  are reduced.
-/


-- Explicit universe annotations were used in this file to improve perfomance #12737

universe u

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

instance : T0Space X := by
  refine T0Space.of_open_cover fun x => ?_
  obtain ⟨U, R, ⟨e⟩⟩ := X.local_affine x
  let e' : U.1 ≃ₜ PrimeSpectrum R :=
    homeoOfIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).mapIso e)
  exact ⟨U.1.1, U.2, U.1.2, e'.embedding.t0Space⟩

instance : QuasiSober X := by
  apply (config := { allowSynthFailures := true })
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.map x).1.base)
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.IsOpen i).base_open.isOpen_range
  · rintro ⟨_, i, rfl⟩
    exact @OpenEmbedding.quasiSober _ _ _ _ _
      (X.affineCover.IsOpen i).base_open.toHomeomorph.symm.openEmbedding PrimeSpectrum.quasiSober
  · rw [Set.top_eq_univ, Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x; exact ⟨_, ⟨_, rfl⟩, X.affineCover.Covers x⟩

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
class IsReduced : Prop where
  component_reduced : ∀ U, IsReduced Γ(X, U) := by infer_instance
#align algebraic_geometry.is_reduced AlgebraicGeometry.IsReduced

attribute [instance] IsReduced.component_reduced

theorem isReduced_of_isReduced_stalk [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x
  rw [RingHom.map_zero]
  change X.presheaf.germ x s = 0
  exact (hs.map _).eq_zero
#align algebraic_geometry.is_reduced_of_stalk_is_reduced AlgebraicGeometry.isReduced_of_isReduced_stalk

instance isReduced_stalk_of_isReduced [IsReduced X] (x : X) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.germ_exist x g
  rw [← map_pow, ← map_zero (X.presheaf.germ ⟨x, hxU⟩)] at e
  obtain ⟨V, hxV, iU, iV, e'⟩ := X.presheaf.germ_eq x hxU hxU _ 0 e
  rw [map_pow, map_zero] at e'
  replace e' := (IsNilpotent.mk _ _ e').eq_zero (R := Γ(X, V))
  erw [← ConcreteCategory.congr_hom (X.presheaf.germ_res iU ⟨x, hxV⟩) s]
  rw [comp_apply, e', map_zero]
#align algebraic_geometry.stalk_is_reduced_of_reduced AlgebraicGeometry.isReduced_stalk_of_isReduced

theorem isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  intro U
  have : U = f ⁻¹ᵁ f ''ᵁ U := by
    ext1; exact (Set.preimage_image_eq _ H.base_open.inj).symm
  rw [this]
  exact isReduced_of_injective (inv <| f.1.c.app (op <| f ''ᵁ U))
    (asIso <| f.1.c.app (op <| f ''ᵁ U) :
      Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective
#align algebraic_geometry.is_reduced_of_open_immersion AlgebraicGeometry.isReduced_of_isOpenImmersion

instance {R : CommRingCat.{u}} [H : _root_.IsReduced R] : IsReduced (𝖲𝗉𝖾𝖼 R) := by
  apply (config := { allowSynthFailures := true }) isReduced_of_isReduced_stalk
  intro x; dsimp
  have : _root_.IsReduced (CommRingCat.of <| Localization.AtPrime (PrimeSpectrum.asIdeal x)) := by
    dsimp; infer_instance
  rw [show (Scheme.Spec.obj <| op R).presheaf = (Spec.structureSheaf R).presheaf from rfl]
  exact isReduced_of_injective (StructureSheaf.stalkIso R x).hom
    (StructureSheaf.stalkIso R x).commRingCatIsoToRingEquiv.injective

theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (𝖲𝗉𝖾𝖼 R) ↔ _root_.IsReduced R := by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  have : _root_.IsReduced
      (LocallyRingedSpace.Γ.obj (op <| Spec.toLocallyRingedSpace.obj <| op R)) := by
    change _root_.IsReduced ((Scheme.Spec.obj <| op R).presheaf.obj <| op ⊤); infer_instance
  exact isReduced_of_injective (toSpecΓ R) (asIso <| toSpecΓ R).commRingCatIsoToRingEquiv.injective
#align algebraic_geometry.affine_is_reduced_iff AlgebraicGeometry.affine_isReduced_iff

theorem isReduced_of_isAffine_isReduced [IsAffine X] [h : _root_.IsReduced Γ(X, ⊤)] :
    IsReduced X :=
  haveI : IsReduced (𝖲𝗉𝖾𝖼 (Scheme.Γ.obj (op X))) := by
    rw [affine_isReduced_iff]; exact h
  isReduced_of_isOpenImmersion X.isoSpec.hom
#align algebraic_geometry.is_reduced_of_is_affine_is_reduced AlgebraicGeometry.isReduced_of_isAffine_isReduced

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immerison `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
@[elab_as_elim]
theorem reduce_to_affine_global (P : ∀ {X : Scheme} (_ : Opens X), Prop)
    {X : Scheme} (U : Opens X)
    (h₁ : ∀ (X : Scheme) (U : Opens X),
      (∀ x : U, ∃ (V : _) (_ : x.1 ∈ V) (_ : V ⟶ U), P V) → P U)
    (h₂ : ∀ (X Y) (f : X ⟶ Y) [hf : IsOpenImmersion f],
      ∃ (U : Set X) (V : Set Y) (hU : U = ⊤) (hV : V = Set.range f.1.base),
        P ⟨U, hU.symm ▸ isOpen_univ⟩ → P ⟨V, hV.symm ▸ hf.base_open.isOpen_range⟩)
    (h₃ : ∀ R : CommRingCat, P (X := 𝖲𝗉𝖾𝖼 R) ⊤) : P U := by
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.IsOpen j).base_open.isOpen_range⟩
  let i' : U' ⟶ U := homOfLE i
  refine ⟨U', hx, i', ?_⟩
  obtain ⟨_, _, rfl, rfl, h₂'⟩ := h₂ _ _ (X.affineBasisCover.map j)
  apply h₂'
  apply h₃
#align algebraic_geometry.reduce_to_affine_global AlgebraicGeometry.reduce_to_affine_global

theorem reduce_to_affine_nbhd (P : ∀ (X : Scheme) (_ : X.carrier), Prop)
    (h₁ : ∀ (R : CommRingCat) (x : PrimeSpectrum R), P (Scheme.Spec.obj <| op R) x)
    (h₂ : ∀ {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X.carrier), P X x → P Y (f.1.base x)) :
    ∀ (X : Scheme) (x : X.carrier), P X x := by
  intro X x
  obtain ⟨y, e⟩ := X.affineCover.Covers x
  convert h₂ (X.affineCover.map (X.affineCover.f x)) y _
  · rw [e]
  apply h₁
#align algebraic_geometry.reduce_to_affine_nbhd AlgebraicGeometry.reduce_to_affine_nbhd

theorem eq_zero_of_basicOpen_eq_bot {X : Scheme} [hX : IsReduced X] {U : Opens X}
    (s : Γ(X, U)) (hs : X.basicOpen s = ⊥) : s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x
  rw [RingHom.map_zero]
  induction U using reduce_to_affine_global generalizing hX with
  | h₁ X U hx =>
    obtain ⟨V, hx, i, H⟩ := hx x
    specialize H (X.presheaf.map i.op s)
    erw [Scheme.basicOpen_res] at H
    rw [hs] at H
    specialize H (inf_bot_eq _) ⟨x, hx⟩
    erw [TopCat.Presheaf.germ_res_apply] at H
    exact H
  | h₂ X Y f =>
    have e : f.val.base ⁻¹' Set.range ↑f.val.base = Set.univ := by
      rw [← Set.image_univ, Set.preimage_image_eq _ ‹IsOpenImmersion f›.base_open.inj]
    refine ⟨_, _, e, rfl, ?_⟩
    rintro H hX s hs ⟨_, x, rfl⟩
    haveI := isReduced_of_isOpenImmersion f
    specialize H (f.1.c.app _ s) _ ⟨x, by rw [Opens.mem_mk, e]; trivial⟩
    · rw [← Scheme.preimage_basicOpen, hs]; ext1; simp [Opens.map]
    · erw [← PresheafedSpace.stalkMap_germ_apply f.1 ⟨_, _⟩ ⟨x, _⟩] at H
      apply_fun inv <| PresheafedSpace.stalkMap f.val x at H
      erw [CategoryTheory.IsIso.hom_inv_id_apply, map_zero] at H
      exact H
  | h₃ R =>
    erw [basicOpen_eq_of_affine', PrimeSpectrum.basicOpen_eq_bot_iff] at hs
    replace hs := hs.map (Scheme.SpecΓIdentity.app R).inv
    -- what the hell?!
    replace hs := @IsNilpotent.eq_zero _ _ _ _ (show _ from ?_) hs
    · rw [Iso.hom_inv_id_apply] at hs
      rw [hs, map_zero]
    exact @IsReduced.component_reduced _ hX ⊤
#align algebraic_geometry.eq_zero_of_basic_open_eq_bot AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot

@[simp]
theorem basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : Opens X.carrier}
    (s : X.presheaf.obj <| op U) : X.basicOpen s = ⊥ ↔ s = 0 := by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp
#align algebraic_geometry.basic_open_eq_bot_iff AlgebraicGeometry.basicOpen_eq_bot_iff

/-- A scheme `X` is integral if its carrier is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class IsIntegral : Prop where
  nonempty : Nonempty X := by infer_instance
  component_integral : ∀ (U : Opens X) [Nonempty U], IsDomain Γ(X, U) := by infer_instance
#align algebraic_geometry.is_integral AlgebraicGeometry.IsIntegral

attribute [instance] IsIntegral.component_integral IsIntegral.nonempty

instance [h : IsIntegral X] : IsDomain (X.presheaf.obj (op ⊤)) :=
  @IsIntegral.component_integral _ _ _ (by
    simp only [Set.univ_nonempty, Opens.nonempty_coeSort, Opens.coe_top])

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
#align algebraic_geometry.is_reduced_of_is_integral AlgebraicGeometry.isReduced_of_isIntegral

instance irreducibleSpace_of_isIntegral [IsIntegral X] : IrreducibleSpace X := by
  by_contra H
  replace H : ¬IsPreirreducible (⊤ : Set X) := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_closed_union_closed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  erw [not_forall] at h₂ h₃
  simp_rw [not_forall] at h₂ h₃
  haveI : Nonempty (⟨Sᶜ, hS.1⟩ : Opens X) := ⟨⟨_, h₂.choose_spec.choose_spec⟩⟩
  haveI : Nonempty (⟨Tᶜ, hT.1⟩ : Opens X) := ⟨⟨_, h₃.choose_spec.choose_spec⟩⟩
  haveI : Nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : Opens X) :=
    ⟨⟨_, Or.inl h₂.choose_spec.choose_spec⟩⟩
  let e : Γ(X, _) ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ ?_).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  · apply (config := { allowSynthFailures := true }) false_of_nontrivial_of_product_domain
    · exact e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    · apply X.toLocallyRingedSpace.component_nontrivial
    · apply X.toLocallyRingedSpace.component_nontrivial
  · ext x
    constructor
    · rintro ⟨hS, hT⟩
      cases' h₁ (show x ∈ ⊤ by trivial) with h h
      exacts [hS h, hT h]
    · intro x
      exact x.rec (by contradiction)
#align algebraic_geometry.is_irreducible_of_is_integral AlgebraicGeometry.irreducibleSpace_of_isIntegral

theorem isIntegral_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X.carrier] :
    IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  haveI := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine ⟨fun {a b} e => ?_⟩
    simp_rw [← basicOpen_eq_bot_iff, ← Opens.not_nonempty_iff_eq_bot]
    by_contra! h
    obtain ⟨_, ⟨x, hx₁, rfl⟩, ⟨x, hx₂, e'⟩⟩ :=
      nonempty_preirreducible_inter (X.basicOpen a).2 (X.basicOpen b).2 h.1 h.2
    replace e' := Subtype.eq e'
    subst e'
    replace e := congr_arg (X.presheaf.germ x) e
    rw [RingHom.map_mul, RingHom.map_zero] at e
    refine zero_ne_one' (X.presheaf.stalk x.1) (isUnit_zero_iff.1 ?_)
    convert hx₁.mul hx₂
    exact e.symm
  exact NoZeroDivisors.to_isDomain _
#align algebraic_geometry.is_integral_of_is_irreducible_is_reduced AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced

theorem isIntegral_iff_irreducibleSpace_and_isReduced :
    IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩
#align algebraic_geometry.is_integral_iff_is_irreducible_and_is_reduced AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced

theorem isIntegral_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsIntegral Y] [Nonempty X] : IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  have : U = f ⁻¹ᵁ f ''ᵁ U := by ext1; exact (Set.preimage_image_eq _ H.base_open.inj).symm
  rw [this]
  have : IsDomain Γ(Y, f ''ᵁ U) := by
    apply (config := { allowSynthFailures := true }) IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.1.c.app (op <| f ''ᵁ U) :
    Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
#align algebraic_geometry.is_integral_of_open_immersion AlgebraicGeometry.isIntegral_of_isOpenImmersion

instance {R : CommRingCat} [IsDomain R] : IrreducibleSpace (𝖲𝗉𝖾𝖼 R) := by
  convert PrimeSpectrum.irreducibleSpace (R := R)

instance {R : CommRingCat} [IsDomain R] : IsIntegral (𝖲𝗉𝖾𝖼 R) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

theorem affine_isIntegral_iff (R : CommRingCat) :
    IsIntegral (𝖲𝗉𝖾𝖼 R) ↔ IsDomain R :=
  ⟨fun _ => MulEquiv.isDomain Γ(𝖲𝗉𝖾𝖼 R, ⊤)
    (asIso <| toSpecΓ R).commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩
#align algebraic_geometry.affine_is_integral_iff AlgebraicGeometry.affine_isIntegral_iff

theorem isIntegral_of_isAffine_of_isDomain [IsAffine X] [Nonempty X]
    [h : IsDomain Γ(X, ⊤)] : IsIntegral X :=
  haveI : IsIntegral (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))) := by
    rw [affine_isIntegral_iff]; exact h
  isIntegral_of_isOpenImmersion X.isoSpec.hom
#align algebraic_geometry.is_integral_of_is_affine_is_domain AlgebraicGeometry.isIntegral_of_isAffine_of_isDomain

theorem map_injective_of_isIntegral [IsIntegral X] {U V : Opens X} (i : U ⟶ V)
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
#align algebraic_geometry.map_injective_of_is_integral AlgebraicGeometry.map_injective_of_isIntegral

end AlgebraicGeometry
