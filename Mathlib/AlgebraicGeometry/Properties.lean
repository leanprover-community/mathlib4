/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Nilpotent
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


open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

instance : T0Space X.carrier := by
  refine' T0Space.of_open_cover fun x => _
  -- ⊢ ∃ s, x ∈ s ∧ IsOpen s ∧ T0Space ↑s
  obtain ⟨U, R, ⟨e⟩⟩ := X.local_affine x
  -- ⊢ ∃ s, x ∈ s ∧ IsOpen s ∧ T0Space ↑s
  let e' : U.1 ≃ₜ PrimeSpectrum R :=
    homeoOfIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).mapIso e)
  exact ⟨U.1.1, U.2, U.1.2, e'.embedding.t0Space⟩
  -- 🎉 no goals

instance : QuasiSober X.carrier := by
  apply (config := { allowSynthFailures := true })
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.map x).1.base)
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.IsOpen i).base_open.open_range
    -- ⊢ IsOpen ↑{ val := (fun x => Set.range ↑(Scheme.OpenCover.map (Scheme.affineCo …
                        -- 🎉 no goals
  · rintro ⟨_, i, rfl⟩
    -- ⊢ QuasiSober ↑↑{ val := (fun x => Set.range ↑(Scheme.OpenCover.map (Scheme.aff …
    exact @OpenEmbedding.quasiSober _ _ _ _ _ (Homeomorph.ofEmbedding _
      (X.affineCover.IsOpen i).base_open.toEmbedding).symm.openEmbedding PrimeSpectrum.quasiSober
  · rw [Set.top_eq_univ, Set.sUnion_range, Set.eq_univ_iff_forall]
    -- ⊢ ∀ (x : (forget TopCat).obj ↑X.toPresheafedSpace), x ∈ ⋃ (x : (Scheme.affineC …
    intro x; exact ⟨_, ⟨_, rfl⟩, X.affineCover.Covers x⟩
    -- ⊢ x ∈ ⋃ (x : (Scheme.affineCover X).J), Set.range ↑(Scheme.OpenCover.map (Sche …
             -- 🎉 no goals

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
class IsReduced : Prop where
  component_reduced : ∀ U, IsReduced (X.presheaf.obj (op U)) := by infer_instance
#align algebraic_geometry.is_reduced AlgebraicGeometry.IsReduced

attribute [instance] IsReduced.component_reduced

theorem isReducedOfStalkIsReduced [∀ x : X.carrier, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine' ⟨fun U => ⟨fun s hs => _⟩⟩
  -- ⊢ s = 0
  apply Presheaf.section_ext X.sheaf U s 0
  -- ⊢ ∀ (x : { x // x ∈ U }), ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) …
  intro x
  -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = ↑(Presheaf.germ (Sh …
  rw [RingHom.map_zero]
  -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
  change X.presheaf.germ x s = 0
  -- ⊢ ↑(Presheaf.germ X.presheaf x) s = 0
  exact (hs.map _).eq_zero
  -- 🎉 no goals
#align algebraic_geometry.is_reduced_of_stalk_is_reduced AlgebraicGeometry.isReducedOfStalkIsReduced

instance stalk_isReduced_of_reduced [IsReduced X] (x : X.carrier) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  -- ⊢ ∀ (x_1 : ↑(Presheaf.stalk X.presheaf x)), IsNilpotent x_1 → x_1 = 0
  rintro g ⟨n, e⟩
  -- ⊢ g = 0
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.germ_exist x g
  -- ⊢ ↑(Presheaf.germ X.presheaf { val := x, property := hxU }) s = 0
  rw [← map_pow, ← map_zero (X.presheaf.germ ⟨x, hxU⟩)] at e
  -- ⊢ ↑(Presheaf.germ X.presheaf { val := x, property := hxU }) s = 0
  obtain ⟨V, hxV, iU, iV, e'⟩ := X.presheaf.germ_eq x hxU hxU _ 0 e
  -- ⊢ ↑(Presheaf.germ X.presheaf { val := x, property := hxU }) s = 0
  rw [map_pow, map_zero] at e'
  -- ⊢ ↑(Presheaf.germ X.presheaf { val := x, property := hxU }) s = 0
  replace e' := (IsNilpotent.mk _ _ e').eq_zero (R := X.presheaf.obj <| op V)
  -- ⊢ ↑(Presheaf.germ X.presheaf { val := x, property := hxU }) s = 0
  erw [← ConcreteCategory.congr_hom (X.presheaf.germ_res iU ⟨x, hxV⟩) s]
  -- ⊢ ↑(X.presheaf.map iU.op ≫ Presheaf.germ X.presheaf { val := x, property := hx …
  rw [comp_apply, e', map_zero]
  -- 🎉 no goals
#align algebraic_geometry.stalk_is_reduced_of_reduced AlgebraicGeometry.stalk_isReduced_of_reduced

theorem isReducedOfOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  -- ⊢ autoParam (∀ (U : Opens ↑↑X.toPresheafedSpace), _root_.IsReduced ↑(X.preshea …
  intro U
  -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op U))
  have : U = (Opens.map f.1.base).obj (H.base_open.isOpenMap.functor.obj U) := by
    ext1; exact (Set.preimage_image_eq _ H.base_open.inj).symm
  rw [this]
  -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op ((Opens.map f.val.base).obj ((IsOpenMa …
  exact isReduced_of_injective (inv <| f.1.c.app (op <| H.base_open.isOpenMap.functor.obj U))
    (asIso <| f.1.c.app (op <| H.base_open.isOpenMap.functor.obj U) :
      Y.presheaf.obj _ ≅ _).symm.commRingCatIsoToRingEquiv.injective
#align algebraic_geometry.is_reduced_of_open_immersion AlgebraicGeometry.isReducedOfOpenImmersion

set_option maxHeartbeats 300000 in
instance {R : CommRingCat} [H : _root_.IsReduced R] : IsReduced (Scheme.Spec.obj <| op R) := by
  apply (config := { allowSynthFailures := true }) isReducedOfStalkIsReduced
  -- ⊢ ∀ (x : ↑↑(Scheme.Spec.obj (op R)).toPresheafedSpace), _root_.IsReduced ↑(Pre …
  intro x; dsimp
  -- ⊢ _root_.IsReduced ↑(Presheaf.stalk (Scheme.Spec.obj (op R)).presheaf x)
           -- ⊢ _root_.IsReduced ↑(Presheaf.stalk (Scheme.Spec.obj (op R)).presheaf x)
  have : _root_.IsReduced (CommRingCat.of <| Localization.AtPrime (PrimeSpectrum.asIdeal x)) := by
    dsimp; infer_instance
  exact isReduced_of_injective (StructureSheaf.stalkIso R x).hom
    (StructureSheaf.stalkIso R x).commRingCatIsoToRingEquiv.injective

theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (Scheme.Spec.obj <| op R) ↔ _root_.IsReduced R := by
  refine' ⟨_, fun h => inferInstance⟩
  -- ⊢ IsReduced (Scheme.Spec.obj (op R)) → _root_.IsReduced ↑R
  intro h
  -- ⊢ _root_.IsReduced ↑R
  have : _root_.IsReduced
      (LocallyRingedSpace.Γ.obj (op <| Spec.toLocallyRingedSpace.obj <| op R)) := by
    change _root_.IsReduced ((Scheme.Spec.obj <| op R).presheaf.obj <| op ⊤); infer_instance
  exact isReduced_of_injective (toSpecΓ R) (asIso <| toSpecΓ R).commRingCatIsoToRingEquiv.injective
  -- 🎉 no goals
#align algebraic_geometry.affine_is_reduced_iff AlgebraicGeometry.affine_isReduced_iff

theorem isReducedOfIsAffineIsReduced [IsAffine X] [h : _root_.IsReduced (X.presheaf.obj (op ⊤))] :
    IsReduced X :=
  haveI : IsReduced (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))) := by
    rw [affine_isReduced_iff]; exact h
    -- ⊢ _root_.IsReduced ↑(Scheme.Γ.obj (op X))
                               -- 🎉 no goals
  isReducedOfOpenImmersion X.isoSpec.hom
#align algebraic_geometry.is_reduced_of_is_affine_is_reduced AlgebraicGeometry.isReducedOfIsAffineIsReduced

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immerison `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
theorem reduce_to_affine_global (P : ∀ (X : Scheme) (_ : Opens X.carrier), Prop)
    (h₁ : ∀ (X : Scheme) (U : Opens X.carrier),
      (∀ x : U, ∃ (V : _) (_ : x.1 ∈ V) (_ : V ⟶ U), P X V) → P X U)
    (h₂ : ∀ {X Y} (f : X ⟶ Y) [hf : IsOpenImmersion f],
      ∃ (U : Set X.carrier) (V : Set Y.carrier) (hU : U = ⊤) (hV : V = Set.range f.1.base),
        P X ⟨U, hU.symm ▸ isOpen_univ⟩ → P Y ⟨V, hV.symm ▸ hf.base_open.open_range⟩)
    (h₃ : ∀ R : CommRingCat, P (Scheme.Spec.obj <| op R) ⊤) :
    ∀ (X : Scheme) (U : Opens X.carrier), P X U := by
  intro X U
  -- ⊢ P X U
  apply h₁
  -- ⊢ ∀ (x : { x // x ∈ U }), ∃ V x x, P X V
  intro x
  -- ⊢ ∃ V x x, P X V
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.IsOpen j).base_open.open_range⟩
  -- ⊢ ∃ V x x, P X V
  let i' : U' ⟶ U := homOfLE i
  -- ⊢ ∃ V x x, P X V
  refine' ⟨U', hx, i', _⟩
  -- ⊢ P X U'
  obtain ⟨_, _, rfl, rfl, h₂'⟩ := h₂ (X.affineBasisCover.map j)
  -- ⊢ P X U'
  apply h₂'
  -- ⊢ P (Scheme.OpenCover.obj (Scheme.affineBasisCover X) j) { carrier := ⊤, is_op …
  apply h₃
  -- 🎉 no goals
#align algebraic_geometry.reduce_to_affine_global AlgebraicGeometry.reduce_to_affine_global

theorem reduce_to_affine_nbhd (P : ∀ (X : Scheme) (_ : X.carrier), Prop)
    (h₁ : ∀ (R : CommRingCat) (x : PrimeSpectrum R), P (Scheme.Spec.obj <| op R) x)
    (h₂ : ∀ {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X.carrier), P X x → P Y (f.1.base x)) :
    ∀ (X : Scheme) (x : X.carrier), P X x := by
  intro X x
  -- ⊢ P X x
  obtain ⟨y, e⟩ := X.affineCover.Covers x
  -- ⊢ P X x
  convert h₂ (X.affineCover.map (X.affineCover.f x)) y _
  -- ⊢ x = ↑(Scheme.OpenCover.map (Scheme.affineCover X) (Scheme.OpenCover.f (Schem …
  · rw [e]
    -- 🎉 no goals
  apply h₁
  -- 🎉 no goals
#align algebraic_geometry.reduce_to_affine_nbhd AlgebraicGeometry.reduce_to_affine_nbhd

theorem eq_zero_of_basicOpen_eq_bot {X : Scheme} [hX : IsReduced X] {U : Opens X.carrier}
    (s : X.presheaf.obj (op U)) (hs : X.basicOpen s = ⊥) : s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  -- ⊢ ∀ (x : { x // x ∈ U }), ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) …
  conv => intro x; rw [RingHom.map_zero]
  -- ⊢ ∀ (x : { x // x ∈ U }), ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) …
  refine' (@reduce_to_affine_global (fun X U =>
     ∀ [IsReduced X] (s : X.presheaf.obj (op U)),
       X.basicOpen s = ⊥ → ∀ x, (X.sheaf.presheaf.germ x) s = 0) _ _ _) X U s hs
  · intro X U hx hX s hs x
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    obtain ⟨V, hx, i, H⟩ := hx x
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    specialize H (X.presheaf.map i.op s)
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    erw [Scheme.basicOpen_res] at H
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    rw [hs] at H
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    specialize H inf_bot_eq ⟨x, hx⟩
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    erw [TopCat.Presheaf.germ_res_apply] at H
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf X)) x) s = 0
    exact H
    -- 🎉 no goals
  · rintro X Y f hf
    -- ⊢ ∃ U V hU hV, (fun X U => ∀ [inst : IsReduced X] (s : ↑(X.presheaf.obj (op U) …
    have e : f.val.base ⁻¹' Set.range ↑f.val.base = Set.univ := by
      rw [← Set.image_univ, Set.preimage_image_eq _ hf.base_open.inj]
    refine' ⟨_, _, e, rfl, _⟩
    -- ⊢ (fun X U => ∀ [inst : IsReduced X] (s : ↑(X.presheaf.obj (op U))), Scheme.ba …
    rintro H hX s hs ⟨_, x, rfl⟩
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf Y)) { val := ↑f.val.base x, pr …
    haveI := isReducedOfOpenImmersion f
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf Y)) { val := ↑f.val.base x, pr …
    specialize H (f.1.c.app _ s) _ ⟨x, by rw [Opens.mem_mk, e]; trivial⟩
    -- ⊢ Scheme.basicOpen X (↑(NatTrans.app f.val.c (op { carrier := Set.range ↑f.val …
    · rw [← Scheme.preimage_basicOpen, hs]; ext1; simp [Opens.map]
      -- ⊢ (Opens.map f.val.base).obj ⊥ = ⊥
                                            -- ⊢ ↑((Opens.map f.val.base).obj ⊥) = ↑⊥
                                                  -- 🎉 no goals
    · erw [← PresheafedSpace.stalkMap_germ_apply f.1 ⟨_, _⟩ ⟨x, _⟩] at H
      -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf Y)) { val := ↑f.val.base x, pr …
      apply_fun inv <| PresheafedSpace.stalkMap f.val x at H
      -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf Y)) { val := ↑f.val.base x, pr …
      erw [CategoryTheory.IsIso.hom_inv_id_apply, map_zero] at H
      -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf Y)) { val := ↑f.val.base x, pr …
      exact H
      -- 🎉 no goals
  · intro R hX s hs x
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf (Scheme.Spec.obj (op R)))) x)  …
    erw [basicOpen_eq_of_affine', PrimeSpectrum.basicOpen_eq_bot_iff] at hs
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf (Scheme.Spec.obj (op R)))) x)  …
    replace hs := hs.map (SpecΓIdentity.app R).inv
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf (Scheme.Spec.obj (op R)))) x)  …
    -- what the hell?!
    replace hs := @IsNilpotent.eq_zero _ _ _ _ (show _ from ?_) hs
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf (Scheme.Spec.obj (op R)))) x)  …
    rw [Iso.hom_inv_id_apply] at hs
    -- ⊢ ↑(Presheaf.germ (Sheaf.presheaf (Scheme.sheaf (Scheme.Spec.obj (op R)))) x)  …
    rw [hs, map_zero]
    -- ⊢ _root_.IsReduced ((fun x => ↑((Spec.toLocallyRingedSpace.rightOp ⋙ LocallyRi …
    exact @IsReduced.component_reduced _ hX ⊤
    -- 🎉 no goals
#align algebraic_geometry.eq_zero_of_basic_open_eq_bot AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot

@[simp]
theorem basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : Opens X.carrier}
    (s : X.presheaf.obj <| op U) : X.basicOpen s = ⊥ ↔ s = 0 := by
  refine' ⟨eq_zero_of_basicOpen_eq_bot s, _⟩
  -- ⊢ s = 0 → Scheme.basicOpen X s = ⊥
  rintro rfl
  -- ⊢ Scheme.basicOpen X 0 = ⊥
  simp
  -- 🎉 no goals
#align algebraic_geometry.basic_open_eq_bot_iff AlgebraicGeometry.basicOpen_eq_bot_iff

/-- A scheme `X` is integral if its carrier is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class IsIntegral : Prop where
  nonempty : Nonempty X.carrier := by infer_instance
  component_integral : ∀ (U : Opens X.carrier) [Nonempty U], IsDomain (X.presheaf.obj (op U)) := by
    infer_instance
#align algebraic_geometry.is_integral AlgebraicGeometry.IsIntegral

attribute [instance] IsIntegral.component_integral IsIntegral.nonempty

instance [h : IsIntegral X] : IsDomain (X.presheaf.obj (op ⊤)) :=
  @IsIntegral.component_integral _ _ _ (by
    simp only [Set.univ_nonempty, Opens.nonempty_coeSort, Opens.coe_top])
    -- 🎉 no goals

instance (priority := 900) isReducedOfIsIntegral [IsIntegral X] : IsReduced X := by
  constructor
  -- ⊢ autoParam (∀ (U : Opens ↑↑X.toPresheafedSpace), _root_.IsReduced ↑(X.preshea …
  intro U
  -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op U))
  cases' U.1.eq_empty_or_nonempty with h h
  -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op U))
  · have : U = ⊥ := SetLike.ext' h
    -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op U))
    haveI := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty this)
    -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op U))
    change _root_.IsReduced (X.sheaf.val.obj (op U))
    -- ⊢ _root_.IsReduced ↑((Scheme.sheaf X).val.obj (op U))
    infer_instance
    -- 🎉 no goals
  · haveI : Nonempty U := by simpa
    -- ⊢ _root_.IsReduced ↑(X.presheaf.obj (op U))
    infer_instance
    -- 🎉 no goals
#align algebraic_geometry.is_reduced_of_is_integral AlgebraicGeometry.isReducedOfIsIntegral

instance is_irreducible_of_isIntegral [IsIntegral X] : IrreducibleSpace X.carrier := by
  by_contra H
  -- ⊢ False
  replace H : ¬IsPreirreducible (⊤ : Set X.carrier) := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_closed_union_closed, not_forall, not_or] at H
  -- ⊢ False
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  -- ⊢ False
  erw [not_forall] at h₂ h₃
  -- ⊢ False
  simp_rw [not_forall] at h₂ h₃
  -- ⊢ False
  haveI : Nonempty (⟨Sᶜ, hS.1⟩ : Opens X.carrier) := ⟨⟨_, h₂.choose_spec.choose_spec⟩⟩
  -- ⊢ False
  haveI : Nonempty (⟨Tᶜ, hT.1⟩ : Opens X.carrier) := ⟨⟨_, h₃.choose_spec.choose_spec⟩⟩
  -- ⊢ False
  haveI : Nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : Opens X.carrier) :=
    ⟨⟨_, Or.inl h₂.choose_spec.choose_spec⟩⟩
  let e : X.presheaf.obj _ ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ ?_).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  apply (config := { allowSynthFailures := true }) false_of_nontrivial_of_product_domain
  · exact e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    -- 🎉 no goals
  · apply X.toLocallyRingedSpace.component_nontrivial
    -- 🎉 no goals
  · apply X.toLocallyRingedSpace.component_nontrivial
    -- 🎉 no goals
  · ext x
    -- ⊢ x ∈ ↑({ carrier := Sᶜ, is_open' := (_ : IsOpen Sᶜ) } ⊓ { carrier := Tᶜ, is_o …
    constructor
    -- ⊢ x ∈ ↑({ carrier := Sᶜ, is_open' := (_ : IsOpen Sᶜ) } ⊓ { carrier := Tᶜ, is_o …
    · rintro ⟨hS, hT⟩
      -- ⊢ x ∈ ↑⊥
      cases' h₁ (show x ∈ ⊤ by trivial) with h h
      -- ⊢ x ∈ ↑⊥
      exacts [hS h, hT h]
      -- 🎉 no goals
    · intro x
      -- ⊢ x✝ ∈ ↑({ carrier := Sᶜ, is_open' := (_ : IsOpen Sᶜ) } ⊓ { carrier := Tᶜ, is_ …
      refine' x.rec (by contradiction)
      -- 🎉 no goals
#align algebraic_geometry.is_irreducible_of_is_integral AlgebraicGeometry.is_irreducible_of_isIntegral

theorem isIntegralOfIsIrreducibleIsReduced [IsReduced X] [H : IrreducibleSpace X.carrier] :
    IsIntegral X := by
  constructor; · infer_instance
  -- ⊢ autoParam (Nonempty ↑↑X.toPresheafedSpace) _auto✝
                 -- 🎉 no goals
  intro U hU
  -- ⊢ IsDomain ↑(X.presheaf.obj (op U))
  haveI := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  -- ⊢ IsDomain ↑(X.presheaf.obj (op U))
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine' ⟨fun {a b} e => _⟩
    simp_rw [← basicOpen_eq_bot_iff, ← Opens.not_nonempty_iff_eq_bot]
    by_contra' h
    obtain ⟨_, ⟨x, hx₁, rfl⟩, ⟨x, hx₂, e'⟩⟩ :=
      nonempty_preirreducible_inter (X.basicOpen a).2 (X.basicOpen b).2 h.1 h.2
    replace e' := Subtype.eq e'
    subst e'
    replace e := congr_arg (X.presheaf.germ x) e
    rw [RingHom.map_mul, RingHom.map_zero] at e
    refine' zero_ne_one' (X.presheaf.stalk x.1) (isUnit_zero_iff.1 _)
    convert hx₁.mul hx₂
    exact e.symm
  exact NoZeroDivisors.to_isDomain _
  -- 🎉 no goals
#align algebraic_geometry.is_integral_of_is_irreducible_is_reduced AlgebraicGeometry.isIntegralOfIsIrreducibleIsReduced

theorem isIntegral_iff_is_irreducible_and_isReduced :
    IsIntegral X ↔ IrreducibleSpace X.carrier ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegralOfIsIrreducibleIsReduced X⟩
#align algebraic_geometry.is_integral_iff_is_irreducible_and_is_reduced AlgebraicGeometry.isIntegral_iff_is_irreducible_and_isReduced

theorem isIntegralOfOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsIntegral Y] [Nonempty X.carrier] : IsIntegral X := by
  constructor; · infer_instance
  -- ⊢ autoParam (Nonempty ↑↑X.toPresheafedSpace) _auto✝
                 -- 🎉 no goals
  intro U hU
  -- ⊢ IsDomain ↑(X.presheaf.obj (op U))
  have : U = (Opens.map f.1.base).obj (H.base_open.isOpenMap.functor.obj U) := by
    ext1; exact (Set.preimage_image_eq _ H.base_open.inj).symm
  rw [this]
  -- ⊢ IsDomain ↑(X.presheaf.obj (op ((Opens.map f.val.base).obj ((IsOpenMap.functo …
  have : IsDomain (Y.presheaf.obj (op (H.base_open.isOpenMap.functor.obj U))) := by
    apply (config := { allowSynthFailures := true }) IsIntegral.component_integral
    refine' ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.1.c.app (op <| H.base_open.isOpenMap.functor.obj U) :
    Y.presheaf.obj _ ≅ _).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
#align algebraic_geometry.is_integral_of_open_immersion AlgebraicGeometry.isIntegralOfOpenImmersion

instance {R : CommRingCat} [H : IsDomain R] :
    IrreducibleSpace (Scheme.Spec.obj <| op R).carrier := by
  convert PrimeSpectrum.irreducibleSpace (R := R)
  -- 🎉 no goals

instance {R : CommRingCat} [IsDomain R] : IsIntegral (Scheme.Spec.obj <| op R) :=
  isIntegralOfIsIrreducibleIsReduced _

theorem affine_isIntegral_iff (R : CommRingCat) :
    IsIntegral (Scheme.Spec.obj <| op R) ↔ IsDomain R :=
  ⟨fun _ => MulEquiv.isDomain ((Scheme.Spec.obj <| op R).presheaf.obj (op ⊤))
    (asIso <| toSpecΓ R).commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩
#align algebraic_geometry.affine_is_integral_iff AlgebraicGeometry.affine_isIntegral_iff

theorem isIntegralOfIsAffineIsDomain [IsAffine X] [Nonempty X.carrier]
    [h : IsDomain (X.presheaf.obj (op ⊤))] : IsIntegral X :=
  haveI : IsIntegral (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))) := by
    rw [affine_isIntegral_iff]; exact h
    -- ⊢ IsDomain ↑(Scheme.Γ.obj (op X))
                                -- 🎉 no goals
  isIntegralOfOpenImmersion X.isoSpec.hom
#align algebraic_geometry.is_integral_of_is_affine_is_domain AlgebraicGeometry.isIntegralOfIsAffineIsDomain

theorem map_injective_of_isIntegral [IsIntegral X] {U V : Opens X.carrier} (i : U ⟶ V)
    [H : Nonempty U] : Function.Injective (X.presheaf.map i.op) := by
  rw [injective_iff_map_eq_zero]
  -- ⊢ ∀ (a : (forget CommRingCat).obj (X.presheaf.obj (op V))), ↑(X.presheaf.map i …
  intro x hx
  -- ⊢ x = 0
  rw [← basicOpen_eq_bot_iff] at hx ⊢
  -- ⊢ Scheme.basicOpen X x = ⊥
  rw [Scheme.basicOpen_res] at hx
  -- ⊢ Scheme.basicOpen X x = ⊥
  revert hx
  -- ⊢ U ⊓ Scheme.basicOpen X x = ⊥ → Scheme.basicOpen X x = ⊥
  contrapose!
  -- ⊢ Scheme.basicOpen X x ≠ ⊥ → U ⊓ Scheme.basicOpen X x ≠ ⊥
  simp_rw [Ne.def, ← Opens.not_nonempty_iff_eq_bot, Classical.not_not]
  -- ⊢ Set.Nonempty ↑(Scheme.basicOpen X x) → Set.Nonempty ↑(U ⊓ Scheme.basicOpen X …
  apply nonempty_preirreducible_inter U.isOpen (RingedSpace.basicOpen _ _).isOpen
  -- ⊢ Set.Nonempty ↑U
  simpa using H
  -- 🎉 no goals
#align algebraic_geometry.map_injective_of_is_integral AlgebraicGeometry.map_injective_of_isIntegral

end AlgebraicGeometry
