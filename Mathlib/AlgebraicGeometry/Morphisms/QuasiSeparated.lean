/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.QuasiSeparated

#align_import algebraic_geometry.morphisms.quasi_separated from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`AlgebraicGeometry.quasiSeparatedSpace_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

## Main result
- `AlgebraicGeometry.is_localization_basicOpen_of_qcqs` (**Qcqs lemma**):
  If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `QuasiSeparated` if diagonal map is quasi-compact. -/
@[mk_iff]
class QuasiSeparated (f : X ⟶ Y) : Prop where
  /-- A morphism is `QuasiSeparated` if diagonal map is quasi-compact. -/
  diagonalQuasiCompact : QuasiCompact (pullback.diagonal f) := by infer_instance
#align algebraic_geometry.quasi_separated AlgebraicGeometry.QuasiSeparated

theorem quasiSeparatedSpace_iff_affine (X : Scheme) :
    QuasiSeparatedSpace X ↔ ∀ U V : X.affineOpens, IsCompact (U ∩ V : Set X) := by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.isCompact V.1.2 V.2.isCompact
  · intro H
    suffices
      ∀ (U : Opens X) (_ : IsCompact U.1) (V : Opens X) (_ : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV'
    intro U hU V hV
    -- Porting note: it complains "unable to find motive", but telling Lean that motive is
    -- underscore is actually sufficient, weird
    apply compact_open_induction_on (P := _) V hV
    · simp
    · intro S _ V hV
      change IsCompact (U.1 ∩ (S.1 ∪ V.1))
      rw [Set.inter_union_distrib_left]
      apply hV.union
      clear hV
      apply compact_open_induction_on (P := _) U hU
      · simp
      · intro S _ W hW
        change IsCompact ((S.1 ∪ W.1) ∩ V.1)
        rw [Set.union_inter_distrib_right]
        apply hW.union
        apply H
#align algebraic_geometry.quasi_separated_space_iff_affine AlgebraicGeometry.quasiSeparatedSpace_iff_affine

theorem quasiCompact_affineProperty_iff_quasiSeparatedSpace {X Y : Scheme} [IsAffine Y]
    (f : X ⟶ Y) :
    AffineTargetMorphismProperty.diagonal (fun X _ _ _ ↦ CompactSpace X) f ↔
      QuasiSeparatedSpace X := by
  delta AffineTargetMorphismProperty.diagonal
  rw [quasiSeparatedSpace_iff_affine]
  constructor
  · intro H U V
    haveI : IsAffine _ := U.2
    haveI : IsAffine _ := V.2
    let g : pullback (X.ofRestrict U.1.openEmbedding) (X.ofRestrict V.1.openEmbedding) ⟶ X :=
      pullback.fst _ _ ≫ X.ofRestrict _
    -- Porting note: `inferInstance` does not work here
    have : IsOpenImmersion g := PresheafedSpace.IsOpenImmersion.comp _ _
    have e := Homeomorph.ofEmbedding _ this.base_open.toEmbedding
    rw [IsOpenImmersion.range_pullback_to_base_of_left] at e
    erw [Subtype.range_coe, Subtype.range_coe] at e
    rw [isCompact_iff_compactSpace]
    exact @Homeomorph.compactSpace _ _ _ _ (H _ _) e
  · introv H h₁ h₂
    let g : pullback f₁ f₂ ⟶ X := pullback.fst _ _ ≫ f₁
    -- Porting note: `inferInstance` does not work here
    have : IsOpenImmersion g := PresheafedSpace.IsOpenImmersion.comp _ _
    have e := Homeomorph.ofEmbedding _ this.base_open.toEmbedding
    rw [IsOpenImmersion.range_pullback_to_base_of_left] at e
    simp_rw [isCompact_iff_compactSpace] at H
    exact
      @Homeomorph.compactSpace _ _ _ _
        (H ⟨⟨_, h₁.base_open.isOpen_range⟩, isAffineOpen_opensRange _⟩
          ⟨⟨_, h₂.base_open.isOpen_range⟩, isAffineOpen_opensRange _⟩)
        e.symm
#align algebraic_geometry.quasi_compact_affine_property_iff_quasi_separated_space AlgebraicGeometry.quasiCompact_affineProperty_iff_quasiSeparatedSpace

theorem quasiSeparated_eq_diagonal_is_quasiCompact :
    @QuasiSeparated = MorphismProperty.diagonal @QuasiCompact := by ext; exact quasiSeparated_iff _
#align algebraic_geometry.quasi_separated_eq_diagonal_is_quasi_compact AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact

@[reducible]
instance : HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X) where
  __ := HasAffineProperty.copy
    quasiSeparated_eq_diagonal_is_quasiCompact.symm
    (by ext; exact quasiCompact_affineProperty_iff_quasiSeparatedSpace _)

instance (priority := 900) quasiSeparatedOfMono {X Y : Scheme} (f : X ⟶ Y) [Mono f] :
    QuasiSeparated f where
#align algebraic_geometry.quasi_separated_of_mono AlgebraicGeometry.quasiSeparatedOfMono

instance quasiSeparated_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸
    (MorphismProperty.diagonal_isStableUnderComposition quasiCompact_stableUnderBaseChange)
#align algebraic_geometry.quasi_separated_stable_under_composition AlgebraicGeometry.quasiSeparated_isStableUnderComposition

theorem quasiSeparated_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ quasiCompact_stableUnderBaseChange.diagonal
#align algebraic_geometry.quasi_separated_stable_under_base_change AlgebraicGeometry.quasiSeparated_stableUnderBaseChange

instance quasiSeparatedComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
    [QuasiSeparated g] : QuasiSeparated (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance
#align algebraic_geometry.quasi_separated_comp AlgebraicGeometry.quasiSeparatedComp

theorem quasiSeparated_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)]
#align algebraic_geometry.quasi_separated_over_affine_iff AlgebraicGeometry.quasiSeparated_over_affine_iff

theorem quasiSeparatedSpace_iff_quasiSeparated (X : Scheme) :
    QuasiSeparatedSpace X ↔ QuasiSeparated (terminal.from X) :=
  (quasiSeparated_over_affine_iff _).symm
#align algebraic_geometry.quasi_separated_space_iff_quasi_separated AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated g] :
    QuasiSeparated (pullback.fst f g) :=
  quasiSeparated_stableUnderBaseChange.fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated f] :
    QuasiSeparated (pullback.snd f g) :=
  quasiSeparated_stableUnderBaseChange.snd f g inferInstance

theorem quasiSeparatedSpace_of_quasiSeparated {X Y : Scheme} (f : X ⟶ Y)
    [hY : QuasiSeparatedSpace Y] [QuasiSeparated f] : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance
#align algebraic_geometry.quasi_separated_space_of_quasi_separated AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated

instance quasiSeparatedSpace_of_isAffine (X : Scheme) [IsAffine X] :
    QuasiSeparatedSpace X := by
  constructor
  intro U V hU hU' hV hV'
  obtain ⟨s, hs, e⟩ := (isCompactOpen_iff_eq_basicOpen_union _).mp ⟨hU', hU⟩
  obtain ⟨s', hs', e'⟩ := (isCompactOpen_iff_eq_basicOpen_union _).mp ⟨hV', hV⟩
  rw [e, e', Set.iUnion₂_inter]
  simp_rw [Set.inter_iUnion₂]
  apply hs.isCompact_biUnion
  intro i _
  apply hs'.isCompact_biUnion
  intro i' _
  change IsCompact (X.basicOpen i ⊓ X.basicOpen i').1
  rw [← Scheme.basicOpen_mul]
  exact ((isAffineOpen_top _).basicOpen _).isCompact
#align algebraic_geometry.quasi_separated_space_of_is_affine AlgebraicGeometry.quasiSeparatedSpace_of_isAffine

theorem IsAffineOpen.isQuasiSeparated {X : Scheme} {U : Opens X} (hU : IsAffineOpen U) :
    IsQuasiSeparated (U : Set X) := by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.isOpen]
#align algebraic_geometry.is_affine_open.is_quasi_separated AlgebraicGeometry.IsAffineOpen.isQuasiSeparated

theorem QuasiSeparated.of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated (f ≫ g)] :
    QuasiSeparated f := by
  let 𝒰 := (Z.affineCover.pullbackCover g).bind fun x => Scheme.affineCover _
  have (i) : IsAffine (𝒰.obj i) := by dsimp [𝒰]; infer_instance
  apply HasAffineProperty.of_openCover
    ((Z.affineCover.pullbackCover g).bind fun x => Scheme.affineCover _)
  rintro ⟨i, j⟩; dsimp at i j
  refine @quasiSeparatedSpace_of_quasiSeparated _ _ ?_
    (HasAffineProperty.of_isPullback (.of_hasPullback _ (Z.affineCover.map i)) ‹_›) ?_
  · exact pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (Category.comp_id _) ≫
      (pullbackRightPullbackFstIso g (Z.affineCover.map i) f).hom
  · exact inferInstance
#align algebraic_geometry.quasi_separated_of_comp AlgebraicGeometry.QuasiSeparated.of_comp

theorem exists_eq_pow_mul_of_isAffineOpen (X : Scheme) (U : Opens X) (hU : IsAffineOpen U)
    (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x := by
  have := (hU.isLocalization_basicOpen f).2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict
  simpa [mul_comm x] using d.symm
#align algebraic_geometry.exists_eq_pow_mul_of_is_affine_open AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen

theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux {X : TopCat}
    (F : X.Presheaf CommRingCat) {U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Opens X} {n₁ n₂ : ℕ}
    {y₁ : F.obj (op U₁)} {y₂ : F.obj (op U₂)} {f : F.obj (op <| U₁ ⊔ U₂)}
    {x : F.obj (op U₃)} (h₄₁ : U₄ ≤ U₁) (h₄₂ : U₄ ≤ U₂) (h₅₁ : U₅ ≤ U₁) (h₅₃ : U₅ ≤ U₃)
    (h₆₂ : U₆ ≤ U₂) (h₆₃ : U₆ ≤ U₃) (h₇₄ : U₇ ≤ U₄) (h₇₅ : U₇ ≤ U₅) (h₇₆ : U₇ ≤ U₆)
    (e₁ : y₁ |_ U₅ = (f |_ U₁ |_ U₅) ^ n₁ * x |_ U₅)
    (e₂ : y₂ |_ U₆ = (f |_ U₂ |_ U₆) ^ n₂ * x |_ U₆) :
    (((f |_ U₁) ^ n₂ * y₁) |_ U₄) |_ U₇ = (((f |_ U₂) ^ n₁ * y₂) |_ U₄) |_ U₇ := by
  apply_fun (fun x : F.obj (op U₅) ↦ x |_ U₇) at e₁
  apply_fun (fun x : F.obj (op U₆) ↦ x |_ U₇) at e₂
  dsimp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at e₁ e₂ ⊢
  simp only [map_mul, map_pow, ← comp_apply, ← op_comp, ← F.map_comp, homOfLE_comp] at e₁ e₂ ⊢
  rw [e₁, e₂, mul_left_comm]

theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme)
    (S : X.affineOpens) (U₁ U₂ : Opens X) {n₁ n₂ : ℕ} {y₁ : Γ(X, U₁)}
    {y₂ : Γ(X, U₂)} {f : Γ(X, U₁ ⊔ U₂)}
    {x : Γ(X, X.basicOpen f)} (h₁ : S.1 ≤ U₁) (h₂ : S.1 ≤ U₂)
    (e₁ : y₁ |_ X.basicOpen (f |_ U₁) = ((f |_ U₁ |_ X.basicOpen _) ^ n₁) * x |_ X.basicOpen _)
    (e₂ : y₂ |_ X.basicOpen (f |_ U₂) = ((f |_ U₂ |_ X.basicOpen _) ^ n₂) * x |_ X.basicOpen _) :
    ∃ n : ℕ, ∀ m, n ≤ m →
      ((f |_ U₁) ^ (m + n₂) * y₁) |_ S.1 = ((f |_ U₂) ^ (m + n₁) * y₂) |_ S.1 := by
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _
      (S.2.isLocalization_basicOpen (f |_ S.1))
        (((f |_ U₁) ^ n₂ * y₁) |_ S.1)
        (((f |_ U₂) ^ n₁ * y₂) |_ S.1)).mp <| by
    apply exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux (e₁ := e₁) (e₂ := e₂)
    · show X.basicOpen _ ≤ _
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      repeat rw [Scheme.basicOpen_res] -- Note: used to be part of the `simp only`
      exact inf_le_inf h₁ le_rfl
    · show X.basicOpen _ ≤ _
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      repeat rw [Scheme.basicOpen_res] -- Note: used to be part of the `simp only`
      exact inf_le_inf h₂ le_rfl
  use n
  intros m hm
  rw [← tsub_add_cancel_of_le hm]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict,
    pow_add, map_pow, map_mul, ← comp_apply, mul_assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp,
    Subtype.coe_mk] at e ⊢
  rw [e]
#align algebraic_geometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux AlgebraicGeometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux

theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : Opens X)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x := by
  delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict
  revert hU' f x
  -- Porting note: complains `expected type is not available`, but tell Lean that it is underscore
  -- is sufficient
  apply compact_open_induction_on (P := _) U hU
  · intro _ f x
    use 0, f
    refine @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)) _ _
    erw [eq_bot_iff]
    exact X.basicOpen_le f
  · -- Given `f : 𝒪(S ∪ U), x : 𝒪(X_f)`, we need to show that `f ^ n * x` is the restriction of
    -- some `y : 𝒪(S ∪ U)` for some `n : ℕ`.
    intro S hS U hU hSU f x
    -- We know that such `y₁, n₁` exists on `S` by the induction hypothesis.
    obtain ⟨n₁, y₁, hy₁⟩ :=
      hU (hSU.of_subset Set.subset_union_left) (X.presheaf.map (homOfLE le_sup_left).op f)
        (X.presheaf.map (homOfLE _).op x)
    -- · rw [X.basicOpen_res]; exact inf_le_right
    -- We know that such `y₂, n₂` exists on `U` since `U` is affine.
    obtain ⟨n₂, y₂, hy₂⟩ :=
      exists_eq_pow_mul_of_isAffineOpen X _ U.2 (X.presheaf.map (homOfLE le_sup_right).op f)
        (X.presheaf.map (homOfLE _).op x)
    delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict at hy₂
    -- swap; · rw [X.basicOpen_res]; exact inf_le_right
    -- Since `S ∪ U` is quasi-separated, `S ∩ U` can be covered by finite affine opens.
    obtain ⟨s, hs', hs⟩ :=
      (isCompactOpen_iff_eq_finset_affine_union _).mp
        ⟨hSU _ _ Set.subset_union_left S.2 hS Set.subset_union_right U.1.2
            U.2.isCompact,
          (S ⊓ U.1).2⟩
    haveI := hs'.to_subtype
    cases nonempty_fintype s
    replace hs : S ⊓ U.1 = iSup fun i : s => (i : Opens X) := by ext1; simpa using hs
    have hs₁ : ∀ i : s, i.1.1 ≤ S := by
      intro i; change (i : Opens X) ≤ S
      refine le_trans ?_ (inf_le_left (b := U.1))
      erw [hs]
      -- Porting note: have to add argument explicitly
      exact @le_iSup (Opens X) s _ (fun (i : s) => (i : Opens X)) i
    have hs₂ : ∀ i : s, i.1.1 ≤ U.1 := by
      intro i; change (i : Opens X) ≤ U
      refine le_trans ?_ (inf_le_right (a := S))
      erw [hs]
      -- Porting note: have to add argument explicitly
      exact @le_iSup (Opens X) s _ (fun (i : s) => (i : Opens X)) i
    -- On each affine open in the intersection, we have `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- for some `n` since `f ^ n₂ * y₁ = f ^ (n₁ + n₂) * x = f ^ n₁ * y₂` on `X_f`.
    have := fun i ↦ exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux
      X i.1 S U (hs₁ i) (hs₂ i) hy₁ hy₂
    choose n hn using this
    -- We can thus choose a big enough `n` such that `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- on `S ∩ U`.
    have :
      X.presheaf.map (homOfLE <| inf_le_left).op
          (X.presheaf.map (homOfLE le_sup_left).op f ^ (Finset.univ.sup n + n₂) * y₁) =
        X.presheaf.map (homOfLE <| inf_le_right).op
          (X.presheaf.map (homOfLE le_sup_right).op f ^ (Finset.univ.sup n + n₁) * y₂) := by
      fapply X.sheaf.eq_of_locally_eq' fun i : s => i.1.1
      · refine fun i => homOfLE ?_; erw [hs]
        -- Porting note: have to add argument explicitly
        exact @le_iSup (Opens X) s _ (fun (i : s) => (i : Opens X)) i
      · exact le_of_eq hs
      · intro i
        delta Scheme.sheaf SheafedSpace.sheaf
        repeat rw [← comp_apply,]
        simp only [← Functor.map_comp, ← op_comp]
        apply hn
        exact Finset.le_sup (Finset.mem_univ _)
    use Finset.univ.sup n + n₁ + n₂
    -- By the sheaf condition, since `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`, it can be glued into
    -- the desired section on `S ∪ U`.
    use (X.sheaf.objSupIsoProdEqLocus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩
    refine (X.sheaf.objSupIsoProdEqLocus_inv_eq_iff _ _ _ (X.basicOpen_res _
      (homOfLE le_sup_left).op) (X.basicOpen_res _ (homOfLE le_sup_right).op)).mpr ⟨?_, ?_⟩
    · delta Scheme.sheaf SheafedSpace.sheaf
      rw [add_assoc, add_comm n₁]
      simp only [pow_add, map_pow, map_mul]
      rw [hy₁] -- Note: `simp` can't use this
      repeat rw [← comp_apply] -- Note: `simp` can't use this
      simp only [← mul_assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    · delta Scheme.sheaf SheafedSpace.sheaf
      simp only [pow_add, map_pow, map_mul]
      rw [hy₂] -- Note: `simp` can't use this
      repeat rw [← comp_apply] -- Note: `simp` can't use this
      simp only [← mul_assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]
#align algebraic_geometry.exists_eq_pow_mul_of_is_compact_of_is_quasi_separated AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
theorem is_localization_basicOpen_of_qcqs {X : Scheme} {U : Opens X} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) :
    IsLocalization.Away f (Γ(X, X.basicOpen f)) := by
  constructor
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, Subtype.coe_mk, RingHom.algebraMap_toAlgebra]
    exact IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ f)
  · intro z
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU hU' f z
    refine ⟨⟨y, _, n, rfl⟩, ?_⟩
    simpa only [map_pow, Subtype.coe_mk, RingHom.algebraMap_toAlgebra, mul_comm z] using e.symm
  · intro x y
    rw [← sub_eq_zero, ← map_sub, RingHom.algebraMap_toAlgebra]
    simp_rw [← @sub_eq_zero _ _ (_ * x) (_ * y), ← mul_sub]
    generalize x - y = z
    intro H
    obtain ⟨n, e⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU _ _ H
    refine ⟨⟨_, n, rfl⟩, ?_⟩
    simpa [mul_comm z] using e
#align algebraic_geometry.is_localization_basic_open_of_qcqs AlgebraicGeometry.is_localization_basicOpen_of_qcqs

end AlgebraicGeometry
