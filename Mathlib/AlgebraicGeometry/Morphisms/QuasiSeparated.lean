/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.quasi_separated
! leanprover-community/mathlib commit 13361559d66b84f80b6d5a1c4a26aa5054766725
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathbin.Topology.QuasiSeparated

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`algebraic_geometry.quasi_separated_space_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

## Main result
- `is_localization_basic_open_of_qcqs` (**Qcqs lemma**):
  If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `quasi_separated` if diagonal map is quasi-compact. -/
@[mk_iff]
class QuasiSeparated (f : X ⟶ Y) : Prop where
  diagonalQuasiCompact : QuasiCompact (pullback.diagonal f)
#align algebraic_geometry.quasi_separated AlgebraicGeometry.QuasiSeparated

/-- The `affine_target_morphism_property` corresponding to `quasi_separated`, asserting that the
domain is a quasi-separated scheme. -/
def QuasiSeparated.affineProperty : AffineTargetMorphismProperty := fun X Y f _ =>
  QuasiSeparatedSpace X.carrier
#align algebraic_geometry.quasi_separated.affine_property AlgebraicGeometry.QuasiSeparated.affineProperty

theorem quasiSeparatedSpace_iff_affine (X : Scheme) :
    QuasiSeparatedSpace X.carrier ↔ ∀ U V : X.affineOpens, IsCompact (U ∩ V : Set X.carrier) :=
  by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.IsCompact V.1.2 V.2.IsCompact
  · intro H
    suffices
      ∀ (U : opens X.carrier) (hU : IsCompact U.1) (V : opens X.carrier) (hV : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV'
    intro U hU V hV
    apply compact_open_induction_on V hV
    · simp
    · intro S hS V hV
      change IsCompact (U.1 ∩ (S.1 ∪ V.1))
      rw [Set.inter_union_distrib_left]
      apply hV.union
      clear hV
      apply compact_open_induction_on U hU
      · simp
      · intro S hS W hW
        change IsCompact ((S.1 ∪ W.1) ∩ V.1)
        rw [Set.union_inter_distrib_right]
        apply hW.union
        apply H
#align algebraic_geometry.quasi_separated_space_iff_affine AlgebraicGeometry.quasiSeparatedSpace_iff_affine

theorem quasi_compact_affineProperty_iff_quasiSeparatedSpace {X Y : Scheme} [IsAffine Y]
    (f : X ⟶ Y) : QuasiCompact.affineProperty.diagonal f ↔ QuasiSeparatedSpace X.carrier :=
  by
  delta affine_target_morphism_property.diagonal
  rw [quasi_separated_space_iff_affine]
  constructor
  · intro H U V
    haveI : is_affine _ := U.2
    haveI : is_affine _ := V.2
    let g : pullback (X.of_restrict U.1.OpenEmbedding) (X.of_restrict V.1.OpenEmbedding) ⟶ X :=
      pullback.fst ≫ X.of_restrict _
    have : is_open_immersion g := inferInstance
    have e := Homeomorph.ofEmbedding _ this.base_open.to_embedding
    rw [is_open_immersion.range_pullback_to_base_of_left] at e 
    erw [Subtype.range_coe, Subtype.range_coe] at e 
    rw [isCompact_iff_compactSpace]
    exact @Homeomorph.compactSpace _ _ (H _ _) e
  · introv H h₁ h₂
    skip
    let g : pullback f₁ f₂ ⟶ X := pullback.fst ≫ f₁
    have : is_open_immersion g := inferInstance
    have e := Homeomorph.ofEmbedding _ this.base_open.to_embedding
    rw [is_open_immersion.range_pullback_to_base_of_left] at e 
    simp_rw [isCompact_iff_compactSpace] at H 
    exact
      @Homeomorph.compactSpace _ _
        (H ⟨⟨_, h₁.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩
          ⟨⟨_, h₂.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩)
        e.symm
#align algebraic_geometry.quasi_compact_affine_property_iff_quasi_separated_space AlgebraicGeometry.quasi_compact_affineProperty_iff_quasiSeparatedSpace

theorem quasiSeparated_eq_diagonal_is_quasiCompact :
    @QuasiSeparated = MorphismProperty.diagonal @QuasiCompact := by ext; exact quasi_separated_iff _
#align algebraic_geometry.quasi_separated_eq_diagonal_is_quasi_compact AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact

theorem quasi_compact_affineProperty_diagonal_eq :
    QuasiCompact.affineProperty.diagonal = QuasiSeparated.affineProperty := by ext;
  rw [quasi_compact_affine_property_iff_quasi_separated_space]; rfl
#align algebraic_geometry.quasi_compact_affine_property_diagonal_eq AlgebraicGeometry.quasi_compact_affineProperty_diagonal_eq

theorem quasiSeparated_eq_affineProperty_diagonal :
    @QuasiSeparated = targetAffineLocally QuasiCompact.affineProperty.diagonal :=
  by
  rw [quasi_separated_eq_diagonal_is_quasi_compact, quasi_compact_eq_affine_property]
  exact
    diagonal_target_affine_locally_eq_target_affine_locally _ quasi_compact.affine_property_is_local
#align algebraic_geometry.quasi_separated_eq_affine_property_diagonal AlgebraicGeometry.quasiSeparated_eq_affineProperty_diagonal

theorem quasiSeparated_eq_affineProperty :
    @QuasiSeparated = targetAffineLocally QuasiSeparated.affineProperty := by
  rw [quasi_separated_eq_affine_property_diagonal, quasi_compact_affine_property_diagonal_eq]
#align algebraic_geometry.quasi_separated_eq_affine_property AlgebraicGeometry.quasiSeparated_eq_affineProperty

theorem QuasiSeparated.affineProperty_isLocal : QuasiSeparated.affineProperty.IsLocal :=
  quasi_compact_affineProperty_diagonal_eq ▸ QuasiCompact.affineProperty_isLocal.diagonal
#align algebraic_geometry.quasi_separated.affine_property_is_local AlgebraicGeometry.QuasiSeparated.affineProperty_isLocal

instance (priority := 900) quasiSeparatedOfMono {X Y : Scheme} (f : X ⟶ Y) [Mono f] :
    QuasiSeparated f :=
  ⟨inferInstance⟩
#align algebraic_geometry.quasi_separated_of_mono AlgebraicGeometry.quasiSeparatedOfMono

theorem quasiSeparated_stableUnderComposition :
    MorphismProperty.StableUnderComposition @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸
    quasiCompact_stableUnderComposition.diagonal quasiCompact_respectsIso
      quasiCompact_stableUnderBaseChange
#align algebraic_geometry.quasi_separated_stable_under_composition AlgebraicGeometry.quasiSeparated_stableUnderComposition

theorem quasiSeparated_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸
    quasiCompact_stableUnderBaseChange.diagonal quasiCompact_respectsIso
#align algebraic_geometry.quasi_separated_stable_under_base_change AlgebraicGeometry.quasiSeparated_stableUnderBaseChange

instance quasiSeparatedComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
    [QuasiSeparated g] : QuasiSeparated (f ≫ g) :=
  quasiSeparated_stableUnderComposition f g inferInstance inferInstance
#align algebraic_geometry.quasi_separated_comp AlgebraicGeometry.quasiSeparatedComp

theorem quasiSeparated_respectsIso : MorphismProperty.RespectsIso @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ quasiCompact_respectsIso.diagonal
#align algebraic_geometry.quasi_separated_respects_iso AlgebraicGeometry.quasiSeparated_respectsIso

theorem QuasiSeparated.affine_openCover_tFAE {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [QuasiSeparated f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, QuasiSeparatedSpace (pullback f (𝒰.map i)).carrier,
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          QuasiSeparatedSpace (pullback f (𝒰.map i)).carrier,
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersionCat g],
          QuasiSeparatedSpace (pullback f g).carrier,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)) (𝒰' :
          ∀ i : 𝒰.J, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) (_ :
          ∀ i j, IsAffine ((𝒰' i).obj j)),
          ∀ (i : 𝒰.J) (j k : (𝒰' i).J),
            CompactSpace (pullback ((𝒰' i).map j) ((𝒰' i).map k)).carrier] :=
  by
  have := quasi_compact.affine_property_is_local.diagonal_affine_open_cover_tfae f
  simp_rw [← quasi_compact_eq_affine_property, ← quasi_separated_eq_diagonal_is_quasi_compact,
    quasi_compact_affine_property_diagonal_eq] at this 
  exact this
#align algebraic_geometry.quasi_separated.affine_open_cover_tfae AlgebraicGeometry.QuasiSeparated.affine_openCover_tFAE

theorem QuasiSeparated.is_local_at_target : PropertyIsLocalAtTarget @QuasiSeparated :=
  quasiSeparated_eq_affineProperty_diagonal.symm ▸
    QuasiCompact.affineProperty_isLocal.diagonal.targetAffineLocallyIsLocal
#align algebraic_geometry.quasi_separated.is_local_at_target AlgebraicGeometry.QuasiSeparated.is_local_at_target

theorem QuasiSeparated.openCover_tFAE {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [QuasiSeparated f,
        ∃ 𝒰 : Scheme.OpenCover.{u} Y,
          ∀ i : 𝒰.J, QuasiSeparated (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J),
          QuasiSeparated (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, QuasiSeparated (f ∣_ U),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersionCat g],
          QuasiSeparated (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (hU : iSup U = ⊤),
          ∀ i, QuasiSeparated (f ∣_ U i)] :=
  QuasiSeparated.is_local_at_target.openCover_TFAE f
#align algebraic_geometry.quasi_separated.open_cover_tfae AlgebraicGeometry.QuasiSeparated.openCover_tFAE

theorem quasiSeparated_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X.carrier := by
  rw [quasi_separated_eq_affine_property,
    quasi_separated.affine_property_is_local.affine_target_iff f, quasi_separated.affine_property]
#align algebraic_geometry.quasi_separated_over_affine_iff AlgebraicGeometry.quasiSeparated_over_affine_iff

theorem quasiSeparatedSpace_iff_quasiSeparated (X : Scheme) :
    QuasiSeparatedSpace X.carrier ↔ QuasiSeparated (terminal.from X) :=
  (quasiSeparated_over_affine_iff _).symm
#align algebraic_geometry.quasi_separated_space_iff_quasi_separated AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated

theorem QuasiSeparated.affine_openCover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (f : X ⟶ Y) :
    QuasiSeparated f ↔ ∀ i, QuasiSeparatedSpace (pullback f (𝒰.map i)).carrier :=
  by
  rw [quasi_separated_eq_affine_property,
    quasi_separated.affine_property_is_local.affine_open_cover_iff f 𝒰]
  rfl
#align algebraic_geometry.quasi_separated.affine_open_cover_iff AlgebraicGeometry.QuasiSeparated.affine_openCover_iff

theorem QuasiSeparated.openCover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y) (f : X ⟶ Y) :
    QuasiSeparated f ↔ ∀ i, QuasiSeparated (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  QuasiSeparated.is_local_at_target.openCover_iff f 𝒰
#align algebraic_geometry.quasi_separated.open_cover_iff AlgebraicGeometry.QuasiSeparated.openCover_iff

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated g] :
    QuasiSeparated (pullback.fst : pullback f g ⟶ X) :=
  quasiSeparated_stableUnderBaseChange.fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated f] :
    QuasiSeparated (pullback.snd : pullback f g ⟶ Y) :=
  quasiSeparated_stableUnderBaseChange.snd f g inferInstance

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  quasiSeparated_stableUnderComposition f g inferInstance inferInstance

theorem quasiSeparatedSpace_of_quasiSeparated {X Y : Scheme} (f : X ⟶ Y)
    [hY : QuasiSeparatedSpace Y.carrier] [QuasiSeparated f] : QuasiSeparatedSpace X.carrier :=
  by
  rw [quasi_separated_space_iff_quasi_separated] at hY ⊢
  have : f ≫ terminal.from Y = terminal.from X := terminal_is_terminal.hom_ext _ _
  rw [← this]
  skip; infer_instance
#align algebraic_geometry.quasi_separated_space_of_quasi_separated AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated

instance quasiSeparatedSpace_of_isAffine (X : Scheme) [IsAffine X] :
    QuasiSeparatedSpace X.carrier := by
  constructor
  intro U V hU hU' hV hV'
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hU', hU⟩
  obtain ⟨s', hs', e'⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hV', hV⟩
  rw [e, e', Set.iUnion₂_inter]
  simp_rw [Set.inter_iUnion₂]
  apply hs.is_compact_bUnion
  · intro i hi
    apply hs'.is_compact_bUnion
    intro i' hi'
    change IsCompact (X.basic_open i ⊓ X.basic_open i').1
    rw [← Scheme.basic_open_mul]
    exact ((top_is_affine_open _).basicOpenIsAffine _).IsCompact
#align algebraic_geometry.quasi_separated_space_of_is_affine AlgebraicGeometry.quasiSeparatedSpace_of_isAffine

theorem IsAffineOpen.isQuasiSeparated {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) :
    IsQuasiSeparated (U : Set X.carrier) :=
  by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.is_open]
#align algebraic_geometry.is_affine_open.is_quasi_separated AlgebraicGeometry.IsAffineOpen.isQuasiSeparated

theorem quasiSeparatedOfComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [H : QuasiSeparated (f ≫ g)] :
    QuasiSeparated f :=
  by
  rw [(quasi_separated.affine_open_cover_tfae f).out 0 1]
  rw [(quasi_separated.affine_open_cover_tfae (f ≫ g)).out 0 2] at H 
  use (Z.affine_cover.pullback_cover g).bind fun x => Scheme.affine_cover _
  constructor; · intro i; dsimp; infer_instance
  rintro ⟨i, j⟩; dsimp at *
  specialize H _ i
  refine' @quasi_separated_space_of_quasi_separated _ H _
  ·
    exact
      pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (category.comp_id _) ≫
        (pullback_right_pullback_fst_iso g (Z.affine_cover.map i) f).Hom
  · apply AlgebraicGeometry.quasiSeparatedOfMono
#align algebraic_geometry.quasi_separated_of_comp AlgebraicGeometry.quasiSeparatedOfComp

theorem exists_eq_pow_mul_of_isAffineOpen (X : Scheme) (U : Opens X.carrier) (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) (x : X.Presheaf.obj (op <| X.basicOpen f)) :
    ∃ (n : ℕ) (y : X.Presheaf.obj (op U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x :=
  by
  have := (is_localization_basic_open hU f).2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict
  simpa [mul_comm x] using d.symm
#align algebraic_geometry.exists_eq_pow_mul_of_is_affine_open AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen

theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme)
    (S : X.affineOpens) (U₁ U₂ : Opens X.carrier) {n₁ n₂ : ℕ} {y₁ : X.Presheaf.obj (op U₁)}
    {y₂ : X.Presheaf.obj (op U₂)} {f : X.Presheaf.obj (op <| U₁ ⊔ U₂)}
    {x : X.Presheaf.obj (op <| X.basicOpen f)} (h₁ : S.1 ≤ U₁) (h₂ : S.1 ≤ U₂)
    (e₁ :
      X.Presheaf.map
          (homOfLE <| X.basicOpen_le (X.Presheaf.map (homOfLE le_sup_left).op f) : _ ⟶ U₁).op y₁ =
        X.Presheaf.map (homOfLE (by erw [X.basic_open_res]; exact inf_le_left)).op
              (X.Presheaf.map (homOfLE le_sup_left).op f) ^
            n₁ *
          (X.Presheaf.map (homOfLE (by erw [X.basic_open_res]; exact inf_le_right)).op) x)
    (e₂ :
      X.Presheaf.map
          (homOfLE <| X.basicOpen_le (X.Presheaf.map (homOfLE le_sup_right).op f) : _ ⟶ U₂).op y₂ =
        X.Presheaf.map (homOfLE (by rw [X.basic_open_res]; exact inf_le_left)).op
              (X.Presheaf.map (homOfLE le_sup_right).op f) ^
            n₂ *
          (X.Presheaf.map (homOfLE (by rw [X.basic_open_res]; exact inf_le_right)).op) x) :
    ∃ n : ℕ,
      X.Presheaf.map (homOfLE <| h₁).op
          (X.Presheaf.map (homOfLE le_sup_left).op f ^ (n + n₂) * y₁) =
        X.Presheaf.map (homOfLE <| h₂).op
          (X.Presheaf.map (homOfLE le_sup_right).op f ^ (n + n₁) * y₂) :=
  by
  have :=
    is_localization_basic_open S.2 (X.presheaf.map (hom_of_le <| le_trans h₁ le_sup_left).op f)
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _ this
          (X.presheaf.map (hom_of_le <| h₁).op
            (X.presheaf.map (hom_of_le le_sup_left).op f ^ n₂ * y₁))
          (X.presheaf.map (hom_of_le <| h₂).op
            (X.presheaf.map (hom_of_le le_sup_right).op f ^ n₁ * y₂))).mp
      _
  swap
  · simp only [map_pow, RingHom.algebraMap_toAlgebra, map_mul, ← comp_apply, ← functor.map_comp, ←
      op_comp, hom_of_le_comp]
    have h₃ : X.basic_open ((X.presheaf.map (hom_of_le (h₁.trans le_sup_left)).op) f) ≤ S.val := by
      simpa only [X.basic_open_res] using inf_le_left
    trans
      X.presheaf.map (hom_of_le <| h₃.trans <| h₁.trans le_sup_left).op f ^ (n₂ + n₁) *
        X.presheaf.map (hom_of_le <| (X.basic_open_res f _).trans_le inf_le_right).op x
    · rw [pow_add, mul_assoc]; congr 1
      convert congr_arg (X.presheaf.map (hom_of_le _).op) e₁
      · simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp]; congr
      · simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp]; congr
      · rw [X.basic_open_res, X.basic_open_res]; rintro x ⟨H₁, H₂⟩; exact ⟨h₁ H₁, H₂⟩
    · rw [add_comm, pow_add, mul_assoc]; congr 1
      convert congr_arg (X.presheaf.map (hom_of_le _).op) e₂.symm
      · simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp]; congr
      · simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp]; congr
      · simp only [X.basic_open_res]
        rintro x ⟨H₁, H₂⟩; exact ⟨h₂ H₁, H₂⟩
  use n
  simp only [pow_add, map_pow, map_mul, ← comp_apply, ← mul_assoc, ← functor.map_comp,
    Subtype.coe_mk] at e ⊢
  exact e
#align algebraic_geometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux AlgebraicGeometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux

theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : Opens X.carrier)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : X.Presheaf.obj (op U))
    (x : X.Presheaf.obj (op <| X.basicOpen f)) :
    ∃ (n : ℕ) (y : X.Presheaf.obj (op U)), y |_ X.basicOpen f = (f |_ X.basicOpen f) ^ n * x :=
  by
  delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict
  revert hU' f x
  apply compact_open_induction_on U hU
  · intro hU' f x
    use 0, f
    refine'
      @Subsingleton.elim
        (CommRingCat.subsingleton_of_isTerminal (X.sheaf.is_terminal_of_eq_empty _)) _ _
    erw [eq_bot_iff]
    exact X.basic_open_le f
  · -- Given `f : 𝒪(S ∪ U), x : 𝒪(X_f)`, we need to show that `f ^ n * x` is the restriction of
    -- some `y : 𝒪(S ∪ U)` for some `n : ℕ`.
    intro S hS U hU hSU f x
    -- We know that such `y₁, n₁` exists on `S` by the induction hypothesis.
    obtain ⟨n₁, y₁, hy₁⟩ :=
      hU (hSU.of_subset <| Set.subset_union_left _ _) (X.presheaf.map (hom_of_le le_sup_left).op f)
        (X.presheaf.map (hom_of_le _).op x)
    swap; · rw [X.basic_open_res]; exact inf_le_right
    -- We know that such `y₂, n₂` exists on `U` since `U` is affine.
    obtain ⟨n₂, y₂, hy₂⟩ :=
      exists_eq_pow_mul_of_is_affine_open X _ U.2 (X.presheaf.map (hom_of_le le_sup_right).op f)
        (X.presheaf.map (hom_of_le _).op x)
    delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict at hy₂ 
    swap; · rw [X.basic_open_res]; exact inf_le_right
    -- Since `S ∪ U` is quasi-separated, `S ∩ U` can be covered by finite affine opens.
    obtain ⟨s, hs', hs⟩ :=
      (is_compact_open_iff_eq_finset_affine_union _).mp
        ⟨hSU _ _ (Set.subset_union_left _ _) S.2 hS (Set.subset_union_right _ _) U.1.2
            U.2.IsCompact,
          (S ⊓ U.1).2⟩
    haveI := hs'.to_subtype
    cases nonempty_fintype s
    replace hs : S ⊓ U.1 = iSup fun i : s => (i : opens X.carrier) := by ext1; simpa using hs
    have hs₁ : ∀ i : s, i.1.1 ≤ S := by
      intro i; change (i : opens X.carrier) ≤ S
      refine' le_trans _ inf_le_left; use U.1; erw [hs]; exact le_iSup _ _
    have hs₂ : ∀ i : s, i.1.1 ≤ U.1 := by
      intro i; change (i : opens X.carrier) ≤ U
      refine' le_trans _ inf_le_right; use S; erw [hs]; exact le_iSup _ _
    -- On each affine open in the intersection, we have `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- for some `n` since `f ^ n₂ * y₁ = f ^ (n₁ + n₂) * x = f ^ n₁ * y₂` on `X_f`.
    have :
      ∀ i : s,
        ∃ n : ℕ,
          X.presheaf.map (hom_of_le <| hs₁ i).op
              (X.presheaf.map (hom_of_le le_sup_left).op f ^ (n + n₂) * y₁) =
            X.presheaf.map (hom_of_le <| hs₂ i).op
              (X.presheaf.map (hom_of_le le_sup_right).op f ^ (n + n₁) * y₂) :=
      by
      intro i
      exact
        exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux X i.1 S U (hs₁ i) (hs₂ i) hy₁
          hy₂
    choose n hn using this
    -- We can thus choose a big enough `n` such that `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`
    -- on `S ∩ U`.
    have :
      X.presheaf.map (hom_of_le <| inf_le_left).op
          (X.presheaf.map (hom_of_le le_sup_left).op f ^ (finset.univ.sup n + n₂) * y₁) =
        X.presheaf.map (hom_of_le <| inf_le_right).op
          (X.presheaf.map (hom_of_le le_sup_right).op f ^ (finset.univ.sup n + n₁) * y₂) :=
      by
      fapply TopCat.Sheaf.eq_of_locally_eq'.{u + 1, u} X.sheaf fun i : s => i.1.1
      · refine' fun i => hom_of_le _; erw [hs]; exact le_iSup _ _
      · exact le_of_eq hs
      · intro i
        replace hn :=
          congr_arg
            (fun x =>
              X.presheaf.map (hom_of_le (le_trans (hs₁ i) le_sup_left)).op f ^
                  (finset.univ.sup n - n i) *
                x)
            (hn i)
        dsimp only at hn 
        delta Scheme.sheaf SheafedSpace.sheaf
        simp only [← map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp, ← mul_assoc] at
          hn ⊢
        erw [← map_mul, ← map_mul] at hn 
        rw [← pow_add, ← pow_add, ← add_assoc, ← add_assoc, tsub_add_cancel_of_le] at hn 
        convert hn
        exact Finset.le_sup (Finset.mem_univ _)
    use finset.univ.sup n + n₁ + n₂
    -- By the sheaf condition, since `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`, it can be glued into
    -- the desired section on `S ∪ U`.
    use (X.sheaf.obj_sup_iso_prod_eq_locus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩
    refine'
      TopCat.Sheaf.eq_of_locally_eq₂.{u + 1, u} X.sheaf
        (hom_of_le (_ : X.basic_open (X.presheaf.map (hom_of_le le_sup_left).op f) ≤ _))
        (hom_of_le (_ : X.basic_open (X.presheaf.map (hom_of_le le_sup_right).op f) ≤ _)) _ _ _ _ _
    · rw [X.basic_open_res]; exact inf_le_right
    · rw [X.basic_open_res]; exact inf_le_right
    · rw [X.basic_open_res, X.basic_open_res]
      erw [← inf_sup_right]
      refine' le_inf_iff.mpr ⟨X.basic_open_le f, le_of_eq rfl⟩
    · convert
        congr_arg (X.presheaf.map (hom_of_le _).op)
          (X.sheaf.obj_sup_iso_prod_eq_locus_inv_fst S U.1 ⟨⟨_ * _, _ * _⟩, this⟩) using
        1
      · delta Scheme.sheaf SheafedSpace.sheaf
        simp only [← comp_apply (X.presheaf.map _) (X.presheaf.map _), ← functor.map_comp, ←
          op_comp]
        congr
      · delta Scheme.sheaf SheafedSpace.sheaf
        simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp, mul_assoc,
          pow_add]
        erw [hy₁]; congr 1; rw [← mul_assoc, ← mul_assoc]; congr 1
        rw [mul_comm, ← comp_apply, ← functor.map_comp]; congr
    · convert
        congr_arg (X.presheaf.map (hom_of_le _).op)
          (X.sheaf.obj_sup_iso_prod_eq_locus_inv_snd S U.1 ⟨⟨_ * _, _ * _⟩, this⟩) using
        1
      · delta Scheme.sheaf SheafedSpace.sheaf
        simp only [← comp_apply (X.presheaf.map _) (X.presheaf.map _), ← functor.map_comp, ←
          op_comp]
        congr
      · delta Scheme.sheaf SheafedSpace.sheaf
        simp only [map_pow, map_mul, ← comp_apply, ← functor.map_comp, ← op_comp, mul_assoc,
          pow_add]
        erw [hy₂]; rw [← comp_apply, ← functor.map_comp]; congr
#align algebraic_geometry.exists_eq_pow_mul_of_is_compact_of_is_quasi_separated AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
theorem is_localization_basicOpen_of_qcqs {X : Scheme} {U : Opens X.carrier} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : X.Presheaf.obj (op U)) :
    IsLocalization.Away f (X.Presheaf.obj (op <| X.basicOpen f)) :=
  by
  constructor
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, Subtype.coe_mk, RingHom.algebraMap_toAlgebra]
    exact IsUnit.pow _ (RingedSpace.is_unit_res_basic_open _ f)
  · intro z
    obtain ⟨n, y, e⟩ := exists_eq_pow_mul_of_is_compact_of_is_quasi_separated X U hU hU' f z
    refine' ⟨⟨y, _, n, rfl⟩, _⟩
    simpa only [map_pow, Subtype.coe_mk, RingHom.algebraMap_toAlgebra, mul_comm z] using e.symm
  · intro x y
    rw [← sub_eq_zero, ← map_sub, RingHom.algebraMap_toAlgebra]
    simp_rw [← @sub_eq_zero _ _ (_ * x) (_ * y), ← mul_sub]
    generalize x - y = z
    constructor
    · intro H
      obtain ⟨n, e⟩ := exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact X hU _ _ H
      refine' ⟨⟨_, n, rfl⟩, _⟩
      simpa [mul_comm z] using e
    · rintro ⟨⟨_, n, rfl⟩, e : f ^ n * z = 0⟩
      rw [← ((RingedSpace.is_unit_res_basic_open _ f).pow n).mul_right_inj, MulZeroClass.mul_zero, ←
        map_pow, ← map_mul, e, map_zero]
#align algebraic_geometry.is_localization_basic_open_of_qcqs AlgebraicGeometry.is_localization_basicOpen_of_qcqs

end AlgebraicGeometry

