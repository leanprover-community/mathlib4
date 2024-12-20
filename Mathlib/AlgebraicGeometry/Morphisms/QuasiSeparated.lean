/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Sheaves.CommRingCat

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

theorem quasiSeparatedSpace_iff_affine (X : Scheme) :
    QuasiSeparatedSpace X ↔ ∀ U V : X.affineOpens, IsCompact (U ∩ V : Set X) := by
  rw [quasiSeparatedSpace_iff]
  constructor
  · intro H U V; exact H U V U.1.2 U.2.isCompact V.1.2 V.2.isCompact
  · intro H
    suffices
      ∀ (U : X.Opens) (_ : IsCompact U.1) (V : X.Opens) (_ : IsCompact V.1),
        IsCompact (U ⊓ V).1
      by intro U V hU hU' hV hV'; exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV'
    intro U hU V hV
    refine compact_open_induction_on V hV ?_ ?_
    · simp
    · intro S _ V hV
      change IsCompact (U.1 ∩ (S.1 ∪ V.1))
      rw [Set.inter_union_distrib_left]
      apply hV.union
      clear hV
      refine compact_open_induction_on U hU ?_ ?_
      · simp
      · intro S _ W hW
        change IsCompact ((S.1 ∪ W.1) ∩ V.1)
        rw [Set.union_inter_distrib_right]
        apply hW.union
        apply H

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
    let g : pullback U.1.ι V.1.ι ⟶ X := pullback.fst _ _ ≫ U.1.ι
    -- Porting note: `inferInstance` does not work here
    have : IsOpenImmersion g := PresheafedSpace.IsOpenImmersion.comp _ _
    have e := Homeomorph.ofIsEmbedding _ this.base_open.isEmbedding
    rw [IsOpenImmersion.range_pullback_to_base_of_left] at e
    erw [Subtype.range_coe, Subtype.range_coe] at e
    rw [isCompact_iff_compactSpace]
    exact @Homeomorph.compactSpace _ _ _ _ (H _ _) e
  · introv H h₁ h₂
    let g : pullback f₁ f₂ ⟶ X := pullback.fst _ _ ≫ f₁
    -- Porting note: `inferInstance` does not work here
    have : IsOpenImmersion g := PresheafedSpace.IsOpenImmersion.comp _ _
    have e := Homeomorph.ofIsEmbedding _ this.base_open.isEmbedding
    rw [IsOpenImmersion.range_pullback_to_base_of_left] at e
    simp_rw [isCompact_iff_compactSpace] at H
    exact
      @Homeomorph.compactSpace _ _ _ _
        (H ⟨⟨_, h₁.base_open.isOpen_range⟩, isAffineOpen_opensRange _⟩
          ⟨⟨_, h₂.base_open.isOpen_range⟩, isAffineOpen_opensRange _⟩)
        e.symm

theorem quasiSeparated_eq_diagonal_is_quasiCompact :
    @QuasiSeparated = MorphismProperty.diagonal @QuasiCompact := by ext; exact quasiSeparated_iff _

instance : HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X) where
  __ := HasAffineProperty.copy
    quasiSeparated_eq_diagonal_is_quasiCompact.symm
    (by ext; exact quasiCompact_affineProperty_iff_quasiSeparatedSpace _)

instance (priority := 900) quasiSeparatedOfMono {X Y : Scheme} (f : X ⟶ Y) [Mono f] :
    QuasiSeparated f where

instance quasiSeparated_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

instance quasiSeparated_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiSeparated :=
  quasiSeparated_eq_diagonal_is_quasiCompact.symm ▸ inferInstance

instance quasiSeparatedComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f]
    [QuasiSeparated g] : QuasiSeparated (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

theorem quasiSeparated_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)]

theorem quasiSeparatedSpace_iff_quasiSeparated (X : Scheme) :
    QuasiSeparatedSpace X ↔ QuasiSeparated (terminal.from X) :=
  (quasiSeparated_over_affine_iff _).symm

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated g] :
    QuasiSeparated (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated f] :
    QuasiSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

theorem quasiSeparatedSpace_of_quasiSeparated {X Y : Scheme} (f : X ⟶ Y)
    [hY : QuasiSeparatedSpace Y] [QuasiSeparated f] : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_quasiSeparated] at hY ⊢
  rw [← terminalIsTerminal.hom_ext (f ≫ terminal.from Y) (terminal.from X)]
  infer_instance

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

theorem IsAffineOpen.isQuasiSeparated {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) :
    IsQuasiSeparated (U : Set X) := by
  rw [isQuasiSeparated_iff_quasiSeparatedSpace]
  exacts [@AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _ hU, U.isOpen]

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

theorem exists_eq_pow_mul_of_isAffineOpen (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ᵣ X.basicOpen f = (f |_ᵣ X.basicOpen f) ^ n * x := by
  have := (hU.isLocalization_basicOpen f).2
  obtain ⟨⟨y, _, n, rfl⟩, d⟩ := this x
  use n, y
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply]
  simpa [mul_comm x] using d.symm

theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux {X : TopCat}
    (F : X.Presheaf CommRingCat) {U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Opens X} {n₁ n₂ : ℕ}
    {y₁ : F.obj (op U₁)} {y₂ : F.obj (op U₂)} {f : F.obj (op <| U₁ ⊔ U₂)}
    {x : F.obj (op U₃)} (h₄₁ : U₄ ≤ U₁) (h₄₂ : U₄ ≤ U₂) (h₅₁ : U₅ ≤ U₁) (h₅₃ : U₅ ≤ U₃)
    (h₆₂ : U₆ ≤ U₂) (h₆₃ : U₆ ≤ U₃) (h₇₄ : U₇ ≤ U₄) (h₇₅ : U₇ ≤ U₅) (h₇₆ : U₇ ≤ U₆)
    (e₁ : y₁ |_ᵣ U₅ = (f |_ᵣ U₁ |_ᵣ U₅) ^ n₁ * x |_ᵣ U₅)
    (e₂ : y₂ |_ᵣ U₆ = (f |_ᵣ U₂ |_ᵣ U₆) ^ n₂ * x |_ᵣ U₆) :
    (((f |_ᵣ U₁) ^ n₂ * y₁) |_ᵣ U₄) |_ᵣ U₇ = (((f |_ᵣ U₂) ^ n₁ * y₂) |_ᵣ U₄) |_ᵣ U₇ := by
  apply_fun (fun x : F.obj (op U₅) ↦ x |_ᵣ U₇) at e₁
  apply_fun (fun x : F.obj (op U₆) ↦ x |_ᵣ U₇) at e₂
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at e₁ e₂ ⊢
  simp only [map_mul, map_pow, ← op_comp, ← F.map_comp, homOfLE_comp, ← CommRingCat.comp_apply]
    at e₁ e₂ ⊢
  rw [e₁, e₂, mul_left_comm]

theorem exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux (X : Scheme)
    (S : X.affineOpens) (U₁ U₂ : X.Opens) {n₁ n₂ : ℕ} {y₁ : Γ(X, U₁)}
    {y₂ : Γ(X, U₂)} {f : Γ(X, U₁ ⊔ U₂)}
    {x : Γ(X, X.basicOpen f)} (h₁ : S.1 ≤ U₁) (h₂ : S.1 ≤ U₂)
    (e₁ : y₁ |_ᵣ X.basicOpen (f |_ᵣ U₁) =
      ((f |_ᵣ U₁ |_ᵣ X.basicOpen _) ^ n₁) * x |_ᵣ X.basicOpen _)
    (e₂ : y₂ |_ᵣ X.basicOpen (f |_ᵣ U₂) =
      ((f |_ᵣ U₂ |_ᵣ X.basicOpen _) ^ n₂) * x |_ᵣ X.basicOpen _) :
    ∃ n : ℕ, ∀ m, n ≤ m →
      ((f |_ᵣ U₁) ^ (m + n₂) * y₁) |_ᵣ S.1 = ((f |_ᵣ U₂) ^ (m + n₁) * y₂) |_ᵣ S.1 := by
  obtain ⟨⟨_, n, rfl⟩, e⟩ :=
    (@IsLocalization.eq_iff_exists _ _ _ _ _ _
      (S.2.isLocalization_basicOpen (f |_ᵣ S.1))
        (((f |_ᵣ U₁) ^ n₂ * y₁) |_ᵣ S.1)
        (((f |_ᵣ U₂) ^ n₁ * y₂) |_ᵣ S.1)).mp <| by
    apply exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux (e₁ := e₁) (e₂ := e₂)
    · show X.basicOpen _ ≤ _
      simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, Scheme.basicOpen_res]
      exact inf_le_inf h₁ le_rfl
    · show X.basicOpen _ ≤ _
      simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, Scheme.basicOpen_res]
      exact inf_le_inf h₂ le_rfl
  use n
  intros m hm
  rw [← tsub_add_cancel_of_le hm]
  simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply,
    pow_add, map_pow, map_mul, mul_assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp,
    Subtype.coe_mk, ← CommRingCat.comp_apply] at e ⊢
  rw [e]

theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated (X : Scheme.{u}) (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ᵣ X.basicOpen f = (f |_ᵣ X.basicOpen f) ^ n * x := by
  dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply]
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    use 0, f
    refine @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)) _ _
    rw [eq_bot_iff]
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
    dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at hy₂
    -- swap; · rw [X.basicOpen_res]; exact inf_le_right
    -- Since `S ∪ U` is quasi-separated, `S ∩ U` can be covered by finite affine opens.
    obtain ⟨s, hs', hs⟩ :=
      (isCompactOpen_iff_eq_finset_affine_union _).mp
        ⟨hSU _ _ Set.subset_union_left S.2 hS Set.subset_union_right U.1.2
            U.2.isCompact,
          (S ⊓ U.1).2⟩
    haveI := hs'.to_subtype
    cases nonempty_fintype s
    replace hs : S ⊓ U.1 = iSup fun i : s => (i : X.Opens) := by ext1; simpa using hs
    have hs₁ : ∀ i : s, i.1.1 ≤ S := by
      intro i; change (i : X.Opens) ≤ S
      refine le_trans ?_ (inf_le_left (b := U.1))
      rw [hs]
      -- Porting note: have to add argument explicitly
      exact @le_iSup X.Opens s _ (fun (i : s) => (i : X.Opens)) i
    have hs₂ : ∀ i : s, i.1.1 ≤ U.1 := by
      intro i; change (i : X.Opens) ≤ U
      refine le_trans ?_ (inf_le_right (a := S))
      rw [hs]
      -- Porting note: have to add argument explicitly
      exact @le_iSup X.Opens s _ (fun (i : s) => (i : X.Opens)) i
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
      · refine fun i => homOfLE ?_; rw [hs]
        -- Porting note: have to add argument explicitly
        exact @le_iSup X.Opens s _ (fun (i : s) => (i : X.Opens)) i
      · exact le_of_eq hs
      · intro i
        -- This unfolds `X.sheaf` and ensures we use `CommRingCat.hom` to apply the morphism
        show (X.presheaf.map _) _ = (X.presheaf.map _) _
        simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
        apply hn
        exact Finset.le_sup (Finset.mem_univ _)
    use Finset.univ.sup n + n₁ + n₂
    -- By the sheaf condition, since `f ^ (n + n₂) * y₁ = f ^ (n + n₁) * y₂`, it can be glued into
    -- the desired section on `S ∪ U`.
    use (X.sheaf.objSupIsoProdEqLocus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩
    refine (X.sheaf.objSupIsoProdEqLocus_inv_eq_iff _ _ _ (X.basicOpen_res _
      (homOfLE le_sup_left).op) (X.basicOpen_res _ (homOfLE le_sup_right).op)).mpr ⟨?_, ?_⟩
    · -- This unfolds `X.sheaf` and ensures we use `CommRingCat.hom` to apply the morphism
      show (X.presheaf.map _) _ = (X.presheaf.map _) _
      rw [add_assoc, add_comm n₁]
      simp only [pow_add, map_pow, map_mul, hy₁, ← CommRingCat.comp_apply, ← mul_assoc,
        ← Functor.map_comp, ← op_comp, homOfLE_comp]
    · -- This unfolds `X.sheaf` and ensures we use `CommRingCat.hom` to apply the morphism
      show (X.presheaf.map _) _ = (X.presheaf.map _) _
      simp only [pow_add, map_pow, map_mul, hy₂, ← CommRingCat.comp_apply, ← mul_assoc,
        ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
theorem is_localization_basicOpen_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompact U.1)
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

lemma exists_of_res_eq_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
    (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    {f g s : Γ(X, U)} (hfg : f |_ᵣ X.basicOpen s = g |_ᵣ X.basicOpen s) :
    ∃ n, s ^ n * f = s ^ n * g := by
  obtain ⟨n, hc⟩ := (is_localization_basicOpen_of_qcqs hU hU' s).exists_of_eq s hfg
  use n

lemma exists_of_res_eq_of_qcqs_of_top {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f g s : Γ(X, ⊤)} (hfg : f |_ᵣ X.basicOpen s = g |_ᵣ X.basicOpen s) :
    ∃ n, s ^ n * f = s ^ n * g :=
  exists_of_res_eq_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hfg

lemma exists_of_res_zero_of_qcqs {X : Scheme.{u}} {U : TopologicalSpace.Opens X}
    (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    {f s : Γ(X, U)} (hf : f |_ᵣ X.basicOpen s = 0) :
    ∃ n, s ^ n * f = 0 := by
  suffices h : ∃ n, s ^ n * f = s ^ n * 0 by
    simpa using h
  apply exists_of_res_eq_of_qcqs hU hU'
  simpa

lemma exists_of_res_zero_of_qcqs_of_top {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
    {f s : Γ(X, ⊤)} (hf : f |_ᵣ X.basicOpen s = 0) :
    ∃ n, s ^ n * f = 0 :=
  exists_of_res_zero_of_qcqs (U := ⊤) CompactSpace.isCompact_univ isQuasiSeparated_univ hf

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
theorem isIso_ΓSpec_adjunction_unit_app_basicOpen {X : Scheme} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X.presheaf.obj (op ⊤)) :
    IsIso ((ΓSpec.adjunction.unit.app X).c.app (op (PrimeSpectrum.basicOpen f))) := by
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ (X.presheaf.map
    (eqToHom (Scheme.toSpecΓ_preimage_basicOpen _ _).symm).op) _ ?_
  rw [ConcreteCategory.isIso_iff_bijective, CommRingCat.forget_map]
  apply (config := { allowSynthFailures := true }) IsLocalization.bijective
  · exact StructureSheaf.IsLocalization.to_basicOpen _ _
  · refine is_localization_basicOpen_of_qcqs ?_ ?_ _
    · exact isCompact_univ
    · exact isQuasiSeparated_univ
  · simp only [RingHom.algebraMap_toAlgebra]
    -- This `rw` doesn't fire as a `simp` (`only`).
    rw [← CommRingCat.hom_comp]
    simp [RingHom.algebraMap_toAlgebra, ← Functor.map_comp]

end AlgebraicGeometry
