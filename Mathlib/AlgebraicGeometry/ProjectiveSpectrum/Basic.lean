/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing

/-!

# Basic properties of the scheme `Proj A`

The scheme `Proj 𝒜` for a graded algebra `𝒜` is constructed in
`AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`.
In this file we provide basic properties of the scheme.

## Main results
- `AlgebraicGeometry.Proj.toSpecZero`: The structure map `Proj A ⟶ Spec (A 0)`.
- `AlgebraicGeometry.Proj.basicOpenIsoSpec`:
  The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
  when `f` is homogeneous of positive degree.
- `AlgebraicGeometry.Proj.awayι`: The open immersion `Spec (A_f)₀ ⟶ Proj A`.
- `AlgebraicGeometry.Proj.affineOpenCover`: The open cover of `Proj A` by `Spec (A_f)₀` for all
  homogeneous `f` of positive degree.
- `AlgebraicGeometry.Proj.stalkIso`:
  The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`.
- `AlgebraicGeometry.Proj.fromOfGlobalSections`:
  Given a map `f : A →+* Γ(X, ⊤)` such that the image of the irrelevant ideal under `f`
  generates the whole ring, we can construct a map `X ⟶ Proj 𝒜`.

-/

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization CategoryTheory

universe u

variable {R : Type*} {A : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A)
variable [GradedAlgebra 𝒜]

section basicOpen

variable (f g : A)

/-- The basic open set `D₊(f)` associated to `f : A`. -/
def basicOpen : (Proj 𝒜).Opens :=
  ProjectiveSpectrum.basicOpen 𝒜 f

@[simp]
theorem mem_basicOpen (x : Proj 𝒜) :
    x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

@[simp] theorem basicOpen_one : basicOpen 𝒜 1 = ⊤ := ProjectiveSpectrum.basicOpen_one ..

@[simp] theorem basicOpen_zero : basicOpen 𝒜 0 = ⊥ := ProjectiveSpectrum.basicOpen_zero ..

@[simp] theorem basicOpen_pow (n) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  ProjectiveSpectrum.basicOpen_pow 𝒜 f n hn

theorem basicOpen_mul : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
  ProjectiveSpectrum.basicOpen_mul ..

theorem basicOpen_mono (hfg : f ∣ g) : basicOpen 𝒜 g ≤ basicOpen 𝒜 f :=
  (hfg.choose_spec ▸ basicOpen_mul 𝒜 f _).trans_le inf_le_left

theorem basicOpen_eq_iSup_proj (f : A) :
    basicOpen 𝒜 f = ⨆ i : ℕ, basicOpen 𝒜 (GradedAlgebra.proj 𝒜 i f) :=
  ProjectiveSpectrum.basicOpen_eq_union_of_projection ..

theorem isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (basicOpen 𝒜)) := by
  delta TopologicalSpace.Opens.IsBasis
  convert ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜
  exact (Set.range_comp _ _).symm

/-- If `{ xᵢ }` spans the irrelevant ideal of `A`, then `D₊(xᵢ)` covers `Proj A`. -/
lemma iSup_basicOpen_eq_top {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  refine top_le_iff.mp fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  rwa [Ideal.span_le, Set.range_subset_iff]

/-- If `{ xᵢ }` are homogeneous and span `A` as an `A₀` algebra, then `D₊(xᵢ)` covers `Proj A`. -/
lemma iSup_basicOpen_eq_top' {ι : Type*} (f : ι → A)
    (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  apply Proj.iSup_basicOpen_eq_top
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x ∈ $hf)).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hfn i
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    convert zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert add_mem (Ideal.mul_mem_left _ x hy')
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
    rw [map_mul]
    ring

/-- The canonical map `(A_f)₀ ⟶ Γ(Proj A, D₊(f))`.
This is an isomorphism when `f` is homogeneous of positive degree. See `basicOpenIsoAway` below. -/
def awayToSection : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  ProjectiveSpectrum.Proj.awayToSection ..

/-- The canonical map `Proj A |_ D₊(f) ⟶ Spec (A_f)₀`.
This is an isomorphism when `f` is homogeneous of positive degree. See `basicOpenIsoSpec` below. -/
noncomputable
def basicOpenToSpec : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f) :=
  (basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)

lemma basicOpenToSpec_app_top :
    (basicOpenToSpec 𝒜 f).app ⊤ = (Scheme.ΓSpecIso _).hom ≫ awayToSection 𝒜 f ≫
      (basicOpen 𝒜 f).topIso.inv := by
  rw [basicOpenToSpec]
  simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
    TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, Scheme.Opens.topIso_inv, eqToHom_op]
  erw [Scheme.Hom.comp_app]
  simp

/-- The structure map `Proj A ⟶ Spec A₀`. -/
noncomputable
def toSpecZero : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0) :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))

variable {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

/-- The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
when `f` is homogeneous of positive degree. -/
@[simps! -isSimp hom]
noncomputable
def basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f) :=
  have : IsIso (basicOpenToSpec 𝒜 f) := by
    apply (isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_
    convert ProjectiveSpectrum.Proj.isIso_toSpec 𝒜 f f_deg hm using 1
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [eqToHom_op, Category.assoc, ← Spec.map_comp]
    rfl
  asIso (basicOpenToSpec 𝒜 f)

/-- The canonical isomorphism `(A_f)₀ ≅ Γ(Proj A, D₊(f))`
when `f` is homogeneous of positive degree. -/
@[simps! -isSimp hom]
noncomputable
def basicOpenIsoAway : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  have : IsIso (awayToSection 𝒜 f) := by
    have := basicOpenToSpec_app_top 𝒜 f
    rw [← Iso.inv_comp_eq, Iso.eq_comp_inv] at this
    rw [← this, ← basicOpenIsoSpec_hom 𝒜 f f_deg hm]
    infer_instance
  asIso (awayToSection 𝒜 f)

/-- The open immersion `Spec (A_f)₀ ⟶ Proj A`. -/
noncomputable
def awayι : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜 :=
  (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι

@[reassoc]
lemma basicOpenIsoSpec_inv_ι :
    (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι = awayι 𝒜 f f_deg hm := rfl

instance : IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) :=
  IsOpenImmersion.comp _ _

lemma opensRange_awayι :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (basicOpen 𝒜 f).opensRange_ι

include f_deg hm in
lemma isAffineOpen_basicOpen : IsAffineOpen (basicOpen 𝒜 f) := by
  rw [← opensRange_awayι 𝒜 f f_deg hm]
  exact isAffineOpen_opensRange (awayι _ _ _ _)

@[reassoc]
lemma awayι_toSpecZero : awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
    Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
  rw [toSpecZero, basicOpenToSpec, awayι]
  simp only [Category.assoc, Iso.inv_comp_eq, basicOpenIsoSpec_hom]
  have (U) (e : U = ⊤) : (basicOpen 𝒜 f).ι ≫ (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e).inv =
      Scheme.homOfLE _ (le_top.trans_eq e.symm) := by
    simp only [← Category.assoc, Iso.comp_inv_eq]
    simp only [Scheme.topIso_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
  rw [reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, basicOpenToSpec,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  rfl

variable {f}
variable {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') {x : A} (hx : x = f * g)

@[reassoc]
lemma awayMap_awayToSection :
    CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ awayToSection 𝒜 x =
      awayToSection 𝒜 f ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩)).op := by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [CommRingCat.hom_ofHom, val_awayMap_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    ← Localization.mk_eq_mk']
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, RingHom.id_apply, one_mul, hx]
  ring

@[reassoc]
lemma basicOpenToSpec_SpecMap_awayMap :
    basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) =
      (Proj 𝒜).homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩) ≫ basicOpenToSpec 𝒜 f := by
  rw [basicOpenToSpec, Category.assoc, ← Spec.map_comp, awayMap_awayToSection,
    Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

@[reassoc]
lemma SpecMap_awayMap_awayι :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫ awayι 𝒜 f f_deg hm =
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) := by
  rw [awayι, awayι, Iso.eq_inv_comp, basicOpenIsoSpec_hom, basicOpenToSpec_SpecMap_awayMap_assoc,
  ← basicOpenIsoSpec_hom _ _ f_deg hm, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

/-- The isomorphism `D₊(f) ×[Proj 𝒜] D₊(g) ≅ D₊(fg)`. -/
noncomputable
def pullbackAwayιIso :
    Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅ Spec (.of <| Away 𝒜 x) :=
    IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
      (awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) <| by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  change ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜 _ _ _).opensRange.1
  rw [opensRange_awayι, opensRange_awayι, opensRange_awayι, ← basicOpen_mul, hx]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_awayι :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) =
      Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_SpecMap_awayMap_left :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) = Limits.pullback.fst _ _ := by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm), ← pullbackAwayιIso_hom_awayι,
    Category.assoc, SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_SpecMap_awayMap_right :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) =
      Limits.pullback.snd _ _ := by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm'), ← Limits.pullback.condition,
    ← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx,
    Category.assoc, SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_inv_fst :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_inv_snd :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right (hx := hx) .., Iso.inv_hom_id_assoc]

include hm' in
lemma awayι_preimage_basicOpen :
    awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 g =
      PrimeSpectrum.basicOpen (Away.isLocalizationElem f_deg g_deg) := by
  ext1
  trans Set.range (Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg rfl))).base
  · rw [← pullbackAwayιIso_inv_fst 𝒜 f_deg hm g_deg hm' rfl]
    simp only [TopologicalSpace.Opens.map_coe, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [Set.range_eq_univ.mpr (by exact
      (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' rfl).inv.homeomorph.surjective),
      ← opensRange_awayι _ _ g_deg hm']
    simp [IsOpenImmersion.range_pullbackFst]
  · letI := (awayMap (f := f) 𝒜 g_deg rfl).toAlgebra
    letI := HomogeneousLocalization.Away.isLocalization_mul f_deg g_deg rfl hm.ne'
    exact PrimeSpectrum.localization_away_comap_range _ _

open TopologicalSpace.Opens in
/-- Given a family of homogeneous elements `f` of positive degree that spans the irrelevant ideal,
`Spec (A_f)₀ ⟶ Proj A` forms an affine open cover of `Proj A`. -/
noncomputable
def affineOpenCoverOfIrrelevantLESpan {ι : Type*} (f : ι → A) {m : ι → ℕ}
    (f_deg : ∀ i, f i ∈ 𝒜 (m i)) (hm : ∀ i, 0 < m i)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    (Proj 𝒜).AffineOpenCover where
  I₀ := ι
  X i := .of (Away 𝒜 (f i))
  f i := awayι 𝒜 (f i) (f_deg i) (hm i)
  idx x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose_spec

@[deprecated (since := "2025-10-07")]
noncomputable alias openCoverOfISupEqTop := affineOpenCoverOfIrrelevantLESpan

/-- `Proj A` is covered by `Spec (A_f)₀` for all homogeneous elements of positive degree. -/
noncomputable
def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan 𝒜
    (ι := Σ i : PNat, 𝒜 i) (m := fun i ↦ i.1) (fun i ↦ i.2) (fun i ↦ i.2.2) (fun i ↦ i.1.2) <| by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
  convert Ideal.zero_mem _
  subst hc0
  exact hz

end basicOpen

section stalk

/-- The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`. -/
noncomputable
def stalkIso (x : Proj 𝒜) :
    (Proj 𝒜).presheaf.stalk x ≅ .of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
  (stalkIso' 𝒜 x).toCommRingCatIso

end stalk

noncomputable section ofGlobalSection

open Limits

variable {X : Scheme.{u}} (f : A →+* Γ(X, ⊤)) {x x' : Γ(X, ⊤)} {t t' : A} {d d' : ℕ}

/-- Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)`,
for each homogeneous `t` of positive degree, it induces a map from `D(f(t)) ⟶ D₊(t)`. -/
def toBasicOpenOfGlobalSections (H : f t = x) (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    (X.basicOpen x).toScheme ⟶ basicOpen 𝒜 t := by
  refine ?_ ≫ (basicOpenIsoSpec _ _ hd h0d).inv
  refine (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ _ ≫ ?_
  refine (basicOpenIsoSpecAway _).hom ≫
    Spec.map (CommRingCat.ofHom (RingHom.comp ?_ (algebraMap _ (Localization.Away t))))
  refine IsLocalization.map (M := .powers t) (T := .powers x) _ f ?_
  · rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
    simp [H]

@[reassoc]
lemma homOfLE_toBasicOpenOfGlobalSections_ι
    {H : f t = x} {h0d : 0 < d} {hd : t ∈ 𝒜 d} {H' : f t' = x'} {h0d' : 0 < d'} {hd' : t' ∈ 𝒜 d'}
    {s : A} (hts : t * s = t') {n : ℕ} (hn : d + n = d') (hs : s ∈ 𝒜 n) :
    X.homOfLE (by aesop) ≫ toBasicOpenOfGlobalSections 𝒜 f H h0d hd ≫ (basicOpen 𝒜 t).ι =
      toBasicOpenOfGlobalSections 𝒜 f H' h0d' hd' ≫ (basicOpen 𝒜 t').ι := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, basicOpenIsoSpec_inv_ι]
  have hx'x : PrimeSpectrum.basicOpen x' ≤ PrimeSpectrum.basicOpen x := by
    aesop (add simp PrimeSpectrum.basicOpen_mul)
  rw [← Scheme.Hom.resLE_map_assoc _ (by simp [X.toSpecΓ_preimage_basicOpen]) hx'x]
  congr 1
  simp only [← Iso.inv_comp_eq]
  subst hts hn
  rw [← SpecMap_awayMap_awayι (𝒜 := 𝒜) hd h0d
    hs rfl, basicOpenIsoSpecAway_inv_homOfLE_assoc (R := Γ(X, ⊤)) x (f s) x' (by simp [← H', H]),
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_awayMap]
  simp only [← RingHom.comp_apply]
  congr 1
  apply IsLocalization.ringHom_ext (M := .powers t)
  ext i
  simp [IsLocalization.Away.awayToAwayRight_eq]

variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

/-- Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)` such that the image of the
irrelevant ideal under `f` generates the whole ring, the set of `D(f(r))` for homogeneous `r`
of positive degree forms an open cover on `X`. -/
def openCoverOfMapIrrelevantEqTop : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
    X.basicOpen (f ir.2.1)) (by
    classical
    have H : Ideal.span (Set.range fun x : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ x.2.1) =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.range_subset_iff]
        rintro ⟨i, r, hi0, hri⟩
        simp [-ZeroMemClass.coe_eq_zero,
          DirectSum.decompose_of_mem_ne 𝒜 hri hi0.ne']
      · intro x hx
        rw [← DirectSum.sum_support_decompose 𝒜 x]
        refine Ideal.sum_mem _ fun c hc ↦ ?_
        have : c ≠ 0 := by contrapose! hc; simpa [hc] using hx
        exact Ideal.subset_span ⟨⟨c, _, this.bot_lt, by simp⟩, rfl⟩
    ext1
    apply compl_injective
    simp only [TopologicalSpace.Opens.coe_iSup, Set.compl_iUnion, ← Scheme.zeroLocus_singleton,
      ← Scheme.zeroLocus_iUnion, Set.iUnion_singleton_eq_range, TopologicalSpace.Opens.coe_top,
      Set.compl_univ]
    rw [← Scheme.zeroLocus_span, Set.range_comp', ← Ideal.map_span, H, hf]
    simp)

@[deprecated (since := "2025-08-22")] noncomputable alias openCoverOfMapIrreleventEqTop :=
  openCoverOfMapIrrelevantEqTop

/-- Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)` such that the image of the
irrelevant ideal under `f` generates the whole ring, we can construct a map `X ⟶ Proj 𝒜`. -/
def fromOfGlobalSections : X ⟶ Proj 𝒜 := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).glueMorphisms
    (fun ri ↦ toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f x)
      ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f y) ≅ (X.basicOpen (f (x.snd.fst * y.snd.fst))) :=
    (isPullback_opens_inf _ _).isoPullback.symm ≪≫ X.isoOfEq (by simp)
  rw [← cancel_epi e.inv]
  trans toBasicOpenOfGlobalSections 𝒜 f rfl (Nat.add_pos_left x.2.2.1 y.1)
    (SetLike.mul_mem_graded x.2.2.2 y.2.2.2) ≫ (Scheme.Opens.ι _)
  · simpa [e, openCoverOfMapIrrelevantEqTop, Scheme.isoOfEq_inv] using
      homOfLE_toBasicOpenOfGlobalSections_ι _ _ rfl rfl y.2.2.2
  · simpa [e, openCoverOfMapIrrelevantEqTop, Scheme.isoOfEq_inv] using
      (homOfLE_toBasicOpenOfGlobalSections_ι _ _ (mul_comm _ _) (add_comm _ _) x.2.2.2).symm

lemma fromOfGlobalSections_preimage_basicOpen {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ basicOpen 𝒜 r = X.basicOpen (f r) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, x, rfl⟩ := (openCoverOfMapIrrelevantEqTop 𝒜 f hf).exists_eq x
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme.Hom.comp_apply, fromOfGlobalSections, Scheme.Cover.ι_glueMorphisms] at hx
    simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_X,
      toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc, basicOpenIsoSpec_inv_ι] at hx
    simp only [Scheme.Hom.comp_base, Scheme.homOfLE_base, homOfLE_leOfHom, TopCat.hom_comp,
      ContinuousMap.comp_assoc, ContinuousMap.comp_apply, morphismRestrict_base,
      TopologicalSpace.Opens.carrier_eq_coe] at hx
    rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe,
      Proj.awayι_preimage_basicOpen (𝒜 := 𝒜) i.2.2.2 i.2.2.1 hr hn,
      ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, ← Function.Injective.mem_set_image
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) _))).isOpenEmbedding.injective,
      ← Scheme.Hom.comp_apply, basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_hom_fac] at hx
    rw [← Scheme.toSpecΓ_preimage_basicOpen, TopologicalSpace.Opens.map_coe, Set.mem_preimage]
    refine Set.mem_of_subset_of_mem (Set.image_subset_iff.mpr ?_) hx
    change PrimeSpectrum.basicOpen _ ≤ PrimeSpectrum.basicOpen _
    simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow,
      PrimeSpectrum.basicOpen_le_basicOpen_iff, IsLocalization.mk'_mem_iff]
    exact Ideal.pow_mem_of_mem _ (Ideal.le_radical (Ideal.mem_span_singleton_self _)) _ i.2.2.1
  · intro x hx
    let I : (openCoverOfMapIrrelevantEqTop 𝒜 f hf).I₀ := ⟨n, r, hn, hr⟩
    obtain ⟨x, rfl⟩ : x ∈ ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f I).opensRange := by
      simpa [openCoverOfMapIrrelevantEqTop] using hx
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme.Hom.comp_apply, fromOfGlobalSections, Scheme.Cover.ι_glueMorphisms]
    simp

lemma fromOfGlobalSections_morphismRestrict {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (fromOfGlobalSections 𝒜 f hf) ∣_ (basicOpen 𝒜 r) =
      (Scheme.isoOfEq _ (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr)).hom ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← Iso.inv_comp_eq, ← cancel_mono (basicOpen 𝒜 r).ι]
  simp only [Scheme.isoOfEq_inv, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
    fromOfGlobalSections]
  exact (openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩

lemma fromOfGlobalSections_resLE {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (fromOfGlobalSections 𝒜 f hf).resLE _ _
      (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr).ge =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← (Iso.inv_comp_eq _).mpr (fromOfGlobalSections_morphismRestrict 𝒜 f hf hn hr),
    ← Scheme.Hom.resLE_eq_morphismRestrict]
  simp [Scheme.isoOfEq_inv]

@[reassoc]
lemma fromOfGlobalSections_toSpecZero
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    fromOfGlobalSections 𝒜 f hf ≫ toSpecZero 𝒜 =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _))) := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun x ↦ ?_
  simp only [fromOfGlobalSections, toBasicOpenOfGlobalSections, CommRingCat.ofHom_comp,
    Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc, basicOpenIsoSpec_inv_ι_assoc,
    awayι_toSpecZero, Iso.inv_comp_eq]
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_X,
    Scheme.openCoverOfIsOpenCover_f, Scheme.isoOfEq_hom_ι_assoc, ← morphismRestrict_ι_assoc]
  congr 1
  simp only [basicOpenIsoSpecAway, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← Iso.eq_inv_comp,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, ← HomogeneousLocalization.algebraMap_eq]
  congr 2
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ A,
    ← RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_assoc]

end ofGlobalSection

end AlgebraicGeometry.Proj
