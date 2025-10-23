/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.Algebra.Category.Ring.EqualizerPushout
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.Category.TopCat.EffectiveEpi

/-!
# Effective epimorphisms in the category of schemes

We prove that are effective epimorphisms in the category of schemes.

## Main results

Let `f : R ⟶ S` be a flat ring map with surjective `Spec.map f : Spec S ⟶ Spec R`.

* `AlgebraicGeometry.Flat.descSpec`: Given a morphism `e : Spec S ⟶ U` of schemes which
  coequalizes the two projections `(Spec S) ×[Spec R] (Spec S) ⟶ Spec S`, this constructs
  a unique morphism `Spec R ⟶ U` of schemes that `e` factors through.
* `AlgebraicGeometry.Flat.effectiveEpi_Spec_of_flat_of_surjective`: The map
  `Spec.map f : Spec S ⟶ Spec R` is an effective epimorphism in the category of schemes.

## Reference

* https://stacks.math.columbia.edu/tag/023Q

## TODO

* Generalize `effectiveEpi_Spec_of_flat_of_surjective` to quasi-compact coverings.

-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section AffineScheme

variable {X Y : AffineScheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]

/-- A flat surjective morphism is an effective epimorphism in the category of affine schemes. -/
lemma AffineScheme.effectiveEpiOfFlatOfSurjective : EffectiveEpi f := by
  apply effectiveEpiOfKernelPair f
  apply isColimitOfReflects AffineScheme.equivCommRingCat.functor
  apply (isColimitMapCoconeCoforkEquiv _ _).symm ?_
  apply Cofork.isColimitOfIsos (Cofork.ofπ _ pullback.condition) ?_ _
    (PreservesPullback.iso _ f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
  apply CommRingCat.Opposite.isColimitOfπPullbackOfFaithfullyFlat _
  simp only [AffineScheme.equivCommRingCat_functor_map]
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹_›, ‹_›⟩

end AffineScheme

namespace Flat

section Spec

variable {R S : CommRingCat.{u}} {f : R ⟶ S}
variable [Flat (Spec.map f)] [Surjective (Spec.map f)]
variable {U : Scheme.{u}} {e : Spec S ⟶ U}
  (h : pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e)

/-
Given
1. a flat ring homomorphism `f : R ⟶ S` in `CommRingCat` such that the induced morphism of schemes
  `Spec.map f : Spec S ⟶ Spec R` is surjective, and
2. any scheme `U` equipped with a morphism `e : Spec S ⟶ U` of schemes which coequalizes the two
  pullback projections of the self-pullback of `Spec.map f`, namely:
  `pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e`,
we construct a morphism `descSpec : Spec R ⟶ U` of schemes that `e : Spec S ⟶ U` factors through,
in three steps.
-/

/- **Step 1:**
We define `desc : (Spec R).carrier ⟶ U.carrier` to be the unique continuous map satisfying
`(Spec.map f).base ≫ desc = e.base`.
-/

/-- A preparation lemma for `base_factorization` below. -/
private lemma base_factorization_type {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    {W : Scheme.{u}} {e : X ⟶ W} (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃ (g : ↥Y → ↥W), ⇑e.base.hom = g ∘ ⇑f.base.hom := by
  let : RegularEpi (Scheme.forget.map f) := by
    have := (isSplitEpi_iff_surjective (Scheme.forget.map f)).mpr ‹Surjective f›.surj
    exact regularEpiOfEffectiveEpi (Scheme.forget.map f)
  refine ⟨_, types_comp _ _ ▸ Cofork.IsColimit.π_desc' this.isColimit _ ?_|>.symm⟩
  change pullback.fst _ _ ≫ Scheme.forget.map e = pullback.snd _ _ ≫ Scheme.forget.map e
  apply ((epi_iff_surjective _).mpr
    (Scheme.pullbackComparison_forget_surjective _ _)).left_cancellation
  simp only [← Category.assoc, pullbackComparison_comp_fst, ← Functor.map_comp, h,
    pullbackComparison_comp_snd]

/- Implementation note: `base_factorization` can be generalized to a (non-private) lemma for
quasi-compact coverings (rather than just quasi-compact maps) that are flat and surjective. It would
be useful in describing the underlying continuous map of a more general version of `descSpec`. -/

/-- For a flat surjective and quasi-compact morphism `f : X ⟶ Y` of schemes,
any morphism `e : X ⟶ W` of schemes satisfying `pullback.fst f f ≫ e = pullback.snd f f ≫ e`
factors through a unique *continuous map* on underlying topological spaces. -/
private lemma base_factorization {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
    [QuasiCompact f] {W : Scheme.{u}} {e : X ⟶ W}
    (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃! (g : Y.carrier ⟶ W.carrier), f.base ≫ g = e.base := by
  have {Z : TopCat} (g₁ g₂ : Z ⟶ X.carrier) (hg : g₁ ≫ f.base = g₂ ≫ f.base) :
      g₁ ≫ e.base = g₂ ≫ e.base := by
    apply TopCat.hom_ext
    apply ContinuousMap.coe_injective
    simp only [TopCat.hom_comp, ContinuousMap.coe_comp]
    rw [(base_factorization_type h).choose_spec, Function.comp_assoc]
    congr 1
    exact congrArg (fun g ↦ g.toFun) ((TopCat.hom_comp _ _).trans (congrArg (fun g ↦ g.hom) hg))
  exact ⟨(TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)).desc _ this,
    ⟨(TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)).fac _ this,
      fun g' hg' ↦ (TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)).uniq _
        this g' hg'⟩⟩

/-- The unique continuous map `(Spec R).carrier ⟶ U.carrier` such that
`(Spec.map f).base ≫ desc = e.base`.-/
local notation "desc" => Exists.choose (base_factorization h)

/- **Step 2:**
For each point `p : (Spec R).carrier`, we construct a diagram
```
      P  --- ιₛ ---> Spec S
    / |                 |  \
   /  f'         Spec.map f \
  /   ∨                 ∨    \
e'    W  --- ιᵣ ---> Spec R   e
  \   |                 |    /
   \ desc'            desc  /
    ↘ ∨                 ∨  ↙
      V  ---- ιᵤ -----> U
```
This diagram commutes in the following sense: Any triangle or square involving `desc` commutes as
topological spaces. All other triangles and squares commute as schemes.

Here, `V` denotes an affine open containing `desc p`, `W` denotes a basic open in `Spec R` mapping
into `V`, and `P` denotes the pullback of `W` with `Spec S`. The morphisms in the diagram are:
- `ιᵤ`, `ιᵣ`, `ιₛ` : the natural open immersions
- `f'` : the pullback projection to `W`
- `e'` : the restriction of `ιₛ ≫ e` to `V`
- `desc'` : the unique morphism of schemes satisfying `f' ≫ desc' = e'`
-/

variable {p : Spec R} (V : U.Opens)

private noncomputable def ιᵤ : V.toScheme ⟶ U := Scheme.Opens.ι V

private instance : IsOpenImmersion (ιᵤ V) := by rw [ιᵤ]; infer_instance

variable {V}

/-- A preparatory lemma, useful when dealing with `ιᵣ`, `ιₛ` and `f'`. -/
private lemma exists_basicOpen_preimage_opens {X Y : Scheme.{u}} [IsAffine X]
    {f : X.carrier ⟶ Y.carrier} {x : X} {V : Y.Opens} (hx : f x ∈ V.carrier) :
    ∃ (r : Γ(X, ⊤)), x ∈ X.basicOpen r ∧ X.basicOpen r ≤ ⇑f ⁻¹' V.carrier :=
  have := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (isBasis_basicOpen X) (V.mem_comap.mpr hx)).choose_spec
  ⟨this.left.choose,
    ⟨this.left.choose_spec.symm ▸ this.right.left, this.left.choose_spec.symm ▸ this.right.right⟩⟩

/-- An element in `Γ(Spec R, ⊤) (≅ R)` defining a basic open subset in `Spec R`. -/
private noncomputable def r (hp : desc p ∈ V) :
    Γ(Spec R, ⊤).carrier :=
  (exists_basicOpen_preimage_opens hp).choose

/-- The open immersion corresponding to `r : Γ(Spec R, ⊤) (≅ R)`. -/
private noncomputable def ιᵣ (hp : desc p ∈ V) :
    ((Spec R).basicOpen (r h hp)).toScheme ⟶ Spec R :=
  (Scheme.basicOpen (Spec R) (r h hp)).ι

/-- The pullback of `Spec.map f` along `ιᵣ`. -/
private noncomputable def f' (hp : desc p ∈ V) :
    pullback (ιᵣ h hp) (Spec.map f) ⟶ ((Spec R).basicOpen (r h hp)).toScheme :=
  pullback.fst (ιᵣ h hp) (Spec.map f)

/-- The pullback of `ιᵣ` along `Spec.map f`. -/
private noncomputable def ιₛ (hp : desc p ∈ V) :
    pullback (ιᵣ h hp) (Spec.map f) ⟶ Spec S :=
  pullback.snd (ιᵣ h hp) (Spec.map f)

/-- In the outer square, the (set-theoretic) image of the composition of the top and right vertical
maps is contained in the (set-theoretic) image of the bottom map. -/
private lemma range_ιₛ_e_subset_ιᵤ (hp : desc p ∈ V) :
    Set.range ⇑(ιₛ h hp ≫ e).base.hom ⊆ Set.range ⇑(ιᵤ V).base.hom := by
  nth_rw 1 [Hom.comp_base (ιₛ h hp) e, (base_factorization h).choose_spec.left.symm,
    ← Category.assoc, ← Hom.comp_base, ιₛ, ← pullback.condition, Hom.comp_base, ← f',
    Category.assoc]
  have : Surjective (f' h hp) := by rw [f']; infer_instance
  simp only [TopCat.hom_comp, ContinuousMap.coe_comp, Surjective.surj.range_comp, Set.range_comp]
  change _ '' ((Spec R).basicOpen (r h hp)).ι.opensRange.carrier ⊆ (Opens.ι V).opensRange.carrier
  simp only [Opens.opensRange_ι]
  exact Set.image_subset_iff.mpr (exists_basicOpen_preimage_opens hp).choose_spec.right

/-- The left vertical map in the outer square of the diagram. -/
private noncomputable def e' (hp : desc p ∈ V) :
    pullback (ιᵣ h hp) (Spec.map f) ⟶ Opens.toScheme V :=
  IsOpenImmersion.lift _ _ (range_ιₛ_e_subset_ιᵤ h hp)

/-- The two projections the self-pullback of `f'` followed by `ιₛ ≫ Spec.map f` are equal. -/
private lemma pullback_ιₛ_f (hp : desc p ∈ V) :
    (pullback.fst (f' h hp) (f' h hp) ≫ ιₛ h hp) ≫ Spec.map f =
    (pullback.snd (f' h hp) (f' h hp) ≫ ιₛ h hp) ≫ Spec.map f := by
  simp only [f', ιₛ, Category.assoc, ← pullback.condition]
  simp only [← Category.assoc, ← pullback.condition]

/-- The outer square is commutative. -/
private lemma e'_ιᵤ_eq_ιₛ_e (hp : desc p ∈ V) : e' h hp ≫ ιᵤ V = ιₛ h hp ≫ e :=
  IsOpenImmersion.lift_fac (ιᵤ V) (ιₛ h hp ≫ e) (range_ιₛ_e_subset_ιᵤ h hp)

/-- A regular epimorphism structure on `AffineScheme.ofHom (f' h hp)`. -/
private noncomputable instance (hp : desc p ∈ V) : RegularEpi (AffineScheme.ofHom (f' h hp)) :=
  have := @AffineScheme.effectiveEpiOfFlatOfSurjective _ _ (AffineScheme.ofHom (f' h hp))
    (by simp only [f', AffineScheme.ofHom]; infer_instance)
    (by simp only [f', AffineScheme.ofHom]; infer_instance)
  regularEpiOfEffectiveEpi (AffineScheme.ofHom (f' h hp))

/-- A condition required to define `desc`. -/
private lemma e'_coeq_pullback_f' (hp : desc p ∈ V) [hV : IsAffine V] :
    pullback.fst (AffineScheme.ofHom (f' h hp)) (AffineScheme.ofHom (f' h hp)) ≫
      AffineScheme.ofHom (e' h hp) =
    pullback.snd (AffineScheme.ofHom (f' h hp)) (AffineScheme.ofHom (f' h hp)) ≫
      AffineScheme.ofHom (e' h hp) := by
  rw [ObjectProperty.FullSubcategory.comp_def, ObjectProperty.FullSubcategory.comp_def,
    ← AffineScheme.forgetToScheme_map (pullback.fst (AffineScheme.ofHom (f' h hp)) _),
    ← AffineScheme.forgetToScheme_map (pullback.snd (AffineScheme.ofHom (f' h hp)) _),
    ← pullbackComparison_comp_fst, ← pullbackComparison_comp_snd,
    Category.assoc, Category.assoc]
  congr 1
  simp only [AffineScheme.forgetToScheme_map, AffineScheme.ofHom]
  apply (inferInstance : Mono (ιᵤ V)).right_cancellation
  simp only [Category.assoc, e'_ιᵤ_eq_ιₛ_e]
  simp only [← Category.assoc, ← Category.assoc]
  nth_rw 1 [ ← pullback.lift_fst _ _ (pullback_ιₛ_f h hp).symm,
    ← pullback.lift_snd _ _ (pullback_ιₛ_f h hp).symm]
  exact congrArg (_ ≫ ·) h.symm

/-- The left vertical map in the bottom square. -/
private noncomputable def desc' (hp : desc p ∈ V) [hV : IsAffine V] :
    ((Spec R).basicOpen (r h hp)).toScheme ⟶ V.toScheme :=
  (RegularEpi.desc' (AffineScheme.ofHom (f' h hp)) (AffineScheme.ofHom (e' h hp))
    (e'_coeq_pullback_f' h hp)).val

/-- The left triangle commutes. -/
private lemma desc'_comp (hp : desc p ∈ V) [hV : IsAffine V] :
    f' h hp ≫ desc' h hp = e' h hp :=
  (RegularEpi.desc' _ (AffineScheme.ofHom (e' h hp)) (e'_coeq_pullback_f' h hp)).property

/- **Step 3:**
We show that the morphisms `desc'` of schemes obtained in **Step 2** for each `p : (Spec R).carrier`
glue together to define a unique morphism `descSpec : Spec R ⟶ U` of schemes satisfying
`Spec.map f ≫ descSpec = e`.
-/

/-- An open cover of `Spec R` by basic open subsets that maps to affine open subsets in `U` under
`desc : (Spec R).carrier ⟶ U.carrier`. -/
private noncomputable def coverR : (Spec R).OpenCover := by
  apply Scheme.openCoverOfIsOpenCover (Spec R) <| fun p ↦ ((Spec R).basicOpen
    (exists_basicOpen_preimage_opens (U.local_affine (desc p)).choose.property).choose)
  apply TopologicalSpace.Opens.coe_eq_univ.mp (Set.eq_univ_iff_forall.mpr ?_)
  intro p
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨p,
    (exists_basicOpen_preimage_opens (U.local_affine (desc p)).choose.property).choose_spec.left⟩

open CategoryTheory.IsPullback in
/-- Two different expressions of the canonical map `P ×[Spec R] P_q ⟶ W ×[Spec R] W_q`, where
`P_q` and `W_q` denote `P` and `W` applied to another point `q : Spec R` and a neighborhood `V'`. -/
private lemma pullback_lift_paste_horiz
    (hp : desc p ∈ V) {V' : U.Opens} {q : Spec R} (hq : desc q ∈ V') :
    pullback.lift
      (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hp)
      (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hq)
      (by simp [pullback.condition]) =
    (paste_horiz (of_hasPullback _ _)
      (paste_vert (of_hasPullback _ _) (of_hasPullback _ _))).isoPullback.inv ≫
    pullback.fst (pullback.snd _ _ ≫ pullback.snd _ _) _ ≫ pullback.snd _ _ := by
  apply (@cancel_mono _ _ _ _ _ (pullback.fst (ιᵣ h hp) (ιᵣ h hq))
    (by simp only [ιᵣ]; infer_instance)).mp
  simp only [pullback.lift_fst, Category.assoc, ← pullback.condition]
  rw [← Category.assoc (pullback.fst _ _) _ _, ← Category.assoc, isoPullback_inv_fst]

/-- The two pullback projections from `W ×[Spec R] W_q` become equal after composed with the scheme
map to `U`, where `W_q` denotes `W` applied to another point `q : Spec R`. -/
private lemma desc'_cocycle_condition (hp : desc p ∈ V) [hV : IsAffine V]
    {V' : U.Opens} {q : Spec R} (hq : desc q ∈ V') [hV' : IsAffine V'] :
    pullback.fst (ιᵣ h hp) (ιᵣ h hq) ≫ desc' h hp ≫ ιᵤ V =
      pullback.snd (ιᵣ h hp) (ιᵣ h hq) ≫ desc' h hq ≫ ιᵤ V' := by
  apply (@cancel_epi _ _ _ _ _ (pullback.lift
    (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hp)
    (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hq)
    (by simp [pullback.condition])) ?_).mp ?_
  · rw [pullback_lift_paste_horiz h hp hq]
    simp only [ιᵣ, f', epi_of_flat_of_surjective]
  · simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    simp only [Category.assoc, desc'_comp, e', IsOpenImmersion.lift_fac]
    rw [← Category.assoc, ← Category.assoc, ← pullback.lift_fst (f := Spec.map f) (g := Spec.map f)
      (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hp)
      (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hq)
      (by simp [ιₛ, f', ← pullback.condition])]
    nth_rw 2 [← pullback.lift_snd (f := Spec.map f) (g := Spec.map f)
      (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hp)
      (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hq)
      (by simp [ιₛ, f', ← pullback.condition])]
    simp only [Category.assoc]
    congr 1

/-- The fpqc descent morphism `Spec R ⟶ U` of schemes obtained from a morphism `e : Spec S ⟶ U` of
schemes which coequalizes the two projections of the self-pullback of `Spec S ⟶ Spec R`. -/
noncomputable def descSpec : Spec R ⟶ U :=
  (coverR h).glueMorphisms
    (fun x ↦ desc' h (U.local_affine (desc x)).choose.property ≫
      ιᵤ (U.local_affine (desc x)).choose.obj)
    (fun x y ↦ desc'_cocycle_condition h
      (U.local_affine ((base_factorization h).choose x)).choose.property
      (U.local_affine ((base_factorization h).choose y)).choose.property)

/-- `descSpec` composed with `Spec.map f` recovers the original morphism `e`. -/
lemma descSpec_comp : Spec.map f ≫ descSpec h = e := by
  apply Cover.hom_ext (Precoverage.ZeroHypercover.pullback₂ (Spec.map f) (coverR h))
  intro p
  simp only [Precoverage.ZeroHypercover.pullback₂, PreZeroHypercover.pullback₂]
  change _ = ιₛ h (U.local_affine ((base_factorization h).choose p)).choose.property ≫ e
  rw [← e'_ιᵤ_eq_ιₛ_e, ← desc'_comp, ← Category.assoc, ← pullback.condition, Category.assoc]
  exact congrArg (_ ≫ ·) (Cover.ι_glueMorphisms (coverR h) _ _ p)

/-- `descSpec` is the unique morphism `Spec R ⟶ U` through which `e` factors. -/
lemma descSpec_unique (t : Spec R ⟶ U) (ht : Spec.map f ≫ t = e) : t = descSpec h := by
  apply Cover.hom_ext (coverR h)
  intro p
  have : Epi (pullback.snd (Spec.map f) ((coverR h).f p)) := epi_of_flat_of_surjective _
  apply (cancel_epi (pullback.snd (Spec.map f) ((coverR h).f p))).mp
  rw [← Category.assoc, ← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc,
    ht, descSpec_comp h]

end Spec

section Scheme

/-- The cofork formed by the two projections `(Spec S) ×[Spec R] (Spec S) ⟶ Spec S` followed by
`Spec S ⟶ Spec R` is a colimit, when `f : R ⟶ S` is a flat ring map with surjective
`Spec.map f : Spec S ⟶ Spec R`. -/
noncomputable def isColimitCoforkSpecPullback {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.Flat) (hs : Surjective (Spec.map f)) :
    IsColimit (Cofork.ofπ (Spec.map f) pullback.condition) := by
  apply Cofork.IsColimit.mk'
  have : Flat (Spec.map f) := HasRingHomProperty.Spec_iff.mpr hf
  intro s
  exact ⟨descSpec s.condition, ⟨by simp [descSpec_comp], fun ht ↦ descSpec_unique s.condition _ ht⟩⟩

/-- `Spec.map f` is an effective epimorphism in the category of schemes, when `f : R ⟶ S` is a flat
ring map with surjective `Spec.map f : Spec S ⟶ Spec R`. -/
@[stacks 023Q]
lemma effectiveEpi_Spec_of_flat_of_surjective {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.Flat) (hs : Surjective (Spec.map f)) : EffectiveEpi (Spec.map f) :=
  effectiveEpiOfKernelPair _ (isColimitCoforkSpecPullback f hf hs)

end Scheme

end Flat

end AlgebraicGeometry
