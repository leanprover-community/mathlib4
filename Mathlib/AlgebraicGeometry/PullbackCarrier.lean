/-
Copyright (c) 2024 Qi Ge, Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Ge, Christian Merten, Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.LinearAlgebra
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Underlying topological space of fibre product of schemes

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes. In this file we describe the underlying
topological space of `pullback f g`, i.e. the fiber product `X ×[S] Y`.

## Main results

- `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: The bijective correspondence between the points
  of `X ×[S] Y` and pairs `(z, p)` of triples `z = (x, y, s)` with `f x = s = g y` and
  prime ideals `q` of `κ(x) ⊗[κ(s)] κ(y)`.
- `AlgebraicGeometry.Scheme.Pullback.exists_preimage`: For every triple `(x, y, s)` with
  `f x = s = g y`, there exists `z : X ×[S] Y` lying above `x` and `y`.

We also give the ranges of `pullback.fst`, `pullback.snd` and `pullback.map`.

-/

open CategoryTheory Limits TopologicalSpace IsLocalRing TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- A `Triplet` over `f : X ⟶ S` and `g : Y ⟶ S` is a triple of points `x : X`, `y : Y`,
`s : S` such that `f x = s = f y`. -/
structure Triplet {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  /-- The point of `X`. -/
  x : X
  /-- The point of `Y`. -/
  y : Y
  /-- The point of `S` below `x` and `y`. -/
  s : S
  hx : f.base x = s
  hy : g.base y = s

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Triplet

@[ext]
protected lemma ext {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y) : t₁ = t₂ := by
  cases t₁; cases t₂; simp; aesop

/-- Make a triplet from `x : X` and `y : Y` such that `f x = g y`. -/
@[simps]
def mk' (x : X) (y : Y) (h : f.base x = g.base y) : Triplet f g where
  x := x
  y := y
  s := g.base y
  hx := h
  hy := rfl

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is `κ(x) ⊗[κ(s)] κ(y)`. -/
def tensor (T : Triplet f g) : CommRingCat :=
  pushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)

instance (T : Triplet f g) : Nontrivial T.tensor :=
  CommRingCat.nontrivial_of_isPushout_of_isField (Field.toIsField _)
    (IsPushout.of_hasPushout _ _)

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is the
canonical map `κ(x) ⟶ κ(x) ⊗[κ(s)] κ(y)`. -/
def tensorInl (T : Triplet f g) : X.residueField T.x ⟶ T.tensor := pushout.inl _ _

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is the
canonical map `κ(y) ⟶ κ(x) ⊗[κ(s)] κ(y)`. -/
def tensorInr (T : Triplet f g) : Y.residueField T.y ⟶ T.tensor := pushout.inr _ _

lemma Spec_map_tensor_isPullback (T : Triplet f g) : CategoryTheory.IsPullback
    (Spec.map T.tensorInl) (Spec.map T.tensorInr)
        (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
          (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
  isPullback_Spec_map_pushout _ _

section Congr

/-- Given propositionally equal triplets `T₁` and `T₂` over `f` and `g`, the corresponding
`T₁.tensor` and `T₂.tensor` are isomorphic. -/
def tensorCongr {T₁ T₂ : Triplet f g} (e : T₁ = T₂) :
    T₁.tensor ≅ T₂.tensor :=
  eqToIso (by subst e; rfl)

@[simp]
lemma tensorCongr_refl {x : Triplet f g} :
    tensorCongr (refl x) = Iso.refl _ := rfl

@[simp]
lemma tensorCongr_symm {x y : Triplet f g} (e : x = y) :
    (tensorCongr e).symm = tensorCongr e.symm := rfl

@[simp]
lemma tensorCongr_inv {x y : Triplet f g} (e : x = y) :
    (tensorCongr e).inv = (tensorCongr e.symm).hom := rfl

@[simp]
lemma tensorCongr_trans {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    tensorCongr e ≪≫ tensorCongr e' =
      tensorCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
lemma tensorCongr_trans_hom {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    (tensorCongr e).hom ≫ (tensorCongr e').hom =
      (tensorCongr (e.trans e')).hom := by
  subst e e'
  rfl

end Congr

variable (T : Triplet f g)

lemma Spec_map_tensorInl_fromSpecResidueField :
    (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x) ≫ f =
      (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) ≫ g := by
  simp only [residueFieldCongr_inv, Category.assoc, tensorInl, tensorInr,
    ← Hom.Spec_map_residueFieldMap_fromSpecResidueField]
  rw [← residueFieldCongr_fromSpecResidueField T.hx.symm,
    ← residueFieldCongr_fromSpecResidueField T.hy.symm]
  simp only [← Category.assoc, ← Spec.map_comp, pushout.condition]

/-- Given `x : X`, `y : Y` and `s : S` such that `f x = s = g y`,
this is `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×ₛ Y`. -/
def SpecTensorTo : Spec T.tensor ⟶ pullback f g :=
  pullback.lift (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x)
    (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y)
    (Spec_map_tensorInl_fromSpecResidueField _)

@[simp]
lemma specTensorTo_base_fst (p : Spec T.tensor) :
    (pullback.fst f g).base (T.SpecTensorTo.base p) = T.x := by
  simp only [SpecTensorTo]
  rw [← Scheme.comp_base_apply]
  simp

@[simp]
lemma specTensorTo_base_snd (p : Spec T.tensor) :
    (pullback.snd f g).base (T.SpecTensorTo.base p) = T.y := by
  simp only [SpecTensorTo]
  rw [← Scheme.comp_base_apply]
  simp

@[reassoc (attr := simp)]
lemma specTensorTo_fst :
    T.SpecTensorTo ≫ pullback.fst f g = Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma specTensorTo_snd :
    T.SpecTensorTo ≫ pullback.snd f g = Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y :=
  pullback.lift_snd _ _ _

/-- Given `t : X ×[S] Y`, it maps to `X` and `Y` with same image in `S`, yielding a
`Triplet f g`. -/
@[simps]
def ofPoint (t : ↑(pullback f g)) : Triplet f g :=
  ⟨(pullback.fst f g).base t, (pullback.snd f g).base t, _, rfl,
    congr((Scheme.Hom.toLRSHom $(pullback.condition (f := f) (g := g))).base t).symm⟩

@[simp]
lemma ofPoint_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    ofPoint (T.SpecTensorTo.base p) = T := by
  ext <;> simp

end Triplet

lemma residueFieldCongr_inv_residueFieldMap_ofPoint (t : ↑(pullback f g)) :
    ((S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ f.residueFieldMap (Triplet.ofPoint t).x) ≫
      (pullback.fst f g).residueFieldMap t = ((S.residueFieldCongr (Triplet.ofPoint t).hy).inv ≫
          g.residueFieldMap (Triplet.ofPoint t).y) ≫ (pullback.snd f g).residueFieldMap t := by
  simp [← residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr pullback.condition]

/-- Given `t : X ×[S] Y` with projections to `X`, `Y` and `S` denoted by `x`, `y` and `s`
respectively, this is the canonical map `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)`. -/
def ofPointTensor (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).tensor ⟶ (pullback f g).residueField t :=
  pushout.desc
    ((pullback.fst f g).residueFieldMap t)
    ((pullback.snd f g).residueFieldMap t)
    (residueFieldCongr_inv_residueFieldMap_ofPoint t)

@[reassoc]
lemma ofPointTensor_SpecTensorTo (t : ↑(pullback f g)) :
    Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo =
      (pullback f g).fromSpecResidueField t := by
  apply pullback.hom_ext
  · rw [← Scheme.Hom.Spec_map_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_fst, Triplet.ofPoint_x]
    rw [← pushout.inl_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t), Spec.map_comp]
    rfl
  · rw [← Scheme.Hom.Spec_map_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_snd, Triplet.ofPoint_y]
    rw [← pushout.inr_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t), Spec.map_comp]
    rfl

/-- If `t` is a point in `X ×[S] Y` above `(x, y, s)`, then this is the image of the unique
point of `Spec κ(s)` in `Spec κ(x) ⊗[κ(s)] κ(y)`. -/
def SpecOfPoint (t : ↑(pullback f g)) : Spec (Triplet.ofPoint t).tensor :=
    (Spec.map (ofPointTensor t)).base (⊥ : PrimeSpectrum _)

@[simp]
lemma SpecTensorTo_SpecOfPoint (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).SpecTensorTo.base (SpecOfPoint t) = t := by
  simp [SpecOfPoint, ← Scheme.comp_base_apply, ofPointTensor_SpecTensorTo]

@[reassoc (attr := simp)]
lemma tensorCongr_SpecTensorTo {T T' : Triplet f g} (h : T = T') :
    Spec.map (Triplet.tensorCongr h).hom ≫ T.SpecTensorTo = T'.SpecTensorTo := by
  subst h
  simp only [Triplet.tensorCongr_refl, Iso.refl_hom, Spec.map_id, Category.id_comp]

lemma Triplet.Spec_ofPointTensor_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    Spec.map (Hom.residueFieldMap T.SpecTensorTo p) ≫
      Spec.map (ofPointTensor (T.SpecTensorTo.base p)) ≫
      Spec.map (tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom =
    (Spec T.tensor).fromSpecResidueField p := by
  apply T.Spec_map_tensor_isPullback.hom_ext
  · rw [← cancel_mono <| X.fromSpecResidueField T.x]
    simp_rw [Category.assoc, ← T.specTensorTo_fst, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.Spec_map_residueFieldMap_fromSpecResidueField_assoc, ofPointTensor_SpecTensorTo_assoc]
  · rw [← cancel_mono <| Y.fromSpecResidueField T.y]
    simp_rw [Category.assoc, ← T.specTensorTo_snd, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.Spec_map_residueFieldMap_fromSpecResidueField_assoc, ofPointTensor_SpecTensorTo_assoc]

/-- A helper lemma to work with `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`. -/
lemma carrierEquiv_eq_iff {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔ ∃ e : T₁.1 = T₂.1, (Spec.map (Triplet.tensorCongr e).inv).base T₁.2 = T₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨T, _⟩ := T₁
    obtain ⟨T', _⟩ := T₂
    rintro ⟨rfl : T = T', e⟩
    simpa [e]

/--
The points of the underlying topological space of `X ×[S] Y` bijectively correspond to
pairs of triples `x : X`, `y : Y`, `s : S` with `f x = s = f y` and prime ideals of
`κ(x) ⊗[κ(s)] κ(y)`.
-/
def carrierEquiv : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  toFun t := ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo.base T.2
  left_inv := SpecTensorTo_SpecOfPoint
  right_inv := by
    intro ⟨T, p⟩
    apply carrierEquiv_eq_iff.mpr
    use T.ofPoint_SpecTensorTo p
    have : (Spec.map (Hom.residueFieldMap T.SpecTensorTo p)).base (⊥ : PrimeSpectrum _) =
        (⊥ : PrimeSpectrum _) :=
      (PrimeSpectrum.instUnique).uniq _
    simp only [SpecOfPoint, Triplet.tensorCongr_inv, ← this, ← Scheme.comp_base_apply,
      ← Scheme.comp_base_apply]
    simp [Triplet.Spec_ofPointTensor_SpecTensorTo]

@[simp]
lemma carrierEquiv_symm_fst (T : Triplet f g) (p : Spec T.tensor) :
    (pullback.fst f g).base (carrierEquiv.symm ⟨T, p⟩) = T.x := by
  simp [carrierEquiv]

@[simp]
lemma carrierEquiv_symm_snd (T : Triplet f g) (p : Spec T.tensor) :
    (pullback.snd f g).base (carrierEquiv.symm ⟨T, p⟩) = T.y := by
  simp [carrierEquiv]

/-- Given a triple `(x, y, s)` with `f x = s = f y` there exists `t : X ×[S] Y` above
`x` and `ỳ`. For the unpacked version without `Triplet`, see
`AlgebraicGeometry.Scheme.Pullback.exists_preimage`. -/
lemma Triplet.exists_preimage (T : Triplet f g) :
    ∃ t : ↑(pullback f g),
    (pullback.fst f g).base t = T.x ∧ (pullback.snd f g).base t = T.y :=
  ⟨carrierEquiv.symm ⟨T, Nonempty.some inferInstance⟩, by simp⟩

/--
If `f : X ⟶ S` and `g : Y ⟶ S` are morphisms of schemes and `x : X` and `y : Y` are points such
that `f x = g y`, then there exists `z : X ×[S] Y` lying above `x` and `y`.

In other words, the map from the underlying topological space of `X ×[S] Y` to the fiber product
of the underlying topological spaces of `X` and `Y` over `S` is surjective.
-/
lemma exists_preimage_pullback (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ z : ↑(pullback f g),
    (pullback.fst f g).base z = x ∧ (pullback.snd f g).base z = y :=
  (Pullback.Triplet.mk' x y h).exists_preimage

/-- The comparison map for pullbacks under the forgetful functor `Scheme ⥤ Type u` is surjective. -/
lemma forget_comparison_surjective {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Function.Surjective (pullbackComparison forget f g) := by
  apply (Function.Surjective.of_comp_iff'
    ((PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback _ _)).bijective) _).mp
  intro ⟨⟨x, y⟩, hb⟩
  obtain ⟨z, ⟨hz, hz'⟩⟩ := exists_preimage_pullback x y hb
  use z
  ext
  · exact hz.symm ▸ congrFun (pullbackComparison_comp_fst forget f g) z
  · exact hz'.symm ▸ congrFun (pullbackComparison_comp_snd forget f g) z

lemma _root_.AlgebraicGeometry.Scheme.isEmpty_pullback_iff {f : X ⟶ S} {g : Y ⟶ S} :
    IsEmpty ↑(Limits.pullback f g) ↔ Disjoint (Set.range f.base) (Set.range g.base) := by
  refine ⟨?_, Scheme.isEmpty_pullback f g⟩
  rw [← not_nonempty_iff, Set.disjoint_iff_forall_ne]
  contrapose!
  rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, e⟩
  obtain ⟨z, -⟩ := exists_preimage_pullback x y e
  exact ⟨z⟩

variable (f g)

lemma range_fst : Set.range (pullback.fst f g).base = f.base ⁻¹' Set.range g.base := by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.comp_base_apply, pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' x y hy.symm)
    use a, ha.left

lemma range_snd : Set.range (pullback.snd f g).base = g.base ⁻¹' Set.range f.base := by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.comp_base_apply, ← pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' y x hy)
    use a, ha.right

lemma range_fst_comp :
    Set.range (pullback.fst f g ≫ f).base = Set.range f.base ∩ Set.range g.base := by
  simp [Set.range_comp, range_fst, Set.image_preimage_eq_range_inter]

lemma range_snd_comp :
    Set.range (pullback.snd f g ≫ g).base = Set.range f.base ∩ Set.range g.base := by
  rw [← pullback.condition, range_fst_comp]

lemma range_map {X' Y' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂).base =
      (pullback.fst f' g').base ⁻¹' Set.range i₁.base ∩
        (pullback.snd f' g').base ⁻¹' Set.range i₂.base := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · use (pullback.fst f g).base t
      rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply]
      simp
    · use (pullback.snd f g).base t
      rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply]
      simp
  · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let T₁ : Triplet (pullback.fst f' g') i₁ := Triplet.mk' z x hx.symm
    obtain ⟨w₁, hw₁⟩ := T₁.exists_preimage
    let T₂ : Triplet (pullback.snd f' g') i₂ := Triplet.mk' z y hy.symm
    obtain ⟨w₂, hw₂⟩ := T₂.exists_preimage
    let T : Triplet (pullback.fst (pullback.fst f' g') i₁) (pullback.fst (pullback.snd f' g') i₂) :=
      Triplet.mk' w₁ w₂ <| by simp [hw₁.left, hw₂.left, T₁, T₂]
    obtain ⟨t, _, ht₂⟩ := T.exists_preimage
    use (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).hom.base t
    rw [pullback_map_eq_pullbackFstFstIso_inv, ← Scheme.comp_base_apply, Iso.hom_inv_id_assoc]
    simp [ht₂, T, hw₂.left, T₂]

end Pullback

instance isJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) :
    IsJointlySurjectivePreserving P where
  exists_preimage_fst_triplet_of_prop {X Y S} f g _ hg x y hxy := by
    obtain ⟨a, b, h⟩ := Pullback.exists_preimage_pullback x y hxy
    use a

end Scheme

namespace Surjective

instance : MorphismProperty.IsStableUnderBaseChange @Surjective := by
  refine .mk' ?_
  introv hg
  simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
  rw [hg, Set.preimage_univ]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective g] :
    Surjective (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f] :
    Surjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

end AlgebraicGeometry.Surjective
