-- `Mathlib/AlgebraicGeometry/PullbackCarrier
import Mathlib.ValuativeCriterion.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

open CategoryTheory CategoryTheory.Limits TopologicalSpace LocalRing
open TensorProduct

noncomputable section
set_option linter.longLine false
namespace AlgebraicGeometry.Scheme.Pullback

universe u

section TOBEMOVED

instance {R M N : Type*} [Field R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Nontrivial M] [Nontrivial N] : Nontrivial (M ⊗[R] N) := by
  rw [← rank_pos_iff_nontrivial (R := R), rank_tensorProduct]
  simp [rank_pos]

lemma tensorProduct_nontrivial_of_isField {R M N : Type*} [CommRing R]
    (h : IsField R)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Nontrivial M] [Nontrivial N] : Nontrivial (M ⊗[R] N) := by
  letI : Field R := h.toField
  infer_instance

-- move me to `Mathlib\Algebra\Category\Ring\Constructions.lean`
lemma CommRingCat.nontrivial_pushout_of_isField {A B C : CommRingCat.{u}}
    (hA : IsField A) (f : A ⟶ B) (g : A ⟶ C)
    [Nontrivial B] [Nontrivial C] : Nontrivial ↑(pushout f g) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  let e : pushout f g ≅ .of (B ⊗[A] C) :=
    colimit.isoColimitCocone ⟨CommRingCat.pushoutCocone A B C,
      CommRingCat.pushoutCoconeIsColimit A B C⟩
  have : Nontrivial (B ⊗[A] C) := tensorProduct_nontrivial_of_isField hA
  let e' : (pushout f g : CommRingCat) ≃ B ⊗[A] C :=
    e.commRingCatIsoToRingEquiv.toEquiv
  apply e'.nontrivial

instance {A : CommRingCat} [Nontrivial A] : Nonempty (Spec A) :=
  inferInstanceAs <| Nonempty (PrimeSpectrum A)

end TOBEMOVED

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

structure Triplet where
  x : X
  y : Y
  s : S
  hx : f.1.base x = s
  hy : g.1.base y = s

variable {f g}

namespace Triplet

@[ext]
protected lemma ext {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y) : t₁ = t₂ := by
  cases t₁; cases t₂; aesop

/-- Make a triplet from `x : X` and `y : Y` such that `f x = g y`. -/
@[simps]
def mk' (x : X) (y : Y) (h : f.val.base x = g.val.base y) : Triplet f g where
  x := x
  y := y
  s := g.val.base y
  hx := h
  hy := rfl

variable (T : Triplet f g)

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is `κ(x) ⊗[κ(s)] κ(y)`. -/
def tensor : CommRingCat :=
  pushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)

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
lemma tensorCongr_trans' {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    (tensorCongr e).hom ≫ (tensorCongr e').hom =
      (tensorCongr (e.trans e')).hom := by
  subst e e'
  rfl

@[reassoc]
lemma Scheme.toResidueField_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.toResidueField x ≫ (X.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.toResidueField y := by
  subst h
  simp

lemma SpecTensorTo_comm :
    (Spec.map
      (pushout.inl ((S.residueFieldCongr T.hx).inv ≫ Hom.residueFieldMap f T.x)
        ((S.residueFieldCongr T.hy).inv ≫ Hom.residueFieldMap g T.y)) ≫
          X.fromSpecResidueField T.x) ≫ f
    = (Spec.map
      (pushout.inr ((S.residueFieldCongr _).inv ≫ Hom.residueFieldMap f T.x)
        ((S.residueFieldCongr _).inv ≫ Hom.residueFieldMap g T.y)) ≫
          Y.fromSpecResidueField T.y) ≫ g := by
  simp [Spec.map_comp]

  have h₁ : X.fromSpecResidueField T.x
      ≫ f
        = Spec.map (f.residueFieldMap T.x)
          ≫ Spec.map (S.residueFieldCongr T.hx).inv
            ≫ S.fromSpecResidueField T.s := by
    simp only [residueFieldCongr_inv, residueFieldCongr_fromSpecResidueField]
    exact Eq.symm (Hom.residueFieldMap_fromSpecResidueField f T.x)

  have h₂ : Y.fromSpecResidueField T.y
      ≫ g
        = Spec.map (g.residueFieldMap T.y)
          ≫ Spec.map (S.residueFieldCongr T.hy).inv
            ≫ S.fromSpecResidueField T.s := by
    simp only [residueFieldCongr_inv, residueFieldCongr_fromSpecResidueField]
    exact Eq.symm (Hom.residueFieldMap_fromSpecResidueField g T.y)

  rw [h₁, h₂]
  simp only [← reassoc_of% Spec.map_comp]

  apply congrFun (congrArg CategoryStruct.comp _)
  apply Spec.map_inj.mpr
  simp only [residueFieldCongr_inv]
  exact pushout.condition

/-- Given `x : X` and `y : Y` such that `f x = s = g y`,
this is `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×ₛ Y`. -/
def SpecTensorTo :
    Spec T.tensor ⟶ pullback f g :=
  pullback.lift
    (Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField T.x)
    (Spec.map (pushout.inr _ _) ≫ Y.fromSpecResidueField T.y)
    (SpecTensorTo_comm _)

@[simp]
lemma specTensorTo_val_base_fst (p : Spec (T.tensor)) :
    (pullback.fst f g).val.base (T.SpecTensorTo.val.base p) = T.x := by
  simp only [SpecTensorTo, residueFieldCongr_inv]
  rw [← Scheme.comp_val_base_apply]
  simp

@[simp]
lemma specTensorTo_val_base_snd (p : Spec (T.tensor)) :
    (pullback.snd f g).val.base (T.SpecTensorTo.val.base p) = T.y := by
  simp only [SpecTensorTo, residueFieldCongr_inv]
  rw [← Scheme.comp_val_base_apply]
  simp

/-- Given `t : X ×ₛ Y`, it maps to `X` and `Y` with same image in `S`, yielding a `Triplet f g`. -/
def ofPoint (t : ↑(pullback f g)) : Triplet f g :=
  ⟨(pullback.fst f g).1.base t, (pullback.snd f g).1.base t, _, rfl,
    congr((LocallyRingedSpace.Hom.val $(pullback.condition (f := f) (g := g))).base t).symm⟩

end Triplet

lemma ofPointTensor_comm (t : ↑(pullback f g)) :
    ((S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ Hom.residueFieldMap f (Triplet.ofPoint t).x)
      ≫ Hom.residueFieldMap (pullback.fst f g) t
        = ((S.residueFieldCongr (Triplet.ofPoint t).hy).inv ≫ Hom.residueFieldMap g (Triplet.ofPoint t).y)
          ≫ Hom.residueFieldMap (pullback.snd f g) t := by
  simp only [Category.assoc]
  change (S.residueFieldCongr _).inv
    ≫ Hom.residueFieldMap f ((pullback.fst f g).val.base t)
      ≫ Hom.residueFieldMap (pullback.fst f g) t
        = (S.residueFieldCongr _).inv
          ≫ Hom.residueFieldMap g ((pullback.snd f g).val.base t)
            ≫ Hom.residueFieldMap (pullback.snd f g) t

  simp only [← residueFieldMap_comp]
  apply Scheme.Hom.residueFieldMap_congr pullback.condition

/-- The ring map from tensor to residue field in the pullback. -/
def ofPointTensor (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).tensor ⟶ (pullback f g).residueField t :=
  pushout.desc
    ((pullback.fst f g).residueFieldMap t)
    ((pullback.snd f g).residueFieldMap t)
    (ofPointTensor_comm t)

lemma ofPointtensor_SpectensorTo (t : ↑(pullback f g)) :
    Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo =
      (pullback f g).fromSpecResidueField t := by
  apply pullback.hom_ext
  · rw [← Scheme.Hom.residueFieldMap_fromSpecResidueField]
    have h : (Triplet.ofPoint t).SpecTensorTo ≫ pullback.fst f g
        = Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField (Triplet.ofPoint t).x :=
      pullback.lift_fst _ _ (Triplet.ofPoint t).SpecTensorTo_comm
    simp only [Category.assoc]
    rw [h]
    rw [← pushout.inl_desc _ _ (ofPointTensor_comm t)]
    simp only [Spec.map_comp]
    rfl
  · rw [← Scheme.Hom.residueFieldMap_fromSpecResidueField]
    have h : (Triplet.ofPoint t).SpecTensorTo ≫ pullback.snd f g
        = Spec.map (pushout.inr _ _) ≫ Y.fromSpecResidueField (Triplet.ofPoint t).y :=
      pullback.lift_snd _ _ (Triplet.ofPoint t).SpecTensorTo_comm
    simp only [Category.assoc]
    rw [h]
    rw [← pushout.inr_desc _ _ (ofPointTensor_comm t)]
    simp only [Spec.map_comp]
    rfl

def SpecOfPoint (t : ↑(pullback f g)) : Spec (Triplet.ofPoint t).tensor :=
    PrimeSpectrum.comap (ofPointTensor t) ⊥

lemma SpecTensorTo_SpecOfPoint (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).SpecTensorTo.1.base (SpecOfPoint t) = t := by
  rw [SpecOfPoint]
  have : (Triplet.ofPoint t).SpecTensorTo.val.base ((PrimeSpectrum.comap (ofPointTensor t)) ⊥) =
    ((Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo)).val.base _ := rfl
  rw [this]
  rw [ofPointtensor_SpectensorTo]
  exact fromSpecResidueField_apply t _

lemma Triplet.ofPoint_SpectensorTo (T : Triplet f g) (p : Spec T.tensor) :
    ofPoint (T.SpecTensorTo.val.base p) = T := by
  ext
  · change (T.SpecTensorTo ≫ pullback.fst f g).val.base p = T.x
    have : T.SpecTensorTo ≫ pullback.fst f g = Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField T.x := pullback.lift_fst _ _ _
    rw [this]
    exact fromSpecResidueField_apply T.x _
  · change (T.SpecTensorTo ≫ pullback.snd f g).val.base p = T.y
    have : T.SpecTensorTo ≫ pullback.snd f g = Spec.map (pushout.inr _ _) ≫ Y.fromSpecResidueField T.y := pullback.lift_snd _ _ _
    rw [this]
    exact fromSpecResidueField_apply T.y _

@[reassoc (attr := simp)]
lemma tensorCongr_SpecTensorTo {T T' : Triplet f g} (h : T = T') :
    Spec.map (Triplet.tensorCongr h).hom ≫ T.SpecTensorTo = T'.SpecTensorTo := by
  subst h
  simp only [Triplet.tensorCongr_refl, Iso.refl_hom, Spec.map_id, Category.id_comp]

lemma isPullback_Spec_map_isPushout {A B C P : CommRingCat} (f : A ⟶ B) (g : A ⟶ C)
    (inl : B ⟶ P) (inr : C ⟶ P) (h : IsPushout f g inl inr) :
    IsPullback (Spec.map inl) (Spec.map inr) (Spec.map f) (Spec.map g) :=
  IsPullback.map Scheme.Spec h.op.flip

lemma isPullback_Spec_map_pushout {A B C : CommRingCat} (f : A ⟶ B) (g : A ⟶ C) :
    IsPullback (Spec.map (pushout.inl f g))
      (Spec.map (pushout.inr f g)) (Spec.map f) (Spec.map g) := by
  apply isPullback_Spec_map_isPushout
  exact IsPushout.of_hasPushout f g

-- This should be a general lemma on adjuction
lemma is_pullback (T : Triplet f g) : CategoryTheory.IsPullback
    (Spec.map (pushout.inl _ _))
      (Spec.map (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
          ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)))
        (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
          (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
  isPullback_Spec_map_pushout _ _

lemma Triplet.Spec_ofPointTensor_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    Spec.map ((Triplet.tensorCongr (T.ofPoint_SpectensorTo p)).inv
      ≫ ofPointTensor (T.SpecTensorTo.val.base p)
        ≫ T.SpecTensorTo.residueFieldMap p)
          = Scheme.fromSpecResidueField _ p := by
  simp only [Spec.map_comp, Category.assoc]

  have Spec_κ_p_to_pullback_eq : Spec.map (T.SpecTensorTo.residueFieldMap p)
    ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
      ≫ Spec.map (tensorCongr <| ofPoint_SpectensorTo T p).inv
        ≫ T.SpecTensorTo
          = (Spec T.tensor).fromSpecResidueField p
            ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).hom
              ≫ (ofPoint (T.SpecTensorTo.val.base p)).SpecTensorTo := by
    simp only [tensorCongr_inv, tensorCongr_SpecTensorTo]
    rw [← Hom.residueFieldMap_fromSpecResidueField T.SpecTensorTo p, ofPointtensor_SpectensorTo]

  have Spec_κ_p_to_X_eq : Spec.map (T.SpecTensorTo.residueFieldMap p)
      ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
        ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).inv
          ≫ Spec.map (pushout.inl _ _)
            ≫ X.fromSpecResidueField T.x
              = (Spec T.tensor).fromSpecResidueField p
                ≫ Spec.map (pushout.inl _ _)
                  ≫ X.fromSpecResidueField T.x := by
    have : T.SpecTensorTo ≫ (pullback.fst f g) = Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField T.x := pullback.lift_fst _ _ _
    rw [← this]
    rw [reassoc_of% Spec_κ_p_to_pullback_eq]
    simp only [tensorCongr_SpecTensorTo_assoc]

  have Spec_κ_p_to_Y_eq : Spec.map (Hom.residueFieldMap T.SpecTensorTo p)
      ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
        ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).inv
          ≫ Spec.map (pushout.inr _ _)
            ≫ Y.fromSpecResidueField T.y
              = (Spec T.tensor).fromSpecResidueField p
                ≫ Spec.map (pushout.inr _ _)
                  ≫ Y.fromSpecResidueField T.y := by
    have : T.SpecTensorTo ≫ (pullback.snd f g) = Spec.map (pushout.inr _ _) ≫ Y.fromSpecResidueField T.y := pullback.lift_snd _ _ _
    rw [← this]
    rw [reassoc_of% Spec_κ_p_to_pullback_eq]
    simp only [tensorCongr_SpecTensorTo_assoc]

  apply (is_pullback _).hom_ext
  exact (cancel_mono <| X.fromSpecResidueField T.x).mp Spec_κ_p_to_X_eq
  exact (cancel_mono <| Y.fromSpecResidueField T.y).mp Spec_κ_p_to_Y_eq

lemma carrier_equiv_eq_iff {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔ ∃ e : T₁.1 = T₂.1, (Spec.map (Triplet.tensorCongr e).inv).1.base T₁.2 = T₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨T, _⟩ := T₁
    obtain ⟨T', _⟩ := T₂
    rintro ⟨rfl : T = T', e⟩
    simpa [e]

def carrierEquiv : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  toFun t := ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo.1.base T.2
  left_inv := SpecTensorTo_SpecOfPoint
  right_inv := by
    intro ⟨T, p⟩
    apply carrier_equiv_eq_iff.mpr
    constructor
    · let e := T.ofPoint_SpectensorTo p
      change ((Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))) ≫ (Spec.map (Triplet.tensorCongr e).inv)).val.base (⊥ : PrimeSpectrum _) = p
      conv =>
        rhs
        rw [← fromSpecResidueField_apply p (⊥ : PrimeSpectrum _)]
        rw [← Triplet.Spec_ofPointTensor_SpecTensorTo T p]
      have : (Spec.map (Hom.residueFieldMap T.SpecTensorTo p)).val.base (⊥ : PrimeSpectrum _) = (⊥ : PrimeSpectrum _) := by
        apply (PrimeSpectrum.instUnique).uniq
      rw [← this]
      simp only [Triplet.tensorCongr_inv, comp_coeBase, TopCat.coe_comp, Function.comp_apply,
        Spec.map_comp, Category.assoc]

@[simp]
lemma carrierEquiv_symm_fst (T : Triplet f g) (p : Spec T.tensor) :
    (pullback.fst f g).val.base (carrierEquiv.symm ⟨T, p⟩) = T.x := by
  simp [carrierEquiv]

@[simp]
lemma carrierEquiv_symm_snd (T : Triplet f g) (p : Spec T.tensor) :
    (pullback.snd f g).val.base (carrierEquiv.symm ⟨T, p⟩) = T.y := by
  simp [carrierEquiv]

instance (T : Triplet f g) : Nontrivial T.tensor := by
  apply CommRingCat.nontrivial_pushout_of_isField
  exact Field.toIsField _

lemma Triplet.exists_preimage (T : Triplet f g) :
    ∃ x : ↑(pullback f g),
    (pullback.fst f g).1.base x = T.x ∧ (pullback.snd f g).1.base x = T.y := by
  have : Nonempty (Spec T.tensor) := inferInstance
  obtain ⟨p⟩ := this
  let a : ↑(pullback f g) := carrierEquiv.symm ⟨T, p⟩
  use a
  simp [a]

variable (f g)

-- via `Triplet.exists_preimage`
lemma range_fst : Set.range (pullback.fst f g).1.base = f.1.base ⁻¹' Set.range g.1.base := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.comp_val_base_apply, pullback.condition]
    simp
  · intro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' x y hy.symm)
    use a, ha.left

-- via `Triplet.exists_preimage`
lemma range_snd : Set.range (pullback.snd f g).1.base = g.1.base ⁻¹' Set.range f.1.base := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.comp_val_base_apply, ← pullback.condition]
    simp
  · intro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' y x hy)
    use a, ha.right

-- via `Triplet.exists_preimage`
lemma range_fst_comp :
    Set.range (pullback.fst f g ≫ f).1.base = Set.range f.1.base ∩ Set.range g.1.base := by
  simp [Set.range_comp, range_fst, Set.image_preimage_eq_range_inter]

-- via `Triplet.exists_preimage`
lemma range_snd_comp :
    Set.range (pullback.snd f g ≫ g).1.base = Set.range f.1.base ∩ Set.range g.1.base := by
  rw [← pullback.condition, range_fst_comp]

-- via `Triplet.exists_preimage`
lemma range_map {X Y S X' Y' S' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂).1.base =
      (pullback.fst f' g').val.base ⁻¹' Set.range i₁.val.base ∩
        (pullback.snd f' g').val.base ⁻¹' Set.range i₂.val.base := sorry

end Pullback

lemma exists_preimage_pullback {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (h : f.val.base x = g.val.base y) :
    ∃ z : ↑(pullback f g),
    (pullback.fst f g).1.base z = x ∧ (pullback.snd f g).1.base z = y :=
  let T : Scheme.Pullback.Triplet f g := .mk' x y h
  T.exists_preimage

end AlgebraicGeometry.Scheme
