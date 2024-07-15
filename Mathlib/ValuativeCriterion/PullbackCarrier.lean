-- `Mathlib/AlgebraicGeometry/PullbackCarrier
import Mathlib.ValuativeCriterion.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks

open CategoryTheory CategoryTheory.Limits TopologicalSpace LocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme.Pullback

universe u

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

/-- Given `x : X` and `y : Y` such that `f x = s = g y`,
this is `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×ₛ Y`. -/
def SpecTensorTo :
    Spec T.tensor ⟶ pullback f g :=
  pullback.lift
    (Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField T.x)
    (Spec.map (pushout.inr _ _) ≫ Y.fromSpecResidueField T.y) sorry

def ofPoint (x : ↑(pullback f g)) : Triplet f g :=
  ⟨(pullback.fst f g).1.base x, (pullback.snd f g).1.base x, _, rfl,
    congr((LocallyRingedSpace.Hom.val $(pullback.condition (f := f) (g := g))).base x).symm⟩

end Triplet

def ofPointTensor (x : ↑(pullback f g)) :
    (Triplet.ofPoint x).tensor ⟶ (pullback f g).residueField x :=
  pushout.desc ((pullback.fst f g).residueFieldMap x) ((pullback.snd f g).residueFieldMap x) sorry

lemma ofPointtensor_SpectensorTo (x : ↑(pullback f g)) :
    Spec.map (ofPointTensor x) ≫ (Triplet.ofPoint x).SpecTensorTo =
      (pullback f g).fromSpecResidueField x := sorry

def SpecOfPoint (x : ↑(pullback f g)) : Spec (Triplet.ofPoint x).tensor :=
    PrimeSpectrum.comap (ofPointTensor x) ⊥

lemma SpecTensorTo_SpecOfPoint (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).SpecTensorTo.1.base (SpecOfPoint t) = t := sorry

lemma Triplet.ofPoint_SpectensorTo (T : Triplet f g) (p : Spec T.tensor) :
    ofPoint (T.SpecTensorTo.1.base p) = T := sorry

lemma Triplet.Spec_ofPointTensor_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    Spec.map ((Triplet.tensorCongr (T.ofPoint_SpectensorTo p)).inv ≫
      ofPointTensor _ ≫ T.SpecTensorTo.residueFieldMap p) =
    Scheme.fromSpecResidueField _ p := sorry

lemma carrier_equiv_eq_iff {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔ ∃ e : T₁.1 = T₂.1, (Spec.map (Triplet.tensorCongr e).inv).1.base T₁.2 = T₂.2 := sorry

def carrierEquiv : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  toFun t := ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo.1.base T.2
  left_inv := sorry
  right_inv := sorry

-- move me to `Mathlib\Algebra\Category\Ring\Constructions.lean`
lemma CommRingCat.nontrivial_pushout_of_isField {A B C : CommRingCat.{u}}
    (hA : IsField A) (f : A ⟶ B) (g : A ⟶ C)
    [Nontrivial B] [Nontrivial C] : Nontrivial ↑(pushout f g) := sorry -- by linear algebra

lemma Triplet.exists_preimage (T : Triplet f g) :
  ∃ x : ↑(pullback f g),
    (pullback.fst f g).1.base x = T.x ∧ (pullback.snd f g).1.base x = T.y := sorry

variable (f g)

-- via `Triplet.exists_preimage`
lemma range_fst : Set.range (pullback.fst f g).1.base = f.1.base ⁻¹' Set.range g.1.base := sorry

-- via `Triplet.exists_preimage`
lemma range_snd : Set.range (pullback.snd f g).1.base = g.1.base ⁻¹' Set.range f.1.base := sorry

-- via `Triplet.exists_preimage`
lemma range_base :
    Set.range (pullback.fst f g ≫ f).1.base = Set.range f.1.base ∩ Set.range f.1.base := sorry

-- via `Triplet.exists_preimage`
lemma range_map {X Y S X' Y' S' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
  (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
  (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
  Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂).1.base =
    (pullback.fst f' g').val.base ⁻¹' Set.range i₁.val.base ∩
      (pullback.snd f' g').val.base ⁻¹' Set.range i₂.val.base := sorry

end AlgebraicGeometry.Scheme.Pullback
