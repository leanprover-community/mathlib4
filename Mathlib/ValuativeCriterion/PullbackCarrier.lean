-- `Mathlib/AlgebraicGeometry/PullbackCarrier
import Mathlib.ValuativeCriterion.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

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

lemma is_pullback : CategoryTheory.IsPullback
    (Spec.map (pushout.inl _ _))
      (Spec.map (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)))
        (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
          (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) := by
  sorry

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
    (Spec.map (pushout.inr _ _) ≫ Y.fromSpecResidueField T.y)
      /-
      X Y S : Scheme
      f : X ⟶ S
      g : Y ⟶ S
      T : Triplet f g
      ⊢ (Spec.map
              (pushout.inl ((S.residueFieldCongr ⋯).inv ≫ Hom.residueFieldMap f T.x)
                ((S.residueFieldCongr ⋯).inv ≫ Hom.residueFieldMap g T.y)) ≫
            X.fromSpecResidueField T.x) ≫
          f =
        (Spec.map
              (pushout.inr ((S.residueFieldCongr ⋯).inv ≫ Hom.residueFieldMap f T.x)
                ((S.residueFieldCongr ⋯).inv ≫ Hom.residueFieldMap g T.y)) ≫
            Y.fromSpecResidueField T.y) ≫
          g
      -/
      sorry

/-- Given `t : X ×ₛ Y`, it maps to `X` and `Y` with same image in `S`, yielding a `Triplet f g`. -/
def ofPoint (t : ↑(pullback f g)) : Triplet f g :=
  ⟨(pullback.fst f g).1.base t, (pullback.snd f g).1.base t, _, rfl,
    congr((LocallyRingedSpace.Hom.val $(pullback.condition (f := f) (g := g))).base t).symm⟩

end Triplet

/-- The ring map from tensor to residue field in the pullback. -/
def ofPointTensor (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).tensor ⟶ (pullback f g).residueField t :=
  /-
  X Y S : Scheme
  f : X ⟶ S
  g : Y ⟶ S
  t : ↑↑(pullback f g).toPresheafedSpace
  ⊢ ((S.residueFieldCongr ⋯).inv ≫ Hom.residueFieldMap f (Triplet.ofPoint t).x) ≫ Hom.residueFieldMap (pullback.fst f g) t =
    ((S.residueFieldCongr ⋯).inv ≫ Hom.residueFieldMap g (Triplet.ofPoint t).y) ≫ Hom.residueFieldMap (pullback.snd f g) t
  -/
  pushout.desc ((pullback.fst f g).residueFieldMap t) ((pullback.snd f g).residueFieldMap t) sorry

lemma ofPointtensor_SpectensorTo (t : ↑(pullback f g)) :
    Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo =
      /-
      X Y S : Scheme
      f : X ⟶ S
      g : Y ⟶ S
      t : ↑↑(pullback f g).toPresheafedSpace
      ⊢ Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo = (pullback f g).fromSpecResidueField t
      -/
      (pullback f g).fromSpecResidueField t := sorry -- two limit

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
    have : T.SpecTensorTo ≫ pullback.fst f g = Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField T.x := by
      sorry
    rw [this]
    change (X.fromSpecResidueField T.x).val.base _ = T.x
    exact fromSpecResidueField_apply T.x _
  ·
    sorry

instance fromSpecResidueField_is_preimmesion (x : X) : AlgebraicGeometry.IsPreimmersion (X.fromSpecResidueField x) := sorry
-- set_option maxHeartbeats 0

@[reassoc (attr := simp)]
lemma tensorCongr_SpecTensorTo {T T' : Triplet f g} (h : T = T') :
    Spec.map (Triplet.tensorCongr h).hom ≫ T.SpecTensorTo = T'.SpecTensorTo := by
  subst h
  simp

lemma Triplet.Spec_ofPointTensor_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    Spec.map ((Triplet.tensorCongr (T.ofPoint_SpectensorTo p)).inv
      ≫ ofPointTensor (T.SpecTensorTo.val.base p)
        ≫ T.SpecTensorTo.residueFieldMap p)
          = Scheme.fromSpecResidueField _ p := by
  simp only [Spec.map_comp, Category.assoc]

  have Spec_κ_p_to_pullback_eq : Spec.map (T.SpecTensorTo.residueFieldMap p)
      ≫ (pullback f g).fromSpecResidueField (T.SpecTensorTo.val.base p)
        = (Spec T.tensor).fromSpecResidueField p
          ≫ T.SpecTensorTo := by
    exact hom.residueFieldMap_fromSpecResidueField T.SpecTensorTo p

  -- have Spec_κ_p_to_pullback_eq' : Spec.map (T.SpecTensorTo.residueFieldMap p)
  --     ≫ (pullback f g).fromSpecResidueField (T.SpecTensorTo.val.base p)
  --       = (Spec T.tensor).fromSpecResidueField p
  --         ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).hom
  --           ≫ (ofPoint (T.SpecTensorTo.val.base p)).SpecTensorTo := by
  --   rw [Spec_κ_p_to_pullback_eq]
  --   rw [tensorCongr_SpecTensorTo (T.ofPoint_SpectensorTo p)]

  have Spec_κ_p_to_pullback_eq' : Spec.map (T.SpecTensorTo.residueFieldMap p)
    ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
      ≫ Spec.map (tensorCongr <| ofPoint_SpectensorTo T p).inv
        ≫ T.SpecTensorTo
          = (Spec T.tensor).fromSpecResidueField p
            ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).hom
              ≫ (ofPoint (T.SpecTensorTo.val.base p)).SpecTensorTo := by
    simp only [tensorCongr_inv, tensorCongr_SpecTensorTo]
    rw [← Spec_κ_p_to_pullback_eq, ofPointtensor_SpectensorTo]

  -- have Spec_κ_p_to_X_eq' : Spec.map (T.SpecTensorTo.residueFieldMap p)
  --     ≫ (pullback f g).fromSpecResidueField (T.SpecTensorTo.val.base p)
  --       ≫ pullback.fst f g
  --         = (Spec T.tensor).fromSpecResidueField p
  --           ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).hom
  --             ≫ (ofPoint (T.SpecTensorTo.val.base p)).SpecTensorTo
  --               ≫ pullback.fst f g := by
  --   rw [reassoc_of% Spec_κ_p_to_pullback_eq']

  have Spec_κ_p_to_X_eq' : Spec.map (T.SpecTensorTo.residueFieldMap p)
    ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
      ≫ Spec.map (tensorCongr <| ofPoint_SpectensorTo T p).inv
        ≫ T.SpecTensorTo ≫ pullback.fst f g
          = (Spec T.tensor).fromSpecResidueField p
            ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).hom
              ≫ (ofPoint (T.SpecTensorTo.val.base p)).SpecTensorTo
                ≫ pullback.fst f g := by
    rw [reassoc_of% Spec_κ_p_to_pullback_eq']

  -- have x_eq : (T.SpecTensorTo ≫ (pullback.fst f g)).val.base p = T.x := sorry

  -- have Spec_κ_SpecTensorTo_p_to_X_eq : (pullback f g).fromSpecResidueField (T.SpecTensorTo.val.base p)
  --     ≫ pullback.fst f g
  --       = Spec.map ((pullback.fst f g).residueFieldMap (T.SpecTensorTo.val.base p))
  --         ≫ Spec.map (X.residueFieldCongr x_eq).inv
  --           ≫ X.fromSpecResidueField T.x := sorry

  -- have Spec_κ_SpecTensorTo_p_to_X_eq' : (pullback f g).fromSpecResidueField (T.SpecTensorTo.val.base p)
  --     ≫ pullback.fst f g
  --       = Spec.map ((pullback.fst f g).residueFieldMap (T.SpecTensorTo.val.base p))
  --         ≫ X.fromSpecResidueField ((T.SpecTensorTo ≫ (pullback.fst f g)).val.base p) := by
  --   rw [Spec_κ_SpecTensorTo_p_to_X_eq]
  --   simp only [comp_coeBase, TopCat.coe_comp, Function.comp_apply, residueFieldCongr_inv,
  --     residueFieldCongr_fromSpecResidueField]

  -- have Spec_κ_p_to_X_eq'' : Spec.map (T.SpecTensorTo.residueFieldMap p)
  --     ≫ (pullback f g).fromSpecResidueField (T.SpecTensorTo.val.base p)
  --       ≫ pullback.fst f g
  --         = Spec.map (T.SpecTensorTo.residueFieldMap p)
  --           ≫ Spec.map ((pullback.fst f g).residueFieldMap (T.SpecTensorTo.val.base p))
  --             ≫ X.fromSpecResidueField ((T.SpecTensorTo ≫ (pullback.fst f g)).val.base p) := by
  --   rw [Spec_κ_SpecTensorTo_p_to_X_eq']

  have Spec_κ_p_to_X_eq : Spec.map (T.SpecTensorTo.residueFieldMap p)
      ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
        ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).inv
          ≫ Spec.map (pushout.inl _ _)
            ≫ X.fromSpecResidueField T.x
              = (Spec T.tensor).fromSpecResidueField p
                ≫ Spec.map (pushout.inl _ _)
                  ≫ X.fromSpecResidueField T.x := by
    have : T.SpecTensorTo ≫ (pullback.fst f g)
        = Spec.map (pushout.inl _ _) ≫ X.fromSpecResidueField T.x := by
      sorry
    rw [← this]
    rw [Spec_κ_p_to_X_eq']
    simp only [tensorCongr_SpecTensorTo_assoc]

  -- Now everything for `Y`

  have Spec_κ_p_to_Y_eq : Spec.map (Hom.residueFieldMap T.SpecTensorTo p)
      ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
        ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).inv
          ≫ Spec.map (pushout.inr _ _)
            ≫ Y.fromSpecResidueField T.y
              = (Spec T.tensor).fromSpecResidueField p
                ≫ Spec.map (pushout.inr _ _)
                  ≫ Y.fromSpecResidueField T.y := by
    sorry

  have Spec_κ_p_to_Spec_κ_x_eq : Spec.map (Hom.residueFieldMap T.SpecTensorTo p)
      ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
        ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).inv
          ≫ Spec.map (pushout.inl _ _)
            = (Spec T.tensor).fromSpecResidueField p
              ≫ Spec.map (pushout.inl _ _) :=
    (cancel_mono <| X.fromSpecResidueField T.x).mp Spec_κ_p_to_X_eq

  have Spec_κ_p_to_Spec_κ_y_eq : Spec.map (Hom.residueFieldMap T.SpecTensorTo p)
      ≫ Spec.map (ofPointTensor (T.SpecTensorTo.val.base p))
        ≫ Spec.map (tensorCongr (T.ofPoint_SpectensorTo p)).inv
          ≫ Spec.map (pushout.inr _ _)
            = (Spec T.tensor).fromSpecResidueField p
              ≫ Spec.map (pushout.inr _ _) :=
    (cancel_mono <| Y.fromSpecResidueField T.y).mp Spec_κ_p_to_Y_eq

  apply (is_pullback _).hom_ext
  exact Spec_κ_p_to_Spec_κ_x_eq
  exact Spec_κ_p_to_Spec_κ_y_eq

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
