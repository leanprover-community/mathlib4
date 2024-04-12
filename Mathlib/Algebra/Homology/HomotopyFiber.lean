import Mathlib.Algebra.Homology.Homotopy

open CategoryTheory Limits HomologicalComplex Category
  ZeroObject

namespace HomologicalComplex

variable {C ι : Type*} [Category C] [HasZeroMorphisms C]
  [HasZeroObject C] {c : ComplexShape ι} [DecidableEq ι] [DecidableRel c.Rel]
  (K : HomologicalComplex C c)

noncomputable def prevX (j : ι) : C :=
  if c.Rel (c.prev j) j
  then K.X (c.prev j)
  else 0

lemma isZero_prevX (j : ι) (h : ¬ c.Rel (c.prev j) j) :
    IsZero (K.prevX j) := by
  dsimp [prevX]
  rw [if_neg h]
  exact Limits.isZero_zero C

noncomputable def prevXIso (i j : ι) (hij : c.Rel i j) : K.prevX j ≅ K.X i :=
  eqToIso (by
    dsimp [prevX]
    obtain rfl := c.prev_eq' hij
    rw [if_pos hij])

noncomputable def prevXd (j : ι) : K.prevX j ⟶ K.X j :=
  if hj : c.Rel (c.prev j) j
  then (K.prevXIso _ _ hj).hom ≫ K.d (c.prev j) j
  else 0

@[reassoc (attr := simp)]
lemma prevXIso_inv_d {i j : ι} (hij : c.Rel i j) :
    (K.prevXIso _ _ hij).inv ≫ K.prevXd j = K.d i j := by
  obtain rfl := c.prev_eq' hij
  dsimp [prevXd]
  rw [dif_pos hij, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma prevXd_d (j k : ι) : K.prevXd j ≫ K.d j k = 0 := by
  dsimp [prevXd]
  split_ifs <;> simp

end HomologicalComplex

namespace Homotopy

variable {C ι : Type*} [Category C] [Preadditive C]
  [HasZeroObject C] {c : ComplexShape ι} [DecidableEq ι] [DecidableRel c.Rel]
  {K L : HomologicalComplex C c} {f g : K ⟶ L} (H : Homotopy f g)

noncomputable def homToPrevX (j : ι) : K.X j ⟶ L.prevX j :=
  if hj : c.Rel (c.prev j) j
  then H.hom _ _ ≫ (L.prevXIso _ _ hj).inv
  else 0

@[reassoc]
lemma homToPrevX_prevXd (j : ι) :
    H.homToPrevX j ≫ L.prevXd j = prevD j H.hom := by
  dsimp [prevXd, homToPrevX]
  split_ifs with h
  · simp [toPrev, dTo]
  · dsimp [dTo]
    rw [L.shape _ _ h, comp_zero, comp_zero]

@[reassoc (attr := simp)]
lemma homToPrevX_prevXIso_hom (i j : ι) (hij : c.Rel i j) :
    H.homToPrevX j ≫ (L.prevXIso _ _ hij).hom = H.hom j i := by
  obtain rfl := c.prev_eq' hij
  simp [homToPrevX, dif_pos hij]

end Homotopy

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

section

variable {F G : CochainComplex C α} (f : F ⟶ G)
  [∀ (n : α), HasBinaryBiproduct (F.X n) (G.prevX n)]

noncomputable def homotopyFiber : CochainComplex C α where
  X i := F.X i ⊞ G.prevX i
  d i j :=
    if hij : i + 1 = j
    then
      biprod.fst ≫ F.d _ _ ≫ biprod.inl -
      (biprod.fst ≫ f.f i + biprod.snd ≫ G.prevXd i) ≫ (G.prevXIso _ _ hij).inv ≫ biprod.inr
    else 0
  shape i j (hij : i + 1 ≠ j) := by simp only [dif_neg hij]
  d_comp_d' := by
    rintro i _ _ rfl rfl
    simp

namespace HomotopyFiber

lemma d_eq (i j : α) (h : i + 1 = j) :
    (homotopyFiber f).d i j =
      biprod.fst ≫ F.d _ _ ≫ biprod.inl -
      (biprod.fst ≫ f.f i + biprod.snd ≫ G.prevXd i) ≫ (G.prevXIso _ _ h).inv ≫ biprod.inr :=
  dif_pos h

noncomputable def fst : homotopyFiber f ⟶ F where
  f n := biprod.fst
  comm' := by
    rintro i _ rfl
    dsimp
    simp only [d_eq _ _ _ rfl, Preadditive.add_comp, assoc, Preadditive.sub_comp,
      biprod.inl_fst, comp_id, biprod.inr_fst, comp_zero, add_zero, sub_zero]

noncomputable def lift {M : CochainComplex C α} (φ : M ⟶ F) (h : Homotopy (φ ≫ f) 0) :
    M ⟶ homotopyFiber f where
  f n := biprod.lift (φ.f n) (-h.homToPrevX n)
  comm' := by
    rintro i _ rfl
    rw [d_eq _ _ _ rfl]
    simp only [Preadditive.add_comp, assoc, Preadditive.comp_sub,
      biprod.lift_fst_assoc, Hom.comm_assoc, Preadditive.comp_add, biprod.lift_snd_assoc,
      Preadditive.neg_comp]
    apply biprod.hom_ext
    · simp
    · dsimp
      simp only [ComplexShape.up_Rel, not_true, Preadditive.sub_comp, Preadditive.neg_comp,
        biprod.inl_snd, comp_zero, neg_zero, biprod.inr_snd,
        comp_id, zero_sub, neg_add_rev, neg_neg, biprod.lift_snd,
        ← cancel_mono (G.prevXIso i (i + 1) rfl).hom,
        Preadditive.add_comp, assoc, Iso.inv_hom_id, comp_id, zero_f,
        h.homToPrevX_prevXd, h.homToPrevX_prevXIso_hom, ← comp_f, h.comm i, add_zero,
        dNext_eq h.hom rfl, Preadditive.comp_neg, add_neg_cancel_left]

@[reassoc (attr := simp)]
lemma lift_fst {M : CochainComplex C α} (φ : M ⟶ F) (h : Homotopy (φ ≫ f) 0) :
    lift f φ h ≫ fst f = φ := by
  ext n
  simp [lift, fst]

end HomotopyFiber

end

section

variable (K L : CochainComplex C α) [DecidableEq α] [HasBinaryBiproduct K K]
  [∀ (n : α), HasBinaryBiproduct ((K ⊞ K).X n) (prevX K n)]

noncomputable abbrev pathObject : CochainComplex C α := homotopyFiber (biprod.desc (𝟙 K) (-𝟙 K))

namespace pathObject

variable {K L}

noncomputable def π₀ : pathObject K ⟶ K := HomotopyFiber.fst _ ≫ biprod.fst

noncomputable def π₁ : pathObject K ⟶ K := HomotopyFiber.fst _ ≫ biprod.snd

section

variable (f₀ f₁ : L ⟶ K) (h : Homotopy f₀ f₁)

noncomputable def lift : L ⟶ pathObject K :=
  HomotopyFiber.lift _ (biprod.lift f₀ f₁)
    (Homotopy.trans (Homotopy.ofEq (by simp [sub_eq_add_neg])) (Homotopy.equivSubZero h))

@[reassoc (attr := simp)]
lemma lift_π₀ : lift f₀ f₁ h ≫ π₀ = f₀ := by simp [lift, π₀]

@[reassoc (attr := simp)]
lemma lift_π₁ : lift f₀ f₁ h ≫ π₁ = f₁ := by simp [lift, π₁]

end

noncomputable def ι : K ⟶ pathObject K := lift (𝟙 K) (𝟙 K) (Homotopy.refl _)

@[reassoc (attr := simp)]
lemma ι_π₀ : ι ≫ π₀ = 𝟙 K := lift_π₀ _ _ _

@[reassoc (attr := simp)]
lemma ι_π₁ : ι ≫ π₁ = 𝟙 K := lift_π₁ _ _ _

end pathObject

end

end CochainComplex
