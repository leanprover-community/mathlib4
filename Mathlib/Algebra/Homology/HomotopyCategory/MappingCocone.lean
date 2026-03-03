/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping cocone

Given a morphism `φ : K ⟶ L` of cochain complexes, the mapping cone
allows to obtain a triangle `K ⟶ L ⟶ mappingCone φ ⟶ ...`. In this
file, we define the mapping cocone, which fits in a rotated triangle:
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The mapping cocone of a morphism `φ : K ⟶ L` of cochain complexes: it is
`(mappingCone φ)⟦(-1 : ℤ)⟧`. -/
noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C ℤ := (mappingCone φ)⟦(-1 : ℤ)⟧

namespace mappingCocone

section

variable [HasHomotopyCofiber φ]

/-- The first projection `mappingCocone φ ⟶ K`. -/
noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

/-- The second projection in `Cochain (mappingCocone φ) L (-1)`. -/
noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

/-- The left inclusion in `Cochain K (mappingCocone φ) 0`. -/
noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

/-- The right inclusion in `Cocycle L (mappingCocone φ) 1`. -/
noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_v_fst_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _ := by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ).v p p (add_zero p) ≫ (snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_v_fst_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (fst φ).f q = 0 := by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_v_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (snd φ).v q p (by lia) = 𝟙 _ := by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

set_option backward.isDefEq.respectTransparency false in
lemma id_X (p q : ℤ) (hpq : p + -1 = q) :
    (fst φ).f p ≫ (inl φ).v p p (add_zero p) +
      (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩,
    mappingCone.id_X φ (p + -1) p (by lia)]

section

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

/-- Constructor for cochains from `mappingCocone`. -/
noncomputable def descCochain : Cochain (mappingCocone φ) M m :=
  (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inl_v_descCochain_v (p q : ℤ) (hpq : p + m = q) :
    (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h).v p q hpq = α.v p q hpq := by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma inr_v_descCochain_v (p q : ℤ) (hpq : p + 1 = q) (r : ℤ) (hr : q + m = r) :
    (inr φ).1.v p q hpq ≫ (descCochain φ α β h).v q r hr = β.v p r (by lia) := by
  obtain rfl : p = q + -1 := by lia
  simp [inr, descCochain, mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

@[simp]
lemma inl_comp_descCochain :
    (inl φ).comp (descCochain φ α β h) (zero_add m) = α := by
  cat_disch

@[simp]
lemma inr_comp_descCochain :
    (inr φ).1.comp (descCochain φ α β h) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

set_option backward.isDefEq.respectTransparency false in
lemma δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ m n (descCochain φ α β h) =
      (Cochain.ofHom (fst φ)).comp
        (δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (zero_add n) +
      (snd φ).comp (δ n n' β) (by lia) := by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by lia
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by lia),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ (p + -1) (by lia),
    Cochain.leftShift_v (n := m + 2) _ (-1) _ _ _ q _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.comp_v (n₁ := 1) _ _ _ (p + -1) p _ (by lia) hpq,
    Cochain.comp_v (n₂ := m + 2) _ _ _ p (p + -1) q rfl (by lia),
    smul_smul, Int.negOnePow_add, Int.negOnePow_even 2 ⟨1, rfl⟩]
  grind

end

/-- Constructor for cocycles from `mappingCocone`. -/
@[simps]
noncomputable def descCocycle {M : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain K M m) (β : Cocycle L M n) (h : m + 1 = n)
    (hαβ : δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β.1 (zero_add n) = 0) :
    Cocycle (mappingCocone φ) M m :=
  ⟨descCochain φ α β h, by
    simp [Cocycle.mem_iff _ n h, δ_descCochain _ _ _ h (n + 1) (by lia), hαβ]⟩

section

variable {M : CochainComplex C ℤ} (α : Cochain K M 0) (β : Cocycle L M 1)
  (hαβ : δ 0 1 α + (Cochain.ofHom φ).comp β.1 (zero_add 1) = 0)

/-- Constructor for morphisms from `mappingCocone`. -/
noncomputable def desc : mappingCocone φ ⟶ M :=
  (descCocycle φ α β (zero_add 1) (by simpa)).homOf

@[simp]
lemma ofHom_desc :
    Cochain.ofHom (desc φ α β hαβ) = descCochain φ α β.1 (by lia) := by
  simp [desc]

@[reassoc (attr := simp)]
lemma inl_v_desc_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (desc φ α β hαβ).f p = α.v p p (add_zero p) := by
  simp [desc]

@[reassoc (attr := simp)]
lemma inr_v_desc_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (desc φ α β hαβ).f q = β.1.v p q hpq := by
  simp [desc]

end

section

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

/-- Constructor for cochains to `mappingCocone`. -/
noncomputable def liftCochain : Cochain M (mappingCocone φ) n :=
  (mappingCone.liftCochain φ α β h).rightShift (-1) n (by lia)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftCochain_v_fst_f (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).f p₂ = α.v p₁ p₂ h₁₂ := by
  simp [liftCochain, mappingCocone, fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftCochain_v_snd_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₃ h₂₃ = β.v p₁ p₃ (by lia) := by
  subst h₂₃
  simp [liftCochain, mappingCocone, snd,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ _ (add_zero _),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

@[simp]
lemma liftCochain_comp_fst :
    (liftCochain φ α β h).comp (Cochain.ofHom (fst φ)) (add_zero _) = α := by
  cat_disch

@[simp]
lemma liftCochain_comp_snd :
    (liftCochain φ α β h).comp (snd φ) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₁ := n) (n₂ := -1) (n₁₂ := m) _ _ _ p _ _ (by lia)
    (Int.add_neg_cancel_right q 1)]

set_option backward.isDefEq.respectTransparency false in
lemma δ_liftCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (liftCochain φ α β h) =
      (δ n n' α).comp (inl φ) (add_zero _) -
        (δ m n β + α.comp (Cochain.ofHom φ) (add_zero n)).comp (inr φ).1 hn' := by
  dsimp [liftCochain, inl, inr]
  ext p q hpq
  simp [mappingCone.δ_liftCochain _ _ _ _ n' hn',
    Cochain.δ_rightShift _ (-1) _ n' _ n  (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (q + -1)),
    Cochain.comp_v _ _ _ p q _ hpq rfl,
    Cochain.comp_v (n₁ := n) (n₂ := 1) _ _ _ p (q + -1) q (by lia) (by lia)]
  grind

end

/-- Constructor for cocycles to `mappingCocone`. -/
@[simps]
noncomputable def liftCocycle {M : CochainComplex C ℤ} {n m : ℤ}
    (α : Cocycle M K n) (β : Cochain M L m) (h : m + 1 = n)
    (hαβ : δ m n β + α.1.comp (Cochain.ofHom φ) (add_zero n) = 0) :
    Cocycle M (mappingCocone φ) n :=
  ⟨liftCochain φ α β h,
    by simp [Cocycle.mem_iff _ _ rfl, δ_liftCochain _ _ _ _ _ rfl, hαβ]⟩

section

variable {M : CochainComplex C ℤ} (α : M ⟶ K) (β : Cochain M L (-1))
  (hαβ : δ (-1) 0 β + Cochain.ofHom (α ≫ φ) = 0)

/-- Constructor for morphisms to `mappingCocone`. -/
noncomputable def lift : M ⟶ mappingCocone φ :=
  Cocycle.homOf (liftCocycle φ (Cocycle.ofHom α) β (by simp) (by simpa [← Cochain.ofHom_comp]))

@[simp]
lemma ofHom_lift :
    Cochain.ofHom (lift φ α β hαβ) = liftCochain φ (Cochain.ofHom α) β (by simp) := by
  simp [lift]

@[reassoc (attr := simp)]
lemma lift_f_fst_f (p : ℤ) :
    (lift φ α β hαβ).f p ≫ (fst φ).f p = α.f p := by
  simp [lift]

@[reassoc (attr := simp)]
lemma lift_fst :
    lift φ α β hαβ ≫ fst φ = α := by
  cat_disch

@[reassoc (attr := simp)]
lemma lift_f_snd_v (p q : ℤ) (hpq : p + (-1) = q) :
    (lift φ α β hαβ).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  simp [lift]

end

end

section

variable [HasBinaryBiproducts C]

/-- Given a morphism `φ : K ⟶ L` of cochain complexes, this is the triangle
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (fst φ) φ
    ((mappingCone.triangle φ).mor₂ ≫ (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by lia)).inv.app _)

set_option backward.isDefEq.respectTransparency false in
/-- Rotating the triangle `mappingCocone.triangle φ` gives a triangle that is
isomorphic to `mappingCone.triangle φ`. -/
noncomputable def rotateTriangleIso :
    (triangle φ).rotate ≅ mappingCone.triangle φ := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by lia)).app _)
    (by simp) (by simp [triangle]) ?_
  dsimp
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

end

end mappingCocone

end CochainComplex
