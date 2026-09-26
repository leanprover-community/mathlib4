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
@[no_expose]
noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C ℤ := (mappingCone φ)⟦(-1 : ℤ)⟧

@[no_expose]
noncomputable def shiftMappingCoconeIso [HasHomotopyCofiber φ] :
    (mappingCocone φ)⟦(1 : ℤ)⟧ ≅ mappingCone φ :=
  (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by lia)).app _

namespace mappingCocone

section

variable [HasHomotopyCofiber φ]

@[simp]
lemma isZero_X_iff (i j : ℤ) (hj : j + 1 = i := by lia) :
    IsZero ((mappingCocone φ).X i) ↔ IsZero (K.X i) ∧ IsZero (L.X j) := by
  obtain rfl : j = i + -1 := by lia
  simp [mappingCocone, mappingCone.isZero_X_iff]

/-- The first projection `mappingCocone φ ⟶ K`. -/
@[no_expose]
noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

/-- The second projection in `Cochain (mappingCocone φ) L (-1)`. -/
@[no_expose]
noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

/-- The left inclusion in `Cochain K (mappingCocone φ) 0`. -/
@[no_expose]
noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

/-- The right inclusion in `Cocycle L (mappingCocone φ) 1`. -/
@[no_expose]
noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

@[reassoc (attr := simp)]
lemma inl_v_fst_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _ := by
  simp [mappingCocone, inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ).v p p (add_zero p) ≫ (snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [mappingCocone, inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

@[reassoc (attr := simp)]
lemma inr_v_fst_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (fst φ).f q = 0 := by
  simp [mappingCocone, inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

@[reassoc (attr := simp)]
lemma inr_v_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (snd φ).v q p (by lia) = 𝟙 _ := by
  simp [mappingCocone, inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

lemma ext_to (i j : ℤ) (hij : i + -1 = j) {A : C} {f g : A ⟶ (mappingCocone φ).X i}
    (h₁ : f ≫ (fst φ).f i = g ≫ (fst φ).f i)
    (h₂ : f ≫ (snd φ).v i j hij = g ≫ (snd φ).v i j hij) :
    f = g := by
  dsimp [mappingCocone] at f g h₁ h₂ ⊢
  refine mappingCone.ext_to _ (i + -1) i (by lia) ?_ ?_
  · simpa [fst, Cochain.leftShift_v (n := 1) _ (-1) 0 (by lia) i i (by lia)
      (i + -1) (by lia)] using h₁
  · obtain rfl : j = i + -1 := by lia
    simpa [snd, Cochain.leftShift_v (n := 0) _ (-1) (-1) (by lia) i (i + -1) (by lia)
      (i + -1) (by lia)] using h₂

lemma ext_to_iff (i j : ℤ) (hij : i + -1 = j) {A : C} (f g : A ⟶ (mappingCocone φ).X i) :
    f = g ↔ f ≫ (fst φ).f i = g ≫ (fst φ).f i ∧
      f ≫ (snd φ).v i j hij = g ≫ (snd φ).v i j hij := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂

attribute [local implicit_reducible] mappingCocone in
open HomComplex in
lemma ext_from (i j : ℤ) (hij : i + 1 = j) {A : C} {f g : (mappingCocone φ).X j ⟶ A}
    (h₁ : (inl φ).v j j (add_zero j) ≫ f = (inl φ).v j j (add_zero j) ≫ g)
    (h₂ : (inr φ).1.v i j hij ≫ f = (inr φ).1.v i j hij ≫ g) :
    f = g := by
  dsimp [mappingCocone]
  refine mappingCone.ext_from _ j (j + -1) (by lia) ?_ ?_
  · simpa [inl, Cochain.rightShift_v (n := -1) _ (-1) 0 (by lia) j j (by lia)
      (j + -1) (by lia)] using h₁
  · obtain rfl : i = j + -1 := by lia
    simpa [inr, Cochain.rightShift_v (n := 0) _ (-1) 1 (by lia) (j + -1) j (by lia)] using h₂

lemma ext_from_iff (i j : ℤ) (hij : i + 1 = j) {A : C} (f g : (mappingCocone φ).X j ⟶ A) :
    f = g ↔ (inl φ).v j j (add_zero j) ≫ f = (inl φ).v j j (add_zero j) ≫ g ∧
      (inr φ).1.v i j hij ≫ f = (inr φ).1.v i j hij ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂

@[reassoc]
lemma inl_v_d (i j : ℤ) (hij : i + 1 = j) :
    (inl φ).v i i (add_zero i) ≫ (mappingCocone φ).d i j =
      K.d i j ≫ (inl φ).v j j (add_zero j) - φ.f i ≫ (inr φ).1.v i j hij := by
  obtain rfl : i = j + -1 := by lia
  simp [inl, inr, mappingCocone,
    Cochain.rightShift_v _ (-1) 0 (zero_add (-1)) (j + -1) (j + -1) (by lia)
      (j + -1 + -1) (by lia),
    mappingCone.inl_v_d _ (j + -1) (j + -1 + -1) j (by lia) (by lia),
    Cochain.rightShift_v (n := -1) _ (-1) 0 (by lia) j j (by lia) (j + -1) (by lia),
    Cochain.rightShift_v (n := 0) _ (-1) 1 (by lia) (j + -1) j (by lia) (j + -1) (by lia)]
  rfl

@[reassoc]
lemma inr_v_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (inr φ).1.v i j hij ≫ (mappingCocone φ).d j k =
      -L.d i j ≫ (inr φ).1.v j k hjk := by
  obtain rfl : j = k + -1 := by lia
  simp [inr, mappingCocone,
    Cochain.rightShift_v (n := 0) _ (-1) 1 (by lia) i (k + -1) (by lia) i (by lia),
    Cochain.rightShift_v (n := 0) _ (-1) 1 (by lia) (k + -1) k (by lia) (k + -1) (by lia)]
  rfl

@[reassoc]
lemma d_fst_v (i j : ℤ) :
    (mappingCocone φ).d i j ≫ (fst φ).f j = (fst φ).f i ≫ K.d i j := by
  simp

@[reassoc]
lemma d_snd_v (i j k : ℤ) (hij : j + -1 = i) (hjk : i + -1 = k) :
    (mappingCocone φ).d i j ≫ (snd φ).v j i (by lia) =
      - (snd φ).v i k hjk ≫ L.d k i - (fst φ).f i ≫ φ.f i := by
  simp [ext_from_iff _ k i (by lia), inl_v_d_assoc φ i j (by lia),
    inr_v_d_assoc φ k i j (by lia) (by lia)]

lemma id_X (p q : ℤ) (hpq : p + -1 = q) :
    (fst φ).f p ≫ (inl φ).v p p (add_zero p) +
      (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simpa [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩] using! mappingCone.id_X φ (p + -1) p (by lia)

section

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

/-- Constructor for cochains from `mappingCocone`. -/
@[no_expose]
noncomputable def descCochain : Cochain (mappingCocone φ) M m :=
  (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma inl_v_descCochain_v (p q : ℤ) (hpq : p + m = q) :
    (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h).v p q hpq = α.v p q hpq := by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  abel

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
@[no_expose]
noncomputable def liftCochain : Cochain M (mappingCocone φ) n :=
  (mappingCone.liftCochain φ α β h).rightShift (-1) n (by lia)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma liftCochain_v_fst_f (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).f p₂ = α.v p₁ p₂ h₁₂ := by
  simp [liftCochain, mappingCocone, fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
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
    Cochain.δ_rightShift _ (-1) _ n' _ n (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (q + -1)),
    Cochain.comp_v _ _ _ p q _ hpq rfl,
    Cochain.comp_v (n₁ := n) (n₂ := 1) _ _ _ p (q + -1) q (by lia) (by lia)]
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  abel

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

@[no_expose]
noncomputable def triangleδ : L ⟶ (mappingCocone φ)⟦(1 : ℤ)⟧ :=
  (mappingCone.triangle φ).mor₂ ≫ (shiftMappingCoconeIso φ).inv

@[reassoc (attr := simp)]
lemma triangleδ_f_snd_v (n : ℤ) :
    (triangleδ φ).f n ≫ (snd φ).v (n + 1) n (by lia) = 𝟙 _ := by
  simp [mappingCocone, triangleδ, shiftMappingCoconeIso, snd,
    HomComplex.Cochain.leftShift_v (n := 0) _ (-1) (-1) (by lia) (n + 1) n (by lia) n (by lia),
    Int.negOnePow_even 2 (by grind), CochainComplex.shiftFunctorCompIsoId_inv_app]

@[reassoc (attr := simp)]
lemma triangleδ_f_fst_f (n : ℤ) :
    (triangleδ φ).f n ≫ (fst φ).f (n + 1) = 0 := by
  simp [mappingCocone, triangleδ, shiftMappingCoconeIso, fst,
    HomComplex.Cochain.leftShift_v (n := 1) _ (-1) 0 (by lia) (n + 1) (n + 1) (by lia) n (by lia),
    CochainComplex.shiftFunctorCompIsoId_inv_app]

@[reassoc (attr := simp)]
lemma triangleδ_shiftMappingCoconeIso_hom :
    triangleδ φ ≫ (shiftMappingCoconeIso φ).hom = mappingCone.inr φ := by
  simp [triangleδ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma shiftMappingCoconeIso_hom_mappingConeTriangle_mor₃ :
    dsimp% (shiftMappingCoconeIso φ).hom ≫ (mappingCone.triangle φ).mor₃ = -(fst φ)⟦1⟧' := by
  dsimp [triangleδ, shiftMappingCoconeIso]
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

/-- Given a morphism `φ : K ⟶ L` of cochain complexes, this is the triangle
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`. -/
@[implicit_reducible, simps!]
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (fst φ) φ (triangleδ φ)

/-- Rotating the triangle `mappingCocone.triangle φ` gives a triangle that is
isomorphic to `mappingCone.triangle φ`. -/
noncomputable def rotateTriangleIso :
    (triangle φ).rotate ≅ mappingCone.triangle φ :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (shiftMappingCoconeIso φ) (by simp) (by simp) (by simp)

end

end mappingCocone

end CochainComplex
