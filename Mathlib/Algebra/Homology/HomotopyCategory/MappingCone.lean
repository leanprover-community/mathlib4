import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

open CategoryTheory Category Limits Preadditive

variable {C : Type _} [Category C]

@[simp]
lemma CategoryTheory.Limits.biprod.is_zero_iff
    [HasZeroMorphisms C] (A B : C)
    [HasBinaryBiproduct A B] : IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  . intro h
    simp only [IsZero.iff_id_eq_zero]
    constructor
    . rw [← cancel_mono (biprod.inl : _ ⟶ A ⊞ B)]
      apply h.eq_of_tgt
    . rw [← cancel_mono (biprod.inr : _ ⟶ A ⊞ B)]
      apply h.eq_of_tgt
  . rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    . apply hA.eq_of_tgt
    . apply hB.eq_of_tgt

namespace CochainComplex

section Preadditive

variable [Preadditive C] {F G : CochainComplex C ℤ}
  [∀ p, HasBinaryBiproduct (F.X (p+1)) (G.X p)] (φ : F ⟶ G)

open HomComplex

noncomputable def mappingCone : CochainComplex C ℤ where
  X i := F.X (i+1) ⊞ G.X i
  d i j := dite (i+1 = j) (fun h => -biprod.fst ≫ F.d _ _ ≫ biprod.inl +
      biprod.fst ≫ (Cochain.ofHom φ).v (i+1) j (by rw [add_zero, h]) ≫ biprod.inr +
      biprod.snd ≫ G.d _ _ ≫ biprod.inr) (fun _ => 0)
  shape i j (hij : i+1 ≠ j) := by simp only [dif_neg hij]
  d_comp_d' := by rintro i _ _ rfl rfl ; simp

namespace MappingCone

noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => (Cochain.ofHom (𝟙 F)).v p (q+1) (by linarith) ≫ biprod.inl)

noncomputable def inr : G ⟶ mappingCone φ :=
  Cocycle.homOf (Cocycle.mk
    (Cochain.mk (fun p q hpq => (Cochain.ofHom (𝟙 G)).v p q hpq ≫ biprod.inr)) 1 (zero_add 1) (by
      ext ⟨p, _, rfl⟩
      dsimp [mappingCone]
      simp only [δ_v 0 1 (zero_add 1) _ p _ rfl p (p+1) (by linarith) rfl, zero_add, ε_1,
        neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero, Cochain.mk_v,
        Cochain.ofHom_v, HomologicalComplex.id_f, id_comp, not_true, dite_eq_ite,
        ite_true, comp_add, comp_neg, biprod.inr_fst_assoc,
        zero_comp, neg_zero, add_zero, biprod.inr_snd_assoc, zero_add]))

noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fun p q hpq =>
    biprod.fst ≫ (Cochain.ofHom (𝟙 F)).v (p+1) q (by rw [add_zero, hpq]))) 2 (by linarith) (by
    ext ⟨p, q, hpq⟩
    obtain rfl : q = p + 1 + 1 := by linarith
    dsimp [mappingCone]
    simp only [δ_v 1 2 (by linarith) _ p (p+1+1) (by linarith) (p+1) (p+1) (by linarith) rfl,
      ε_succ, ε_1, Cochain.mk_v, Cochain.ofHom_v, HomologicalComplex.id_f, comp_id, not_true,
      neg_neg, dite_eq_ite, ite_true, add_comp, neg_comp, assoc,
      biprod.inl_fst, biprod.inr_fst, comp_zero, add_zero, smul_neg, one_smul, add_right_neg])

noncomputable def snd : Cochain (mappingCone φ) G 0 :=
  Cochain.mk (fun p q hpq => biprod.snd ≫ (Cochain.ofHom (𝟙 G)).v p q hpq)

@[reassoc (attr := simp)]
lemma inl_v_fst_v (p q : ℤ) (hpq : q+1 = p) :
    (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫
      (fst φ : Cochain (mappingCone φ) F 1).v q p hpq = 𝟙 _ := by
  subst hpq
  simp [inl, fst]

@[simp]
lemma inl_fst :
    (inl φ).comp (fst φ : Cochain (mappingCone φ) F 1) (neg_add_self 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_self 1) p (p-1) p rfl (by linarith)]

@[simp]
lemma inl_fst_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain F K d) (he : 1 + d = e) :
    (inl φ).comp ((fst φ : Cochain (mappingCone φ) F 1).comp γ he)
      (by rw [← he, neg_add_cancel_left]) = γ := by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_self 1) (by linarith) (by linarith), inl_fst,
    Cochain.id_comp]

@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p+(-1) = q) :
    (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0 := by
  subst hpq
  simp [inl, snd]

@[simp]
lemma inl_snd :
    (inl φ).comp (snd φ) (add_zero (-1)) = 0 := by
  ext ⟨p, q, hpq⟩
  simp [Cochain.comp_v _ _ (add_zero (-1)) p q q (by linarith) (by linarith)]

@[simp]
lemma inl_snd_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain G K d) (he : 0 + d = e) (hf : -1 + e = f) :
    (inl φ).comp ((snd φ).comp γ he) hf = 0 := by
  obtain rfl : e = d := by linarith
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, inl_snd, Cochain.zero_comp]

@[reassoc (attr := simp)]
lemma inr_f_fst_v (p q : ℤ) (hpq : p+1 = q) :
    (inr φ).f p ≫ (fst φ : Cochain (mappingCone φ) F 1).v p q hpq = 0 := by
  simp [inr, fst]

@[simp]
lemma inr_fst :
    (Cochain.ofHom (inr φ)).comp (fst φ : Cochain (mappingCone φ) F 1) (zero_add 1) = 0 := by
  ext ⟨p, q, hpq⟩
  simp [Cochain.comp_v _ _ (zero_add 1) p p q (by linarith) (by linarith)]

@[simp]
lemma inr_fst_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (inr φ)).comp ((fst φ : Cochain (mappingCone φ) F 1).comp γ he) hf = 0 := by
  obtain rfl : e = f := by linarith
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_fst, Cochain.zero_comp]

@[reassoc (attr := simp)]
lemma inr_f_snd_v (p : ℤ) :
    (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [inr, snd]

@[simp]
lemma inr_snd :
    (Cochain.ofHom (inr φ)).comp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G) := by aesop_cat

@[simp]
lemma inr_snd_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain G K d) (he : 0 + d = e) :
  (Cochain.ofHom (inr φ)).comp ((snd φ).comp γ (he))
    (show _ = d by rw [← he, zero_add, zero_add]) = γ := by
  obtain rfl : d = e := by linarith
  aesop_cat

lemma id (p q : ℤ) (hpq : p + 1 = q) :
  𝟙 ((mappingCone φ).X p) = (fst φ : Cochain (mappingCone φ) F 1).v p q hpq ≫
    (inl φ).v q p (by rw [← hpq, Int.add_neg_one, add_tsub_cancel_right]) +
      (snd φ).v p p (add_zero p) ≫ (inr φ).f p := by
  subst hpq
  simp [inl, inr, fst, snd, mappingCone]

lemma to_ext_iff {A : C} {n₁ : ℤ} (f g : A ⟶ (mappingCone φ).X n₁) (n₂ : ℤ) (h : n₁ + 1 = n₂)  :
    f = g ↔ f ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ h =
      g ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ h ∧
      f ≫ (snd φ).v n₁ n₁ (add_zero n₁) = g ≫ (snd φ).v n₁ n₁ (add_zero n₁) := by
  constructor
  . rintro rfl
    tauto
  . rintro ⟨h₁, h₂⟩
    rw [← cancel_mono (𝟙 _), id φ n₁ n₂ h]
    simp only [comp_add, reassoc_of% h₁, reassoc_of% h₂]

lemma from_ext_iff {A : C} {n₁ : ℤ} (f g : (mappingCone φ).X n₁ ⟶ A)
  (n₂ : ℤ) (h : n₁ + 1 = n₂) :
  f = g ↔ (inl φ).v n₂ n₁ (by rw [← h, add_neg_cancel_right]) ≫ f =
    (inl φ).v n₂ n₁ (by rw [← h, add_neg_cancel_right]) ≫ g ∧
    (inr φ).f n₁ ≫ f = (inr φ).f n₁ ≫ g := by
  constructor
  . rintro rfl
    tauto
  . rintro ⟨h₁, h₂⟩
    rw [← cancel_epi (𝟙 _), id φ n₁ n₂ h]
    simp only [add_comp, assoc, h₁, h₂]

lemma cochain_from_ext_iff {K : CochainComplex C ℤ} {n : ℤ} (γ₁ γ₂ : Cochain (mappingCone φ) K n)
    (n' : ℤ) (hn' : -1 + n = n') :
    γ₁ = γ₂ ↔ (inl φ : Cochain F (mappingCone φ) (-1)).comp γ₁ hn' =
      (inl φ : Cochain F (mappingCone φ) (-1)).comp γ₂ hn' ∧
      (Cochain.ofHom (inr φ)).comp γ₁ (zero_add n) =
        (Cochain.ofHom (inr φ)).comp γ₂ (zero_add n) := by
  constructor
  . rintro rfl
    tauto
  . rintro ⟨h₁, h₂⟩
    ext ⟨p, q, hpq⟩
    dsimp
    rw [from_ext_iff _ _ _ _ rfl]
    constructor
    . simpa only [Cochain.comp_v _ _ hn' (p+1) p q (by linarith) hpq]
        using Cochain.congr_v h₁ (p+1) q (by linarith)
    . simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using Cochain.congr_v h₂ p q hpq

@[reassoc]
lemma inl_v_d (n₁ n₂ n₃ : ℤ) (h₁₂ : n₁ + (-1) = n₂) (h₁₃ : n₃ + (-1) = n₁) :
    (inl φ).v n₁ n₂ h₁₂ ≫ (mappingCone φ).d n₂ n₁ =
      φ.f n₁ ≫ (inr φ).f n₁ - F.d n₁ n₃ ≫ (inl φ).v _ _ h₁₃ := by
  obtain rfl : n₁ = n₂ + 1 := by linarith
  obtain rfl : n₃ = n₂ + 1 + 1 := by linarith
  dsimp [mappingCone, inl, inr]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, id_comp, not_true, dite_eq_ite,
    ite_true, comp_add, comp_neg, biprod.inl_fst_assoc,
    biprod.inl_snd_assoc, zero_comp, add_zero]
  abel

@[reassoc (attr := simp 1100)]
lemma inr_f_d (n₁ n₂ : ℤ) :
    (inr φ).f n₁ ≫ (mappingCone φ).d n₁ n₂ = G.d n₁ n₂ ≫ (inr φ).f n₂ := by
  by_cases h : n₁ + 1 = n₂
  . dsimp [mappingCone, inr]
    subst h
    simp only [Cochain.ofHom_v, HomologicalComplex.id_f, id_comp, ComplexShape.up_Rel,
      not_true, dite_eq_ite, ite_true, comp_add, comp_neg,
      biprod.inr_fst_assoc, zero_comp, neg_zero, add_zero, biprod.inr_snd_assoc, zero_add]
  . rw [(mappingCone φ).shape _ _ h, G.shape _ _ h, zero_comp, comp_zero]

@[reassoc]
lemma d_fst_v (n₁ n₂ n₃ : ℤ) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃):
  (mappingCone φ).d n₁ n₂ ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₂ n₃ hn₃ =
    -(fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ hn₂ ≫ F.d n₂ n₃ := by
  subst hn₂
  simp [mappingCone, fst]

@[reassoc]
lemma d_snd_v (n₁ n₂ : ℤ) (hn₂ : n₁ + 1 = n₂) :
  (mappingCone φ).d n₁ n₂ ≫ (snd φ).v n₂ n₂ (add_zero n₂) =
    (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ hn₂ ≫ φ.f n₂ +
      (snd φ).v n₁ n₁ (add_zero n₁) ≫ G.d n₁ n₂ := by
  subst hn₂
  simp [mappingCone, fst, snd]

@[simp]
lemma inl_comp_diff :
  (inl φ).comp (Cochain.diff (mappingCone φ)) (neg_add_self 1) =
    Cochain.ofHom (φ ≫ inr φ) - (Cochain.diff F).comp (inl φ) (add_neg_self 1) := by
  ext p
  simp only [Cochain.comp_v _ _ (neg_add_self 1) p (p-1) p (by linarith) (by linarith),
    Cochain.diff_v, Cochain.sub_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
    Cochain.comp_v _ _ (add_neg_self 1) p (p+1) p (by linarith) (by linarith),
    inl_v_d φ p (p-1) (p+1) (by linarith) (by linarith)]

@[simp]
lemma inr_comp_diff :
  (Cochain.ofHom (inr φ)).comp (Cochain.diff (mappingCone φ)) (zero_add 1) =
    (Cochain.diff G).comp (Cochain.ofHom (inr φ)) (add_zero 1) := by aesop_cat

@[simp]
lemma diff_comp_fst :
  (Cochain.diff (mappingCone φ)).comp
    (fst φ : Cochain (mappingCone φ) F 1) (show 1 + 1 = 2 by rfl) =
      -(fst φ : Cochain (mappingCone φ) F 1).comp (Cochain.diff F) (show 1 + 1 = 2 by rfl) := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ (show 1 + 1 = 2 by rfl) p (p+1) q (by linarith) (by linarith),
    Cochain.diff_v, d_fst_v]

@[simp]
lemma diff_comp_snd :
  (Cochain.diff (mappingCone φ)).comp (snd φ) (add_zero 1) =
    (fst φ : Cochain (mappingCone φ) F 1).comp (Cochain.ofHom φ) (add_zero 1) +
      (snd φ).comp (Cochain.diff G) (zero_add 1) := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ (add_zero 1) p q q hpq (add_zero q),
    Cochain.comp_v _ _ (zero_add 1) p p q (add_zero p) hpq,
    Cochain.diff_v, Cochain.ofHom_v, d_snd_v _ _ _ hpq]

@[simp]
lemma δ_inl : δ (-1) 0 (inl φ) = Cochain.ofHom (φ ≫ inr φ) := by
  simp only [δ_eq (-1) 0 (neg_add_self 1), inl_comp_diff, Cochain.ofHom_comp,
    add_left_neg, ε_0, one_smul, sub_add_cancel]

@[simp]
lemma δ_snd : δ 0 1 (snd φ) =
    -(fst φ : Cochain (mappingCone φ) F 1).comp (Cochain.ofHom φ) (add_zero 1) := by
  simp only [δ_eq 0 1 (zero_add 1), zero_add, ε_1,
    diff_comp_snd, smul_add, neg_smul, one_smul, add_neg_cancel_comm_assoc]

attribute [irreducible] mappingCone inl inr fst snd

@[simps]
noncomputable def XIso (n i : ℤ) (hi : n + 1 = i) [HasBinaryBiproduct (F.X i) (G.X n)] :
  (mappingCone φ).X n ≅ F.X i ⊞ G.X n where
  hom := (fst φ : Cochain (mappingCone φ) F 1).v n i hi ≫ biprod.inl +
    (snd φ).v n n (add_zero n) ≫ biprod.inr
  inv := biprod.fst ≫ (inl φ).v i n (by linarith) + biprod.snd ≫ (inr φ).f n
  hom_inv_id := by simp [← id]
  inv_hom_id := by simp [← id]

lemma X_is_zero_iff (n : ℤ) :
    IsZero ((mappingCone φ).X n) ↔ IsZero (F.X (n+1)) ∧ IsZero (G.X n) := by
  rw [(XIso φ n (n+1) rfl).isZero_iff, biprod.is_zero_iff]

noncomputable def descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) : Cochain (mappingCone φ) K n :=
  (fst φ : Cochain (mappingCone φ) F 1).comp α (show 1 + m = n by rw [← h, add_comm]) +
    (snd φ).comp β (zero_add n)

lemma inl_descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) :
    (inl φ).comp (descCochain φ α β h) (by rw [← h, neg_add_cancel_comm_assoc]) = α := by
  dsimp only [descCochain]
  simp only [Cochain.comp_add, inl_fst_assoc, inl_snd_assoc, add_zero]

@[reassoc (attr := simp)]
lemma inl_v_descCochain_v {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n) (p₁ p₂ p₃ : ℤ)
      (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) :
    (inl φ).v p₁ p₂ h₁₂ ≫ (descCochain φ α β h).v p₂ p₃ h₂₃ =
        α.v p₁ p₃ (by rw [← h₂₃, ← h₁₂, ← h, add_comm m, add_assoc, neg_add_cancel_left]) := by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by linarith) p₁ p₂ p₃
    (by linarith) (by linarith)] using
      Cochain.congr_v (inl_descCochain φ α β h) p₁ p₃ (by linarith)

@[simp]
lemma inr_descCochain {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n) :
      (Cochain.ofHom (inr φ)).comp (descCochain φ α β h) (zero_add n) = β := by
  dsimp only [descCochain]
  simp only [Cochain.comp_add, inr_fst_assoc, inr_snd_assoc, zero_add]

@[reassoc (attr := simp)]
lemma inr_f_descCochain_v {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n) (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (inr φ).f p₁ ≫ (descCochain φ α β h).v p₁ p₂ h₁₂ = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (inr_descCochain φ α β h) p₁ p₂ (by linarith)

lemma δ_descCochain {K : CochainComplex C ℤ} {n m n' : ℤ} (α : Cochain F K m) (β : Cochain G K n)
  (h : m + 1 = n) (hn' : n+1 = n') :
  δ n n' (descCochain φ α β h) = (fst φ : Cochain (mappingCone φ) F 1).comp (δ m n α +
    ε (n+1) • (Cochain.ofHom φ).comp β (zero_add n)) (by rw [← hn', add_comm]) +
      (snd φ).comp (δ n n' β) (zero_add n') := by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, Cochain.comp_zsmul,
    δ_zero_cochain_comp _ _ _ hn', δ_snd, Cochain.neg_comp, smul_neg,
    δ_comp _ _ (show 1 + m = n by linarith) 2 n _ hn' rfl h, ε_succ,
    Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.zero_comp,
    Cocycle.δ_eq_zero, smul_zero, add_zero, neg_smul,
    Cochain.comp_neg, Cochain.comp_zsmul]
  abel

@[simps!]
noncomputable def descCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cocycle G K n)
    (h : m + 1 = n) (eq : δ m n α = ε n • (Cochain.ofHom φ).comp (β : Cochain G K n) (zero_add n)) :
    Cocycle (mappingCone φ) K n :=
  Cocycle.mk (descCochain φ α (β : Cochain G K n) h) (n+1) rfl
    (by simp only [δ_descCochain _ _ _ _ rfl, eq, ε_succ, neg_smul, add_right_neg,
      Cochain.comp_zero, Cocycle.δ_eq_zero, add_zero])

noncomputable def desc {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) : mappingCone φ ⟶ K :=
  Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_self 1)
    (by simp only [eq, Cochain.ofHom_comp, ε_0, Cocycle.ofHom_coe, one_smul]))

section

attribute [local simp] desc

@[reassoc (attr := simp)]
lemma inl_v_desc_f {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) (p₁ p₂ : ℤ) (h : p₁ + (-1) = p₂) :
    (inl φ : Cochain F (mappingCone φ) (-1)).v p₁ p₂ h ≫ (desc φ α β eq).f p₂ = α.v p₁ p₂ h := by
  aesop_cat

@[simp]
lemma inl_desc {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) :
    (inl φ : Cochain F (mappingCone φ) (-1)).comp
      (Cochain.ofHom (desc φ α β eq)) (add_zero (-1)) = α := by aesop_cat

@[reassoc (attr := simp)]
lemma inr_f_desc_f {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) (p : ℤ) :
    (inr φ).f p ≫ (desc φ α β eq).f p = β.f p := by aesop_cat

@[simp]
lemma inr_desc {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) :
    inr φ ≫ desc φ α β eq = β := by aesop_cat

end

noncomputable def descHomotopy {K : CochainComplex C ℤ} (f₁ f₂ : mappingCone φ ⟶ K)
    (γ₁ : Cochain F K (-2)) (γ₂ : Cochain G K (-1))
    (h₁ : (inl φ).comp (Cochain.ofHom f₁) (add_zero (-1)) =
      δ (-2) (-1) γ₁ + (Cochain.ofHom φ).comp γ₂ (zero_add (-1)) +
      (inl φ).comp (Cochain.ofHom f₂) (add_zero (-1)))
    (h₂ : Cochain.ofHom (inr φ ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)) :
  Homotopy f₁ f₂ := (Cochain.equivHomotopy f₁ f₂).symm (⟨descCochain φ γ₁ γ₂ (by linarith), by
    simp only [δ_descCochain _ _ _ _ (neg_add_self 1), neg_add_self, ε_0, one_smul,
      cochain_from_ext_iff _ _ _ _ (add_zero (-1))]
    constructor
    . simp only [h₁, Cochain.comp_add, inl_fst_assoc, inl_snd_assoc, add_zero]
    . simp only [Cochain.ofHom_comp] at h₂
      simp only [h₂, Cochain.comp_add, inr_fst_assoc, add_zero, inr_snd_assoc, zero_add]⟩)

end MappingCone

end Preadditive

end CochainComplex


#exit


open CategoryTheory Category Limits

#exit
import algebra.homology.quasi_iso
import algebra.homology.short_complex.pseudoelements
import for_mathlib.algebra.homology.hom_complex_shift
import category_theory.triangulated.triangulated
import for_mathlib.algebra.homology.homological_complex_limits

noncomputable theory
open category_theory category_theory.category category_theory.limits
  category_theory.pretriangulated

omit φ

namespace mappingCone

include φ


@[simp, priority 1100]
lemma inr_δ : inr φ ≫ δ φ = 0 :=
begin
  ext n,
  dsimp only [δ],
  simp only [homological_complex.comp_f, cocycle.hom_of_f, cochain.neg_v,
    cocycle.right_shift_coe, δ_as_cocycle_coe, homological_complex.zero_f_apply,
    hom_complex.cochain.right_shift_v _ 1 0 (zero_add 1).symm n n (by linarith) _ rfl,
    preadditive.neg_comp, preadditive.comp_neg, inr_fst_assoc, zero_comp, neg_zero],
end

@[simp]
lemma inl_δ :
  (inl φ).comp (cochain.of_hom (δ φ)) (add_zero _).symm =
  -(cochain.of_hom (𝟙 F)).right_shift _ _ (add_neg_self 1).symm :=
begin
  /- TODO deduplicate the proof of this and the lemma above -/
  ext p q hpq,
  simp only [cochain.comp_zero_cochain, cochain.of_hom_v, δ,
    cocycle.hom_of_f, cocycle.right_shift_coe, δ_as_cocycle_coe,
    hom_complex.cochain.right_shift_v _ 1 0 (zero_add 1).symm q q (by linarith) p (by linarith),
    hom_complex.cochain.right_shift_v _ 1 (-1) (add_neg_self 1).symm p q hpq p (by linarith),
    cochain.neg_v, preadditive.comp_neg, preadditive.neg_comp, cochain.neg_v,
    inl_fst_assoc, homological_complex.id_f, id_comp],
end

variable {φ}


variable (φ)

lemma of_d_eq : cochain.of_d (mappingCone φ) =
  -((fst φ : cochain (mappingCone φ) F 1).comp (cochain.of_d F)
    int.two_eq_one_add_one).comp (inl φ) int.one_eq_two_add_neg_one +
  ((fst φ : cochain (mappingCone φ) F 1).comp (cochain.of_hom φ) (add_zero 1).symm).comp
      (cochain.of_hom (inr φ)) (add_zero 1).symm +
  ((snd φ).comp (cochain.of_d G) (zero_add 1).symm).comp
    (cochain.of_hom (inr φ)) (add_zero 1).symm :=
begin
  ext p q hpq,
  simp only [from_ext_iff _ _ _ hpq,
    cochain.of_d_v, inl_d φ p q (q+1) (by linarith) (by linarith), cochain.add_v,
    preadditive.comp_add, cochain.comp_assoc_of_third_is_zero_cochain, cochain.comp_zero_cochain,
    cochain.of_hom_v, inl_fst_assoc, cochain.neg_v, inl_snd_assoc, zero_comp,
    cochain.comp_assoc_of_first_is_zero_cochain, cochain.zero_cochain_comp, preadditive.comp_neg,
    cochain.comp_v _ _ int.one_eq_two_add_neg_one p (q+1) q (by linarith) (by linarith),
    cochain.comp_v _ _ _root_.int.two_eq_one_add_one p q (q+1) hpq rfl, assoc, add_zero,
    inl_fst_assoc, inr_d, inr_fst_assoc, neg_zero, zero_add, inr_snd_assoc, sub_eq_neg_add,
    eq_self_iff_true, and_true],
end

variable {φ}

lemma to_decomposition {A : C} {n : ℤ} (f : A ⟶ (mappingCone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  ∃ (x : A ⟶ F.X n') (y : A ⟶ G.X n), f = x ≫
    (inl φ : cochain F (mappingCone φ) (-1)).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right])
      + y ≫ (inr φ).f n :=
begin
  refine ⟨f ≫ (fst φ : cochain (mappingCone φ) F 1).v _ _ (by linarith), f ≫ (snd φ).v n n (by linarith), _⟩,
  have h := f ≫= id φ n n' h,
  rw comp_id at h,
  nth_rewrite 0 ← h,
  simp only [preadditive.comp_add, assoc],
end

lemma cochain_ext {K : cochain_complex C ℤ} {m m' : ℤ}
  (y₁ y₂ : cochain (mappingCone φ) K m) (hm' : m = m'+1) :
  y₁ = y₂ ↔ (inl φ).comp y₁ (show m' = -1+m, by rw [hm', neg_add_cancel_comm_assoc]) =
    (inl φ).comp y₂ (show m' = -1+m, by rw [hm', neg_add_cancel_comm_assoc]) ∧
    (cochain.of_hom (inr φ)).comp y₁ (zero_add m).symm =
      (cochain.of_hom (inr φ)).comp y₂ (zero_add m).symm :=
begin
  split,
  { rintro rfl,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    ext p q hpq,
    replace h₁ := cochain.congr_v h₁ (p+1) q (by linarith),
    replace h₂ := cochain.congr_v h₂ p q (by linarith),
    simp only [cochain.comp_v _ _ (show m' = -1+m, by linarith) (p+1) p q (by linarith) hpq] at h₁,
    simp only [cochain.zero_cochain_comp, cochain.of_hom_v] at h₂,
    rw [from_ext_iff _ _ (p+1) rfl, h₁, h₂],
    tauto, },
end

lemma cochain_ext' {K : cochain_complex C ℤ} {m m' : ℤ}
  (y₁ y₂ : cochain K (mappingCone φ) m) (hm' : m' = m+1) :
  y₁ = y₂ ↔ y₁.comp (fst φ : cochain (mappingCone φ) F 1) hm' =
    y₂.comp (fst φ : cochain (mappingCone φ) F 1) hm' ∧
    y₁.comp (snd φ) (add_zero m).symm =
      y₂.comp (snd φ) (add_zero m).symm :=
begin
  split,
  { rintro rfl,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    ext p q hpq,
    replace h₁ := cochain.congr_v h₁ p (q+1) (by linarith),
    simp only [cochain.comp_v _ _ hm' p q (q+1) (by linarith) (by linarith)] at h₁,
    replace h₂ := cochain.congr_v h₂ p q (by linarith),
    simp only [cochain.comp_zero_cochain] at h₂,
    rw [to_ext_iff _ _ (q+1) rfl, h₂, h₁],
    tauto, },
end

variable (φ)

@[simp]
def ι' := (homotopy_category.quotient _ _).map (inr φ)

def δ' : (homotopy_category.quotient _ _).obj (mappingCone φ) ⟶
  ((homotopy_category.quotient _ _).obj F)⟦(1 : ℤ)⟧ :=
(homotopy_category.quotient _ _).map (δ φ)


lemma δ_desc_cochain {K : cochain_complex C ℤ} {n m n' : ℤ} (α : cochain F K m) (β : cochain G K n)
  (h : m+1=n) (hn' : n+1 = n') : hom_complex.δ n n' (desc_cochain φ α β h) =
  (fst φ : cochain (mappingCone φ) F 1).comp (hom_complex.δ m n α +
    ε (n+1) • (cochain.of_hom φ).comp β (zero_add n).symm) (by rw [← hn', add_comm]) +
    (snd φ).comp (hom_complex.δ n n' β) (zero_add n').symm :=
begin
  ext p q hpq,
  simp only [from_ext_iff _ _ (p+1) rfl,
    δ_v n n' hn' _ p q hpq (q-1) (p+1) rfl rfl, cochain.add_v,
    cochain.comp_v _ _ (show n' = 1+n, by linarith) p (p+1) q rfl (by linarith),
    zero_add, neg_zero, add_zero, ε_succ, neg_smul, preadditive.comp_add,
    inl_desc_cochain_v_assoc, preadditive.comp_neg, linear.comp_smul, cochain.neg_v,
    cochain.zsmul_v, cochain.zero_cochain_comp, cochain.of_hom_v, inl_fst_assoc,
    inl_snd_assoc, zero_comp, inr_desc_cochain_v_assoc, inr_d_assoc, inr_desc_cochain_v,
    inr_fst_assoc, smul_zero, inr_snd_assoc, smul_sub, show m = n-1, by linarith,
    inl_d_assoc φ p (p+1) (p+2) (by linarith) (by linarith),
    δ_v m n h _ (p+1) q (by linarith) (q-1) (p+2) rfl (by linarith),
    preadditive.sub_comp, assoc, inl_desc_cochain_v, ε_sub, ε_1, mul_neg, mul_one, neg_neg],
  exact ⟨by abel, rfl⟩,
end

def desc_cocycle {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cocycle G K n)
  (h : m+1=n) (eq : hom_complex.δ m n α =
    ε n • (cochain.of_hom φ).comp (β : cochain G K n) (zero_add n).symm) :
  cocycle (mappingCone φ) K n :=
cocycle.mk (desc_cochain φ α (β : cochain G K n) h) (n+1) rfl
  (by simp only [δ_desc_cochain φ α (β : cochain G K n) h rfl, ε_add, ε_1, mul_neg, mul_one, eq,
    neg_smul, ← sub_eq_add_neg, sub_self, cochain.comp_zero, zero_add,
    cocycle.δ_eq_zero, cochain.comp_zero])

@[simp]
lemma desc_cocycle_coe {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cocycle G K n)
  (h : m+1=n) (eq : hom_complex.δ m n α = ε n • (cochain.of_hom φ).comp β.1 (zero_add n).symm) :
(desc_cocycle φ α β h eq : cochain (mappingCone φ) K n) =
  desc_cochain φ α β h := rfl

def desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  mappingCone φ ⟶ K :=
cocycle.hom_of (desc_cocycle φ α (cocycle.of_hom β) (neg_add_self 1)
  (by simp only [eq, ε_0, cochain.of_hom_comp, subtype.val_eq_coe, cocycle.of_hom_coe, one_zsmul]))

@[simp, reassoc]
lemma inl_desc_v {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (p q : ℤ) (hpq : q = p + (-1)) :
  (inl φ).v p q hpq ≫ (desc φ α β eq).f q = α.v p q hpq :=
begin
  dsimp only [desc],
  simp only [cocycle.hom_of_f, desc_cocycle_coe, inl_desc_cochain_v],
end

@[simp]
lemma inl_desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  (inl φ).comp (cochain.of_hom (desc φ α β eq)) (add_zero _).symm = α :=
by tidy

@[simp, reassoc]
lemma inr_desc_f {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (n : ℤ):
  (inr φ).f n ≫ (desc φ α β eq).f n = β.f n :=
begin
  dsimp only [desc],
  simp only [cocycle.hom_of_f, desc_cocycle_coe, cocycle.of_hom_coe,
    inr_desc_cochain_v, cochain.of_hom_v],
end

@[simp, reassoc]
lemma inr_desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  inr φ ≫ desc φ α β eq = β :=
begin
  dsimp only [desc],
  ext n,
  simp only [homological_complex.comp_f, cocycle.hom_of_f, desc_cocycle_coe,
    cocycle.of_hom_coe, inr_desc_cochain_v, cochain.of_hom_v],
end

lemma desc_f {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (n n' : ℤ) (hn' : n' = n+1) :
  (desc φ α β eq).f n =
    (fst φ : cochain (mappingCone φ) F 1).v n n' hn' ≫
      α.v n' n (by { rw [hn', int.add_neg_one, add_tsub_cancel_right]}) +
      (snd φ).v n n (add_zero n).symm ≫ β.f n :=
by simp only [from_ext_iff _ _ _ hn', add_zero, inl_desc_v, preadditive.comp_add,
  inl_fst_assoc, inl_snd_assoc, zero_comp, eq_self_iff_true, inr_desc_f,
  inr_fst_assoc, inr_snd_assoc, zero_add, and_self]

def desc_homotopy {K : cochain_complex C ℤ} (f₁ f₂ : mappingCone φ ⟶ K)
  (γ₁ : cochain F K (-2)) (γ₂ : cochain G K (-1))
  (h₁ : (inl φ).comp (cochain.of_hom f₁) (add_zero (-1)).symm =
    hom_complex.δ (-2) (-1) γ₁ + (cochain.of_hom φ).comp γ₂ (zero_add _).symm +
    (inl φ).comp (cochain.of_hom f₂) (add_zero (-1)).symm)
  (h₂ : cochain.of_hom (inr φ ≫ f₁) =
    hom_complex.δ (-1) 0 γ₂ + cochain.of_hom (inr φ ≫ f₂)) :
  homotopy f₁ f₂ :=
(equiv_homotopy _ _).symm
begin
  refine ⟨desc_cochain _ γ₁ γ₂ (by linarith), _⟩,
  rw [δ_desc_cochain φ γ₁ γ₂ (by linarith) (neg_add_self 1),
    cochain_ext _ _ (show (0 : ℤ) = -1 +1 , by linarith)],
  split,
  { rw [cochain.comp_add, h₁],
    nth_rewrite 0 cochain.comp_add,
    simp only [← cochain.comp_assoc _ _ _ (neg_add_self 1).symm (add_neg_self 1).symm
        (show (-1 : ℤ) = (-1) +1 + (-1), by linarith), inl_comp_fst, cochain.id_comp,
        neg_add_self, ε_0, one_smul, ← cochain.comp_assoc_of_second_is_zero_cochain,
        inl_comp_snd, cochain.zero_comp, add_zero], },
  { rw [cochain.comp_add, ← cochain.of_hom_comp, ← cochain.of_hom_comp, h₂],
    nth_rewrite 0 cochain.comp_add,
    simp only [← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      inr_comp_fst, cochain.zero_comp, zero_add, inr_comp_snd,
      cochain.id_comp], },
end

def lift_cochain {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m) :
  cochain K (mappingCone φ) n :=
α.comp (inl φ) (by linarith) + β.comp (cochain.of_hom (inr φ)) (by linarith)

@[simp, reassoc]
lemma lift_cochain_fst_v {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m) (p₁ p₂ p₃ : ℤ)
  (h₁₂ : p₂ = p₁ + n) (h₂₃ : p₃ = p₂ + 1) :
  (lift_cochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ : cochain (mappingCone φ) F 1).v p₂ p₃ h₂₃ =
    α.v p₁ p₃ (by rw [h₂₃, h₁₂, ← h, add_assoc])  :=
begin
  dsimp only [lift_cochain],
  simp only [cochain.add_v, add_zero, cochain.comp_zero_cochain, cochain.of_hom_v,
    subtype.val_eq_coe, preadditive.add_comp, assoc, inr_fst, comp_zero,
    cochain.comp_v _ _ (show n = m+(-1), by linarith) p₁ p₃ p₂ (by linarith) (by linarith),
    inl_fst, comp_id],
end

@[simp, reassoc]
lemma lift_cochain_snd_v {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m)
    (p₁ p₂ : ℤ) (h₁₂ : p₂ = p₁ + n) :
  (lift_cochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₂ (add_zero p₂).symm =
    β.v p₁ p₂ h₁₂ :=
begin
  dsimp [lift_cochain],
  simp only [cochain.comp_zero_cochain, cochain.of_hom_v, preadditive.add_comp, assoc,
    cochain.comp_v _ _ (show n = m+(-1), by linarith) p₁ (p₁+m) p₂ rfl (by linarith),
    inr_snd, comp_id, add_left_eq_self, inl_snd, comp_zero],
end

@[simp]
lemma lift_cochain_fst {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m)  :
  (lift_cochain φ α β h).comp (fst φ : cochain (mappingCone φ) F 1) h.symm = α :=
begin
  ext p q hpq,
  simp only [cochain.comp_v _ _ h.symm p (p+n) q rfl (by linarith), lift_cochain_fst_v],
end

@[simp]
lemma lift_cochain_snd {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m)  :
  (lift_cochain φ α β h).comp (snd φ) (add_zero n).symm = β :=
begin
  ext p q hpq,
  simp only [cochain.comp_zero_cochain, lift_cochain_snd_v],
end

lemma δ_lift_cochain {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m) (m' : ℤ) (hm' : m = m'+(-1)) :
  hom_complex.δ n m (lift_cochain φ α β h) =
    -(hom_complex.δ m m' α).comp (inl φ) hm' +
    (hom_complex.δ n m β + α.comp (cochain.of_hom φ) (add_zero m).symm).comp
      (cochain.of_hom (inr φ)) (add_zero m).symm :=
begin
  ext p q hpq,
  simp only [to_ext_iff _ _ (q+1) rfl, δ_v n m h _ p q hpq _ _ rfl rfl, cochain.add_v,
    cochain.comp_v _ _ hm' p (q+1) q (by linarith) (by linarith),
    δ_v m m' (by linarith) _ p  (q+1) (by linarith) q (p+1) (by linarith) rfl,
    cochain.neg_v, cochain.comp_zero_cochain, cochain.of_hom_v,
    preadditive.add_comp, assoc, preadditive.zsmul_comp, lift_cochain_fst_v, inl_fst, inr_fst,
    preadditive.neg_comp, preadditive.comp_neg, comp_zero, smul_zero, add_zero,
    d_fst φ (q-1) q (q+1) (by linarith) rfl, lift_cochain_fst_v_assoc, comp_id, neg_add, h,
    ε_succ, neg_smul, neg_neg, inl_snd, neg_zero, zero_add, d_snd φ (q-1) q (by linarith),
    preadditive.comp_add, lift_cochain_snd_v_assoc, inr_snd, lift_cochain_snd_v],
  refine ⟨rfl, _⟩,
  have : ∀ (x y z : K.X p ⟶ G.X q), x +y +z = y+z +x := λ x y z, by abel,
  apply this,
end

def lift_cocycle {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cocycle K F m) (β : cochain K G n) (h : n+1=m)
  (hαβ : hom_complex.δ n m β + (α : cochain K F m).comp (cochain.of_hom φ) (add_zero m).symm = 0) :
  cocycle K (mappingCone φ) n :=
cocycle.mk (lift_cochain φ (α : cochain K F m) β h) _ h
  (by simp only [δ_lift_cochain φ _ _ h (m+1) (by linarith), hαβ, cochain.zero_comp, add_zero,
    cocycle.δ_eq_zero, neg_zero])

@[simp]
def lift_cocycle_coe {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cocycle K F m) (β : cochain K G n) (h : n+1=m)
  (hαβ : hom_complex.δ n m β + (α : cochain K F m).comp (cochain.of_hom φ) (add_zero m).symm = 0) :
  (lift_cocycle φ α β h hαβ : cochain K (mappingCone φ) n) =
    lift_cochain φ (α : cochain K F m) β h := rfl

def lift {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
   K ⟶ mappingCone φ :=
cocycle.hom_of (lift_cocycle φ α β (zero_add 1) hαβ)

@[simp, reassoc]
lemma lift_fst_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0)
  (n n' : ℤ) (hnn' : n' = n+1) :
    (lift φ α β hαβ).f n ≫
      (fst φ : cochain (mappingCone φ) F 1).v n n' hnn' = (α : cochain K F 1).v n n' hnn' :=
begin
  dsimp only [lift],
  simp only [cocycle.hom_of_f, lift_cocycle_coe, lift_cochain_fst_v],
end

@[simp]
lemma lift_fst {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
  (cochain.of_hom (lift φ α β hαβ)).comp
    (fst φ : cochain (mappingCone φ) F 1) (zero_add 1).symm =
      (α : cochain K F 1) :=
begin
  ext p q hpq,
  simp only [cochain.zero_cochain_comp, cochain.of_hom_v, lift_fst_f],
end

@[simp, reassoc]
lemma lift_snd_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) (n : ℤ) :
  (lift φ α β hαβ).f n ≫ (snd φ).v n n (add_zero n).symm =
    β.v n n (add_zero n).symm :=
begin
  dsimp only [lift],
  simp only [cocycle.hom_of_f, lift_cocycle_coe, lift_cochain_snd_v],
end

@[simp]
lemma lift_snd {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
  (cochain.of_hom (lift φ α β hαβ)).comp
    (snd φ) (add_zero 0).symm = β :=
begin
  dsimp only [lift],
  simp only [cocycle.cochain_of_hom_hom_of_eq_coe, lift_cocycle_coe, lift_cochain_snd],
end

lemma lift_desc_f {K L : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0)
  (α' : cochain F L (-1)) (β' : G ⟶ L) (eq : hom_complex.δ (-1) 0 α' = cochain.of_hom (φ ≫ β'))
  (n n' : ℤ) (hnn' : n' = n+1) :
  (lift φ α β hαβ).f n ≫ (desc φ α' β' eq).f n =
    (α : cochain K F 1).v n n' hnn' ≫ α'.v n' n (by { rw [hnn', int.add_neg_one, add_tsub_cancel_right], }) +
      β.v n n (add_zero n).symm ≫ β'.f n :=
begin
  rw [← id_comp ((desc φ α' β' eq).f n), ← id φ _ _ hnn'],
  simp only [preadditive.add_comp, assoc, inl_desc_v, inr_desc_f, preadditive.comp_add,
    lift_fst_f_assoc, lift_snd_f_assoc],
end

lemma lift_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) (n n' : ℤ)
    (hn' : n' = n+1) :
    (lift φ α β hαβ).f n = (α : cochain K F 1).v n n' hn' ≫
      (inl φ).v n' n (by rw [hn', int.add_neg_one, add_tsub_cancel_right]) +
    β.v n n (add_zero n).symm ≫ (inr φ).f n :=
by simp only [to_ext_iff _ _ _ hn', add_zero, lift_fst_f, preadditive.add_comp, assoc,
  inl_fst, comp_id, inr_fst, comp_zero, eq_self_iff_true, lift_snd_f, inl_snd,
  inr_snd, zero_add, and_self]

def lift_homotopy {K : cochain_complex C ℤ} (f₁ f₂ : K ⟶ mappingCone φ)
  (γ₁ : cochain K F 0) (γ₂ : cochain K G (-1))
  (h₁ : (cochain.of_hom f₁).comp (fst φ :
    cochain (mappingCone φ) F 1) (zero_add 1).symm = -hom_complex.δ 0 1 γ₁ +
      (cochain.of_hom f₂).comp (fst φ : cochain (mappingCone φ) F 1) (zero_add 1).symm)
  (h₂ : (cochain.of_hom f₁).comp (snd φ) (add_zero 0).symm =
    hom_complex.δ (-1) 0 γ₂ + γ₁.comp (cochain.of_hom φ) (zero_add 0).symm +
    (cochain.of_hom f₂).comp (snd φ) (add_zero 0).symm) :
  homotopy f₁ f₂ :=
(equiv_homotopy _ _).symm
begin
  refine ⟨lift_cochain φ γ₁ γ₂ (neg_add_self 1), _⟩,
  simp only [δ_lift_cochain φ _ _ _ 1 (show (0 : ℤ) = 1 +(-1), by linarith),
    cochain_ext' _ _ (zero_add 1).symm],
  split,
  { simp only [add_zero, cochain.add_comp, cochain.neg_comp,
      cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst,
      cochain.comp_zero,
      cochain.comp_assoc _ _ _ (add_neg_self 1).symm (neg_add_self 1).symm
      (show (1 : ℤ) = 1+(-1)+1, by linarith),
      inl_comp_fst, cochain.comp_id, h₁], },
  { simp only [zero_add, neg_zero, cochain.add_comp, cochain.comp_assoc_of_third_is_zero_cochain,
      cochain.neg_comp, inl_comp_snd, cochain.comp_zero, inr_comp_snd, cochain.comp_id, h₂], },
end

section

variables {K₁ K₂ L₁ L₂ : cochain_complex C ℤ}
  [∀ p, has_binary_biproduct (K₁.X (p+1)) (L₁.X p)]
  [∀ p, has_binary_biproduct (K₂.X (p+1)) (L₂.X p)]
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (τ₁ : K₁ ⟶ K₂) (τ₂ : L₁ ⟶ L₂) (comm : f₁ ≫ τ₂ = τ₁ ≫ f₂)

include comm

def map : mappingCone f₁ ⟶ mappingCone f₂ :=
desc f₁ ((cochain.of_hom τ₁).comp (inl f₂) (zero_add _).symm)
  (τ₂ ≫ inr f₂)
begin
  rw [δ_comp_of_first_is_zero_cochain _ _ _ (neg_add_self 1), δ_inl,
    cocycle.δ_cochain_of_hom, cochain.zero_comp, smul_zero, add_zero, cochain.of_hom_comp f₂,
    ← assoc f₁, ← cochain.of_hom_comp, ← cochain.of_hom_comp, ← assoc, comm],
end

lemma inr_comp_map :
  inr f₁ ≫ map _ _ _ _ comm =
    τ₂ ≫ inr f₂ :=
begin
  apply hom_complex.cochain.of_hom_injective,
  rw cochain_ext' _ _ (zero_add 1).symm,
  dsimp only [map],
  split,
  { simp only [inr_desc, cochain.of_hom_comp,
      cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst,
      inr_fst], },
  { simp only [inr_desc, cochain.of_hom_comp, inr_snd,
      cochain.comp_assoc_of_third_is_zero_cochain, inr_comp_snd], },
end

lemma map_comp_δ :
  map _ _ _ _ comm ≫ δ f₂ =
  δ f₁ ≫ τ₁⟦1⟧' :=
begin
  apply hom_complex.cochain.of_hom_injective,
  rw cochain_ext _ _(neg_add_self 1).symm,
  dsimp only [map],
  split,
  { simp only [cochain.of_hom_comp, ← hom_complex.cochain.comp_assoc_of_second_is_zero_cochain,
      inl_desc, hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      inl_δ, cochain.comp_neg, cochain.of_hom_comp],
    ext p q hpq,
    have hp : p = q+1 := by linarith,
    subst hp,
    simp only [cochain.neg_v, cochain.zero_cochain_comp, cochain.of_hom_v,
      cochain.neg_comp, cochain.comp_zero_cochain, shift_functor_map_f', neg_inj],
    erw cochain.right_shift_v (cochain.of_hom _) 1 (-1)
      (by linarith) (q+1) q (by linarith) (q+1) (by linarith),
    erw cochain.right_shift_v (cochain.of_hom _) 1 (-1)
      (by linarith) (q+1) q (by linarith) (q+1) (by linarith),
    simp only [shift_functor_obj_X_iso, cochain.of_hom_v, homological_complex.id_f,
      homological_complex.X_iso_of_eq_refl, id_comp],
    dsimp [iso.refl],
    rw [comp_id, id_comp], },
  { rw [cochain.of_hom_comp, ← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      ← cochain.of_hom_comp, inr_desc, ← cochain.of_hom_comp, assoc,
      inr_δ, comp_zero, cochain.of_hom_zero, ← cochain.of_hom_comp, ← assoc,
      inr_δ, zero_comp, cochain.of_hom_zero], },
end

end

section

variables {K L : cochain_complex C ℤ} (f : K ⟶ L) {D : Type*} [category D] [preadditive D]
  [∀ p, has_binary_biproduct (K.X (p+1)) (L.X p)] (Φ : C ⥤ D) [functor.additive Φ]
  [∀ p, has_binary_biproduct (((Φ.map_homological_complex (complex_shape.up ℤ)).obj K).X (p + 1))
    (((Φ.map_homological_complex (complex_shape.up ℤ)).obj  L).X p)]

@[simps]
def map_iso : (Φ.map_homological_complex _).obj (mappingCone f) ≅
  mappingCone ((Φ.map_homological_complex _).map f) :=
{ hom := mappingCone.lift _ (cocycle.map (mappingCone.fst f) Φ)
    ((mappingCone.snd f).map Φ) (by simp),
  inv := mappingCone.desc _ ((mappingCone.inl f).map Φ)
      ((Φ.map_homological_complex _).map (mappingCone.inr f)) (by simp),
  hom_inv_id' := begin
    ext n,
    simpa only [homological_complex.comp_f, homological_complex.id_f,
      lift_desc_f _ _ _ _ _ _ _ n (n+1) rfl, cocycle.map_coe, cochain.map_v,
      functor.map_homological_complex_map_f, ← Φ.map_comp, ← Φ.map_add,
      mappingCone.id, Φ.map_id],
  end,
  inv_hom_id' := hom_complex.cochain.of_hom_injective begin
    ext n,
    simp only [cochain.of_hom_comp, cochain.comp_zero_cochain, cochain.of_hom_v,
      homological_complex.id_f, from_ext_iff _ _ (n+1) rfl, to_ext_iff _ _ (n+1) rfl,
      assoc, lift_fst_f, cocycle.map_coe, cochain.map_v, inl_desc_v_assoc, id_comp,
      inl_fst, inr_desc_f_assoc, functor.map_homological_complex_map_f, inr_fst,
      lift_snd_f, inl_snd, inr_snd, ← Φ.map_comp, Φ.map_zero, Φ.map_id],
    tauto,
  end, }

end

end mappingCone

end preadditive

section abelian

open hom_complex

variables [abelian C] {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)

include ex

lemma degreewise_exact (n : ℤ) :
  (S.map (homological_complex.eval C (complex_shape.up ℤ) n)).short_exact :=
ex.map_of_exact (homological_complex.eval C (complex_shape.up ℤ) n)

def from_mappingCone_of_ses : mappingCone S.f ⟶ S.X₃ :=
mappingCone.desc S.f 0 S.g (by simp)

@[simp, reassoc]
lemma inr_from_mappingCone_of_ses (n : ℤ) :
  (mappingCone.inr S.f).f n ≫ (from_mappingCone_of_ses ex).f n = S.g.f n :=
begin
  dsimp only [from_mappingCone_of_ses],
  simp only [mappingCone.inr_desc_f],
end

@[simp, reassoc]
lemma inl_from_mappingCone_of_ses (p q : ℤ) (hpq : q = p + (-1)) :
  (mappingCone.inl S.f).v p q hpq ≫ (from_mappingCone_of_ses ex).f q = 0 :=
begin
  dsimp only [from_mappingCone_of_ses],
  simp only [mappingCone.inl_desc_v, cochain.zero_v],
end

@[simp, reassoc]
lemma inr_mappingCone_comp_from_mappingCone_of_ses :
  mappingCone.inr S.f ≫ from_mappingCone_of_ses ex = S.g :=
begin
  ext n : 2,
  simp only [homological_complex.comp_f, inr_from_mappingCone_of_ses],
end

instance from_mappingCone_of_ses_quasi_iso : quasi_iso (from_mappingCone_of_ses ex) :=
⟨λ n, begin
  rw is_iso_homology_map_iff_short_complex_quasi_iso'
    (from_mappingCone_of_ses ex) (show (n-1)+1=n, by linarith) rfl,
  change is_iso _,
  haveI : ∀ (n : ℤ), mono (S.f.f n) :=
    λ n, (ex.map_of_exact (homological_complex.eval _ _ n)).mono_f,
  rw is_iso_iff_mono_and_epi,
  split,
  { rw short_complex.mono_homology_map_iff,
    dsimp,
    intros A x₂ hxy z hz,
    obtain ⟨x, y, rfl⟩ := mappingCone.to_decomposition x₂ _ rfl,
    simp only [preadditive.add_comp, assoc, mappingCone.inr_d, preadditive.comp_sub,
      mappingCone.inl_d S.f n (n+1) (n+1+1) (by linarith) (by linarith)] at hxy,
    obtain ⟨hx, hy⟩ := (mappingCone.to_ext_iff _ _ _ rfl).mp hxy,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mappingCone.inr_fst,
      comp_zero, mappingCone.inl_fst, comp_id, zero_sub, add_zero, zero_comp, neg_eq_zero] at hx,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mappingCone.inr_snd, comp_id,
      mappingCone.inl_snd, comp_zero, sub_zero, zero_comp, ← eq_neg_iff_add_eq_zero] at hy,
    clear hxy,
    simp only [preadditive.add_comp, assoc, inr_from_mappingCone_of_ses,
      inl_from_mappingCone_of_ses, comp_zero, zero_add] at hz,
    haveI : epi (S.g.f (n-1)) := (ex.map_of_exact (homological_complex.eval _ _ _)).epi_g,
    obtain ⟨A', π, hπ, z', hz'⟩ := abelian.pseudo_surjective_of_epi' (S.g.f (n-1)) z,
    have ex' := (ex.map_of_exact (homological_complex.eval _ _ n)),
    haveI := ex'.mono_f,
    let w : A' ⟶ S.X₁.X n := ex'.exact.lift (π ≫ y - z' ≫ S.X₂.d _ _) begin
      dsimp,
      simp only [preadditive.sub_comp, assoc, hz, reassoc_of hz',
        homological_complex.hom.comm, sub_self],
    end,
    have hw : w ≫ S.f.f n = _ := ex'.exact.lift_f _ _,
    refine ⟨A', π, hπ, w ≫ (mappingCone.inl S.f).v n (n-1) (show n-1 = n+(-1), by refl) + z' ≫ (mappingCone.inr S.f).f (n-1),
      (mappingCone.to_ext_iff _ _ _ rfl).mpr ⟨_, _⟩⟩,
    { simp only [assoc, preadditive.add_comp, mappingCone.inr_fst, comp_zero, add_zero,
        mappingCone.inl_fst, comp_id, mappingCone.inr_d_assoc,
        mappingCone.inl_d_assoc S.f (n-1) n (n+1) (by refl) (by linarith),
        preadditive.sub_comp, preadditive.comp_sub, ← cancel_mono (S.f.f (n+1)), zero_comp],
      simp only [← S.f.comm, reassoc_of hw, preadditive.sub_comp, assoc, homological_complex.d_comp_d,
        comp_zero, sub_zero, zero_sub, hy, preadditive.comp_neg], },
    { simp only [assoc, preadditive.comp_add, preadditive.add_comp, mappingCone.inl_snd, comp_zero,
        zero_add, mappingCone.inr_snd, comp_id, mappingCone.inr_d_assoc, preadditive.comp_sub,
        preadditive.sub_comp, hw,
        mappingCone.inl_d S.f (n-1) n (n+1) (show n-1 = n+(-1), by refl) (by linarith)],
        abel, }, },
  { rw short_complex.epi_homology_map_iff,
    dsimp,
    intros A z hz,
    haveI : epi (S.g.f n) := (ex.map_of_exact (homological_complex.eval _ _ _)).epi_g,
    obtain ⟨A', π, hπ, y, hy⟩ := abelian.pseudo_surjective_of_epi' (S.g.f n) z,
    have ex' := (ex.map_of_exact (homological_complex.eval _ _ (n+1))),
    haveI := ex'.mono_f,
    let x : A' ⟶ S.X₁.X (n+1) := ex'.exact.lift (y ≫ S.X₂.d _ _) begin
      dsimp,
      simp only [assoc, ← S.g.comm, ← reassoc_of hy, hz, comp_zero],
    end,
    have hx : x ≫ S.f.f (n+1) = _ := ex'.exact.lift_f _ _,
    have hdx : x ≫ S.X₁.d (n+1) (n+1+1) = 0,
    { simp only [← cancel_mono (S.f.f (n+1+1)), assoc, zero_comp, ← S.f.comm, reassoc_of hx,
        homological_complex.d_comp_d, comp_zero], },
    refine ⟨A', π, hπ, y ≫ (mappingCone.inr S.f).f n -
      x ≫ (mappingCone.inl S.f).v (n+1) n (show n = (n+1)+(-1), by linarith), _, _⟩,
    { simp only [preadditive.sub_comp, assoc, mappingCone.inr_d, ← reassoc_of hx,
        mappingCone.inl_d S.f n (n+1) (n+1+1) (by linarith) (by linarith), preadditive.comp_sub,
        reassoc_of hdx, zero_comp, sub_zero, sub_self], },
    { exact ⟨0, by simp only [hy, preadditive.sub_comp, assoc, inr_from_mappingCone_of_ses,
        inl_from_mappingCone_of_ses, comp_zero, sub_zero, zero_comp, add_zero]⟩, }, },
end⟩

end abelian

end cochain_complex
