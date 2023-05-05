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

lemma cochain_to_ext_iff {K : CochainComplex C ℤ} {n : ℤ} (γ₁ γ₂ : Cochain K (mappingCone φ) n)
    (n' : ℤ) (hn' : n + 1 = n'):
    γ₁ = γ₂ ↔ γ₁.comp (fst φ : Cochain (mappingCone φ) F 1) hn' =
        γ₂.comp (fst φ : Cochain (mappingCone φ) F 1) hn' ∧
      γ₁.comp (snd φ) (add_zero n) = γ₂.comp (snd φ) (add_zero n) := by
  constructor
  . rintro rfl
    tauto
  . rintro ⟨h₁, h₂⟩
    ext ⟨p, q, hpq⟩
    dsimp
    rw [to_ext_iff _ _ _ _ rfl]
    constructor
    . simpa only [Cochain.comp_v _ _ hn' p q (q+1) hpq rfl]
        using Cochain.congr_v h₁ p (q+1) (by linarith)
    . simpa only [Cochain.comp_zero_cochain_v] using Cochain.congr_v h₂ p q hpq

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
  (h : m + 1 = n) (hn' : n + 1 = n') :
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

@[simp]
lemma ofHom_desc {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) :
    Cochain.ofHom (desc φ α β eq) = descCochain φ α (Cochain.ofHom β) (neg_add_self 1) := by
  simp only [desc, Cocycle.cochain_ofHom_homOf_eq_coe, descCocycle_coe, Cocycle.ofHom_coe]

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

lemma desc_f {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) (p q : ℤ) (hpq : p + 1 = q) :
    (desc φ α β eq).f p = (fst φ : Cochain (mappingCone φ) F 1).v p q hpq ≫
        α.v q p (by rw [← hpq, add_neg_cancel_right]) +
      (snd φ).v p p (add_zero p) ≫ β.f p := by
    rw [from_ext_iff _ _ _ _ hpq]
    simp only [inl_v_desc_f, comp_add, inl_v_fst_v_assoc, inl_v_snd_v_assoc,
      zero_comp, add_zero, inr_f_desc_f, inr_f_fst_v_assoc, inr_f_snd_v_assoc,
      zero_add, and_self]

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

noncomputable def liftCochain {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m) : Cochain K (mappingCone φ) n :=
    α.comp (inl φ) (by linarith) + β.comp (Cochain.ofHom (inr φ)) (by linarith)

@[simp]
lemma liftCochain_fst {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain K F m)
    (β : Cochain K G n) (h : n + 1 = m) :
    (liftCochain φ α β h).comp (fst φ : Cochain (mappingCone φ) F 1) h = α := by
  dsimp only [liftCochain]
  simp only [Cochain.add_comp, Cochain.comp_assoc_of_second_degree_eq_neg_third_degree,
    inl_fst, Cochain.comp_id, Cochain.comp_assoc_of_second_is_zero_cochain, inr_fst,
    Cochain.comp_zero, add_zero]

@[reassoc (attr := simp)]
lemma liftCochain_v_fst_v {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain K F m)
    (β : Cochain K G n) (h : n + 1 = m) (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ : Cochain (mappingCone φ) F 1).v p₂ p₃ h₂₃ =
      α.v p₁ p₃ (by rw [← h, ← h₂₃, ← h₁₂, add_assoc]) := by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (liftCochain_fst φ α β h) p₁ p₃ (by linarith)

@[simp]
lemma liftCochain_snd {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain K F m)
    (β : Cochain K G n) (h : n + 1 = m) :
    (liftCochain φ α β h).comp (snd φ : Cochain (mappingCone φ) G 0) (add_zero n) = β := by
  dsimp only [liftCochain]
  simp only [Cochain.add_comp, Cochain.comp_assoc_of_third_is_zero_cochain, inl_snd,
    Cochain.comp_zero, inr_snd, Cochain.comp_id, zero_add]

@[reassoc (attr := simp)]
lemma liftCochain_v_snd_v {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain K F m)
    (β : Cochain K G n) (h : n + 1 = m) (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫
      (snd φ : Cochain (mappingCone φ) G 0).v p₂ p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (liftCochain_snd φ α β h) p₁ p₂ (by linarith)

lemma δ_liftCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain K F m) (β : Cochain K G n)
    (h : n + 1 = m) (m' : ℤ) (hm' : m + 1 = m') :
    δ n m (liftCochain φ α β h) = -(δ m m' α).comp (inl φ) (by rw [← hm', add_neg_cancel_right]) +
      (δ n m β + α.comp (Cochain.ofHom φ) (add_zero m)).comp
        (Cochain.ofHom (inr φ)) (add_zero m) := by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp _ _ (show m + (-1) = n by linarith) m' 0 m h hm' (neg_add_self 1),
    δ_inl, Cochain.ofHom_comp, ε_neg, ε_1, neg_smul, one_smul, δ_comp_ofHom, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  abel

@[simps!]
noncomputable def liftCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cocycle K F m) (β : Cochain K G n) (h : n + 1 = m)
    (eq : δ n m β + (α : Cochain K F m).comp (Cochain.ofHom φ) (add_zero m) = 0) :
    Cocycle K (mappingCone φ) n :=
  Cocycle.mk (liftCochain φ α β h) m h
    (by simp only [δ_liftCochain φ α β h (m+1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

noncomputable def lift {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0) :
    K ⟶ mappingCone φ :=
  Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]
lemma ofHom_lift {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0) :
    Cochain.ofHom (lift φ α β eq) = liftCochain φ α β (zero_add 1) := by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

section

attribute [local simp] lift

@[reassoc (attr := simp)]
lemma lift_f_fst_v {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p ≫ (fst φ : Cochain (mappingCone φ) F 1).v p q hpq =
      (α : Cochain K F 1).v p q hpq := by simp

lemma lift_fst {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0) :
    (Cochain.ofHom (lift φ α β eq)).comp
      (fst φ : Cochain (mappingCone φ) F 1) (zero_add 1) = α := by simp

@[reassoc (attr := simp)]
lemma lift_f_snd_v {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (p q : ℤ) (hpq : p + 0 = q) :
    (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  obtain rfl : p = q := by linarith
  simp

lemma lift_snd {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0) :
    (Cochain.ofHom (lift φ α β eq)).comp (snd φ) (zero_add 0) = β := by simp

lemma lift_f {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p = (α : Cochain K F 1).v p q hpq ≫
      (inl φ : Cochain F (mappingCone φ) (-1)).v q p (by rw [← hpq, add_neg_cancel_right]) +
      β.v p p (add_zero p) ≫ (inr φ).f p := by
    rw [to_ext_iff _ _ _ _ hpq]
    simp only [lift_f_fst_v, add_comp, assoc, inl_v_fst_v, comp_id, inr_f_fst_v,
      comp_zero, add_zero, lift_f_snd_v, inl_v_snd_v, inr_f_snd_v, zero_add, and_self]

end

@[simps!]
noncomputable def liftHomotopy {K : CochainComplex C ℤ} (f₁ f₂ : K ⟶ mappingCone φ)
    (α : Cochain K F 0) (β : Cochain K G (-1))
    (h₁ : (Cochain.ofHom f₁).comp (fst φ : Cochain (mappingCone φ) F 1) (zero_add 1) =
      -δ 0 1 α + (Cochain.ofHom f₂).comp (fst φ : Cochain (mappingCone φ) F 1) (zero_add 1))
    (h₂ : (Cochain.ofHom f₁).comp (snd φ) (zero_add 0) =
      δ (-1) 0 β + α.comp (Cochain.ofHom φ) (zero_add 0) +
        (Cochain.ofHom f₂).comp (snd φ) (zero_add 0)) :
    Homotopy f₁ f₂ := (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_self 1), by
      simp only [δ_liftCochain φ α β (neg_add_self 1) 1 (zero_add 1),
        cochain_to_ext_iff _ _ _ _ (zero_add 1)]
      constructor
      . simp only [h₁, Cochain.add_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          Cochain.neg_comp, Cochain.comp_assoc_of_second_degree_eq_neg_third_degree,
          inl_fst, Cochain.comp_id, inr_fst, Cochain.comp_zero, add_zero]
      . simp only [h₂, Cochain.add_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain, inl_snd,
          Cochain.comp_zero, neg_zero, inr_snd, Cochain.comp_id, zero_add]⟩

@[reassoc]
lemma lift_desc_f {K L : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1).comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (α' : Cochain F L (-1)) (β' : G ⟶ L)
    (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : ℤ) (hnn' : n+1 = n') :
    (lift φ α β eq).f n ≫ (desc φ α' β' eq').f n =
    (α : Cochain K F 1).v n n' hnn' ≫ α'.v n' n (by rw [← hnn', add_neg_cancel_right]) +
      β.v n n (add_zero n) ≫ β'.f n := by
  rw [← id_comp ((desc φ α' β' eq').f n), id φ _ _ hnn']
  simp only [add_comp, assoc, inl_v_desc_f, inr_f_desc_f, comp_add,
    lift_f_fst_v_assoc, lift_f_snd_v_assoc]

end MappingCone

end Preadditive

end CochainComplex
