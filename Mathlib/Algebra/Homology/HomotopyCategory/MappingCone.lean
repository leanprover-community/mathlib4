import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

open CategoryTheory Category Limits Preadditive

variable {C D : Type _} [Category C] [Category D]

@[simp]
lemma CategoryTheory.Limits.biprod.is_zero_iff
    [HasZeroMorphisms C] (A B : C)
    [HasBinaryBiproduct A B] : IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero]
    constructor
    · rw [← cancel_mono (biprod.inl : _ ⟶ A ⊞ B)]
      apply h.eq_of_tgt
    · rw [← cancel_mono (biprod.inr : _ ⟶ A ⊞ B)]
      apply h.eq_of_tgt
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

namespace CochainComplex

section Preadditive

variable [Preadditive C] [Preadditive D] {F G : CochainComplex C ℤ}
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

@[simp]
lemma isZero_mappingCone_X_iff (i : ℤ) :
    IsZero ((mappingCone φ).X i) ↔ IsZero (F.X (i+1)) ∧ IsZero (G.X i) :=
  CategoryTheory.Limits.biprod.is_zero_iff _ _

noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => (Cochain.ofHom (𝟙 F)).v p (q+1) (by linarith) ≫ biprod.inl)

noncomputable def inr : G ⟶ mappingCone φ :=
  Cocycle.homOf (Cocycle.mk
    (Cochain.mk (fun p q hpq => (Cochain.ofHom (𝟙 G)).v p q hpq ≫ biprod.inr)) 1 (zero_add 1) (by
      ext p _ rfl
      dsimp [mappingCone]
      simp only [δ_v 0 1 (zero_add 1) _ p _ rfl p (p+1) (by linarith) rfl, zero_add,
        Int.negOnePow_one,
        neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero, Cochain.mk_v,
        Cochain.ofHom_v, HomologicalComplex.id_f, id_comp, not_true, dite_eq_ite,
        ite_true, comp_add, comp_neg, biprod.inr_fst_assoc,
        zero_comp, neg_zero, add_zero, biprod.inr_snd_assoc, zero_add]))

noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fun p q hpq =>
    biprod.fst ≫ (Cochain.ofHom (𝟙 F)).v (p+1) q (by rw [add_zero, hpq]))) 2 (by linarith) (by
    ext p q hpq
    obtain rfl : q = p + 1 + 1 := by linarith
    dsimp [mappingCone]
    have : Int.negOnePow 2 = 1 := by simp
    simp only [δ_v 1 2 (by linarith) _ p (p+1+1) (by linarith) (p+1) (p+1) (by linarith) rfl,
      Int.negOnePow_succ, Int.negOnePow_one, Cochain.mk_v, Cochain.ofHom_v, HomologicalComplex.id_f, comp_id, not_true,
      neg_neg, dite_eq_ite, ite_true, add_comp, neg_comp, assoc,
      biprod.inl_fst, biprod.inr_fst, comp_zero, add_zero, smul_neg, one_smul, add_right_neg, this])

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
    (inl φ) •[neg_add_self 1] (fst φ : Cochain (mappingCone φ) F 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_self 1) p (p-1) p rfl (by linarith)]

@[simp]
lemma inl_fst_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain F K d) (he : 1 + d = e) :
    (inl φ) •[by rw [← he, neg_add_cancel_left]] ((fst φ : Cochain (mappingCone φ) F 1) •[he] γ) = γ := by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_self 1) (by linarith) (by linarith), inl_fst,
    Cochain.id_comp]

@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p+(-1) = q) :
    (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0 := by
  subst hpq
  simp [inl, snd]

@[simp]
lemma inl_snd :
    (inl φ) •[add_zero (-1)] (snd φ) = 0 := by
  ext p q hpq
  simp [Cochain.comp_v _ _ (add_zero (-1)) p q q (by linarith) (by linarith)]

@[simp]
lemma inl_snd_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain G K d) (he : 0 + d = e) (hf : -1 + e = f) :
    (inl φ) •[hf] ((snd φ) •[he] γ) = 0 := by
  obtain rfl : e = d := by linarith
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, inl_snd, Cochain.zero_comp]

@[reassoc (attr := simp)]
lemma inr_f_fst_v (p q : ℤ) (hpq : p+1 = q) :
    (inr φ).f p ≫ (fst φ : Cochain (mappingCone φ) F 1).v p q hpq = 0 := by
  simp [inr, fst]

@[simp]
lemma inr_fst :
    Cochain.ofHom (inr φ) •[zero_add 1] (fst φ : Cochain (mappingCone φ) F 1) = 0 := by
  ext p q hpq
  simp [Cochain.comp_v _ _ (zero_add 1) p p q (by linarith) (by linarith)]

@[simp]
lemma inr_fst_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (inr φ)) •[hf] ((fst φ : Cochain (mappingCone φ) F 1) •[he] γ) = 0 := by
  obtain rfl : e = f := by linarith
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_fst, Cochain.zero_comp]

@[reassoc (attr := simp)]
lemma inr_f_snd_v (p : ℤ) :
    (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [inr, snd]

@[simp]
lemma inr_snd :
    (Cochain.ofHom (inr φ)) •[zero_add 0] (snd φ) = Cochain.ofHom (𝟙 G) := by aesop_cat

@[simp]
lemma inr_snd_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain G K d) (he : 0 + d = e) :
    (Cochain.ofHom (inr φ)) •[show _ = d by rw [← he, zero_add, zero_add]]
      ((snd φ) •[he] γ) = γ := by
  obtain rfl : d = e := by linarith
  aesop_cat

lemma id_X (p q : ℤ) (hpq : p + 1 = q) :
  𝟙 ((mappingCone φ).X p) = (fst φ : Cochain (mappingCone φ) F 1).v p q hpq ≫
    (inl φ).v q p (by rw [← hpq, Int.add_neg_one, add_tsub_cancel_right]) +
      (snd φ).v p p (add_zero p) ≫ (inr φ).f p := by
  subst hpq
  simp [inl, inr, fst, snd, mappingCone]

lemma id : (fst φ).1.comp (inl φ) (add_neg_self 1) + (snd φ).comp (Cochain.ofHom (inr φ)) (add_zero 0) =
    Cochain.ofHom (𝟙 _) := by
  ext n
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f, Cochain.add_v, Cochain.comp_zero_cochain_v,
    Cochain.comp_v _ _ (add_neg_self 1) n (n+1) n (by linarith) (by linarith),
    id_X φ n (n+1) rfl]

lemma cochain_to_break {K : CochainComplex C ℤ} {n : ℤ} (α : Cochain K (mappingCone φ) n)
    (m : ℤ) (hm : n + 1 = m) :
    ∃ (a : Cochain K F m) (b : Cochain K G n), α = a.comp (inl φ) (by linarith) +
      b.comp (Cochain.ofHom (inr φ)) (add_zero n) := by
  refine' ⟨α.comp (fst φ).1 hm, α.comp (snd φ) (add_zero n), _⟩
  simp only [Cochain.comp_assoc_of_second_degree_eq_neg_third_degree,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.comp_add, id, Cochain.comp_id]

lemma to_ext_iff {A : C} {n₁ : ℤ} (f g : A ⟶ (mappingCone φ).X n₁) (n₂ : ℤ) (h : n₁ + 1 = n₂) :
    f = g ↔ f ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ h =
      g ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ h ∧
      f ≫ (snd φ).v n₁ n₁ (add_zero n₁) = g ≫ (snd φ).v n₁ n₁ (add_zero n₁) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    rw [← cancel_mono (𝟙 _), id_X φ n₁ n₂ h]
    simp only [comp_add, reassoc_of% h₁, reassoc_of% h₂]

lemma cochain_from_break {K : CochainComplex C ℤ} {n : ℤ} (α : Cochain (mappingCone φ) K n)
    (m : ℤ) (hm : m + 1 = n) :
    ∃ (a : Cochain F K m) (b : Cochain G K n),
      α = (MappingCone.fst φ).1.comp a (by linarith) +
        (MappingCone.snd φ).comp b (zero_add n) := by
  refine' ⟨(inl φ).comp α (by linarith),
    (Cochain.ofHom (inr φ)).comp α (zero_add n), _⟩
  nth_rewrite 1 [← α.id_comp]
  rw [← id, Cochain.add_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    add_left_inj, Cochain.comp_assoc _ _ _ _ _ (by linarith)]

lemma from_ext_iff {A : C} {n₁ : ℤ} (f g : (mappingCone φ).X n₁ ⟶ A)
  (n₂ : ℤ) (h : n₁ + 1 = n₂) :
  f = g ↔ (inl φ).v n₂ n₁ (by rw [← h, add_neg_cancel_right]) ≫ f =
    (inl φ).v n₂ n₁ (by rw [← h, add_neg_cancel_right]) ≫ g ∧
    (inr φ).f n₁ ≫ f = (inr φ).f n₁ ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    rw [← cancel_epi (𝟙 _), id_X φ n₁ n₂ h]
    simp only [add_comp, assoc, h₁, h₂]

lemma to_break {A : C} {n₁ : ℤ} (f : A ⟶ (mappingCone φ).X n₁) (n₂ : ℤ) (h : n₁ + 1 = n₂) :
    ∃ (f₁ : A ⟶ F.X n₂) (f₂ : A ⟶ G.X n₁),
      f = f₁ ≫ (inl φ : Cochain F (mappingCone φ) (-1)).v n₂ n₁
        (by rw [← h, add_neg_cancel_right]) + f₂ ≫ (inr φ).f n₁ := by
  refine' ⟨f ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ h,
    f ≫ (snd φ).v n₁ n₁ (add_zero n₁), _⟩
  rw [to_ext_iff _ _ _ _ h]
  simp

lemma cochain_from_ext_iff {K : CochainComplex C ℤ} {n : ℤ} (γ₁ γ₂ : Cochain (mappingCone φ) K n)
    (n' : ℤ) (hn' : -1 + n = n') :
    γ₁ = γ₂ ↔ (inl φ : Cochain F (mappingCone φ) (-1)) •[hn'] γ₁ =
      (inl φ : Cochain F (mappingCone φ) (-1)) •[hn'] γ₂ ∧
      (Cochain.ofHom (inr φ)) •[zero_add n] γ₁ =
        (Cochain.ofHom (inr φ)) •[zero_add n] γ₂ := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    dsimp
    rw [from_ext_iff _ _ _ _ rfl]
    constructor
    · simpa only [Cochain.comp_v _ _ hn' (p+1) p q (by linarith) hpq]
        using Cochain.congr_v h₁ (p+1) q (by linarith)
    · simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using Cochain.congr_v h₂ p q hpq

lemma cochain_to_ext_iff {K : CochainComplex C ℤ} {n : ℤ} (γ₁ γ₂ : Cochain K (mappingCone φ) n)
    (n' : ℤ) (hn' : n + 1 = n'):
    γ₁ = γ₂ ↔ γ₁ •[hn'] (fst φ : Cochain (mappingCone φ) F 1) =
        γ₂ •[hn'] (fst φ : Cochain (mappingCone φ) F 1) ∧
      γ₁ •[add_zero n] (snd φ) = γ₂ •[add_zero n] (snd φ) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    dsimp
    rw [to_ext_iff _ _ _ _ rfl]
    constructor
    · simpa only [Cochain.comp_v _ _ hn' p q (q+1) hpq rfl]
        using Cochain.congr_v h₁ p (q+1) (by linarith)
    · simpa only [Cochain.comp_zero_cochain_v] using Cochain.congr_v h₂ p q hpq

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
  · dsimp [mappingCone, inr]
    subst h
    simp only [Cochain.ofHom_v, HomologicalComplex.id_f, id_comp, ComplexShape.up_Rel,
      not_true, dite_eq_ite, ite_true, comp_add, comp_neg,
      biprod.inr_fst_assoc, zero_comp, neg_zero, add_zero, biprod.inr_snd_assoc, zero_add]
  · rw [(mappingCone φ).shape _ _ h, G.shape _ _ h, zero_comp, comp_zero]

@[reassoc]
lemma d_fst_v (n₁ n₂ n₃ : ℤ) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
  (mappingCone φ).d n₁ n₂ ≫ (fst φ : Cochain (mappingCone φ) F 1).v n₂ n₃ hn₃ =
    -(fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ hn₂ ≫ F.d n₂ n₃ := by
  subst hn₂
  simp [mappingCone, fst]

@[reassoc (attr := simp)]
lemma d_fst_v' (n n' : ℤ) (hn' : n + 1 = n') :
  (mappingCone φ).d (n-1) n ≫ (fst φ : Cochain (mappingCone φ) F 1).v n n' hn' =
    -(fst φ : Cochain (mappingCone φ) F 1).v (n-1) n (by rw [sub_add_cancel]) ≫ F.d n n' :=
  d_fst_v φ (n-1) n n' (by linarith) hn'

@[reassoc]
lemma d_snd_v (n₁ n₂ : ℤ) (hn₂ : n₁ + 1 = n₂) :
  (mappingCone φ).d n₁ n₂ ≫ (snd φ).v n₂ n₂ (add_zero n₂) =
    (fst φ : Cochain (mappingCone φ) F 1).v n₁ n₂ hn₂ ≫ φ.f n₂ +
      (snd φ).v n₁ n₁ (add_zero n₁) ≫ G.d n₁ n₂ := by
  subst hn₂
  simp [mappingCone, fst, snd]

@[reassoc (attr := simp)]
lemma d_snd_v' (n : ℤ) :
  (mappingCone φ).d (n-1) n ≫ (snd φ).v n n (add_zero n) =
    (fst φ : Cochain (mappingCone φ) F 1).v (n-1) n (by rw [sub_add_cancel]) ≫ φ.f n +
      (snd φ).v (n-1) (n-1) (add_zero _) ≫ G.d (n-1) n := by
  apply d_snd_v

@[simp]
lemma inl_comp_diff :
  (inl φ) •[neg_add_self 1] (Cochain.diff (mappingCone φ)) =
    Cochain.ofHom (φ ≫ inr φ) - (Cochain.diff F) •[add_neg_self 1] (inl φ) := by
  ext p
  simp only [Cochain.comp_v _ _ (neg_add_self 1) p (p-1) p (by linarith) (by linarith),
    Cochain.diff_v, Cochain.sub_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
    Cochain.comp_v _ _ (add_neg_self 1) p (p+1) p (by linarith) (by linarith),
    inl_v_d φ p (p-1) (p+1) (by linarith) (by linarith)]

@[simp]
lemma inr_comp_diff :
  (Cochain.ofHom (inr φ)) •[zero_add 1] (Cochain.diff (mappingCone φ)) =
    (Cochain.diff G) •[add_zero 1] (Cochain.ofHom (inr φ)) := by aesop_cat

@[simp]
lemma diff_comp_fst :
  (Cochain.diff (mappingCone φ)) •[show 1 + 1 = 2 by rfl]
    (fst φ : Cochain (mappingCone φ) F 1) =
      -(fst φ : Cochain (mappingCone φ) F 1) •[show 1 + 1 = 2 by rfl] (Cochain.diff F) := by
  ext p q hpq
  dsimp
  simp only [Cochain.comp_v _ _ (show 1 + 1 = 2 by rfl) p (p+1) q (by linarith) (by linarith),
    Cochain.diff_v, d_fst_v]

@[simp]
lemma diff_comp_snd :
  (Cochain.diff (mappingCone φ)) •[add_zero 1] (snd φ) =
    (fst φ : Cochain (mappingCone φ) F 1) •[add_zero 1] (Cochain.ofHom φ) +
      (snd φ) •[zero_add 1] (Cochain.diff G) := by
  ext p q hpq
  dsimp
  simp only [Cochain.comp_v _ _ (add_zero 1) p q q hpq (add_zero q),
    Cochain.comp_v _ _ (zero_add 1) p p q (add_zero p) hpq,
    Cochain.diff_v, Cochain.ofHom_v, d_snd_v _ _ _ hpq]

@[simp]
lemma δ_inl : δ (-1) 0 (inl φ) = Cochain.ofHom (φ ≫ inr φ) := by
  simp only [δ_eq (-1) 0 (neg_add_self 1), inl_comp_diff, Cochain.ofHom_comp,
    add_left_neg, Int.negOnePow_zero, one_smul, sub_add_cancel]

@[simp]
lemma δ_snd : δ 0 1 (snd φ) =
    -(fst φ : Cochain (mappingCone φ) F 1) •[add_zero 1] (Cochain.ofHom φ) := by
  simp only [δ_eq 0 1 (zero_add 1), zero_add, Int.negOnePow_one,
    diff_comp_snd, smul_add, neg_smul, one_smul, add_neg_cancel_comm_assoc]

attribute [irreducible] mappingCone inl inr fst snd

@[simps]
noncomputable def XIso (n i : ℤ) (hi : n + 1 = i) [HasBinaryBiproduct (F.X i) (G.X n)] :
  (mappingCone φ).X n ≅ F.X i ⊞ G.X n where
  hom := (fst φ : Cochain (mappingCone φ) F 1).v n i hi ≫ biprod.inl +
    (snd φ).v n n (add_zero n) ≫ biprod.inr
  inv := biprod.fst ≫ (inl φ).v i n (by linarith) + biprod.snd ≫ (inr φ).f n
  hom_inv_id := by simp [← id_X]
  inv_hom_id := by simp [← id_X]

lemma X_is_zero_iff (n : ℤ) :
    IsZero ((mappingCone φ).X n) ↔ IsZero (F.X (n+1)) ∧ IsZero (G.X n) := by
  rw [(XIso φ n (n+1) rfl).isZero_iff, biprod.is_zero_iff]

noncomputable def descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) : Cochain (mappingCone φ) K n :=
  (fst φ : Cochain (mappingCone φ) F 1) •[show 1 + m = n by rw [← h, add_comm]] α +
    (snd φ) •[zero_add n] β

lemma inl_descCochain {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n) :
    (inl φ) •[by rw [← h, neg_add_cancel_comm_assoc]] (descCochain φ α β h) = α := by
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
      (Cochain.ofHom (inr φ)) •[zero_add n] (descCochain φ α β h)  = β := by
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
  δ n n' (descCochain φ α β h) = (fst φ : Cochain (mappingCone φ) F 1) •[by rw [← hn', add_comm]] (δ m n α +
    (n+1).negOnePow • (Cochain.ofHom φ) •[zero_add n] β) +
      (snd φ) •[zero_add n'] (δ n n' β) := by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, Cochain.comp_zsmul,
    δ_zero_cochain_comp _ _ _ hn', δ_snd, Cochain.neg_comp, smul_neg,
    δ_comp _ _ (show 1 + m = n by linarith) 2 n _ hn' rfl h, Int.negOnePow_succ,
    Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.zero_comp,
    Cocycle.δ_eq_zero, smul_zero, add_zero, neg_smul,
    Cochain.comp_neg, Cochain.comp_zsmul]
  abel

@[simps!]
noncomputable def descCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cocycle G K n)
    (h : m + 1 = n) (eq : δ m n α = n.negOnePow • (Cochain.ofHom φ) •[zero_add n] (β : Cochain G K n)) :
    Cocycle (mappingCone φ) K n :=
  Cocycle.mk (descCochain φ α (β : Cochain G K n) h) (n+1) rfl
    (by simp only [δ_descCochain _ _ _ _ rfl, eq, Int.negOnePow_succ, neg_smul, add_right_neg,
      Cochain.comp_zero, Cocycle.δ_eq_zero, add_zero])

noncomputable def desc {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) : mappingCone φ ⟶ K :=
  Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_self 1)
    (by simp only [eq, Cochain.ofHom_comp, Int.negOnePow_zero, Cocycle.ofHom_coe, one_smul]))

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

lemma inl_desc {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) :
    (inl φ : Cochain F (mappingCone φ) (-1)) •[add_zero (-1)]
      (Cochain.ofHom (desc φ α β eq)) = α := by aesop_cat

@[reassoc (attr := simp)]
lemma inr_f_desc_f {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) (p : ℤ) :
    (inr φ).f p ≫ (desc φ α β eq).f p = β.f p := by aesop_cat

@[reassoc (attr := simp)]
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
    (h₁ : (inl φ) •[add_zero (-1)] (Cochain.ofHom f₁) =
      δ (-2) (-1) γ₁ + (Cochain.ofHom φ) •[zero_add (-1)] γ₂ +
      (inl φ) •[add_zero (-1)] (Cochain.ofHom f₂))
    (h₂ : Cochain.ofHom (inr φ ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)) :
  Homotopy f₁ f₂ := (Cochain.equivHomotopy f₁ f₂).symm (⟨descCochain φ γ₁ γ₂ (by linarith), by
    simp only [δ_descCochain _ _ _ _ (neg_add_self 1), neg_add_self, Int.negOnePow_zero, one_smul,
      cochain_from_ext_iff _ _ _ _ (add_zero (-1))]
    constructor
    · simp only [h₁, Cochain.comp_add, inl_fst_assoc, inl_snd_assoc, add_zero]
    · simp only [Cochain.ofHom_comp] at h₂
      simp only [h₂, Cochain.comp_add, inr_fst_assoc, add_zero, inr_snd_assoc, zero_add]⟩)

noncomputable def liftCochain {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m) : Cochain K (mappingCone φ) n :=
    α •[by linarith] (inl φ) + β •[by linarith] (Cochain.ofHom (inr φ))

@[simp]
lemma liftCochain_fst {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain K F m)
    (β : Cochain K G n) (h : n + 1 = m) :
    (liftCochain φ α β h) •[h] (fst φ : Cochain (mappingCone φ) F 1) = α := by
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
    (liftCochain φ α β h) •[add_zero n] (snd φ : Cochain (mappingCone φ) G 0) = β := by
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
    δ n m (liftCochain φ α β h) = -(δ m m' α) •[by rw [← hm', add_neg_cancel_right]] (inl φ) +
      (δ n m β + α •[add_zero m] (Cochain.ofHom φ)) •[add_zero m] (Cochain.ofHom (inr φ)) := by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp _ _ (show m + (-1) = n by linarith) m' 0 m h hm' (neg_add_self 1),
    δ_inl, Cochain.ofHom_comp, Int.negOnePow_neg, Int.negOnePow_one, neg_smul, one_smul, δ_comp_ofHom, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  abel

@[simps!]
noncomputable def liftCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cocycle K F m) (β : Cochain K G n) (h : n + 1 = m)
    (eq : δ n m β + (α : Cochain K F m) •[add_zero m] (Cochain.ofHom φ) = 0) :
    Cocycle K (mappingCone φ) n :=
  Cocycle.mk (liftCochain φ α β h) m h
    (by simp only [δ_liftCochain φ α β h (m+1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

noncomputable def lift {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0) :
    K ⟶ mappingCone φ :=
  Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]
lemma ofHom_lift {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0) :
    Cochain.ofHom (lift φ α β eq) = liftCochain φ α β (zero_add 1) := by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

section

attribute [local simp] lift

@[reassoc (attr := simp)]
lemma lift_f_fst_v {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0)
    (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p ≫ (fst φ : Cochain (mappingCone φ) F 1).v p q hpq =
      (α : Cochain K F 1).v p q hpq := by simp

lemma lift_fst {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0) :
    (Cochain.ofHom (lift φ α β eq)) •[zero_add 1]
      (fst φ : Cochain (mappingCone φ) F 1) = α := by simp

@[reassoc (attr := simp)]
lemma lift_f_snd_v {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0)
    (p q : ℤ) (hpq : p + 0 = q) :
    (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  obtain rfl : p = q := by linarith
  simp

lemma lift_snd {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0) :
    (Cochain.ofHom (lift φ α β eq)) •[zero_add 0] (snd φ) = β := by simp

lemma lift_f {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0)
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
    (h₁ : (Cochain.ofHom f₁) •[zero_add 1] (fst φ : Cochain (mappingCone φ) F 1) =
      -δ 0 1 α + (Cochain.ofHom f₂) •[zero_add 1] (fst φ : Cochain (mappingCone φ) F 1))
    (h₂ : (Cochain.ofHom f₁) •[zero_add 0] (snd φ) =
      δ (-1) 0 β + α •[zero_add 0] (Cochain.ofHom φ) +
        (Cochain.ofHom f₂) •[zero_add 0] (snd φ)) :
    Homotopy f₁ f₂ := (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_self 1), by
      simp only [δ_liftCochain φ α β (neg_add_self 1) 1 (zero_add 1),
        cochain_to_ext_iff _ _ _ _ (zero_add 1)]
      constructor
      · simp only [h₁, Cochain.add_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          Cochain.neg_comp,
          inl_fst, Cochain.comp_id, inr_fst, Cochain.comp_zero, add_zero,
          Cochain.comp_assoc_of_second_degree_eq_neg_third_degree]
      · simp only [h₂, Cochain.add_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain, inl_snd,
          Cochain.comp_zero, neg_zero, inr_snd, Cochain.comp_id, zero_add]⟩

@[reassoc]
lemma lift_desc_f {K L : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + (α : Cochain K F 1) •[add_zero 1] (Cochain.ofHom φ) = 0)
    (α' : Cochain F L (-1)) (β' : G ⟶ L)
    (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : ℤ) (hnn' : n+1 = n') :
    (lift φ α β eq).f n ≫ (desc φ α' β' eq').f n =
    (α : Cochain K F 1).v n n' hnn' ≫ α'.v n' n (by rw [← hnn', add_neg_cancel_right]) +
      β.v n n (add_zero n) ≫ β'.f n := by
  rw [← id_comp ((desc φ α' β' eq').f n), id_X φ _ _ hnn']
  simp only [add_comp, assoc, inl_v_desc_f, inr_f_desc_f, comp_add,
    lift_f_fst_v_assoc, lift_f_snd_v_assoc]

noncomputable def homotopySelfCompInr : Homotopy (φ ≫ inr φ) 0 :=
  liftHomotopy _ _ _ (Cochain.ofHom (𝟙 F)) 0 (by simp) (by simp)

section

variable (H : C ⥤ D) [H.Additive]
  [∀ p, HasBinaryBiproduct (((H.mapHomologicalComplex _).obj F).X (p+1)) (((H.mapHomologicalComplex _).obj G).X p)]

@[simps]
noncomputable def mapHomologicalComplexXIso' (n m : ℤ) (hnm : n + 1 = m) :
  ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mappingCone φ)).X n ≅
    (mappingCone ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).X n where
  hom := H.map ((fst φ).1.v n m (by linarith)) ≫
      (inl ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).v m n (by linarith) +
      H.map ((snd φ).v n n (add_zero n)) ≫
        (inr ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).f n
  inv := (fst ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).1.v n m (by linarith) ≫ H.map ((inl φ).v m n (by linarith)) +
      (snd ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).v n n (add_zero n) ≫ H.map ((inr φ).f n)
  hom_inv_id := by
    simp only [Functor.mapHomologicalComplex_obj_X, comp_add, add_comp, assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc,
      zero_comp, comp_zero, add_zero, inl_v_snd_v_assoc, inr_f_snd_v_assoc, zero_add, ← Functor.map_comp, ← Functor.map_add]
    rw [← H.map_id]
    congr 1
    rw [from_ext_iff _ _ _ _ hnm]
    simp
  inv_hom_id := by
    simp only [Functor.mapHomologicalComplex_obj_X, comp_add, add_comp, assoc, ← H.map_comp_assoc, inl_v_fst_v,
      CategoryTheory.Functor.map_id, id_comp, inr_f_fst_v, inl_v_snd_v, inr_f_snd_v]
    rw [H.map_zero, H.map_zero, zero_comp, zero_comp, comp_zero, comp_zero, add_zero, zero_add,
      from_ext_iff _ _ _ _ hnm]
    simp

noncomputable def mapHomologicalComplexXIso (n : ℤ) := mapHomologicalComplexXIso' φ H n (n+1) rfl

lemma mapHomologicalComplexXIso_eq (n m : ℤ) (hnm : n + 1 = m) :
    mapHomologicalComplexXIso φ H n = mapHomologicalComplexXIso' φ H n m hnm := by
  subst hnm
  rfl

noncomputable def mapHomologicalComplexIso :
  (H.mapHomologicalComplex _).obj (mappingCone φ) ≅
    mappingCone ((H.mapHomologicalComplex _).map φ) :=
  HomologicalComplex.Hom.isoOfComponents (mapHomologicalComplexXIso φ H) (by
    rintro n _ rfl
    rw [to_ext_iff _ _ _ (n+2) (by linarith), assoc, assoc, d_fst_v _ _ _ _ rfl,
      assoc, assoc, d_snd_v _ _ _ rfl]
    simp only [mapHomologicalComplexXIso_eq φ H n (n+1) rfl,
      mapHomologicalComplexXIso_eq φ H (n+1) (n+2) (by linarith),
      mapHomologicalComplexXIso'_hom, mapHomologicalComplexXIso'_hom]
    constructor
    · dsimp
      simp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
        comp_neg, add_comp, assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero,
        comp_add, inl_v_fst_v, comp_id, inr_f_fst_v, ← H.map_comp,
        d_fst_v φ n (n+1) (n+2) rfl (by linarith), Functor.map_neg]
    · dsimp
      simp only [comp_add, add_comp, assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc,
        Functor.mapHomologicalComplex_obj_X, zero_comp, comp_zero, add_zero, inl_v_snd_v_assoc, inr_f_snd_v_assoc,
        zero_add, inl_v_snd_v, inr_f_snd_v, comp_id, ← H.map_comp, d_snd_v φ n (n+1) rfl, Functor.map_add])

end

end MappingCone

end Preadditive

end CochainComplex
