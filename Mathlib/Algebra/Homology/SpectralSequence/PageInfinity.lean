import Mathlib.Algebra.Homology.SpectralSequence.Basic

lemma Set.has_min_of_ℤ (S : Set ℤ) (hS : S.Nonempty) (m₀ : ℤ)
    (hm₀ : ∀ (x : ℤ) (_ : x ∈ S), m₀ ≤ x) :
    ∃ (m : ℤ) (_ : m ∈ S), ∀ (x : ℤ) (_ : x ∈ S), m ≤ x := by
  let T : Set ℕ := fun i => m₀ + i ∈ S
  obtain ⟨x, hx⟩ := hS
  obtain ⟨t₀, rfl⟩ := Int.eq_add_ofNat_of_le (hm₀ x hx)
  have hT : T.Nonempty := ⟨t₀, hx⟩
  let μ := (Nat.lt_wfRel.wf).min T hT
  refine' ⟨m₀ + μ, (Nat.lt_wfRel.wf).min_mem T hT, fun y hy => _⟩
  have hy' : 0 ≤ y - m₀ := by linarith [hm₀ y hy]
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hy'
  obtain rfl : y = m₀ + t := by linarith
  simp only [ge_iff_le, add_le_add_iff_left, Nat.cast_le]
  exact (Nat.lt_wfRel.wf).min_le hy _

namespace CategoryTheory

open Category ZeroObject

variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

attribute [local instance] epi_comp

variable (E : SpectralSequence C c r₀)

class HasPageInfinityAt (pq : ι) : Prop where
  nonempty_hasEdgeMonoSet : (E.hasEdgeMonoSet pq).Nonempty
  nonempty_hasEdgeEpiSet : (E.hasEdgeEpiSet pq).Nonempty

section

variable (pq : ι) [E.HasPageInfinityAt pq]

lemma nonempty_hasEdgeMonoSet :
    (E.hasEdgeMonoSet pq).Nonempty :=
  HasPageInfinityAt.nonempty_hasEdgeMonoSet

lemma nonempty_hasEdgeEpiSet :
    (E.hasEdgeEpiSet pq).Nonempty :=
  HasPageInfinityAt.nonempty_hasEdgeEpiSet

noncomputable def rToMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le)).choose

lemma rToMin_mem : E.rToMin pq ∈ E.hasEdgeMonoSet pq :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le)).choose_spec.choose

lemma rToMin_LE (r : ℤ) (hr : r ∈ E.hasEdgeMonoSet pq) :
    E.rToMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le)).choose_spec.choose_spec r hr

lemma LE_rToMin :
    r₀ ≤ E.rToMin pq :=
  ((E.rToMin_mem pq) _ (by rfl)).choose.le

lemma hasPage_of_rToMin_LE (r : ℤ) (hr : E.rToMin pq ≤ r) :
    E.HasPage r :=
  ((E.rToMin_mem pq) r hr).choose

instance : E.HasPage (E.rToMin pq) :=
  E.hasPage_of_rToMin_LE pq _ (by rfl)

noncomputable def rFromMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le)).choose

lemma rFromMin_mem : E.rFromMin pq ∈ E.hasEdgeEpiSet pq :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le)).choose_spec.choose

lemma rFromMin_LE (r : ℤ) (hr : r ∈ E.hasEdgeEpiSet pq) :
    E.rFromMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le)).choose_spec.choose_spec r hr

lemma LE_rFromMin :
    r₀ ≤ E.rFromMin pq :=
  ((E.rFromMin_mem pq) _ (by rfl)).choose.le

lemma hasPage_of_rFromMin_LE (r : ℤ) (hr : E.rFromMin pq ≤ r) :
    E.HasPage r :=
  ((E.rFromMin_mem pq) r hr).choose

instance : E.HasPage (E.rFromMin pq) :=
  E.hasPage_of_rFromMin_LE pq _ (by rfl)

noncomputable def rMin : ℤ := max (E.rToMin pq) (E.rFromMin pq)

lemma rFromMin_LE_rMin : E.rFromMin pq ≤ E.rMin pq := le_max_right _ _

lemma rToMin_LE_rMin : E.rToMin pq ≤ E.rMin pq := le_max_left _ _

lemma LE_rMin :
    r₀ ≤ E.rMin pq :=
  (E.LE_rFromMin pq).trans (E.rFromMin_LE_rMin pq)

instance : E.HasPage (E.rMin pq) :=
  E.hasPage_of_rToMin_LE pq _ (E.rToMin_LE_rMin pq)

end

lemma d_to_eq_zero (r : ℤ) [E.HasPage r] (pq pq' : ι) [E.HasPageInfinityAt pq']
    (hr : E.rToMin pq' ≤ r) :
    (E.page r).d pq pq' = 0 := by
  have := ((E.rToMin_mem pq') r hr).choose_spec
  rw [d_eq_zero_of_hasEdgeMonoAt]

lemma d_from_eq_zero (r : ℤ) [E.HasPage r] (pq pq' : ι) [E.HasPageInfinityAt pq]
    (hr : E.rFromMin pq ≤ r) :
    (E.page r).d pq pq' = 0 := by
  have := ((E.rFromMin_mem pq) r hr).choose_spec
  rw [d_eq_zero_of_hasEdgeEpiAt]

lemma hasEdgeMonoAt_of_rToMin_LE (pq : ι) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : E.rToMin pq ≤ r) [E.HasPage r] :
    E.HasEdgeMonoAt pq r where
  zero pq' := E.d_to_eq_zero r pq' pq hr

lemma hasEdgeEpiAt_of_rFromMin_LE (pq : ι) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : E.rFromMin pq ≤ r) [E.HasPage r] :
    E.HasEdgeEpiAt pq r where
  zero pq' := E.d_from_eq_zero r pq pq' hr

section

variable (pq : ι) (r : ℤ) [E.HasPageInfinityAt pq]

class HasEdgeMonoAtFrom : Prop where
  le : E.rToMin pq ≤ r

instance : E.HasEdgeMonoAtFrom pq (E.rToMin pq) where
  le := by rfl

instance : E.HasEdgeMonoAtFrom pq (E.rMin pq) where
  le := E.rToMin_LE_rMin pq

lemma HasEdgeMonoAtFrom.mk' [E.HasPage r] (hr : ∀ (k : ℕ), E.HasEdgeMonoAt pq (r + k)) :
    E.HasEdgeMonoAtFrom pq r where
  le := E.rToMin_LE _ _ (fun r' hr' => by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hr'
    exact ⟨inferInstance, hr _⟩)

variable [E.HasEdgeMonoAtFrom pq r]

lemma LE_of_hasEdgeMonoAtFrom : E.rToMin pq ≤ r := by apply HasEdgeMonoAtFrom.le

lemma mem_hasEdgeMonoSet : r ∈ E.hasEdgeMonoSet pq := by
  intro r' hr'
  have H := (E.LE_of_hasEdgeMonoAtFrom pq r).trans hr'
  have := E.hasPage_of_LE _ _ H
  exact ⟨this, ⟨fun pq' => E.d_to_eq_zero _ _ _ H⟩⟩

lemma hasEdgeMonoAtFrom_of_GE (r' : ℤ) (_ : r ≤ r') :
    E.HasEdgeMonoAtFrom pq r' where
  le := by linarith [E.LE_of_hasEdgeMonoAtFrom pq r]

instance (r' : ℤ) :
    E.HasEdgeMonoAtFrom pq (max r r') :=
  E.hasEdgeMonoAtFrom_of_GE pq r _ (le_max_left _ _)

instance (r' : ℤ) :
    E.HasEdgeMonoAtFrom pq (max r' r) :=
  E.hasEdgeMonoAtFrom_of_GE pq r _ (le_max_right _ _)

instance [E.HasPage r] : E.HasEdgeMonoAt pq r where
  zero pq' := E.d_to_eq_zero r pq' pq (E.LE_of_hasEdgeMonoAtFrom pq r)

instance (k : ℕ) : E.HasEdgeMonoAtFrom pq (r + k) where
  le := by linarith [E.LE_of_hasEdgeMonoAtFrom pq r]

instance [E.HasEdgeMonoAtFrom pq 2] : E.HasEdgeMonoAtFrom pq 3 := by
  change E.HasEdgeMonoAtFrom pq (2 + (1 : ℕ))
  infer_instance

noncomputable def edgeMonoSteps' (k : ℕ) [E.HasPage r] :
    (E.page (r + k)).X pq ⟶ (E.page r).X pq := by
  induction' k with k hk
  · exact (E.pageXIsoOfEq pq _ _ (by simp)).hom
  · exact E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ))
      (by simp only [Nat.cast_add, Nat.cast_one]; linarith) ≫ hk

@[simp]
lemma edgeMonoSteps'_zero [E.HasPage r] :
    E.edgeMonoSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)).hom := rfl

@[simp]
lemma edgeMonoSteps'_succ (k : ℕ) [E.HasPage r] :
    E.edgeMonoSteps' pq r (k + 1) = E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ))
      (by simp only [Nat.cast_add, Nat.cast_one]; linarith) ≫ E.edgeMonoSteps' pq r k := rfl

instance (k : ℕ) [E.HasPage r] : Mono (E.edgeMonoSteps' pq r k) := by
  induction' k with k hk
  · rw [edgeMonoSteps'_zero]
    infer_instance
  · rw [edgeMonoSteps'_succ]
    infer_instance

noncomputable def edgeMonoSteps (r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r'] :
    (E.page r').X pq ⟶ (E.page r).X pq :=
  (E.pageXIsoOfEq pq _ _ (by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
    simp)).inv ≫ E.edgeMonoSteps' pq r (Int.toNat (r' - r))

instance (r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r'] :
    Mono (E.edgeMonoSteps pq r r' h) := by
  dsimp [edgeMonoSteps]
  infer_instance

lemma edgeMonoSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r') [E.HasPage r] [E.HasPage r'] :
    E.edgeMonoSteps pq r r' (by linarith) =
      (E.pageXIsoOfEq pq _ _ h).inv ≫ E.edgeMonoSteps' pq r k := by
  obtain rfl : k = Int.toNat (r' - r) := by
    rw [← Int.ofNat_inj, Int.toNat_of_nonneg (by linarith)]
    linarith
  rfl

lemma edgeMonoSteps_eq_edgeMonoSteps' (k : ℕ) [E.HasPage r] :
    E.edgeMonoSteps pq r (r + k) (by linarith) =
      E.edgeMonoSteps' pq r k := by
  simp [E.edgeMonoSteps_eq pq r (r + k) k rfl, pageXIsoOfEq]

@[simp]
lemma edgeMonoSteps_eq_id [E.HasPage r] :
    E.edgeMonoSteps pq r r (by rfl) = 𝟙 _ := by
  rw [E.edgeMonoSteps_eq pq r r 0 (by simp), edgeMonoSteps'_zero, Iso.inv_hom_id]

lemma edgeMonoSteps_eq_of_eq (r' : ℤ) (h : r = r') [E.HasPage r] [E.HasPage r'] :
    E.edgeMonoSteps pq r r' (by linarith) = (E.pageXIsoOfEq pq r r' h).inv := by
  subst h
  rw [edgeMonoSteps_eq_id]
  rfl

lemma edgeMonoSteps_eq_pageXIsoOfEq_inv_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r') (h₂ : r' = r'')
    [E.HasPage r] [E.HasPage r'] [E.HasPage r''] :
    E.edgeMonoSteps pq r r'' (by linarith) =
      (E.pageXIsoOfEq pq r' r'' h₂).inv ≫ E.edgeMonoSteps pq r r' h₁ := by
  subst h₂
  simp [pageXIsoOfEq]

lemma edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r') (h₂ : r' + 1 = r'')
    [E.HasPage r] [E.HasPage r'] [E.HasPage r''] [E.HasEdgeMonoAt pq r'] :
    E.edgeMonoSteps pq r r'' (by linarith) =
      E.edgeMonoStep pq r' r'' h₂ ≫ E.edgeMonoSteps pq r r' h₁ := by
  obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  rw [E.edgeMonoSteps_eq_edgeMonoSteps', E.edgeMonoSteps_eq_edgeMonoSteps', E.edgeMonoSteps'_succ]

lemma edgeMonoSteps_eq_edgeMonoStep
    (r' : ℤ) (h : r + 1 = r') [E.HasPage r] [E.HasPage r'] :
    E.edgeMonoSteps pq r r' (by linarith) = E.edgeMonoStep pq r r' h := by
  rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r r r' (by rfl) h,
    edgeMonoSteps_eq_id, comp_id]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp (r' r'' : ℤ) (hr' : r ≤ r') (hr'' : r' ≤ r'')
    [E.HasPage r] [E.HasPage r'] [h : E.HasPage r'']
    [E.HasEdgeMonoAtFrom pq r'] :
    E.edgeMonoSteps pq r' r'' hr'' ≫ E.edgeMonoSteps pq r r' hr' =
      E.edgeMonoSteps pq r r'' (hr'.trans hr'') := by
  suffices ∀ (k : ℕ), E.edgeMonoSteps pq r' (r' + k) (by linarith) ≫
      E.edgeMonoSteps pq r r' hr' =
        E.edgeMonoSteps pq r (r' + k) (by linarith) by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hr''
    apply this
  intro k
  induction' k with k hk
  · simp only [E.edgeMonoSteps_eq_of_eq pq r' (r' + Nat.zero) (by simp),
      E.edgeMonoSteps_eq_pageXIsoOfEq_inv_comp_edgeMonoSteps pq r r' (r' + Nat.zero) hr' (by simp)]
  · simp only [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r' (r' + k) (r' + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]), assoc, hk,
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r' + k) (r' + k.succ) (by linarith)
      (by simp only [Nat.cast_succ, add_assoc])]

end

section

variable (pq : ι) (r : ℤ) [E.HasPageInfinityAt pq]

class HasEdgeEpiAtFrom : Prop where
  le : E.rFromMin pq ≤ r

instance : E.HasEdgeEpiAtFrom pq (E.rFromMin pq) where
  le := by rfl

instance : E.HasEdgeEpiAtFrom pq (E.rMin pq) where
  le := E.rFromMin_LE_rMin pq

lemma HasEdgeEpiAtFrom.mk' [E.HasPage r] (hr : ∀ (k : ℕ), E.HasEdgeEpiAt pq (r + k)) :
    E.HasEdgeEpiAtFrom pq r where
  le := E.rFromMin_LE _ _ (fun r' hr' => by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hr'
    exact ⟨inferInstance, hr _⟩)

variable [E.HasEdgeEpiAtFrom pq r]

lemma LE_of_hasEdgeEpiAtFrom : E.rFromMin pq ≤ r := by apply HasEdgeEpiAtFrom.le

lemma mem_hasEdgeEpiSet : r ∈ E.hasEdgeEpiSet pq := by
  intro r' hr'
  have H := (E.LE_of_hasEdgeEpiAtFrom pq r).trans hr'
  have := E.hasPage_of_LE _ _ H
  exact ⟨this, ⟨fun pq' => E.d_from_eq_zero _ _ _ H⟩⟩

lemma hasEdgeEpiAtFrom_of_GE (r' : ℤ) (_ : r ≤ r') :
    E.HasEdgeEpiAtFrom pq r' where
  le := by linarith [E.LE_of_hasEdgeEpiAtFrom pq r]

instance (r' : ℤ) :
    E.HasEdgeEpiAtFrom pq (max r r') :=
  E.hasEdgeEpiAtFrom_of_GE pq r _ (le_max_left _ _)

instance (r' : ℤ) :
    E.HasEdgeEpiAtFrom pq (max r' r) :=
  E.hasEdgeEpiAtFrom_of_GE pq r _ (le_max_right _ _)

instance [E.HasPage r] : E.HasEdgeEpiAt pq r where
  zero pq' := E.d_from_eq_zero r pq pq' (E.LE_of_hasEdgeEpiAtFrom pq r)

instance (k : ℕ) : E.HasEdgeEpiAtFrom pq (r + k) where
  le := by linarith [E.LE_of_hasEdgeEpiAtFrom pq r]

instance [E.HasEdgeEpiAtFrom pq 2] : E.HasEdgeEpiAtFrom pq 3 := by
  change E.HasEdgeEpiAtFrom pq (2 + (1 : ℕ))
  infer_instance


noncomputable def edgeEpiSteps' (k : ℕ) [E.HasPage r] :
    (E.page r).X pq ⟶ (E.page (r + k)).X pq := by
  induction' k with k hk
  · exact (E.pageXIsoOfEq pq _ _ (by simp)).inv
  · exact hk ≫ E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ))
      (by simp only [Nat.cast_add, Nat.cast_one]; linarith)

@[simp]
lemma edgeEpiSteps'_zero [E.HasPage r] :
    E.edgeEpiSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)).inv := rfl

@[simp]
lemma edgeEpiSteps'_succ (k : ℕ) [E.HasPage r] :
    E.edgeEpiSteps' pq r (k + 1) = E.edgeEpiSteps' pq r k ≫
      E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ))
      (by simp only [Nat.cast_add, Nat.cast_one]; linarith) := rfl

instance (k : ℕ) [E.HasPage r] : Epi (E.edgeEpiSteps' pq r k) := by
  induction' k with k hk
  · rw [edgeEpiSteps'_zero]
    infer_instance
  · rw [edgeEpiSteps'_succ]
    infer_instance

noncomputable def edgeEpiSteps (r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r'] :
    (E.page r).X pq ⟶ (E.page r').X pq :=
  E.edgeEpiSteps' pq r (Int.toNat (r' - r)) ≫ (E.pageXIsoOfEq pq _ _ (by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
    simp)).hom

instance (r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r'] :
    Epi (E.edgeEpiSteps pq r r' h) := by
  dsimp [edgeEpiSteps]
  infer_instance

lemma edgeEpiSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r') [E.HasPage r] [E.HasPage r'] :
    E.edgeEpiSteps pq r r' (by linarith) =
      E.edgeEpiSteps' pq r k ≫ (E.pageXIsoOfEq pq _ _ h).hom := by
  obtain rfl : k = Int.toNat (r' - r) := by
    rw [← Int.ofNat_inj, Int.toNat_of_nonneg (by linarith)]
    linarith
  rfl

lemma edgeEpiSteps_eq_edgeEpiSteps' (k : ℕ) [E.HasPage r] :
    E.edgeEpiSteps pq r (r + k) (by linarith) =
      E.edgeEpiSteps' pq r k := by
  simp [E.edgeEpiSteps_eq pq r (r + k) k rfl, pageXIsoOfEq]

@[simp]
lemma edgeEpiSteps_eq_id [E.HasPage r] :
    E.edgeEpiSteps pq r r (by rfl) = 𝟙 _ := by
  rw [E.edgeEpiSteps_eq pq r r 0 (by simp), edgeEpiSteps'_zero, Iso.inv_hom_id]

lemma edgeEpiSteps_eq_of_eq (r' : ℤ) (h : r = r') [E.HasPage r] [E.HasPage r'] :
    E.edgeEpiSteps pq r r' (by linarith) = (E.pageXIsoOfEq pq r r' h).hom := by
  subst h
  rw [edgeEpiSteps_eq_id]
  rfl

lemma edgeEpiSteps_eq_edgeEpiSteps_comp_pageXIsoOfEq_hom
    (r' r'' : ℤ) (h₁ : r ≤ r') (h₂ : r' = r'')
    [E.HasPage r] [E.HasPage r'] [E.HasPage r''] :
    E.edgeEpiSteps pq r r'' (by linarith) =
      E.edgeEpiSteps pq r r' h₁ ≫ (E.pageXIsoOfEq pq r' r'' h₂).hom := by
  subst h₂
  simp [pageXIsoOfEq]

lemma edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep
    (r' r'' : ℤ) (h₁ : r ≤ r') (h₂ : r' + 1 = r'')
    [E.HasPage r] [E.HasPage r'] [E.HasPage r''] [E.HasEdgeEpiAt pq r'] :
    E.edgeEpiSteps pq r r'' (by linarith) =
      E.edgeEpiSteps pq r r' h₁ ≫ E.edgeEpiStep pq r' r'' h₂ := by
  obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  rw [E.edgeEpiSteps_eq_edgeEpiSteps', E.edgeEpiSteps_eq_edgeEpiSteps', E.edgeEpiSteps'_succ]

lemma edgeEpiSteps_eq_edgeEpiStep
    (r' : ℤ) (h : r + 1 = r') [E.HasPage r] [E.HasPage r'] :
    E.edgeEpiSteps pq r r' (by linarith) = E.edgeEpiStep pq r r' h := by
  rw [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r r r' (by rfl) h,
    edgeEpiSteps_eq_id, id_comp]

@[reassoc (attr := simp)]
lemma edgeEpiSteps_comp (r' r'' : ℤ) (hr' : r ≤ r') (hr'' : r' ≤ r'')
    [E.HasPage r] [E.HasPage r'] [h : E.HasPage r'']
    [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' hr' ≫ E.edgeEpiSteps pq r' r'' hr'' =
      E.edgeEpiSteps pq r r'' (hr'.trans hr'') := by
  suffices ∀ (k : ℕ), E.edgeEpiSteps pq r r' hr' ≫
      E.edgeEpiSteps pq r' (r' + k) (by linarith) =
        E.edgeEpiSteps pq r (r' + k) (by linarith) by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hr''
    apply this
  intro k
  induction' k with k hk
  · simp only [E.edgeEpiSteps_eq_of_eq pq r' (r' + Nat.zero) (by simp),
      E.edgeEpiSteps_eq_edgeEpiSteps_comp_pageXIsoOfEq_hom pq r r' (r' + Nat.zero) hr' (by simp)]
  · simp only [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r' (r' + k) (r' + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]), reassoc_of% hk,
      E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r' + k) (r' + k.succ) (by linarith)
      (by simp only [Nat.cast_succ, add_assoc])]

end

@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeMonoSteps (pq : ι) (r r' : ℤ) (hrr' : r ≤ r')
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasPage r] [E.HasPage r'] :
    E.edgeEpiSteps pq r r' hrr' ≫ E.edgeMonoSteps pq r r' hrr' = 𝟙 _ := by
  suffices ∀ (k : ℕ), E.edgeEpiSteps pq r (r + k) (by linarith) ≫
      E.edgeMonoSteps pq r (r + k) (by linarith) = 𝟙 _ by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hrr'
    apply this
  intro k
  induction' k with k hk
  · simp only [E.edgeEpiSteps_eq_of_eq pq r (r + Nat.zero) (by simp),
      E.edgeMonoSteps_eq_of_eq pq r (r + Nat.zero) (by simp), Iso.hom_inv_id]
  · simp only [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) (r + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]),
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) (r + k.succ)
        (by simp) (by simp only [Nat.cast_succ, add_assoc]),
      assoc, edgeEpiStep_edgeMonoStep_assoc, hk]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_edgeEpiSteps (pq : ι) (r r' : ℤ) (hrr' : r ≤ r')
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasPage r] [E.HasPage r'] :
    E.edgeMonoSteps pq r r' hrr' ≫ E.edgeEpiSteps pq r r' hrr' = 𝟙 _ := by
  suffices ∀ (k : ℕ), E.edgeMonoSteps pq r (r + k) (by linarith) ≫
      E.edgeEpiSteps pq r (r + k) (by linarith) = 𝟙 _ by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hrr'
    apply this
  intro k
  induction' k with k hk
  · simp only [E.edgeEpiSteps_eq_of_eq pq r (r + Nat.zero) (by simp),
      E.edgeMonoSteps_eq_of_eq pq r (r + Nat.zero) (by simp), Iso.inv_hom_id]
  · simp only [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) (r + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]),
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) (r + k.succ)
        (by simp) (by simp only [Nat.cast_succ, add_assoc]), assoc, reassoc_of% hk,
      edgeMonoStep_edgeEpiStep]

@[simps]
noncomputable def edgeIsoSteps (pq : ι) (r r' : ℤ) (hrr' : r ≤ r')
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasPage r] [E.HasPage r'] :
    (E.page r).X pq ≅ (E.page r').X pq where
  hom := E.edgeEpiSteps pq r r' hrr'
  inv := E.edgeMonoSteps pq r r' hrr'

noncomputable def pageInfinity (pq : ι) : C := by
  by_cases E.HasPageInfinityAt pq
  · exact (E.page (E.rMin pq)).X pq
  · exact 0

section

variable (pq : ι) [E.HasPageInfinityAt pq]

noncomputable def pageInfinityIso' :
    E.pageInfinity pq ≅ (E.page (E.rMin pq)).X pq :=
  eqToIso (dif_pos (by infer_instance))

noncomputable def pageInfinityIso
    (r : ℤ) [E.HasPage r] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    E.pageInfinity pq ≅ (E.page r).X pq :=
  E.pageInfinityIso' pq ≪≫ E.edgeIsoSteps pq (E.rMin pq) r
    (max_le (E.LE_of_hasEdgeMonoAtFrom pq r) (E.LE_of_hasEdgeEpiAtFrom pq r))

@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeEpiSteps
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    (E.pageInfinityIso pq r).hom ≫ E.edgeEpiSteps pq r r' h =
      (E.pageInfinityIso pq r').hom := by
  simp [pageInfinityIso]

lemma pageInfinityIso_hom_edgeEpiStep
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    (E.pageInfinityIso pq r).hom ≫ E.edgeEpiStep pq r r' h =
      (E.pageInfinityIso pq r').hom := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep pq r r' h, pageInfinityIso_hom_edgeEpiSteps]

@[reassoc (attr := simp)]
lemma edgeEpiSteps_pageInfinityIso_inv
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv =
      (E.pageInfinityIso pq r).inv := by
  simp only [← cancel_epi (E.pageInfinityIso pq r).hom,
    pageInfinityIso_hom_edgeEpiSteps_assoc, Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma edgeEpiStep_pageInfinityIso_inv
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv =
      (E.pageInfinityIso pq r).inv := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep pq r r' h, edgeEpiSteps_pageInfinityIso_inv]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_pageInfinityIso_inv
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    E.edgeMonoSteps pq r r' h ≫ (E.pageInfinityIso pq r).inv =
      (E.pageInfinityIso pq r').inv := by
  simp [pageInfinityIso]

@[reassoc (attr := simp)]
lemma edgeMonoStep_pageInfinityIso_inv
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    E.edgeMonoStep pq r r' h ≫ (E.pageInfinityIso pq r).inv =
      (E.pageInfinityIso pq r').inv := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep pq r r' h, edgeMonoSteps_pageInfinityIso_inv]

@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeMonoSteps
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h =
      (E.pageInfinityIso pq r).hom := by
  simp only [← cancel_mono (E.pageInfinityIso pq r).inv,
    assoc, edgeMonoSteps_pageInfinityIso_inv, Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeMonoStep
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r']
    [E.HasPage r] [E.HasPage r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h =
      (E.pageInfinityIso pq r).hom := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep pq r r' h, pageInfinityIso_hom_edgeMonoSteps]

noncomputable def edgeMono (r : ℤ) [E.HasPage r] [E.HasEdgeMonoAtFrom pq r] :
    E.pageInfinity pq ⟶ (E.page r).X pq :=
  if h : r ≤ E.rMin pq
    then
      (E.pageInfinityIso' pq).hom ≫ E.edgeMonoSteps pq r _ h
    else
      have : E.HasEdgeEpiAtFrom pq r := ⟨by
        simp only [not_le] at h
        linarith [E.rFromMin_LE_rMin pq]⟩
      (E.pageInfinityIso pq r).hom

instance (r : ℤ) [E.HasPage r] [E.HasEdgeMonoAtFrom pq r] :
    Mono (E.edgeMono pq r) := by
  dsimp [edgeMono]
  split_ifs <;> infer_instance

@[reassoc (attr := simp)]
lemma edgeMono_edgeMonoSteps (r r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] :
    E.edgeMono pq r' ≫ E.edgeMonoSteps pq r r' h = E.edgeMono pq r := by
  by_cases hr : r ≤ E.rMin pq
  · dsimp [edgeMono]
    rw [dif_pos hr]
    by_cases hr' : r' ≤ E.rMin pq
    · simp [dif_pos hr']
    · rw [dif_neg hr']
      dsimp [pageInfinityIso]
      simp only [assoc]
      congr 1
      rw [← cancel_epi (E.edgeIsoSteps pq (E.rMin pq) r' (by linarith)).inv,
        edgeIsoSteps_inv, edgeMonoSteps_edgeEpiSteps_assoc, edgeMonoSteps_comp]
  · dsimp [edgeMono]
    rw [dif_neg hr, dif_neg (by linarith)]
    dsimp [pageInfinityIso]
    simp only [assoc]
    have : E.HasEdgeEpiAtFrom pq r := ⟨by linarith [E.rFromMin_LE_rMin pq]⟩
    rw [← cancel_mono (E.edgeIsoSteps pq r r' h).hom, assoc, assoc, assoc,
      edgeIsoSteps_hom, edgeMonoSteps_edgeEpiSteps, comp_id, edgeEpiSteps_comp]

-- priority less than that of pageInfinityIso_hom_edgeMonoSteps
@[reassoc (attr := simp 900)]
lemma pageInfinityIso_hom_edgeMonoSteps' (r r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h = E.edgeMono pq r := by
  rw [← E.edgeMono_edgeMonoSteps pq r r' h]
  congr 1
  dsimp [edgeMono]
  split_ifs with h'
  · rw [← E.pageInfinityIso_hom_edgeMonoSteps pq _ _ h']
    dsimp [pageInfinityIso]
    rw [edgeEpiSteps_eq_id, comp_id]
  · rfl

lemma edgeMono_eq_pageInfinityIso_hom (r : ℤ) [E.HasPage r]
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r] :
    E.edgeMono pq r = (E.pageInfinityIso pq r).hom := by
  rw [← E.pageInfinityIso_hom_edgeMonoSteps' pq r r (by rfl),
    edgeMonoSteps_eq_id, comp_id]

@[reassoc (attr := simp 900)]
lemma pageInfinityIso_hom_edgeMonoStep' (r r' : ℤ) (h : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h = E.edgeMono pq r := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep, pageInfinityIso_hom_edgeMonoSteps']

noncomputable def edgeEpi (r : ℤ) [E.HasPage r] [E.HasEdgeEpiAtFrom pq r] :
    (E.page r).X pq ⟶ E.pageInfinity pq :=
  if h : r ≤ E.rMin pq
    then
      E.edgeEpiSteps pq r _ h ≫ (E.pageInfinityIso' pq).inv
    else
      have : E.HasEdgeMonoAtFrom pq r := ⟨by
        simp only [not_le] at h
        linarith [E.rToMin_LE_rMin pq]⟩
      (E.pageInfinityIso pq r).inv

instance (r : ℤ) [E.HasPage r] [E.HasEdgeEpiAtFrom pq r] :
    Epi (E.edgeEpi pq r) := by
  dsimp [edgeEpi]
  split_ifs <;> infer_instance

@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeEpi (r r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' h ≫ E.edgeEpi pq r' = E.edgeEpi pq r := by
  by_cases hr : r ≤ E.rMin pq
  · dsimp [edgeEpi]
    rw [dif_pos hr]
    by_cases hr' : r' ≤ E.rMin pq
    · simp [dif_pos hr']
    · rw [dif_neg hr']
      dsimp [pageInfinityIso]
      simp only [← assoc]
      congr 1
      rw [← cancel_mono (E.edgeIsoSteps pq (E.rMin pq) r' (by linarith)).hom,
        edgeIsoSteps_hom, assoc, edgeMonoSteps_edgeEpiSteps, comp_id, edgeEpiSteps_comp]
  · dsimp [edgeEpi]
    rw [dif_neg hr, dif_neg (by linarith)]
    dsimp [pageInfinityIso]
    have : E.HasEdgeMonoAtFrom pq r := ⟨by linarith [E.rToMin_LE_rMin pq]⟩
    rw [← cancel_epi (E.edgeIsoSteps pq r r' h).inv,
      edgeIsoSteps_inv, edgeMonoSteps_edgeEpiSteps_assoc, edgeMonoSteps_comp_assoc]

-- priority less than that of edgeEpiSteps_pageInfinityIso_inv
@[reassoc (attr := simp 900)]
lemma edgeEpiSteps_pageInfinityIso_inv' (r r' : ℤ) (h : r ≤ r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r := by
  rw [← E.edgeEpiSteps_edgeEpi pq r r' h]
  congr 1
  dsimp [edgeEpi]
  split_ifs with h'
  · rw [← E.edgeEpiSteps_pageInfinityIso_inv pq _ _ h']
    dsimp [pageInfinityIso]
    rw [edgeMonoSteps_eq_id, id_comp]
  · rfl

@[reassoc (attr := simp 900)]
lemma edgeEpiStep_pageInfinityIso_inv' (r r' : ℤ) (h : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep, edgeEpiSteps_pageInfinityIso_inv']

lemma edgeEpi_eq_pageInfinityIso_inv (r : ℤ) [E.HasPage r]
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r] :
    E.edgeEpi pq r = (E.pageInfinityIso pq r).inv := by
  rw [← E.edgeEpiSteps_pageInfinityIso_inv' pq r r (by rfl),
    edgeEpiSteps_eq_id, id_comp]

end

namespace Hom

variable {E}
variable {E' : SpectralSequence C c r₀} (f : E ⟶ E')

noncomputable def mapPageInfinity (pq : ι) :
    E.pageInfinity pq ⟶ E'.pageInfinity pq := by
  by_cases E.HasPageInfinityAt pq
  · by_cases E'.HasPageInfinityAt pq
    · exact (E.pageInfinityIso pq _).hom ≫ (f.hom (max (E.rMin pq) (E'.rMin pq))).f pq ≫
        (E'.pageInfinityIso pq _).inv
    · exact 0
  · exact 0

-- TODO: naturality of edgeEpiStep(s)

@[reassoc]
lemma edgeMonoStep_naturality (pq : ι) (r r' : ℤ) (hrr' : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r]
    [E'.HasPage r] [E'.HasPage r'] [E'.HasEdgeMonoAt pq r] :
    E.edgeMonoStep pq r r' hrr' ≫ (f.hom r).f pq =
      (f.hom r').f pq ≫ E'.edgeMonoStep pq r r' hrr' := by
  rw [← cancel_epi (E.iso r r' hrr' pq).hom, iso_hom_comp_edgeMonoStep_assoc,
    ← cancel_epi ((E.page r).isoHomologyπ _ pq rfl (by simp)).hom,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    ← Hom.comm_assoc f r r' hrr' pq, iso_hom_comp_edgeMonoStep,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, HomologicalComplex.cyclesMap_i]

@[reassoc]
lemma edgeMonoSteps_naturality (pq : ι)
    (r r' : ℤ) (hr : r ≤ r') [E.HasPage r] [E.HasPage r'] [E'.HasPage r] [E'.HasPage r']
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeMonoAtFrom pq r] [E'.HasEdgeMonoAtFrom pq r] :
    E.edgeMonoSteps pq r r' hr ≫ (f.hom r).f pq =
      (f.hom r').f pq ≫ E'.edgeMonoSteps pq r r' hr := by
  obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le hr
  revert r'
  induction' k with k hk
  · intro r' hrr' _ _ hr'
    obtain rfl : r = r' := by simp [hr']
    simp
  · intro r' hrr' _ _ hr'
    simp only [Nat.cast_succ, ← add_assoc] at hr'
    rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r'
      (by linarith) hr'.symm, assoc, hk (r + k) (by linarith) rfl,
      edgeMonoStep_naturality_assoc,
      E'.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r'
        (by linarith) hr'.symm]

lemma mapPageInfinity_eq (pq : ι) (r : ℤ)
    [E.HasPageInfinityAt pq] [E.HasPage r] [E'.HasPageInfinityAt pq] [E'.HasPage r]
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E'.HasEdgeMonoAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r] :
    mapPageInfinity f pq =
      (E.pageInfinityIso pq r).hom ≫ (f.hom r).f pq ≫ (E'.pageInfinityIso pq r).inv := by
  set r' := max (E.rMin pq) (E'.rMin pq)
  have hr : r' ≤ r := max_le
    (max_le (E.LE_of_hasEdgeMonoAtFrom pq r) (E.LE_of_hasEdgeEpiAtFrom pq r))
    (max_le (E'.LE_of_hasEdgeMonoAtFrom pq r) (E'.LE_of_hasEdgeEpiAtFrom pq r))
  dsimp [mapPageInfinity]
  rw [dif_pos (by infer_instance), dif_pos (by infer_instance),
    ← E.pageInfinityIso_hom_edgeEpiSteps pq r' r hr,
    ← E'.edgeMonoSteps_pageInfinityIso_inv pq r' r hr, assoc,
    ← edgeMonoSteps_naturality_assoc, edgeEpiSteps_edgeMonoSteps_assoc]

lemma isIso_mapPageInfinity_of_isIso_hom (r : ℤ) (pq : ι) [E.HasPage r] [E'.HasPage r]
    (hf : IsIso (f.hom r)) [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq] :
    IsIso (mapPageInfinity f pq) := by
  let r' := max r (max (E.rMin pq) (E'.rMin pq))
  rw [mapPageInfinity_eq f pq r']
  have := isIso_hom_of_GE f r r' (le_max_left _ _) hf
  have : IsIso ((f.hom r').f pq) := by
    -- this should already be an instance
    change IsIso ((HomologicalComplex.eval C _ pq).map (f.hom r'))
    infer_instance
  infer_instance

end Hom

end SpectralSequence

namespace CohomologicalSpectralSequenceNat

variable (E : CohomologicalSpectralSequenceNat C r₀)

lemma hasEdgeEpiAt
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.2 + 2 ≤ r) [E.HasPage r] :
    E.HasEdgeEpiAt pq r where
  zero pq' := by
    apply HomologicalComplex.shape
    intro h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    linarith

lemma hasEdgeMonoAt
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.1 + 1 ≤ r) [E.HasPage r] :
    E.HasEdgeMonoAt pq r where
  zero pq' := by
    apply HomologicalComplex.shape
    intro h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    linarith

instance (pq : ℕ × ℕ) : E.HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet := ⟨max r₀ (pq.2 + 2), fun r hr =>
    have := E.hasPage_of_LE r₀ r ((le_max_left _ _).trans hr)
    ⟨this, E.hasEdgeEpiAt pq r ((le_max_right _ _).trans hr)⟩⟩
  nonempty_hasEdgeMonoSet := ⟨max r₀ (pq.1 + 1), fun r hr =>
    have := E.hasPage_of_LE r₀ r ((le_max_left _ _).trans hr)
    ⟨this, E.hasEdgeMonoAt pq r ((le_max_right _ _).trans hr)⟩⟩

lemma hasEdgeEpiAtFrom
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.2 + 2 ≤ r) [E.HasPage r] :
    E.HasEdgeEpiAtFrom pq r where
  le := by
    apply E.rFromMin_LE
    intro r' hrr'
    have := E.hasPage_of_LE _ _ hrr'
    refine' ⟨inferInstance, _⟩
    apply hasEdgeEpiAt
    linarith

lemma hasEdgeMonoAtFrom
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.1 + 1 ≤ r) [E.HasPage r] :
    E.HasEdgeMonoAtFrom pq r where
  le := by
    apply E.rToMin_LE
    intro r' hrr'
    have := E.hasPage_of_LE _ _ hrr'
    refine' ⟨inferInstance, _⟩
    apply hasEdgeMonoAt
    linarith

instance (p : ℕ) [E.HasPage 2]: E.HasEdgeEpiAtFrom ⟨p, 0⟩ 2 := by
  apply hasEdgeEpiAtFrom
  dsimp
  linarith

instance (p : ℕ) [E.HasPage 2] : E.HasEdgeEpiAtFrom ⟨p, 1⟩ 3 := by
  apply hasEdgeEpiAtFrom
  dsimp
  linarith

instance (q : ℕ) [E.HasPage 2] : E.HasEdgeMonoAtFrom ⟨0, q⟩ 2 := by
  apply hasEdgeMonoAtFrom
  dsimp
  linarith

instance (q : ℕ) [E.HasPage 2] : E.HasEdgeMonoAtFrom ⟨1, q⟩ 2 := by
  apply hasEdgeMonoAtFrom
  dsimp
  linarith

instance (q : ℕ) [E.HasPage 2]: E.HasEdgeMonoAtFrom ⟨2, q⟩ 3 := by
  apply hasEdgeMonoAtFrom
  dsimp
  linarith

end CohomologicalSpectralSequenceNat

end CategoryTheory
