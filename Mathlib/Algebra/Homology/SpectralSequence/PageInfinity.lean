/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.EdgeStep

/-!
# The infinity page of a spectral sequence

-/

@[expose] public section

lemma Set.has_min_of_ℤ (S : Set ℤ) (hS : S.Nonempty) (m₀ : ℤ)
    (hm₀ : ∀ (x : ℤ) (_ : x ∈ S), m₀ ≤ x) :
    ∃ (m : ℤ) (_ : m ∈ S), ∀ (x : ℤ) (_ : x ∈ S), m ≤ x := by
  let T : Set ℕ := fun i => m₀ + i ∈ S
  obtain ⟨x, hx⟩ := hS
  obtain ⟨t₀, rfl⟩ := Int.le.dest (hm₀ x hx)
  have hT : T.Nonempty := ⟨t₀, hx⟩
  let μ := (Nat.lt_wfRel.wf).min T hT
  refine ⟨m₀ + μ, (Nat.lt_wfRel.wf).min_mem T hT, fun y hy => ?_⟩
  have hy' : 0 ≤ y - m₀ := by have := hm₀ y hy; lia
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hy'
  obtain rfl : y = m₀ + t := by lia
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
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀ (fun _ hx ↦ hx.1)).choose

lemma rToMin_mem : E.rToMin pq ∈ E.hasEdgeMonoSet pq :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀ (fun _ hx ↦ hx.1)).choose_spec.choose

lemma rToMin_LE (r : ℤ) (hr : r ∈ E.hasEdgeMonoSet pq) :
    E.rToMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun _ hx => hx.1)).choose_spec.choose_spec r hr

lemma LE_rToMin :
    r₀ ≤ E.rToMin pq :=
  (E.rToMin_mem pq).1

noncomputable def rFromMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀ (fun _ hx => hx.1)).choose

lemma rFromMin_mem : E.rFromMin pq ∈ E.hasEdgeEpiSet pq :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose

lemma rFromMin_LE (r : ℤ) (hr : r ∈ E.hasEdgeEpiSet pq) :
    E.rFromMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun _ hx => hx.1)).choose_spec.choose_spec r hr

lemma LE_rFromMin :
    r₀ ≤ E.rFromMin pq :=
  (E.rFromMin_mem pq).1

noncomputable def rMin : ℤ := max (E.rToMin pq) (E.rFromMin pq)

lemma rFromMin_LE_rMin : E.rFromMin pq ≤ E.rMin pq := le_max_right _ _

lemma rToMin_LE_rMin : E.rToMin pq ≤ E.rMin pq := le_max_left _ _

lemma LE_rMin :
    r₀ ≤ E.rMin pq :=
  (E.LE_rFromMin pq).trans (E.rFromMin_LE_rMin pq)

end

lemma d_to_eq_zero (r : ℤ) (pq pq' : ι) [E.HasPageInfinityAt pq']
    (hr : E.rToMin pq' ≤ r) :
    (E.page r (by have := E.LE_rToMin pq'; lia)).d pq pq' = 0 := by
  have := (E.rToMin_mem pq').2 _ hr
  simp

lemma d_from_eq_zero (r : ℤ) (pq pq' : ι) [E.HasPageInfinityAt pq]
    (hr : E.rFromMin pq ≤ r) :
    (E.page r (by have := E.LE_rFromMin pq; lia)).d pq pq' = 0 := by
  have := (E.rFromMin_mem pq).2 _ hr
  simp

lemma hasEdgeMonoAt_of_rToMin_LE (pq : ι) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : E.rToMin pq ≤ r) :
    E.HasEdgeMonoAt pq r where
  le := (E.LE_rToMin pq).trans hr
  zero pq' := E.d_to_eq_zero r pq' pq hr

lemma hasEdgeEpiAt_of_rFromMin_LE (pq : ι) [E.HasPageInfinityAt pq] (r : ℤ)
    (hr : E.rFromMin pq ≤ r) :
    E.HasEdgeEpiAt pq r where
  le := (E.LE_rFromMin pq).trans hr
  zero pq' := E.d_from_eq_zero r pq pq' hr

section

variable (pq : ι) (r : ℤ) [E.HasPageInfinityAt pq]

class HasEdgeMonoAtFrom : Prop where
  le : E.rToMin pq ≤ r

instance : E.HasEdgeMonoAtFrom pq (E.rToMin pq) where
  le := by rfl

instance : E.HasEdgeMonoAtFrom pq (E.rMin pq) where
  le := E.rToMin_LE_rMin pq

/-- Constructor for `HasEdgeMonoAtFrom`. -/
lemma HasEdgeMonoAtFrom.mk' (h : ∀ (k : ℕ), E.HasEdgeMonoAt pq (r + k)) (hr : r₀ ≤ r := by lia) :
    E.HasEdgeMonoAtFrom pq r where
  le := E.rToMin_LE _ _ ⟨hr, fun r' hr' ↦ by
    obtain ⟨k, rfl⟩ := Int.le.dest hr'
    infer_instance⟩

variable [E.HasEdgeMonoAtFrom pq r]

lemma LE_of_hasEdgeMonoAtFrom : E.rToMin pq ≤ r := by apply HasEdgeMonoAtFrom.le

include E pq in
lemma le₀_of_hasEdgeMonoAtFrom : r₀ ≤ r :=
  (E.LE_rToMin pq).trans (E.LE_of_hasEdgeMonoAtFrom pq r)

lemma mem_hasEdgeMonoSet : r ∈ E.hasEdgeMonoSet pq :=
  ⟨(E.LE_rToMin pq).trans HasEdgeMonoAtFrom.le, fun _ hrr' ↦
    ⟨(E.le₀_of_hasEdgeMonoAtFrom pq r).trans hrr',
      fun _ ↦  E.d_to_eq_zero _ _ _ ((E.LE_of_hasEdgeMonoAtFrom pq r).trans hrr')⟩⟩

lemma hasEdgeMonoAtFrom_of_GE (r' : ℤ) (_ : r ≤ r' := by lia) :
    E.HasEdgeMonoAtFrom pq r' where
  le := by have := E.LE_of_hasEdgeMonoAtFrom pq r; lia

instance (r' : ℤ) :
    E.HasEdgeMonoAtFrom pq (max r r') :=
  E.hasEdgeMonoAtFrom_of_GE pq r _ (le_max_left _ _)

instance (r' : ℤ) :
    E.HasEdgeMonoAtFrom pq (max r' r) :=
  E.hasEdgeMonoAtFrom_of_GE pq r _ (le_max_right _ _)

instance : E.HasEdgeMonoAt pq r where
  le := E.le₀_of_hasEdgeMonoAtFrom pq r
  zero pq' := E.d_to_eq_zero r pq' pq (E.LE_of_hasEdgeMonoAtFrom pq r)

instance (k : ℕ) : E.HasEdgeMonoAtFrom pq (r + k) where
  le := by have := E.LE_of_hasEdgeMonoAtFrom pq r; lia

instance [E.HasEdgeMonoAtFrom pq 2] : E.HasEdgeMonoAtFrom pq 3 := by
  change E.HasEdgeMonoAtFrom pq (2 + (1 : ℕ))
  infer_instance

/-- Auxiliary definition for `edgeMonoSteps`. -/
noncomputable def edgeMonoSteps' (k : ℕ) :
    (E.page (r + k) (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).X pq ⟶
      (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq := by
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)
      (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).hom
  | succ k hk => exact E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ hk

@[simp]
lemma edgeMonoSteps'_zero :
    E.edgeMonoSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)
      (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).hom := rfl

@[simp]
lemma edgeMonoSteps'_succ (k : ℕ) :
    E.edgeMonoSteps' pq r (k + 1) =
      E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ E.edgeMonoSteps' pq r k := rfl

instance (k : ℕ) : Mono (E.edgeMonoSteps' pq r k) := by
  induction k with
  | zero => simp only [edgeMonoSteps'_zero]; infer_instance
  | succ => simp only [edgeMonoSteps'_succ]; infer_instance

noncomputable def edgeMonoSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    (E.page r' (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).X pq ⟶
      (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq :=
  (E.pageXIsoOfEq pq _ _ (by
    obtain ⟨k, rfl⟩ := Int.le.dest h
    simp) (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).inv ≫
      E.edgeMonoSteps' pq r (Int.toNat (r' - r))

instance (r' : ℤ) (h : r ≤ r') :
    Mono (E.edgeMonoSteps pq r r' h) := by
  dsimp [edgeMonoSteps]
  infer_instance

lemma edgeMonoSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
      (E.pageXIsoOfEq pq _ _ h (by
        have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).inv ≫ E.edgeMonoSteps' pq r k := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

/-- `edgeMonoSteps` identifies to `edgeMonoSteps'`. -/
lemma edgeMonoSteps_eq_edgeMonoSteps' (k : ℕ) :
    E.edgeMonoSteps pq r (r + k) (by lia) =
      E.edgeMonoSteps' pq r k := by
  simp [E.edgeMonoSteps_eq pq r (r + k) k rfl, pageXIsoOfEq]

@[simp]
lemma edgeMonoSteps_eq_id :
    E.edgeMonoSteps pq r r (by rfl) = 𝟙 _ := by
  rw [E.edgeMonoSteps_eq pq r r 0 (by simp), edgeMonoSteps'_zero, Iso.inv_hom_id]

lemma edgeMonoSteps_eq_of_eq (r' : ℤ) (h : r = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
    (E.pageXIsoOfEq pq r r' h (E.le₀_of_hasEdgeMonoAtFrom pq r)).inv := by
  subst h
  rw [edgeMonoSteps_eq_id]
  rfl

lemma edgeMonoSteps_eq_pageXIsoOfEq_inv_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' = r'' := by lia) :
    E.edgeMonoSteps pq r r'' (by lia) =
      (E.pageXIsoOfEq pq r' r'' h₂ (by
        have := E.le₀_of_hasEdgeMonoAtFrom pq r
        lia)).inv ≫ E.edgeMonoSteps pq r r' h₁ := by
  subst h₂
  simp [pageXIsoOfEq]

@[reassoc]
lemma edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia)
    [E.HasEdgeMonoAt pq r'] :
    E.edgeMonoSteps pq r r'' (by lia) =
      E.edgeMonoStep pq r' r'' h₂ ≫ E.edgeMonoSteps pq r r' h₁ := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeMonoSteps_eq_edgeMonoSteps',
    E.edgeMonoSteps_eq_edgeMonoSteps', E.edgeMonoSteps'_succ]

lemma edgeMonoSteps_eq_edgeMonoStep
    (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
    E.edgeMonoStep pq r r' h := by
  rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r r r' (by rfl) h,
    E.edgeMonoSteps_eq_id, comp_id]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp (r' r'' : ℤ) [E.HasEdgeMonoAtFrom pq r']
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    E.edgeMonoSteps pq r' r'' hr'' ≫ E.edgeMonoSteps pq r r' hr' =
      E.edgeMonoSteps pq r r'' (hr'.trans hr'') := by
  suffices ∀ (k : ℕ), E.edgeMonoSteps pq r' (r' + k) (by lia) ≫
      E.edgeMonoSteps pq r r' hr' =
        E.edgeMonoSteps pq r (r' + k) (by lia) by
    obtain ⟨k, rfl⟩ := Int.le.dest hr''
    apply this
  intro k
  induction k with
  | zero => simp only [E.edgeMonoSteps_eq_of_eq pq r' (r' + Nat.zero) (by simp),
      E.edgeMonoSteps_eq_pageXIsoOfEq_inv_comp_edgeMonoSteps pq r r' (r' + Nat.zero) hr' (by simp)]
  | succ k hk =>
    simp only [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r' (r' + k) (r' + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]), assoc, hk,
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r' + k) (r' + k.succ) (by lia)
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

/-- Constructor for `HasEdgeEpiAtFrom`. -/
lemma HasEdgeEpiAtFrom.mk' (hr : ∀ (k : ℕ), E.HasEdgeEpiAt pq (r + k)) (hr : r₀ ≤ r := by lia) :
    E.HasEdgeEpiAtFrom pq r where
  le := E.rFromMin_LE _ _ ⟨hr, fun r' hr' ↦ by
    obtain ⟨k, rfl⟩ := Int.le.dest hr'
    infer_instance⟩

variable [E.HasEdgeEpiAtFrom pq r]

lemma LE_of_hasEdgeEpiAtFrom : E.rFromMin pq ≤ r := by apply HasEdgeEpiAtFrom.le

include E pq in
lemma le₀_of_hasEdgeEpiAtFrom : r₀ ≤ r :=
  (E.LE_rFromMin pq).trans (E.LE_of_hasEdgeEpiAtFrom pq r)

lemma mem_hasEdgeEpiSet : r ∈ E.hasEdgeEpiSet pq :=
  ⟨(E.LE_rFromMin pq).trans HasEdgeEpiAtFrom.le, fun _ hrr' ↦
    ⟨(E.le₀_of_hasEdgeEpiAtFrom pq r).trans hrr',
      fun _ ↦ E.d_from_eq_zero _ _ _ ((E.LE_of_hasEdgeEpiAtFrom pq r).trans hrr')⟩⟩

lemma hasEdgeEpiAtFrom_of_GE (r' : ℤ) (_ : r ≤ r' := by lia) :
    E.HasEdgeEpiAtFrom pq r' where
  le := by have := E.LE_of_hasEdgeEpiAtFrom pq r; lia

instance (r' : ℤ) :
    E.HasEdgeEpiAtFrom pq (max r r') :=
  E.hasEdgeEpiAtFrom_of_GE pq r _ (le_max_left _ _)

instance (r' : ℤ) :
    E.HasEdgeEpiAtFrom pq (max r' r) :=
  E.hasEdgeEpiAtFrom_of_GE pq r _ (le_max_right _ _)

instance : E.HasEdgeEpiAt pq r where
  le := E.le₀_of_hasEdgeEpiAtFrom pq r
  zero pq' := E.d_from_eq_zero r pq pq' (E.LE_of_hasEdgeEpiAtFrom pq r)

instance (k : ℕ) : E.HasEdgeEpiAtFrom pq (r + k) where
  le := by have := E.LE_of_hasEdgeEpiAtFrom pq r; lia

instance [E.HasEdgeEpiAtFrom pq 2] : E.HasEdgeEpiAtFrom pq 3 := by
  change E.HasEdgeEpiAtFrom pq (2 + (1 : ℕ))
  infer_instance

/-- Auxiliary definition for `edgeEpiSteps`. -/
noncomputable def edgeEpiSteps' (k : ℕ) :
    (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq ⟶ (E.page (r + k) (by
      have := E.le₀_of_hasEdgeEpiAtFrom pq r
      lia)).X pq := by
  have := E.le₀_of_hasEdgeEpiAtFrom pq r
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)).inv
  | succ k hk =>
    exact hk ≫ E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ))

@[simp]
lemma edgeEpiSteps'_zero :
    E.edgeEpiSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp) (by
      have := E.le₀_of_hasEdgeEpiAtFrom pq r
      lia)).inv := rfl

@[simp]
lemma edgeEpiSteps'_succ (k : ℕ) :
    E.edgeEpiSteps' pq r (k + 1) = E.edgeEpiSteps' pq r k ≫
      E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ)) := rfl

instance (k : ℕ) : Epi (E.edgeEpiSteps' pq r k) := by
  induction k with
  | zero => simp only [edgeEpiSteps'_zero]; infer_instance
  | succ => simp only [edgeEpiSteps'_succ]; infer_instance

noncomputable def edgeEpiSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq ⟶
      (E.page r' (by have := E.le₀_of_hasEdgeEpiAtFrom pq r; lia)).X pq :=
  E.edgeEpiSteps' pq r (Int.toNat (r' - r)) ≫ (E.pageXIsoOfEq pq _ _ (by
    obtain ⟨k, rfl⟩ := Int.le.dest h
    simp) (by have := E.le₀_of_hasEdgeEpiAtFrom pq r; lia)).hom

instance (r' : ℤ) (h : r ≤ r') :
    Epi (E.edgeEpiSteps pq r r' h) := by
  dsimp [edgeEpiSteps]
  infer_instance

lemma edgeEpiSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
      E.edgeEpiSteps' pq r k ≫ (E.pageXIsoOfEq pq _ _ h (by
        have := E.le₀_of_hasEdgeEpiAtFrom pq r
        lia)).hom := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

/-- `edgeEpiSteps` identifies to `edgeEpiSteps'`. -/
lemma edgeEpiSteps_eq_edgeEpiSteps' (k : ℕ) :
    E.edgeEpiSteps pq r (r + k) =
      E.edgeEpiSteps' pq r k := by
  simp [E.edgeEpiSteps_eq pq r (r + k) k rfl, pageXIsoOfEq]

@[simp]
lemma edgeEpiSteps_eq_id :
    E.edgeEpiSteps pq r r (by rfl) = 𝟙 _ := by
  rw [E.edgeEpiSteps_eq pq r r 0, edgeEpiSteps'_zero, Iso.inv_hom_id]

lemma edgeEpiSteps_eq_of_eq (r' : ℤ) (h : r = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
    (E.pageXIsoOfEq pq r r' h (E.le₀_of_hasEdgeEpiAtFrom pq r)).hom := by
  subst h
  rw [edgeEpiSteps_eq_id]
  rfl

@[reassoc]
lemma edgeEpiSteps_eq_edgeEpiSteps_comp_pageXIsoOfEq_hom
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' = r'' := by lia) :
    E.edgeEpiSteps pq r r'' (by lia) =
    E.edgeEpiSteps pq r r' h₁ ≫ (E.pageXIsoOfEq pq r' r'' h₂ (by
      have := E.le₀_of_hasEdgeEpiAtFrom pq r
      lia)).hom := by
  subst h₂
  simp [pageXIsoOfEq]

lemma edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia)
    [E.HasEdgeEpiAt pq r'] :
    E.edgeEpiSteps pq r r'' (by lia) =
      E.edgeEpiSteps pq r r' h₁ ≫ E.edgeEpiStep pq r' r'' h₂ := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeEpiSteps_eq_edgeEpiSteps', E.edgeEpiSteps_eq_edgeEpiSteps',
    E.edgeEpiSteps'_succ]

lemma edgeEpiSteps_eq_edgeEpiStep (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
      E.edgeEpiStep pq r r' h := by
  rw [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r r r' (by rfl) h,
    E.edgeEpiSteps_eq_id, id_comp]

@[reassoc (attr := simp)]
lemma edgeEpiSteps_comp (r' r'' : ℤ) [E.HasEdgeEpiAtFrom pq r']
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    E.edgeEpiSteps pq r r' hr' ≫ E.edgeEpiSteps pq r' r'' hr'' =
      E.edgeEpiSteps pq r r'' (hr'.trans hr'') := by
  suffices ∀ (k : ℕ), E.edgeEpiSteps pq r r' hr' ≫
      E.edgeEpiSteps pq r' (r' + k) = E.edgeEpiSteps pq r (r' + k) by
    obtain ⟨k, rfl⟩ := Int.le.dest hr''
    apply this
  intro k
  induction k with
  | zero =>
    simp only [E.edgeEpiSteps_eq_of_eq pq r' (r' + Nat.zero),
      E.edgeEpiSteps_eq_edgeEpiSteps_comp_pageXIsoOfEq_hom pq r r' (r' + Nat.zero)]
  | succ k hk =>
    simp only [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r' (r' + k) (r' + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]), reassoc_of% hk,
      E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r' + k) (r' + k.succ)]

end

@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeMonoSteps (pq : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    (hrr' : r ≤ r' := by lia) :
    E.edgeEpiSteps pq r r' hrr' ≫ E.edgeMonoSteps pq r r' hrr' = 𝟙 _ := by
  suffices ∀ (k : ℕ), E.edgeEpiSteps pq r (r + k) ≫
      E.edgeMonoSteps pq r (r + k) = 𝟙 _ by
    obtain ⟨k, rfl⟩ := Int.le.dest hrr'
    apply this
  intro k
  induction k with
  | zero =>
    simp only [E.edgeEpiSteps_eq_of_eq pq r (r + Nat.zero),
      E.edgeMonoSteps_eq_of_eq pq r (r + Nat.zero), Iso.hom_inv_id]
  | succ k hk =>
    simp only [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) (r + k.succ),
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) (r + k.succ),
      assoc, edgeEpiStep_edgeMonoStep_assoc, hk]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_edgeEpiSteps (pq : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    (hrr' : r ≤ r' := by lia) :
    E.edgeMonoSteps pq r r' hrr' ≫ E.edgeEpiSteps pq r r' hrr' = 𝟙 _ := by
  suffices ∀ (k : ℕ), E.edgeMonoSteps pq r (r + k) ≫
      E.edgeEpiSteps pq r (r + k) = 𝟙 _ by
    obtain ⟨k, rfl⟩ := Int.le.dest hrr'
    apply this
  intro k
  induction k with
  | zero =>
    simp only [E.edgeEpiSteps_eq_of_eq pq r (r + Nat.zero) (by simp),
      E.edgeMonoSteps_eq_of_eq pq r (r + Nat.zero) (by simp), Iso.inv_hom_id]
  | succ k hk =>
    simp only [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) (r + k.succ)
      (by simp) (by simp only [Nat.cast_succ, add_assoc]),
      E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) (r + k.succ)
        (by simp) (by simp only [Nat.cast_succ, add_assoc]), assoc, reassoc_of% hk,
      edgeMonoStep_edgeEpiStep]

@[simps]
noncomputable def edgeIsoSteps (pq : ι) (r r' : ℤ)
    [E.HasPageInfinityAt pq] [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    (hrr' : r ≤ r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq ≅ (E.page r' (by
      have := E.le₀_of_hasEdgeMonoAtFrom pq r
      lia)).X pq where
  hom := E.edgeEpiSteps pq r r' hrr'
  inv := E.edgeMonoSteps pq r r' hrr'

noncomputable def pageInfinity (pq : ι) : C := by
  by_cases E.HasPageInfinityAt pq
  · exact (E.page (E.rMin pq) (E.LE_rMin pq)).X pq
  · exact 0

section

variable (pq : ι) [E.HasPageInfinityAt pq]

/-- Auxiliary definition for `pageInfinityIso`. -/
noncomputable def pageInfinityIso' :
    E.pageInfinity pq ≅ (E.page (E.rMin pq) (E.LE_rMin pq)).X pq :=
  eqToIso (dif_pos (by infer_instance))

noncomputable def pageInfinityIso
    (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    E.pageInfinity pq ≅ (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq :=
  E.pageInfinityIso' pq ≪≫ E.edgeIsoSteps pq (E.rMin pq) r
    ((max_le (E.LE_of_hasEdgeMonoAtFrom pq r) (E.LE_of_hasEdgeEpiAtFrom pq r)))

@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeEpiSteps
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r).hom ≫ E.edgeEpiSteps pq r r' h =
      (E.pageInfinityIso pq r').hom := by
  simp [pageInfinityIso]

lemma pageInfinityIso_hom_edgeEpiStep
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r).hom ≫ E.edgeEpiStep pq r r' h =
      (E.pageInfinityIso pq r').hom := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep pq r r' h, pageInfinityIso_hom_edgeEpiSteps]

@[reassoc (attr := simp)]
lemma edgeEpiSteps_pageInfinityIso_inv
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv =
      (E.pageInfinityIso pq r).inv := by
  simp only [← cancel_epi (E.pageInfinityIso pq r).hom,
    pageInfinityIso_hom_edgeEpiSteps_assoc, Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma edgeEpiStep_pageInfinityIso_inv
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv =
      (E.pageInfinityIso pq r).inv := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep pq r r' h,
    edgeEpiSteps_pageInfinityIso_inv]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_pageInfinityIso_inv
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeMonoSteps pq r r' h ≫ (E.pageInfinityIso pq r).inv =
      (E.pageInfinityIso pq r').inv := by
  simp [pageInfinityIso]

@[reassoc (attr := simp)]
lemma edgeMonoStep_pageInfinityIso_inv
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeMonoStep pq r r' h ≫ (E.pageInfinityIso pq r).inv =
      (E.pageInfinityIso pq r').inv := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep pq r r' h,
    edgeMonoSteps_pageInfinityIso_inv]

@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeMonoSteps
    (r r' : ℤ) (h : r ≤ r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h =
      (E.pageInfinityIso pq r).hom := by
  simp only [← cancel_mono (E.pageInfinityIso pq r).inv,
    assoc, edgeMonoSteps_pageInfinityIso_inv, Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma pageInfinityIso_hom_edgeMonoStep
    (r r' : ℤ) (h : r + 1 = r') [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h =
      (E.pageInfinityIso pq r).hom := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep pq r r' h,
    pageInfinityIso_hom_edgeMonoSteps]

noncomputable def edgeMono (r : ℤ) [E.HasEdgeMonoAtFrom pq r] :
    E.pageInfinity pq ⟶ (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq :=
  if h : r ≤ E.rMin pq
    then
      (E.pageInfinityIso' pq).hom ≫ E.edgeMonoSteps pq r _ h
    else
      have : E.HasEdgeEpiAtFrom pq r := ⟨by
        have := E.rFromMin_LE_rMin pq
        lia⟩
      (E.pageInfinityIso pq r).hom

instance (r : ℤ) [E.HasEdgeMonoAtFrom pq r] :
    Mono (E.edgeMono pq r) := by
  dsimp [edgeMono]
  split_ifs <;> infer_instance

@[reassoc (attr := simp)]
lemma edgeMono_edgeMonoSteps (r r' : ℤ) (h : r ≤ r' := by lia)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] :
    E.edgeMono pq r' ≫ E.edgeMonoSteps pq r r' h =
      E.edgeMono pq r := by
  by_cases hr : r ≤ E.rMin pq
  · dsimp [edgeMono]
    rw [dif_pos hr]
    by_cases hr' : r' ≤ E.rMin pq
    · simp [dif_pos hr']
    · rw [dif_neg hr']
      dsimp [pageInfinityIso]
      simp only [assoc]
      congr 1
      simp only [← cancel_epi (E.edgeIsoSteps pq (E.rMin pq) r' (by lia)).inv,
        edgeIsoSteps_inv, edgeMonoSteps_edgeEpiSteps_assoc, edgeMonoSteps_comp]
  · dsimp [edgeMono]
    rw [dif_neg hr, dif_neg (by lia)]
    dsimp [pageInfinityIso]
    simp only [assoc]
    have : E.HasEdgeEpiAtFrom pq r := ⟨by have := E.rFromMin_LE_rMin pq; lia⟩
    simp only [← cancel_mono (E.edgeIsoSteps pq r r' h).hom,
      assoc, assoc, assoc, edgeIsoSteps_hom, edgeMonoSteps_edgeEpiSteps,
      comp_id, edgeEpiSteps_comp]

-- priority less than that of pageInfinityIso_hom_edgeMonoSteps
/-- `(E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h = E.edgeMono pq r`. -/
@[reassoc (attr := simp 900)]
lemma pageInfinityIso_hom_edgeMonoSteps' (r r' : ℤ) (h : r ≤ r' := by lia)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoSteps pq r r' h = E.edgeMono pq r := by
  rw [← E.edgeMono_edgeMonoSteps pq r r' h]
  congr 1
  dsimp [edgeMono]
  split_ifs with h'
  · rw [← E.pageInfinityIso_hom_edgeMonoSteps pq _ _ h']
    dsimp [pageInfinityIso]
    rw [E.edgeEpiSteps_eq_id _ _, comp_id]
  · rfl

lemma edgeMono_eq_pageInfinityIso_hom (r : ℤ)
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r] :
    E.edgeMono pq r = (E.pageInfinityIso pq r).hom := by
  rw [← E.pageInfinityIso_hom_edgeMonoSteps' pq r r (by rfl),
    E.edgeMonoSteps_eq_id, comp_id]

/-- `(E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h = E.edgeMono pq r`. -/
@[reassoc (attr := simp 900)]
lemma pageInfinityIso_hom_edgeMonoStep' (r r' : ℤ) (h : r + 1 = r' := by lia)
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    (E.pageInfinityIso pq r').hom ≫ E.edgeMonoStep pq r r' h = E.edgeMono pq r := by
  have := E.le₀_of_hasEdgeMonoAtFrom pq r
  rw [← E.edgeMonoSteps_eq_edgeMonoStep _ _ _, E.pageInfinityIso_hom_edgeMonoSteps' _ _ _]

noncomputable def edgeEpi (r : ℤ) [E.HasEdgeEpiAtFrom pq r] :
    (E.page r (E.le₀_of_hasEdgeEpiAtFrom pq r)).X pq ⟶ E.pageInfinity pq :=
  if h : r ≤ E.rMin pq
    then
      E.edgeEpiSteps pq r _ h ≫ (E.pageInfinityIso' pq).inv
    else
      have : E.HasEdgeMonoAtFrom pq r := ⟨by
        have := E.rToMin_LE_rMin pq
        lia⟩
      (E.pageInfinityIso pq r).inv

instance (r : ℤ) [E.HasEdgeEpiAtFrom pq r] :
    Epi (E.edgeEpi pq r) := by
  dsimp [edgeEpi]
  split_ifs <;> infer_instance

@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeEpi (r r' : ℤ) (h : r ≤ r')
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
      simp [← cancel_mono (E.edgeIsoSteps pq (E.rMin pq) r' (by lia)).hom]
  · dsimp [edgeEpi]
    rw [dif_neg hr, dif_neg (by lia)]
    dsimp [pageInfinityIso]
    have : E.HasEdgeMonoAtFrom pq r := ⟨by have := E.rToMin_LE_rMin pq; lia⟩
    simp [← cancel_epi (E.edgeIsoSteps pq r r' h).inv]

-- priority less than that of edgeEpiSteps_pageInfinityIso_inv
/-- `E.edgeEpiSteps pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r`. -/
@[reassoc (attr := simp 900)]
lemma edgeEpiSteps_pageInfinityIso_inv' (r r' : ℤ) (h : r ≤ r')
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

/-- `E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv = E.edgeEpi pq r`. -/
@[reassoc (attr := simp 900)]
lemma edgeEpiStep_pageInfinityIso_inv' (r r' : ℤ) (h : r + 1 = r')
    [E.HasEdgeEpiAtFrom pq r] [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r'] :
    E.edgeEpiStep pq r r' h ≫ (E.pageInfinityIso pq r').inv =
    E.edgeEpi pq r := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep _ _ _ h, edgeEpiSteps_pageInfinityIso_inv']

lemma edgeEpi_eq_pageInfinityIso_inv (r : ℤ)
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
    · exact (E.pageInfinityIso pq _).hom ≫ (f.hom (max (E.rMin pq) (E'.rMin pq))
        ((E.LE_rMin pq).trans (le_max_left _ _))).f pq ≫
        (E'.pageInfinityIso pq _).inv
    · exact 0
  · exact 0

-- TODO: naturality of edgeEpiStep(s)

@[reassoc]
lemma edgeMonoStep_naturality (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] [E'.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    E.edgeMonoStep pq r r' hrr' ≫ (f.hom r).f pq =
      (f.hom r').f pq ≫ E'.edgeMonoStep pq r r' hrr' := by
  rw [← cancel_epi (E.iso r r' pq hrr').hom, iso_hom_comp_edgeMonoStep_assoc _ _ _ _,
    ← cancel_epi ((E.page r).isoHomologyπ _ pq rfl (by simp)).hom,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    ← Hom.comm_assoc f r r' pq hrr', iso_hom_comp_edgeMonoStep _ _ _ _,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, HomologicalComplex.cyclesMap_i]

@[reassoc]
lemma edgeMonoSteps_naturality (pq : ι) (r r' : ℤ)
    (hrr' : r ≤ r' := by lia) (hr₀ : r₀ ≤ r := by lia)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeMonoAtFrom pq r] [E'.HasEdgeMonoAtFrom pq r] :
    E.edgeMonoSteps pq r r' hrr' ≫ (f.hom r).f pq =
      (f.hom r').f pq ≫ E'.edgeMonoSteps pq r r' hrr' := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r'
  induction k with
  | zero =>
    intro r' hrr' hr₀
    obtain rfl : r = r' := by omega
    simp
  | succ k hk =>
    intro r' hrr' hr₀
    rw [E.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r',
      assoc, hk (r + k) (by lia) rfl, edgeMonoStep_naturality_assoc _ _ _ _ _ (by lia),
      E'.edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r']

lemma mapPageInfinity_eq (pq : ι) (r : ℤ)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]
    [E'.HasEdgeMonoAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r] (hr : r₀ ≤ r := by lia) :
    mapPageInfinity f pq =
      (E.pageInfinityIso pq r).hom ≫ (f.hom r).f pq ≫ (E'.pageInfinityIso pq r).inv := by
  set r' := max (E.rMin pq) (E'.rMin pq)
  have hrr' : r' ≤ r := max_le
    (max_le (E.LE_of_hasEdgeMonoAtFrom pq r) (E.LE_of_hasEdgeEpiAtFrom pq r))
    (max_le (E'.LE_of_hasEdgeMonoAtFrom pq r) (E'.LE_of_hasEdgeEpiAtFrom pq r))
  have : r₀ ≤ r' := (E.LE_rMin pq).trans (le_max_left _ _)
  dsimp [mapPageInfinity]
  rw [dif_pos (by infer_instance), dif_pos (by infer_instance),
    ← E.pageInfinityIso_hom_edgeEpiSteps pq r' r hrr',
    ← E'.edgeMonoSteps_pageInfinityIso_inv pq r' r hrr', assoc,
    ← edgeMonoSteps_naturality_assoc _ _ _ _ ,
    edgeEpiSteps_edgeMonoSteps_assoc _ _ _ _]

lemma isIso_mapPageInfinity_of_isIso_hom (r : ℤ) (pq : ι) {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr)) [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq] :
    IsIso (mapPageInfinity f pq) := by
  let r' := max r (max (E.rMin pq) (E'.rMin pq))
  have hr' : r₀ ≤ r' := hr.trans (le_max_left _ _)
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

section

variable (E : CohomologicalSpectralSequenceNat C r₀)

lemma hasEdgeEpiAt
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.2 + 2 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeEpiAt pq r where
  zero pq' := by
    apply HomologicalComplex.shape
    intro h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

lemma hasEdgeMonoAt
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.1 + 1 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeMonoAt pq r where
  zero pq' := by
    apply HomologicalComplex.shape
    intro h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

instance (pq : ℕ × ℕ) : E.HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet :=
    ⟨max r₀ (pq.2 + 2), ⟨le_max_left _ _,
      fun _ hr ↦ E.hasEdgeEpiAt _ _ ((le_max_right _ _).trans hr) ((le_max_left _ _).trans hr)⟩⟩
  nonempty_hasEdgeMonoSet :=
    ⟨max r₀ (pq.1 + 1), ⟨le_max_left _ _,
      fun _ hr ↦ E.hasEdgeMonoAt _ _ ((le_max_right _ _).trans hr) ((le_max_left _ _).trans hr)⟩⟩

lemma hasEdgeEpiAtFrom
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.2 + 2 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeEpiAtFrom pq r where
  le := E.rFromMin_LE _ _ ⟨hr₀, fun r' hrr' ↦ hasEdgeEpiAt _ _ _⟩

lemma hasEdgeMonoAtFrom
    (pq : ℕ × ℕ) (r : ℤ) (hpq : pq.1 + 1 ≤ r := by lia) (hr₀ : r₀ ≤ r := by lia) :
    E.HasEdgeMonoAtFrom pq r where
  le := E.rToMin_LE _ _ ⟨hr₀, fun _ _ ↦ hasEdgeMonoAt _ _ _⟩

end

section

variable (E : CohomologicalSpectralSequenceNat C 2)

instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 0⟩ 2 :=
  hasEdgeEpiAtFrom _ _ _

instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 1⟩ 3 :=
  hasEdgeEpiAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨0, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨1, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨2, q⟩ 3 :=
  hasEdgeMonoAtFrom _ _ _

end

section

variable (E : CohomologicalSpectralSequenceNat C 1)

instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 0⟩ 2 :=
  hasEdgeEpiAtFrom _ _ _

instance (p : ℕ) : E.HasEdgeEpiAtFrom ⟨p, 1⟩ 3 :=
  hasEdgeEpiAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨0, q⟩ 1 :=
  hasEdgeMonoAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨0, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨1, q⟩ 2 :=
  hasEdgeMonoAtFrom _ _ _

instance (q : ℕ) : E.HasEdgeMonoAtFrom ⟨2, q⟩ 3 :=
  hasEdgeMonoAtFrom _ _ _

end

end CohomologicalSpectralSequenceNat

end CategoryTheory
