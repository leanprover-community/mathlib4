/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.EdgeStep

/-!
# ...

-/

public section

namespace CategoryTheory

open Category ZeroObject

variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

/-- Given `pq`, this is the condition that the differentials to the objects `E_{r'}^{pq}`
on all pages `r' ≥ r` of a spectral sequence are zero. -/
class HasEdgeMonoAtFrom (E : SpectralSequence C c r₀) (pq : ι) (r : ℤ) : Prop where
  hasEdgeMonoAt (E pq r) (r' : ℤ) (hr' : r ≤ r' := by lia) : E.HasEdgeMonoAt pq r'

export HasEdgeMonoAtFrom (hasEdgeMonoAt)

variable (E E' : SpectralSequence C c r₀) (f : E ⟶ E') (pq : ι) (r : ℤ)

section

variable [E.HasEdgeMonoAtFrom pq r]

lemma hasEdgeMonoAtFrom_of_le (r' : ℤ) (hr' : r ≤ r' := by lia) :
    E.HasEdgeMonoAtFrom pq r' where
  hasEdgeMonoAt r'' hr' := E.hasEdgeMonoAt pq r _

instance : E.HasEdgeMonoAt pq r :=
  E.hasEdgeMonoAt pq r r

instance (k : ℕ) : E.HasEdgeMonoAtFrom pq (r + k) :=
  E.hasEdgeMonoAtFrom_of_le pq r _

instance : E.HasEdgeMonoAtFrom pq (r + 1) :=
  E.hasEdgeMonoAtFrom_of_le pq r _

instance (r' : ℤ) : E.HasEdgeMonoAtFrom pq (max r r') :=
  E.hasEdgeMonoAtFrom_of_le pq r _

instance (r' : ℤ) : E.HasEdgeMonoAtFrom pq (max r' r) :=
  E.hasEdgeMonoAtFrom_of_le pq r _

/-- Auxiliary definition for `edgeMonoSteps`. -/
private noncomputable def edgeMonoSteps' (k : ℕ) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    (E.page (r + k)).X pq ⟶ (E.page r).X pq := by
  haveI := E.le₀_of_hasEdgeMonoAt pq r
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)).hom
  | succ k hk => exact E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ hk

@[simp]
private lemma edgeMonoSteps'_zero :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.edgeMonoSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)).hom := rfl

@[simp]
private lemma edgeMonoSteps'_succ (k : ℕ) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.edgeMonoSteps' pq r (k + 1) =
      E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ E.edgeMonoSteps' pq r k := rfl

private instance (k : ℕ) : Mono (E.edgeMonoSteps' pq r k) := by
  induction k with
  | zero => simp only [edgeMonoSteps'_zero]; infer_instance
  | succ => simp only [edgeMonoSteps'_succ]; infer_instance

/-- The monomorphism `E_{r'}^pq ⟶ E_r^{pq}` when `r ≤ r'` and `pq` is such
that `E.HasEdgeMonoAtFrom pq r` holds, i.e. all the differentials to the objects
`E_{r''}^pq` vanish for `r'' ≥ r`. -/
noncomputable def edgeMonoSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    (E.page r').X pq ⟶ (E.page r).X pq :=
  haveI := E.le₀_of_hasEdgeMonoAt pq r
  (E.pageXIsoOfEq pq _ _ (by lia) (by lia)).inv ≫
    E.edgeMonoSteps' pq r (Int.toNat (r' - r))

private lemma edgeMonoSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.edgeMonoSteps pq r r' (by lia) =
      (E.pageXIsoOfEq pq _ _ h).inv ≫ E.edgeMonoSteps' pq r k := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

instance (r' : ℤ) (h : r ≤ r') :
    Mono (E.edgeMonoSteps pq r r' h) := by
  rw [E.edgeMonoSteps_eq pq r r' (Int.toNat (r' - r))]
  infer_instance

instance (r' : ℤ) (k : ℕ) (h : r + k = r') :
    Mono (E.edgeMonoSteps pq r r') := by
  infer_instance

@[simp]
lemma edgeMonoSteps_eq_id :
    E.edgeMonoSteps pq r r (by rfl) = 𝟙 _ := by
  simp [E.edgeMonoSteps_eq pq r r 0]

@[reassoc (attr := simp)]
lemma edgeMonoStep_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia) :
    haveI := E.hasEdgeMonoAtFrom_of_le pq r r'
    E.edgeMonoStep pq r' r'' h₂ ≫ E.edgeMonoSteps pq r r' h₁ =
    E.edgeMonoSteps pq r r'' (by lia) := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeMonoSteps_eq pq r (r + (k + 1 : ℕ)) (k + 1), E.edgeMonoSteps_eq pq r (r + k) k]
  simp

lemma edgeMonoSteps_eq_edgeMonoStep (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
    E.edgeMonoStep pq r r' h := by
  simp [← E.edgeMonoStep_comp_edgeMonoSteps pq r r r']

@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp (r' r'' : ℤ)
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    haveI := E.hasEdgeMonoAtFrom_of_le pq r r'
    E.edgeMonoSteps pq r' r'' hr'' ≫ E.edgeMonoSteps pq r r' hr' =
      E.edgeMonoSteps pq r r'' (hr'.trans hr'') := by
  have := E.hasEdgeMonoAtFrom_of_le pq r r'
  obtain ⟨k, hk⟩ := Int.le.dest hr''
  induction k generalizing r'' with
  | zero =>
    obtain rfl : r' = r'' := by simpa using hk
    simp
  | succ k hk' =>
    rw [← E.edgeMonoStep_comp_edgeMonoSteps_assoc pq r' (r' + k) r'',
      hk' _ (by lia) (by lia)]
    simp

@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp_edgeMonoStep
    (r' r'' : ℤ) (h₁ : r + 1 = r' := by lia) (h₂ : r' ≤ r'' := by lia) :
    haveI := E.hasEdgeMonoAtFrom_of_le pq r r'
    E.edgeMonoSteps pq r' r'' h₂ ≫ E.edgeMonoStep pq r r' h₁ =
    E.edgeMonoSteps pq r r'' (by lia) := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep ..]
  simp

variable {E E'} in
@[reassoc]
lemma edgeMonoSteps_naturality (r' : ℤ) (h : r ≤ r' := by lia)
    [E'.HasEdgeMonoAtFrom pq r] :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    (f.hom r').f pq ≫ E'.edgeMonoSteps pq r r' h =
      E.edgeMonoSteps pq r r' h ≫ (f.hom r).f pq := by
  have := E.le₀_of_hasEdgeMonoAt pq r
  obtain ⟨k, hk⟩ := Int.le.dest h
  induction k generalizing r' with
  | zero =>
    obtain rfl : r = r' := by lia
    simp
  | succ k hk' =>
    simp only [← edgeMonoStep_comp_edgeMonoSteps _ pq r (r + k) r',
      edgeMonoStep_naturality_assoc f pq (r + k) r',
      Category.assoc, hk' (r + k) (by lia) rfl]

end

/-- Given `pq`, this is the condition that the differentials from the objects `E_{r'}^{pq}`
on all pages `r' ≥ r` of a spectral sequence are zero. -/
class HasEdgeEpiAtFrom (E : SpectralSequence C c r₀) (pq : ι) (r : ℤ) : Prop where
  hasEdgeEpiAt (E pq r) (r' : ℤ) (hr' : r ≤ r' := by lia) : E.HasEdgeEpiAt pq r'

export HasEdgeEpiAtFrom (hasEdgeEpiAt)

section

variable [E.HasEdgeEpiAtFrom pq r]

lemma hasEdgeEpiAtFrom_of_le (r' : ℤ) (hr' : r ≤ r' := by lia) :
    E.HasEdgeEpiAtFrom pq r' where
  hasEdgeEpiAt r'' hr' := E.hasEdgeEpiAt pq r _

instance : E.HasEdgeEpiAt pq r :=
  E.hasEdgeEpiAt pq r r

instance (k : ℕ) : E.HasEdgeEpiAtFrom pq (r + k) :=
  E.hasEdgeEpiAtFrom_of_le pq r _

instance : E.HasEdgeEpiAtFrom pq (r + 1) :=
  E.hasEdgeEpiAtFrom_of_le pq r _

instance (r' : ℤ) : E.HasEdgeEpiAtFrom pq (max r r') :=
  E.hasEdgeEpiAtFrom_of_le pq r _

instance (r' : ℤ) : E.HasEdgeEpiAtFrom pq (max r' r) :=
  E.hasEdgeEpiAtFrom_of_le pq r _

/-- Auxiliary definition for `edgeEpiSteps`. -/
private noncomputable def edgeEpiSteps' (k : ℕ) :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    (E.page r).X pq ⟶ (E.page (r + k)).X pq := by
  haveI := E.le₀_of_hasEdgeEpiAt pq r
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)).inv
  | succ k hk => exact hk ≫ E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ))

@[simp]
private lemma edgeEpiSteps'_zero :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    E.edgeEpiSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)).inv := rfl

@[simp]
private lemma edgeEpiSteps'_succ (k : ℕ) :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    E.edgeEpiSteps' pq r (k + 1) =
      E.edgeEpiSteps' pq r k ≫ E.edgeEpiStep pq (r + k) (r + ((k + 1) : ℕ)) := rfl

private instance (k : ℕ) : Epi (E.edgeEpiSteps' pq r k) := by
  induction k with
  | zero => simp only [edgeEpiSteps'_zero]; infer_instance
  | succ => simp only [edgeEpiSteps'_succ]; infer_instance

/-- The monomorphism `E_r^pq ⟶ E_{r'}^{pq}` when `r ≤ r'` and `pq` is such
that `E.HasEdgeEpiAtFrom pq r` holds, i.e. all the differentials from the objects
`E_{r''}^pq` vanish for `r'' ≥ r`. -/
noncomputable def edgeEpiSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    (E.page r).X pq ⟶ (E.page r').X pq :=
  haveI := E.le₀_of_hasEdgeEpiAt pq r
  E.edgeEpiSteps' pq r (Int.toNat (r' - r)) ≫
    (E.pageXIsoOfEq pq _ _ (by lia) (by lia)).hom

private lemma edgeEpiSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    E.edgeEpiSteps pq r r' (by lia) =
      E.edgeEpiSteps' pq r k ≫ (E.pageXIsoOfEq pq _ _ h).hom := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

instance (r' : ℤ) (h : r ≤ r') :
    Epi (E.edgeEpiSteps pq r r' h) := by
  rw [E.edgeEpiSteps_eq pq r r' (Int.toNat (r' - r))]
  infer_instance

instance (r' : ℤ) (k : ℕ) (h : r + k = r') :
    Epi (E.edgeEpiSteps pq r r') := by
  infer_instance

@[simp]
lemma edgeEpiSteps_eq_id :
    E.edgeEpiSteps pq r r (by rfl) = 𝟙 _ := by
  simp [E.edgeEpiSteps_eq pq r r 0]

@[reassoc (attr := simp)]
lemma edgeEpiSteps_comp_edgeEpiStep
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia) :
    haveI := E.hasEdgeEpiAtFrom_of_le pq r r'
    E.edgeEpiSteps pq r r' h₁ ≫ E.edgeEpiStep pq r' r'' h₂ =
    E.edgeEpiSteps pq r r'' (by lia) := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeEpiSteps_eq pq r (r + (k + 1 : ℕ)) (k + 1), E.edgeEpiSteps_eq pq r (r + k) k]
  simp

lemma edgeEpiSteps_eq_edgeEpiStep (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeEpiSteps pq r r' (by lia) =
    E.edgeEpiStep pq r r' h := by
  simp [← E.edgeEpiSteps_comp_edgeEpiStep pq r r r']

@[reassoc (attr := simp)]
lemma edgeEpiSteps_comp (r' r'' : ℤ)
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    haveI := E.hasEdgeEpiAtFrom_of_le pq r r'
    E.edgeEpiSteps pq r r' hr' ≫ E.edgeEpiSteps pq r' r'' hr'' =
      E.edgeEpiSteps pq r r'' (hr'.trans hr'') := by
  have := E.hasEdgeEpiAtFrom_of_le pq r r'
  obtain ⟨k, hk⟩ := Int.le.dest hr''
  induction k generalizing r'' with
  | zero =>
    obtain rfl : r' = r'' := by simpa using hk
    simp
  | succ k hk' =>
    rw [← E.edgeEpiSteps_comp_edgeEpiStep pq r' (r' + k) r'',
      reassoc_of% hk' _ (by lia) (by lia)]
    simp

@[reassoc (attr := simp)]
lemma edgeEpiStep_comp_edgeEpiSteps
    (r' r'' : ℤ) (h₁ : r + 1 = r' := by lia) (h₂ : r' ≤ r'' := by lia) :
    haveI := E.hasEdgeEpiAtFrom_of_le pq r r'
    E.edgeEpiStep pq r r' h₁ ≫ E.edgeEpiSteps pq r' r'' h₂ =
    E.edgeEpiSteps pq r r'' (by lia) := by
  rw [← E.edgeEpiSteps_eq_edgeEpiStep ..]
  simp

variable {E E'} in
@[reassoc]
lemma edgeEpiSteps_naturality (r' : ℤ) (h : r ≤ r' := by lia)
    [E'.HasEdgeEpiAtFrom pq r] :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    (f.hom r).f pq ≫ E'.edgeEpiSteps pq r r' h =
      E.edgeEpiSteps pq r r' h ≫ (f.hom r').f pq := by
  have := E.le₀_of_hasEdgeEpiAt pq r
  obtain ⟨k, hk⟩ := Int.le.dest h
  induction k generalizing r with
  | zero =>
    obtain rfl : r = r' := by lia
    simp
  | succ k hk' =>
    simp only [← edgeEpiStep_comp_edgeEpiSteps _ pq r (r + 1) r',
      Category.assoc, edgeEpiStep_naturality_assoc f pq r (r + 1),
      hk' (r + 1) (by lia) (by lia) (by lia)]

end

section

variable [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r]

@[reassoc (attr := simp)]
lemma edgeEpiSteps_edgeMonoSteps (r' : ℤ) (hr' : r ≤ r' := by lia) :
    E.edgeEpiSteps pq r r' hr' ≫ E.edgeMonoSteps pq r r' hr' = 𝟙 _ := by
  obtain ⟨k, hk⟩ := Int.le.dest hr'
  induction k generalizing r' with
  | zero =>
    obtain rfl : r = r' := by simpa using hk
    simp
  | succ k hk' =>
    simp only [← E.edgeEpiSteps_comp_edgeEpiStep_assoc pq r (r + k) r',
      ← E.edgeMonoStep_comp_edgeMonoSteps pq r (r + k) r',
      edgeEpiStep_edgeMonoStep_assoc, hk']

@[reassoc (attr := simp)]
lemma edgeMonoSteps_edgeEpiSteps (r' : ℤ) (hr' : r ≤ r' := by lia) :
    E.edgeMonoSteps pq r r' hr' ≫ E.edgeEpiSteps pq r r' hr' = 𝟙 _ := by
  obtain ⟨k, hk⟩ := Int.le.dest hr'
  induction k generalizing r r' with
  | zero =>
    obtain rfl : r = r' := by simpa using hk
    simp
  | succ k hk' =>
    rw [← E.edgeMonoSteps_comp_edgeMonoStep_assoc pq r (r + 1) r',
      ← E.edgeEpiStep_comp_edgeEpiSteps pq r (r + 1) r',
      E.edgeMonoStep_edgeEpiStep_assoc ..,
      hk' (r + 1) r' (by lia) (by lia)]

@[expose, simps]
noncomputable def edgeIsoSteps (r' : ℤ) (hr' : r ≤ r' := by lia) :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    (E.page r).X pq ≅ (E.page r').X pq where
  hom := E.edgeEpiSteps pq r r'
  inv := E.edgeMonoSteps pq r r'

instance (r' : ℤ) (hr' : r ≤ r') : IsIso (E.edgeMonoSteps pq r r' hr') :=
  ⟨E.edgeEpiSteps pq r r', by simp⟩

instance (r' : ℤ) (hr' : r ≤ r') : IsIso (E.edgeEpiSteps pq r r' hr') :=
  ⟨E.edgeMonoSteps pq r r', by simp⟩

end

@[reassoc]
lemma congr_edgeEpiSteps_comp_edgeMonoSteps
    (r r' s t : ℤ) [E.HasEdgeMonoAtFrom pq r'] [E.HasEdgeEpiAtFrom pq r]
    (h₁ : r ≤ s := by lia) (h₂ : r' ≤ s := by lia)
    (h₃ : r ≤ t := by lia) (h₄ : r' ≤ t := by lia) :
    E.edgeEpiSteps pq r s h₁ ≫ E.edgeMonoSteps pq r' s h₂ =
    E.edgeEpiSteps pq r t h₃ ≫ E.edgeMonoSteps pq r' t h₄ := by
  wlog hst : s ≤ t generalizing s t
  · exact (this _ _ _ _ _ _ (by lia)).symm
  · by_cases hr' : r ≤ r'
    · simp [← E.edgeEpiSteps_comp_assoc pq r r' s, ← E.edgeEpiSteps_comp_assoc pq r r' t]
    · have := E.hasEdgeMonoAtFrom_of_le pq r' r
      rw [← E.edgeMonoSteps_comp pq r' r s, ← E.edgeMonoSteps_comp pq r' r t,
        E.edgeEpiSteps_edgeMonoSteps_assoc pq r s, E.edgeEpiSteps_edgeMonoSteps_assoc pq r t]

end SpectralSequence

end CategoryTheory
