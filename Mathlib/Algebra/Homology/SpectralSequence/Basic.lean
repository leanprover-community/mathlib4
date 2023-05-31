import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits ZeroObject

lemma Int.eq_add_ofNat_of_le {i j : ℤ} (hij : i ≤ j) :
    ∃ (d : ℕ), j = i + d := by
  have h : 0 ≤ j - i := by linarith
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le h
  exact ⟨d, by linarith⟩

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

variable (C : Type _) [Category C] [Abelian C] (degrees : ℤ → ℤ × ℤ) (r₀ : ℤ)

structure SpectralSequence where
  page (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ) : C
  d (r : ℤ) (hr : r₀ ≤ r) (pq pq' : ℤ × ℤ) (h : pq + degrees r = pq') :
    page r hr pq ⟶ page r hr pq'
  d_comp_d (r : ℤ) (hr : r₀ ≤ r) (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
      d r hr _ _ h₁₂ ≫ d r hr _ _ h₂₃ = 0
  iso (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r + 1 = r') (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
      (ShortComplex.mk _ _ (d_comp_d r hr pq₁ pq₂ pq₃ h₁₂ h₂₃)).homology ≅
        page r' (hr.trans (by simp only [← hr', le_add_iff_nonneg_right])) pq₂

abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r => ⟨r, 1-r⟩)

abbrev E₀CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 0

abbrev E₁CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 1

abbrev E₂CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 2

abbrev HomologicalSpectralSequence :=
  SpectralSequence C (fun r => ⟨-r, r-1⟩)

abbrev E₀HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 0

abbrev E₁HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 1

abbrev E₂HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 2

namespace SpectralSequence

variable {C r₀ degrees}
variable (E : SpectralSequence C degrees r₀)

def pageIsoOfEq (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r = r') (pq : ℤ × ℤ) :
    E.page r hr pq ≅ E.page r' (hr.trans (by rw [hr'])) pq :=
  eqToIso (by congr)

def toSet (pq : ℤ × ℤ) : Set ℤ := fun r => ∃ (hr : r₀ ≤ r), ∀ (r' : ℤ) (hr' : r ≤ r'),
  (∀ (pq' : ℤ × ℤ) (hpq' : pq' + degrees r' = pq), E.d r' (hr.trans hr') pq' pq hpq' = 0)

def fromSet (pq : ℤ × ℤ) : Set ℤ := fun r => ∃ (hr : r₀ ≤ r), ∀ (r' : ℤ) (hr' : r ≤ r'),
  (∀ (pq' : ℤ × ℤ) (hpq' : pq + degrees r' = pq'), E.d r' (hr.trans hr') pq pq' hpq' = 0)

class HasInfinityPageAt (pq : ℤ × ℤ) : Prop where
  nonemptyToSet' : (E.toSet pq).Nonempty
  nonemptyFromSet' : (E.fromSet pq).Nonempty

section

variable (pq : ℤ × ℤ) [h : E.HasInfinityPageAt pq]

lemma nonemptyToSet : (E.toSet pq).Nonempty := HasInfinityPageAt.nonemptyToSet'
lemma nonemptyFromSet : (E.fromSet pq).Nonempty := HasInfinityPageAt.nonemptyFromSet'

noncomputable def rToMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonemptyToSet pq) r₀ (fun _ hx => hx.1)).choose

lemma rToMin_mem : E.rToMin pq ∈ E.toSet pq :=
  (Set.has_min_of_ℤ _ (E.nonemptyToSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose

lemma rToMin_le (r : ℤ) (hr : r ∈ E.toSet pq) :
    E.rToMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonemptyToSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose_spec r hr

lemma le_rToMin :
    r₀ ≤ E.rToMin pq := (E.rToMin_mem pq).1

lemma d_to_eq_zero (r : ℤ) (hr : E.rToMin pq ≤ r) (pq' : ℤ × ℤ)
    (hpq' : pq' + degrees r = pq) :
      E.d r ((E.le_rToMin pq).trans hr) pq' pq hpq' = 0 :=
  (E.rToMin_mem pq).2 r hr pq' hpq'

noncomputable def rFromMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonemptyFromSet pq) r₀ (fun _ hx => hx.1)).choose

lemma rFromMin_mem : E.rFromMin pq ∈ E.fromSet pq :=
  (Set.has_min_of_ℤ _ (E.nonemptyFromSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose

lemma rFromMin_le (r : ℤ) (hr : r ∈ E.fromSet pq) :
    E.rFromMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonemptyFromSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose_spec r hr

lemma le_rFromMin :
    r₀ ≤ E.rFromMin pq := (E.rFromMin_mem pq).1

lemma d_from_eq_zero (r : ℤ) (hr : E.rFromMin pq ≤ r) (pq' : ℤ × ℤ)
    (hpq' : pq + degrees r = pq') :
      E.d r ((E.le_rFromMin pq).trans hr) pq pq' hpq' = 0 :=
  (E.rFromMin_mem pq).2 r hr pq' hpq'

noncomputable def rMin : ℤ := max (E.rToMin pq) (E.rFromMin pq)

lemma rFromMin_le_rMin : E.rFromMin pq ≤ E.rMin pq := le_max_right _ _

lemma rToMin_le_rMin : E.rToMin pq ≤ E.rMin pq := le_max_left _ _

lemma le_rMin :
    r₀ ≤ E.rMin pq :=
  (E.le_rFromMin pq).trans (E.rFromMin_le_rMin pq)

noncomputable def isoPageSucc (r r' : ℤ)
  (hr : E.rMin pq ≤ r) (hr' : r + 1 = r') :
    E.page r ((E.le_rMin pq).trans hr) pq ≅
      E.page r' (((E.le_rMin pq).trans hr).trans
        (by simp only [← hr', le_add_iff_nonneg_right])) pq := by
    refine' Iso.symm _ ≪≫ E.iso r r' ((E.le_rMin pq).trans hr) hr'
      (pq - degrees r) pq (pq + degrees r) (by simp) rfl
    refine' (ShortComplex.HomologyData.ofZeros _ _ _).left.homologyIso
    . exact E.d_to_eq_zero pq r ((E.rToMin_le_rMin pq).trans hr) _ _
    . exact E.d_from_eq_zero pq r ((E.rFromMin_le_rMin pq).trans hr) _ _

noncomputable def isoPageOfAddNat (r : ℤ) (hr : E.rMin pq ≤ r) (k : ℕ) :
    E.page r ((E.le_rMin pq).trans hr) pq ≅
      E.page (r+k) (((E.le_rMin pq).trans hr).trans (by simp)) pq := by
  induction' k with _ e
  . exact E.pageIsoOfEq _ _ _ (by simp) _
  . exact e ≪≫ E.isoPageSucc _ _ _ (hr.trans (by simp))
      (by simp only [Nat.cast_succ, add_assoc])

noncomputable def isoPageOfLE
    (r r' : ℤ) (hr : E.rMin pq ≤ r) (hr' : r ≤ r') :
    E.page r ((E.le_rMin pq).trans hr) pq ≅
      E.page r' (((E.le_rMin pq).trans hr).trans hr') pq :=
  E.isoPageOfAddNat pq r hr
    (Int.eq_ofNat_of_zero_le (show 0 ≤ r' - r by linarith)).choose ≪≫
      E.pageIsoOfEq _ _ _
        (by linarith [(Int.eq_ofNat_of_zero_le (show 0 ≤ r' - r by linarith)).choose_spec]) _

lemma isoPageOfLE_eq
    (r r' : ℤ) (hr : E.rMin pq ≤ r) (k : ℕ) (hr' : r + k = r') :
    E.isoPageOfLE pq r r' hr
      (by simp only [← hr', le_add_iff_nonneg_right, Nat.cast_nonneg]) =
      E.isoPageOfAddNat pq r hr k ≪≫ E.pageIsoOfEq _ _ _ hr' _ := by
  have : 0 ≤ r' - r := by simp only [← hr', add_sub_cancel', Nat.cast_nonneg]
  obtain rfl : (Int.eq_ofNat_of_zero_le this).choose = k := by
    linarith [(Int.eq_ofNat_of_zero_le this).choose_spec]
  rfl

end

noncomputable def pageInfinity (pq : ℤ × ℤ) : C := by
  by_cases E.HasInfinityPageAt pq
  . exact E.page (E.rMin pq) (E.le_rMin pq) pq
  . exact 0

noncomputable def pageInfinityIso (pq : ℤ × ℤ) [E.HasInfinityPageAt pq] :
    E.pageInfinity pq ≅ E.page (E.rMin pq) (E.le_rMin pq) pq := eqToIso (dif_pos _)

noncomputable def isoPageInfinityOfLE (pq : ℤ × ℤ) [E.HasInfinityPageAt pq]
    (r : ℤ) (hr : E.rMin pq ≤ r) :
    E.page r ((E.le_rMin pq).trans hr) pq ≅ E.pageInfinity pq :=
  Iso.symm (E.pageInfinityIso pq ≪≫ E.isoPageOfLE pq _ _ (by rfl) hr)

structure ConvergenceStripes where
  stripe : ℤ × ℤ → ℤ
  position (n i : ℤ) : ℤ × ℤ
  position_stripe (n i : ℤ) : stripe (position n i) = n

variable (c : ConvergenceStripes)

structure StronglyConvergesToInDegree (n : ℤ) (X : C) where
  hasInfinityPageAt : ∀ (pq : ℤ × ℤ) (_ : c.stripe pq = n), E.HasInfinityPageAt pq
  filtration' : ℤ ⥤ MonoOver X
  exists_isZero_filtration' :
    ∃ (j : ℤ), IsZero ((filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).obj j)
  exists_isIso_filtration'_hom :
    ∃ (i : ℤ), IsIso ((filtration' ⋙ MonoOver.forget X).obj i).hom
  π' (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    (filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).obj i ⟶ E.pageInfinity pq
  epi_π' (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) : Epi (π' i pq hpq)
  comp_π' (i j : ℤ) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).map
      (homOfLE (show i ≤ j by linarith)) ≫ π' j pq hpq = 0
  exact' (i j : ℤ) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (ShortComplex.mk _ _ (comp_π' i j hij pq hpq)).Exact

namespace StronglyConvergesToInDegree

variable {E c}
variable {n : ℤ} {X : C} (h : E.StronglyConvergesToInDegree c n X)

def filtration : ℤ ⥤ C := h.filtration' ⋙ MonoOver.forget X ⋙ Over.forget X

def filtrationι (i : ℤ) : h.filtration.obj i ⟶ X :=
  ((h.filtration' ⋙ MonoOver.forget X).obj i).hom

instance (i : ℤ) : Mono (h.filtrationι i) := by
  dsimp [filtrationι]
  infer_instance

lemma exists_isZero_filtration_obj :
    ∃ (j : ℤ), IsZero (h.filtration.obj j) := h.exists_isZero_filtration'

lemma exists_isIso_filtrationι :
    ∃ (i : ℤ), IsIso (h.filtrationι i) := h.exists_isIso_filtration'_hom

@[reassoc (attr := simp)]
lemma filtration_map_ι {i j : ℤ} (φ : i ⟶ j) :
    h.filtration.map φ ≫ h.filtrationι j = h.filtrationι i := by
  simp [filtration, filtrationι]

def π (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    h.filtration.obj i ⟶ E.pageInfinity pq := h.π' i pq hpq

instance (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    Epi (h.π i pq hpq) := h.epi_π' i pq hpq

lemma comp_π {i j : ℤ} (φ : i ⟶ j) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    h.filtration.map φ ≫ h.π j pq hpq = 0 :=
  h.comp_π' i j hij pq hpq

instance {i j : ℤ} (f : i ⟶ j) :
    Mono (h.filtration.map f) :=
  mono_of_mono_fac (MonoOver.w (h.filtration'.map f))

lemma shortExact {i j : ℤ} (φ : i ⟶ j) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (ShortComplex.mk _ _ (h.comp_π φ hij pq hpq)).ShortExact where
  exact := h.exact' i j hij pq hpq

lemma isIso_filtration_map_succ_iff {i j : ℤ} (φ : i ⟶ j) (hij : i + 1 = j) :
    IsIso (h.filtration.map φ) ↔ IsZero (E.pageInfinity (c.position n j)) :=
  (h.shortExact φ hij (c.position n j) rfl).isIso_f_iff

lemma isIso_filtration_map_iff {i j : ℤ} (φ : i ⟶ j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k)) := by
  let H := fun (d : ℕ) => ∀ {i j : ℤ} (φ : i ⟶ j) (_ : i + d = j),
    IsIso (h.filtration.map φ) ↔
      ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k))
  suffices ∀ (d : ℕ), H d by
    obtain ⟨d, hd⟩ := Int.eq_add_ofNat_of_le (leOfHom φ)
    exact this d φ hd.symm
  intro d
  induction' d with d hd
  . intro i j φ hij
    simp only [Nat.zero_eq, Nat.cast_zero, add_zero] at hij
    subst hij
    obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
    constructor
    . intro _ k _ _
      exfalso
      linarith
    . intro
      infer_instance
  . intro i j' φ hij'
    simp only [Nat.cast_succ, ← add_assoc ] at hij'
    subst hij'
    have hij : i ≤ i + d := by linarith
    have hjj' : i + d ≤ i + d + 1 := by linarith
    have fac : h.filtration.map φ = h.filtration.map (homOfLE hij) ≫
      h.filtration.map (homOfLE hjj') := by
        rw [← Functor.map_comp]
        congr
    constructor
    . intro h₁₂
      have : Epi (h.filtration.map φ) := IsIso.epi_of_iso (h.filtration.map φ)
      have := epi_of_epi_fac fac.symm
      have h₁ : IsIso (h.filtration.map (homOfLE hjj')) := isIso_of_mono_of_epi _
      have h₂ := IsIso.of_isIso_fac_right fac.symm
      rw [h.isIso_filtration_map_succ_iff _ rfl] at h₁
      rw [hd _ rfl] at h₂
      intro k hk hk'
      by_cases k ≤ i + d
      . exact h₂ _ hk h
      . obtain rfl : k = i + d + 1 := by linarith
        exact h₁
    . intro hij'
      have : IsIso (h.filtration.map (homOfLE hij)) := by
        rw [hd _ rfl]
        intro k hk hk'
        exact hij' _ hk (by linarith)
      have : IsIso (h.filtration.map (homOfLE hjj')) := by
        rw [h.isIso_filtration_map_succ_iff _ rfl]
        exact hij' _ (by linarith) (by linarith)
      rw [fac]
      infer_instance

lemma isZero_filtration_obj_iff_of_le (i j : ℤ) (hij : i ≤ j):
    IsZero (h.filtration.obj j) ↔
      (IsZero (h.filtration.obj i) ∧
        ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k))) := by
  rw [← h.isIso_filtration_map_iff (homOfLE hij)]
  constructor
  . intro hj
    have : IsZero (h.filtration.obj i) := by
      simp only [IsZero.iff_id_eq_zero, ← cancel_mono (h.filtration.map (homOfLE hij))]
      exact hj.eq_of_tgt _ _
    exact ⟨this, ⟨0, this.eq_of_src _ _, hj.eq_of_src _ _⟩⟩
  . rintro ⟨hi, _⟩
    exact IsZero.of_iso hi (asIso (h.filtration.map (homOfLE hij))).symm

lemma isZero_filtration_obj_iff (j : ℤ) :
    IsZero (h.filtration.obj j) ↔
      ∀ (k : ℤ) (_ : k ≤ j), IsZero (E.pageInfinity (c.position n k)) := by
  obtain ⟨i, hi⟩ := h.exists_isZero_filtration_obj
  have : ∀ (k : ℤ) (_ : k ≤ i), IsZero (E.pageInfinity (c.position n k)) := by
    intro k hk
    rw [h.isZero_filtration_obj_iff_of_le (k-1) i (by linarith)] at hi
    exact hi.2 k (by linarith) hk
  by_cases hij : j ≤ i
  . rw [h.isZero_filtration_obj_iff_of_le j i (by linarith)] at hi
    simp only [hi.1, true_iff]
    intro k hk
    exact this _ (by linarith)
  . simp only [not_le] at hij
    simp only [h.isZero_filtration_obj_iff_of_le i j (by linarith), hi, true_and]
    constructor
    . intro H k hk
      by_cases hik : i < k
      . exact H k hik hk
      . simp only [not_lt] at hik
        exact this k hik
    . tauto

lemma isIso_filtrationι_iff_of_le (i j : ℤ) (hij : i ≤ j):
    IsIso (h.filtrationι i) ↔
      (IsIso (h.filtrationι j) ∧
        ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k))) := by
  rw [← h.isIso_filtration_map_iff (homOfLE hij)]
  constructor
  . intro hi
    have fac := (h.filtration_map_ι (homOfLE hij))
    have := epi_of_epi_fac fac
    have : IsIso (h.filtrationι j) := isIso_of_mono_of_epi _
    simp only [this, true_and]
    exact IsIso.of_isIso_fac_right fac
  . rintro ⟨_, _⟩
    rw [← h.filtration_map_ι (homOfLE hij)]
    infer_instance

lemma isIso_filtrationι_iff (j : ℤ) :
    IsIso (h.filtrationι j) ↔
      ∀ (k : ℤ) (_ : j < k), IsZero (E.pageInfinity (c.position n k)) := by
  obtain ⟨i, hi⟩ := h.exists_isIso_filtrationι
  have : ∀ (k : ℤ) (_ : i < k), IsZero (E.pageInfinity (c.position n k)) := by
    intro k hk
    rw [h.isIso_filtrationι_iff_of_le i k (by linarith)] at hi
    exact hi.2 k hk (by rfl)
  by_cases hij : i ≤ j
  . rw [h.isIso_filtrationι_iff_of_le i j (by linarith)] at hi
    simp only [hi.1, true_iff]
    intro k hk
    exact this _ (by linarith)
  . simp only [not_le] at hij
    simp only [h.isIso_filtrationι_iff_of_le j i (by linarith), hi, true_and]
    constructor
    . intro H k hk
      by_cases hik : i < k
      . exact this _ hik
      . simp only [not_lt] at hik
        exact H k hk hik
    . tauto

-- TODO: Cartan-Eilenberg, prop 5.6, p. 326

end StronglyConvergesToInDegree

variable (X : ℤ → C)

structure StronglyConvergesTo where
  stronglyConvergesToInDegree (n : ℤ) : E.StronglyConvergesToInDegree c n (X n)

variable (h : E.StronglyConvergesTo c X)

lemma StronglyConvergesTo.hasInfinityPageAt (pq : ℤ × ℤ) :
    E.HasInfinityPageAt pq :=
  (h.stronglyConvergesToInDegree (c.stripe pq)).hasInfinityPageAt pq rfl

end SpectralSequence
