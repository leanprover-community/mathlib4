/- Copyright-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.Decomposability
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Data.Nat.Parity

/-! This files contains the definition of the Euler-Poincaré characteristic of a finite simplicial
complex, and its calculation for a decomposable complex (see
`Mathlinb.Cominnatorics.AbstractSimplicialComplex.Decomposability`).-/

universe u

open BigOperators

variable {α : Type u} {K L : AbstractSimplicialComplex α}

namespace AbstractSimplicialComplex

/-- If `K` is finite, definition of the set of faces of `K` as a finset of `K.faces`.-/
@[reducible]
noncomputable def finset_of_faces (hfin : FiniteComplex K) : Finset K.faces :=
  @Finset.univ K.faces (@Fintype.ofFinite _ hfin)

-- TODO: integrate into next definition, if not used anywhere.
/-- If `K` is finite, then `K.facets` is finite.-/
lemma facets_finite (hfin : FiniteComplex K) : Finite K.facets :=
  @Finite.of_injective _ K.faces hfin
  (fun s => ⟨s.1, facets_subset s.2⟩) (fun _ _ h ↦ by
  simp only [Subtype.mk.injEq, SetCoe.ext_iff] at h; exact h)

/-- If `K` is finite, definition of the set of facets of `K` as a finset of `K.facets`.-/
@[reducible]
noncomputable def finset_of_facets (hfin : FiniteComplex K) : Finset K.facets :=
  @Finset.univ K.facets (@Fintype.ofFinite _ (facets_finite hfin))

/-- The Euler-Poincaré characteristic of a finite simplicial complex `K` is the sum over all faces
`s` of `K` of `-1` to the dimension of `s` (i.e. `s.card - 1`). -/
noncomputable def EulerPoincareCharacteristic (hfin : FiniteComplex K) : ℤ :=
  ∑ s in @Finset.univ K.faces (@Fintype.ofFinite _ hfin), (-1 : ℤ)^(s.1.card - 1)

/-! The case of decomposable abstract simplicial complexes.-/

variable (R : K.facets → Finset α) (DF : K.faces → K.facets) (hdec : isDecomposition R DF)

/-- If `s` is a nonempty finset, then the sum of `(-1)^t.card` on the powerset of `s` is `0`.-/
lemma AlternatingSumPowerset {s : Finset α} (hsne : s.Nonempty) :
    ∑ t in s.powerset, (-1)^t.card = 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : ℤ) (1 : ℤ) s
  rw [← Finset.card_pos] at hsne
  simp only [zero_pow hsne, one_pow, mul_one, add_left_neg] at h
  exact h

/-- If `s ⊂ t` are finsets, then the sum of `(-1)^(x.card - 1)` on the interval `Finset.Icc s t`
is `0`.-/
lemma sum_on_finsetInterval1 [DecidableEq α] {s t : Finset α} (hst : s ⊂ t) :
    ∑ x in Finset.Icc s t, (-1)^x.card = 0 := by
  set i : (x : Finset α) → x ∈ Finset.Icc s t → Finset α := by
    intro x _
    exact x \ s
  have hi : ∀ (x : Finset α) (hx : x ∈ Finset.Icc s t), i x hx ∈ (t \ s).powerset := by
    intro _ hx
    exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff (Finset.mem_Icc.mp hx).2 (by rfl))
  set j : (x : Finset α) → x ∈ (t \ s).powerset → Finset α := by
    intro x _
    exact x ⊔ s
  have hj : ∀ (x : Finset α) (hx : x ∈ (t \ s).powerset), j x hx ∈ Finset.Icc s t := by
    intro x hx
    simp only [Finset.sup_eq_union, Finset.mem_Icc, Finset.le_eq_subset]
    constructor
    · exact Finset.subset_union_right _ _
    · exact Finset.union_subset (Finset.subset_sdiff.mp (Finset.mem_powerset.mp hx)).1
        (le_of_lt hst)
  rw [Finset.sum_bij' (s := Finset.Icc s t) (t := Finset.powerset (t \ s))
    (f := fun x => (-1)^x.card) (g := fun x ↦ (-1)^x.card * (-1)^s.card) i j hi hj]
  · rw [← Finset.sum_mul, AlternatingSumPowerset (Finset.sdiff_nonempty.mpr (not_le_of_lt hst)),
        zero_mul]
  · intro x hx
    simp only [Finset.sup_eq_union, Finset.sdiff_union_self_eq_union, Finset.union_eq_left]
    exact (Finset.mem_Icc.mp hx).1
  · intro x hx
    simp only [Finset.sup_eq_union]
    rw [Finset.union_sdiff_self, Finset.sdiff_eq_self_iff_disjoint]
    exact (Finset.subset_sdiff.mp (Finset.mem_powerset.mp hx)).2
  · intro x hx
    rw [Finset.card_sdiff (Finset.mem_Icc.mp hx).1]
    rw [← npow_add, tsub_add_cancel_of_le (Finset.card_le_card (Finset.mem_Icc.mp hx).1)]

/-- If `s` is a nonempty finset, then the sum of `(-1)^(x.card - 1)` on the interval
`Finset.Ioc ∅ s` is `1`.-/
lemma Sum_on_FinsetInterval2 [DecidableEq α] {s : Finset α} (hsne : s.Nonempty) :
    ∑ x in Finset.Ioc ∅ s, (-1)^(x.card - 1) = 1 := by
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.Ioc ∅ s) _ (fun s => (-1)^(Finset.card s - 1)) (fun s => (-1 : ℤ) * (-1 : ℤ)^(Finset.card s)) _ rfl
  (fun s hs => by simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset] at hs
                  simp only
                  conv => rhs
                          congr
                          rw [←(pow_one (-1 : ℤ))]
                  rw [←pow_add]
                  conv => lhs
                          rw [←(one_mul ((-1 : ℤ)^(Finset.card s - 1)))]
                          congr
                          rw [←neg_one_pow_two]
                  rw [←pow_add]
                  apply congr_arg
                  rw [add_comm, add_comm 1 _, Nat.add_succ, ←(Nat.succ_eq_add_one (Finset.card s)), Nat.succ_inj', ←Nat.succ_eq_add_one,
                         ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos (by rw [←Finset.card_pos] at hs; exact hs.1)]
  )]
  rw [←Finset.mul_sum]
  have hsum := AlternatingSumPowerset hsne
  have hunion : Finset.powerset s = {∅} ∪ Finset.Ioc ∅ s := by
    ext t
    simp only [Finset.mem_powerset, ge_iff_le, Finset.le_eq_subset, Finset.mem_union, Finset.mem_singleton,
  Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset]
    constructor
    · exact fun ht => by by_cases hte : t = ∅
                         · exact Or.inl hte
                         · rw [←ne_eq, ←Finset.nonempty_iff_ne_empty] at hte
                           exact Or.inr ⟨hte, ht⟩
    · exact fun ht => by cases ht with
                         | inl hte => rw [hte]; simp only [Finset.empty_subset]
                         | inr htne => exact htne.2
  have hdisj : Disjoint {∅} (Finset.Ioc ∅ s) := by
    rw [Finset.disjoint_iff_ne]
    intro t ht u hu
    simp only [Finset.mem_singleton] at ht
    by_contra habs
    rw [ht] at habs
    rw [←habs] at hu
    simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, lt_self_iff_false, Finset.empty_subset, and_true] at hu
  rw [←(Finset.disjUnion_eq_union _ _ hdisj)] at hunion
  rw [hunion] at hsum
  rw [Finset.sum_disjUnion hdisj] at hsum
  simp only [Finset.sum_singleton, Finset.card_empty, pow_zero, ge_iff_le, Finset.le_eq_subset] at hsum
  rw [add_comm, ←eq_neg_iff_add_eq_zero] at hsum
  rw [hsum]
  simp only [mul_neg, mul_one, neg_neg]

variable {R DF}
/-- If `s` is a boring facet, then `R s` is nonempty and strictly contained in `s`.-/
lemma BoringFacet_image_by_R {s : K.facets} (hs : ¬ isPi0Facet R s ∧ ¬ isHomologyFacet R s) :
    R s ≠ ∅ ∧ R s ⊂ s :=  by
  constructor
  · intro he
    have heq : decompositionInterval R s = Set.Iic (⟨s.1, facets_subset s.2⟩ : K.faces) := by
      ext t
      simp only [Finset.mem_coe, decompositionInterval_def, he, Finset.le_eq_subset,
        Finset.empty_subset, true_and, Set.mem_Iic]
      rfl
    exact hs.1 heq
  · by_contra habs
    have heq : decompositionInterval R s = {⟨s.1, facets_subset s.2⟩} := by
      ext x
      simp only [decompositionInterval_def, eq_of_le_of_not_lt (hdec.1 s) habs, Finset.le_eq_subset,
        Finset.mem_singleton]
      erw [← le_antisymm_iff (a := s.1) (b := x.1), ← SetCoe.ext_iff, eq_comm]
    exact hs.2 ⟨hs.1, heq⟩

lemma sum_fiber_pi0Facet [DecidableEq α] [DecidableEq K.facets] (hfin : FiniteComplex K)
    {s : K.facets}
    (hs : isPi0Facet R s) : ∑ i in Finset.filter (fun t ↦ DF t = s) (finset_of_faces hfin),
    (-1) ^ (i.1.card - 1) = 1 := by
  letI := @Fintype.ofFinite _ hfin
  rw [isPi0Facet_iff] at hs
  rw [Finset.sum_congr (s₂ := decompositionInterval R s) (g := fun s ↦ (-1)^(s.1.card -1))]
  · set i : (t : K.faces) → t ∈ decompositionInterval R s → Finset α := fun t _ ↦ t.1
    have hi : ∀ (t : K.faces) (ht : t ∈ decompositionInterval R s),
        i t ht ∈ Finset.Ioc ∅ s.1 := by
      intro t ht
      simp only [Finset.mem_Ioc]
      exact ⟨Finset.empty_ssubset.mpr (K.nonempty_of_mem t.2),
        ((decompositionInterval_def R s).mp ht).2⟩
    set j : (t : Finset α) → t ∈ Finset.Ioc ∅ s.1 → K.faces := by
      intro t ht
      rw [Finset.mem_Ioc] at ht
      exact ⟨t, K.down_closed (facets_subset s.2) ht.2 (Finset.empty_ssubset.mp ht.1)⟩
    have hj : ∀ (t : Finset α) (ht : t ∈ Finset.Ioc ∅ s.1),
        j t ht ∈ decompositionInterval R s := by
      intro t ht
      rw [Finset.mem_Ioc] at ht
      simp only [decompositionInterval_def]
      rw [and_iff_left ht.2]
      cases hs with
      | inl h => rw [h]; simp only [Finset.le_eq_subset, Finset.empty_subset]
      | inr h =>
        have heq : t = s := by
          refine le_antisymm ht.2 ?_
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
          rw [ha]
          simp only [Finset.le_eq_subset, Finset.singleton_subset_iff]
          obtain ⟨b, hb⟩ := Finset.empty_ssubset.mp ht.1
          have heq := Finset.card_le_one_iff.mp (le_of_eq h) (ht.2 hb)
            (by rw [ha]; exact Finset.mem_singleton_self _ )
          rw [← heq]; exact hb
        rw [heq]; exact hdec.1 s
    rw [Finset.sum_bij' i j hi hj (g := fun x ↦ (-1)^(x.card - 1))]
    · exact Sum_on_FinsetInterval2 (K.nonempty_of_mem (facets_subset s.2))
    · intro _ _
      simp only [Subtype.coe_eta]
    · intro _ _
      simp only
    · intro _ _
      simp only
  · ext x
    rw [mem_decompositionInterval hdec, eq_comm]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · exact fun _ _ ↦ rfl
  exact fun s ↦ hdec.1 s

lemma sum_fiber_homologyFacet [DecidableEq K.facets] (hfin : FiniteComplex K) {s : K.facets}
    (hs : isHomologyFacet R s) : ∑ i in Finset.filter (fun t ↦ DF t = s) (finset_of_faces hfin),
    (-1) ^ (i.1.card - 1) = (-1)^(s.1.card - 1) := by
  letI := @Fintype.ofFinite _ hfin
  rw [Finset.sum_congr (s₂ := {⟨s.1, facets_subset s.2⟩}) (g := fun s ↦ (-1)^(s.1.card -1))]
  · rw [Finset.sum_singleton]
  · ext x
    unfold isHomologyFacet at hs
    rw [← hs.2, mem_decompositionInterval hdec, eq_comm]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro _ _; rfl

lemma sum_fiber_boringFacet [DecidableEq α] [DecidableEq K.facets] (hfin : FiniteComplex K)
    {s : K.facets} (hs : ¬ isPi0Facet R s ∧ ¬ isHomologyFacet R s) :
    ∑ i in Finset.filter (fun t ↦ DF t = s) (finset_of_faces hfin), (-1) ^ (i.1.card - 1) = 0 := by
  letI := @Fintype.ofFinite _ hfin
  rw [Finset.sum_congr (s₂ := decompositionInterval R s) (g := fun s ↦ (-1)^(s.1.card -1))]
  · set i : (t : K.faces) → t ∈ decompositionInterval R s → Finset α := fun t _ ↦ t.1
    have hi : ∀ (t : K.faces) (ht : t ∈ decompositionInterval R s),
        i t ht ∈ Finset.Icc (R s) s.1 := by
      intro t ht
      simp only [Finset.mem_Icc]
      exact (decompositionInterval_def R s).mp ht
    set j : (t : Finset α) → t ∈ Finset.Icc (R s) s → K.faces := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      exact ⟨t, K.down_closed (facets_subset s.2) ht.2
        ⟨_, ht.1 (Classical.choose_spec (Finset.nonempty_of_ne_empty
        (BoringFacet_image_by_R hdec hs).1))⟩⟩
    have hj : ∀ (t : Finset α) (ht : t ∈ Finset.Icc (R s) s),
        j t ht ∈ decompositionInterval R s := by
      intro t ht
      simp only [decompositionInterval_def]
      exact Finset.mem_Icc.mp ht
    rw [Finset.sum_bij' i j hi hj (g := fun x ↦ (-1)*(-1)^x.card)]
    · rw [← Finset.mul_sum, sum_on_finsetInterval1 (BoringFacet_image_by_R hdec hs).2, mul_zero]
    · intro _ _
      simp only [Subtype.coe_eta]
    · intro _ _
      simp only
    · intro t ht
      simp only
      obtain ⟨k, hk⟩ := Nat.even_or_odd' t.1.card
      cases hk with
      | inl hk => rw [hk, Even.neg_one_pow (n := 2*k), mul_one, Odd.neg_one_pow]
                  refine Nat.Even.sub_odd (m := 2* k) ?_ (by simp only [even_two, Even.mul_right])
                    odd_one
                  rw [← hk]
                  refine le_trans ?_
                    (Finset.card_le_card ((decompositionInterval_def R s).mp ht).1)
                  rw [Nat.succ_le, Finset.card_pos, Finset.nonempty_iff_ne_empty]
                  exact (BoringFacet_image_by_R hdec hs).1
                  simp only [even_two, Even.mul_right]
      | inr hk => rw [hk]
                  simp only [add_tsub_cancel_right, even_two, Even.mul_right, Even.neg_pow, one_pow,
                    neg_mul, one_mul]
                  rw [pow_add, Even.neg_one_pow, pow_one, one_mul, neg_neg]
                  simp only [even_two, Even.mul_right]
  · ext x
    rw [finset_of_faces, mem_decompositionInterval hdec, Finset.mem_filter, eq_comm]
    simp only [Finset.mem_univ, true_and]
  · exact fun _ _ ↦ rfl

/- Finally we put everything to calculate the Euler-Poincaré characteristic of `K`, for `K` finite
and having a decomposition: it is equal to the cardinality of the set of `π₀` facets plus the sum
over homology facets of the function `fun s ↦ (-1)^(s.card - 1)`.-/
lemma EulerPoincareCharacteristicDecomposable [DecidableEq K.faces] [DecidableEq (Set K.faces)]
    (hfin : FiniteComplex K) :
    EulerPoincareCharacteristic hfin = (Finset.filter (fun (s : K.facets) ↦ isPi0Facet R s)
    (finset_of_facets hfin)).card +
    ∑ s in Finset.filter (fun (s : K.facets) ↦ isHomologyFacet R s) (finset_of_facets hfin),
    (-1 : ℤ)^(s.1.card - 1) := by
  classical
  letI : Finite (K.faces) := hfin
  letI : Finite (K.facets) := @Finite.of_injective _ K.faces hfin
    (fun s => ⟨s.1, facets_subset s.2⟩) (fun _ _ h ↦ by
    simp only [Subtype.mk.injEq, SetCoe.ext_iff] at h; exact h)
  letI : Fintype K.facets := Fintype.ofFinite K.facets
  unfold EulerPoincareCharacteristic
  rw [← Finset.sum_fiberwise (g := DF)]
  rw [← Finset.sum_add_sum_compl (Finset.filter (fun s ↦ isPi0Facet R s) (finset_of_facets hfin))]
  rw [Finset.sum_congr (s₁ := Finset.filter (fun s ↦ isPi0Facet R s) (finset_of_facets hfin))
    rfl (fun _ hs ↦ by erw [sum_fiber_pi0Facet hdec hfin (Finset.mem_filter.mp hs).2])]
  rw [Finset.sum_const, nsmul_one]
  congr 1
  erw [Finset.compl_filter]
  have hsub : Finset.filter (fun s ↦ isHomologyFacet R s) Finset.univ ⊆
      Finset.filter (fun s ↦ ¬ isPi0Facet R s) Finset.univ := by
    intro s
    simp only [Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_univ, true_and,
      isHomologyFacet]
    tauto
  rw [← Finset.sum_sdiff hsub]
  rw [Finset.sum_congr (s₁ := Finset.filter (fun s ↦ isHomologyFacet R s) Finset.univ)
    rfl (fun _ hs ↦ by erw [sum_fiber_homologyFacet hdec hfin (Finset.mem_filter.mp hs).2])]
  have heq : Finset.filter (fun s ↦ ¬ isPi0Facet R s) Finset.univ \
      Finset.filter (fun s ↦ isHomologyFacet R s) Finset.univ =
      Finset.filter (fun s ↦ ¬ isPi0Facet R s ∧ ¬ isHomologyFacet R s) Finset.univ := by
    ext s
    simp only [ne_eq, Finset.filter_congr_decidable, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, not_and]
  rw [heq]
  rw [Finset.sum_congr rfl (fun _ hs ↦ by erw [sum_fiber_boringFacet hdec hfin
    (Finset.mem_filter.mp hs).2])]
  rw [Finset.sum_const, nsmul_zero, zero_add]

end AbstractSimplicialComplex
