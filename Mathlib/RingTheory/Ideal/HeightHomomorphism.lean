import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {R : Type*} [CommRing R]

lemma Ideal.height_le_card_of_mem_minimalPrimes [IsNoetherianRing R]
    {p : Ideal R} [p.IsPrime] {s : Finset R} (hI : p ∈ (Ideal.span s).minimalPrimes) :
    p.height ≤ s.card := by
  trans (Cardinal.toENat (Submodule.spanRank (Ideal.span (s : Set R))))
  · exact Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hI
  · simpa using Submodule.spanRank_span_le_card (s : Set R)

variable {S : Type*} [CommRing S] [Algebra R S]

@[simp]
lemma Ideal.comap_map_quotient_mk {R : Type*} [CommRing R] (I J : Ideal R) :
    (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J := by
  ext x
  simp only [mem_comap, mem_quotient_iff_mem_sup]
  rw [sup_comm]

lemma Ideal.map_quotient_mk_isPrime_of_isPrime {R : Type*} [CommRing R]
    (I : Ideal R) (p : Ideal R) [p.IsPrime] (hIP : I ≤ p) :
    (p.map (Ideal.Quotient.mk I)).IsPrime := by
  apply Ideal.map_isPrime_of_surjective
  · exact Quotient.mk_surjective
  · simpa

instance (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (P.map (Ideal.Quotient.mk <| p.map (algebraMap R S))).IsPrime := by
  apply Ideal.map_quotient_mk_isPrime_of_isPrime
  rw [Ideal.map_le_iff_le_comap, Ideal.LiesOver.over (p := p) (P := P)]

@[simp]
lemma Function.comp_surjInv {α β : Type*} {f : α → β} (hf : f.Surjective) : f ∘ f.surjInv hf = id :=
  funext (Function.surjInv_eq _)

lemma Finset.exists_image_eq_and_card_le_of_surjective {α β : Type*} [DecidableEq β] {f : α → β}
    (hf : f.Surjective) (t : Finset β) :
    ∃ (s : Finset α), s.image f = t ∧ s.card ≤ t.card := by
  classical
  exact ⟨t.image (f.surjInv hf), by simp [Finset.image_image], Finset.card_image_le⟩

lemma Function.Surjective.finsetImage_surjective {α β : Type*} [DecidableEq β] (f : α → β)
    (hf : f.Surjective) : (Finset.image f).Surjective := by
  intro t
  obtain ⟨s, hs, _⟩ := t.exists_image_eq_and_card_le_of_surjective hf
  use s

lemma Finset.exists_image_eq_and_card_le_of_image_eq {α β : Type*} [DecidableEq β] {f : α → β}
    (s : Set α) (t : Finset β) (hfs : s.SurjOn f t) :
    ∃ (u : Finset α), u.image f = t ∧ u.card ≤ t.card ∧ (u : Set _) ⊆ s := by
  classical
  have hm : (s ∩ f ⁻¹' t).MapsTo f (t : Set β) :=
    Set.MapsTo.mono_left (Set.mapsTo_preimage _ _) Set.inter_subset_right
  have : Function.Surjective (hm.restrict f _ _) := by
    rw [Set.MapsTo.restrict_surjective_iff]
    intro x hx
    obtain ⟨a, hmem, rfl⟩ := hfs hx
    use a, ⟨hmem, hx⟩
  obtain ⟨u, hu⟩ := Finset.exists_image_eq_and_card_le_of_surjective this .univ
  refine ⟨Finset.image Subtype.val u, ?_, le_trans Finset.card_image_le (by simpa using hu.2), ?_⟩
  · have : f ∘ Subtype.val = Subtype.val ∘ (hm.restrict f _ _) := rfl
    rw [Finset.image_image, this, ← Finset.image_image, hu.1]
    simp
  · trans s ∩ f ⁻¹' t
    · simpa only [coe_image] using Subtype.coe_image_subset _ _
    · simp

/-- If `P` lies over `p`, `p` is a minimal prime over `I` and the image of `P` is
a minimal prime over the image of `K` in `S ⧸ p S`, then `P` is a minimal prime
over `I S ⊔ P`. -/
lemma Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes
    {I p : Ideal R} [p.IsPrime] {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    (hI : p ∈ I.minimalPrimes) {K : Ideal S} (hKP : K ≤ P)
    (hK : P.map (Ideal.Quotient.mk _) ∈
      (K.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).minimalPrimes) :
    P ∈ (I.map (algebraMap R S) ⊔ K).minimalPrimes := by
  refine ⟨⟨inferInstance, sup_le_iff.mpr ?_⟩, fun q ⟨_, hleq⟩ hqle ↦ ?_⟩
  · refine ⟨?_, hKP⟩
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Ideal.over_def P p]
    exact hI.1.2
  · simp only [sup_le_iff] at hleq
    have h1 : p.map (algebraMap R S) ≤ q := by
      rw [Ideal.map_le_iff_le_comap]
      refine hI.2 ⟨inferInstance, le_trans Ideal.le_comap_map (Ideal.comap_mono hleq.1)⟩ ?_
      convert Ideal.comap_mono hqle
      exact Ideal.LiesOver.over
    have h2 : P.map (Ideal.Quotient.mk (p.map (algebraMap R S))) ≤
        q.map (Ideal.Quotient.mk (p.map (algebraMap R S))) :=
      hK.2 ⟨Ideal.map_quotient_mk_isPrime_of_isPrime _ _ h1, Ideal.map_mono hleq.2⟩
        (Ideal.map_mono hqle)
    simpa [h1] using Ideal.comap_mono (f := Ideal.Quotient.mk (p.map (algebraMap R S))) h2

/--
If `P` lies over `p`, the height of `P` is bounded by the height of `p` plus
the height of the image of `P` in `S ⧸ p S`.
Equality holds if `S` satisfies going-down as an `R`-algebra.
-/
lemma Ideal.primeHeight_le_primeHeight_add_of_liesOver [IsNoetherianRing R]
      [IsNoetherianRing S] (p : Ideal R) [p.IsPrime]
      (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    P.height ≤ p.height +
      (P.map (Ideal.Quotient.mk <| p.map (algebraMap R S))).height := by
  classical
  obtain ⟨s, hp, heq⟩ := p.exists_finset_card_eq_height_of_isNoetherianRing
  let P' := P.map (Ideal.Quotient.mk <| p.map (algebraMap R S))
  obtain ⟨s', hP', heq'⟩ := P'.exists_finset_card_eq_height_of_isNoetherianRing
  have hsP'sub : (s' : Set <| S ⧸ (Ideal.map (algebraMap R S) p)) ⊆ (P' : Set <| S ⧸ _) :=
    fun x hx ↦ hP'.1.2 (Ideal.subset_span hx)
  have : Set.SurjOn (Ideal.Quotient.mk (p.map (algebraMap R S))) P s' := by
    apply Set.SurjOn.mono subset_rfl hsP'sub
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [SetLike.mem_coe, Ideal.mem_quotient_iff_mem] at hx
    simp only [Set.mem_image, SetLike.mem_coe]
    use y, hx
    rw [Ideal.map_le_iff_le_comap, Ideal.LiesOver.over (p := p) (P := P)]
  obtain ⟨o, himgo, hcardo, ho⟩ := s'.exists_image_eq_and_card_le_of_image_eq (P : Set S) this
  rw [← heq, ← heq']
  let t : Finset S := Finset.image (algebraMap R S) s ∪ o
  suffices h : P.height ≤ t.card by
    apply le_trans h
    norm_cast
    exact le_trans (Finset.card_union_le _ _) (add_le_add Finset.card_image_le hcardo)
  refine Ideal.height_le_card_of_mem_minimalPrimes ?_
  have : Ideal.span t = Ideal.map (algebraMap R S) (.span s) ⊔ .span o := by
    simp [t, Ideal.span_union, Ideal.map_span]
  refine this ▸ map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes hp (span_le.mpr ho) ?_
  convert hP'
  simp [Ideal.map_span, ← himgo]
