import Mathlib.KolmogorovExtension4.IonescuTulceaFinset2

open MeasureTheory ProbabilityTheory Finset ENNReal Filter Topology Function

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

noncomputable def prod_meas : Measure ((n : ℕ) → X n) :=
  Measure.snd ((μ 0) ⊗ₘ
    (@ionescu_ker _ (ProbabilityMeasure.nonempty ⟨μ 0, hμ 0⟩) _
      (fun n ↦ kernel.const _ (μ (n + 1))) _))

instance : IsProbabilityMeasure (prod_meas μ) := by
  rw [prod_meas]
  infer_instance

theorem kernel.comap_const {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure Z) {f : X → Y} (hf : Measurable f) :
    kernel.comap (kernel.const Y μ) f hf = kernel.const X μ := by
  ext1 x
  rw [kernel.const_apply, kernel.comap_apply, kernel.const_apply]

theorem prod_ioc (n : ℕ) (f : (Ioc 0 (n + 1)) → ℝ≥0∞) :
    (f ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl _⟩⟩) *
      (∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩) =
    ∏ i : Ioc 0 (n + 1), f i := by
  let g : ℕ → ℝ≥0∞ := fun k ↦ if hk : k ∈ Ioc 0 (n + 1) then f ⟨k, hk⟩ else 1
  have h1 : ∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩ =
      ∏ i : Ioc 0 n, g i := by
    refine Finset.prod_congr rfl ?_
    simp only [Finset.mem_univ, mem_Ioc, true_implies, Subtype.forall, g]
    rintro k ⟨hk1, hk2⟩
    rw [dif_pos ⟨hk1, hk2.trans n.le_succ⟩]
  have h2 : ∏ i : Ioc 0 (n + 1), f i = ∏ i : Ioc 0 (n + 1), g i := by
    refine Finset.prod_congr rfl ?_
    simp only [Finset.mem_univ, mem_Ioc, Subtype.coe_eta, dite_eq_ite, true_implies, Subtype.forall,
      g]
    intro k hk
    simp [hk]
  rw [h1, h2, Finset.prod_coe_sort, Finset.prod_coe_sort]
  have : f ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩ = g (n + 1) := by simp [g]
  rw [this]
  exact Finset.mul_prod_Ico_eq_prod_Icc (Nat.le_add_left (0 + 1) n)

theorem er_succ_preimage_pi {n : ℕ} (hn : 0 < n) (s : (i : Ioc 0 (n + 1)) → Set (X i)) :
    er 0 n (n + 1) hn n.le_succ ⁻¹' Set.univ.pi s =
      (Set.univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)) ×ˢ
        ((e n).symm ⁻¹' (s ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl (n + 1)⟩⟩)) := by
  ext p
  simp only [er, Nat.succ_eq_add_one, Nat.reduceAdd, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
    Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, mem_Ioc, e,
    MeasurableEquiv.symm_mk, Equiv.coe_fn_symm_mk, Set.mem_prod]
  refine ⟨fun h ↦ ⟨fun i ⟨hi1, hi2⟩ ↦ ?_, ?_⟩, fun ⟨h1, h2⟩ i ⟨hi1, hi2⟩ ↦ ?_⟩
  · convert h i ⟨hi1, hi2.trans n.le_succ⟩
    rw [dif_pos hi2]
  · convert h (n + 1) ⟨n.succ_pos, le_refl _⟩
    simp
  · split_ifs with h
    · exact h1 i ⟨hi1, h⟩
    · cases (by omega : i = n + 1)
      exact h2

example (a b : Prop) (h : a) : a ∧ b = b := by exact ⟨h, rfl⟩

theorem kerNat_prod {N : ℕ} (hN : 0 < N) :
    (kerNat (fun n ↦ kernel.const _ (μ (n + 1))) 0 N) =
      kernel.const _ (Measure.pi (fun i : Ioc 0 N ↦ μ i)) := by
  ext1 x₀
  refine Nat.le_induction ?_ (fun n hn hind ↦ ?_) N (Nat.succ_le.2 hN)
  · rw [kerNat_succ, kernel.const_apply]
    refine (Measure.pi_eq (fun s ms ↦ ?_)).symm
    have : Subsingleton (Ioc 0 1) := by
      constructor
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      rw [mem_Ioc] at hi hj
      simp only [Subtype.mk.injEq]
      omega
    rw [Fintype.prod_subsingleton _ ⟨1, mem_Ioc.2 ⟨zero_lt_one, le_refl _⟩⟩,
      kernel.map_apply' _ (e 0).measurable, kernel.const_apply]
    · congr with x
      simp only [Nat.reduceAdd, e, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Nat.succ_eq_add_one,
        Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall,
        Nat.Ioc_succ_singleton, zero_add, mem_singleton, Nat.zero_eq]
      refine ⟨fun h ↦ h 1 rfl, fun h i hi ↦ ?_⟩
      cases hi
      exact h
    exact MeasurableSet.univ_pi ms
  · rw [kernel.const_apply]
    refine (Measure.pi_eq fun s ms ↦ ?_).symm
    rw [kerNat_succ_right _ _ _ (Nat.succ_le.1 hn), kerNat_succ, compProd,
      dif_pos ⟨Nat.succ_le.1 hn, n.lt_succ_self⟩,
      kernel.map_apply' _ _ _ (MeasurableSet.univ_pi ms)]
    rw [er_succ_preimage_pi (Nat.succ_le.1 hn), split, kernel.map_const, kernel.comap_const,
      kernel.compProd_apply]
    · simp only [kernel.const_apply, Nat.succ_eq_add_one, Set.mem_prod]
      have this b : (μ (n + 1)).map (e n) {c | b ∈
          (Set.univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)) ∧
            c ∈ (e n).symm ⁻¹' (s ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl (n + 1)⟩⟩)} =
          (Set.univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)).indicator
          (fun _ ↦ (μ (n + 1)) (s ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl _⟩⟩)) b := by
        simp only [Nat.succ_eq_add_one, Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]
        split_ifs with h <;> simp [h]
        · rw [Measure.map_apply (e n).measurable]
          · rfl
          · exact (e n).measurable_invFun (ms ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩)
      simp_rw [this]
      rw [lintegral_indicator_const, hind, kernel.const_apply, Measure.pi_pi]
      · exact prod_ioc n (fun i ↦ (μ i) (s i))
      · exact MeasurableSet.univ_pi (fun i ↦ ms ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)
    apply MeasurableSet.prod
    · exact MeasurableSet.univ_pi (fun i ↦ ms ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)
    · exact (e n).measurable_invFun (ms ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩)

theorem prod_noyau_proj (N : ℕ) :
    my_ker (fun n ↦ kernel.const _ (μ (n + 1))) N =
      kernel.map ((kernel.deterministic id measurable_id) ×ₖ
          (kernel.const _ (Measure.pi (fun i : Ioc 0 N ↦ μ i))))
        (er' N) (er' N).measurable := by
  rcases eq_zero_or_pos N with hN | hN
  · cases hN
    rw [my_ker_zero]
    have : IsEmpty (Ioc 0 0) := by simp
    rw [Measure.pi_of_empty]
    ext x s ms
    rw [kernel.map_apply, kernel.map_apply, kernel.deterministic_apply, kernel.prod_apply,
      kernel.deterministic_apply, kernel.const_apply, Measure.dirac_prod_dirac,
      Measure.map_apply zer.measurable ms, Measure.map_apply (er' 0).measurable ms,
      Measure.dirac_apply' _ (zer.measurable ms), Measure.dirac_apply' _ ((er' 0).measurable ms)]
    apply indicator_eq_indicator
    simp only [id_eq, zer, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_preimage, er']
    congrm (fun i ↦ ?_) ∈ s
    simp [(mem_Iic_zero i.2).symm]
  · rw [my_ker_pos _ hN, kerNat_prod _ hN]
    rfl

variable {ι : Type*} {α : ι → Type*}

theorem preimage_proj (I J : Finset ι) [∀ i : ι, Decidable (i ∈ I)]
    (hIJ : I ⊆ J) (s : (i : I) → Set (α i)) :
    (fun t : (∀ j : J, α j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (Set.univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · exact h i i_mem
  · trivial

variable {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
variable (ν : (i : ι) → Measure (Y i)) [hν : ∀ i, IsProbabilityMeasure (ν i)]

/-- Consider a family of probability measures. You can take their products for any fimite
subfamily. This gives a projective family of measures, see `IsProjectiveMeasureFamily`. -/
theorem isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ ν i))) := by
  classical
  refine fun I J hJI ↦ Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := Y) I J hJI) (MeasurableSet.univ_pi ms),
    preimage_proj J I hJI, Measure.pi_pi]
  let g := fun i ↦ (ν i) (if hi : i ∈ J then s ⟨i, hi⟩ else Set.univ)
  have h1 : (@Finset.univ I _).prod (fun i ↦ g i) = (@Finset.univ I.toSet _).prod (fun i ↦ g i) :=
    Finset.prod_congr rfl (by simp)
  have h2 : (@Finset.univ J _).prod (fun i ↦ (ν i) (s i)) =
      (@Finset.univ J.toSet _).prod (fun i ↦ g i) :=
    Finset.prod_congr rfl (by simp [g])
  rw [h1, h2, Finset.prod_set_coe, Finset.prod_set_coe,
    Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.prod_subset hJI (fun _ h h' ↦ by simp [g, h, h'])]

-- theorem kolContent_eq_measure_pi [Fintype ι] {s : Set ((i : ι) → Y i)} (hs : MeasurableSet s) :
--     kolContent (isProjectiveMeasureFamily_pi ν) s = Measure.pi ν s := by
--   have : s = cylinder Finset.univ s := by simp
--   rw [kolContent_congr (I := Finset.univ)]

theorem Measure.map_prod_snd {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν]
    (f : Y → Z) :
    (μ.prod ν).snd.map f = (μ.prod (ν.map f)).snd := by
  rw [Measure.snd_prod, Measure.snd_prod]

theorem Measure.map_snd_compProd {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) [IsProbabilityMeasure μ] (κ : kernel X Y)
    [IsSFiniteKernel κ] {f : Y → Z} (hf : Measurable f) :
    (μ ⊗ₘ κ).snd.map f = Measure.snd (μ ⊗ₘ (kernel.map κ f hf)) := by
  ext s ms
  rw [Measure.map_apply hf ms, Measure.snd_apply (ms.preimage hf),
    Measure.compProd_apply (measurable_snd (hf ms)), Measure.snd_apply ms,
    Measure.compProd_apply (measurable_snd ms)]
  refine lintegral_congr fun x ↦ ?_
  simp_rw [Set.preimage_preimage]
  rw [kernel.map_apply', Set.preimage_preimage]
  exact measurable_id ms

lemma indicator_const_mul {α : Type*} (s : Set α) (c : ℝ≥0∞) (a : α) :
    (s.indicator 1 a) * c = s.indicator (fun _ ↦ c) a := by
  simp [Set.indicator]

theorem prod_iic (n : ℕ) (f : (Iic n) → ℝ≥0∞) :
    (∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Iic_self i.2⟩) * f ⟨0, mem_Iic.2 <| zero_le _⟩ =
    ∏ i : Iic n, f i := by
  let g : ℕ → ℝ≥0∞ := fun k ↦ if hk : k ∈ Iic n then f ⟨k, hk⟩ else 1
  have h1 : ∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Iic_self i.2⟩ = ∏ i : Ioc 0 n, g i := by
    refine Finset.prod_congr rfl ?_
    simp only [Finset.mem_univ, mem_Ioc, true_implies, Subtype.forall, g]
    rintro k ⟨hk1, hk2⟩
    rw [dif_pos <| mem_Iic.2 hk2]
  have h2 : ∏ i : Iic n, f i = ∏ i : Iic n, g i := by
    refine Finset.prod_congr rfl ?_
    simp only [Finset.mem_univ, mem_Ioc, Subtype.coe_eta, dite_eq_ite, true_implies, Subtype.forall,
      g]
    intro k hk
    simp [hk]
  rw [h1, h2, Finset.prod_coe_sort, Finset.prod_coe_sort]
  have : f ⟨0, mem_Iic.2 <| zero_le _⟩ = g 0 := by simp [g]
  rw [this]
  exact Finset.prod_Ioc_mul_eq_prod_Icc (zero_le n)

theorem projectiveLimit_prod_meas : IsProjectiveLimit (prod_meas μ)
    (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  have := ProbabilityMeasure.nonempty ⟨μ 0, hμ 0⟩
  intro I
  have sub : I ⊆ Finset.Iic (I.sup id) := fun i hi ↦ Finset.mem_Iic.2 <| Finset.le_sup (f := id) hi
  have : Measure.pi (fun i : I ↦ μ i) =
      (Measure.pi (fun i : Iic (I.sup id) ↦ μ i)).map
        (fun x (i : I) ↦ x ⟨i.1, sub i.2⟩) := by
    conv_lhs => change (fun I : Finset ℕ ↦ Measure.pi (fun i : I ↦ μ i)) I
    rw [isProjectiveMeasureFamily_pi μ (Finset.Iic (I.sup id)) I sub]
  simp_rw [this]
  have : (fun (x : (n : ℕ) → X n) (i : I) ↦ x i) =
      (fun x (i : I) ↦ x ⟨i.1, Finset.mem_Iic.2 <| Finset.le_sup (f := id) i.2⟩) ∘
      (fun x (i : Iic (I.sup id)) ↦ x i) := by
    ext x i
    simp
  rw [this, ← Measure.map_map (measurable_proj₂' _ _ sub) (measurable_proj' _)]
  congr
  rw [prod_meas, Measure.map_snd_compProd, ionescu_ker_proj, prod_noyau_proj]
  · refine (Measure.pi_eq fun s ms ↦ ?_).symm
    have mpis := MeasurableSet.univ_pi ms
    rw [Measure.snd_apply mpis, Measure.compProd_apply (measurable_snd mpis)]
    refine Eq.trans (b := ∫⁻ x₀, (s ⟨0, mem_Iic.2 <| zero_le _⟩).indicator 1 (id x₀) *
      ∏ i : Ioc 0 (I.sup id), (μ ↑i) (s ⟨i.1, Ioc_subset_Iic_self i.2⟩) ∂μ 0) ?_ ?_
    · refine lintegral_congr fun x₀ ↦ ?_
      have this : (er' (I.sup id)) ⁻¹' (Prod.mk x₀ ⁻¹' (Prod.snd ⁻¹' Set.univ.pi fun i ↦ s i)) =
          s ⟨0, mem_Iic.2 <| zero_le _⟩ ×ˢ
            Set.univ.pi (fun i : Ioc 0 (I.sup id) ↦ s ⟨i.1, Ioc_subset_Iic_self i.2⟩) := by
        ext x
        simp only [er', MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_pi,
          Set.mem_univ, true_implies, Subtype.forall, mem_Iic, Set.mem_prod, mem_Ioc]
        refine ⟨fun h ↦ ⟨h 0 (zero_le _), fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i hi ↦ ?_⟩
        · convert h i hi2
          simp [hi1.ne.symm]
        · split_ifs with h
          · cases h; exact h1
          · exact h2 i ⟨by omega, hi⟩
      rw [kernel.map_apply', this, kernel.prod_apply, Measure.prod_prod, kernel.deterministic_apply,
        Measure.dirac_apply', kernel.const_apply, Measure.pi_pi]
      · exact ms _
      · exact measurable_prod_mk_left (m := inferInstance) (measurable_snd mpis)
    · simp_rw [indicator_const_mul, id_eq]
      rw [lintegral_indicator_const]
      · exact prod_iic (I.sup id) (fun i ↦ (μ i) (s i))
      · exact ms _


theorem kolContent_eq_prod_meas {A : Set ((n : ℕ) → X n)} (hA : A ∈ cylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) A = prod_meas μ A := by
  obtain ⟨s, S, mS, A_eq⟩ : ∃ s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_cylinders] using hA
  rw [kolContent_congr _ hA A_eq mS, A_eq, cylinder, ← Measure.map_apply (measurable_proj' _) mS,
    projectiveLimit_prod_meas μ]

variable {X : ι → Type*} [hX : ∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

lemma omg_ (s : Set ι) (x : (i : s) → X i) (i j : s) (h : i = j) (h' : X i = X j) :
    cast h' (x i) = x j := by
  subst h
  rfl

lemma omg'_ (α β : Type _) (h : α = β) (a : α) (s : Set α) (h' : Set α = Set β) :
    (cast h a ∈ cast h' s) = (a ∈ s) := by
  subst h
  rfl

lemma HEq_meas {i j : ι} (hij : i = j) :
    HEq (inferInstance : MeasurableSpace (X i)) (inferInstance : MeasurableSpace (X j)) := by
  cases hij; rfl

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by a countable type. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem secondLemma
    (φ : ℕ ≃ ι) {A : ℕ → Set ((i : ι) → X i)} (A_mem : ∀ n, A n ∈ cylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
    infer_instance
  set μ_proj := isProjectiveMeasureFamily_pi μ
  let μ_proj' := isProjectiveMeasureFamily_pi (fun k : ℕ ↦ μ (φ k))
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa [mem_cylinders] using A_mem n
  choose s S mS A_eq using A_cyl
  -- The goal of the proof is to apply the same result when the index set is `ℕ`. To do so we
  -- have to pull back the sets `sₙ` and `Sₙ` using equivalences.
  let t n := (s n).preimage φ φ.injective.injOn
  have h i : X (φ (φ.symm i)) = X i := congrArg X (φ.apply_symm_apply i)
  have e n i (h : i ∈ s n) : φ.symm i ∈ t n := by simpa [t] using h
  have e' n k (h : k ∈ t n) : φ k ∈ s n := by simpa [t] using h
  -- The function `f` does the link between families indexed by `ℕ` and those indexed by `ι`.
  -- Here we have to use `cast` because otherwhise we land in `X (φ (φ.symm i))`, which is not
  -- definitionally equal to X i.
  have meas_cast i : Measurable (cast (h i)) := by
    apply measurable_cast
    exact HEq_meas (by simp)
  let f : ((k : ℕ) → X (φ k)) → (i : ι) → X i := fun x i ↦ cast (h i) (x (φ.symm i))
  -- `aux n` is an equivalence between `sₙ` ans `tₙ`, it will be used to link the two.
  let aux n : s n ≃ t n :=
    { toFun := fun i ↦ ⟨φ.symm i, e n i.1 i.2⟩
      invFun := fun k ↦ ⟨φ k, e' n k.1 k.2⟩
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
  -- `gₙ` is the equivalent of `f` for families indexed by `tₙ` and `sₙ`.
  let g n : ((k : t n) → X (φ k)) → (i : s n) → X i :=
    fun x i ↦ cast (h i) (x (aux n i))
  -- Transfering from `ℕ` to `ι` and then projecting on `sₙ` is the same as first
  -- projecting on `uₙ` and then transfering to `ι`.
  have test n : (fun (x : (i : ι) → X i) (i : s n) ↦ x i) ∘ f =
      (g n) ∘ (fun (x : (k : ℕ) → X (φ k)) (k : t n) ↦ x k) := by
    ext x
    simp [f, g, aux]
  -- Now fe define `Bₙ` and `Tₙ` as follows. `Bₙ` is a cylinder.
  let B n := f ⁻¹' (A n)
  let T n := (g n) ⁻¹' (S n)
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, test n]
    rfl
  -- `gₙ` is measurable. We have to play with `Heq` to prove measurability of `cast`.
  have mg n : Measurable (g n) :=
    measurable_pi_lambda _ (fun i ↦ (meas_cast _).comp <| measurable_pi_apply _)
  -- We deduce that `Tₙ` is measurable.
  have mT n : MeasurableSet (T n) := (mS n).preimage (mg n)
  -- The sequence `(Bₙ)` satisfies the hypotheses of `firstLemma`, we now have to prove that we can
  -- rewrite the goal in terms of `B`.
  have B_anti : Antitone B := fun m n hmn ↦ Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  have B_mem n : B n ∈ cylinders (fun k ↦ X (φ k)) :=
    (mem_cylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  -- Taking the preimage of a product indexed by `sₙ` by `gₙ` yields a product indexed by `uₙ`,
  -- again we have to play with `cast`.
  have imp n (u : (i : s n) → Set (X i)) : (g n) ⁻¹' (Set.univ.pi u) =
      Set.univ.pi (fun k : t n ↦ u ((aux n).symm k)) := by
    ext x
    simp only [Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Subtype.forall, Equiv.coe_fn_symm_mk, g, aux]
    refine ⟨fun h' k hk ↦ ?_, fun h' i hi ↦ ?_⟩
    · convert h' (φ k) (e' n k hk)
      rw [@omg_ ℕ (fun k ↦ X (φ k)) (t n) x ⟨φ.symm (φ k), by simp [hk]⟩ ⟨k, hk⟩]
      simp
    · convert h' (φ.symm i) (e n i hi)
      rw [← @omg_ ι (fun i ↦ Set (X i)) (s n) u ⟨φ (φ.symm i), by simp [hi]⟩ ⟨i, hi⟩ (by simp) _,
        omg'_ (X (φ (φ.symm i))) (X i) (by simp) (x ⟨φ.symm i, e n i hi⟩)
          (u ⟨φ (φ.symm i), by simp [hi]⟩) (by simp)]
  -- The pushforward measure of the product measure of `(ν_{φ k})_{k ∈ tₙ}` by `gₙ` is the
  -- product measre of `(∨ᵢ)_{i ∈ sₙ}`.
  have test' n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun k : t n ↦ μ (φ k))).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (mg n), imp n, Measure.pi_pi,
      Fintype.prod_equiv (aux n).symm _ (fun i ↦ (μ i) (x i))]
    · simp [aux]
    · exact MeasurableSet.pi Set.countable_univ (by simp [mx])
  -- This yields the desired result: the `kolContent` of `Aₙ` is the same as the one of `Bₙ`.
  have crucial n : kolContent μ_proj (A n) = kolContent μ_proj' (B n) := by
    simp_rw [fun n ↦ kolContent_congr μ_proj
      (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
      fun n ↦ kolContent_congr μ_proj'
      (by rw [mem_cylinders]; exact ⟨t n, T n, mT n, B_eq n⟩) (B_eq n) (mT n), T, test' n]
    rw [Measure.map_apply (mg n) (mS n)]
  simp_rw [crucial, fun n ↦ kolContent_eq_prod_meas (fun k ↦ μ (φ k)) (B_mem n),
    ← measure_empty (μ := prod_meas (fun k ↦ μ (φ k))), ← B_inter]
  exact tendsto_measure_iInter (fun n ↦ cylinders_measurableSet (B_mem n))
    B_anti ⟨0, measure_ne_top _ _⟩

/-- The `kolContent` of `cylinder I S` can be computed by integrating the indicator of
`cylinder I S` over the variables indexed by `I`. -/
theorem kolContent_eq_lmarginal [DecidableEq ι] [∀ (S : Finset ι) i, Decidable (i ∈ S)]
    (I : Finset ι) {S : Set ((i : I) → X i)} (mS : MeasurableSet S) (x : (i : ι) → X i) :
    kolContent (isProjectiveMeasureFamily_pi μ) (cylinder I S) =
    (∫⋯∫⁻_I, (cylinder I S).indicator 1 ∂μ) x := by
  rw [kolContent_congr (isProjectiveMeasureFamily_pi μ)
      (by rw [mem_cylinders]; exact ⟨I, S, mS, rfl⟩) rfl mS,
    ← lintegral_indicator_one₀ mS.nullMeasurableSet]
  refine lintegral_congr <| fun x ↦ ?_
  by_cases hx : x ∈ S <;> simp [hx, Function.updateFinset]

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$.
This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem thirdLemma (A : ℕ → Set ((i : ι) → X i)) (A_mem : ∀ n, A n ∈ cylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
    infer_instance
  set μ_proj := isProjectiveMeasureFamily_pi μ
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa only [mem_cylinders, exists_prop] using A_mem n
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set,
  -- so that we can apply `secondLemma`. The proof is very similar to the previous one, except
  -- that the use of coercions avoids manipulating `cast`, as equalities will hold by `rfl`.
  let u := ⋃ n, (s n).toSet
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t : ℕ → Finset u := fun n ↦ (s n).preimage Subtype.val Subtype.val_injective.injOn
  -- These are a few lemmas to move between `sₙ` and `tₙ`.
  have su n : (s n).toSet ⊆ u := Set.subset_iUnion (fun n ↦ (s n).toSet) n
  have st n i (hi : i ∈ s n) : ⟨i, su n hi⟩ ∈ t n := by simpa [t] using hi
  have ts n i (hi : i ∈ t n) : i.1 ∈ s n := by simpa [t] using hi
  -- This brings again `aux`.
  let aux : (n : ℕ) → (s n ≃ t n) := fun n ↦
    { toFun := fun i ↦ ⟨⟨i.1, su n i.2⟩, st n i i.2⟩
      invFun := fun i ↦ ⟨i.1.1, ts n i i.2⟩
      left_inv := fun i ↦ by simp
      right_inv := fun i ↦ by simp }
  have h n (i : s n) : X (aux n i) = X i.1 := rfl
  have imp n (x : (i : s n) → Set (X i)) : Set.univ.pi (fun i : t n ↦ x ((aux n).invFun i)) =
      (fun x i ↦ cast (h n i) (x (aux n i))) ⁻¹' Set.univ.pi x := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, Set.mem_preimage]
    exact ⟨fun h i hi ↦ h i (su n hi) (st n i hi), fun h i hi1 hi2 ↦ h i (ts n ⟨i, hi1⟩ hi2)⟩
  have meas n : Measurable (fun (x : (i : t n) → X i) i ↦ cast (h n i) (x (aux n i))) := by
    apply measurable_pi_lambda
    exact fun _ ↦ measurable_pi_apply _
  have crucial n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun i : t n ↦ μ i)).map (fun x i ↦ cast (h n i) (x (aux n i))) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (meas n), ← imp n x, Measure.pi_pi, Fintype.prod_equiv (aux n)]
    · simp [aux]
    · exact MeasurableSet.pi Set.countable_univ (by simp [mx])
  let T : (n : ℕ) → Set ((i : t n) → X i) :=
    fun n ↦ (fun x i ↦ cast (h n i) (x (aux n i))) ⁻¹' (S n)
  have mT n : MeasurableSet (T n) := by
    apply (mS n).preimage (meas n)
  let B : ℕ → Set (∀ i : u, X i) := fun n ↦ cylinder (t n) (T n)
  classical
  have B_eq n : B n = (fun x : (i : u) → X i ↦ fun i ↦ if hi : i ∈ u
      then x ⟨i, hi⟩ else Classical.ofNonempty) ⁻¹' (A n) := by
    ext x
    simp [B, T, -cast_eq]
    have this k : (fun i : s k ↦ (fun j ↦ if hj : j ∈ u then x ⟨j, hj⟩
        else Classical.ofNonempty) i.1) = fun i ↦ cast (h k i) (x (aux k i)) := by
      ext i
      simp only [i.2, su k i.2, ↓reduceDite, cast_eq]
      rfl
    rw [← this, ← mem_cylinder (s n) (S n) (fun j ↦ if hj : j ∈ u then x ⟨j, hj⟩
        else Classical.ofNonempty), ← A_eq]
  have B_anti : Antitone B := by
    intro m n hmn
    simp_rw [B_eq]
    exact Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B_eq, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  let μ_proj' := isProjectiveMeasureFamily_pi (fun i : u ↦ μ i)
  have this n : kolContent μ_proj (A n) = kolContent μ_proj' (B n) := by
    simp_rw [fun n ↦ kolContent_congr μ_proj
      (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
      fun n ↦ kolContent_congr μ_proj'
      (by rw [mem_cylinders]; exact ⟨t n, T n, mT n, rfl⟩) rfl (mT n), T, crucial n]
    rw [Measure.map_apply (meas n) (mS n)]
  simp_rw [this]
  -- We now have two cases: if `u` is finite, then the result is simple because
  -- we have an actual measure.
  rcases finite_or_infinite u with (u_fin | u_inf)
  · have obv : (fun _ ↦ 1 : ((i : u) → X i) → ℝ≥0∞) = 1 := rfl
    have := Fintype.ofFinite u
    have concl n : kolContent μ_proj' (B n) =
        (Measure.pi (fun i : u ↦ μ i)) (cylinder (t n) (T n)) := by
      simp_rw [B, kolContent_eq_lmarginal (fun i : u ↦ μ i) (t n) (mT n) Classical.ofNonempty]
      rw [← lmarginal_eq_of_disjoint_diff (μ := (fun i : u ↦ μ i)) _
          (dependsOn_cylinder_indicator (T n))
          (t n).subset_univ, lmarginal_univ, ← obv, lintegral_indicator_const]
      · simp
      · exact @measurableSet_cylinder u (fun i : u ↦ X i) _ (t n) (T n) (mT n)
      · rw [Finset.coe_univ, ← Set.compl_eq_univ_diff]
        exact disjoint_compl_right
      · rw [← obv, measurable_indicator_const_iff 1]
        exact @measurableSet_cylinder u (fun i : u ↦ X i) _ (t n) (T n) (mT n)
    simp_rw [concl, ← measure_empty (μ := Measure.pi (fun i : u ↦ μ i)), ← B_inter]
    exact tendsto_measure_iInter (fun n ↦ measurableSet_cylinder (t n) (T n) (mT n))
      B_anti ⟨0, measure_ne_top _ _⟩
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    refine secondLemma (fun i : u ↦ μ i) φ (fun n ↦ ?_) B_anti B_inter
    simp only [mem_cylinders, exists_prop]
    exact ⟨t n, T n, mT n, rfl⟩

/-- The `kolContent` associated to a family of probability measures is $\simga$-subadditive. -/
theorem kolContent_sigma_subadditive ⦃f : ℕ → Set ((i : ι) → X i)⦄ (hf : ∀ n, f n ∈ cylinders X)
    (hf_Union : (⋃ n, f n) ∈ cylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) (⋃ n, f n) ≤
    ∑' n, kolContent (isProjectiveMeasureFamily_pi μ) (f n) := by
  classical
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩;
    infer_instance
  refine (kolContent (isProjectiveMeasureFamily_pi μ)).sigma_subadditive_of_sigma_additive
    setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
    (kolContent (isProjectiveMeasureFamily_pi μ)) (fun h ↦ ?_) ?_ hf hf_Union hf'
  · rcases (mem_cylinders _).1 h with ⟨s, S, mS, s_eq⟩
    rw [s_eq, kolContent_eq_lmarginal μ (mS := mS) (x := Classical.ofNonempty)]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
    rw [← lmarginal_const (μ := μ) (s := s) 1 Classical.ofNonempty]
    apply lmarginal_mono
    intro x
    apply Set.indicator_le
    simp
  · intro s hs anti_s inter_s
    exact thirdLemma μ s hs anti_s inter_s

/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the assiocated product
measure. -/
noncomputable def measure_produit : Measure ((i : ι) → X i) := by
  exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (kolContent (isProjectiveMeasureFamily_pi μ))
    (kolContent_sigma_subadditive μ)

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_measure_produit :
    IsProjectiveLimit (measure_produit μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_proj
  have h_mem : (fun (x : (i : ι) → X i) (i : I) ↦ x i) ⁻¹' s ∈ cylinders X := by
    rw [mem_cylinders]; exact ⟨I, s, hs, rfl⟩
  rw [measure_produit, Measure.ofAddContent_eq _ _ _ _ h_mem,
    kolContent_congr (isProjectiveMeasureFamily_pi μ) h_mem rfl hs]

instance : IsProbabilityMeasure (measure_produit μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← Measure.map_apply, isProjectiveLimit_measure_produit μ]
  · simp
  · exact measurable_proj _
  · exact MeasurableSet.univ

theorem measure_boxes {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    measure_produit μ (Set.pi s t) = ∏ i ∈ s, (μ i) (t i) := by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← Measure.map_apply, isProjectiveLimit_measure_produit μ,
    Measure.pi_pi]
  · rw [Finset.univ_eq_attach, Finset.prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_proj _
  · exact MeasurableSet.pi Set.countable_univ fun i _ ↦ mt i.1 i.2

theorem measure_cylinder {s : Finset ι} {S : Set ((i : s) → X i)} (mS : MeasurableSet S) :
    measure_produit μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply (measurable_proj' _) mS, isProjectiveLimit_measure_produit μ]

theorem integral_dep_measure_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : s) → X i) → E} (hf : StronglyMeasurable f) :
    ∫ y, f ((fun x (i : s) ↦ x i) y) ∂measure_produit μ =
    ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map (measurable_proj' _).aemeasurable hf.aestronglyMeasurable,
    isProjectiveLimit_measure_produit μ]

theorem integral_dependsOn [DecidableEq ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : ι) → X i) → E} (mf : StronglyMeasurable f) (hf : DependsOn f s)
    (x : (i : ι) → X i) :
    ∫ y, f y ∂measure_produit μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : ((i : s) → X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g ((fun z (i : s) ↦ z i) y) = f y := by
    apply hf
    intro i hi
    simp only [Function.updateFinset, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  rw [← integral_congr_ae <| eventually_of_forall this, integral_dep_measure_prod]
  exact mf.comp_measurable measurable_updateFinset

theorem lintegral_dep {s : Finset ι} {f : ((i : s) → X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f ((fun x (i : s) ↦ x i) y) ∂measure_produit μ =
    ∫⁻ y, f y∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf (measurable_proj' _), isProjectiveLimit_measure_produit μ]

theorem lintegral_dependsOn [DecidableEq ι]
    {f : ((i : ι) → X i) → ℝ≥0∞} (mf : Measurable f) {s : Finset ι} (hf : DependsOn f s)
    (x : (i : ι) → X i) : ∫⁻ y, f y ∂measure_produit μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : ((i : s) → X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g ((fun z (i : s) ↦ z i) y) = f y := by
    refine hf fun i hi ↦ ?_
    simp only [Function.updateFinset, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  simp_rw [← this]
  rw [lintegral_dep]
  · rfl
  · exact mf.comp measurable_updateFinset
