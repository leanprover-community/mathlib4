import Mathlib

open Set MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι ι' : Type*}

section Definitions

variable {mΩ₀ : MeasurableSpace Ω} (P : Measure[mΩ₀] Ω := by volume_tac) (mΩ : MeasurableSpace Ω)

/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel `κ` and
a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.
It will be used for families of pi_systems. -/
def iCondIndepSets' (π : ι → Set (Set Ω)) : Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
  P⁻⸨⋂ i ∈ s, f i| mΩ⸩ =ᵐ[P] ∏ i ∈ s, P⁻⸨f i | mΩ⸩

/-- Two sets of sets `s₁, s₂` are independent with respect to a kernel `κ` and a measure `μ` if for
any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def CondIndepSets' (s1 s2 : Set (Set Ω)) : Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → P⁻⸨t1 ∩ t2| mΩ⸩ =ᵐ[P] P⁻⸨t1| mΩ⸩ * P⁻⸨t2| mΩ⸩

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
kernel `κ` and a measure `μ` if the family of sets of measurable sets they define is independent. -/
def iCondIndep' (m : ι → MeasurableSpace Ω) : Prop :=
  iCondIndepSets' P mΩ (fun x ↦ {s | MeasurableSet[m x] s})

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
kernel `κ` and a measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def CondIndep' (m₁ m₂ : MeasurableSpace Ω) : Prop :=
  CondIndepSets' P mΩ {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s}

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def iCondIndepSet' (s : ι → Set Ω) : Prop :=
  iCondIndep' P mΩ (m := fun i ↦ generateFrom {s i})

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def CondIndepSet' (s t : Set Ω) : Prop :=
  CondIndep' P mΩ (generateFrom {s}) (generateFrom {t})

end Definitions


section ByDefinition

variable {mΩ₀ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω}

variable {π : ι → Set (Set Ω)} {s : ι → Set Ω} {m : ι → MeasurableSpace Ω} {S : Finset ι}
  {g : ι' → ι}

lemma iCondIndepSets'.meas_biInter (h : iCondIndepSets' P mΩ π) (s : Finset ι)
    {f : ι → Set Ω} (hf : ∀ i, i ∈ s → f i ∈ π i) :
    P⁻⸨⋂ i ∈ s, f i| mΩ⸩ =ᵐ[P] ∏ i ∈ s, P⁻⸨f i| mΩ⸩ := h s hf

lemma iCondIndepSets'.meas_iInter [Fintype ι] (h : iCondIndepSets' P mΩ π) (hs : ∀ i, s i ∈ π i) :
    P⁻⸨⋂ i, s i| mΩ⸩ =ᵐ[P] ∏ i, P⁻⸨s i| mΩ⸩ := by
  filter_upwards [h.meas_biInter Finset.univ (fun _i _ ↦ hs _)] with a ha using by simp [← ha]

lemma iCondIndep'.iCondIndepSets'' (hP : iCondIndep' P mΩ m) :
    iCondIndepSets' P mΩ (fun x ↦ {s | MeasurableSet[m x] s}) := hP

lemma iCondIndep'.meas_biInter (hP : iCondIndep' P mΩ m)
    (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) :
    P⁻⸨⋂ i ∈ S, s i| mΩ⸩ =ᵐ[P] ∏ i ∈ S, P⁻⸨s i| mΩ⸩ := hP _ hs

lemma iCondIndep'.meas_iInter [Fintype ι] (h : iCondIndep' P mΩ m)
    (hs : ∀ i, MeasurableSet[m i] (s i)) :
    P⁻⸨⋂ i, s i| mΩ⸩ =ᵐ[P] ∏ i, P⁻⸨s i| mΩ⸩ := by
  filter_upwards [h.meas_biInter (fun i (_ : i ∈ Finset.univ) ↦ hs _)] with a ha
  simp [← ha]

@[nontriviality, simp]
lemma iCondIndepSets'.of_subsingleton (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
 [Subsingleton ι] : iCondIndepSets' P mΩ π:= by
  rintro s f hf
  obtain rfl | ⟨i, rfl⟩ : s = ∅ ∨ ∃ i, s = {i} := by
    simpa using (subsingleton_of_subsingleton (s := (s : Set ι))).eq_empty_or_singleton
  · simp [condLExp_one hm P]
  · simp

@[nontriviality, simp]
lemma iCondIndep'.of_subsingleton (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] [Subsingleton ι] :
    iCondIndep' P mΩ m := by simp [iCondIndep', hm]

lemma iCondIndepSets'.precomp (hg : Function.Injective g) (h : iCondIndepSets' P mΩ π) :
    iCondIndepSets' P mΩ (π ∘ g) := by
  intro s f hf
  let f' := Function.extend g f fun _ => ∅
  have f'_apply x : f' (g x) = f x := hg.extend_apply ..
  classical
  have hf' : ∀ i ∈ s.image g, f' i ∈ π i := by
    simp_rw [Finset.forall_mem_image, f'_apply]
    exact hf
  filter_upwards [@h (s.image g) f' hf'] with a ha
  simpa [Finset.set_biInter_finset_image, Finset.prod_image hg.injOn, f'_apply] using ha

lemma iCondIndepSets'.of_precomp (hg : Function.Surjective g) (h : iCondIndepSets' P mΩ (π ∘ g)) :
    iCondIndepSets' P mΩ π := by
  obtain ⟨g', hg'⟩ := hg.hasRightInverse
  convert h.precomp hg'.injective
  rw [Function.comp_assoc, hg'.comp_eq_id, Function.comp_id]

lemma iCondIndepSets_precomp_of_bijective' (hg : Function.Bijective g) :
    iCondIndepSets' P mΩ (π ∘ g) ↔ iCondIndepSets' P mΩ π :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

lemma iCondIndep'.precomp (hg : Function.Injective g) (h : iCondIndep' P mΩ m) :
    iCondIndep' P mΩ (m ∘ g) := (iCondIndepSets'.precomp hg h :)

lemma iCondIndep'.of_precomp (hg : Function.Surjective g) (h : iCondIndep' P mΩ (m ∘ g)) :
    iCondIndep' P mΩ m := iCondIndepSets'.of_precomp hg h

lemma iCondIndep_precomp_of_bijective (hg : Function.Bijective g) :
    iCondIndep' P mΩ (m ∘ g) ↔ iCondIndep' P mΩ m :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

lemma iCondIndepSet'.precomp (hg : Function.Injective g) (h : iCondIndepSet' P mΩ s) :
    iCondIndepSet' P mΩ (s ∘ g) := iCondIndep'.precomp hg h

lemma iCondIndepSet'.of_precomp (hg : Function.Surjective g) (h : iCondIndepSet' P mΩ (s ∘ g)) :
    iCondIndepSet' P mΩ s := iCondIndep'.of_precomp hg h

lemma iCondIndepSet_precomp_of_bijective (hg : Function.Bijective g) :
    iCondIndepSet' P mΩ (s ∘ g) ↔ iCondIndepSet' P mΩ s :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

section Indep

variable {mΩ₀ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω}

@[symm]
theorem CondIndepSets'.symm {s₁ s₂ : Set (Set Ω)} (h : CondIndepSets' P mΩ s₁ s₂) :
    CondIndepSets' P mΩ s₂ s₁ := by
  intro t1 t2 ht1 ht2
  filter_upwards [h t2 t1 ht2 ht1] with a ha
  rwa [Set.inter_comm, mul_comm]

@[symm]
theorem CondIndep'.symm {m₁ m₂ : MeasurableSpace Ω} (h : CondIndep' P mΩ m₁ m₂) :
    CondIndep' P mΩ m₂ m₁ := CondIndepSets'.symm h

theorem condIndep'_bot_right (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] (m : MeasurableSpace Ω) :
    CondIndep' P mΩ m ⊥ := by
  intro s t _ ht
  rw [Set.mem_setOf_eq, MeasurableSpace.measurableSet_bot_iff] at ht
  refine Filter.Eventually.of_forall (fun a ↦ ?_)
  rcases ht with ht | ht <;> simp [ht, hm]

theorem condIndep'_bot_left (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] (m : MeasurableSpace Ω) :
    CondIndep' P mΩ ⊥ m := (condIndep'_bot_right hm m).symm

theorem condIndepSet'_empty_right (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] (s : Set Ω) :
    CondIndepSet' P mΩ s ∅ := by
  simp only [CondIndepSet', generateFrom_singleton_empty]
  exact condIndep'_bot_right hm _

theorem condIndepSet'_empty_left (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] (s : Set Ω) :
    CondIndepSet' P mΩ ∅ s :=
  (condIndepSet'_empty_right hm s).symm

theorem condIndepSets'_of_condIndepSets'_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets' P mΩ s₁ s₂) (h31 : s₃ ⊆ s₁) : CondIndepSets' P mΩ s₃ s₂ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2

theorem condIndepSets'_of_condIndepSets'_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets' P mΩ s₁ s₂) (h32 : s₃ ⊆ s₂) : CondIndepSets' P mΩ s₁ s₃ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)

theorem condIndep'_of_condIndep'_of_le_left {m₁ m₂ m₃ : MeasurableSpace Ω}
    (h_indep : CondIndep' P mΩ m₁ m₂) (h31 : m₃ ≤ m₁) : CondIndep' P mΩ m₃ m₂ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2

theorem condIndep'_of_condIndep'_of_le_right {m₁ m₂ m₃ : MeasurableSpace Ω}
    (h_indep : CondIndep' P mΩ m₁ m₂) (h32 : m₃ ≤ m₂) : CondIndep' P mΩ m₁ m₃ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)

theorem iCondIndep_of_iCondIndep_of_le {m₁ m₂ : ι → MeasurableSpace Ω}
    (h_indep : iCondIndep' P mΩ m₂) (h_le : ∀ i, m₁ i ≤ m₂ i) : iCondIndep' P mΩ m₁ :=
  fun s t ht ↦ h_indep s fun i hi ↦ h_le i (t i) <| ht i hi

theorem CondIndepSets'.union {s₁ s₂ s' : Set (Set Ω)}
    (h₁ : CondIndepSets' P mΩ s₁ s') (h₂ : CondIndepSets' P mΩ s₂ s') :
    CondIndepSets' P mΩ (s₁ ∪ s₂) s' := by
  intro t1 t2 ht1 ht2
  rcases (Set.mem_union _ _ _).mp ht1 with ht1₁ | ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
  · exact h₂ t1 t2 ht1₂ ht2

@[simp]
theorem CondIndepSets'.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    CondIndepSets' P mΩ (s₁ ∪ s₂) s' ↔ CondIndepSets' P mΩ s₁ s' ∧ CondIndepSets' P mΩ s₂ s' :=
  ⟨fun h =>
    ⟨condIndepSets'_of_condIndepSets'_of_le_left h Set.subset_union_left,
      condIndepSets'_of_condIndepSets'_of_le_left h Set.subset_union_right⟩,
    fun h => CondIndepSets'.union h.left h.right⟩

theorem CondIndepSets'.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : ∀ i, CondIndepSets' P mΩ (s i) s') : CondIndepSets' P mΩ (⋃ n, s n) s' := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_iUnion] at ht1
  obtain ⟨n, ht1⟩ := ht1
  exact hyp n t1 t2 ht1 ht2

theorem CondIndepSets'.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {u : Set ι}
    (hyp : ∀ i ∈ u, CondIndepSets' P mΩ (s i) s') : CondIndepSets' P mΩ (⋃ n ∈ u, s n) s' := by
  intro t1 t2 ht1 ht2
  simp_rw [Set.mem_iUnion] at ht1
  rcases ht1 with ⟨n, hpn, ht1⟩
  exact hyp n hpn t1 t2 ht1 ht2

theorem CondIndepSets'.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    (h₁ : CondIndepSets' P mΩ s₁ s') : CondIndepSets' P mΩ (s₁ ∩ s₂) s' :=
  fun t1 t2 ht1 ht2 => h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2

theorem CondIndepSets'.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ i, CondIndepSets' P mΩ (s i) s') : CondIndepSets' P mΩ (⋂ n, s n) s' := by
  intro t1 t2 ht1 ht2; obtain ⟨n, h⟩ := h; exact h t1 t2 (Set.mem_iInter.mp ht1 n) ht2

theorem CondIndepSets'.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {u : Set ι}
    (h : ∃ i ∈ u, CondIndepSets' P mΩ (s i) s') : CondIndepSets' P mΩ (⋂ n ∈ u, s n) s' := by
  intro t1 t2 ht1 ht2
  rcases h with ⟨n, hn, h⟩
  exact h t1 t2 (Set.biInter_subset_of_mem hn ht1) ht2

theorem iCondIndep_comap_mem_iff {f : ι → Set Ω} :
    iCondIndep' P mΩ (fun i => MeasurableSpace.comap (· ∈ f i) ⊤) ↔ iCondIndepSet' P mΩ f := by
  simp_rw [← generateFrom_singleton, iCondIndepSet']

theorem iCondIndepSets'_singleton_iff {s : ι → Set Ω} :
    iCondIndepSets' P mΩ (fun i ↦ {s i}) ↔
      ∀ S : Finset ι, P⁻⸨⋂ i ∈ S, s i| mΩ⸩ =ᵐ[P] ∏ i ∈ S, P⁻⸨s i| mΩ⸩  := by
  refine ⟨fun h S ↦ h S (fun i _ ↦ rfl), fun h S f hf ↦ ?_⟩
  filter_upwards [h S] with a ha
  have : ∀ i ∈ S, P⁻⸨f i| mΩ⸩ =ᵐ[P] P⁻⸨s i| mΩ⸩ := fun i hi ↦ by rw [hf i hi]
  sorry
  -- rwa [Finset.prod_congr rfl this, Set.iInter₂_congr hf]

theorem condIndepSets'_singleton_iff {s t : Set Ω} :
    CondIndepSets' P mΩ {s} {t} ↔ P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ * P⁻⸨t| mΩ⸩ :=
  ⟨fun h ↦ h s t rfl rfl,
   fun h s1 t1 hs1 ht1 ↦ by rwa [Set.mem_singleton_iff.mp hs1, Set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `Indep` from `iIndep` -/

section FromiIndepToIndep

variable {mΩ₀ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω}

theorem iCondIndepSets'.condIndepSets' {s : ι → Set (Set Ω)} (h_indep : iCondIndepSets' P mΩ s)
    {i j : ι} (hij : i ≠ j) : CondIndepSets' P mΩ (s i) (s j) := by
  classical
  intro t₁ t₂ ht₁ ht₂
  have hf_m : ∀ x : ι, x ∈ ({i, j} : Finset ι) → ite (x = i) t₁ t₂ ∈ s x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simp [hx, ht₁]
    · simp [Finset.mem_singleton.mp hx, hij.symm, ht₂]
  have h_inter : ⋂ (t : ι) (_ : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂ =
      ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ := by
    simp only [Finset.set_biInter_singleton, Finset.set_biInter_insert]
  filter_upwards [h_indep {i, j} hf_m] with a h_indep'
  grind

theorem iCondIndep'.condIndep' {m : ι → MeasurableSpace Ω} (h_indep : iCondIndep' P mΩ m)
    {i j : ι} (hij : i ≠ j) : CondIndep' P mΩ (m i) (m j) :=
  iCondIndepSets'.condIndepSets' h_indep hij

end FromiIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/

variable {mΩ₀ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω}

theorem iCondIndep'.iCondIndepSets' {s : ι → Set (Set Ω)} {m : ι → MeasurableSpace Ω}
    (hms : ∀ i, m i = generateFrom (s i)) (h_indep : iCondIndep' P mΩ m) :
    iCondIndepSets' P mΩ s :=
  fun S f hfs =>
  h_indep S fun x hxS =>
    ((hms x).symm ▸ measurableSet_generateFrom (hfs x hxS) : MeasurableSet[m x] (f x))

theorem CondIndep'.condIndepSets' {s1 s2 : Set (Set Ω)}
    (h_indep : CondIndep' P mΩ (generateFrom s1) (generateFrom s2)) :
    CondIndepSets' P mΩ s1 s2 :=
  fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurableSet_generateFrom ht1) (measurableSet_generateFrom ht2)

end FromMeasurableSpacesToSetsOfSets

end ProbabilityTheory
