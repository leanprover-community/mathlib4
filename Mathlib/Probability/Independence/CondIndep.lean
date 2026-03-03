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
  have : ∀ i ∈ S, P⁻⸨f i| mΩ⸩ = P⁻⸨s i| mΩ⸩ := fun i hi ↦ by rw [hf i hi]
  rwa [Finset.prod_congr rfl this, Set.iInter₂_congr hf]

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

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

variable {mΩ₀ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω}

theorem CondIndepSets'.condIndep_aux {m₂ m : MeasurableSpace Ω} {p1 p2 : Set (Set Ω)}
    (hm' : m ≤ mΩ₀) (hm'₂ : m₂ ≤ mΩ₀) (h2 : m₂ ≤ m) (hp2 : IsPiSystem p2)
    (hpm2 : m₂ = generateFrom p2) (hyp : CondIndepSets' P mΩ p1 p2) {t1 t2 : Set Ω} (ht1 : t1 ∈ p1)
    (ht1m : MeasurableSet[m] t1) (ht2m : MeasurableSet[m₂] t2) :
    P⁻⸨t1 ∩ t2| mΩ⸩ =ᵐ[P] P⁻⸨t1| mΩ⸩ * P⁻⸨t2| mΩ⸩ := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · filter_upwards using by simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · filter_upwards using by simp [condLExp_of_not_sigmaFinite hm hσ]
  induction t2, ht2m using induction_on_inter hpm2 hp2 with
  | empty => simp [← Pi.zero_def]
  | basic u hu => exact hyp t1 u ht1 hu
  | compl u hu ihu =>
    grw [← Set.diff_eq, ← Set.diff_self_inter, condLProb_diff inter_subset_left, condLProb_compl]
    · filter_upwards [ihu, condLProb_le_one P t1] with ω hω ht1
      rw [Pi.sub_apply, Pi.mul_apply, Pi.sub_apply, hω, ENNReal.mul_sub]
      · simp
      · exact fun _ _ ↦ ne_top_of_le_ne_top (by simp) ht1
    all_goals measurability
  | iUnion f hfd hfm ihf =>
    grw [inter_iUnion, condLProb_iUnion hfd (by measurability), condLProb_iUnion
      (hfd.mono fun i j h ↦ (h.inter_left' _).inter_right' _) (by measurability)]
    simp only [Filter.EventuallyEq, ← ae_all_iff] at ihf
    filter_upwards [ihf] with ω hω
    simp [ENNReal.tsum_apply, hω, ENNReal.tsum_mul_left]

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem CondIndepSets'.condIndep' (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {m1 m2 : MeasurableSpace Ω} {p1 p2 : Set (Set Ω)}
    (h1 : m1 ≤ mΩ₀) (h2 : m2 ≤ mΩ₀) (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2) (hyp : CondIndepSets' P mΩ p1 p2) :
    CondIndep' P mΩ m1 m2 := by
  intro t1 t2 ht1 ht2
  induction t1, ht1 using induction_on_inter hpm1 hp1 with
  | empty => simp [← Pi.zero_def]
  | basic t ht =>
    refine CondIndepSets'.condIndep_aux (le_refl _) h2 h2 hp2 hpm2 hyp ht (h1 _ ?_) ht2
    rw [hpm1]
    exact measurableSet_generateFrom ht
  | compl t ht iht =>
    have : tᶜ ∩ t2 = t2 \ (t ∩ t2) := by
      rw [inter_comm t, Set.diff_self_inter, Set.diff_eq_compl_inter]
    grw [this, inter_comm t t2, condLProb_diff (by simp) (by measurability) (by measurability),
      inter_comm, condLProb_compl hm (h1 _ ht)]
    filter_upwards [iht, condLProb_le_one P t2] with ω hω ht2
    rw [Pi.mul_apply, Pi.sub_apply, Pi.sub_apply, hω, ENNReal.sub_mul]
    · simp
    · exact fun _ _ ↦ ne_top_of_le_ne_top (by simp) ht2
  | iUnion f hf_disj hf_meas h =>
    simp only [Filter.EventuallyEq, ← ae_all_iff] at h
    grw [inter_comm, inter_iUnion, condLProb_iUnion
      (hf_disj.mono fun i j h ↦ (h.inter_left' _).inter_right' _) (by measurability),
      condLProb_iUnion hf_disj (by measurability)]
    filter_upwards [h] with ω hω
    simp [ENNReal.tsum_apply, inter_comm t2, hω, ENNReal.tsum_mul_right]

theorem CondIndepSets'.condIndep'' (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] {p1 p2 : Set (Set Ω)}
    (hp1m : ∀ s ∈ p1, MeasurableSet[mΩ₀] s) (hp2m : ∀ s ∈ p2, MeasurableSet[mΩ₀] s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : CondIndepSets' P mΩ p1 p2) :
    CondIndep' P mΩ (generateFrom p1) (generateFrom p2) :=
  hyp.condIndep' hm (generateFrom_le hp1m) (generateFrom_le hp2m) hp1 hp2 rfl rfl

theorem condIndepSets_piiUnionInter_of_disjoint' (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {s : ι → Set (Set Ω)} {S T : Set ι} (h_indep : iCondIndepSets' P mΩ s) (hST : Disjoint S T) :
    CondIndepSets' P mΩ (piiUnionInter s S) (piiUnionInter s T) := by
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
  let g i := ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ
  have h_P_inter : P⁻⸨t1 ∩ t2| mΩ⸩ =ᵐ[P] ∏ i ∈ p1 ∪ p2, P⁻⸨g i| mΩ⸩ := by
    have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
      intro i hi_mem_union
      rw [Finset.mem_union] at hi_mem_union
      rcases hi_mem_union with hi1 | hi2
      · have hi2 : i ∉ p2 := fun hip2 => Set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2)
        simp_rw [g, if_pos hi1, if_neg hi2, Set.inter_univ]
        exact ht1_m i hi1
      · have hi1 : i ∉ p1 := fun hip1 => Set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1)
        simp_rw [g, if_neg hi1, if_pos hi2, Set.univ_inter]
        exact ht2_m i hi2
    have h_p1_inter_p2 :
      ((⋂ x ∈ p1, f1 x) ∩ ⋂ x ∈ p2, f2 x) =
        ⋂ i ∈ p1 ∪ p2, ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ := by
      ext1 x
      simp only [Set.mem_ite_univ_right, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
      exact
        ⟨fun h i _ => ⟨h.1 i, h.2 i⟩, fun h =>
          ⟨fun i hi => (h i (Or.inl hi)).1 hi, fun i hi => (h i (Or.inr hi)).2 hi⟩⟩
    filter_upwards [h_indep _ hgm] with a ha
    rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← ha]
  have h_μg : ∀ i ∈ (p1 ∪ p2 : Finset ι), P⁻⸨g i| mΩ⸩ =ᵐ[P]
    (ite (i ∈ p1) (P⁻⸨f1 i| mΩ⸩) 1) * (ite (i ∈ p2) (P⁻⸨f2 i| mΩ⸩) 1) := by
    intro i
    dsimp only [g]
    split_ifs with h1 h2
    · exact absurd rfl (Set.disjoint_iff_forall_ne.mp hST (hp1 h1) (hp2 h2))
    all_goals simp [hm]
  simp only [Filter.EventuallyEq] at h_μg
  rw [← eventually_finset_ball] at h_μg
  filter_upwards [h_P_inter, h_indep p1 ht1_m, h_indep p2 ht2_m, h_μg] with ω h_P_inter hω1 hω2 hω3
  simp_rw [h_P_inter, Finset.prod_apply, Finset.prod_congr rfl hω3, Pi.mul_apply,
    Finset.prod_mul_distrib, ite_apply]
  simp [Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, ht2_eq, ht1_eq, hω1, hω2]

theorem iCondIndepSet'.condIndep_generateFrom_of_disjoint (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[mΩ₀] (s i)) (hs : iCondIndepSet' P mΩ s) (S T : Set ι)
    (hST : Disjoint S T) : CondIndep' P mΩ
      (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) := by
  rw [← generateFrom_piiUnionInter_singleton_left, ← generateFrom_piiUnionInter_singleton_left]
  refine
    CondIndepSets'.condIndep'' hm
      (fun t ht => generateFrom_piiUnionInter_le _ ?_ _ _ (measurableSet_generateFrom ht))
      (fun t ht => generateFrom_piiUnionInter_le _ ?_ _ _ (measurableSet_generateFrom ht)) ?_ ?_ ?_
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact fun k => generateFrom_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact isPiSystem_piiUnionInter _ (fun k => IsPiSystem.singleton _) _
  · exact condIndepSets_piiUnionInter_of_disjoint' hm
      (iCondIndep'.iCondIndepSets' (fun n => rfl) (by congr)) hST

theorem condIndep'_iSup_of_disjoint (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {m : ι → MeasurableSpace Ω} (h_le : ∀ i, m i ≤ mΩ₀) (h_indep : iCondIndep' P mΩ m)
    {S T : Set ι} (hST : Disjoint S T) :
    CondIndep' P mΩ (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) := by
  refine
    CondIndepSets'.condIndep' hm (iSup₂_le fun i _ => h_le i) (iSup₂_le fun i _ => h_le i) ?_ ?_
      (generateFrom_piiUnionInter_measurableSet m S).symm
      (generateFrom_piiUnionInter_measurableSet m T).symm ?_
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact isPiSystem_piiUnionInter _ (fun n => @isPiSystem_measurableSet Ω (m n)) _
  · exact condIndepSets_piiUnionInter_of_disjoint' hm (by congr) hST

theorem condIndep'_iSup_of_directed_le (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω}
    (h_indep : ∀ i, CondIndep' P mΩ (m i) m') (h_le : ∀ i, m i ≤ mΩ₀) (h_le' : m' ≤ mΩ₀)
    (hdir : Directed (· ≤ ·) m) : CondIndep' P mΩ (⨆ i, m i) m' := by
  let p : ι → Set (Set Ω) := fun n => { t | MeasurableSet[m n] t }
  have hp : ∀ n, IsPiSystem (p n) := fun n => @isPiSystem_measurableSet Ω (m n)
  have h_gen_n : ∀ n, m n = generateFrom (p n) := fun n =>
    (@generateFrom_measurableSet Ω (m n)).symm
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := isPiSystem_iUnion_of_directed_le p hp hdir
  let p' := { t : Set Ω | MeasurableSet[m'] t }
  have hp'_pi : IsPiSystem p' := @isPiSystem_measurableSet Ω m'
  have h_gen' : m' = generateFrom p' := (@generateFrom_measurableSet Ω m').symm
  -- the π-systems defined are independent
  have h : CondIndepSets' P mΩ (⋃ n, p n) p' := by
    refine CondIndepSets'.iUnion ?_
    conv at h_indep =>
      intro i
      rw [h_gen_n i, h_gen']
    exact fun n => (h_indep n).condIndepSets'
  -- now go from π-systems to σ-algebras
  refine CondIndepSets'.condIndep' hm (iSup_le h_le) h_le' hp_supr_pi hp'_pi ?_ h_gen' h
  exact (generateFrom_iUnion_measurableSet _).symm

theorem iCondIndepSet'.condIndep'_generateFrom_lt (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    [Preorder ι] {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[mΩ₀] (s i)) (hs : iCondIndepSet' P mΩ s)
    (i : ι) : CondIndep' P mΩ (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) := by
  convert iCondIndepSet'.condIndep_generateFrom_of_disjoint hm hsm hs {i} { j | j < i }
    (Set.disjoint_singleton_left.mpr (lt_irrefl _)) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.setOf_eq_eq_singleton']

theorem iCondIndepSet'.condIndep'_generateFrom_le (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    [Preorder ι] {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[mΩ₀] (s i)) (hs : iCondIndepSet' P mΩ s)
    (i : ι) {k : ι} (hk : i < k) :
    CondIndep' P mΩ (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) := by
  convert iCondIndepSet'.condIndep_generateFrom_of_disjoint hm hsm hs {k} { j | j ≤ i }
      (Set.disjoint_singleton_left.mpr hk.not_ge) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.setOf_eq_eq_singleton']

theorem iCondIndepSet'.condIndep'_generateFrom_le_nat (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {s : ℕ → Set Ω} (hsm : ∀ i, MeasurableSet[mΩ₀] (s i)) (hs : iCondIndepSet' P mΩ s) (n : ℕ) :
    CondIndep' P mΩ (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) :=
  iCondIndepSet'.condIndep'_generateFrom_le hm hsm hs _ n.lt_succ_self

theorem condIndep'_iSup_of_monotone (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] [SemilatticeSup ι]
    {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω} (h_indep : ∀ i, CondIndep' P mΩ (m i) m')
    (h_le : ∀ i, m i ≤ mΩ₀) (h_le' : m' ≤ mΩ₀) (hmono : Monotone m) :
    CondIndep' P mΩ (⨆ i, m i) m' :=
  condIndep'_iSup_of_directed_le hm h_indep h_le h_le' (Monotone.directed_le hmono)

theorem condIndep'_iSup_of_antitone (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] [SemilatticeInf ι]
    {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω} (h_indep : ∀ i, CondIndep' P mΩ (m i) m')
    (h_le : ∀ i, m i ≤ mΩ₀) (h_le' : m' ≤ mΩ₀) (hanti : Antitone m) :
    CondIndep' P mΩ (⨆ i, m i) m' :=
  condIndep'_iSup_of_directed_le hm h_indep h_le h_le' hanti.directed_le

theorem iCondIndepSets'.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iCondIndepSets' P mΩ π) (haS : a ∉ S) :
    CondIndepSets' P mΩ (piiUnionInter π S) (π a) := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
  let f := fun n => ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.univ)
  have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
    intro n hn_mem_insert
    dsimp only [f]
    rcases Finset.mem_insert.mp hn_mem_insert with hn_mem | hn_mem
    · simp [hn_mem, ht2_mem_pia]
    · grind
  have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS => h_f_mem x (by simp [hxS])
  have h_t1 : t1 = ⋂ n ∈ s, f n := by
    suffices h_forall : ∀ n ∈ s, f n = ft1 n by grind
    intro n hnS
    have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hnS)
    simp_rw [f, if_pos hnS, if_neg hn_ne_a]
  have h_μ_t1 : P⁻⸨t1| mΩ⸩ =ᵐ[P] ∏ n ∈ s, P⁻⸨f n| mΩ⸩ := by
    filter_upwards [hp_ind s h_f_mem_pi] with ω hω
    rw [h_t1, ← hω]
  have h_t2 : t2 = f a := by simp [f]
  have h_μ_inter : P⁻⸨t1 ∩ t2| mΩ⸩ =ᵐ[P] ∏ n ∈ insert a s, P⁻⸨f n| mΩ⸩ := by
    have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
      rw [h_t1, h_t2, Finset.set_biInter_insert, Set.inter_comm]
    filter_upwards [hp_ind (insert a s) h_f_mem] with a' ha'
    rw [h_t1_inter_t2, ← ha']
  have has : a ∉ s := fun has_mem => haS (hs_mem has_mem)
  filter_upwards [h_μ_t1, h_μ_inter] with a' ha1 ha2
  rw [ha2, Finset.prod_insert has, h_t2, mul_comm, Pi.mul_apply, Pi.mul_apply, ← ha1]

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem iCondIndepSets'.iCondIndep' (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (m : ι → MeasurableSpace Ω) (h_le : ∀ i, m i ≤ mΩ₀) (π : ι → Set (Set Ω))
    (h_pi : ∀ i, IsPiSystem (π i)) (h_generate : ∀ i, m i = generateFrom (π i))
    (h_ind : iCondIndepSets' P mΩ π) : iCondIndep' P mΩ m  := by
  classical
  intro s f
  refine Finset.induction ?_ ?_ s
  · simp [hm]
  · intro a S ha_notin_S h_rec hf_m
    have hf_m_S : ∀ x ∈ S, MeasurableSet[m x] (f x) := fun x hx => hf_m x (by simp [hx])
    let p := piiUnionInter π S
    set m_p := generateFrom p with hS_eq_generate
    have h_indep : CondIndep' P mΩ m_p (m a) := by
      have hp : IsPiSystem p := isPiSystem_piiUnionInter π h_pi S
      have h_le' : ∀ i, generateFrom (π i) ≤ mΩ₀ := fun i ↦ (h_generate i).symm.trans_le (h_le i)
      have hm_p : m_p ≤ mΩ₀ := generateFrom_piiUnionInter_le π h_le' S
      exact CondIndepSets'.condIndep' hm hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
        (iCondIndepSets'.piiUnionInter_of_notMem h_ind ha_notin_S)
    have h := h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (Finset.mem_insert_self a S)) ?_
    · filter_upwards [h_rec hf_m_S, h] with a' ha' h'
      rwa [Finset.set_biInter_insert, Finset.prod_insert ha_notin_S, Pi.mul_apply, ← ha']
    · have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
        intro n hn
        rw [hS_eq_generate, h_generate n]
        exact le_generateFrom_piiUnionInter (S : Set ι) hn
      have h_S_f : ∀ i ∈ S, MeasurableSet[m_p] (f i) :=
        fun i hi ↦ (h_le_p i hi) (f i) (hf_m_S i hi)
      exact S.measurableSet_biInter h_S_f

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t`,
* `IndepSet s t κ μ ↔ IndepSets {s} {t} κ μ`.
-/

variable {mΩ₀ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω}

theorem iCondIndepSet'_iff_iCondIndepSets'_singleton (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {f : ι → Set Ω} (hf : ∀ i, MeasurableSet[mΩ₀] (f i)) :
    iCondIndepSet' P mΩ f ↔ iCondIndepSets' P mΩ (fun i ↦ {f i}) :=
  ⟨iCondIndep'.iCondIndepSets' fun _ ↦ rfl,
    iCondIndepSets'.iCondIndep' hm _
      (fun i ↦ generateFrom_le <| by rintro t (rfl : t = _); exact hf _) _
      (fun _ ↦ IsPiSystem.singleton _) fun _ ↦ rfl⟩

theorem iCondIndepSet'.meas_biInter {f : ι → Set Ω} (h : iCondIndepSet' P mΩ f) (s : Finset ι) :
    P⁻⸨⋂ i ∈ s, f i| mΩ⸩ =ᵐ[P] ∏ i ∈ s, P⁻⸨f i| mΩ⸩ :=
  iCondIndep'.iCondIndepSets' (fun _ ↦ rfl) h _ (by simp)

theorem iCondIndepSet'_iff_meas_biInter (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {f : ι → Set Ω} (hf : ∀ i, MeasurableSet[mΩ₀] (f i)) :
    iCondIndepSet' P mΩ f ↔ ∀ s, P⁻⸨⋂ i ∈ s, f i| mΩ⸩ =ᵐ[P] ∏ i ∈ s, P⁻⸨f i| mΩ⸩ :=
  (iCondIndepSet'_iff_iCondIndepSets'_singleton hm hf).trans iCondIndepSets'_singleton_iff

theorem iCondIndepSets'.iCondIndepSet_of_mem (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {π : ι → Set (Set Ω)} {f : ι → Set Ω} (hfπ : ∀ i, f i ∈ π i)
    (hf : ∀ i, MeasurableSet[mΩ₀] (f i)) (hπ : iCondIndepSets' P mΩ π) :
    iCondIndepSet' P mΩ f :=
  (iCondIndepSet'_iff_meas_biInter hm hf).2 fun _t ↦ hπ.meas_biInter _ fun _i _ ↦ hfπ _

variable {s t : Set Ω} (S T : Set (Set Ω))

theorem condIndepSet'_iff_condIndepSets'_singleton (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hs_meas : MeasurableSet[mΩ₀] s) (ht_meas : MeasurableSet[mΩ₀] t) :
    CondIndepSet' P mΩ s t ↔ CondIndepSets' P mΩ {s} {t} :=
  ⟨CondIndep'.condIndepSets', fun h =>
    CondIndepSets'.condIndep' hm
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (generateFrom_le fun u hu => by rwa [Set.mem_singleton_iff.mp hu])
      (IsPiSystem.singleton s) (IsPiSystem.singleton t) rfl rfl h⟩

theorem condIndepSet'_iff_measure_inter_eq_mul (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hs_meas : MeasurableSet[mΩ₀] s) (ht_meas : MeasurableSet[mΩ₀] t) :
    CondIndepSet' P mΩ s t ↔ P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ * P⁻⸨t| mΩ⸩ :=
  (condIndepSet'_iff_condIndepSets'_singleton hm hs_meas ht_meas).trans condIndepSets'_singleton_iff

theorem CondIndepSet'.measure_inter_eq_mul (h : CondIndepSet' P mΩ s t) :
    P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ * P⁻⸨t| mΩ⸩ :=
  CondIndep'.condIndepSets' h _ _ (by simp) (by simp)

theorem CondIndepSets'.condIndepSet_of_mem (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hs : s ∈ S) (ht : t ∈ T) (hs_meas : MeasurableSet[mΩ₀] s) (ht_meas : MeasurableSet[mΩ₀] t)
    (h_indep : CondIndepSets' P mΩ S T) : CondIndepSet' P mΩ s t :=
  (condIndepSet'_iff_measure_inter_eq_mul hm hs_meas ht_meas).mpr (h_indep s t hs ht)

theorem CondIndep'.condIndepSet_of_measurableSet {m₁ m₂ : MeasurableSpace Ω}
    (h_indep : CondIndep' P mΩ m₁ m₂) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) : CondIndepSet' P mΩ s t := by
  refine fun s' t' hs' ht' => h_indep s' t' ?_ ?_
  · induction s', hs' using generateFrom_induction with
    | hC t ht => exact ht ▸ hs
    | empty => exact @MeasurableSet.empty _ m₁
    | compl u _ hu => exact hu.compl
    | iUnion f _ hf => exact .iUnion hf
  · induction t', ht' using generateFrom_induction with
    | hC s hs => exact hs ▸ ht
    | empty => exact @MeasurableSet.empty _ m₂
    | compl u _ hu => exact hu.compl
    | iUnion f _ hf => exact .iUnion hf

theorem condIndep'_iff_forall_condIndepSet' (m₁ m₂ : MeasurableSpace Ω) :
    CondIndep' P mΩ m₁ m₂ ↔
      ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → CondIndepSet' P mΩ s t :=
  ⟨fun h => fun _s _t hs ht => h.condIndepSet_of_measurableSet hs ht, fun h s t hs ht =>
    h s t hs ht s t (measurableSet_generateFrom (Set.mem_singleton s))
      (measurableSet_generateFrom (Set.mem_singleton t))⟩

end IndepSet

end ProbabilityTheory
