import Mathlib.NumberTheory.IccSums

open  TopologicalSpace Filter Function Finset

open scoped Topology

variable {α β γ : Type*}

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
def HasProdFilter (L : Filter (Finset β)) (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b ∈ s, f b) L (𝓝 a)

@[to_additive
/-- `SummableAlongFilter f` means that `f` has some (infinite) sum. -/]
def MultipliableFilter (L : Filter (Finset β)) (f : β → α) : Prop :=
  ∃ a, HasProdFilter L f a

open scoped Classical in
/-- `∏' i, f i` is the product of `f` if along the filter `L` if it exists or 1 otherwise. -/
@[to_additive /-- `∑' i, f i` is the sum  of `f` if along the filter `L` if it exists
 or 0 otherwise. -/]
noncomputable irreducible_def tprodFilter {β} (L : Filter (Finset β)) (f : β → α) :=
  if h : MultipliableFilter L f then
   h.choose
  else 1

@[inherit_doc tprod]
notation3 "∏' " "[" L "]" (...)", "r:67:(scoped f => tprodFilter L f) => r
@[inherit_doc tsumFilter]
notation3 "∑' " "[" L "]" (...)", "r:67:(scoped f => tsumFilter L f) => r

variable (L : Filter (Finset β)) {f : β → α} {a : α}

@[to_additive]
theorem HasProdFilter.multipliableFilter (h : HasProdFilter L f a) : MultipliableFilter L f :=
  ⟨a, h⟩

@[to_additive]
theorem tprodFilter_eq_one_of_not_multipliableFilter (h : ¬MultipliableFilter L f) :
    ∏'[L] b, f b = 1 := by
  simp [tprodFilter_def, h]

@[to_additive]
theorem MultipliableFilter.hasProdFilter {L : Filter (Finset β)} (ha : MultipliableFilter L f) :
    HasProdFilter L f (∏'[L] b, f b) := by
  simp only [tprodFilter_def, ha, dite_true]
  apply ha.choose_spec

@[to_additive]
theorem HasProdFilter.unique {a₁ a₂ : α} [T2Space α] [L.NeBot] :
    HasProdFilter L f a₁ → HasProdFilter L f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique

variable [T2Space α]

@[to_additive]
theorem HasProdFilter.tprodFilter_eq (ha : HasProdFilter L f a) [L.NeBot] : ∏'[L] b, f b = a :=
  (MultipliableFilter.hasProdFilter ha.multipliableFilter).unique L ha

omit [T2Space α] in
/-- Constant one function has product `1` -/
@[to_additive /-- Constant zero function has sum `0` -/]
theorem hasProdFilter_one : HasProdFilter L (fun _ ↦ 1 : β → α) 1 := by
  simp [HasProdFilter, tendsto_const_nhds]

omit [T2Space α] in
@[to_additive]
theorem multipliableFilter_one : MultipliableFilter L (fun _ ↦ 1 : β → α) :=
  (hasProdFilter_one L).multipliableFilter

@[to_additive, simp]
lemma tprodFilter_one_eq_one [L.NeBot] : ∏'[L] _, (1 : α) = 1 := by
  exact (hasProdFilter_one L).tprodFilter_eq


@[to_additive]
theorem MultipliableFilter.hasProdFilter_iff (h : MultipliableFilter L f) [L.NeBot] :
    HasProdFilter L f a ↔ ∏'[L] b, f b = a := by
  apply Iff.intro
  · intro h
    apply h.tprodFilter_eq
  · intro H
    have := h.hasProdFilter
    rw [H] at this
    exact this

omit [T2Space α] in
@[to_additive]
protected theorem HasProdFilter.map [CommMonoid γ] [TopologicalSpace γ] (hf : HasProdFilter L f a)
    {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    HasProdFilter L (g ∘ f) (g a) := by
  have : (g ∘ fun s : Finset β ↦ ∏ b ∈ s, f b) = fun s : Finset β ↦ ∏ b ∈ s, (g ∘ f) b :=
    funext <| map_prod g _
  unfold HasProdFilter
  rw [← this]
  exact (hg.tendsto a).comp hf

variable {γ : Type*} [NonUnitalNonAssocSemiring γ] [TopologicalSpace γ] [IsTopologicalSemiring γ]
{f : β → γ}

theorem HasSumFilter.mul_left (a a₁ : γ) (L : Filter (Finset β)) (h : HasSumFilter L f a₁) :
      HasSumFilter L (fun i ↦ a * f i) (a * a₁) := by
  simpa using h.map L (AddMonoidHom.mulLeft a)  (continuous_const.mul continuous_id)

theorem SummableFilter.mul_left (a) (hf : SummableFilter L f) : SummableFilter L fun i ↦ a * f i :=
  (hf.hasSumFilter.mul_left _).summableFilter

protected theorem SummableFilter.tsumFilter_mul_left {α : Type*} [DivisionSemiring α]
    [TopologicalSpace α] [T2Space α] [IsTopologicalSemiring α] (a : α) (f : β → α)
    [L.NeBot] (hf : SummableFilter L f) :
    ∑'[L] i, a * f i = a * ∑'[L] i, f i :=
  ((hf.hasSumFilter.mul_left) a).tsumFilter_eq

theorem hasSumFilter_mul_left_iff {α : Type*} [DivisionSemiring α] [TopologicalSpace α] [T2Space α]
    [L.NeBot] [IsTopologicalSemiring α] {a a₁ : α} (h : a ≠ 0) (f : β → α) :
      HasSumFilter L (fun i ↦ a * f i) (a * a₁) ↔ HasSumFilter L f a₁ :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, HasSumFilter.mul_left _ _ L⟩

theorem summableFilter_mul_left_iff {α : Type*} [DivisionSemiring α] [TopologicalSpace α]
    [T2Space α] [L.NeBot] [IsTopologicalSemiring α] {a : α} (h : a ≠ 0) (f : β → α) :
      (SummableFilter L fun i ↦ a * f i) ↔ SummableFilter L f :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left L a⁻¹ , fun H ↦ H.mul_left L _⟩

lemma tsumFilter_mul_left {α : Type*} [DivisionSemiring α] [TopologicalSpace α] [T2Space α]
    [L.NeBot] [IsTopologicalSemiring α] (a : α) (f : β → α) :
    ∑'[L] b, a * f b = a * ∑'[L] b, f b := by
  classical
  exact if hf : SummableFilter L f then hf.tsumFilter_mul_left L a
  else if ha : a = 0 then by simp [ha];  apply tsumFilter_zero_eq_zero
  else by rw [tsumFilter_eq_zero_of_not_summableFilter L hf,
              tsumFilter_eq_zero_of_not_summableFilter L
                (mt (summableFilter_mul_left_iff L ha f).mp hf), mul_zero]


@[to_additive]
theorem HasProdFilter.inv {α : Type*} {a : α} {f : β → α} [CommGroup α] [TopologicalSpace α]
    [IsTopologicalGroup α] {L : Filter (Finset β)} (h : HasProdFilter L f a) :
    HasProdFilter L (fun b ↦ (f b)⁻¹) a⁻¹ := by
  apply h.map L (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]
theorem MultipliableFilter.inv {α : Type*} {f : β → α} [CommGroup α] [TopologicalSpace α]
    [IsTopologicalGroup α] {L : Filter (Finset β)}
    (hf : MultipliableFilter L f) : MultipliableFilter L fun b ↦ (f b)⁻¹ :=
  hf.hasProdFilter.inv.multipliableFilter

omit [T2Space α] in
@[to_additive]
theorem HasProdFilter.mul {f g : β → α} {a b : α} [ContinuousMul α] {L : Filter (Finset β)}
    (hf : HasProdFilter L f a) (hg : HasProdFilter L g b) :
    HasProdFilter L (fun b ↦ f b * g b) (a * b) := by
  dsimp only [HasProdFilter] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg

omit [T2Space α] in
@[to_additive]
theorem MultipliableFilter.mul {f g : β → α} [ContinuousMul α] (hf : MultipliableFilter L f)
    (hg : MultipliableFilter L g) :
    MultipliableFilter L (fun b ↦ f b * g b) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  use a * b
  simp [HasProdFilter] at *
  have := Tendsto.mul (ha) (hb)
  apply this.congr
  intro s
  exact Eq.symm prod_mul_distrib

@[to_additive]
theorem HasProdFilter.div {α : Type*} {f g : β → α} {a b : α} [CommGroup α] [TopologicalSpace α]
    [IsTopologicalGroup α] {L : Filter (Finset β)} (hf : HasProdFilter L f a)
    (hg : HasProdFilter L g b) : HasProdFilter L (fun b ↦ f b / g b) (a / b) := by
  simp only [div_eq_mul_inv]
  apply hf.mul hg.inv

@[to_additive]
theorem MultipliableFilter.div {α : Type*} {f g : β → α} [CommGroup α]
    [TopologicalSpace α] [IsTopologicalGroup α] (hf : MultipliableFilter L f)
    (hg : MultipliableFilter L g) : MultipliableFilter L fun b ↦ f b / g b :=
  (hf.hasProdFilter.div hg.hasProdFilter).multipliableFilter

@[to_additive]
protected theorem MultipliableFilter.tprodFilter_div {α : Type*} {f g : β → α} [CommGroup α]
    [TopologicalSpace α] [IsTopologicalGroup α] [T2Space α] [L.NeBot] (hf : MultipliableFilter L f)
    (hg : MultipliableFilter L g) : ∏'[L] b, (f b / g b) = (∏'[L] b, f b) / ∏'[L] b, g b :=
  (hf.hasProdFilter.div hg.hasProdFilter).tprodFilter_eq

omit [T2Space α] in
@[to_additive]
lemma multipliable_iff_multipliableFilter_atTop {f : β → α} :
    Multipliable f ↔ MultipliableFilter atTop f := by
  simp [Multipliable, MultipliableFilter, HasProd, HasProdFilter]

omit [T2Space α] in
@[to_additive]
lemma hasProd_iff_hasProdFilter_atTop {f : β → α} {a : α} :
    HasProd f a ↔ HasProdFilter atTop f a := by
  simp [HasProd, HasProdFilter]

@[to_additive]
lemma tprod_eq_tproFilter_atTop {f : β → α} : ∏' [atTop] b, f b = ∏' b, f b := by
  by_cases h : MultipliableFilter atTop f
  · have := h.hasProdFilter
    rw [this.tprodFilter_eq atTop]
    rw [← multipliable_iff_multipliableFilter_atTop] at h
    have H := h.hasProd
    rw [← hasProd_iff_hasProdFilter_atTop] at this
    apply HasProd.unique this H
  · rw [tprodFilter_eq_one_of_not_multipliableFilter atTop h, tprod_eq_one_of_not_multipliable h]

variable {ι : Type*} {X : α → Type*} [∀ x, CommMonoid (X x)] [∀ x, TopologicalSpace (X x)]

omit [CommMonoid α] [TopologicalSpace α] [T2Space α] in
@[to_additive]
theorem Pi.hasProdFilter {f : β → ∀ x, X x} {g : ∀ x, X x} :
    HasProdFilter L f g ↔ ∀ x, HasProdFilter L (fun i ↦ f i x) (g x) := by
  simp only [HasProdFilter, tendsto_pi_nhds, prod_apply]

omit [CommMonoid α] [TopologicalSpace α] [T2Space α] in
@[to_additive]
theorem Pi.multipliableFilter {f : β → ∀ x, X x} :
    MultipliableFilter L f ↔ ∀ x, MultipliableFilter L fun i ↦ f i x := by
  simp only [MultipliableFilter, Pi.hasProdFilter, Classical.skolem]

omit [CommMonoid α] [TopologicalSpace α] [T2Space α] in
@[to_additive]
theorem tprodFilter_apply [∀ x, T2Space (X x)] {f : β → ∀ x, X x} {x : α} [L.NeBot]
    (hf : MultipliableFilter L f) : (∏'[L] i, f i) x = ∏'[L] i, f i x :=
  ((Pi.hasProdFilter L).mp hf.hasProdFilter x).tprodFilter_eq.symm

def Icc_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N)

def Ico_filter : Filter (Finset ℤ) := atTop.map (fun N : ℕ ↦ Ico (-(N : ℤ)) N)

instance : NeBot (Icc_filter) := by
  simp [Icc_filter, Filter.NeBot.map]

instance : NeBot (Ico_filter) := by
  simp [Ico_filter, Filter.NeBot.map]


lemma tendsto_Icc_atTop_atTop : Tendsto (fun N : ℕ => Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma tendsto_Ico_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    Int.lt_add_one_iff.mpr (le_abs_self x)⟩ ⟩

lemma tendsto_Ioc_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ioc (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioc_subset_Ioc (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x)).le⟩⟩

lemma tendsto_Ioo_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ioo (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioo_subset_Ioo (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x))⟩⟩



@[to_additive]
lemma prodFilter_int_atTop_eq_Icc_filter {f : ℤ → α}
    (hf : MultipliableFilter atTop f) : ∏'[atTop] b, f b  = ∏'[Icc_filter] b, f b := by
  have := (hf.hasProdFilter).comp tendsto_Icc_atTop_atTop
  simp only [Icc_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff]
  apply this.congr
  simp


@[to_additive]
lemma prodFilter_int_atTop_eq_Ico_filter {f : ℤ → α}
    (hf : MultipliableFilter atTop f) : ∏'[atTop] b, f b  = ∏'[Ico_filter] b, f b := by
  have := (hf.hasProdFilter).comp tendsto_Ico_atTop_atTop
  simp only [Ico_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff]
  apply this.congr
  simp

@[to_additive] --this needs a hyp, but lets see what the min it needs
lemma multipliableFilter_int_Icc_eq_Ico_filter {α : Type*} {f : ℤ → α} [CommGroup α]
    [TopologicalSpace α] [ContinuousMul α] [T2Space α] (hf : MultipliableFilter Icc_filter f)
    (hf2 : Tendsto (fun N : ℕ ↦ (f ↑N)⁻¹) atTop (𝓝 1)) : MultipliableFilter Ico_filter f := by
  have := (hf.hasProdFilter)
  apply HasProdFilter.multipliableFilter
  · simp only [Ico_filter] at *
    simp only [HasProdFilter, tendsto_map'_iff] at *
    apply Filter.Tendsto_of_div_tendsto_one _ (by apply this)
    conv =>
      enter [1, N]
      simp
      rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
      simp
    apply hf2

@[to_additive] --this needs a hyp, but lets see what the min it needs
lemma prodFilter_int_Icc_eq_Ico_filter {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α]
    [ContinuousMul α] [T2Space α] (hf : MultipliableFilter Icc_filter f)
    (hf2 : Tendsto (fun N : ℕ ↦ (f ↑N)⁻¹) atTop (𝓝 1)) :
    ∏'[Icc_filter] b, f b  = ∏'[Ico_filter] b, f b := by
  have := (hf.hasProdFilter)
  simp only [Ico_filter] at *
  apply symm
  apply HasProdFilter.tprodFilter_eq
  simp only [HasProdFilter, tendsto_map'_iff] at *
  apply Filter.Tendsto_of_div_tendsto_one _ (by apply this)
  conv =>
    enter [1, N]
    simp
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
    simp
  apply hf2
