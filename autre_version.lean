import Mathlib.KolmogorovExtension4.compo_perso
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Data.PNat.Interval

open MeasureTheory ProbabilityTheory Set ENNReal Filter Topology

variable {X : ℕ → Type*} [∀ n, Nonempty (X n)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((i : Iic k) → X i) ((i : Ioc k (k + 1)) → X i))
variable [∀ k, IsMarkovKernel (κ k)]

lemma mem_Iic_zero {i : ℕ} (hi : i ∈ Iic 0) : i = 0 := by simpa using hi

def zer : (X 0) ≃ᵐ ((i : Iic 0) → X i) where
  toFun := fun x₀ i ↦ (mem_Iic_zero i.2).symm ▸ x₀
  invFun := fun x ↦ x ⟨0, mem_Iic.2 <| le_refl 0⟩
  left_inv := fun x₀ ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨0, mem_Iic.2 <| le_refl 0⟩ = i := by simp [(mem_Iic_zero i.2).symm]
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨0, mem_Iic.2 <| le_refl 0⟩ = i := by simp [(mem_Iic_zero i.2).symm]
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

noncomputable def family (x₀ : X 0) :
  (S : Finset ℕ+) → Measure ((k : S) → X k) := fun S ↦
  (kerNat κ 0 (S.sup id).1 (zer x₀)).map
  (fun x (i : S) ↦ x ⟨i.1, ⟨i.1.2, Finset.le_sup (f := id) i.2⟩⟩)

theorem isMarkovKernel_compProd {i j k : ℕ}
    (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))
    [IsMarkovKernel κ] [IsMarkovKernel η] (hij : i < j) (hjk : j < k) :
    IsMarkovKernel (κ ⊗ₖ' η) := by
  rw [compProd]
  simp only [hij, hjk, and_self, ↓reduceDite, split]
  infer_instance

theorem isMarkovKernel_castPath {i j k : ℕ}
    (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) [IsMarkovKernel κ] (hjk : j = k)  :
    IsMarkovKernel (castPath κ hjk) := by
  rw [castPath]; infer_instance

theorem isMarkovKernel_kerInterval {i j k : ℕ}
    (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) [h₀ : IsMarkovKernel κ₀]
    (κ : ∀ k, kernel ((x : Iic k) → X x) ((x : Ioc k (k + 1)) → X x)) [∀ k, IsMarkovKernel (κ k)]
    (hij : i < j) (hjk : j ≤ k) :
    IsMarkovKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => linarith
  | succ n hn =>
    rw [kerInterval_succ]
    split_ifs with h
    · apply isMarkovKernel_castPath
    · have : j ≤ n := Nat.lt_succ.1 <| lt_iff_le_and_ne.2 ⟨hjk, h⟩
      have _ := hn this
      exact isMarkovKernel_compProd _ _ (lt_of_lt_of_le hij this) n.lt_succ_self

theorem isMarkovKernel_kerNat {i j : ℕ}
    (κ : ∀ k, kernel ((x : Iic k) → X x) ((x : Ioc k (k + 1)) → X x))
    [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
    IsMarkovKernel (kerNat κ i j) := by
  simp only [kerNat, hij, ↓reduceIte]
  exact isMarkovKernel_kerInterval _ _ i.lt_succ_self (Nat.succ_le.2 hij)

theorem proj_kerNat {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
    kernel.map (kerNat κ 0 l)
      (fun (x : ((i : Ioc 0 l) → X i)) (i : Ioc 0 k) ↦ x ⟨i.1, Ioc_subset_Ioc_right hkl i.2⟩)
      (measurable_proj₂ ..) = kerNat κ 0 k := by
  by_cases h : k = l
  · cases h
    exact kernel.map_id _
  · have hkl : k < l := lt_iff_le_and_ne.2 ⟨hkl, h⟩
    ext x s ms
    rw [kernel.map_apply' _ _ _ ms, ← compProd_kerNat κ hk hkl,
      compProd_apply' _ _ hk hkl _ (measurable_proj₂ _ _ _ ms)]
    simp_rw [preimage_preimage]
    refine Eq.trans (b := ∫⁻ b, s.indicator 1 b ∂kerNat κ 0 k x) ?_ ?_
    · refine lintegral_congr fun b ↦ ?_
      simp only [indicator, Pi.one_apply]
      split_ifs with hb
      · have := isMarkovKernel_kerNat κ hkl
        convert measure_univ
        · ext c
          simp only [er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_preimage, mem_setOf_eq,
            mem_univ, iff_true]
          convert hb using 1
          ext i
          simp [(mem_Ioc.2 i.2).2]
        · infer_instance
      · convert measure_empty
        · ext c
          simp only [er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_preimage, mem_setOf_eq,
            mem_empty_iff_false, iff_false]
          convert hb using 2
          ext i
          simp [(mem_Ioc.2 i.2).2]
        · infer_instance
    · have : (1 : ((i : Ioc 0 k) → X i) → ℝ≥0∞) = fun _ ↦ 1 := rfl
      rw [this, lintegral_indicator_const ms, one_mul]

theorem kernel.map_map {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace T]
    (κ : kernel X Y) {f : Y → Z} (hf : Measurable f) {g : Z → T} (hg : Measurable g) :
    kernel.map (kernel.map κ f hf) g hg = kernel.map κ (g ∘ f) (hg.comp hf) := by
  ext1 x
  rw [kernel.map_apply, kernel.map_apply, Measure.map_map hg hf, ← kernel.map_apply]

theorem proj_family (x₀ : X 0) :
    IsProjectiveMeasureFamily (α := fun k : ℕ+ ↦ X k) (family κ x₀) := by
  intro S T hTS
  have : T.sup id ≤ S.sup id := Finset.sup_mono hTS
  simp only [family]
  rw [← kernel.map_apply, ← proj_kerNat _ _ this, Measure.map_map, kernel.map_map, kernel.map_apply]
  · rfl
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · exact PNat.pos _

noncomputable def updateSet {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) (s : Set ι)
    (y : (i : s) → α i) (i : ι) : α i := by
  classical
  exact if hi : i ∈ s then y ⟨i, hi⟩ else x i

theorem updateSet_empty {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) {s : Set ι} (hs : s = ∅)
    (y : (i : s) → α i) : updateSet x s y = x := by
  ext i
  simp [updateSet, hs]

theorem dependsOn_updateSet {ι β : Type*} {α : ι → Type*} {f : ((i : ι) → α i) → β} {s : Set ι}
    (hf : DependsOn f s) (t : Set ι) (y : (i : t) → α i) :
    DependsOn (fun x ↦ f (updateSet x t y)) (s \ t) := by
  refine fun x₁ x₂ h ↦ hf (fun i hi ↦ ?_)
  simp only [updateSet]
  split_ifs with h'
  · rfl
  · exact h i <| (mem_diff _).2 ⟨hi, h'⟩

theorem measurable_updateSet {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (x : (i : ι) → α i) (s : Set ι) :
    Measurable (updateSet x s) := by
  simp only [updateSet, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

abbrev pioc (a b : ℕ) := Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

abbrev fpioc (a b : ℕ) : Finset ℕ+ :=
  Finset.Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

theorem mem_ioc_of_mem_pioc {a b : ℕ} (i : pioc a b) : i.1.1 ∈ Ioc a b := by
  rcases mem_Ico.1 i.2 with ⟨h1, h2⟩
  simp only [mem_Ioc]
  rw [← PNat.coe_le_coe] at h1
  rw [← PNat.coe_lt_coe] at h2
  simp only [PNat.mk_coe] at h1 h2
  exact mem_Ioc.2 ⟨Nat.succ_le_iff.1 h1, Nat.lt_succ_iff.1 h2⟩

def ioc_eq {a b : ℕ} (i : pioc a b) : Ioc a b := ⟨i.1.1, mem_ioc_of_mem_pioc i⟩

def pioc_ioc {a b : ℕ} (z : (i : Ioc a b) → X i) (i : pioc a b) : X i := z (ioc_eq i)

theorem measurable_pioc_ioc (a b : ℕ) : Measurable (@pioc_ioc X a b) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

def ioc_fpioc {a b : ℕ} : ((i : Ioc a b) → X i) ≃ᵐ ((i : fpioc a b) → X i) where
  toFun := fun z i ↦ by
    have : i.1.1 ∈ Ioc a b := by
      have := i.2
      simp only [fpioc, Finset.mem_Ico] at this
      rw [← PNat.coe_le_coe, ← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe] at this
      exact mem_Ioc.2 ⟨Nat.succ_le.2 this.1, Nat.lt_succ.1 this.2⟩
    exact z ⟨i.1.1, this⟩
  invFun := fun z i ↦ by
    have := i.2
    simp only [Finset.mem_Ioc] at this
    have i_pos := Nat.zero_lt_of_lt this.1
    have : ⟨i.1, i_pos⟩ ∈ fpioc a b := by
      simp only [fpioc, Finset.mem_Ico]
      exact ⟨Nat.succ_le.2 this.1, Nat.lt_succ.2 this.2⟩
    exact z ⟨⟨i.1, i_pos⟩, this⟩
  left_inv := fun z ↦ by rfl
  right_inv := fun z ↦ by rfl
  measurable_toFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem mem_pioc {k : ℕ} (i : Iic k) (hi : ¬i.1 = 0) :
    ⟨i.1, i.1.pos_of_ne_zero hi⟩ ∈ pioc 0 k := by
  simp [pioc]
  rw [← PNat.coe_le_coe]
  rcases mem_Iic.1 i.2 with h
  exact ⟨Nat.one_le_iff_ne_zero.2 hi, Nat.lt_succ.2 h⟩

def fus {k : ℕ} (x₀ : X 0) (y : (i : pioc 0 k) → X i) (i : Iic k) : X i :=
  if hi : i.1 = 0 then hi ▸ x₀ else y ⟨⟨i.1, i.1.pos_of_ne_zero hi⟩, mem_pioc i hi⟩

theorem measurable_fus (k : ℕ) (x₀ : X 0) : Measurable (fus (k := k) x₀) := by
  simp only [fus, measurable_pi_iff]
  intro i
  by_cases h : i.1 = 0 <;> simp [h, measurable_pi_apply]

noncomputable def kerint (k N : ℕ) (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0)
    (x : (i : ℕ+) → X i) : ℝ≥0∞ := by
  classical
  exact if k < N then ∫⁻ z : (i : Ioc k N) → X i,
    f (updateSet x _ (pioc_ioc z)) ∂(kerNat κ k N (fus x₀ (fun i ↦ x i.1)))
    else f x

theorem sup_fpioc {N : ℕ} (hN : 0 < N) : ((fpioc 0 N).sup id).1 = N := by
  simp only [fpioc, zero_add, PNat.mk_ofNat]
  conv_rhs => change ((↑) : ℕ+ → ℕ) (⟨N, hN⟩ : ℕ+)
  conv_lhs => change ((↑) : ℕ+ → ℕ) ((Finset.Ico 1 ⟨N + 1, N.succ_pos⟩).sup id)
  apply le_antisymm <;> rw [PNat.coe_le_coe]
  · apply Finset.sup_le
    simp only [Finset.mem_Ico, PNat.one_le, true_and, id_eq]
    intro b hb
    rw [← PNat.coe_lt_coe, PNat.mk_coe, Nat.lt_succ] at hb
    rwa [← PNat.coe_le_coe]
  · have : (⟨N, hN⟩ : ℕ+) = id ⟨N, hN⟩ := rfl
    rw [this]
    apply Finset.le_sup
    simp only [Finset.mem_Ico, Subtype.mk_lt_mk, lt_add_iff_pos_right, zero_lt_one, and_true]
    rw [← PNat.coe_le_coe]
    simp only [PNat.val_ofNat, PNat.mk_coe]
    omega

theorem fpioc_mem_ioc {N : ℕ} (hN : 0 < N) (i : fpioc 0 N) :
    i.1.1 ∈ Ioc 0 ((fpioc 0 N).sup id).1 := by
  rw [sup_fpioc hN]
  have := i.2
  simp only [fpioc, Nat.reduceAdd, PNat.mk_ofNat, zero_add, Finset.mem_Ico, PNat.one_le,
    true_and] at this
  simp only [fpioc, Nat.reduceAdd, PNat.mk_ofNat, mem_Ioc]
  constructor
  · exact i.1.pos
  · rw [← Nat.lt_succ]
    rw [← PNat.coe_lt_coe] at this
    simpa using this

theorem lint_eq {α β : Type _} [hα : MeasurableSpace α] [hβ : MeasurableSpace β] (h : α = β)
    (h' : HEq hα hβ) {f : β → ℝ≥0∞} (hf : Measurable f) (μ : Measure α) :
    ∫⁻ a : α, f (cast h a) ∂μ = ∫⁻ b : β, f b ∂μ.map (cast h) := by
  rw [lintegral_map]
  · exact hf
  · exact measurable_cast h h'

theorem lint_eq' {α β : Type _} [hα : MeasurableSpace α] (h : α = β)
    {f : α → ℝ≥0∞} (μ : Measure α) :
    ∫⁻ a : α, f a ∂μ = ∫⁻ a : α, f (cast h.symm (cast h a)) ∂μ := by
  apply lintegral_congr
  simp

theorem lint_eq'' {α β : Type _} [hα : MeasurableSpace α] [hβ : MeasurableSpace β] (h : α = β)
    (h' : HEq hα hβ) {f : α → ℝ≥0∞} (hf : Measurable f) (μ : Measure α) :
    ∫⁻ a : α, f a ∂μ = ∫⁻ b : β, f (cast h.symm b) ∂μ.map (cast h) := by
  rw [lint_eq', lint_eq _ h' (f := fun b : β ↦ f (cast h.symm b))]
  exact hf.comp <| measurable_cast h.symm h'.symm

theorem eq_pi' {a b : ℕ} (h : a = b) :
    ((i : Ioc 0 a) → X i) = ((i : Ioc 0 b) → X i) := by cases h; rfl

theorem eq_fpioc {N : ℕ} (hN : 0 < N) :
    ((i : Ioc 0 ((fpioc 0 N).sup id).1) → X i) = ((i : Ioc 0 N) → X i) :=
  eq_pi' <| sup_fpioc hN

theorem heq_meas (s t : Set ℕ) (h : s = t) :
    HEq (inferInstance : MeasurableSpace ((i : s) → X i))
    (inferInstance : MeasurableSpace ((i : t) → X i)) := by cases h; rfl

theorem heq_fpioc {N : ℕ} (hN : 0 < N) :
    HEq (inferInstance : MeasurableSpace ((i : Ioc 0 ((fpioc 0 N).sup id).1) → X i))
    (inferInstance : MeasurableSpace ((i : Ioc 0 N) → X i)) := by
  apply heq_meas
  rw [sup_fpioc hN]

theorem measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure ((i : Ioc 0 n) → X i)) :
    (μ a).map (cast (eq_pi' h)) = μ b := by
  subst h
  have : (cast (rfl : ((i : Ioc 0 a) → X i) = ((i : Ioc 0 a) → X i))) = id := by
    ext x
    simp
  rw [this, Measure.map_id]

theorem preimage_indicator {α β : Type*} (f : α → β) (s : Set β) (a : α) :
    (f ⁻¹' s).indicator 1 a = s.indicator (1 : β → ℝ≥0∞) (f a) := by
  simp only [indicator, mem_preimage, Pi.one_apply]
  by_cases h : f a ∈ s <;> simp [h]

lemma omg {s t : Set ℕ} {u : Set ℕ+} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : s) → X i) (i : u) (hi1 : i.1.1 ∈ s) (hi2 : i.1.1 ∈ t) :
    cast h' x ⟨i.1.1, hi2⟩ = x ⟨i.1.1, hi1⟩ := by
  subst h
  rfl

theorem indicator_eq_indicator {α : Type*} (s t : Set α) {a b : α} (h : a ∈ s ↔ b ∈ t) :
    s.indicator (1 : α → ℝ≥0∞) a = t.indicator 1 b := by
  by_cases h' : a ∈ s
  · simp [indicator, h', h.1 h']
  · simp [indicator, h', h.not.1 h']

theorem kolContent_eq_kerint {N : ℕ} (hN : 0 < N) {S : Set ((i : fpioc 0 N) → X i)}
    (mS : MeasurableSet S)
    (x₀ : X 0) (x : (n : ℕ+) → X n) :
    kolContent (α := fun n : ℕ+ ↦ X n) (proj_family κ x₀) (cylinder (fpioc 0 N) S) =
    kerint κ 0 N ((cylinder _ S).indicator 1) x₀ x := by
  rw [kolContent_congr _ (by rw [mem_cylinders]; exact ⟨fpioc 0 N, S, mS, rfl⟩) rfl mS, family,
    Measure.map_apply _ mS, ← lintegral_indicator_one₀, kerint]
  · simp only [cast_eq, hN, ↓reduceIte]
    rw [lint_eq'' (eq_fpioc hN) (heq_fpioc hN)]
    congr
    · rw [measure_cast (sup_fpioc hN) (fun n ↦ kerNat κ 0 n (zer x₀))]
      congr
      ext i
      simp [zer, fus, mem_Iic_zero i.2]
    · ext z
      rw [preimage_indicator]
      apply indicator_eq_indicator
      congrm ?_ ∈ S
      ext i
      simp only [updateSet, pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and,
        pioc_ioc, Nat.reduceAdd, ioc_eq]
      have := i.2
      simp only [fpioc, Nat.reduceAdd, PNat.mk_ofNat, zero_add, Finset.mem_Ico, PNat.one_le,
        true_and] at this
      simp only [this, ↓reduceDite]
      have : Ioc 0 N = Ioc 0 ((fpioc 0 N).sup id).1 := by rw [sup_fpioc hN]
      rw [← omg _ (eq_fpioc hN).symm z i]; rfl
      rw [sup_fpioc hN]
    · exact (measurable_indicator_const_iff 1).2 <|
        measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) mS
  · apply MeasurableSet.nullMeasurableSet
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) mS
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem kerint_mono (k N : ℕ) {f g : ((n : ℕ+) → X n) → ℝ≥0∞} (hfg : f ≤ g) (x₀ : X 0)
    (x : (n : ℕ+) → X n) : kerint κ k N f x₀ x ≤ kerint κ k N g x₀ x := by
  simp only [kerint]
  split_ifs
  · exact lintegral_mono fun _ ↦ hfg _
  · exact hfg _

theorem measurable_kerint (k N : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : Measurable f) (x₀ : X 0) :
    Measurable (kerint κ k N f x₀) := by
  unfold kerint
  split_ifs with h
  · let g : ((i : Ioc k N) → X i) × ((n : ℕ+) → X n) → ℝ≥0∞ :=
      fun c ↦ f (updateSet c.2 _ (pioc_ioc c.1))
    let η : kernel ((n : ℕ+) → X n) ((i : Ioc k N) → X i) :=
      { val := fun x ↦ kerNat κ k N (fus x₀ (fun i ↦ x i.1))
        property := (kernel.measurable _).comp <| (measurable_fus _ _).comp <|
          measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) }
    change Measurable fun x ↦ ∫⁻ z : (i : Ioc k N) → X i, g (z, x) ∂η x
    have := isMarkovKernel_kerNat κ h
    have : IsMarkovKernel η := by
      constructor; exact fun x ↦ this.isProbabilityMeasure _
    apply Measurable.lintegral_kernel_prod_left'
    apply hf.comp
    simp only [updateSet, measurable_pi_iff]
    intro i
    by_cases h : i ∈ pioc k N <;> simp [h]
    · exact (measurable_pi_apply _).comp measurable_fst
    · exact measurable_snd.eval
  · exact hf

theorem dependsOn_kerint (k N : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : DependsOn f (pioc 0 N))
    (x₀ : X 0) : DependsOn (kerint κ k N f x₀) (pioc 0 k) := by
  intro x y hxy
  simp_rw [kerint]
  split_ifs with h
  · congrm ∫⁻ z : _, ?_ ∂(kerNat κ k N ?_)
    · ext i
      simp only [fus]
      split_ifs with h'
      · rfl
      · apply hxy
        simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and]
        rw [← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe, Nat.lt_succ]
        exact i.2
    · refine hf fun i hi ↦ ?_
      simp only [updateSet, pioc, mem_Ico, pioc_ioc, ioc_eq]
      split_ifs with h
      · rfl
      · push_neg at h
        have : i < k + 1 := by
          by_contra!
          rw [← PNat.coe_le_coe, PNat.mk_coe] at h
          simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hi
          exact h this hi
        simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hxy
        apply hxy
        rwa [← PNat.coe_lt_coe]
  · apply hf
    intro i hi
    simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hi
    apply hxy
    simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and]
    rw [← PNat.coe_lt_coe] at hi ⊢
    rw [not_lt] at h
    exact lt_of_lt_of_le hi (Nat.succ_le_succ_iff.2 h)


theorem kerint_self {k N : ℕ} (hkN : ¬k < N)
    (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0) :
    kerint κ k N f x₀ = f := by
  ext x
  rw [kerint, if_neg hkN]

theorem dependsOn_kerint' (k N K : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : DependsOn f (pioc 0 N))
    (hNk : N ≤ k) (x₀ : X 0) : kerint κ k K f x₀ = f := by
  ext x
  simp only [kerint]
  split_ifs with hkK
  · have := isMarkovKernel_kerNat κ hkK
    rw [← mul_one (f x),
      ← measure_univ (μ := (kerNat κ k K) (fus x₀ (fun i ↦ x i.1))),
      ← lintegral_const]
    refine lintegral_congr fun y ↦ hf fun i hi ↦ ?_
    simp only [updateSet, pioc, mem_Ico, pioc_ioc, ioc_eq, dite_eq_right_iff]
    rintro ⟨h1, h2⟩
    simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hi
    rw [← PNat.coe_lt_coe, PNat.mk_coe] at hi
    rw [← PNat.coe_le_coe, PNat.mk_coe] at h1
    omega
  · rfl

theorem updateSet_eq {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) {s : Set ι}
    (y : (i : s) → α i) : y = (fun i : s ↦ updateSet x s y i) := by
  ext i
  simp [updateSet, i.2]

theorem kerint_eq {a b : ℕ} (hab : a + 1 < b) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : Measurable f)
    (x₀ : X 0) :
    kerint κ a b f x₀ = kerint κ a (a + 1) (kerint κ (a + 1) b f x₀) x₀ := by
  ext x
  simp [kerint, lt_trans a.lt_succ_self hab, hab]
  rw [kerNat_succ_left κ _ _ hab, compProd_eq _ _ (Nat.lt_succ_self _) hab,
    kernel.map_apply,
    lintegral_map (f := fun z ↦ f (updateSet x (pioc a b) (pioc_ioc z))) _ (er ..).measurable,
    kernel.lintegral_compProd]
  congrm ∫⁻ _ : ?_, ∫⁻ _ : ?_, f fun i ↦ ?_ ∂(?_) ∂(?_)
  · rfl
  · rfl
  · rw [split_eq_comap, kernel.comap_apply]
    congr
    ext i
    simp only [Nat.succ_eq_add_one, el, pioc, Nat.reduceAdd, PNat.mk_ofNat, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, fus, updateSet, mem_Ico, pioc_ioc, PNat.mk_coe]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · rw [← PNat.coe_le_coe, PNat.mk_coe, PNat.mk_coe] at *
      omega
    · rfl
    · omega
    · rfl
    · push_neg at h5
      rw [← PNat.coe_le_coe, ← PNat.coe_le_coe, PNat.mk_coe, PNat.mk_coe, PNat.mk_coe] at h5
      have hi := mem_Iic.1 i.2
      omega
  · rfl
  · simp only [er, updateSet, pioc, mem_Ico, pioc_ioc, Nat.succ_eq_add_one, ioc_eq,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
      rw [← PNat.coe_le_coe, ← PNat.coe_lt_coe, PNat.mk_coe] at *
    · exfalso; linarith [le_trans h3.1 h2]
    · push_neg at h3 h4
      exfalso; linarith [h3 (h4 h1.1), h1.2]
    · rw [PNat.mk_coe, Nat.lt_succ] at h6
      exact (h2 h6.2).elim
    · push_neg at h5 h6
      rw [PNat.mk_coe] at h6
      exfalso; linarith [h1.2, h5 (h6 h1.1)]
    · push_neg at h1
      exfalso; linarith [h7.2, h1 (le_trans (a + 1).le_succ h7.1)]
    · push_neg at h1 h7
      have := Nat.eq_of_le_of_lt_succ h8.1 h8.2
      rw [this, PNat.mk_coe] at h1
      exfalso; linarith [h1 (le_refl _)]
  · exact hf.comp <| (measurable_updateSet _ _).comp <| (measurable_pioc_ioc _ _).comp
      (er ..).measurable
  · exact hf.comp <| (measurable_updateSet _ _).comp <| measurable_pioc_ioc ..

theorem kerint_eq' {a b : ℕ} (hab : a < b) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : Measurable f)
    (x₀ : X 0) :
    kerint κ a (b + 1) f x₀ = kerint κ a b (kerint κ b (b + 1) f x₀) x₀ := by
  ext x
  simp [kerint, hab, hab.trans b.lt_succ_self]
  rw [kerNat_succ_right κ _ _ hab, compProd_eq _ _ hab b.lt_succ_self,
    kernel.map_apply,
    lintegral_map (f := fun z ↦ f (updateSet x (pioc a (b + 1)) (pioc_ioc z))) _ (er ..).measurable,
    kernel.lintegral_compProd]
  congrm ∫⁻ _ : ?_, ∫⁻ _ : ?_, f fun i ↦ ?_ ∂(?_) ∂(?_)
  · rfl
  · rfl
  · rw [split_eq_comap, kernel.comap_apply]
    congr
    ext i
    simp only [Nat.succ_eq_add_one, el, pioc, Nat.reduceAdd, PNat.mk_ofNat, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, fus, updateSet, mem_Ico, pioc_ioc, PNat.mk_coe]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · rw [← PNat.coe_le_coe, PNat.mk_coe, PNat.mk_coe] at *
      omega
    · rfl
    · omega
    · rfl
    · push_neg at h5
      rw [← PNat.coe_le_coe, ← PNat.coe_le_coe, PNat.mk_coe, PNat.mk_coe, PNat.mk_coe] at h5
      have hi := mem_Iic.1 i.2
      omega
  · rfl
  · simp only [er, updateSet, pioc, mem_Ico, pioc_ioc, Nat.succ_eq_add_one, ioc_eq,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
      rw [← PNat.coe_le_coe, ← PNat.coe_lt_coe, PNat.mk_coe] at *
    · exfalso; linarith [le_trans h3.1 h2]
    · push_neg at h3 h4
      exfalso; linarith [h3 (h4 h1.1), h1.2]
    · rw [PNat.mk_coe, Nat.lt_succ] at h6
      exact (h2 h6.2).elim
    · push_neg at h5 h6
      rw [PNat.mk_coe] at h6
      exfalso; linarith [h1.2, h5 (h6 h1.1)]
    · push_neg at h1
      exfalso; linarith [h7.2, h1 (le_trans (Nat.succ_lt_succ hab).le h7.1)]
    · push_neg at h1
      rw [PNat.mk_coe] at h1 h8
      exfalso; linarith [h8.2, h1 h8.1]
  · exact hf.comp <| (measurable_updateSet _ _).comp <| (measurable_pioc_ioc _ _).comp
      (er ..).measurable
  · exact hf.comp <| (measurable_updateSet _ _).comp <| measurable_pioc_ioc ..


theorem auxiliaire {f : ℕ → ((n : ℕ+) → X n) → ℝ≥0∞} {N : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (pioc 0 (N n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    {x₀ : X 0}
    (anti : ∀ x, Antitone (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x))
    {l : ((n : ℕ+) → X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : (n : pioc 0 k) → X n)
    (hpos : ∀ x, ∀ n, ε ≤ kerint κ k (N n) (f n) x₀ (updateSet x _ y)) :
    ∃ z, ∀ x n,
    ε ≤ kerint κ (k + 1) (N n) (f n) x₀ (Function.update (updateSet x _ y) k.succPNat z) := by
  -- Shorter name for integrating over all the variables except the first `k + 1`.
  let F : ℕ → ((n : ℕ+) → X n) → ℝ≥0∞ := fun n ↦ kerint κ (k + 1) (N n) (f n) x₀
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` over all the variables except the first `k` is the same as integrating
  -- `Fₙ` over the `k`-th variable.
  have f_eq x n : kerint κ k (N n) (f n) x₀ x = kerint κ k (k + 1) (F n) x₀ x := by
    simp only [F]
    rcases lt_trichotomy (k + 1) (N n) with h | h' | h'
    · rw [kerint_eq κ h (mf n)]
    · rw [← h']
      congr
      ext x
      rw [kerint_self κ (by simp)]
    · have : N n ≤ k := Nat.lt_succ.1 h'
      rw [kerint_self _ (not_lt.2 this), dependsOn_kerint' _ _ _ _ (hcte n) (this.trans k.le_succ),
        dependsOn_kerint' _ _ _ _ (hcte n) this]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simp only [F, kerint]
    split_ifs with h
    · have : IsMarkovKernel (kerNat κ (k + 1) (N n)) := isMarkovKernel_kerNat κ h
      rw [← mul_one bound,
        ← measure_univ (μ := (kerNat κ (k + 1) (N n)) (fus x₀ (fun i ↦ x i.1))),
        ← lintegral_const]
      exact lintegral_mono fun _ ↦ le_bound _ _
    · exact le_bound _ _
  -- By dominated convergence, the integral of `fₙ` with respect to all the variable except
  -- the `k` first converges to the integral of `l`.
  have tendsto_int x : Tendsto (fun n ↦ kerint κ k (N n) (f n) x₀ x) atTop
      (𝓝 (kerint κ k (k + 1) l x₀ x)) := by
    simp_rw [f_eq, kerint, if_pos k.lt_succ_self]
    · refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
        (fun n ↦ (measurable_kerint _ _ _ (mf n) _).comp <|
          (measurable_updateSet _ _).comp <| measurable_pioc_ioc ..)
        (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
        ?_ (eventually_of_forall (fun _ ↦ tendstoF _))
      have := isMarkovKernel_kerNat κ k.lt_succ_self
      simp [fin_bound]
  -- By hypothesis, we have `ε ≤ ∫ F(y, xₖ) ∂μₖ`, so this is also true for `l`.
  have ε_le_lint x : ε ≤ kerint κ k (k + 1) l x₀ (updateSet x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ+) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (updateSet x_ _ y) k.succPNat x') := by
    have aux : ∫⁻ (a : (i : Ioc k (k + 1)) → X i),
        l (updateSet (updateSet x_ _ y) _ (pioc_ioc a)) ∂(κ k (fus x₀ y)) ≠ ⊤ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := κ k (fus x₀ y)), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    refine ⟨x' ⟨k + 1, right_mem_Ioc.2 <| Nat.lt_succ_self _⟩, ?_⟩
    calc
      ε ≤ ∫⁻ (z : (i : Ioc k (k + 1)) → X i),
          l (updateSet (updateSet x_ _ y) _ (pioc_ioc z)) ∂(κ k (fus x₀ y)) := by
          rw [← kerNat_succ κ k]
          nth_rw 1 [updateSet_eq x_ y]
          simp only [kerint, k.lt_succ_self, ↓reduceIte] at ε_le_lint
          exact ε_le_lint _
      _ ≤ l (updateSet (updateSet x_ _ y) _ (pioc_ioc x')) := hx'
      _ = l (Function.update (updateSet x_ _ y) k.succPNat (x' ⟨k + 1, _⟩)) := by
          congr
          ext i
          simp only [updateSet, pioc, mem_Ico, pioc_ioc, ioc_eq, zero_add, PNat.mk_ofNat,
            PNat.one_le, true_and, Nat.reduceAdd, Function.update]
          split_ifs with h1 h2 h3 h4 h5 h6
          · cases h2; rfl
          · exfalso; linarith [(PNat.coe_le_coe _ _).2 h1.1, (PNat.coe_lt_coe _ _).2 h3]
          · have : i.1 = k + 1 :=
              Nat.eq_of_le_of_lt_succ ((PNat.coe_le_coe _ _).2 h1.1) ((PNat.coe_lt_coe _ _).2 h1.2)
            exact (PNat.coe_inj.ne.2 h2 this).elim
          · rw [h5] at h4
            have := (PNat.coe_lt_coe _ _).2 h4
            simp at this
          · rfl
          · push_neg at h1
            rw [← PNat.coe_lt_coe, Nat.not_lt, h6] at h1
            simp [← PNat.coe_lt_coe] at h1
          · rfl
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine dependsOn_kerint _ _ _ (hcte n) _ fun i hi ↦ ?_
  simp only [Function.update, updateSet, pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le,
    true_and, Nat.reduceAdd]
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hi
    rw [← PNat.coe_lt_coe] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | b
    · rw [← PNat.coe_lt_coe] at h2
      exact (h2 a).elim
    · rw [← PNat.coe_inj] at h1
      exact (h1 b).elim

-- (fun (f : ((n : fpioc 0 (t.sup id)) → X n)) (k : t) ↦
--       f ⟨k.1, Finset.mem_Icc.2 ⟨Nat.zero_le k.1, Finset.le_sup (f := id) k.2⟩⟩) ⁻¹' S

theorem cylinders_pnat :
    cylinders (fun n : ℕ+ ↦ X n) = ⋃ (N) (_ : 0 < N) (S) (_ : MeasurableSet S),
    {cylinder (fpioc 0 N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨t, S, mS, rfl⟩
    refine ⟨(t.sup id).1, (t.sup id).pos, (fun (f : (n : fpioc 0 (t.sup id).1) → X n) (k : t) ↦
      f ⟨k.1, ?_⟩) ⁻¹' S, ?_, ?_⟩
    · simp only [fpioc, zero_add, PNat.mk_ofNat, Finset.mem_Ico]
      refine ⟨PNat.one_le _, ?_⟩
      have := Finset.le_sup (f := id) k.2
      rw [← PNat.coe_lt_coe]
      simp at this ⊢
      rw [← PNat.coe_le_coe] at this
      exact Nat.lt_succ_iff.2 this
    · exact mS.preimage <| measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
    · dsimp only [cylinder]
      rw [← preimage_comp]
      rfl
  · rintro ⟨N, -, S, mS, rfl⟩
    exact ⟨fpioc 0 N, S, mS, rfl⟩

def key (ind : (k : ℕ) → ((n : pioc 0 k) → X n) → X k.succPNat) : (k : ℕ+) → X k := fun k ↦ by
  use cast (congrArg (fun k : ℕ+ ↦ X k) k.succPNat_natPred) (ind k.natPred (fun i ↦ key ind i.1))
  termination_by k => k
  decreasing_by
  have := i.2
  simp [pioc] at this
  exact this.2

theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
    (S : Set ((i : I) → α i)) :
    DependsOn ((cylinder I S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) I := by
  intro x y hxy
  have : x ∈ cylinder I S ↔ y ∈ cylinder I S := by simp [hxy]
  by_cases h : x ∈ cylinder I S
  · simp [h, this.1 h]
  · simp [h, this.not.1 h]

/-- This is the key theorem to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by $\mathbb{N}$. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem firstLemma (A : ℕ → Set ((n : ℕ+) → X n)) (A_mem : ∀ n, A n ∈ cylinders _)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) (x₀ : X 0) :
    Tendsto (fun n ↦ kolContent (proj_family κ x₀) (A n)) atTop (𝓝 0) := by
  -- `Aₙ` is a cylinder, it can be written `cylinder sₙ Sₙ`.
  have A_cyl n : ∃ N S, 0 < N ∧ MeasurableSet S ∧ A n = cylinder (fpioc 0 N) S := by
    simpa [cylinders_pnat] using A_mem n
  choose N S hN mS A_eq using A_cyl
  set proj := proj_family κ x₀
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : ((n : ℕ+) → X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (pioc 0 (N n)) := by
    simp_rw [χ, A_eq]
    rw [pioc, ← Finset.coe_Ico]
    exact dependsOn_cylinder_indicator _
  -- Therefore its integral is constant.
  have lma_const x y n : kerint κ 0 (N n) (χ n) x₀ x = kerint κ 0 (N n) (χ n) x₀ y := by
    apply dependsOn_empty
    convert dependsOn_kerint κ 0 (N n) (χ_dep n) x₀
    simp [pioc]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := by
    intro m n hmn y
    apply indicator_le
    exact fun a ha ↦ by simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` over all the variables except the first
  -- `k` ones is non-increasing.
  have lma_inv k M n (h : N n ≤ M) :
      kerint κ k M (χ n) x₀ = kerint κ k (N n) (χ n) x₀ := by
    refine Nat.le_induction rfl ?_ M h
    intro K hK heq
    rw [← heq]
    ext x
    rcases lt_trichotomy k K with hkK | hkK | hkK
    · rw [kerint_eq' κ hkK (mχ n), dependsOn_kerint' _ _ _ _ (χ_dep n) hK]
    · rw [hkK, dependsOn_kerint' _ _ _ _ (χ_dep n) hK, dependsOn_kerint' _ _ _ _ (χ_dep n) hK]
    · rw [kerint_self _ (not_lt.2 <| Nat.succ_le.2 hkK), kerint_self _ (not_lt.2 hkK.le)]
  -- the integral of `χₙ` over all the variables except the first `k` ones is non-increasing.
  have anti_lma k x : Antitone fun n ↦ kerint κ k (N n) (χ n) x₀ x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    exact kerint_mono _ _ _ (χ_anti hmn) _ _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l, Tendsto (fun n ↦ kerint κ k (N n) (χ n) x₀ x) atTop (𝓝 l) := by
    rcases tendsto_of_antitone <| anti_lma k x with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `l₀` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l 0 x = l 0 y := by
    have := hl 0 x
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl 0 _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l 0 x = ε := ⟨l 0 Classical.ofNonempty, fun x ↦ l_const ..⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ kerint κ 0 (N n) (χ n) x₀ x :=
    hε x ▸ ((anti_lma 0 _).le_of_tendsto (hl 0 _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply àuxiliaire. This allows us to recursively
  -- build a sequence `(zₙ)` with the following crucial property: for any `k` and `n`,
  -- `ε ≤ ∫ χₙ(z₀, ..., z_{k-1}) ∂(μₖ ⊗ ... ⊗ μ_{Nₙ})`.
  choose! ind hind using
    fun k y h ↦ auxiliaire κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞) χ_le (anti_lma (k + 1))
      (hl (k + 1)) ε y h
  let z := key ind
  have crucial : ∀ k x n, ε ≤ kerint κ k (N n) (χ n) x₀ (updateSet x (pioc 0 k) (fun i ↦ z i)) := by
    intro k
    induction k with
    | zero =>
      intro x n
      rw [pioc, Ico_self, updateSet_empty (hs := rfl)]
      exact hpos x n
    | succ m hm =>
      intro x n
      have : updateSet x (pioc 0 (m + 1)) (fun i ↦ z i) =
          Function.update (updateSet x (pioc 0 m) (fun i ↦ z i))
          ⟨m + 1, m.succ_pos⟩ (z ⟨m + 1, _⟩) := by
        ext i
        simp only [updateSet, pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and,
          Nat.reduceAdd, dite_eq_ite, Function.update]
        split_ifs with h1 h2 h3 h4 h5
        · cases h2; rfl
        · rfl
        · rw [← PNat.coe_lt_coe] at h1 h3
          rw [← PNat.coe_inj] at h2
          exact (not_or.2 ⟨h3, h2⟩ <| Nat.lt_succ_iff_lt_or_eq.1 h1).elim
        · rw [h4, ← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe] at h1
          exfalso; linarith
        · rw [← PNat.coe_lt_coe, PNat.mk_coe] at h1 h5
          exfalso; linarith
        · rfl
      rw [this]
      convert hind m (fun i ↦ z i.1) hm x n
  -- We now want to prove that the integral of `χₙ` converges to `0`.
  have concl x n : kolContent proj (A n) = kerint κ 0 (N n) (χ n) x₀ x := by
    simp_rw [χ, A_eq]
    have : (fun s ↦ (kolContent proj).toFun s) = (kolContent proj).toFun := rfl
    rw [← this, kolContent_eq_kerint _ (hN n) (mS n) x₀ x]
  simp_rw [concl Classical.ofNonempty]
  convert hl 0 Classical.ofNonempty
  rw [hε]
  by_contra!
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > Nₙ` we get `ε ≤ χₙ(z₀, ..., z_{Nₙ})` and therefore `(z n) ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  have ε_pos : 0 < ε := this.symm.bot_lt
  have incr : ∀ n, z ∈ A n := by
    intro n
    have : χ n z = kerint κ (N n) (N n) (χ n) x₀
        (updateSet z (pioc 0 (N n)) (fun i ↦ z i)) := by
      rw [kerint]
      simp only [lt_self_iff_false, ↓reduceIte]
      congr
      ext i
      simp [updateSet, pioc]
    have : 0 < χ n (z) := by
      rw [this]
      exact lt_of_lt_of_le ε_pos (crucial (N n) z n)
    exact mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ mem_iInter.2 incr).elim

theorem kolContent_sigma_subadditive_proj (x₀ : X 0) ⦃f : ℕ → Set ((n : ℕ+) → X n)⦄
    (hf : ∀ n, f n ∈ cylinders (fun n : ℕ+ ↦ X n))
    (hf_Union : (⋃ n, f n) ∈ cylinders (fun n : ℕ+ ↦ X n)) :
    kolContent (proj_family κ x₀) (⋃ n, f n) ≤
    ∑' n, kolContent (proj_family κ x₀) (f n) := by
  classical
  refine (kolContent (proj_family κ x₀)).sigma_subadditive_of_sigma_additive
    setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
    (kolContent (proj_family κ x₀)) (fun h ↦ ?_) ?_ hf hf_Union hf'
  · rename_i s
    obtain ⟨N, S, hN, mS, s_eq⟩ : ∃ N S, 0 < N ∧ MeasurableSet S ∧ s = cylinder (fpioc 0 N) S := by
      simpa [cylinders_pnat] using h
    let x_ : (n : ℕ+) → X n := Classical.ofNonempty
    rw [s_eq, kolContent_eq_kerint κ hN mS x₀ x_]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
    rw [kerint, if_pos hN]
    have : IsMarkovKernel (kerNat κ 0 N) := isMarkovKernel_kerNat κ hN
    nth_rw 2 [← mul_one 1, ← measure_univ (μ := kerNat κ 0 N (fus x₀ fun i ↦ x_ i.1))]
    rw [← lintegral_const]
    apply lintegral_mono
    apply Set.indicator_le
    simp
  · exact fun s hs anti_s inter_s ↦ firstLemma κ s hs anti_s inter_s x₀

noncomputable def ionescu_tulcea_fun (x₀ : X 0) : Measure ((n : ℕ+) → X n) := by
  exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (kolContent (proj_family κ x₀))
    (kolContent_sigma_subadditive_proj κ x₀)

theorem proba_ionescu (x₀ : X 0) : IsProbabilityMeasure (ionescu_tulcea_fun κ x₀) := by
  constructor
  rw [← cylinder_univ ∅, ionescu_tulcea_fun, Measure.ofAddContent_eq,
      fun x₀ ↦ kolContent_congr (proj_family κ x₀) _ rfl MeasurableSet.univ]
  · simp only [family]
    rw [← kernel.map_apply _ (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _))]
    have : IsMarkovKernel (kerNat κ 0 1) := isMarkovKernel_kerNat κ zero_lt_one
    simp
  · simp only [mem_cylinders, exists_prop, forall_const]
    exact ⟨∅, univ, MeasurableSet.univ, rfl⟩
  · simp only [mem_cylinders, exists_prop, forall_const]
    exact ⟨∅, univ, MeasurableSet.univ, rfl⟩


/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_ionescu_tulcea_fun (x₀ : X 0) :
    IsProjectiveLimit (ionescu_tulcea_fun κ x₀) (family κ x₀) := by
  intro I
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_proj
  have h_mem : (fun (x : (n : ℕ+) → X n.1) (i : I) ↦ x i) ⁻¹' s ∈
      cylinders (fun n : ℕ+ ↦ X n.1) := by
    rw [mem_cylinders]; exact ⟨I, s, hs, rfl⟩
  rw [ionescu_tulcea_fun, Measure.ofAddContent_eq,
    kolContent_congr (proj_family κ x₀)]
  · exact h_mem
  · rfl
  · exact hs
  · exact h_mem

theorem measurable_ionescu : Measurable (ionescu_tulcea_fun κ) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ↦ Measurable (fun x₀ ↦ ionescu_tulcea_fun κ x₀ t))
    (s := cylinders (fun n : ℕ+ ↦ X n))
    generateFrom_cylinders.symm
    isPiSystem_cylinders
    ?empty
    (fun t ht ↦ ?cylinder)
    (fun t mt ht ↦ ?compl)
    (fun f disf mf hf ↦ ?union)
  · simp_rw [measure_empty]
    exact measurable_const
  · obtain ⟨N, S, -, mS, t_eq⟩ : ∃ N S, 0 < N ∧ MeasurableSet S ∧ t = cylinder (fpioc 0 N) S := by
      simpa [cylinders_pnat] using ht
    simp_rw [ionescu_tulcea_fun, Measure.ofAddContent_eq _ _ _ _ ht,
      fun x₀ ↦ kolContent_congr (proj_family κ x₀) ht t_eq mS]
    simp only [family]
    refine Measure.measurable_measure.1 ?_ _ mS
    refine (Measure.measurable_map _ ?_).comp <| (kernel.measurable _).comp zer.measurable
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · have this x₀ : ionescu_tulcea_fun κ x₀ tᶜ = 1 - ionescu_tulcea_fun κ x₀ t := by
      have := fun x₀ ↦ proba_ionescu κ x₀
      rw [measure_compl mt (measure_ne_top _ _), measure_univ]
    simp_rw [this]
    exact Measurable.const_sub ht _
  · simp_rw [measure_iUnion disf mf]
    exact Measurable.ennreal_tsum hf

noncomputable def ionescu_tulcea_kernel : kernel (X 0) ((n : ℕ+) → X n) :=
  { val := ionescu_tulcea_fun κ
    property := measurable_ionescu κ }

instance : IsMarkovKernel (ionescu_tulcea_kernel κ) := IsMarkovKernel.mk fun _ ↦ proba_ionescu _ _

def er' (N : ℕ) : (X 0) × ((i : Ioc 0 N) → X i) ≃ᵐ ((i : Iic N) → X i) where
  toFun := fun p n ↦ if h : n.1 = 0 then h.symm ▸ p.1 else
    p.2 ⟨n.1, ⟨Nat.zero_lt_of_ne_zero h, n.2⟩⟩
  invFun := fun x ↦ ⟨x ⟨0, N.zero_le⟩, fun n ↦ x ⟨n.1, Ioc_subset_Iic_self n.2⟩⟩
  left_inv := fun p ↦ by
    ext i
    · simp
    · simp only
      split_ifs with h
      · simpa [h] using i.2
      · rfl
  right_inv := fun x ↦ by
    ext i
    simp only
    split_ifs with h
    · have : i = ⟨0, N.zero_le⟩ := by rwa [← Subtype.val_inj]
      cases this; rfl
    · rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun n ↦ ?_)
    by_cases h : n.1 = 0
    · simp only [Equiv.coe_fn_mk, h, ↓reduceDite]
      simp_rw [eqRec_eq_cast]
      exact (measurable_cast _ (by aesop)).comp measurable_fst
    · simp only [Equiv.coe_fn_mk, h, ↓reduceDite]
      exact (measurable_pi_apply _).comp measurable_snd
  measurable_invFun := (measurable_pi_apply _).prod_mk <|
    measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

def er'' :
    (X 0) × ((n : ℕ+) → X n) ≃ᵐ ((n : ℕ) → X n) where
  toFun := fun p n ↦ if h : n = 0 then h ▸ p.1 else p.2 ⟨n, Nat.zero_lt_of_ne_zero h⟩
  invFun := fun x ↦ ⟨x 0, fun n ↦ x n⟩
  left_inv := fun p ↦ by
    simp only [↓reduceDite, PNat.ne_zero]
    rfl
  right_inv := fun p ↦ by
    simp only [PNat.mk_coe]
    ext n
    split_ifs with h
    · cases h; rfl
    · rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun n ↦ ?_)
    by_cases h : n = 0
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      simp_rw [eqRec_eq_cast]
      exact (measurable_cast _ (by cases h; rfl)).comp measurable_fst
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := (measurable_pi_apply _).prod_mk <|
    measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem proj_zero_er''_eq : (fun x ↦ x 0) ∘ (er'' (X := X)) = Prod.fst := by
    ext x
    simp [er'']

noncomputable def ionescu_ker : kernel (X 0) ((n : ℕ) → X n) :=
  kernel.map
    ((kernel.deterministic id measurable_id) ×ₖ (ionescu_tulcea_kernel κ))
    er'' er''.measurable

theorem ionescu_ker_proj_zero :
    kernel.map (ionescu_ker κ) (fun x ↦ x 0) (measurable_pi_apply _) =
    kernel.deterministic id measurable_id := by
  rw [ionescu_ker, kernel.map_map]
  conv_lhs => enter [2]; rw [proj_zero_er''_eq]
  exact kernel.fst_prod _ _

noncomputable def my_ker (N : ℕ) :
    kernel (X 0) ((i : Iic N) → X i) := by
  cases N with
  | zero =>
    exact kernel.map (kernel.deterministic id measurable_id) zer zer.measurable_toFun
  | succ n =>
    exact kernel.map ((kernel.deterministic id measurable_id) ×ₖ
        (kernel.comap (kerNat κ 0 (n + 1)) zer zer.measurable_toFun))
      (er' (n + 1)) (er' (n + 1)).measurable

theorem my_ker_zero : my_ker κ 0 =
    kernel.map (kernel.deterministic id measurable_id) zer zer.measurable := rfl

theorem my_ker_pos {N : ℕ} (hN : 0 < N) :
    my_ker κ N = kernel.map ((kernel.deterministic id measurable_id) ×ₖ
        (kernel.comap (kerNat κ 0 N) zer zer.measurable_toFun))
      (er' N) (er' N).measurable := by
  rw [← N.succ_pred (ne_of_lt hN).symm]
  rfl

theorem Measure.map_prod {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace T] (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] {f : X → Z} (hf : Measurable f)
    {g : Y → T} (hg : Measurable g) :
    (μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g) := by
  refine (Measure.prod_eq fun s t ms mt ↦ ?_).symm
  rw [Measure.map_apply (hf.prod_map hg) (ms.prod mt)]
  · have : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) := prod_preimage_eq.symm
    rw [this, Measure.prod_prod, Measure.map_apply hf ms, Measure.map_apply hg mt]

theorem kernel.map_prod {X Y Z T U : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace U]
    (κ : kernel X Y) [IsFiniteKernel κ] (η : kernel X T) [IsFiniteKernel η]
    {f : Y → Z} (hf : Measurable f) {g : T → U} (hg : Measurable g) :
    kernel.map (κ ×ₖ η) (Prod.map f g) (hf.prod_map hg) =
    (kernel.map κ f hf) ×ₖ (kernel.map η g hg) := by
  ext1 x
  rw [kernel.map_apply, kernel.prod_apply, Measure.map_prod _ _ hf hg, kernel.prod_apply,
    kernel.map_apply, kernel.map_apply]

theorem ionescu_tulcea_kernel_apply (x₀ : X 0) :
    ionescu_tulcea_kernel κ x₀ = ionescu_tulcea_fun κ x₀ := by
  rw [ionescu_tulcea_kernel]
  rfl

lemma omg' {s t : Set ℕ} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : s) → X i) (i : s) (hi : i.1 ∈ t) :
    cast h' x ⟨i.1, hi⟩ = x i := by
  subst h
  rfl

theorem ionescu_ker_proj (N : ℕ) :
    kernel.map (ionescu_ker κ) (fun x (i : Iic N) ↦ x i) (measurable_proj _) = my_ker κ N := by
  rcases eq_zero_or_pos N with hN | hN
  · cases hN
    rw [my_ker_zero]
    have : (fun (x : (n : ℕ) → X n) (i : Iic 0) ↦ x i) = zer ∘ (fun x ↦ x 0) := by
      ext x i
      simp only [zer, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]
      have : ⟨0, mem_Iic.2 <| le_refl 0⟩ = i := by
        rw [← Subtype.coe_inj]
        exact (mem_Iic_zero i.2).symm
      cases this; rfl
    conv_lhs => enter [2]; rw [this]
    rw [← kernel.map_map _ (measurable_pi_apply _) zer.measurable, ionescu_ker_proj_zero]
  · rw [ionescu_ker, kernel.map_map, my_ker_pos _ hN]
    have : (fun (x : (n : ℕ) → X n) (i : Iic N) ↦ x i) ∘ er'' = (er' N) ∘
        (Prod.map id (fun x (i : Ioc 0 N) ↦ x ⟨i.1, (mem_Ioc.1 i.2).1⟩)) := by
      ext x i
      simp only [er', MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er'', MeasurableEquiv.symm_mk,
        Equiv.coe_fn_symm_mk, Function.comp_apply, Prod_map, id_eq, PNat.mk_coe]
    conv_lhs => enter [2]; rw [this]
    rw [← kernel.map_map, my_ker_pos _ hN]
    · congr
      rw [kernel.map_prod, kernel.map_id]
      · congr
        ext1 x₀
        rw [kernel.map_apply, ionescu_tulcea_kernel_apply,
          ← Function.id_comp
            (fun (x : (n : ℕ+) → X n) (i : Ioc 0 N) ↦ x ⟨i.1, (mem_Ioc.1 i.2).1⟩),
          ← (@ioc_fpioc _ _ 0 N).symm_comp_self, Function.comp.assoc, ← Measure.map_map]
        · have : ⇑ioc_fpioc ∘ (fun (x : (n : ℕ+) → X n) (i : Ioc 0 N) ↦
              x ⟨i.1, (mem_Ioc.1 i.2).1⟩) =
              fun (x : (n : ℕ+) → X n) (i : fpioc 0 N) ↦ x i := by ext; rfl
          rw [this, isProjectiveLimit_ionescu_tulcea_fun, family,
            ← measure_cast (sup_fpioc hN).symm (fun n ↦ kerNat κ 0 n (zer x₀)),
            Measure.map_map, Measure.map_map]
          · convert kernel.comap_apply (kerNat κ 0 N) zer.measurable_toFun x₀
            rw [kernel.comap_apply]
            nth_rw 2 [← kernel.map_id (kerNat κ 0 N)]
            rw [kernel.map_apply]
            congr
            ext x i
            simp only [ioc_fpioc, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
              Equiv.coe_fn_symm_mk, Function.comp_apply, PNat.mk_coe, id_eq]
            apply omg'
            rw [sup_fpioc hN]
          · apply ioc_fpioc.measurable_invFun.comp
            exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
          · apply measurable_cast
            apply heq_meas
            rw [sup_fpioc hN]
          · exact ioc_fpioc.measurable_invFun
          · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
        · exact ioc_fpioc.measurable_invFun
        · exact ioc_fpioc.measurable_toFun.comp <|
            measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
        · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
    · exact (er' N).measurable_toFun

theorem integral_dep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (x₀ : X 0) {f : ((i : Iic N) → X i) → E} (hf : AEStronglyMeasurable f (my_ker κ N x₀)) :
    ∫ y, f ((fun x (i : Iic N) ↦ x i) y) ∂ionescu_ker κ x₀ =
    ∫ y, f y ∂my_ker κ N x₀ := by
  rw [← ionescu_ker_proj, kernel.map_apply, integral_map]
  · exact (measurable_proj _).aemeasurable
  · rw [← kernel.map_apply, ionescu_ker_proj]
    exact hf





def e (n : ℕ) : (X (n + 1)) ≃ᵐ ((i : Ioc n (n + 1)) → X i) where
  toFun := fun x i ↦ by
    have : n + 1 = i.1 := by
      have := i.2
      simp at this
      linarith
    exact this ▸ x
  invFun := fun x ↦ x ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩ = i := by
      have := i.2
      simp at this
      rw [← Subtype.coe_inj]
      linarith
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩ = i := by
      have := i.2
      simp at this
      rw [← Subtype.coe_inj]
      linarith
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

variable (κ : (n : ℕ) → kernel ((i : Iic n) → X i) (X (n + 1)))
variable [∀ n, IsMarkovKernel (κ n)]

noncomputable def noyau : kernel (X 0) ((n : ℕ) → X n) :=
  ionescu_ker (fun n ↦ kernel.map (κ n) (e n) (e n).measurable_toFun)

instance : IsMarkovKernel (noyau κ) := by
  apply kernel.IsMarkovKernel.map
  exact er''.measurable

noncomputable def noyau_partiel (N : ℕ) : kernel (X 0) ((i : Iic N) → X i) :=
  my_ker (fun n ↦ kernel.map (κ n) (e n) (e n).measurable_toFun) N

theorem noyau_proj (N : ℕ) :
    kernel.map (noyau κ) (fun x (i : Iic N) ↦ x i) (measurable_proj _) =
    noyau_partiel κ N := ionescu_ker_proj _ _

variable (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

noncomputable def prod_meas : Measure ((n : ℕ) → X n) :=
  Measure.snd ((μ 0) ⊗ₘ (noyau (fun n ↦ kernel.const _ (μ (n + 1)))))

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
  rw [h1, h2, Finset.prod_set_coe, Finset.prod_set_coe]
  have this (a b : ℕ) : (Ioc a b).toFinset = Finset.Ioc a b := by simp
  rw [Finset.prod_congr (this 0 n) (fun _ _ ↦ rfl),
    Finset.prod_congr (this 0 (n + 1)) (fun _ _ ↦ rfl)]
  have : f ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩ = g (n + 1) := by simp [g]
  rw [this]
  exact Finset.mul_prod_Ico_eq_prod_Icc (Nat.le_add_left (0 + 1) n)


theorem kerNat_prod {N : ℕ} (hN : 0 < N) :
    (kerNat (fun n ↦ kernel.const _ ((μ (n + 1)).map (e n))) 0 N) =
      kernel.const _ (Measure.pi (fun i : Ioc 0 N ↦ μ i)) := by
  ext1 x₀
  refine Nat.le_induction ?_ ?_ N (Nat.succ_le.2 hN)
  · rw [kerNat_succ, kernel.const_apply]
    refine (Measure.pi_eq (fun s ms ↦ ?_)).symm
    have : Subsingleton (Ioc 0 1) := by
      constructor
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      rw [mem_Ioc] at hi hj
      simp only [Subtype.mk.injEq]
      omega
    rw [Fintype.prod_subsingleton _ ⟨1, mem_Ioc.2 ⟨zero_lt_one, le_refl _⟩⟩, Measure.map_apply]
    congr
    · ext x
      simp only [Nat.reduceAdd, e, Ioc.mk_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        mem_preimage, Set.mem_pi, mem_univ, true_implies, Subtype.forall, mem_Ioc, Nat.zero_eq]
      constructor
      · intro h
        exact h 1 (by omega)
      · intro h i hi
        have : i = 1 := by omega
        cases this
        exact h
    · exact (e 0).measurable
    · exact MeasurableSet.univ_pi ms
  · intro n hn h_ind
    rw [kernel.const_apply]
    refine (Measure.pi_eq ?_).symm
    intro s ms
    rw [kerNat_succ_right, kerNat_succ, compProd,
      dif_pos ⟨Nat.succ_le.1 hn, n.lt_succ_self⟩, kernel.map_apply']
    · have : er 0 n (n + 1) (Nat.succ_le.1 hn) n.le_succ ⁻¹' univ.pi s =
          (univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)) ×ˢ
            ((e n).symm ⁻¹' (s ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl (n + 1)⟩⟩)) := by
        ext p
        simp only [er, Nat.succ_eq_add_one, Nat.reduceAdd, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
          mem_preimage, Set.mem_pi, mem_univ, true_implies, Subtype.forall, mem_Ioc, e,
          MeasurableEquiv.symm_mk, Equiv.coe_fn_symm_mk, mem_prod]
        refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ i ⟨hi1, hi2⟩ ↦ ?_⟩
        · intro i hi
          convert h i (mem_Ioc.1 <| Ioc_subset_Ioc_right n.le_succ hi)
          rw [dif_pos hi.2]
        · convert h (n + 1) ⟨n.succ_pos, le_refl _⟩
          simp
        · split_ifs with h
          · exact h1 i ⟨hi1, h⟩
          · have : i = n + 1 := by
              rcases Nat.le_or_eq_of_le_succ hi2 with a | b
              · exact (h a).elim
              · exact b
            cases this
            exact h2
      rw [this, split, kernel.comap_const, kernel.compProd_apply]
      · simp only [kernel.const_apply, Nat.succ_eq_add_one, mem_prod, mem_preimage]
        have this b : (μ (n + 1)).map (e n) {c | b ∈
            (univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)) ∧
              (e n).symm c ∈ s ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl (n + 1)⟩⟩} =
            (univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)).indicator
            (fun _ ↦ (μ (n + 1)) (s ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl _⟩⟩)) b := by
          simp only [Nat.succ_eq_add_one, Set.mem_pi, mem_univ, true_implies, Subtype.forall,
            mem_Ioc, indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]
          split_ifs with h
          · rw [mem_univ_pi] at h
            rw [Measure.map_apply]
            · congr
              ext x
              simp only [e, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.symm_mk,
                Equiv.coe_fn_symm_mk, preimage_setOf_eq, mem_setOf_eq, and_iff_right_iff_imp]
              rintro - i ⟨hi1, hi2⟩
              exact h ⟨i, mem_Ioc.2 ⟨hi1, hi2⟩⟩
            · exact (e n).measurable_toFun
            · have : MeasurableSet ((e n).symm ⁻¹' s ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩) :=
                (ms ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩).preimage (e n).measurable_invFun
              convert this
              ext x
              simp only [mem_setOf_eq, mem_preimage, and_iff_right_iff_imp]
              exact fun _ ↦ by simpa [mem_univ_pi] using h
          · rw [Measure.map_apply]
            · convert measure_empty
              · ext x
                simp only [e, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.symm_mk,
                  Equiv.coe_fn_symm_mk, preimage_setOf_eq, mem_setOf_eq, mem_empty_iff_false,
                  iff_false, not_and]
                intro h1 _
                apply h
                rw [mem_univ_pi]
                rintro ⟨i, hi⟩
                exact h1 i (mem_Ioc.1 hi)
              infer_instance
            · exact (e n).measurable_toFun
            · convert MeasurableSet.empty
              ext x
              simp only [e, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.symm_mk,
                Equiv.coe_fn_symm_mk, preimage_setOf_eq, mem_setOf_eq, mem_empty_iff_false,
                iff_false, not_and]
              intro h1 h2
              apply h
              rw [mem_univ_pi]
              rintro ⟨i, hi⟩
              exact h1 i (mem_Ioc.1 hi)
        simp_rw [this]
        rw [lintegral_indicator_const]
        · rw [h_ind, kernel.const_apply, Measure.pi_pi]
          apply prod_ioc n (fun i ↦ (μ i) (s i))
        · exact MeasurableSet.univ_pi (fun i ↦ ms ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)
      apply MeasurableSet.prod
      · exact MeasurableSet.univ_pi (fun i ↦ ms ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)
      · exact (ms ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩).preimage (e n).measurable_invFun
    · exact MeasurableSet.univ_pi ms
    exact Nat.succ_le.1 hn

theorem prod_noyau_proj (N : ℕ) :
    noyau_partiel (fun n ↦ kernel.const _ (μ (n + 1))) N =
      kernel.map ((kernel.deterministic id measurable_id) ×ₖ
          (kernel.const _ (Measure.pi (fun i : Ioc 0 N ↦ μ i))))
        (er' N) (er' N).measurable_toFun := by
  rw [noyau_partiel]
  cases N with
  | zero =>
    rw [my_ker_zero]
    have : IsEmpty (Ioc 0 0) := by
      rw [← not_nonempty_iff]
      intro h
      rw [nonempty_coe_sort, nonempty_Ioc] at h
      exact lt_irrefl 0 h
    rw [Measure.pi_of_empty]
    ext x s ms
    rw [kernel.map_apply, kernel.map_apply, kernel.deterministic_apply, kernel.prod_apply,
      kernel.deterministic_apply, kernel.const_apply, Measure.dirac_prod_dirac,
      Measure.map_apply, Measure.map_apply, Measure.dirac_apply', Measure.dirac_apply']
    · simp only [indicator, id_eq, mem_preimage, Pi.one_apply]
      have : zer x ∈ s ↔ (er' 0) (x, fun a : Ioc 0 0 ↦ isEmptyElim a) ∈ s := by
        simp only [zer, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er']
        congrm ?_ ∈ s
        ext i
        have := i.2
        rw [mem_Iic] at this
        have : i.1 = 0 := by omega
        simp [this]
      by_cases h : zer x ∈ s
      · simp [h, this.1 h]
      · simp [h, this.not.1 h]
    · exact ms.preimage (er' 0).measurable
    · exact ms.preimage zer.measurable
    · exact (er' 0).measurable
    · exact ms
    · exact zer.measurable
    · exact ms
  | succ n =>
    rw [my_ker_pos _ n.succ_pos]
    simp_rw [kernel.map_const]
    rw [kerNat_prod _ n.succ_pos]
    congr

variable {ι : Type*} {α : ι → Type*}

theorem preimage_proj (I J : Finset ι) [∀ i : ι, Decidable (i ∈ I)]
    (hIJ : I ⊆ J) (s : (i : I) → Set (α i)) :
    (fun t : (∀ j : J, α j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · simp [i_mem, h i i_mem]
  · simp [i_mem]

variable {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
variable (ν : (i : ι) → Measure (Y i)) [hμ : ∀ i, IsProbabilityMeasure (ν i)]

/-- Consider a family of probability measures. You can take their products for any fimite
subfamily. This gives a projective family of measures, see `IsProjectiveMeasureFamily`. -/
theorem isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ ν i))) := by
  classical
  intro I J hJI
  refine Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := Y) I J hJI) (MeasurableSet.univ_pi ms),
    preimage_proj J I hJI, Measure.pi_pi]
  have h1 : (@Finset.univ I _).prod (fun i ↦ (ν i) (if hi : i.1 ∈ J then s ⟨i.1, hi⟩ else univ)) =
      (@Finset.univ I.toSet _).prod
      (fun i ↦ (fun j ↦ (ν j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i) :=
    Finset.prod_congr rfl (by simp)
  have h2 : (@Finset.univ J _).prod (fun i ↦ (ν i) (s i)) =
      (@Finset.univ J.toSet _).prod
      (fun i ↦ (fun j ↦ (ν j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i) :=
    Finset.prod_congr rfl (by simp)
  rw [h1, h2, Finset.prod_set_coe
      (f := fun i ↦ (fun j ↦ (ν j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i),
    Finset.prod_set_coe
      (f := fun i ↦ (fun j ↦ (ν j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i),
    Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.prod_subset hJI (fun _ h h' ↦ by simp [h, h'])]

-- theorem kolContent_eq_measure_pi [Fintype ι] {s : Set ((i : ι) → Y i)} (hs : MeasurableSet s) :
--     kolContent (isProjectiveMeasureFamily_pi ν) s = Measure.pi ν s := by
--   have : s = cylinder Finset.univ s := by simp
--   rw [kolContent_congr (I := Finset.univ)]

theorem Measure.map_prod_snd {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [SFinite ν]
    (f : Y → Z) :
    (μ.prod ν).snd.map f = (μ.prod (ν.map f)).snd := by
  rw [Measure.snd_prod, Measure.snd_prod]

theorem Measure.map_snd_compProd {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μ : Measure X) (κ : kernel X Y) [IsProbabilityMeasure μ] [IsSFiniteKernel κ]
    {f : Y → Z} (hf : Measurable f) :
    (μ ⊗ₘ κ).snd.map f = Measure.snd (μ ⊗ₘ (kernel.map κ f hf)) := by
  ext s ms
  rw [Measure.map_apply hf ms, Measure.snd_apply (ms.preimage hf),
    Measure.compProd_apply (measurable_snd (hf ms)), Measure.snd_apply ms,
    Measure.compProd_apply (measurable_snd ms)]
  apply lintegral_congr
  intro x
  simp_rw [preimage_preimage]
  rw [kernel.map_apply', preimage_preimage]
  exact measurable_id ms

def e_Iic (b : ℕ) : (Finset.Iic b) ≃ (Iic b) where
  toFun := by
    intro ⟨i, hi⟩
    rw [← Finset.mem_coe, Finset.coe_Iic] at hi
    exact ⟨i, hi⟩
  invFun := by
    intro ⟨i, hi⟩
    rw [← Finset.coe_Iic, Finset.mem_coe] at hi
    exact ⟨i, hi⟩
  left_inv := fun _ ↦ by simp
  right_inv := fun _ ↦ by simp

def equiv_Iic (b : ℕ) : ((i : Finset.Iic b) → X i) ≃ᵐ ((i : Iic b) → X i) where
  toFun := fun x i ↦ x ((e_Iic b).symm i)
  invFun := fun x i ↦ x (e_Iic b i)
  left_inv := fun _ ↦ by simp [e_Iic]
  right_inv := fun _ ↦ by simp [e_Iic]
  measurable_toFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

lemma indicator_const_mul {α : Type*} (s : Set α) (c : ℝ≥0∞) (a : α) :
    (s.indicator 1 a) * c = s.indicator (fun _ ↦ c) a := by
  simp [indicator]

theorem prod_iic (n : ℕ) (f : (Iic n) → ℝ≥0∞) :
    (∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Iic_self i.2⟩) * f ⟨0, mem_Iic.2 <| zero_le _⟩ =
    ∏ i : Iic n, f i := by
  let g : ℕ → ℝ≥0∞ := fun k ↦ if hk : k ∈ Iic n then f ⟨k, hk⟩ else 1
  have h1 : ∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Iic_self i.2⟩ =
      ∏ i : Ioc 0 n, g i := by
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
  rw [h1, h2, Finset.prod_set_coe, Finset.prod_set_coe]
  have this (a b : ℕ) : (Ioc a b).toFinset = Finset.Ioc a b := by simp
  have this' (a : ℕ) : (Iic a).toFinset = Finset.Iic a := by simp
  rw [Finset.prod_congr (this 0 n) (fun _ _ ↦ rfl),
    Finset.prod_congr (this' n) (fun _ _ ↦ rfl)]
  have : f ⟨0, mem_Iic.2 <| zero_le _⟩ = g 0 := by simp [g]
  rw [this]
  exact Finset.prod_Ioc_mul_eq_prod_Icc (zero_le n)

theorem projectiveLimit_prod_meas : IsProjectiveLimit (prod_meas μ)
    (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  have sub : I ⊆ Finset.Iic (I.sup id) := fun i hi ↦ Finset.mem_Iic.2 <| Finset.le_sup (f := id) hi
  have : Measure.pi (fun i : I ↦ μ i) =
      (Measure.pi (fun i : Iic (I.sup id) ↦ μ i)).map
      (fun x (i : I) ↦ ((equiv_Iic _).symm x) ⟨i.1, sub i.2⟩) := by
    conv_lhs => change (fun I : Finset ℕ ↦ Measure.pi (fun i : I ↦ μ i)) I
    rw [isProjectiveMeasureFamily_pi μ (Finset.Iic (I.sup id)) I sub]
    simp only
    conv_rhs =>
      enter [1]
      change fun x ↦ ((fun x (i : I) ↦ x ⟨i.1, sub i.2⟩) ∘ (equiv_Iic (I.sup id)).symm) x
    rw [← Measure.map_map]
    · congr
      refine Measure.pi_eq (fun s ms ↦ ?_)
      rw [Measure.map_apply]
      · have : (equiv_Iic (I.sup id)).symm ⁻¹' univ.pi s =
            univ.pi (fun i : Iic (I.sup id) ↦ s ((e_Iic _).symm i)) := by
          ext x
          simp [equiv_Iic, e_Iic]
        rw [this, Measure.pi_pi]
        apply Fintype.prod_equiv ((e_Iic (I.sup id)).symm)
        simp [e_Iic]
      · exact MeasurableEquiv.measurable_invFun _
      · exact MeasurableSet.univ_pi ms
    · exact measurable_proj₂' _ _ sub
    · exact MeasurableEquiv.measurable_invFun _
  simp_rw [this]
  have : (fun (x : (n : ℕ) → X n) (i : I) ↦ x i) =
      (fun x (i : I) ↦ x ⟨i.1, Finset.mem_Iic.2 <| Finset.le_sup (f := id) i.2⟩) ∘
      (equiv_Iic (I.sup id)).symm ∘
      (fun x (i : Iic (I.sup id)) ↦ x i) := by ext x i; simp [equiv_Iic, e_Iic]
  rw [this, ← Function.comp.assoc, ← Measure.map_map]
  congr
  rw [prod_meas, Measure.map_snd_compProd, noyau_proj, prod_noyau_proj]
  refine (Measure.pi_eq fun s ms ↦ ?_).symm
  have mpis := MeasurableSet.univ_pi ms
  rw [Measure.snd_apply mpis, Measure.compProd_apply (measurable_snd mpis)]
  refine Eq.trans (b := ∫⁻ x₀, (s ⟨0, mem_Iic.2 <| zero_le _⟩).indicator 1 (id x₀) *
    ∏ i : Ioc 0 (I.sup id), (μ ↑i) (s ⟨i.1, Ioc_subset_Iic_self i.2⟩) ∂μ 0) ?_ ?_
  · refine lintegral_congr fun x₀ ↦ ?_
    have this : (er' (I.sup id)) ⁻¹' (Prod.mk x₀ ⁻¹' (Prod.snd ⁻¹' univ.pi fun i ↦ s i)) =
        s ⟨0, mem_Iic.2 <| zero_le _⟩ ×ˢ
          univ.pi (fun i : Ioc 0 (I.sup id) ↦ s ⟨i.1, Ioc_subset_Iic_self i.2⟩) := by
      ext x
      simp only [er', MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_preimage, Set.mem_pi, mem_univ,
        true_implies, Subtype.forall, mem_Iic, mem_prod, mem_Ioc]
      refine ⟨fun h ↦ ⟨?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i hi ↦ ?_⟩
      · exact h 0 (zero_le _)
      · convert h i hi2
        simp [hi1.ne.symm]
      · split_ifs with h
        · cases h; exact h1
        · have : 0 < i := by omega
          exact h2 i ⟨this, hi⟩
    rw [kernel.map_apply', this, kernel.prod_apply, Measure.prod_prod, kernel.deterministic_apply,
      Measure.dirac_apply', kernel.const_apply, Measure.pi_pi]
    · exact ms _
    · exact measurable_prod_mk_left (m := inferInstance) (measurable_snd mpis)
  · simp_rw [indicator_const_mul, id_eq]
    rw [lintegral_indicator_const]
    apply prod_iic (I.sup id) (fun i ↦ (μ i) (s i))
    exact ms _
  · apply (measurable_proj₂' _ _ _).comp (equiv_Iic (I.sup id)).measurable_invFun
    exact fun i hi ↦ Finset.mem_Iic.2 <| Finset.le_sup (f := id) hi
  · exact measurable_proj _


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

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by a countable type. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem secondLemma
    (φ : ℕ ≃ ι) (A : ℕ → Set ((i : ι) → X i)) (A_mem : ∀ n, A n ∈ cylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩;
    infer_instance
  set μ_proj := isProjectiveMeasureFamily_pi μ
  let μ_proj' := isProjectiveMeasureFamily_pi (fun k : ℕ ↦ μ (φ k))
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa only [mem_cylinders, exists_prop] using A_mem n
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
  let f : ((k : ℕ) → X (φ k)) → (i : ι) → X i := fun x i ↦ cast (h i) (x (φ.symm i))
  -- `aux n` is an equivalence between `sₙ` ans `tₙ`, it will be used to link the two.
  let aux n : s n ≃ t n :=
    { toFun := fun i ↦ ⟨φ.symm i, e n i.1 i.2⟩
      invFun := fun k ↦ ⟨φ k, e' n k.1 k.2⟩
      left_inv := by simp [Function.LeftInverse]
      right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
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
    simp_rw [B, A_eq, cylinder, ← preimage_comp, test n]
    rfl
  -- `gₙ` is measurable. We have to play with `Heq` to prove measurability of `cast`.
  have mg n : Measurable (g n) := by
    simp only [g]
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    have : (fun c : (k : t n) → X (φ k) ↦ cast (h i) (c (aux n i))) =
        ((fun a ↦ cast (h i) a) ∘ (fun x ↦ x (aux n i))) := by
      ext x
      simp
    rw [this]
    apply Measurable.comp
    · have aux1 : HEq (hX i) (hX (φ (φ.symm i))) := by
        rw [← cast_eq_iff_heq (e := by simp [h i])]
        exact @omg_ ι (fun i ↦ MeasurableSpace (X i)) (s n) (fun i ↦ hX i)
          i ⟨φ (φ.symm i), by simp [i.2]⟩ (by simp) _
      let f := MeasurableEquiv.cast (h i).symm aux1
      have aux2 : (fun a : X (φ (φ.symm i)) ↦ cast (h i) a) = f.symm := by
        ext a
        simp [f, MeasurableEquiv.cast]
      rw [aux2]
      exact f.measurable_invFun
    · exact @measurable_pi_apply (t n) (fun k ↦ X (φ k)) _ _
  -- We deduce that `Tₙ` is measurable.
  have mT n : MeasurableSet (T n) := (mS n).preimage (mg n)
  -- The sequence `(Bₙ)` satisfies the hypotheses of `firstLemma`, we now have to prove that we can
  -- rewrite the goal in terms of `B`.
  have B_anti : Antitone B := fun m n hmn ↦ preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← preimage_iInter, A_inter, Set.preimage_empty]
  have B_mem n : B n ∈ cylinders (fun k ↦ X (φ k)) :=
    (mem_cylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  -- Taking the preimage of a product indexed by `sₙ` by `gₙ` yields a product indexed by `uₙ`,
  -- again we have to play with `cast`.
  have imp n (u : (i : s n) → Set (X i)) : (g n) ⁻¹' (Set.univ.pi u) =
      Set.univ.pi (fun k : t n ↦ u ⟨φ k, e' n k.1 k.2⟩) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, g]
    constructor
    · intro h' k hk
      convert h' (φ k) (e' n k hk)
      simp only [Equiv.coe_fn_mk, aux]
      rw [@omg_ ℕ (fun k ↦ X (φ k)) (t n) x ⟨φ.symm (φ k), by simp [hk]⟩ ⟨k, hk⟩]
      simp
    · intro h' i hi
      convert h' (φ.symm i) (e n i hi)
      simp only [Equiv.coe_fn_mk, aux]
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
    · exact MeasurableSet.pi countable_univ (by simp [mx])
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
theorem thirdLemma (A : ℕ → Set (∀ i, X i)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  classical
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
      left_inv := by simp [Function.LeftInverse]
      right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
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
    · exact MeasurableSet.pi countable_univ (by simp [mx])
  let T : (n : ℕ) → Set ((i : t n) → X i) :=
    fun n ↦ (fun x i ↦ cast (h n i) (x (aux n i))) ⁻¹' (S n)
  have mT n : MeasurableSet (T n) := by
    apply (mS n).preimage (meas n)
  let B : ℕ → Set (∀ i : u, X i) := fun n ↦ cylinder (t n) (T n)
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
    exact preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B_eq, ← preimage_iInter, A_inter, Set.preimage_empty]
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
          (dependsOn_cylinder_indicator (t n) (T n))
          (t n).subset_univ, lmarginal_univ, ← obv, lintegral_indicator_const]
      · simp
      · exact @measurableSet_cylinder u (fun i : u ↦ X i) _ (t n) (T n) (mT n)
      · rw [Finset.coe_univ, ← compl_eq_univ_diff]
        exact disjoint_compl_right
      · rw [← obv, measurable_indicator_const_iff 1]
        exact @measurableSet_cylinder u (fun i : u ↦ X i) _ (t n) (T n) (mT n)
    simp_rw [concl, ← measure_empty (μ := Measure.pi (fun i : u ↦ μ i)), ← B_inter]
    exact tendsto_measure_iInter (fun n ↦ measurableSet_cylinder (t n) (T n) (mT n))
      B_anti ⟨0, measure_ne_top _ _⟩
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    refine secondLemma (fun i : u ↦ μ i) φ B (fun n ↦ ?_) B_anti B_inter
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
    measure_produit μ (pi s t) = ∏ i ∈ s, (μ i) (t i) := by
  classical
  have : pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← Measure.map_apply, isProjectiveLimit_measure_produit μ,
    Measure.pi_pi]
  · rw [Finset.univ_eq_attach, Finset.prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_proj _
  · apply MeasurableSet.pi countable_univ fun i _ ↦ mt i.1 i.2

theorem measure_cylinder {s : Finset ι} {S : Set ((i : s) → X i)} (mS : MeasurableSet S) :
    measure_produit μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply _ mS, isProjectiveLimit_measure_produit μ]
  exact measurable_proj _

theorem integral_dep_measure_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : s) → X i) → E} (hf : StronglyMeasurable f) :
    ∫ y, f ((fun x (i : s) ↦ x i) y) ∂measure_produit μ =
    ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map, isProjectiveLimit_measure_produit μ]
  · exact (measurable_proj _).aemeasurable
  · exact hf.aestronglyMeasurable

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
  rw [← integral_congr_ae <| eventually_of_forall this]
  rw [integral_dep_measure_prod]
  · exact mf.comp_measurable measurable_updateFinset

theorem lintegral_dep {s : Finset ι} {f : ((i : s) → X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f ((fun x (i : s) ↦ x i) y) ∂measure_produit μ =
    ∫⁻ y, f y∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf, isProjectiveLimit_measure_produit μ]
  exact (measurable_proj _)

theorem lintegral_dependsOn [DecidableEq ι]
    {f : ((i : ι) → X i) → ℝ≥0∞} (mf : Measurable f) {s : Finset ι} (hf : DependsOn f s)
    (x : (i : ι) → X i) : ∫⁻ y, f y ∂measure_produit μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : ((i : s) → X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g ((fun z (i : s) ↦ z i) y) = f y := by
    apply hf
    intro i hi
    simp only [Function.updateFinset, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  simp_rw [← this]
  rw [lintegral_dep]
  · rfl
  · exact mf.comp measurable_updateFinset
