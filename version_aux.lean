import Mathlib.KolmogorovExtension4.Transition
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Data.PNat.Interval

open MeasureTheory ProbabilityTheory MeasurableSpaceGraph Set ENNReal Filter Topology

variable {X : ℕ → Type*} [∀ n, Nonempty (X n)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((transitionGraph X).node k) ((transitionGraph X).path k (k + 1)))

def zer : (X 0) ≃ᵐ ((i : Iic 0) → X i) where
  toFun := fun x₀ i ↦ by
    have : 0 = i.1 := by
      have := i.2
      simp at this
      exact this.symm
    exact this ▸ x₀
  invFun := fun x ↦ x ⟨0, mem_Iic.2 <| le_refl 0⟩
  left_inv := fun x₀ ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : 0 = i.1 := by
      have := i.2
      simp at this
      exact this.symm
    aesop
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : 0 = i.1 := by
      have := i.2
      simp at this
      exact this.symm
    aesop
  measurable_invFun := measurable_pi_apply _

def er' (N : ℕ) : (X 0) × ((i : Ioc 0 N) → X i) ≃ᵐ ((i : Iic N) → X i) where
  toFun := fun p n ↦ if h : n.1 = 0 then h.symm ▸ p.1 else
    p.2 ⟨n.1, ⟨Nat.zero_lt_of_ne_zero h, n.2⟩⟩
  invFun := fun x ↦ ⟨x ⟨0, N.zero_le⟩, fun n ↦ x ⟨n.1, Ioc_subset_Iic_self n.2⟩⟩
  left_inv := fun p ↦ by
    ext n
    · simp
    · simp only
      split_ifs with h
      · have := n.2
        rw [h] at this
        simp at this
      · rfl
  right_inv := fun x ↦ by
    ext n
    simp only
    split_ifs with h
    · have : n = ⟨0, N.zero_le⟩ := by
        rwa [← Subtype.val_inj]
      cases this; rfl
    · rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun n ↦ ?_)
    by_cases h : n.1 = 0
    · simp only [Equiv.coe_fn_mk, h, ↓reduceDite]
      simp_rw [eqRec_eq_cast]
      apply (measurable_cast _ _).comp
      · exact measurable_fst
      · aesop
    · simp only [Equiv.coe_fn_mk, h, ↓reduceDite]
      apply (measurable_pi_apply _).comp
      exact measurable_snd
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_
    · apply measurable_pi_apply
    · exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

noncomputable def my_ker [∀ k, IsSFiniteKernel (κ k)] (N : ℕ) :
    kernel (X 0) ((i : Iic N) → X i) := by
  cases N with
  | zero =>
    exact kernel.map (kernel.deterministic id measurable_id) zer zer.measurable_toFun
  | succ n =>
    exact kernel.map ((kernel.deterministic id measurable_id) ×ₖ
        (kernel.comap ((transition κ).ker 0 (n + 1)) zer zer.measurable_toFun))
      (er' (n + 1)) (er' (n + 1)).measurable_toFun

theorem my_ker_zero [∀ k, IsSFiniteKernel (κ k)] : my_ker κ 0 =
    kernel.map (kernel.deterministic id measurable_id) zer zer.measurable_toFun := rfl

theorem my_ker_pos [∀ k, IsSFiniteKernel (κ k)] {N : ℕ} (hN : 0 < N) :
    my_ker κ N = kernel.map ((kernel.deterministic id measurable_id) ×ₖ
        (kernel.comap ((transition κ).ker 0 N) zer zer.measurable_toFun))
      (er' N) (er' N).measurable_toFun := by
  rw [← N.succ_pred]
  · rfl
  · exact (ne_of_lt hN).symm

variable [∀ k, IsMarkovKernel (κ k)]

theorem markov1 {M : MeasurableSpaceGraph ℕ} {i j k : ℕ}
    (κ : kernel (M.node i) (M.path i j)) (η : kernel (M.node j) (M.path j k))
    [IsMarkovKernel κ] [IsMarkovKernel η] (hij : i < j) (hjk : j < k) :
    IsMarkovKernel (M.compProd κ η) := by
  rw [compProd]
  simp only [hij, hjk, and_self, ↓reduceDite, split]
  infer_instance

theorem markov2 {M : MeasurableSpaceGraph ℕ} {i j k : ℕ}
    (κ : kernel (M.node i) (M.path i j)) [IsMarkovKernel κ] (hjk : j = k)  :
    IsMarkovKernel (castPath κ hjk) := by
  rw [castPath]; infer_instance

theorem markov {M : MeasurableSpaceGraph ℕ} {i j k : ℕ}
    (κ₀ : kernel (M.node i) (M.path i j)) [h₀ : IsMarkovKernel κ₀]
    (κ : ∀ k, kernel (M.node k) (M.path k (k + 1))) [∀ k, IsMarkovKernel (κ k)]
    (hij : i < j) (hjk : j ≤ k) :
    IsMarkovKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => linarith
  | succ n hn =>
    rw [kerInterval_succ]
    split_ifs with h
    · apply markov2
    · have : j ≤ n := Nat.lt_succ.1 <| lt_iff_le_and_ne.2 ⟨hjk, h⟩
      have _ := hn this
      exact markov1 _ _ (lt_of_lt_of_le hij this) n.lt_succ_self

theorem markov_kerNat {M : MeasurableSpaceGraph ℕ} {i j : ℕ}
    (κ : ∀ k, kernel (M.node k) (M.path k (k + 1))) [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
    IsMarkovKernel (kerNat κ i j) := by
  simp only [kerNat, hij, ↓reduceIte]
  exact markov _ _ i.lt_succ_self (Nat.succ_le.2 hij)

instance {N : ℕ} : IsMarkovKernel (my_ker κ N) := by
  rcases eq_zero_or_pos N with hN | hN
  · rw [hN, my_ker_zero]; infer_instance
  · have : IsMarkovKernel ((transition κ).ker 0 N) := markov_kerNat _ hN
    rw [my_ker_pos _ hN]; infer_instance

noncomputable def family (x₀ : X 0) :
  (S : Finset ℕ) → Measure ((k : S) → X k) := fun S ↦
  (my_ker κ (S.sup id) x₀).map
  (fun x (i : S) ↦ x ⟨i.1, Finset.le_sup (f := id) i.2⟩)

theorem kernel.map_map {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace T]
    (κ : kernel X Y) (f : Y → Z) (hf : Measurable f) (g : Z → T) (hg : Measurable g) :
    kernel.map (kernel.map κ f hf) g hg = kernel.map κ (g ∘ f) (hg.comp hf) := by
  ext1 x
  rw [kernel.map_apply, kernel.map_apply, Measure.map_map, ← kernel.map_apply]
  · exact hg
  · exact hf

theorem kernel.map_prod {X Y Z T U : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace U]
    (κ : kernel X Y) (η : kernel X T)
    {f : Y → Z} (hf : Measurable f) {g : T → U} (hg : Measurable g) :
    kernel.map (κ ×ₖ η) (Prod.map f g) (hf.prod_map hg) =
    (kernel.map κ f hf) ×ₖ (kernel.map η g hg) := by sorry

theorem my_ker_proj {k l : ℕ} (hkl : k ≤ l) :
    kernel.map (my_ker κ l)
      (fun (x : ((i : Iic l) → X i)) (i : Iic k) ↦ x ⟨i.1, Iic_subset_Iic.2 hkl i.2⟩)
      (measurable_proj₂ ..) = my_ker κ k := by
  by_cases h : k = l
  · have aux : ((i : Iic l) → X i) = ((i : Iic k) → X i) := by aesop
    have : (fun (x : ((i : Iic l) → X i)) (i : Iic k) ↦
        x ⟨i.1, Iic_subset_Iic.2 hkl i.2⟩) = cast aux := by aesop
    conv_lhs =>
      enter [2]
      rw [this]
    ext x s ms
    rw [kernel.map_apply' _ _ _ ms]
    cases h; rfl
  · have hkl : k < l := lt_iff_le_and_ne.2 ⟨hkl, h⟩
    by_cases hk : k = 0
    · cases hk
      rw [my_ker_pos _ hkl, my_ker_zero, kernel.map_map]
      have : (fun (x : (i : Iic l) → X i) (i : Iic 0) ↦ x ⟨i.1, Iic_subset_Iic.2 hkl.le i.2⟩) ∘
          (er' l) = zer ∘ Prod.fst := by
        ext p i
        have : i.1 = 0 := (i.1.le_zero).1 i.2
        simp [er', zer, this]
      conv_lhs =>
        enter [2]
        rw [this]
      have : kernel.map ((kernel.deterministic id measurable_id) ×ₖ
          (kernel.comap ((transition κ).ker 0 l) zer zer.measurable_toFun))
          Prod.fst measurable_fst =
          kernel.deterministic id measurable_id := by
        have : IsMarkovKernel ((transition κ).ker 0 l) := markov_kerNat _ hkl
        apply kernel.fst_prod
      rw [← kernel.map_map]
      congr
      exact zer.measurable_toFun
    · have hk : 0 < k := Nat.zero_lt_of_ne_zero hk
      rw [my_ker_pos _ (hk.trans hkl), transition_ker, ← compProd_kerNat _ hk hkl, kernel.map_map]
      have : (fun (x : (i : Iic l) → X i) (i : Iic k) ↦ x ⟨i.1, Iic_subset_Iic.2 hkl.le i.2⟩) ∘
          (er' l) = (er' k) ∘ (Prod.map id (fun (x : (i : Ioc 0 l) → X i)
          (i : Ioc 0 k) ↦ x ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩)) := by
        ext p i
        simp only [er', MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, Prod_map,
          id_eq]
      conv_lhs =>
        enter [2]
        rw [this]
      rw [← kernel.map_map, my_ker_pos _ hk]
      congr
      rw [kernel.map_prod, kernel.map_id]
      congr
      ext x s ms
      rw [kernel.map_apply', kernel.comap_apply', compProd_apply' _ _ hk hkl]
      simp_rw [preimage_preimage]
      have aux1 (b : (transitionGraph X).path 0 k) (c : (transitionGraph X).path k l) :
          b ∈ s ↔
          c ∈ {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
          (transitionGraph X).er 0 k l hk hkl x
          ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) ⁻¹' s} := by
        have : (fun (i : Ioc 0 k) ↦ (transitionGraph X).er 0 k l hk hkl (b, c)
            ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) = b := by
          ext i
          rw [er_eq]
          simp [ProbabilityTheory.er, (mem_Ioc.2 i.2).2]
        simp [this]
      have aux2 b (hb : b ∈ s) :
          {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
          (transitionGraph X).er 0 k l hk hkl x
          ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) ⁻¹' s} = univ := by
        ext c
        simp only [mem_preimage, mem_univ, iff_true]
        exact (aux1 b c).1 hb
      have aux3 b (hb : b ∉ s) :
          {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
          (transitionGraph X).er 0 k l hk hkl x
          ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) ⁻¹' s} = ∅ := by
        ext c
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact (aux1 b c).not.1 hb
      have aux4 b : ((kerNat κ k l) ((transitionGraph X).el 0 k hk (zer x, b)))
          {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
          (transitionGraph X).er 0 k l hk hkl x ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) ⁻¹' s} =
          s.indicator 1 b := by
        have := markov_kerNat κ hkl
        by_cases hb : b ∈ s
        · simp_rw [indicator, aux2 b hb]
          simp [hb]
        · simp_rw [aux3 b hb]
          simp [hb]
      simp_rw [aux4]
      · have : (1 : (transitionGraph X).path 0 k → ℝ≥0∞) = fun _ ↦ 1 := rfl
        rw [this, lintegral_indicator_const, transition_ker, one_mul]
        · rfl
        · exact ms
      · exact ms.preimage <| measurable_proj₂ _ _ <| Icc_subset_Icc_right hkl.le
      · exact ms
      · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
      · exact (er' _).measurable_toFun


-- theorem test {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
--     kernel.map ((transition κ).ker 0 l)
--       (fun (x : ((i : Ioc 0 l) → X i)) (i : Ioc 0 k) ↦ x ⟨i.1, Ioc_subset_Ioc_right hkl i.2⟩)
--       (measurable_proj₂ ..) =
--     (transition κ).ker 0 k := by
--   by_cases h : k = l
--   · have : (fun (x : ((i : Ioc 0 l) → X i)) (i : Ioc 0 k) ↦
--         x ⟨i.1, Ioc_subset_Ioc_right hkl i.2⟩) =
--         transitionGraph.path_eq X ▸ (e_path_eq _ h.symm).toFun := by aesop
--     conv_lhs =>
--       enter [2]
--       rw [this]
--     simp only [Equiv.toFun_as_coe, MeasurableEquiv.coe_toEquiv]
--     exact (kerNat_cast _ _ _ _ _).symm
--   · have hkl : k < l := lt_iff_le_and_ne.2 ⟨hkl, h⟩
--     ext x s ms
--     rw [kernel.map_apply', transition_ker κ 0 l, ← compProd_kerNat κ hk hkl,
--       compProd_apply' _ _ hk hkl]
--     simp_rw [preimage_preimage]
--     have aux1 (b : (transitionGraph X).path 0 k) (c : (transitionGraph X).path k l) :
--         b ∈ s ↔
--         c ∈ {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
--         (transitionGraph X).er 0 k l hk hkl x ⟨i.1, _⟩) ⁻¹' s} := by
--       have : (fun (i : Ioc 0 k) ↦ (transitionGraph X).er 0 k l hk hkl (b, c)
--           ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) = b := by
--         ext i
--         rw [er_eq]
--         simp [ProbabilityTheory.er, (mem_Ioc.2 i.2).2]
--       simp [this]
--     have aux2 b (hb : b ∈ s) :
--         {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
--         (transitionGraph X).er 0 k l hk hkl x ⟨i.1, _⟩) ⁻¹' s} = univ := by
--       ext c
--       simp only [mem_preimage, mem_univ, iff_true]
--       exact (aux1 b c).1 hb
--     have aux3 b (hb : b ∉ s) :
--         {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
--         (transitionGraph X).er 0 k l hk hkl x ⟨i.1, _⟩) ⁻¹' s} = ∅ := by
--       ext c
--       simp only [mem_preimage, mem_empty_iff_false, iff_false]
--       exact (aux1 b c).not.1 hb
--     have aux4 b : ((kerNat κ k l) ((transitionGraph X).el 0 k hk (x, b)))
--         {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
--         (transitionGraph X).er 0 k l hk hkl x ⟨↑i, _⟩) ⁻¹' s} =
--         s.indicator 1 b := by
--       have := markov_kerNat κ hkl
--       by_cases hb : b ∈ s
--       · simp_rw [indicator, aux2 b hb]
--         simp [hb]
--       · simp_rw [aux3 b hb]
--         simp [hb]
--     simp_rw [aux4]
--     · have : (1 : (transitionGraph X).path 0 k → ℝ≥0∞) = fun _ ↦ 1 := rfl
--       rw [this, lintegral_indicator_const, transition_ker, one_mul]
--       · rfl
--       · exact ms
--     · exact ms.preimage <| measurable_proj₂ _ _ <| Icc_subset_Icc_right hkl.le
--     · exact ms

theorem proj_family (x₀ : X 0) :
    IsProjectiveMeasureFamily (family κ x₀) := by
  intro S T hTS
  have aux1 : T.sup id ≤ S.sup id := Finset.sup_mono hTS
  simp only [family]
  rw [← kernel.map_apply, ← my_ker_proj _ aux1, Measure.map_map, kernel.map_map, kernel.map_apply]
  · rfl
  · simp_all only [Finset.le_eq_subset, add_le_add_iff_right, Finset.sup_le_iff, id_eq]
    apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'
  · simp_all only [Finset.le_eq_subset, add_le_add_iff_right, Finset.sup_le_iff, id_eq]
    apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'
  · simp_all only [Finset.le_eq_subset, add_le_add_iff_right, Finset.sup_le_iff, id_eq]
    apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'

noncomputable def updateSet {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) (s : Set ι)
    (y : (i : s) → α i) (i : ι) : α i := by
  classical
  exact if hi : i ∈ s then y ⟨i, hi⟩ else x i

theorem updateSet_empty {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) (s : Set ι) (hs : s = ∅)
    (y : (i : s) → α i) : updateSet x s y = x := by
  ext i
  simp [updateSet, hs]

theorem measurable_updateSet {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (x : (i : ι) → α i) (s : Set ι) :
    Measurable (updateSet x s) := by
  simp (config := { unfoldPartialApp := true }) only [updateSet, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

def pioc (a b : ℕ) := Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

def fpioc (a b : ℕ) : Finset ℕ+ := Finset.Ico (⟨a + 1, a.succ_pos⟩ : ℕ+) (⟨b + 1, b.succ_pos⟩ : ℕ+)

theorem mem_ioc_of_mem_pioc {a b : ℕ} (i : pioc a b) : i.1.1 ∈ Ioc a b := by
  rcases mem_Ico.1 i.2 with ⟨h1, h2⟩
  rw [← PNat.coe_le_coe] at h1
  rw [← PNat.coe_lt_coe] at h2
  simp only [PNat.mk_coe] at h1 h2
  exact mem_Ioc.2 ⟨Nat.succ_le_iff.1 h1, Nat.lt_succ_iff.1 h2⟩

def ioc_eq {a b : ℕ} (i : pioc a b) : Ioc a b := ⟨i.1.1, mem_ioc_of_mem_pioc i⟩

theorem measurable_ioc_eq (a b : ℕ) : Measurable (@ioc_eq a b) := measurable_discrete _

def pioc_ioc {a b : ℕ} (z : (i : Ioc a b) → X i) (i : pioc a b) : X i := z (ioc_eq i)

theorem measurable_pioc_ioc (a b : ℕ) : Measurable (@pioc_ioc X a b) := by
  apply measurable_pi_lambda
  intro a_1
  apply measurable_pi_apply

theorem mem_pioc {k : ℕ} (i : Iic k) (hi : ¬i.1 = 0) :
    ⟨i.1, i.1.pos_of_ne_zero hi⟩ ∈ pioc 0 k := by
  simp [pioc]
  rw [← PNat.coe_le_coe]
  rcases mem_Iic.1 i.2 with h
  exact ⟨Nat.one_le_iff_ne_zero.2 hi, Nat.lt_succ.2 h⟩

def fus {k : ℕ} (x₀ : X 0) (y : (i : pioc 0 k) → X i) (i : Iic k) : X i :=
  if hi : i.1 = 0 then hi ▸ x₀ else y ⟨⟨i.1, i.1.pos_of_ne_zero hi⟩, mem_pioc i hi⟩

theorem measurable_fus (k : ℕ) (x₀ : X 0) : Measurable (fus (k := k) x₀) := by
  simp (config := { unfoldPartialApp := true }) only [fus, measurable_pi_iff]
  intro i
  by_cases h : i.1 = 0 <;> simp [h, measurable_pi_apply]

noncomputable def kerint (k N : ℕ) (f : ((n : ℕ) → X n) → ℝ≥0∞) (x₀ : X 0)
    (x : (i : ℕ) → X i) : ℝ≥0∞ :=
  if k = 0
    then ∫⁻ z : (i : Iic N) → X i, f (updateSet x _ z) ∂my_ker κ N x₀
    else if k < N
      then ∫⁻ z : (i : Ioc k N) → X i,
        f (updateSet x _ z) ∂((transition κ).ker k N (er' k (x₀, (fun i ↦ x i))))
      else f x

theorem sup_ioc (N : ℕ) : ((Finset.Ioc 0 N).sup id) = N := by sorry
  -- apply le_antisymm
  -- · apply Finset.sup_le
  -- simp only [fpioc, zero_add, PNat.mk_ofNat]
  -- conv_rhs => change ((↑) : ℕ+ → ℕ) (⟨N, hN⟩ : ℕ+)
  -- conv_lhs => change ((↑) : ℕ+ → ℕ) ((Finset.Ico 1 ⟨N + 1, N.succ_pos⟩).sup id)
  -- apply le_antisymm <;> rw [PNat.coe_le_coe]
  -- · apply Finset.sup_le
  --   simp only [Finset.mem_Ico, PNat.one_le, true_and, id_eq]
  --   intro b hb
  --   rw [← PNat.coe_lt_coe, PNat.mk_coe, Nat.lt_succ] at hb
  --   rwa [← PNat.coe_le_coe]
  -- · have : (⟨N, hN⟩ : ℕ+) = id ⟨N, hN⟩ := rfl
  --   rw [this]
  --   apply Finset.le_sup
  --   simp only [Finset.mem_Ico, Subtype.mk_lt_mk, lt_add_iff_pos_right, zero_lt_one, and_true]
  --   rw [← PNat.coe_le_coe]
  --   simp only [PNat.val_ofNat, PNat.mk_coe]
  --   linarith

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

-- theorem cast_fpioc (N : ℕ) : ((i : fpioc 0 N) → X i) =
--     ((i : fpioc 0 N) → X (⟨i.1.1, fpioc_mem_ioc i⟩ : Ioc 0 ((fpioc 0 N).sup id).1).1) := rfl



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
  rw [lint_eq', lint_eq (f := fun b : β ↦ f (cast h.symm b))]
  · exact h'
  · apply hf.comp
    exact measurable_cast h.symm h'.symm

theorem eq_pi (s t : Set ℕ) (h : s = t) :
    ((i : s) → X i) = ((i : t) → X i) := by
  aesop

theorem eq_pi' {a b : ℕ} (h : a = b) :
    ((i : Ioc 0 a) → X i) = ((i : Ioc 0 b) → X i) := by
  aesop

theorem eq_fpioc {N : ℕ} (hN : 0 < N) :
    ((transitionGraph X).path 0 ((fpioc 0 N).sup id).1) = ((i : Ioc 0 N) → X i) := by
  apply eq_pi'
  exact sup_fpioc hN

theorem heq_meas (s t : Set ℕ) (h : s = t) :
    HEq (inferInstance : MeasurableSpace ((i : s) → X i))
    (inferInstance : MeasurableSpace ((i : t) → X i)) := by
  aesop

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

theorem kolContent_eq_kerint {N : ℕ} (hN : 0 < N) {S : Set ((i : fpioc 0 N) → X i)}
    (mS : MeasurableSet S)
    (x₀ : X 0) (x : (n : ℕ+) → X n) :
    kolContent (α := fun n : ℕ+ ↦ X n) (proj_family κ x₀) (cylinder (fpioc 0 N) S) =
    kerint κ 0 N ((cylinder _ S).indicator 1) x₀ x := by
  rw [kolContent_congr _
      (by rw [mem_cylinders]; exact ⟨fpioc 0 N, S, mS, rfl⟩) rfl mS, family]
  rw [Measure.map_apply, ← lintegral_indicator_one₀, kerint]
  · simp only [cast_eq, hN, ↓reduceIte]
    rw [lint_eq'' (eq_fpioc hN)]
    congr
    · rw [measure_cast (sup_fpioc hN) (fun n ↦ (transition κ).ker 0 n (zer x₀))]
      congr
      ext i
      simp only [zer, fus]
      have := i.2
      simp only [mem_Iic, nonpos_iff_eq_zero] at this
      simp [this]
    · ext z
      rw [preimage_indicator]
      simp only [indicator, Pi.one_apply, mem_cylinder]
      have : (fun i : fpioc 0 N ↦ cast (eq_fpioc hN).symm z ⟨i.1.1, fpioc_mem_ioc hN i⟩) ∈ S ↔
          updateSet x _ (pioc_ioc z) ∈ cylinder (fpioc 0 N) S := by
        simp only [mem_cylinder]
        congrm ?_ ∈ S
        ext i
        simp only [updateSet, pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and,
          pioc_ioc, Nat.reduceAdd, ioc_eq]
        have := i.2
        simp only [fpioc, Nat.reduceAdd, PNat.mk_ofNat, zero_add, Finset.mem_Ico, PNat.one_le,
          true_and] at this
        simp only [this, ↓reduceDite]
        rw [omg (h' := (eq_fpioc hN).symm) (i := i)]
        rw [sup_fpioc hN]
      by_cases h : updateSet x _ (pioc_ioc z) ∈ cylinder (fpioc 0 N) S
      · simpa [h] using this.2 h
      · simpa [h] using this.not.2 h
    · exact heq_fpioc hN
    · have : (1 : (transitionGraph X).path 0 ((fpioc 0 N).sup id).1 → ℝ≥0∞) = fun _ ↦ 1 := rfl
      rw [this, measurable_indicator_const_iff]
      apply mS.preimage
      apply measurable_pi_lambda
      intro a
      simp_all only
      apply Measurable.eval
      apply measurable_id'
  · apply MeasurableSet.nullMeasurableSet
    apply mS.preimage
    apply measurable_pi_lambda
    intro a
    simp_all only
    apply Measurable.eval
    apply measurable_id'
  · apply measurable_pi_lambda
    intro a
    simp_all only
    apply Measurable.eval
    apply measurable_id'
  · exact mS


theorem kerint_mono (k N : ℕ) (f g : ((n : ℕ+) → X n) → ℝ≥0∞) (hfg : f ≤ g) (x₀ : X 0) :
    kerint κ k N f x₀ ≤ kerint κ k N g x₀ := by
  intro x
  simp only [kerint]
  split_ifs
  · apply lintegral_mono
    exact fun _ ↦ hfg _
  · exact hfg _

theorem measurable_kerint (k N : ℕ) (f : ((n : ℕ+) → X n) → ℝ≥0∞) (hf : Measurable f) (x₀ : X 0) :
    Measurable (kerint κ k N f x₀) := by
  unfold kerint
  split_ifs with h
  · let g : ((i : Ioc k N) → X i) × ((n : ℕ+) → X n) → ℝ≥0∞ :=
      fun c ↦ f (updateSet c.2 _ (pioc_ioc c.1))
    let η : kernel ((n : ℕ+) → X n) ((i : Ioc k N) → X i) :=
      { val := fun x ↦ (transition κ).ker k N (fus x₀ (fun i ↦ x i.1))
        property := by
          intro s ms
          apply ms.preimage
          apply Measurable.comp (kernel.measurable _)
          apply (measurable_fus _ _).comp
          measurability }
    change Measurable fun x ↦ ∫⁻ z : (i : Ioc k N) → X i, g (z, x) ∂η x
    have : IsMarkovKernel η := by
      constructor
      intro x
      have : IsMarkovKernel ((transition κ).ker k N) := by
        apply markov_kerNat
        exact h
      apply this.isProbabilityMeasure _
    apply Measurable.lintegral_kernel_prod_left'
    apply hf.comp
    simp (config := { unfoldPartialApp := true }) only [updateSet, measurable_pi_iff]
    intro i
    by_cases h : i ∈ pioc k N <;> simp [h]
    · simp_all only [η]
      apply Measurable.eval
      apply Measurable.comp'
      apply measurable_pioc_ioc
      apply measurable_fst
    apply measurable_snd.eval
  · exact hf

theorem dependsOn_kerint (k N : ℕ) {f : ((n : ℕ+) → X n) → ℝ≥0∞} (hf : DependsOn f (pioc 0 N))
    (x₀ : X 0) : DependsOn (kerint κ k N f x₀) (pioc 0 k) := by
  intro x y hxy
  simp_rw [kerint]
  split_ifs with h
  · congrm ∫⁻ _, ?_ ∂((transition κ).ker k N ?_)
    · ext i
      simp only [fus]
      split_ifs with h'
      · rfl
      · simp_rw [Nat.ne_zero_iff_zero_lt] at h'
        apply hxy ⟨i.1, h'⟩
        simp [pioc]
        rw [← PNat.coe_lt_coe, PNat.mk_coe, PNat.mk_coe, Nat.lt_succ]
        exact i.2
    · apply hf
      intro i hi
      simp only [updateSet, pioc, mem_Ico, pioc_ioc, ioc_eq]
      split_ifs with h1
      · rfl
      · push_neg at h1
        have : i < k + 1 := by
          by_contra!
          rw [← PNat.coe_le_coe, PNat.mk_coe] at h1
          simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and] at hi
          exact h1 this hi
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


theorem kerint_self (k N : ℕ) (hkN : ¬k < N)
    (f : ((n : ℕ+) → X n) → ℝ≥0∞) (x₀ : X 0) (x : (i : ℕ+) → X i) :
    kerint κ k N f x₀ x = f x := by
  rw [kerint]
  simp [hkN]

-- lemma omg (s : Set ι) (x : (i : s) → X i) (i j : s) (h : i = j) (h' : X i = X j) :
--     cast h' (x i) = x j := by
--   subst h

-- def eq (k : ℕ) : ((i : Ioc k (k + 1)) → X i) ≃ᵐ X (k + 1) :=
--   { toFun := fun x ↦ x ⟨k + 1, right_mem_Ioc.2 <| Nat.lt_succ_self _⟩
--     invFun := fun x i ↦ by
--       have : i = k + 1 := by
--         rcases mem_Ioc.2 i.2 with ⟨h1, h2⟩
--         exact eq_of_le_of_not_lt h2 (by linarith)
--       exact cast (congrArg X this.symm) x
--     left_inv := by
--       simp only [Function.LeftInverse]
--       intro x
--       ext i
--        }

theorem updateSet_eq {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) {s : Set ι}
    (y : (i : s) → α i) : y = (fun i : s ↦ updateSet x s y i) := by
  ext i
  simp [updateSet, i.2]

theorem kerint_eq {a b : ℕ} (hab : a + 1 < b) {f : ((n : ℕ) → X n) → ℝ≥0∞} (hf : Measurable f)
    (x₀ : X 0) :
    kerint κ a b f x₀ = kerint κ a (a + 1) (kerint κ (a + 1) b f x₀) x₀ := by
  ext x
  simp [kerint, transition_ker, lt_trans a.lt_succ_self hab, hab]
  rw [kerNat_succ_left κ _ _ hab, compProd_eq _ _ _ (Nat.lt_succ_self _) hab,
    kernel.map_apply, lintegral_map (f := fun z ↦ f (updateSet x (pioc a b) (pioc_ioc z))),
    kernel.lintegral_compProd]
  congrm ∫⁻ _ : ?_, ∫⁻ _ : ?_, ?_ ∂(?_) ∂(?_)
  · rfl
  · rfl
  · rw [split_eq_comap, kernel.comap_apply]
    congr
    rw [el_eq, ProbabilityTheory.el]
    simp only [Nat.succ_eq_add_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    ext i
    simp only [fus, pioc, Nat.reduceAdd, PNat.mk_ofNat, Nat.succ_eq_add_one, updateSet, mem_Ico,
      pioc_ioc, ioc_eq, PNat.mk_coe]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · have := (PNat.coe_le_coe _ _).2 h3.1
      change a + 1 ≤ i.1 at this
      exfalso; linarith
    · rfl
    · have : i.1 ≤ a := by
        rw [h4]
        exact zero_le _
      exact (h1 this).elim
    · rfl
    · push_neg at h5
      rw [← PNat.coe_le_coe] at h5
      have hi := mem_Iic.1 i.2
      have : i.1 = a + 1 := by
        rcases Nat.le_succ_iff.1 hi with h | h'
        · exact (h1 h).elim
        · exact h'
      rw [← PNat.coe_le_coe] at h5
      simp at h5
      rw [this] at h5 hi
      exfalso
      linarith [h5 hi]
  · rfl
  · congr
    ext i
    rw [er_eq, ProbabilityTheory.er]
    simp only [updateSet, pioc, mem_Ico, pioc_ioc, Nat.succ_eq_add_one, ioc_eq,
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
  · apply hf.comp
    apply (measurable_updateSet _ _).comp
    apply (measurable_pioc_ioc _ _).comp
    apply (transitionGraph X).er_meas
  · apply hf.comp
    apply (measurable_updateSet _ _).comp
    apply measurable_pioc_ioc
  · apply (transitionGraph X).er_meas


theorem auxiliaire (f : ℕ → ((n : ℕ) → X n) → ℝ≥0∞) (N : ℕ → ℕ)
    (hcte : ∀ n, DependsOn (f n) (Iic (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) (k : ℕ)
    (x₀ : X 0)
    (anti : ∀ x, Antitone (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x))
    (l : ((n : ℕ) → X n) → ℝ≥0∞)
    (htendsto : ∀ x, Tendsto (fun n ↦ kerint κ (k + 1) (N n) (f n) x₀ x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞)
    (y : (n : Iic k) → X n)
    (hpos : ∀ x, ∀ n, ε ≤ kerint κ k (N n) (f n) x₀ (updateSet x _ y)) :
    ∃ z, ∀ x n,
    ε ≤ kerint κ (k + 1) (N n) (f n) x₀ (Function.update (updateSet x _ y) (k + 1) z) := by
  -- Shorter name for integrating over all the variables except the first `k + 1`.
  let F : ℕ → ((n : ℕ) → X n) → ℝ≥0∞ := fun n ↦ kerint κ (k + 1) (N n) (f n) x₀
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` over all the variables except the first `k` is the same as integrating
  -- `Fₙ` over the `k`-th variable.
  have f_eq x n : kerint κ k (N n) (f n) x₀ x = kerint κ k (k + 1) (F n) x₀ x := by
    simp only [F]
    by_cases h : k + 1 < N n
    · rw [kerint_eq κ h (mf n)]
    · by_cases h' : k + 1 = N n
      · rw [← h']
        congr
        ext x
        rw [kerint_self κ (k + 1) (k + 1) (by simp) (f n) x₀]
      · have : N n ≤ k := by
          rw [not_lt] at h
          rcases Nat.le_or_eq_of_le_succ h with a | b
          · exact a
          · exact (h' b.symm).elim
        rw [kerint_self _ _ _ (not_lt.2 this)]
        have : kerint κ (k + 1) (N n) (f n) x₀ = f n := by
          ext x
          rw [kerint_self _ _ _ h]
        rw [this, kerint]
        simp [Nat.lt_succ_self]
        have : IsMarkovKernel ((transition κ).ker k (k + 1)) := by
          apply markov_kerNat
          exact k.lt_succ_self
        rw [← mul_one (f n x),
          ← measure_univ (μ := ((transition κ).ker k (k + 1)) (fus x₀ (fun i ↦ x i.1))),
          ← lintegral_const]
        apply lintegral_congr
        intro z
        apply hcte
        intro i hi
        have : i ∉ pioc k (k + 1) := by
          simp [pioc] at hi ⊢
          intro hh
          have aux := (PNat.coe_lt_coe _ _).2 <| lt_of_le_of_lt hh hi
          simp_rw [PNat.mk_coe] at aux
          rw [Nat.lt_succ_iff_lt_or_eq] at aux
          rcases aux with a | b
          · exact (h a).elim
          · exact (h' b).elim
        simp [updateSet, this]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simp only [F, kerint]
    split_ifs with h
    · have : IsMarkovKernel ((transition κ).ker (k + 1) (N n)) := by
          apply markov_kerNat
          exact h
      rw [← mul_one bound,
        ← measure_univ (μ := ((transition κ).ker (k + 1) (N n)) (fus x₀ (fun i ↦ x i.1))),
        ← lintegral_const]
      apply lintegral_mono
      exact fun _ ↦ le_bound _ _
    · exact le_bound _ _
  -- By dominated convergence, the integral of `fₙ` with respect to all the variable except
  -- the `k` first converges to the integral of `l`.
  have tendsto_int x : Tendsto (fun n ↦ kerint κ k (N n) (f n) x₀ x) atTop
      (𝓝 (kerint κ k (k + 1) l x₀ x)) := by
    simp_rw [f_eq, kerint]
    simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceIte]
    · refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound) ?_ ?_ ?_ ?_
      · intro n
        apply (measurable_kerint κ (k + 1) (N n) (f n) (mf n) x₀).comp
        apply (measurable_updateSet _ _).comp
        apply measurable_pioc_ioc
      · exact fun n ↦ eventually_of_forall <| fun y ↦ F_le n _
      · rw [transition_ker]
        have := markov_kerNat κ (by linarith : k < k + 1)
        simp [fin_bound]
      · exact eventually_of_forall (fun _ ↦ tendstoF _)
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
          rw [← kerNat_succ κ k, ← transition_ker]
          nth_rw 1 [updateSet_eq x_ y]
          simp [kerint, k.lt_succ_self] at ε_le_lint
          apply ε_le_lint
      _ ≤ l (updateSet (updateSet x_ _ y) _ (pioc_ioc x')) := hx'
      _ = l (Function.update (updateSet x_ _ y) k.succPNat (x' ⟨k + 1, _⟩)) := by
          congr
          ext i
          simp [updateSet, pioc, pioc_ioc, ioc_eq, Function.update]
          split_ifs with h1 h2 h3 h4 h5 h6
          · aesop
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
  have aux : F n (Function.update (updateSet x_ _ y) k.succPNat x') =
      F n (Function.update (updateSet x _ y) k.succPNat x') := by
    simp only [F]
    apply dependsOn_kerint
    · exact hcte n
    intro i hi
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
  simp only [F] at aux
  rw [aux] at this
  exact this

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
      constructor
      · exact PNat.one_le _
      · have := Finset.le_sup (f := id) k.2
        rw [← PNat.coe_lt_coe]
        simp at this ⊢
        rw [← PNat.coe_le_coe] at this
        exact Nat.lt_succ_iff.2 this
    · simp only [Nat.reduceAdd, PNat.mk_ofNat, id_eq, PNat.mk_coe, Nat.succ_eq_add_one,
      eq_mp_eq_cast, cast_eq, eq_mpr_eq_cast]
      apply measurableSet_preimage
      apply measurable_pi_lambda
      intro a
      apply measurable_pi_apply
      exact mS
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

theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} (I : Finset ι)
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
    Tendsto (fun n ↦ kolContent
    (proj_family κ x₀) (A n)) atTop (𝓝 0) := by
  -- `Aₙ` is a cylinder, it can be writtent `cylinder sₙ Sₙ`.
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
    apply dependsOn_cylinder_indicator
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
    ext x
    simp only [kerint]
    split_ifs with h1 h2 h3
    · have heq := fun x ↦ congrFun heq x
      simp only [kerint, lt_of_lt_of_le h2 hK, ↓reduceIte, h2] at heq
      rw [transition_ker, kerNat_succ_right _ _ _ (lt_of_lt_of_le h2 hK),
        compProd_eq _ _ _ (lt_of_lt_of_le h2 hK) K.lt_succ_self, kernel.map_apply,
        lintegral_map (f := fun z ↦ χ n (updateSet x (pioc k (K + 1)) (pioc_ioc z))),
        kernel.lintegral_compProd, ← heq]
      · congrm ∫⁻ z, ?_ ∂_
        have aux (c : (i : Ioc K (K + 1)) → X i) :
            (A n).indicator 1 (updateSet x _ (pioc_ioc z)) =
            (A n).indicator (1 : ((n : ℕ+) → X n) → ℝ≥0∞)
              (updateSet x _ (pioc_ioc ((transitionGraph X).er k K (K + 1)
              (lt_of_lt_of_le h2 hK) K.lt_succ_self (z, c)))) := by
          apply χ_dep
          simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and, updateSet,
            pioc_ioc, ioc_eq, er_eq, ProbabilityTheory.er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
          intro i hi
          split_ifs with h1 h2 h3 h4 h5 <;>
            rw [← PNat.coe_le_coe, ← PNat.coe_lt_coe, PNat.mk_coe] at *
          · rw [not_le, ← Nat.succ_le] at h3
            exact (not_lt.2 h3 h1.2).elim
          · push_neg at h2
            exact (lt_irrefl i.1 <|
              lt_of_lt_of_le (lt_trans h1.2 (K + 1).lt_succ_self) (h2 h1.1)).elim
          · push_neg at h1
            exact (lt_irrefl i.1 <|
              lt_of_lt_of_le (lt_of_le_of_lt h5 K.lt_succ_self) (h1 h4.1)).elim
          · push_neg at h1
            rw [not_le] at h5
            apply Nat.succ_le_of_lt at h5
            rw [Nat.lt_succ] at hi
            exact (lt_irrefl K.succ <|
              lt_of_le_of_lt (le_trans h5 hi) (lt_of_le_of_lt hK K.lt_succ_self)).elim
        have : IsMarkovKernel (kerNat κ K (K + 1)) := by
          apply markov_kerNat
          exact K.lt_succ_self
        have : IsMarkovKernel ((transitionGraph X).split k K (K + 1) (lt_of_lt_of_le h2 hK)
            (kerNat κ K (K + 1))) := by
          rw [split]
          infer_instance
        rw [← mul_one ((A n).indicator 1 (updateSet x _ (pioc_ioc z))),
          ← measure_univ (μ := ((transitionGraph X).split k K (K + 1) (lt_of_lt_of_le h2 hK)
            (kerNat κ K (K + 1))) (fus x₀ (fun i ↦ x i.1), z)),
          ← lintegral_const]
        apply lintegral_congr
        exact fun c ↦ (aux c).symm
      · apply (mχ _).comp
        apply (measurable_updateSet _ _).comp
        apply (measurable_pioc_ioc _ _).comp
        apply (transitionGraph X).er_meas
      · apply (mχ _).comp
        apply (measurable_updateSet _ _).comp
        apply measurable_pioc_ioc
      · apply (transitionGraph X).er_meas
    · have : IsMarkovKernel ((transition κ).ker k (K + 1)) := by
        apply markov_kerNat
        exact h1
      rw [← mul_one (χ n x),
        ← measure_univ (μ := ((transition κ).ker k (K + 1)) (fus x₀ (fun i ↦ x i.1))),
        ← lintegral_const]
      apply lintegral_congr
      intro a
      apply χ_dep
      simp only [pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and, updateSet, pioc_ioc,
        ioc_eq, dite_eq_right_iff]
      rintro i hi1 ⟨hi2, hi3⟩
      rw [← PNat.coe_le_coe] at hi2
      rw [← PNat.coe_lt_coe] at hi1
      exact (h2 <| Nat.lt_of_succ_lt_succ <| lt_of_le_of_lt hi2 hi1).elim
    · rw [Nat.lt_succ, not_le] at h1
      exfalso; linarith [lt_trans h1 h3]
    · rfl
  -- the integral of `χₙ` over all the variables except the first `k` ones is non-increasing.
  have anti_lma k x : Antitone fun n ↦ kerint κ k (N n) (χ n) x₀ x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    apply kerint_mono _ _ _ _ _ (χ_anti hmn)
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
    fun k y h ↦ auxiliaire κ χ N χ_dep mχ 1 (by norm_num) χ_le k x₀ (anti_lma (k + 1))
      (l (k + 1)) (hl (k + 1)) ε y h
  let z := key ind
  have crucial : ∀ k x n, ε ≤ kerint κ k (N n) (χ n) x₀
      (updateSet x (pioc 0 k) (fun i ↦ z i)) := by
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
        · aesop_subst h2
          simp_all only [le_refl, implies_true, PNat.mk_coe, χ, z]
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
    rw [← this, kolContent_eq_kerint _ _ (mS n) x₀ x]
    exact hN n

    -- exact kolContent_eq_lmarginal μ (Finset.Icc 0 (N n)) (mS n) x
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
      simp only [updateSet, pioc, zero_add, PNat.mk_ofNat, mem_Ico, PNat.one_le, true_and,
        Nat.reduceAdd, dite_eq_ite, ite_self]
      -- rw [Finset.Icc_eq_empty (by simp), lmarginal_empty]
      -- congr
      -- ext i
      -- by_cases h : i ∈ Finset.Ico 0 (N n + 1) <;> simp [Function.updateFinset, h]
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
    rw [kerint]
    simp only [hN, ↓reduceIte]
    have : IsMarkovKernel ((transition κ).ker 0 N) := by
      apply markov_kerNat
      exact hN
    nth_rw 2 [← mul_one 1, ← measure_univ (μ := (transition κ).ker 0 N (fus x₀ fun i ↦ x_ i.1))]
    rw [← lintegral_const]
    apply lintegral_mono
    apply Set.indicator_le
    simp
  · intro s hs anti_s inter_s
    exact firstLemma κ s hs anti_s inter_s x₀

noncomputable def ionescu_tulcea_fun (x₀ : X 0) : Measure ((n : ℕ+) → X n) := by
  exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (kolContent (proj_family κ x₀))
    (kolContent_sigma_subadditive_proj κ x₀)

theorem proba_ionescu (x₀ : X 0) : IsProbabilityMeasure (ionescu_tulcea_fun κ x₀) := by
  constructor
  rw [← cylinder_univ {1}, ionescu_tulcea_fun, Measure.ofAddContent_eq,
      fun x₀ ↦ kolContent_congr (proj_family κ x₀) _ rfl MeasurableSet.univ]
  simp only [family]
  rw [← kernel.map_apply]
  have : IsMarkovKernel ((transition κ).ker 0 (Finset.sup ({1} : Finset ℕ+) id).1) := by
    apply markov_kerNat
    simp
  · simp
  · apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'
  · simp only [mem_cylinders, exists_prop, forall_const]
    exact ⟨{1}, univ, MeasurableSet.univ, rfl⟩
  · simp only [mem_cylinders, exists_prop, forall_const]
    exact ⟨{1}, univ, MeasurableSet.univ, rfl⟩


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
    apply Measure.measurable_measure.1
    apply (Measure.measurable_map _ _).comp
    · apply (kernel.measurable _).comp
      apply zer.measurable_toFun
    · apply measurable_pi_lambda
      intro a
      apply Measurable.eval
      apply measurable_id'
    · exact mS
  · have this x₀ : ionescu_tulcea_fun κ x₀ tᶜ = 1 - ionescu_tulcea_fun κ x₀ t := by
      have := fun x₀ ↦ proba_ionescu κ x₀
      rw [measure_compl mt]
      · simp
      · exact measure_ne_top _ _
    simp_rw [this]
    exact Measurable.const_sub ht _
  · simp_rw [measure_iUnion disf mf]
    exact Measurable.ennreal_tsum hf

noncomputable def ionescu_tulcea_kernel : kernel (X 0) ((n : ℕ+) → X n) :=
  { val := ionescu_tulcea_fun κ
    property := measurable_ionescu κ }

instance : IsMarkovKernel (ionescu_tulcea_kernel κ) := IsMarkovKernel.mk fun _ ↦ proba_ionescu _ _

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
    split_ifs
    · aesop
    · rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun n ↦ ?_)
    by_cases h : n = 0
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      aesop_subst h
      apply measurable_fst
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_
    · apply measurable_pi_apply
    · exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

noncomputable def ionescu_ker : kernel (X 0) ((n : ℕ) → X n) :=
  kernel.map
    ((kernel.deterministic id measurable_id) ×ₖ (ionescu_tulcea_kernel κ))
    er'' er''.measurable_toFun



def equiv_Icc (a b : ℕ) : ((i : Finset.Icc a b) → X i) ≃ᵐ ((i : Icc a b) → X i) where
  toFun := by
    intro x ⟨i, hi⟩
    rw [← Finset.coe_Icc, Finset.mem_coe] at hi
    exact x ⟨i, hi⟩
  invFun := by
    intro x ⟨i, hi⟩
    rw [← Finset.mem_coe, Finset.coe_Icc] at hi
    exact x ⟨i, hi⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ by simp
  measurable_toFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem integral_dep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {f : ((i : Icc 0 N) → X i) → E} (hf : StronglyMeasurable f)
    (x₀ : X 0) :
    ∫ y, f ((fun x (i : Icc 0 N) ↦ x i) y) ∂ionescu_ker κ x₀ =
    ∫ y, f y ∂ker κ N x₀ := by
