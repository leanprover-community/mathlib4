/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Annexe

open Finset ENNReal ProbabilityTheory MeasureTheory

section compProd

lemma measurable_cast {X Y : Type _} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] (h : X = Y)
    (hm : HEq mX mY) :
    Measurable (cast h) := by
  subst h
  subst hm
  exact measurable_id

@[simp]
lemma kernel.map_zero_left (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (f : β → γ) (hf : Measurable f) :
    kernel.map (0 : kernel α β) f hf = 0 := by
  ext a s
  rw [kernel.map_apply]
  simp

variable {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]

section equivs

def e (n : ℕ) : (X (n + 1)) ≃ᵐ ((i : Ioc n (n + 1)) → X i) where
  toFun := fun x i ↦ (mem_Ioc_succ.1 i.2).symm ▸ x
  invFun := fun x ↦ x ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩ = i := by
      simp [(mem_Ioc_succ.1 i.2).symm]
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨n + 1, mem_Ioc.2 ⟨n.lt_succ_self, le_refl (n + 1)⟩⟩ = i := by
      simp [(mem_Ioc_succ.1 i.2).symm]
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

def el (m n : ℕ) (hmn : m ≤ n) :
    ((i : Iic m) → X i) × ((i : Ioc m n) → X i) ≃ᵐ ((i : Iic n) → X i) where
  toFun := fun p x ↦ if h : x ≤ m then p.1 ⟨x, mem_Iic.2 h⟩
    else p.2 ⟨x, mem_Ioc.2 ⟨not_le.mp h, mem_Iic.1 x.2⟩⟩
  invFun := fun p ↦ ⟨fun x ↦ p ⟨x, mem_Iic.2 <| (mem_Iic.mp x.2).trans hmn⟩,
    fun x ↦ p ⟨x, mem_Iic.2 (mem_Ioc.mp x.2).2⟩⟩
  left_inv := fun p ↦ by
    ext x
    · simp only
      rw [dif_pos (mem_Iic.mp x.2)]
    · simp only
      rw [dif_neg (not_le.mpr (mem_Ioc.mp x.2).1)]
  right_inv := fun p ↦ by
    ext x
    simp only
    split_ifs <;> rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun (x : Iic n) ↦ ?_)
    by_cases h : x ≤ m
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      exact measurable_fst.eval
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

def er (i j k : ℕ) (hij : i < j) (hjk : j ≤ k) :
    (∀ x : Ioc i j, X x) × (∀ x : Ioc j k, X x) ≃ᵐ ∀ x : Ioc i k, X x where
  toFun := fun p x ↦ if h : x ≤ j then p.1 ⟨x, mem_Ioc.2 ⟨(mem_Ioc.1 x.2).1, h⟩⟩
    else p.2 ⟨x, mem_Ioc.2 ⟨not_le.mp h, (mem_Ioc.1 x.2).2⟩⟩
  invFun := fun p ↦ ⟨fun x ↦ p ⟨x, mem_Ioc.2 ⟨(mem_Ioc.1 x.2).1, (mem_Ioc.1 x.2).2.trans hjk⟩⟩,
    fun x ↦ p ⟨x, mem_Ioc.2 ⟨hij.trans (mem_Ioc.1 x.2).1, (mem_Ioc.1 x.2).2⟩⟩⟩
  left_inv := fun p ↦ by
    ext x
    · simp only
      rw [dif_pos (mem_Ioc.1 x.2).2]
    · simp only
      rw [dif_neg (not_le.mpr (mem_Ioc.1 x.2).1)]
  right_inv := fun p ↦ by
    ext x
    simp only
    split_ifs <;> rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun x ↦ ?_)
    by_cases h : x ≤ j
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      exact measurable_fst.eval
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

lemma el_assoc {i j k : ℕ} (hij : i < j) (hjk : j ≤ k) (a : (x : Iic i) → X ↑x)
    (b : (x : Ioc i j) → X ↑x) (c : (x : Ioc j k) → X ↑x) :
    el j k hjk (el i j hij.le (a, b), c)
      = el i k (hij.le.trans hjk) (a, er i j k hij hjk (b, c)) := by
  ext x
  simp only [el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er]
  split_ifs with h _ h3
  · rfl
  · rfl
  · exfalso; exact h (h3.trans hij.le)
  · rfl

lemma er_assoc {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k ≤ l)
    (b : (x : Ioc i j) → X ↑x) (c : (x : Ioc j k) → X ↑x) (d : (x : Ioc k l) → X ↑x) :
    er i j l hij (hjk.le.trans hkl) (b, er j k l hjk hkl (c, d))
      = er i k l (hij.trans hjk) hkl (er i j k hij hjk.le (b, c), d) := by
  ext x
  simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er]
  split_ifs with h h2
  · rfl
  · exfalso; exact h2 (h.trans hjk.le)
  · rfl
  · rfl

end equivs

def e_path_eq {i j k : ℕ} (h : j = k) : ((x : Ioc i j) → X x) ≃ᵐ ((x : Ioc i k) → X x) :=
  MeasurableEquiv.cast (by rw [h]) (by rw [h])

theorem e_path_eq_eq {i j : ℕ} :
    e_path_eq (rfl : j = j) = MeasurableEquiv.refl ((x : Ioc i j) → X x) := by aesop

def split (i j k : ℕ) (hij : i < j)
    (κ : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) :
    kernel (((x : Iic i) → X x) × ((x : Ioc i j) → X x)) ((x : Ioc j k) → X x) :=
  kernel.comap κ (el i j hij.le) (el i j hij.le).measurable

lemma split_eq_comap (i j k : ℕ) (hij : i < j)
    (κ : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) :
    split i j k hij κ = kernel.comap κ (el i j hij.le) (el i j hij.le).measurable := rfl

instance {i j k : ℕ} (hij : i < j) (κ : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))
    [IsSFiniteKernel κ] :
    IsSFiniteKernel (split i j k hij κ) := by
  rw [split]
  infer_instance

instance {i j k : ℕ} (hij : i < j) (κ : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))
    [IsFiniteKernel κ] :
    IsFiniteKernel (split i j k hij κ) := by
  rw [split]
  infer_instance

@[simp]
lemma split_zero (i j k : ℕ) (hij : i < j) :
    split i j k hij (0 : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) = 0 := by
  rw [split] -- todo: kernel.comap_zero missing as simp lemma
  ext1 a
  rw [kernel.comap_apply, kernel.zero_apply, kernel.zero_apply]

open Classical

noncomputable
def compProd {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) :
    kernel ((x : Iic i) → X x) ((x : Ioc i k) → X x) :=
  if h : i < j ∧ j < k
    then kernel.map (κ ⊗ₖ split i j k h.1 η) (er i j k h.1 h.2.le) (er i j k h.1 h.2.le).measurable
    else 0

lemma compProd_eq {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) (hij : i < j) (hjk : j < k) :
    compProd κ η = kernel.map (κ ⊗ₖ split i j k hij η) (er i j k hij hjk.le)
      (er i j k hij hjk.le).measurable := by
  rw [compProd, dif_pos]
  exact ⟨hij, hjk⟩

instance {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) :
    IsSFiniteKernel (compProd κ η) := by
  rw [compProd]
  split_ifs <;> infer_instance

instance {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    [IsFiniteKernel κ]
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))
    [IsFiniteKernel η] :
    IsFiniteKernel (compProd κ η) := by
  rw [compProd]
  split_ifs <;> infer_instance

notation κ " ⊗ₖ' " η => compProd κ η

lemma compProd_apply' {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hij : i < j) (hjk : j < k) (a : (x : Iic i) → X x) {s : Set ((x : Ioc i k) → X x)}
    (hs : MeasurableSet s) :
    (κ ⊗ₖ' η) a s
      = ∫⁻ b, η (el i j hij.le (a, b)) {c | (b, c) ∈ er i j k hij hjk.le ⁻¹' s} ∂(κ a) := by
  rw [compProd_eq _ _ hij hjk, kernel.map_apply' _ _ _ hs,
    kernel.compProd_apply _ _ _ ((er _ _ _ _ _).measurable hs)]
  simp_rw [split, kernel.comap_apply]

@[simp]
lemma compProd_zero_right {i j : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) (k : ℕ) :
    (κ ⊗ₖ' (0 : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))) = 0 := by
  rw [compProd]
  split_ifs
  · simp only [split_zero, kernel.compProd_zero_right, kernel.map_zero_left]
  · rfl

@[simp]
lemma compProd_zero_left {j k : ℕ} (i : ℕ) (κ : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) :
    ((0 : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) ⊗ₖ' κ) = 0 := by
  rw [compProd]
  split_ifs
  · simp only [kernel.compProd_zero_left, kernel.map_zero_left]
  · rfl

lemma compProd_undef_left {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x)) (hij : i < j) (hjk : j < k)
    (h : ¬ IsSFiniteKernel κ) :
    (κ ⊗ₖ' η) = 0 := by
  rw [compProd_eq _ _ hij hjk, kernel.compProd_of_not_isSFiniteKernel_left _ _ h]
  simp

lemma compProd_assoc {i j k l : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (η : kernel ((x : Iic j) → X x) ((x : Ioc j k) → X x))
    (ξ : kernel ((x : Iic k) → X x) ((x : Ioc k l) → X x))
    [IsSFiniteKernel η] [IsSFiniteKernel ξ]
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    (κ ⊗ₖ' (η ⊗ₖ' ξ)) = (κ ⊗ₖ' η) ⊗ₖ' ξ := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_undef_left _ _ hij (hjk.trans hkl) hκ, compProd_undef_left _ _ hij hjk hκ]
    simp
  ext a s hs
  have h_comp_det : ∀ b, ξ (el i k (hij.trans hjk).le (a, b))
      = (ξ ∘ₖ kernel.deterministic (el i k (hij.trans hjk).le)
          (el i k (hij.trans hjk).le).measurable) (a, b) := by
    intro b
    rw [kernel.comp_deterministic_eq_comap, kernel.comap_apply]
  have h_meas_comp : Measurable fun b ↦
      ξ (el i k (hij.trans hjk).le (a, b))
        {c | (b, c) ∈ er i k l (hij.trans hjk) hkl.le ⁻¹' s} := by
    simp_rw [h_comp_det]
    exact kernel.measurable_kernel_prod_mk_left' ((er _ _ _ _ _).measurable hs) a
  rw [compProd_apply' _ _ hij (hjk.trans hkl) _ hs,
    compProd_apply' _ _ (hij.trans hjk) hkl _ hs, compProd_eq _ _ hjk hkl,
    compProd_eq _ _ hij hjk, kernel.map_apply, lintegral_map h_meas_comp (er _ _ _ _ _).measurable]
  have : ∀ b, MeasurableSet {c | (b, c) ∈ er i j l hij (hjk.trans hkl).le ⁻¹' s} :=
    fun b ↦ (@measurable_prod_mk_left _ _ inferInstance _ b) ((er _ _ _ _ _).measurable hs)
  simp_rw [kernel.map_apply' _ _ _ (this _)]
  have : ∀ b, MeasurableSet
      (er j k l hjk hkl.le ⁻¹' {c | (b, c) ∈ er i j l hij (hjk.trans hkl).le ⁻¹' s}) :=
    fun b ↦ (er _ _ _ _ _).measurable (this b)
  simp_rw [kernel.compProd_apply _ _ _ (this _), split, kernel.comap_apply]
  rw [kernel.lintegral_compProd]
  swap; exact h_meas_comp.comp (er i j k hij hjk.le).measurable
  simp only [kernel.comap_apply, el_assoc, Set.mem_preimage, Set.preimage_setOf_eq,
    Set.mem_setOf_eq, er_assoc]
  simp_rw [el_assoc hij hjk.le]

noncomputable
def castPath {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) (h : j = k) :
    kernel ((x : Iic i) → X x) ((x : Ioc i k) → X x) :=
  kernel.map κ (e_path_eq h) (MeasurableEquiv.measurable _)

lemma castPath_apply {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) (h : j = k)
    (a : (x : Iic i) → X x) (s : Set ((x : Ioc i k) → X x)) (hs : MeasurableSet s) :
    castPath κ h a s = κ a (e_path_eq h ⁻¹' s) := by
  rw [castPath, kernel.map_apply' _ _ _ hs]

instance {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) (h : j = k)
    [IsSFiniteKernel κ] :
    IsSFiniteKernel (castPath κ h) := by
  rw [castPath]; infer_instance

instance {i j k : ℕ} (κ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) (h : j = k)
    [IsFiniteKernel κ] :
    IsFiniteKernel (castPath κ h) := by
  rw [castPath]; infer_instance

section kerNat

variable {i j k : ℕ}

noncomputable
def kerInterval (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))) (k : ℕ) :
    kernel ((x : Iic i) → X x) ((x : Ioc i k) → X x) := by
  induction k with
  | zero => exact 0
  | succ k κ_k => exact if h : j = k + 1 then castPath κ₀ h else
    (κ_k ⊗ₖ' (kernel.map (κ k) (e k) (e k).measurable))

@[simp]
lemma kerInterval_zero (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))) :
    kerInterval κ₀ κ 0 = 0 := rfl

lemma kerInterval_succ {κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)}
    {κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))} (k : ℕ) :
    kerInterval κ₀ κ (k + 1)
      = if h : j = k + 1 then castPath κ₀ h else
        ((kerInterval κ₀ κ k) ⊗ₖ' (kernel.map (κ k) (e k) (e k).measurable)) := rfl

lemma kerInterval_succ_of_ne {κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)}
    {κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))} (h : j ≠ k + 1) :
    kerInterval κ₀ κ (k + 1) =
      (kerInterval κ₀ κ k) ⊗ₖ' (kernel.map (κ k) (e k) (e k).measurable) := by
  rw [kerInterval_succ, dif_neg h]

lemma kerInterval_succ_right {κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)}
    {κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))} (h : j ≤ k) :
    kerInterval κ₀ κ (k + 1) =
      (kerInterval κ₀ κ k) ⊗ₖ' (kernel.map (κ k) (e k) (e k).measurable) := by
  rw [kerInterval_succ, dif_neg (by linarith)]

lemma kerInterval_of_lt {κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)}
    {κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))} (h : k < j) :
    kerInterval κ₀ κ k = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [kerInterval_succ, dif_neg h.ne', ih (by linarith)]
      simp

lemma kerInterval_of_eq (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x))
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))) (hj : 0 < j) :
    kerInterval κ₀ κ j = κ₀ := by
  cases j with
  | zero => exfalso; linarith
  | succ n =>
    rw [kerInterval_succ, dif_pos rfl]
    ext a s hs
    rw [castPath_apply _ _ _ _ hs]
    rfl

instance (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) [h₀ : IsSFiniteKernel κ₀]
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))) (k : ℕ) :
    IsSFiniteKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => rw [kerInterval_zero]; infer_instance
  | succ n _ => rw [kerInterval_succ]; split_ifs <;> infer_instance

instance (κ₀ : kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x)) [h₀ : IsFiniteKernel κ₀]
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1)))
    [∀ k, IsFiniteKernel (κ k)] (k : ℕ) :
    IsFiniteKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => rw [kerInterval_zero]; infer_instance
  | succ n _ => rw [kerInterval_succ]; split_ifs <;> infer_instance

noncomputable
def kerNat (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1))) (i j : ℕ) :
    kernel ((x : Iic i) → X x) ((x : Ioc i j) → X x) :=
  if i < j then kerInterval (kernel.map (κ i) (e i) (e i).measurable) κ j else 0

theorem kerNat_cast (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    (i j k : ℕ)
    (hjk : j = k) : kerNat κ i k = castPath (kerNat κ i j) hjk := by
  subst hjk
  simp_rw [kerNat]
  split_ifs with h
  · rw [castPath]
    conv_rhs =>
      enter [2]
      rw [e_path_eq_eq]
    simp [MeasurableEquiv.refl]
  · simp [castPath]

lemma kerNat_eq (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    (hij : i < j) :
    kerNat κ i j = kerInterval (kernel.map (κ i) (e i) (e i).measurable) κ j :=
  dif_pos hij

lemma kerNat_of_ge (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1))) (hij : j ≤ i) :
    kerNat κ i j = 0 :=
  dif_neg (not_lt.mpr hij)

instance (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1))) [∀ i, IsSFiniteKernel (κ i)] :
    IsSFiniteKernel (kerNat κ i j) := by
  rw [kerNat]; split_ifs <;> infer_instance

instance (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1))) [∀ i, IsFiniteKernel (κ i)] :
    IsFiniteKernel (kerNat κ i j) := by
  rw [kerNat]; split_ifs <;> infer_instance

lemma kerNat_succ (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1))) (i : ℕ) :
    kerNat κ i (i + 1) = kernel.map (κ i) (e i) (e i).measurable := by
  rw [kerNat_eq _ (Nat.lt_succ_self _), kerInterval_of_eq _ _ (by linarith)]

lemma kerNat_succ_right (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    (i j : ℕ) (hij : i < j) :
    kerNat κ i (j + 1) = (kerNat κ i j) ⊗ₖ' (kerNat κ j (j + 1)) := by
  rw [kerNat_eq _ (hij.trans (Nat.lt_succ_self _)),
    kerInterval_succ_right (Nat.succ_le_iff.mpr hij)]
  congr
  · rw [kerNat_eq _ hij]
  · rw [kerNat_succ κ j]

lemma kerNat_succ_left (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (i j : ℕ) (hij : i + 1 < j) :
    kerNat κ i j = (kerNat κ i (i + 1)) ⊗ₖ' (kerNat κ (i + 1) j) := by
  induction j with
  | zero =>
    rw [kerNat_of_ge κ (Nat.zero_le _), kerNat_of_ge κ (Nat.zero_le _)]
    simp
  | succ j hj => cases le_or_lt j (i + 1) with
    | inl h =>
      have hj_eq : j = i + 1 := le_antisymm h (Nat.succ_lt_succ_iff.mp (by convert hij))
      rw [kerNat_succ_right]
      · congr
      · rw [hj_eq]; exact Nat.lt_succ_self i
    | inr h =>
      rw [kerNat_succ_right _ _ _ (Nat.succ_lt_succ_iff.mp hij), hj h,
        kerNat_succ_right _ _ j h,
        compProd_assoc (kerNat κ i (i + 1)) (kerNat κ (i + 1) j)
          (kerNat κ j (j + 1)) (Nat.lt_succ_self i) h (Nat.lt_succ_self j)]

theorem compProd_kerNat (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (hij : i < j) (hjk : j < k) :
    ((kerNat κ i j) ⊗ₖ' (kerNat κ j k)) = kerNat κ i k := by
  cases k with
  | zero => exfalso; linarith
  | succ k =>
    refine Nat.decreasingInduction' ?_ (Nat.lt_succ_iff.mp hjk) ?_
    · intro l hlk hjl h
      rw [← h, kerNat_succ_left _ l]
      swap; linarith
      rw [kerNat_succ_right _ i _ (hij.trans_le hjl),
        compProd_assoc _ _ _ (hij.trans_le hjl) (Nat.lt_succ_self l)]
      linarith
    · rw [kerNat_succ_right _ _ _ (hij.trans_le (Nat.lt_succ_iff.mp hjk))]

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
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1))) [∀ k, IsMarkovKernel (κ k)]
    (hij : i < j) (hjk : j ≤ k) :
    IsMarkovKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => linarith
  | succ n hn =>
    rw [kerInterval_succ]
    split_ifs with h
    · exact isMarkovKernel_castPath _ _
    · have _ := hn (by omega)
      exact isMarkovKernel_compProd _ _ (by omega) n.lt_succ_self

theorem isMarkovKernel_kerNat {i j : ℕ}
    (κ : ∀ k, kernel ((x : Iic k) → X x) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
    IsMarkovKernel (kerNat κ i j) := by
  simp only [kerNat, hij, ↓reduceIte]
  exact isMarkovKernel_kerInterval _ _ i.lt_succ_self (Nat.succ_le.2 hij)

theorem proj_kerNat (κ : (k : ℕ) → kernel ((x : Iic k) → X x) (X (k + 1)))
    [∀ i, IsMarkovKernel (κ i)]
    {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) :
    kernel.map (kerNat κ a c)
      (fun (x : ((i : Ioc a c) → X i)) (i : Ioc a b) ↦ x ⟨i.1, Ioc_subset_Ioc_right hbc i.2⟩)
      (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)) = kerNat κ a b := by
  rcases eq_or_lt_of_le hbc with hbc | hbc
  · cases hbc
    exact kernel.map_id _
  · ext x s ms
    rw [kernel.map_apply' _ _ _ ms, ← compProd_kerNat κ hab hbc,
      compProd_apply' _ _ hab hbc _ (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) ms)]
    simp_rw [Set.preimage_preimage]
    refine Eq.trans (b := ∫⁻ b, s.indicator 1 b ∂kerNat κ a b x) ?_ ?_
    · refine lintegral_congr fun b ↦ ?_
      simp only [el, nonpos_iff_eq_zero, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er,
        Set.mem_preimage, Set.indicator, Pi.one_apply]
      split_ifs with hb
      · have := isMarkovKernel_kerNat κ hbc
        convert measure_univ
        · ext c
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          convert hb using 1
          ext i
          simp [(mem_Ioc.1 i.2).2]
        · infer_instance
      · convert measure_empty
        · ext c
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          convert hb using 2
          ext i
          simp [(mem_Ioc.1 i.2).2]
        · infer_instance
    · rw [← one_mul (((kerNat κ a b) x) s)]
      exact lintegral_indicator_const ms _

end kerNat

end compProd

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (κ : (n : ℕ) → kernel ((i : Iic n) → X i) (X (n + 1)))

abbrev proj : (n : ℕ) → ((n : ℕ) → X n) → (i : Iic n) → X i := fun _ x i ↦ x i

theorem meas_proj (n : ℕ) : Measurable (@proj X n) := measurable_proj _

lemma Finset.sub_Iic (I : Finset ℕ) : I ⊆ (Iic (I.sup id)) :=
  fun _ hi ↦ mem_Iic.2 <| le_sup (f := id) hi

abbrev projection {I J : Finset ℕ} (hIJ : I ⊆ J) : ((i : J) → X i) → (i : I) → X i :=
  fun x i ↦ x ⟨i.1, hIJ i.2⟩

theorem projection_comp_projection {I J K : Finset ℕ} (hIJ : I ⊆ J) (hJK : J ⊆ K) :
    (projection (X := X) hIJ) ∘ (projection hJK) = projection (hIJ.trans hJK) := by
  ext x i
  simp

theorem measurable_projection {I J : Finset ℕ} (hIJ : I ⊆ J) :
    Measurable (projection (X := X) hIJ) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

noncomputable def composition (a b : ℕ) : kernel ((i : Iic a) → X i) ((i : Iic b) → X i) :=
  if hab : a < b
    then kernel.map ((kernel.deterministic id measurable_id) ×ₖ kerNat κ a b)
      (el a b hab.le) (el a b hab.le).measurable
    else kernel.deterministic
      (fun (x : (i : Iic a) → X i) (i : Iic b) ↦ x ⟨i.1, Iic_subset_Iic.2 (not_lt.1 hab) i.2⟩)
      (measurable_proj₂' ..)

theorem composition_lt {a b : ℕ} (hab : a < b) :
    composition κ a b =
      kernel.map ((kernel.deterministic id measurable_id) ×ₖ kerNat κ a b)
        (el a b hab.le) (el a b hab.le).measurable := by
  rw [composition, dif_pos hab]

theorem composition_le {a b : ℕ} (hab : b ≤ a) :
    composition κ a b =
      kernel.deterministic (projection (Iic_subset_Iic.2 hab)) (measurable_projection _) := by
  rw [composition, dif_neg (not_lt.2 hab)]

variable [∀ n, IsMarkovKernel (κ n)]

instance (a b : ℕ) : IsMarkovKernel (composition κ a b) := by
  rw [composition]
  split_ifs with hab
  · have := isMarkovKernel_kerNat κ hab
    infer_instance
  · infer_instance

theorem compo_proj (a : ℕ) {b c : ℕ} (hbc : b ≤ c) :
    kernel.map (composition κ a c) (projection (Iic_subset_Iic.2 hbc)) (measurable_projection _) =
    composition κ a b := by
  unfold composition
  split_ifs with h1 h2 h3
  · have : (projection (X := X) (Iic_subset_Iic.2 hbc)) ∘ (el a c h1.le) =
        (el a b h2.le) ∘ (Prod.map id (projection (Ioc_subset_Ioc_right hbc))) := by
      ext x i
      simp [el]
    rw [kernel.map_map, kernel.map_eq _ _ this, ← kernel.map_map, kernel.map_prod, kernel.map_id,
      proj_kerNat _ h2 hbc]
  · have : (projection (X := X) (Iic_subset_Iic.2 hbc)) ∘ (el a c h1.le) =
          (projection (Iic_subset_Iic.2 (not_lt.1 h2))) ∘ Prod.fst := by
      ext x i
      simp [el, projection, (mem_Iic.1 i.2).trans (not_lt.1 h2)]
    have _ := isMarkovKernel_kerNat κ h1
    rw [kernel.map_map, kernel.map_eq _ _ this, ← kernel.map_map, kernel.map_prod_fst,
      kernel.map_deterministic]
    rfl
    exact measurable_projection _
  · omega
  · rw [kernel.map_deterministic]
    congr

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

theorem composition_comp (c : ℕ) {a b : ℕ} (h : a ≤ b) :
    (composition κ b c) ∘ₖ (composition κ a b) = composition κ a c := by
  by_cases hab : a < b <;> by_cases hbc : b < c <;> by_cases hac : a < c <;> try omega
  · ext x s ms
    rw [composition_lt κ hab, composition_lt κ hbc, composition_lt κ hac,
      kernel.comp_apply' _ _ _ ms, kernel.lintegral_map, kernel.lintegral_prod,
      kernel.map_apply' _ _ _ ms, kernel.prod_apply', kernel.lintegral_deterministic',
      kernel.lintegral_deterministic', ← compProd_kerNat κ hab hbc, compProd_apply' _ _ hab hbc]
    · congr with y
      rw [kernel.map_apply', kernel.prod_apply', kernel.lintegral_deterministic']
      · congr with z
        simp only [el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Set.mem_preimage,
          Set.mem_setOf_eq, er, Set.preimage_setOf_eq]
        congrm (fun i ↦ ?_) ∈ s
        have := mem_Iic.1 i.2
        split_ifs <;> try rfl
        omega
      · exact measurable_measure_prod_mk_left ((el b c hbc.le).measurable ms)
      · exact (el b c hbc.le).measurable ms
      · exact ms
    · exact measurable_prod_mk_left ((el a c hac.le).measurable ms)
    · exact measurable_measure_prod_mk_left ((el a c hac.le).measurable ms)
    · apply Measurable.lintegral_prod_right'
        (f := fun x ↦ (kernel.map _ _ _) _ _)
      exact (kernel.measurable_coe _ ms).comp (el a b hab.le).measurable
    · exact (el a c hac.le).measurable ms
    · exact (kernel.measurable_coe _ ms).comp (el a b hab.le).measurable
    · exact kernel.measurable_coe _ ms
  · rw [composition_le κ (not_lt.1 hbc), kernel.deterministic_comp_eq_map,
      compo_proj κ a (not_lt.1 hbc)]
  · rw [composition_le κ (not_lt.1 hbc), kernel.deterministic_comp_eq_map,
      compo_proj κ a (not_lt.1 hbc)]
  · have : a = b := by omega
    cases this
    rw [composition_le κ (le_refl a), kernel.comp_deterministic_eq_comap]
    convert kernel.comap_id (composition κ a c)
  · rw [composition_le κ (not_lt.1 hbc), kernel.deterministic_comp_eq_map,
      compo_proj κ a (not_lt.1 hbc)]

theorem composition_comp' (a : ℕ) {b c : ℕ} (h : c ≤ b) :
    (composition κ b c) ∘ₖ (composition κ a b) = composition κ a c := by
  by_cases hab : a < b <;> by_cases hbc : b < c <;> by_cases hac : a < c <;> try omega
  · rw [composition_le κ (not_lt.1 hbc), kernel.deterministic_comp_eq_map,
      compo_proj κ a (not_lt.1 hbc)]
  · rw [composition_le κ (not_lt.1 hbc), kernel.deterministic_comp_eq_map,
      compo_proj κ a (not_lt.1 hbc)]
  · rw [composition_le κ (not_lt.1 hbc), kernel.deterministic_comp_eq_map,
      compo_proj κ a (not_lt.1 hbc)]
