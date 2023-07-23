/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition

/-!
# Graphs of measurable spaces and kernels on those graphs

## Main definitions

## Main statements

## Notations

* `κ ⊗[M] η`

-/

open Set ENNReal ProbabilityTheory MeasureTheory


namespace ProbabilityTheory

@[simp]
lemma kernel.compProd_zero_right [MeasurableSpace α] [MeasurableSpace β]
    (κ : kernel α β) (γ : Type _) [MeasurableSpace γ] :
    κ ⊗ₖ (0 : kernel (α × β) γ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [kernel.compProd_apply _ _ _ hs]
    simp
  · rw [kernel.compProd_undef_left _ _ h]

@[simp]
lemma kernel.compProd_zero_left [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] (κ : kernel (α × β) γ)  :
    (0 : kernel α β) ⊗ₖ κ = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [kernel.compProd_apply _ _ _ hs]
    simp
  · rw [kernel.compProd_undef_right _ _ h]

@[simp]
lemma kernel.map_zero_left (α : Type _) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (f : β → γ) (hf : Measurable f) :
    kernel.map (0 : kernel α β) f hf = 0 := by
  ext a s
  rw [kernel.map_apply]
  simp

variable [Preorder ι]

-- For IT: `node i = (x : Iic i) → α x`, `path i j = (x : Ioc i j) → α x`
-- TODO: for markov chains on `(i : ℕ) → α i`, `node i = α i`, `path i j = α j`
structure MeasurableSpaceGraph (ι : Type _) [Preorder ι] :=
  (node : ι → Type _)
  (path : ι → ι → Type _)
  (node_meas : ∀ i, MeasurableSpace (node i))
  (path_meas : ∀ i j, MeasurableSpace (path i j))
  (el : ∀ i j, i < j → node i × path i j → node j)
  (el_meas : ∀ i j hij, Measurable (el i j hij))
  (er : ∀ i j k, i < j → j < k → path i j × path j k → path i k)
  (er_meas : ∀ i j k hij hjk, Measurable (er i j k hij hjk))
  (el_assoc : ∀ i j k hij hjk (a : node i) (b : path i j) (c : path j k),
    el j k hjk (el i j hij (a, b), c) = el i k (hij.trans hjk) (a, er i j k hij hjk (b, c)))
  (er_assoc : ∀ i j k l hij hjk hkl (b : path i j) (c : path j k) (d : path k l),
    er i j l hij (hjk.trans hkl) (b, er j k l hjk hkl (c, d)) =
      er i k l (hij.trans hjk) hkl (er i j k hij hjk (b, c), d))

instance (M : MeasurableSpaceGraph ι) (i : ι) : MeasurableSpace (M.node i) := M.node_meas i
instance (M : MeasurableSpaceGraph ι) (i j : ι) : MeasurableSpace (M.path i j) := M.path_meas i j

def e_path_eq (M : MeasurableSpaceGraph ι) (h : j = k) : M.path i j ≃ᵐ M.path i k :=
  MeasurableEquiv.cast (by rw [h]) (by rw [h])

namespace MeasurableSpaceGraph

variable {i j k l : ι}

def split (M : MeasurableSpaceGraph ι) (i j k : ι) (hij : i < j)
    (κ : kernel (M.node j) (M.path j k)) :
    kernel (M.node i × M.path i j) (M.path j k) :=
  kernel.comap κ (M.el i j hij) (M.el_meas i j hij)

lemma split_eq_comap (M : MeasurableSpaceGraph ι) (i j k : ι) (hij : i < j)
    (κ : kernel (M.node j) (M.path j k)) :
    split M i j k hij κ = kernel.comap κ (M.el i j hij) (M.el_meas i j hij) := rfl

instance (M : MeasurableSpaceGraph ι) (hij : i < j) (κ : kernel (M.node j) (M.path j k))
    [IsSFiniteKernel κ] :
    IsSFiniteKernel (M.split i j k hij κ) := by
  rw [split]
  infer_instance

@[simp]
lemma split_zero (M : MeasurableSpaceGraph ι) (i j k : ι) (hij : i < j) :
    split M i j k hij (0 : kernel (M.node j) (M.path j k)) = 0 := by
  rw [split] -- todo: kernel.comap_zero missing as simp lemma
  ext1 a
  rw [kernel.comap_apply, kernel.zero_apply, kernel.zero_apply]

open Classical

noncomputable
def compProd (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (η : kernel (M.node j) (M.path j k)) :
    kernel (M.node i) (M.path i k) :=
  if h : i < j ∧ j < k
    then kernel.map (κ ⊗ₖ M.split i j k h.1 η) (M.er i j k h.1 h.2) (M.er_meas i j k h.1 h.2)
    else 0

lemma compProd_eq (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (η : kernel (M.node j) (M.path j k)) (hij : i < j) (hjk : j < k) :
    M.compProd κ η = kernel.map (κ ⊗ₖ M.split i j k hij η) (M.er i j k hij hjk)
      (M.er_meas i j k hij hjk) := by
  rw [compProd, dif_pos]
  exact ⟨hij, hjk⟩

instance (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (η : kernel (M.node j) (M.path j k)) :
    IsSFiniteKernel (M.compProd κ η) := by
  rw [compProd]
  split_ifs <;> infer_instance

notation κ " ⊗[" M "] " η => MeasurableSpaceGraph.compProd M κ η

lemma compProd_apply' (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (η : kernel (M.node j) (M.path j k)) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hij : i < j) (hjk : j < k) (a : node M i) {s : Set (path M i k)} (hs : MeasurableSet s) :
    (κ ⊗[M] η) a s
      = ∫⁻ b, η (el M i j hij (a, b)) {c | (b, c) ∈ er M i j k hij hjk ⁻¹' s} ∂(κ a) := by
  rw [compProd_eq _ _ _ hij hjk, kernel.map_apply' _ _ _ hs,
    kernel.compProd_apply _ _ _ ((M.er_meas _ _ _ _ _) hs)]
  simp_rw [split, kernel.comap_apply]

@[simp]
lemma compProd_zero_right (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (k : ι) :
    (κ ⊗[M] (0 : kernel (M.node j) (M.path j k))) = 0 := by
  rw [compProd]
  split_ifs
  · simp only [split_zero, kernel.compProd_zero_right, kernel.map_zero_left]
  · rfl

@[simp]
lemma compProd_zero_left (M : MeasurableSpaceGraph ι) (i : ι) (κ : kernel (M.node j) (M.path j k)) :
    ((0 : kernel (M.node i) (M.path i j)) ⊗[M] κ) = 0 := by
  rw [compProd]
  split_ifs
  · simp only [kernel.compProd_zero_left, kernel.map_zero_left]
  · rfl

lemma compProd_undef_left (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (η : kernel (M.node j) (M.path j k)) (hij : i < j) (hjk : j < k) (h : ¬ IsSFiniteKernel κ) :
    (κ ⊗[M] η) = 0 := by
  rw [compProd_eq _ _ _ hij hjk, kernel.compProd_undef_left _ _ h]
  simp

lemma compProd_assoc (M : MeasurableSpaceGraph ι) (κ : kernel (M.node i) (M.path i j))
    (η : kernel (M.node j) (M.path j k)) (ξ : kernel (M.node k) (M.path k l))
    [IsSFiniteKernel η] [IsSFiniteKernel ξ]
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    (κ ⊗[M] (η ⊗[M] ξ)) = (κ ⊗[M] η) ⊗[M] ξ := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_undef_left _ _ _ hij (hjk.trans hkl) hκ, compProd_undef_left _ _ _ hij hjk hκ]
    simp
  ext a s hs
  have h_comp_det : ∀ b, ξ (M.el i k (hij.trans hjk) (a, b))
      = (ξ ∘ₖ kernel.deterministic (M.el i k (hij.trans hjk)) (M.el_meas i k (hij.trans hjk)))
        (a, b) := by
    intro b
    rw [kernel.comp_deterministic_eq_comap, kernel.comap_apply]
  have h_meas_comp : Measurable fun b ↦
      ξ (el M i k (hij.trans hjk) (a, b)) {c | (b, c) ∈ er M i k l (hij.trans hjk) hkl ⁻¹' s} := by
    simp_rw [h_comp_det]
    exact kernel.measurable_kernel_prod_mk_left' (M.er_meas _ _ _ _ _ hs) a
  rw [compProd_apply' _ _ _ hij (hjk.trans hkl) _ hs,
    compProd_apply' _ _ _ (hij.trans hjk) hkl _ hs, compProd_eq _ _ _ hjk hkl,
    compProd_eq _ _ _ hij hjk, kernel.map_apply, lintegral_map h_meas_comp (M.er_meas _ _ _ _ _)]
  have : ∀ b, MeasurableSet {c | (b, c) ∈ er M i j l hij (hjk.trans hkl) ⁻¹' s} :=
    fun b ↦ (@measurable_prod_mk_left _ _ inferInstance _ b) (M.er_meas _ _ _ _ _ hs)
  simp_rw [kernel.map_apply' _ _ _ (this _)]
  have : ∀ b, MeasurableSet
      (er M j k l hjk hkl ⁻¹' {c | (b, c) ∈ er M i j l hij (hjk.trans hkl) ⁻¹' s}) :=
    fun b ↦ M.er_meas _ _ _ _ _ (this b)
  simp_rw [kernel.compProd_apply _ _ _ (this _), split, kernel.comap_apply]
  rw [kernel.lintegral_compProd]
  swap ; exact h_meas_comp.comp (M.er_meas i j k hij hjk)
  simp only [kernel.comap_apply, M.el_assoc, mem_preimage, preimage_setOf_eq, mem_setOf_eq,
    M.er_assoc]

end MeasurableSpaceGraph

structure Transition (M : MeasurableSpaceGraph ι) :=
(ker : ∀ i j, kernel (M.node i) (M.path i j))
(s_finite : ∀ i j, IsSFiniteKernel (ker i j))
(comp : ∀ i j k (_hij : i < j) (_hjk : j < k), ((ker i j) ⊗[M] (ker j k)) = ker i k)

section nat

/-! ### MeasurableSpaceGraph on ℕ

We descibe the `MeasurableSpaceGraph` indexed by `ℕ` with nodes `(x : Ici i) → α x` and
paths `(x : Ioc i j) → α x`.

The intended application is the following: we consider a stochastic process `X : (i : ℕ) → α i` and
a kernel from `(x : Ici i) → α x` to `(x : Ioc i j) → α x` describes the law of the random variables
`X (i + 1), …, X j` given `X 0, …, X i`. -/

variable {α : ℕ → Type _} [∀ i, MeasurableSpace (α i)]

section equivs

def el (i j : ℕ) (hij : i < j) :
    (∀ x : Iic i, α x) × (∀ x : Ioc i j, α x) ≃ᵐ ∀ x : Iic j, α x where
  toFun := fun p x ↦ if h : x ≤ i then p.1 ⟨x, h⟩ else p.2 ⟨x, ⟨not_le.mp h, x.2⟩⟩
  invFun := fun p ↦ ⟨fun x ↦ p ⟨x, (mem_Iic.mp x.2).trans hij.le⟩,
    fun x ↦ p ⟨x, (mem_Ioc.mp x.2).2⟩⟩
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
    apply measurable_pi_lambda _ (fun (x : Iic j) ↦ ?_)
    by_cases x ≤ i
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      exact measurable_fst.eval
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

def er (i j k : ℕ) (hij : i < j) (hjk : j < k) :
    (∀ x : Ioc i j, α x) × (∀ x : Ioc j k, α x) ≃ᵐ ∀ x : Ioc i k, α x where
  toFun := fun p x ↦ if h : x ≤ j then p.1 ⟨x, ⟨x.2.1, h⟩⟩ else p.2 ⟨x, ⟨not_le.mp h, x.2.2⟩⟩
  invFun := fun p ↦ ⟨fun x ↦ p ⟨x, ⟨x.2.1, x.2.2.trans hjk.le⟩⟩,
    fun x ↦ p ⟨x, ⟨hij.trans x.2.1, x.2.2⟩⟩⟩
  left_inv := fun p ↦ by
    ext x
    · simp only
      rw [dif_pos x.2.2]
    · simp only
      rw [dif_neg (not_le.mpr x.2.1)]
  right_inv := fun p ↦ by
    ext x
    simp only
    split_ifs <;> rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun x ↦ ?_)
    by_cases x ≤ j
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      exact measurable_fst.eval
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

lemma measurable_cast {α β} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (h : α = β)
    (hm : HEq mα mβ) :
    Measurable (cast h) := by
  subst h
  subst hm
  exact measurable_id

def e_succ_nat {α : ℕ → Type _} [mα : ∀ n, MeasurableSpace (α n)]
    (j : ℕ) :
    α (j + 1) ≃ᵐ ((k : Ioc j (j + 1)) → α ↑k) where
  toFun := fun a x ↦ by
    rw [le_antisymm x.2.2 (Nat.succ_le_iff.mpr x.2.1)]
    exact a
  invFun := fun a ↦ a ⟨j + 1, ⟨Nat.lt_succ_self j, le_rfl⟩⟩
  left_inv := fun a ↦ by simp only [eq_mpr_eq_cast, cast_eq]
  right_inv := fun a ↦ by
    simp only [eq_mpr_eq_cast]
    ext x
    refine (cast_eq rfl ?_).trans ?_
    have : x = ⟨j + 1, ⟨Nat.lt_succ_self j, le_rfl⟩⟩ := by
      rw [← Subtype.eta x x.2, Subtype.coe_eta]
      exact le_antisymm x.2.2 (Nat.succ_le_iff.mpr x.2.1)
    rw [this]
  measurable_toFun := by
    simp only [eq_mpr_eq_cast, Equiv.coe_fn_mk]
    apply measurable_pi_lambda _ (fun x ↦ ?_)
    have h : ↑x = j + 1 := le_antisymm x.2.2 (Nat.succ_le_iff.mpr x.2.1)
    have hm : HEq (mα ↑x) (mα (j + 1)) := by rw [h]
    have hα : α ↑x = α (j + 1) := by rw [h]
    exact measurable_cast hα.symm hm.symm
  measurable_invFun := by
    simp only [eq_mpr_eq_cast, Equiv.coe_fn_symm_mk]
    apply measurable_pi_apply

lemma el_assoc {i j k : ℕ} (hij : i < j) (hjk : j < k) (a : (x : Iic i) → α ↑x)
    (b : (x : Ioc i j) → α ↑x) (c : (x : Ioc j k) → α ↑x) :
    el j k hjk (el i j hij (a, b), c) = el i k (hij.trans hjk) (a, er i j k hij hjk (b, c)) := by
  ext x
  simp only [el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er]
  split_ifs
  · rfl
  · rfl
  · exfalso ; linarith
  · rfl

lemma er_assoc {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (b : (x : Ioc i j) → α ↑x) (c : (x : Ioc j k) → α ↑x) (d : (x : Ioc k l) → α ↑x) :
    er i j l hij (hjk.trans hkl) (b, er j k l hjk hkl (c, d))
      = er i k l (hij.trans hjk) hkl (er i j k hij hjk (b, c), d) := by
  ext x
  simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er]
  split_ifs
  · rfl
  · exfalso ; linarith
  · rfl
  · rfl

end equivs

def measurableSpaceGraph_nat (α : ℕ → Type _) [∀ i, MeasurableSpace (α i)] :
    MeasurableSpaceGraph ℕ where
  node := fun i ↦ ∀ x : Iic i, α x
  path := fun i j ↦ ∀ x : Ioc i j, α x
  node_meas := fun i ↦ by infer_instance
  path_meas := fun i j ↦ by infer_instance
  el := fun i j hij x ↦ el i j hij x
  el_meas := fun i j hij ↦ MeasurableEquiv.measurable (el i j hij)
  er := fun i j k hij hjk x ↦ er i j k hij hjk x
  er_meas := fun i j k hij hjk ↦ MeasurableEquiv.measurable (er i j k hij hjk)
  el_assoc := fun i j k ↦ el_assoc
  er_assoc := fun i j k l ↦ er_assoc

local notation "M" => ProbabilityTheory.measurableSpaceGraph_nat

variable (α)

lemma measurableSpaceGraph_nat.node_eq : (M α).node i = ∀ x : Iic i, α x := rfl
lemma measurableSpaceGraph_nat.path_eq : (M α).path i j = ∀ x : Ioc i j, α x := rfl
def measurableSpaceGraph_nat.node_equiv : (M α).node i ≃ᵐ ∀ x : Iic i, α x :=
  MeasurableEquiv.refl _
def measurableSpaceGraph_nat.path_equiv : (M α).path i j ≃ᵐ ∀ x : Ioc i j, α x :=
  MeasurableEquiv.refl _

variable {α}

noncomputable
def cast_path (κ : kernel ((M α).node i) ((M α).path i j)) (h : j = k) :
    kernel ((M α).node i) ((M α).path i k) :=
  kernel.map κ (e_path_eq (M α) h) (MeasurableEquiv.measurable _)

lemma cast_path_apply (κ : kernel ((M α).node i) ((M α).path i j)) (h : j = k)
    (a : (M α).node i) (s : Set ((M α).path i k)) (hs : MeasurableSet s) :
    cast_path κ h a s = κ a (e_path_eq (M α) h ⁻¹' s) := by
  rw [cast_path, kernel.map_apply' _ _ _ hs]

instance (κ : kernel ((M α).node i) ((M α).path i j)) (h : j = k) [IsSFiniteKernel κ] :
    IsSFiniteKernel (cast_path κ h) := by
  rw [cast_path] ; infer_instance

noncomputable
def kerInterval (κ₀ : kernel ((M α).node i) ((M α).path i j)) [IsSFiniteKernel κ₀]
    (κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))) (k : ℕ) :
    kernel ((M α).node i) ((M α).path i k) := by
  induction k with
  | zero => exact 0
  | succ k κ_k => exact if h : j = k + 1 then cast_path κ₀ h else (κ_k ⊗[M α] (κ k))

@[simp]
lemma kerInterval_zero (κ₀ : kernel ((M α).node i) ((M α).path i j)) [IsSFiniteKernel κ₀]
    (κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))) :
    kerInterval κ₀ κ 0 = 0 := rfl

lemma kerInterval_succ {κ₀ : kernel ((M α).node i) ((M α).path i j)} [IsSFiniteKernel κ₀]
    {κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))} (k : ℕ) :
    kerInterval κ₀ κ (k + 1)
      = if h : j = k + 1 then cast_path κ₀ h else ((kerInterval κ₀ κ k) ⊗[M α] (κ k)) := rfl

lemma kerInterval_succ_of_ne {κ₀ : kernel ((M α).node i) ((M α).path i j)} [IsSFiniteKernel κ₀]
    {κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))} (h : j ≠ k + 1) :
    kerInterval κ₀ κ (k + 1) = (kerInterval κ₀ κ k) ⊗[M α] (κ k) := by
  rw [kerInterval_succ, dif_neg h]

lemma kerInterval_succ_right {κ₀ : kernel ((M α).node i) ((M α).path i j)} [IsSFiniteKernel κ₀]
    {κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))} (h : j ≤ k) :
    kerInterval κ₀ κ (k + 1) = (kerInterval κ₀ κ k) ⊗[M α] (κ k) := by
  rw [kerInterval_succ, dif_neg (by linarith)]

lemma kerInterval_of_lt {κ₀ : kernel ((M α).node i) ((M α).path i j)} [IsSFiniteKernel κ₀]
    {κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))} (h : k < j) :
    kerInterval κ₀ κ k = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [kerInterval_succ, dif_neg h.ne', ih (by linarith)]
      simp

lemma kerInterval_of_eq (κ₀ : kernel ((M α).node i) ((M α).path i j)) [IsSFiniteKernel κ₀]
    (κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1))) (hj : 0 < j) :
    kerInterval κ₀ κ j = κ₀ := by
  cases j with
  | zero => exfalso ; linarith
  | succ n =>
    rw [kerInterval_succ, dif_pos rfl]
    ext a s hs
    rw [cast_path_apply _ _ _ _ hs]
    rfl

instance (κ₀ : kernel ((M α).node i) ((M α).path i j)) [h₀ : IsSFiniteKernel κ₀]
    (κ : ∀ k, kernel ((M α).node k) ((M α).path k (k + 1)))
    (k : ℕ) :
    IsSFiniteKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => rw [kerInterval_zero] ; infer_instance
  | succ n _ =>
      rw [kerInterval_succ]
      split_ifs with h_eq
      · infer_instance
      · infer_instance

noncomputable
def kerNat (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (i j : ℕ) :
    kernel ((M α).node i) ((M α).path i j) :=
  if i < j then kerInterval (κ i) κ j else 0

lemma kerNat_eq (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (hij : i < j) :
    kerNat κ i j = kerInterval (κ i) κ j :=
  dif_pos hij

lemma kerNat_of_ge (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (hij : j ≤ i) :
    kerNat κ i j = 0 :=
  dif_neg (not_lt.mpr hij)

instance (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1))) [∀ i, IsSFiniteKernel (κ i)] :
    IsSFiniteKernel (kerNat κ i j) := by
  rw [kerNat]; split_ifs <;> infer_instance

lemma kerNat_succ (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (i : ℕ) :
    kerNat κ i (i + 1) = κ i := by
  rw [kerNat_eq _ (Nat.lt_succ_self _), kerInterval_of_eq _ _ (by linarith)]

lemma kerNat_succ_right (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (i j : ℕ) (hij : i < j) :
    kerNat κ i (j + 1) = (kerNat κ i j) ⊗[M α] (kerNat κ j (j + 1)) := by
  rw [kerNat_eq _ (hij.trans (Nat.lt_succ_self _)),
    kerInterval_succ_right (Nat.succ_le_iff.mpr hij)]
  congr
  · rw [kerNat_eq _ hij]
  · rw [kerNat_succ κ j]

lemma kerNat_succ_left (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (i j : ℕ) (hij : i + 1 < j) :
    kerNat κ i j = (kerNat κ i (i + 1)) ⊗[M α] (kerNat κ (i + 1) j) := by
  induction j with
  | zero =>
    rw [kerNat_of_ge κ (Nat.zero_le _), kerNat_of_ge κ (Nat.zero_le _)]
    simp
  | succ j hj => cases le_or_lt j (i + 1) with
    | inl h =>
      have hj_eq : j = i + 1 := le_antisymm h (Nat.succ_lt_succ_iff.mp (by convert hij))
      rw [kerNat_succ_right]
      · congr
      · rw [hj_eq] ; exact Nat.lt_succ_self i
    | inr h =>
      rw [kerNat_succ_right _ _ _ (Nat.succ_lt_succ_iff.mp hij), hj h,
        kerNat_succ_right _ _ j h,
        MeasurableSpaceGraph.compProd_assoc (M α) (kerNat κ i (i + 1)) (kerNat κ (i + 1) j)
          (kerNat κ j (j + 1)) (Nat.lt_succ_self i) h (Nat.lt_succ_self j)]

theorem compProd_kerNat (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (hij : i < j) (hjk : j < k) :
    ((kerNat κ i j) ⊗[M α] (kerNat κ j k)) = kerNat κ i k := by
  cases k with
  | zero => exfalso ; linarith
  | succ k =>
    refine Nat.decreasingInduction' ?_ (Nat.lt_succ_iff.mp hjk) ?_
    · intro l hlk hjl h
      rw [← h, kerNat_succ_left _ l]
      swap; linarith
      rw [kerNat_succ_right _ i _ (hij.trans_le hjl),
        (M α).compProd_assoc _ _ _ (hij.trans_le hjl) (Nat.lt_succ_self l)]
      linarith
    · rw [kerNat_succ_right _ _ _ (hij.trans_le (Nat.lt_succ_iff.mp hjk))]

noncomputable
def Transition_of_seq (κ : (k : ℕ) → kernel ((M α).node k) ((M α).path k (k + 1)))
  [∀ i, IsSFiniteKernel (κ i)] :
  Transition (M α) :=
{ ker := kerNat κ,
  s_finite := fun _ _ ↦ inferInstance,
  comp := fun _ _ _ ↦ compProd_kerNat κ, }

def e_succ (j : ℕ) : α (j + 1) ≃ᵐ (M α).path j (j + 1) :=
  (e_succ_nat j).trans (measurableSpaceGraph_nat.path_equiv α).symm

noncomputable
def to_M (κ : (k : ℕ) → kernel ((x : Iic k) → α ↑x) (α (k + 1))) (i : ℕ) :
    kernel ((M α).node i) ((M α).path i (i + 1)) :=
  kernel.map (κ i) (e_succ i) (MeasurableEquiv.measurable _)

instance (κ : (k : ℕ) → kernel ((x : Iic k) → α ↑x) (α (k + 1))) [∀ i, IsSFiniteKernel (κ i)]
    (i : ℕ) :
    IsSFiniteKernel (to_M κ i) := by
  rw [to_M]; infer_instance

noncomputable
def Transition_of_seq_nat (κ : ∀ i, kernel ((j : Iic i) → α ↑j) (α (i + 1)))
  [∀ i, IsSFiniteKernel (κ i)] :
  Transition (M α) :=
{ ker := kerNat (to_M κ),
  s_finite := fun _ _ ↦ inferInstance,
  comp := fun _ _ _ ↦ compProd_kerNat (to_M κ), }

end nat

section Markov

/-! ### Markov MeasurableSpaceGraph on ℕ

We descibe the `MeasurableSpaceGraph` indexed by `ℕ` with nodes `i ↦ α i` and paths `i j ↦ α j`.

The intended application is the following: we consider a Markov process `X : (i : ℕ) → α i` and
a kernel from `α i` to `α j` describes the law of the random variables `X j` given `X i`. -/

variable {α : ℕ → Type _} [∀ i, MeasurableSpace (α i)]

def measurableSpaceGraph_markov_nat (α : ℕ → Type _) [∀ i, MeasurableSpace (α i)] :
    MeasurableSpaceGraph ℕ where
  node := fun i ↦ α i
  path := fun _ j ↦ α j
  node_meas := fun i ↦ by infer_instance
  path_meas := fun i j ↦ by infer_instance
  el := fun i j _ x ↦ x.2
  el_meas := fun i j _ ↦ measurable_snd
  er := fun i j k _ _ x ↦ x.2
  er_meas := fun i j k _ _ ↦ measurable_snd
  el_assoc := fun i j k hij hjk a b c ↦ rfl
  er_assoc := fun i j k l hij hjk hkl b c d ↦ rfl

local notation "M" => measurableSpaceGraph_markov_nat

variable (α)

lemma measurableSpaceGraph_markov_nat.node_eq : (M α).node i = α i := rfl
lemma measurableSpaceGraph_markov_nat.path_eq : (M α).path i j = α j := rfl
def measurableSpaceGraph_markov_nat.node_equiv : (M α).node i ≃ᵐ α i := MeasurableEquiv.refl _
def measurableSpaceGraph_markov_nat.path_equiv : (M α).path i j ≃ᵐ α j := MeasurableEquiv.refl _

variable {α}

noncomputable
def Transition_of_markov_seq_nat (κ : ∀ i, kernel (α i) (α (i + 1)))
  [∀ i, IsSFiniteKernel (κ i)] :
  Transition (M α) :=
{ ker := kerNat κ,
  s_finite := fun _ _ ↦ inferInstance,
  comp := fun _ _ _ ↦ compProd_kerNat κ, }

end Markov

end ProbabilityTheory
