/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.Maps

/-!
# Consecutive composition of kernels

This file is the first step towards Ionescu-Tulcea theorem, which allows for instance to construct
the product of an infinite family of probability measures. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` takes the trajectory up to time `a` as input and outputs
the distribution of the trajectory in `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem then tells us that these compositions can be extended into a kernel
`η : Kernel (Π i : Iic a, X i) → Π n > a, X n` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

To be able to even state the theorem we want to take the composition-product
(see `ProbabilityTheory.Kernel.compProd`) of consecutive kernels.
This however is not straightforward.

Consider `n : ℕ`. We cannot write `(κ n) ⊗ₖ (κ (n + 1))` directly, we need to first
introduce an equivalence to see `κ (n + 1)` as a kernel with codomain
`(Π i : Iic n, X i) × X (n + 1)`, and we get a `Kernel (Π i : Iic n, X i) (X (n + 1) × (X (n + 2))`.
However we want to do multiple composition at ones, i.e. write
`(κ n) ⊗ₖ ... ⊗ₖ (κ m)` for `n < m`. This requires even more equivalences to make sense of, and at
the end of the day we get kernels which still cannot be composed together.

To tackle this issue, we decide here to only consider kernels of the form
`Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)`. In other words these kernels take as input
a trajectory up to time `a` and output the distribution of the full trajectory up to time `b`.
This is captured in the definition `partialTraj κ a b`
(`partialTraj` stands for "partial trajectory").
The advantage of this approach is that it allows us to write for instance
`partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c` (see `partialTraj_comp_partialTraj`.)

In this file we therefore define this family of kernels and prove some properties of it.
In particular we provide at the end of the file some results to compute the integral of a function
against `partialTraj κ a b`, taking inspiration from `MeasureTheory.lmarginal`.

## Main definitions

* `partialTraj κ a b`: Given the trajectory of a point up to time `a`, returns the distribution
  of the trajectory up to time `b`.
* `lmarginalPartialTraj κ a b f`: The integral of `f` against `partialTraj κ a b`.
  This is essentially the integral of `f` against `κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` but seen as depending
  on all the variables, mimicking `MeasureTheory.lmarginal`. This allows to write
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f)`.

## Main statements

* `partialTraj_comp_partialTraj`: if `a ≤ b` and `b ≤ c` then
  `partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c`.
* `lmarginalPartialTraj_self` : if `a ≤ b` and `b ≤ c` then
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTraj κ a c`.

## Tags

Ionescu-Tulcea theorem, composition of kernels
-/

open Finset Function MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

variable {X : ℕ → Type*} {mX : ∀ n, MeasurableSpace (X n)} {a b c : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}

section partialTraj

/-! ### Definition of `partialTraj` -/

namespace ProbabilityTheory.Kernel

open MeasurableEquiv

variable (κ) in
/-- Given a family of kernels `κ n` from `X 0 × ... × X n` to `X (n + 1)` for all `n`,
construct a kernel from `X 0 × ... × X a` to `X 0 × ... × X b` by iterating `κ`.

The idea is that the input is some trajectory up to time `a`, and the output is the distribution
of the trajectory up to time `b`. In particular if `b ≤ a`, this is just a deterministic kernel
(see `partialTraj_le`). The name `partialTraj` stands for "partial trajectory".

This kernel can be extended into a kernel with codomain `Π n, X n` via the Ionescu-Tulcea theorem.
-/
noncomputable def partialTraj (a b : ℕ) : Kernel (Π i : Iic a, X i) (Π i : Iic b, X i) :=
  if h : b ≤ a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_ge h)

section Basic

/-- If `b ≤ a`, given the trajectory up to time `a`, the trajectory up to time `b` is
deterministic and is equal to the restriction of the trajectory up to time `a`. -/
lemma partialTraj_le (hba : b ≤ a) :
    partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _) := by
  rw [partialTraj, dif_pos hba]

@[simp]
lemma partialTraj_self (a : ℕ) : partialTraj κ a a = Kernel.id := by rw [partialTraj_le le_rfl]; rfl

@[simp]
lemma partialTraj_zero :
    partialTraj κ a 0 = deterministic (frestrictLe₂ (zero_le a)) (measurable_frestrictLe₂ _) := by
  rw [partialTraj_le (zero_le a)]

lemma partialTraj_le_def (hab : a ≤ b) : partialTraj κ a b =
    @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b hab := by
  obtain rfl | hab := eq_or_lt_of_le hab
  · simp
  · rw [partialTraj, dif_neg (not_le.2 hab)]

lemma partialTraj_succ_of_le (hab : a ≤ b) : partialTraj κ a (b + 1) =
    ((Kernel.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ partialTraj κ a b).map
    (IicProdIoc b (b + 1)) := by
  rw [partialTraj, dif_neg (by omega)]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak hk => rw [Nat.leRec_succ, ← partialTraj_le_def]; omega

instance (a b : ℕ) : IsSFiniteKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

instance [∀ n, IsFiniteKernel (κ n)] (a b : ℕ) : IsFiniteKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

instance [∀ n, IsZeroOrMarkovKernel (κ n)] (a b : ℕ) :
    IsZeroOrMarkovKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

instance [∀ n, IsMarkovKernel (κ n)] (a b : ℕ) :
    IsMarkovKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak =>
      rw [partialTraj_succ_of_le hak]
      have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ measurable_IicProdIoc
  · rw [partialTraj_le hba]; infer_instance

lemma partialTraj_succ_self (a : ℕ) :
    partialTraj κ a (a + 1) =
    (Kernel.id ×ₖ ((κ a).map (piSingleton a))).map (IicProdIoc a (a + 1)) := by
  rw [partialTraj_succ_of_le le_rfl, partialTraj_self, comp_id]

lemma partialTraj_succ_eq_comp (hab : a ≤ b) :
    partialTraj κ a (b + 1) = partialTraj κ b (b + 1) ∘ₖ partialTraj κ a b := by
  rw [partialTraj_succ_self, ← map_comp, partialTraj_succ_of_le hab]

/-- Given the trajectory up to time `a`, `partialTraj κ a b` gives the distribution of
the trajectory up to time `b`. Then plugging this into `partialTraj κ b c` gives
the distribution of the trajectory up to time `c`. -/
theorem partialTraj_comp_partialTraj (hab : a ≤ b) (hbc : b ≤ c) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [partialTraj_succ_eq_comp h, comp_assoc, hk,
      ← partialTraj_succ_eq_comp (hab.trans h)]

/-- This is a specific lemma used in the proof of `partialTraj_eq_prod`. It is the main rewrite step
and stating it as a separate lemma avoids using extensionality of kernels, which would generate
a lot of measurability subgoals. -/
private lemma fst_prod_comp_id_prod {X Y Z : Type*} {mX : MeasurableSpace X}
    {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z} (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel (X × Y) Z) [IsSFiniteKernel η] :
    ((deterministic Prod.fst measurable_fst) ×ₖ η) ∘ₖ (Kernel.id ×ₖ κ) =
    Kernel.id ×ₖ (η ∘ₖ (Kernel.id ×ₖ κ)) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, lintegral_id_prod (Kernel.measurable_coe _ ms),
    deterministic_prod_apply' _ _ _ ms, id_prod_apply' _ _ ms,
    comp_apply' _ _ _ (measurable_prodMk_left ms),
    lintegral_id_prod (η.measurable_coe (measurable_prodMk_left ms))]

/-- This is a technical lemma saying that `partialTraj κ a b` consists of two independent parts, the
first one being the identity. It allows to compute integrals. -/
lemma partialTraj_eq_prod [∀ n, IsSFiniteKernel (κ n)] (a b : ℕ) :
    partialTraj κ a b =
    (Kernel.id ×ₖ (partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map
    (IicProdIoc a b) := by
  obtain hba | hab := le_total b a
  · rw [partialTraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, deterministic_map,
      fst_prod, id_map]
    all_goals fun_prop
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [partialTraj_self, id_map, map_apply, prod_apply, IicProdIoc_self, ← Measure.fst,
    Measure.fst_prod]
    all_goals fun_prop
  | succ k h hk =>
    have : (IicProdIoc (X := X) k (k + 1)) ∘ (Prod.map (IicProdIoc a k) id) =
        (IicProdIoc (h.trans k.le_succ) ∘ (Prod.map id (IocProdIoc a k (k + 1)))) ∘
        prodAssoc := by
      ext x i
      simp only [IicProdIoc_def, MeasurableEquiv.IicProdIoc, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_mk, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Nat.succ_eq_add_one, IocProdIoc]
      split_ifs <;> try rfl
      omega
    nth_rw 1 [← partialTraj_comp_partialTraj h k.le_succ, hk, partialTraj_succ_self, comp_map,
      comap_map_comm, comap_prod, id_comap, ← id_map, map_prod_eq, ← map_comp_right, this,
      map_comp_right, id_prod_eq, prodAssoc_prod, map_comp_right, ← map_prod_map, map_id,
      ← map_comp, map_apply_eq_iff_map_symm_apply_eq, fst_prod_comp_id_prod, ← map_comp_right,
      ← coe_IicProdIoc (h.trans k.le_succ), symm_comp_self, map_id,
      deterministic_congr IicProdIoc_comp_restrict₂.symm, ← deterministic_comp_deterministic,
      comp_deterministic_eq_comap, ← comap_prod, ← map_comp, ← comp_map, ← hk,
      ← partialTraj_comp_partialTraj h k.le_succ, partialTraj_succ_self, map_comp, map_comp,
      ← map_comp_right, ← id_map, map_prod_eq, ← map_comp_right]
    · rfl
    all_goals fun_prop

variable [∀ n, IsMarkovKernel (κ n)]

lemma partialTraj_succ_map_frestrictLe₂ (a b : ℕ) :
    (partialTraj κ a (b + 1)).map (frestrictLe₂ b.le_succ) = partialTraj κ a b := by
  obtain hab | hba := le_or_gt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [partialTraj_succ_eq_comp hab, map_comp, partialTraj_succ_self, ← map_comp_right,
      frestrictLe₂_comp_IicProdIoc, ← fst_eq, fst_prod, id_comp]
    all_goals fun_prop
  · rw [partialTraj_le (Nat.succ_le.2 hba), partialTraj_le hba.le, deterministic_map]
    · rfl
    · fun_prop

/-- If we restrict the distribution of the trajectory up to time `c` to times `≤ b` we get
the trajectory up to time `b`. -/
theorem partialTraj_map_frestrictLe₂ (a : ℕ) (hbc : b ≤ c) :
    (partialTraj κ a c).map (frestrictLe₂ hbc) = partialTraj κ a b := by
  induction c, hbc using Nat.le_induction with
  | base => exact map_id ..
  | succ k h hk =>
    rw [← hk, ← frestrictLe₂_comp_frestrictLe₂ h k.le_succ, map_comp_right,
      partialTraj_succ_map_frestrictLe₂]
    all_goals fun_prop

lemma partialTraj_map_frestrictLe₂_apply (x₀ : Π i : Iic a, X i) (hbc : b ≤ c) :
    (partialTraj κ a c x₀).map (frestrictLe₂ hbc) = partialTraj κ a b x₀ := by
  rw [← map_apply _ (by fun_prop), partialTraj_map_frestrictLe₂]

/-- Same as `partialTraj_comp_partialTraj` but only assuming `a ≤ b`. It requires Markov kernels. -/
lemma partialTraj_comp_partialTraj' (c : ℕ) (hab : a ≤ b) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  obtain hbc | hcb := le_total b c
  · rw [partialTraj_comp_partialTraj hab hbc]
  · rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

/-- Same as `partialTraj_comp_partialTraj` but only assuming `b ≤ c`. It requires Markov kernels. -/
lemma partialTraj_comp_partialTraj'' {b c : ℕ} (hcb : c ≤ b) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

end Basic

section lmarginalPartialTraj

/-! ### Integrating against `partialTraj` -/

variable (κ)

/-- This function computes the integral of a function `f` against `partialTraj`,
and allows to view it as a function depending on all the variables.

This is inspired by `MeasureTheory.lmarginal`, to be able to write
`lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTraj κ a c`. -/
noncomputable def lmarginalPartialTraj (a b : ℕ) (f : (Π n, X n) → ℝ≥0∞) (x₀ : Π n, X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x₀ _ z) ∂(partialTraj κ a b (frestrictLe a x₀))

/-- If `b ≤ a`, then integrating `f` against `partialTraj κ a b` does nothing. -/
lemma lmarginalPartialTraj_le (hba : b ≤ a) {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) :
    lmarginalPartialTraj κ a b f = f := by
  ext x₀
  rw [lmarginalPartialTraj, partialTraj_le hba, Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

variable {κ}

lemma lmarginalPartialTraj_mono (a b : ℕ) {f g : (Π n, X n) → ℝ≥0∞} (hfg : f ≤ g) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a b f x₀ ≤ lmarginalPartialTraj κ a b g x₀ :=
  lintegral_mono fun _ ↦ hfg _

/-- Integrating `f` against `partialTraj κ a b x` is the same as integrating only over the variables
  from `x_{a+1}` to `x_b`. -/
lemma lmarginalPartialTraj_eq_lintegral_map [∀ n, IsSFiniteKernel (κ n)] {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a b f x₀ =
    ∫⁻ x : (Π i : Ioc a b, X i), f (updateFinset x₀ _ x)
      ∂(partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self) (frestrictLe a x₀) := by
  nth_rw 1 [lmarginalPartialTraj, partialTraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ _, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def,
      frestrictLe_apply, mem_Ioc]
    split_ifs <;> try rfl
    all_goals omega
  all_goals fun_prop

/-- Integrating `f` against `partialTraj κ a (a + 1)` is the same as integrating against `κ a`. -/
lemma lmarginalPartialTraj_succ [∀ n, IsSFiniteKernel (κ n)] (a : ℕ)
    {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a (a + 1) f x₀ =
      ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x₀) := by
  rw [lmarginalPartialTraj, partialTraj_succ_self, lintegral_map, lintegral_id_prod, lintegral_map]
  · congrm ∫⁻ x, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, frestrictLe_apply, piSingleton,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, update]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals omega
  all_goals fun_prop

@[measurability, fun_prop]
lemma measurable_lmarginalPartialTraj (a b : ℕ) {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (lmarginalPartialTraj κ a b f) := by
  unfold lmarginalPartialTraj
  let g : ((i : Iic b) → X i) × (Π n, X n) → ℝ≥0∞ := fun c ↦ f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (partialTraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x₀ ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x₀) ∂η x₀
  refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ Iic b <;> simp [h] <;> fun_prop

/-- Integrating `f` against `partialTraj κ a b` and then against `partialTraj κ b c` is the same
as integrating `f` against `partialTraj κ a c`. -/
theorem lmarginalPartialTraj_self (hab : a ≤ b) (hbc : b ≤ c)
    {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginalPartialTraj κ a b (lmarginalPartialTraj κ b c f) = lmarginalPartialTraj κ a c f := by
  ext x₀
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl hf]
  simp_rw [lmarginalPartialTraj, frestrictLe, restrict_updateFinset,
    updateFinset_updateFinset_of_subset (Iic_subset_Iic.2 hbc.le)]
  rw [← lintegral_comp, partialTraj_comp_partialTraj hab.le hbc.le]
  fun_prop

end lmarginalPartialTraj

end ProbabilityTheory.Kernel

open ProbabilityTheory Kernel

namespace DependsOn

/-! ### Lemmas about `lmarginalPartialTraj` and `DependsOn` -/

/-- If `f` only depends on the variables up to rank `a` and `a ≤ b`, integrating `f` against
`partialTraj κ b c` does nothing. -/
theorem lmarginalPartialTraj_of_le [∀ n, IsMarkovKernel (κ n)] (c : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginalPartialTraj κ b c f = f := by
  ext x
  rw [lmarginalPartialTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ (ae_of_all _ fun y ↦ hf fun i hi ↦ ?_)
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, Function.updateFinset, mem_Ioc, dite_eq_right_iff]
    omega

/-- If `f` only depends on the variables uo to rank `a`, integrating beyond rank `a` is the same
as integrating up to rank `a`. -/
theorem lmarginalPartialTraj_const_right [∀ n, IsMarkovKernel (κ n)] {d : ℕ} {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hac : a ≤ c) (had : a ≤ d) :
    lmarginalPartialTraj κ b c f = lmarginalPartialTraj κ b d f := by
  wlog hcd : c ≤ d generalizing c d
  · rw [this had hac (le_of_not_ge hcd)]
  obtain hbc | hcb := le_total b c
  · rw [← lmarginalPartialTraj_self hbc hcd mf, hf.lmarginalPartialTraj_of_le d mf hac]
  · rw [hf.lmarginalPartialTraj_of_le c mf (hac.trans hcb),
      hf.lmarginalPartialTraj_of_le d mf (hac.trans hcb)]

/-- If `f` only depends on variables up to rank `b`, its integral from `a` to `b` only depends on
variables up to rank `a`. -/
theorem dependsOn_lmarginalPartialTraj [∀ n, IsSFiniteKernel (κ n)] (a : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPartialTraj κ a b f) (Iic a) := by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPartialTraj_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  rw [lmarginalPartialTraj_eq_lintegral_map mf, lmarginalPartialTraj_eq_lintegral_map mf]
  congrm ∫⁻ z : _, ?_ ∂(partialTraj κ a b).map _ (fun i ↦ ?_)
  · exact hxy i.1 i.2
  · refine hf.updateFinset _ ?_
    rwa [← coe_sdiff, Iic_diff_Ioc_self_of_le hab]

end DependsOn

end partialTraj
