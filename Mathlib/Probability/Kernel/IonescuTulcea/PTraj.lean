/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Probability.Kernel.Composition.Basic

/-!
# Consecutive composition of kernels

This file is the first step towards Ionescu-Tulcea theorem, which allows for instance to construct
the product of an infinite family of probability measures. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` will take the trajectory up to time `a` as input and outputs
the distrbution of the trajectory in `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem then tells us that these compositions can be extend into a kernel
`η : Kernel (Π i : Iic a, X i) → Π n ≥ a, X n` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

To be able to even state the theorem we want to take the composition-product
(see `ProbabilityTheory.Kernel.compProd`) of consecutive kernels.
This however is not straight forward.

Consider `n : ℕ`. We cannot write `(κ n) ⊗ₖ (κ (n + 1))` directly, we need to first
introduce an equivalence to see `κ (n + 1)` as a kernel with codomain
`(Π i : Iic n, X i) × X (n + 1)`, and we get a `Kernel (Π i : Iic n, X i) (X (n + 1) × (X (n + 2))`.
However we want to do multiple compostion at ones, i.e. write
`(κ n) ⊗ₖ ... ⊗ₖ (κ m)` for `n < m`. This requires even more equivalences to make sense of, and at
the end of the day we get kernels which still cannot be composed together.

To tackle this issue, we decide here to only consider kernels of the form
`Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)`. In other words these kernels take as input
a trajectory up to time `a` and outputs the distribution of the full trajectory up to time `b`.
This is captured in the definition `ptraj κ a b` (`ptraj` stands for "partial trajectory").
The advantage of this approach is that it allows us to write for instance
`ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c` (see `ptraj_comp_ptraj`.)

In this file we therefore define this family of kernels and prove some properties of it.
In particular we provide at the end of the file some results to compute the integral of a function
against `ptraj κ a b`, takin inspiration from `MeasureTheory.lmarginal`.

## Main definitions

* `ptraj κ a b`: Given the trajectory of a point up to time `a`, returns the distribution
  of the trajectory up to time `b`.
* `lmarginalPTraj κ a b f`: The integral of `f` against `ptraj κ a b`. This is essentially the
  integral of `f` against `κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` but seen as depending on all the variables,
  mimicking `MeasureTheory.lmarginal`. This allows to write
  `lmarginalPTraj κ b c (lmarginalPTraj κ a b f)`.

## Main statements

* `ptraj_comp_ptraj`: if `a ≤ b` and `b ≤ c` then `ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c`.
* `lmarginalPTraj_self` : if `a ≤ b` and `b ≤ c` then
  `lmarginalPTraj κ b c (lmarginalPTraj κ a b f) = lmarginalPTraj κ a c`.

## Tags

Ionescu-Tulcea theorem, composition of kernels
-/

open Finset Function MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

variable {X : ℕ → Type*}

section Maps

/-! ### Auxiliary maps for the definition -/

/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. If `b < a`, this is just a projection on the first
coordinate followed by a restriction, see `IicProdIoc_le`. -/
def IicProdIoc (a b : ℕ) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) (i : Iic b) : X i :=
  if h : i ≤ a
    then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

/-- When `IicProdIoc` is only partially applied (i.e. `IicProdIoc a b x` but not
`IicProdIoc a b x i`) `simp [IicProdIoc]` won't unfold the definition.
This lemma allows to unfold it by writing `simp [IicProdIoc_def]`. -/
lemma IicProdIoc_def (a b : ℕ) :
    IicProdIoc (X := X) a b = fun x i ↦ if h : i.1 ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩ := rfl

lemma frestrictLe₂_comp_IicProdIoc {a b : ℕ} (hab : a ≤ b) :
    (frestrictLe₂ hab) ∘ (IicProdIoc (X := X) a b) = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

lemma restrict₂_comp_IicProdIoc (a b : ℕ) :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

@[simp]
lemma IicProdIoc_self (a : ℕ) : IicProdIoc (X := X) a a = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

lemma IicProdIoc_le {a b : ℕ} (hba : b ≤ a) :
    IicProdIoc (X := X) a b = (frestrictLe₂ hba) ∘ Prod.fst := by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]

lemma IicProdIoc_comp_restrict₂ {a b : ℕ} :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

/-- Gluing `Ioc a b` and `Ioc b c` into `Ioc a c`. -/
def IocProdIoc (a b c : ℕ) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (i : Ioc a c) : X i :=
  if h : i ≤ b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

variable [∀ n, MeasurableSpace (X n)]

@[measurability, fun_prop]
lemma measurable_IicProdIoc {m n : ℕ} : Measurable (IicProdIoc (X := X) m n) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

@[measurability, fun_prop]
lemma measurable_IocProdIoc {a b c : ℕ} : Measurable (IocProdIoc (X := X) a b c) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

/-- Identifying `{n + 1}` with `Ioc n (n + 1)`, as a measurable equiv on dependent functions. -/
def MeasurableEquiv.piSingleton (a : ℕ) : (X (a + 1)) ≃ᵐ ((i : Ioc a (a + 1)) → X i) where
  toFun x i := (Nat.mem_Ioc_succ i.2).symm ▸ x
  invFun x := x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ funext fun i ↦ by cases Nat.mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i ↦ (MeasurableEquiv.cast _ ?_).measurable)
    cases Nat.mem_Ioc_succ' i; rfl
  measurable_invFun := measurable_pi_apply _

/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. This version requires `a ≤ b` to get a measurable
equivalence. -/
def MeasurableEquiv.IicProdIoc {a b : ℕ} (hab : a ≤ b) :
    ((Π i : Iic a, X i) × (Π i : Ioc a b, X i)) ≃ᵐ Π i : Iic b, X i where
  toFun x i := if h : i ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
  invFun x := ⟨fun i ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩, fun i ↦ x ⟨i.1, Ioc_subset_Iic_self i.2⟩⟩
  left_inv := fun x ↦ by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 (mem_Ioc.1 i.2).1]
  right_inv := fun x ↦ funext fun i ↦ by
    by_cases hi : i.1 ≤ a <;> simp [hi]
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun x ↦ ?_)
    by_cases h : x ≤ a
    · simpa [h] using measurable_fst.eval
    · simpa [h] using measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

lemma MeasurableEquiv.coe_IicProdIoc {a b : ℕ} (hab : a ≤ b) :
    ⇑(IicProdIoc (X := X) hab) = _root_.IicProdIoc a b := rfl

lemma MeasurableEquiv.coe_IicProdIoc_symm {a b : ℕ} (hab : a ≤ b) :
    ⇑(IicProdIoc (X := X) hab).symm =
    fun x ↦ (frestrictLe₂ hab x, restrict₂ Ioc_subset_Iic_self x) := rfl

end Maps

variable {mX : ∀ n, MeasurableSpace (X n)} {a b c : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}

section ptraj

/-! ### Definition of `ptraj` -/

namespace ProbabilityTheory.Kernel

open MeasurableEquiv

variable (κ) in
/-- Given a family of kernels `κ n` from `X 0 × ... × X n` to `X (n + 1)` for all `n`,
construct a kernel from `X 0 × ... × X a` to `X 0 × ... × X b` by iterating `κ`.

The idea is that the input is some trajectory up to time `a`, and the ouptut is the distribution
of the trajectory up to time `b`. In particular if `b ≤ a`, this is just a deterministic kernel
(see `ptraj_le`). The name `ptraj` stands for "partial trajectory".

This kernel can be extended into a kernel with codomain `Π n, X n` via the Ionescu-Tulcea theorem.
-/
noncomputable def ptraj (a b : ℕ) : Kernel (Π i : Iic a, X i) (Π i : Iic b, X i) :=
  if h : b ≤ a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_le h)

section Basic

/-- If `b ≤ a`, given the trajectory up to time `a`, the trajectory up to time `b` is
deterministic and is equal to the restriction of the trajectory up to time `a`. -/
lemma ptraj_le (hba : b ≤ a) :
    ptraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _) := by
  rw [ptraj, dif_pos hba]

@[simp]
lemma ptraj_self (a : ℕ) : ptraj κ a a = Kernel.id := by rw [ptraj_le le_rfl]; rfl

@[simp]
lemma ptraj_zero :
    ptraj κ a 0 = deterministic (frestrictLe₂ (zero_le a)) (measurable_frestrictLe₂ _) := by
  rw [ptraj_le (zero_le a)]

lemma ptraj_le_def (hab : a ≤ b) : ptraj κ a b =
    @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b hab := by
  obtain rfl | hab := eq_or_lt_of_le hab
  · simp
  · rw [ptraj, dif_neg (not_le.2 hab)]

lemma ptraj_succ_of_le (hab : a ≤ b) : ptraj κ a (b + 1) =
    ((Kernel.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ ptraj κ a b).map (IicProdIoc b (b + 1)) := by
  rw [ptraj, dif_neg (by omega)]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak hk => rw [Nat.leRec_succ, ← ptraj_le_def]; omega

instance (a b : ℕ) : IsSFiniteKernel (ptraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [ptraj_self]; infer_instance
    | succ k hak => rw [ptraj_succ_of_le hak]; infer_instance
  · rw [ptraj_le hba]; infer_instance

instance [∀ n, IsFiniteKernel (κ n)] (a b : ℕ) : IsFiniteKernel (ptraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [ptraj_self]; infer_instance
    | succ k hak => rw [ptraj_succ_of_le hak]; infer_instance
  · rw [ptraj_le hba]; infer_instance

instance [∀ n, IsZeroOrMarkovKernel (κ n)] (a b : ℕ) : IsZeroOrMarkovKernel (ptraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [ptraj_self]; infer_instance
    | succ k hak => rw [ptraj_succ_of_le hak]; infer_instance
  · rw [ptraj_le hba]; infer_instance

instance IsMarkovKernel.ptraj [∀ n, IsMarkovKernel (κ n)] (a b : ℕ) :
    IsMarkovKernel (ptraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [ptraj_self]; infer_instance
    | succ k hak =>
      rw [ptraj_succ_of_le hak]
      have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ measurable_IicProdIoc
  · rw [ptraj_le hba]; infer_instance

lemma ptraj_succ_self (a : ℕ) : ptraj κ a (a + 1) =
    (Kernel.id ×ₖ ((κ a).map (piSingleton a))).map (IicProdIoc a (a + 1)) := by
  rw [ptraj_succ_of_le le_rfl, ptraj_self, comp_id]

lemma ptraj_succ_eq_comp (hab : a ≤ b) : ptraj κ a (b + 1) = ptraj κ b (b + 1) ∘ₖ ptraj κ a b := by
  rw [ptraj_succ_self, ← map_comp, ptraj_succ_of_le hab]

/-- Given the trajectory up to time `a`, `ptraj κ a b` gives the distribution of the trajectory
up to time `b`. Then plugging this into `ptraj κ b c` gives the distribution of the trajectory
up to time `c`. -/
theorem ptraj_comp_ptraj (hab : a ≤ b) (hbc : b ≤ c) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [ptraj_succ_eq_comp h, comp_assoc, hk, ← ptraj_succ_eq_comp (hab.trans h)]

/-- This is a technical lemma saying that `ptraj κ a b` consists of two independent parts, the
first one being the identity. It allows to compute integrals. -/
lemma ptraj_eq_prod [∀ n, IsSFiniteKernel (κ n)] (a b : ℕ) : ptraj κ a b =
    (Kernel.id ×ₖ (ptraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map (IicProdIoc a b) := by
  obtain hba | hab := le_total b a
  · rw [ptraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, @fst_prod _ _ _ _ _ _ _ _ _ ?_,
      id_map]
    · exact IsMarkovKernel.map _ (measurable_restrict₂ _)
    all_goals fun_prop
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [ptraj_self, id_map, map_apply, prod_apply, IicProdIoc_self, ← Measure.fst,
      Measure.fst_prod]
    all_goals fun_prop
  | succ k h hk =>
    have : (IicProdIoc (X := X) k (k + 1)) ∘ (Prod.map (IicProdIoc a k) id) =
        (IicProdIoc (h.trans k.le_succ) ∘ (Prod.map id (IocProdIoc a k (k + 1)))) ∘
        prodAssoc := by
      ext x i
      simp only [IicProdIoc_def, MeasurableEquiv.IicProdIoc, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_mk, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Nat.succ_eq_add_one, Equiv.prodAssoc_apply, Prod.map_apply, IocProdIoc]
      split_ifs <;> try rfl
      omega
    nth_rw 1 [← ptraj_comp_ptraj h k.le_succ, hk, ptraj_succ_self, comp_map, comap_map_comm,
      prod_comap, ← id_map_eq_id_comap, map_prod_eq, ← map_comp_right, this, map_comp_right,
      id_prod_eq, prodAssoc_prod, map_comp_right, ← map_prod_map, map_id, ← map_comp,
      map_apply_eq_iff_map_symm_apply_eq, fst_prod_comp_id_prod, ← map_comp_right,
      ← coe_IicProdIoc (h.trans k.le_succ), symm_comp_self, map_id,
      deterministic_congr IicProdIoc_comp_restrict₂.symm, ← deterministic_comp_deterministic,
      comp_deterministic_eq_comap, ← prod_comap, ← map_comp, ← comp_map, ← hk,
      ← ptraj_comp_ptraj h k.le_succ, ptraj_succ_self, map_comp, map_comp, ← map_comp_right,
      ← id_map, map_prod_eq, ← map_comp_right]
    · rfl
    all_goals fun_prop

variable [∀ n, IsMarkovKernel (κ n)]

lemma ptraj_succ_map_frestrictLe₂ (a b : ℕ) :
    (ptraj κ a (b + 1)).map (frestrictLe₂ b.le_succ) = ptraj κ a b := by
  obtain hab | hba := le_or_lt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [ptraj_succ_eq_comp hab, map_comp, ptraj_succ_self, ← map_comp_right,
      frestrictLe₂_comp_IicProdIoc, ← fst_eq, fst_prod, id_comp]
    all_goals fun_prop
  · rw [ptraj_le (Nat.succ_le.2 hba), ptraj_le hba.le, deterministic_map]
    · rfl
    · fun_prop

/-- If we restrict the distribution of the trajectory up to time `c` to times `≤ b` we get
the trajectory up to time `b`. -/
theorem ptraj_map_frestrictLe₂ (a : ℕ) (hbc : b ≤ c) :
    (ptraj κ a c).map (frestrictLe₂ hbc) = ptraj κ a b := by
  induction c, hbc using Nat.le_induction with
  | base => exact map_id ..
  | succ k h hk =>
    rw [← hk, ← frestrictLe₂_comp_frestrictLe₂ h k.le_succ, map_comp_right,
      ptraj_succ_map_frestrictLe₂]
    all_goals fun_prop

lemma ptraj_map_frestrictLe₂_apply (x₀ : Π i : Iic a, X i) (hbc : b ≤ c) :
    (ptraj κ a c x₀).map (frestrictLe₂ hbc) = ptraj κ a b x₀ := by
  rw [← map_apply _ (by fun_prop), ptraj_map_frestrictLe₂]

/-- Same as `ptraj_comp_ptraj` but only assuming `a ≤ b`. It requires Markov kernels. -/
lemma ptraj_comp_ptraj' (c : ℕ) (hab : a ≤ b) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  obtain hbc | hcb := le_total b c
  · rw [ptraj_comp_ptraj hab hbc]
  · rw [ptraj_le hcb, deterministic_comp_eq_map, ptraj_map_frestrictLe₂]

/-- Same as `ptraj_comp_ptraj` but only assuming `b ≤ c`. It requires Markov kernels. -/
lemma ptraj_comp_ptraj'' {b c : ℕ} (hcb : c ≤ b) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  rw [ptraj_le hcb, deterministic_comp_eq_map, ptraj_map_frestrictLe₂]

end Basic

section lmarginalPTraj

/-! ### Integrating against `ptraj` -/

variable (κ)

/-- This function computes the integral of a function `f` against `ptraj`,
and allows to view it as a function depending on all the variables.

This is inspired by `MeasureTheory.lmarginal`, to be able to write
`lmarginalPTraj κ b c (lmarginalPTraj κ a b f) = lmarginalPTraj κ a c`. -/
noncomputable def lmarginalPTraj (a b : ℕ) (f : (Π n, X n) → ℝ≥0∞) (x₀ : Π n, X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x₀ _ z) ∂(ptraj κ a b (frestrictLe a x₀))

/-- If `b ≤ a`, then integrating `f` against `ptraj κ a b` does nothing. -/
lemma lmarginalPTraj_le (hba : b ≤ a) {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) :
    lmarginalPTraj κ a b f = f := by
  ext x₀
  rw [lmarginalPTraj, ptraj_le hba, Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

variable {κ}

lemma lmarginalPTraj_mono (a b : ℕ) {f g : (Π n, X n) → ℝ≥0∞} (hfg : f ≤ g) (x₀ : Π n, X n) :
    lmarginalPTraj κ a b f x₀ ≤ lmarginalPTraj κ a b g x₀ :=
  lintegral_mono fun _ ↦ hfg _

/-- Integrating `f` against `ptraj κ a b x` is the same as integrating only over the variables
  from `x_{a+1}` to `x_b`. -/
lemma lmarginalPTraj_eq_lintegral_map [∀ n, IsSFiniteKernel (κ n)] {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (x₀ : Π n, X n) : lmarginalPTraj κ a b f x₀ =
    ∫⁻ x : (Π i : Ioc a b, X i), f (updateFinset x₀ _ x)
      ∂(ptraj κ a b).map (restrict₂ Ioc_subset_Iic_self) (frestrictLe a x₀) := by
  nth_rw 1 [lmarginalPTraj, ptraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ _, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      frestrictLe_apply, restrict₂, mem_Ioc]
    split_ifs <;> try rfl
    all_goals omega
  all_goals fun_prop

/-- Integrating `f` against `ptraj κ a (a + 1)` is the same as integrating against `κ a`. -/
lemma lmarginalPTraj_succ [∀ n, IsSFiniteKernel (κ n)] (a : ℕ)
    {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPTraj κ a (a + 1) f x₀ =
      ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x₀) := by
  rw [lmarginalPTraj, ptraj_succ_self, lintegral_map, lintegral_id_prod, lintegral_map]
  · congrm ∫⁻ x, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, frestrictLe_apply, piSingleton,
      MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, update]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals omega
  all_goals fun_prop

@[measurability, fun_prop]
lemma measurable_lmarginalPTraj (a b : ℕ) {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (lmarginalPTraj κ a b f) := by
  unfold lmarginalPTraj
  let g : ((i : Iic b) → X i) × (Π n, X n) → ℝ≥0∞ := fun c ↦ f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (ptraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x₀ ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x₀) ∂η x₀
  refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ Iic b <;> simp [h] <;> fun_prop

/-- Integrating `f` against `ptraj κ a b` and then against `ptraj κ b c` is the same
as integrating `f` against `ptraj κ a c`. -/
theorem lmarginalPTraj_self (hab : a ≤ b) (hbc : b ≤ c)
    {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginalPTraj κ a b (lmarginalPTraj κ b c f) = lmarginalPTraj κ a c f := by
  ext x₀
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPTraj_le κ le_rfl (measurable_lmarginalPTraj _ _ hf)]
  · rw [lmarginalPTraj_le κ le_rfl (measurable_lmarginalPTraj _ _ hf)]
  · rw [lmarginalPTraj_le κ le_rfl hf]
  simp_rw [lmarginalPTraj, frestrictLe, restrict_updateFinset,
    updateFinset_updateFinset_subset (Iic_subset_Iic.2 hbc.le)]
  rw [← lintegral_comp, ptraj_comp_ptraj hab.le hbc.le]
  fun_prop

end lmarginalPTraj

end ProbabilityTheory.Kernel

open ProbabilityTheory Kernel

namespace DependsOn

/-! ### Lemmas about `lmarginalPTraj` and `DependsOn` -/

/-- If `f` only depends on the variables up to rank `a` and `a ≤ b`, integrating `f` against
`ptraj κ b c` does nothing. -/
theorem lmarginalPTraj_le [∀ n, IsMarkovKernel (κ n)] (c : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginalPTraj κ b c f = f := by
  ext x
  rw [lmarginalPTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ (ae_of_all _ fun y ↦ hf fun i hi ↦ ?_)
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, Function.updateFinset, mem_Ioc, dite_eq_right_iff]
    omega

/-- If `f` only depends on the variables uo to rank `a`, integrating beyond rank `a` is the same
as integrating up to rank `a`. -/
theorem lmarginalPTraj_const_right [∀ n, IsMarkovKernel (κ n)] {d : ℕ} {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hac : a ≤ c) (had : a ≤ d) :
    lmarginalPTraj κ b c f = lmarginalPTraj κ b d f := by
  wlog hcd : c ≤ d generalizing c d
  · rw [this had hac (le_of_not_le hcd)]
  obtain hbc | hcb := le_total b c
  · rw [← lmarginalPTraj_self hbc hcd mf, hf.lmarginalPTraj_le d mf hac]
  · rw [hf.lmarginalPTraj_le c mf (hac.trans hcb), hf.lmarginalPTraj_le d mf (hac.trans hcb)]

/-- If `f` only depends on variables up to rank `b`, its integral from `a` to `b` only depends on
variables up to rank `a`. -/
theorem dependsOn_lmarginalPTraj [∀ n, IsSFiniteKernel (κ n)] (a : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPTraj κ a b f) (Iic a) := by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPTraj_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  rw [lmarginalPTraj_eq_lintegral_map mf, lmarginalPTraj_eq_lintegral_map mf]
  congrm ∫⁻ z : _, ?_ ∂(ptraj κ a b).map _ (fun i ↦ ?_)
  · exact hxy i.1 i.2
  · refine hf.updateFinset _ ?_
    rwa [← coe_sdiff, Iic_diff_Ioc_self_of_le hab]

end DependsOn

end ptraj
