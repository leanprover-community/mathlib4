/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Restriction

/-! # Auxiliary maps for Ionescu-Tulcea theorem

This file contains auxiliary maps which are used to prove the Ionescu-Tulcea theorem.
-/

open Finset Preorder

section Definitions

section LinearOrder

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι → Type*}

/-- Gluing `Ioc a b` and `Ioc b c` into `Ioc a c`. -/
def IocProdIoc (a b c : ι) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (i : Ioc a c) : X i :=
  if h : i ≤ b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

@[measurability, fun_prop]
lemma measurable_IocProdIoc [∀ i, MeasurableSpace (X i)] {a b c : ι} :
    Measurable (IocProdIoc (X := X) a b c) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

variable [LocallyFiniteOrderBot ι]

/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. If `b < a`, this is just a projection on the first
coordinate followed by a restriction, see `IicProdIoc_le`. -/
def IicProdIoc (a b : ι) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) (i : Iic b) : X i :=
  if h : i ≤ a
    then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

/-- When `IicProdIoc` is only partially applied (i.e. `IicProdIoc a b x` but not
`IicProdIoc a b x i`) `simp [IicProdIoc]` won't unfold the definition.
This lemma allows to unfold it by writing `simp [IicProdIoc_def]`. -/
lemma IicProdIoc_def (a b : ι) :
    IicProdIoc (X := X) a b = fun x i ↦ if h : i.1 ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩ := rfl

lemma frestrictLe₂_comp_IicProdIoc {a b : ι} (hab : a ≤ b) :
    (frestrictLe₂ hab) ∘ (IicProdIoc (X := X) a b) = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

lemma restrict₂_comp_IicProdIoc (a b : ι) :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

@[simp]
lemma IicProdIoc_self (a : ι) : IicProdIoc (X := X) a a = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

lemma IicProdIoc_le {a b : ι} (hba : b ≤ a) :
    IicProdIoc (X := X) a b = (frestrictLe₂ hba) ∘ Prod.fst := by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]

lemma IicProdIoc_comp_restrict₂ {a b : ι} :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

variable [∀ i, MeasurableSpace (X i)]

@[measurability, fun_prop]
lemma measurable_IicProdIoc {m n : ι} : Measurable (IicProdIoc (X := X) m n) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

namespace MeasurableEquiv

/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. This version requires `a ≤ b` to get a measurable
equivalence. -/
def IicProdIoc {a b : ι} (hab : a ≤ b) :
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
  measurable_invFun := by dsimp; fun_prop

lemma coe_IicProdIoc {a b : ι} (hab : a ≤ b) :
    ⇑(IicProdIoc (X := X) hab) = _root_.IicProdIoc a b := rfl

lemma coe_IicProdIoc_symm {a b : ι} (hab : a ≤ b) :
    ⇑(IicProdIoc (X := X) hab).symm =
    fun x ↦ (frestrictLe₂ hab x, restrict₂ Ioc_subset_Iic_self x) := rfl

/-- Gluing `Iic a` and `Ioi a` into `ℕ`, version as a measurable equivalence
on dependent functions. -/
def IicProdIoi (a : ι) :
    ((Π i : Iic a, X i) × (Π i : Set.Ioi a, X i)) ≃ᵐ (Π n, X n) where
  toFun := fun x i ↦ if hi : i ≤ a
    then x.1 ⟨i, mem_Iic.2 hi⟩
    else x.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
  invFun := fun x ↦ (fun i ↦ x i, fun i ↦ x i)
  left_inv := fun x ↦ by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
  right_inv := fun x ↦ by simp
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    by_cases hi : i ≤ a <;> simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]
    · exact measurable_fst.eval
    · exact measurable_snd.eval
  measurable_invFun := Measurable.prodMk (measurable_restrict _) (Set.measurable_restrict _)

end MeasurableEquiv

end LinearOrder

section Nat

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Identifying `{a + 1}` with `Ioc a (a + 1)`, as a measurable equiv on dependent functions. -/
def MeasurableEquiv.piSingleton (a : ℕ) : X (a + 1) ≃ᵐ Π i : Ioc a (a + 1), X i where
  toFun x i := (Nat.mem_Ioc_succ.1 i.2).symm ▸ x
  invFun x := x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ funext fun i ↦ by cases Nat.mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i ↦ (MeasurableEquiv.cast _ ?_).measurable)
    cases Nat.mem_Ioc_succ' i; rfl
  measurable_invFun := measurable_pi_apply _

end Nat

end Definitions

section Lemmas

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι → Type*}

lemma _root_.IocProdIoc_preimage {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c)
    (s : (i : Ioc a c) → Set (X i)) :
    IocProdIoc a b c ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_right hbc) s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_left hab) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IocProdIoc, forall_const, Subtype.forall,
    mem_Ioc, Set.mem_prod, restrict₂]
  refine ⟨fun h ↦ ⟨fun i ⟨hi1, hi2⟩ ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i ⟨hi1, hi2⟩ ↦ ?_⟩
  · convert h i ⟨hi1, hi2.trans hbc⟩
    rw [dif_pos hi2]
  · convert h i ⟨lt_of_le_of_lt hab hi1, hi2⟩
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i ⟨hi1, hi3⟩
    · exact h2 i ⟨not_le.1 hi3, hi2⟩

variable [LocallyFiniteOrderBot ι]

lemma _root_.IicProdIoc_preimage {a b : ι} (hab : a ≤ b) (s : (i : Iic b) → Set (X i)) :
    IicProdIoc a b ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| frestrictLe₂ (π := (fun n ↦ Set (X n))) hab s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) Ioc_subset_Iic_self s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc_def, forall_const,
    Subtype.forall, mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i hi ↦ ?_⟩
  · convert h i (hi.trans hab)
    rw [dif_pos hi]
  · convert h i hi2
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i hi3
    · exact h2 i ⟨not_le.1 hi3, hi⟩

end Lemmas
