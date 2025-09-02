/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# modular equivalence for submodule
-/


open Submodule

open Polynomial

variable {R : Type*} [Ring R]
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module R M] (U U₁ U₂ : Submodule R M)
variable {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}
variable {N : Type*} [AddCommGroup N] [Module R N] (V V₁ V₂ : Submodule R N)

/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y

@[inherit_doc] notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

variable {U U₁ U₂}

protected theorem SModEq.def :
    x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl

namespace SModEq

theorem sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U := by rw [SModEq.def, Submodule.Quotient.eq]

@[simp]
theorem top : x ≡ y [SMOD (⊤ : Submodule R M)] :=
  (Submodule.Quotient.eq ⊤).2 mem_top

@[simp]
theorem bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y := by
  rw [SModEq.def, Submodule.Quotient.eq, mem_bot, sub_eq_zero]

@[mono]
theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
  (Submodule.Quotient.eq U₂).2 <| HU <| (Submodule.Quotient.eq U₁).1 hxy

@[refl]
protected theorem refl (x : M) : x ≡ x [SMOD U] :=
  @rfl _ _

protected theorem rfl : x ≡ x [SMOD U] :=
  SModEq.refl _

instance : IsRefl _ (SModEq U) :=
  ⟨SModEq.refl⟩

@[symm]
nonrec theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm

theorem comm : x ≡ y [SMOD U] ↔ y ≡ x [SMOD U] := ⟨symm, symm⟩

@[trans]
nonrec theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz

instance instTrans : Trans (SModEq U) (SModEq U) (SModEq U) where
  trans := trans

@[gcongr]
theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_add, hxy₁, hxy₂]

@[gcongr]
theorem sum {ι} {s : Finset ι} {x y : ι → M}
    (hxy : ∀ i ∈ s, x i ≡ y i [SMOD U]) : ∑ i ∈ s, x i ≡ ∑ i ∈ s, y i [SMOD U] := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.sum_cons, Finset.sum_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj ↦ hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]
theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
lemma nsmul (hxy : x ≡ y [SMOD U]) (n : ℕ) : n • x ≡ n • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
lemma zsmul (hxy : x ≡ y [SMOD U]) (n : ℤ) : n • x ≡ n • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]

@[gcongr]
theorem mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
    (hxy₂ : x₂ ≡ y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_mul] at hxy₁ hxy₂ ⊢
  rw [hxy₁, hxy₂]

@[gcongr]
theorem prod {I : Ideal A} {ι} {s : Finset ι} {x y : ι → A}
    (hxy : ∀ i ∈ s, x i ≡ y i [SMOD I]) : ∏ i ∈ s, x i ≡ ∏ i ∈ s, y i [SMOD I] := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [SModEq.rfl]
  | cons i s _ ih =>
    grw [Finset.prod_cons, Finset.prod_cons, hxy i (Finset.mem_cons_self i s),
      ih (fun j hj ↦ hxy j (Finset.mem_cons_of_mem hj))]

@[gcongr]
lemma pow {I : Ideal A} {x y : A} (n : ℕ) (hxy : x ≡ y [SMOD I]) :
    x ^ n ≡ y ^ n [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_pow] at hxy ⊢
  rw [hxy]

@[gcongr]
lemma neg (hxy : x ≡ y [SMOD U]) : - x ≡ - y [SMOD U] := by
  simpa only [SModEq.def, Quotient.mk_neg, neg_inj]

@[gcongr]
lemma sub (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ - x₂ ≡ y₁ - y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_sub, hxy₁, hxy₂]

theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U := by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]

theorem _root_.sub_smodEq_zero : x - y ≡ 0 [SMOD U] ↔ x ≡ y [SMOD U] := by
  simp only [SModEq.sub_mem, sub_zero]

theorem map (hxy : x ≡ y [SMOD U]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
  (Submodule.Quotient.eq _).2 <| f.map_sub x y ▸ mem_map_of_mem <| (Submodule.Quotient.eq _).1 hxy

theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
  (Submodule.Quotient.eq _).2 <|
    show f (x - y) ∈ V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy

@[gcongr]
theorem eval {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X]) :
    f.eval x ≡ f.eval y [SMOD I] := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  gcongr

end SModEq
