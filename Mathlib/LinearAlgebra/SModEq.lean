/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient

#align_import linear_algebra.smodeq from "leanprover-community/mathlib"@"146d3d1fa59c091fedaad8a4afa09d6802886d24"

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

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y
#align smodeq SModEq

notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

variable {U U₁ U₂}

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
protected theorem SModEq.def :
    x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl
#align smodeq.def SModEq.def

namespace SModEq

theorem sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U := by rw [SModEq.def, Submodule.Quotient.eq]
#align smodeq.sub_mem SModEq.sub_mem

@[simp]
theorem top : x ≡ y [SMOD (⊤ : Submodule R M)] :=
  (Submodule.Quotient.eq ⊤).2 mem_top
#align smodeq.top SModEq.top

@[simp]
theorem bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y := by
  rw [SModEq.def, Submodule.Quotient.eq, mem_bot, sub_eq_zero]
#align smodeq.bot SModEq.bot

@[mono]
theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
  (Submodule.Quotient.eq U₂).2 <| HU <| (Submodule.Quotient.eq U₁).1 hxy
#align smodeq.mono SModEq.mono

@[refl]
protected theorem refl (x : M) : x ≡ x [SMOD U] :=
  @rfl _ _
#align smodeq.refl SModEq.refl

protected theorem rfl : x ≡ x [SMOD U] :=
  SModEq.refl _
#align smodeq.rfl SModEq.rfl

instance : IsRefl _ (SModEq U) :=
  ⟨SModEq.refl⟩

@[symm]
nonrec theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm
#align smodeq.symm SModEq.symm

@[trans]
nonrec theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz
#align smodeq.trans SModEq.trans

instance instTrans : Trans (SModEq U) (SModEq U) (SModEq U) where
  trans := trans

theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] := by
  rw [SModEq.def] at hxy₁ hxy₂ ⊢
  simp_rw [Quotient.mk_add, hxy₁, hxy₂]
#align smodeq.add SModEq.add

theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] := by
  rw [SModEq.def] at hxy ⊢
  simp_rw [Quotient.mk_smul, hxy]
#align smodeq.smul SModEq.smul

theorem mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
    (hxy₂ : x₂ ≡ y₂ [SMOD I]) : x₁ * x₂ ≡ y₁ * y₂ [SMOD I] := by
  simp only [SModEq.def, Ideal.Quotient.mk_eq_mk, map_mul] at hxy₁ hxy₂ ⊢
  rw [hxy₁, hxy₂]

theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U := by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]
#align smodeq.zero SModEq.zero

theorem map (hxy : x ≡ y [SMOD U]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
  (Submodule.Quotient.eq _).2 <| f.map_sub x y ▸ mem_map_of_mem <| (Submodule.Quotient.eq _).1 hxy
#align smodeq.map SModEq.map

theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
  (Submodule.Quotient.eq _).2 <|
    show f (x - y) ∈ V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy
#align smodeq.comap SModEq.comap

theorem eval {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X]) :
    f.eval x ≡ f.eval y [SMOD I] := by
  rw [SModEq.def] at h ⊢
  show Ideal.Quotient.mk I (f.eval x) = Ideal.Quotient.mk I (f.eval y)
  replace h : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := h
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, h]
#align smodeq.eval SModEq.eval

end SModEq
