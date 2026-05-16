/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth

Modifications:
Copyright (c) 2026 Edwin Park.
-/
import Mathlib.Computability.SingleOracle.Oracle
import Mathlib.Order.Antisymmetrization
open Oracle.Single

@[simp] abbrev TuringReducible (f g : ℕ → ℕ) : Prop := RecursiveIn g f
@[simp] abbrev TuringReducibleStrict (f g : ℕ → ℕ) : Prop := RecursiveIn g f ∧ ¬ RecursiveIn f g
@[simp] abbrev TuringEquivalent (f g : ℕ → ℕ) : Prop := AntisymmRel TuringReducible f g

@[reducible,simp] scoped[Computability] infix : 50 " ≤ᵀᶠ " => TuringReducible
@[reducible,simp] scoped[Computability] infix : 50 " ≡ᵀᶠ " => TuringEquivalent
@[reducible,simp] scoped[Computability] infix : 50 " <ᵀᶠ " => TuringReducibleStrict

open scoped Computability

protected theorem TuringReducible.refl (f : ℕ → ℕ) : f ≤ᵀᶠ f := Oracle.Single.RecursiveIn.oracle
protected theorem TuringReducible.rfl {f} : f ≤ᵀᶠ f := .refl _

theorem TuringReducible.trans {f g h} (hg : f ≤ᵀᶠ g) (hh : g ≤ᵀᶠ h) : f ≤ᵀᶠ h := by
  generalize z : (↑f : ℕ →. ℕ)=x at hg
  simp only [TuringReducible,z] at *
  induction hg with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | oracle => exact hh
  | pair hf hh hf_ih hh_ih => (expose_names; exact RecursiveIn.pair hf_ih hh_ih)
  | comp hf hh hf_ih hh_ih => (expose_names; exact RecursiveIn.comp hf_ih hh_ih)
  | prec hf hh hf_ih hh_ih => (expose_names; exact RecursiveIn.prec hf_ih hh_ih)
  | rfind hf ih => (expose_names; exact RecursiveIn.rfind ih)

theorem TuringReducible.trans' {f g h} (hg : RecursiveIn g f) (hh : g ≤ᵀᶠ h) : RecursiveIn h f := by
  generalize z : (↑f : ℕ →. ℕ)=x at hg
  simp only [TuringReducible,z] at *
  induction hg with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | oracle => exact hh
  | pair hf hh hf_ih hh_ih => (expose_names; exact RecursiveIn.pair hf_ih hh_ih)
  | comp hf hh hf_ih hh_ih => (expose_names; exact RecursiveIn.comp hf_ih hh_ih)
  | prec hf hh hf_ih hh_ih => (expose_names; exact RecursiveIn.prec hf_ih hh_ih)
  | rfind hf ih => (expose_names; exact RecursiveIn.rfind ih)

instance : IsTrans (ℕ → ℕ) TuringReducible := ⟨@TuringReducible.trans⟩
instance : IsPreorder (ℕ → ℕ) TuringReducible where refl := .refl
theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv
@[refl] protected theorem TuringEquivalent.refl (f : ℕ → ℕ) : f ≡ᵀᶠ f :=
  Equivalence.refl equivalence f
@[symm] theorem TuringEquivalent.symm {f g : ℕ → ℕ} (h : f ≡ᵀᶠ g) : g ≡ᵀᶠ f :=
  Equivalence.symm equivalence h
@[trans] theorem TuringEquivalent.trans {f g h : ℕ → ℕ} (h₁ : f ≡ᵀᶠ g) (h₂ : g ≡ᵀᶠ h) : f ≡ᵀᶠ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ → ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

abbrev FuncTuringDegree := Antisymmetrization _ TuringReducible
private instance : Preorder (ℕ → ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans
  lt := TuringReducibleStrict
