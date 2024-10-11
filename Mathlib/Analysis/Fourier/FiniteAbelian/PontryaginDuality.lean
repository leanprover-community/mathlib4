/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.DirectSum.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.FiniteAbelian

/-!
# Pontryagin duality for finite abelian groups

This file proves the Pontryagin duality in case of finite abelian groups. This states that any
finite abelian group is canonically isomorphic to its double dual (the space of complex-valued
characters of its space of complex-valued characters).

We first prove it for `ZMod n` and then extend to all finite abelian groups using the
Structure Theorem.
-/

noncomputable section

open Circle Finset Function Multiplicative
open Fintype (card)
open scoped BigOperators DirectSum

variable {α : Type*} [AddCommGroup α] {n : ℕ} {a b : α}

namespace AddChar

private def zmodAuxAux (n : ℕ) : ℤ →+ Additive Circle where
  toFun x := .ofMul <| e <| x / n
  map_zero' := by dsimp; rw [Int.cast_zero, zero_div, ofMul_eq_zero, map_zero_eq_one]
  map_add' x y := by rw [← ofMul_mul, Equiv.apply_eq_iff_eq, Int.cast_add, add_div, map_add_eq_mul]

@[simp]
lemma zmodAuxAux_apply (n : ℕ) (z : ℤ) : zmodAuxAux n z = Additive.ofMul (e <| z / n) := rfl

/-- The character sending `k : ZMod n` to `e ^ (2 * π * i * k / n)`. -/
private def zmodAux (n : ℕ) : AddChar (ZMod n) Circle :=
  AddChar.toAddMonoidHomEquiv.symm <| ZMod.lift n ⟨zmodAuxAux n, by
    obtain hn | hn := eq_or_ne (n : ℝ) 0 <;> simp [hn, zmodAuxAux]⟩

--TODO: Heavily generalise. Yaël's attempts at generalising failed :(
@[simp] lemma aux (n : ℕ) (h) :
    (⟨zmodAuxAux n, h⟩ : {f : ℤ →+ Additive Circle // f n = 0}) = zmodAuxAux n := rfl

@[simp] lemma zmodAux_apply (n : ℕ) (z : ℤ) : zmodAux n z = e (z / n) := by simp [zmodAux]

-- probably an evil lemma
-- @[simp] lemma zmodAux_apply (n : ℕ) (x : ZMod n) : zmodAux n x = e (x / n) :=
-- by simp [zmodAux]

lemma zmodAux_injective (hn : n ≠ 0) : Injective (zmodAux n) := by
  replace hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp [zmodAux, ZMod.lift_injective, CharP.intCast_eq_zero_iff _ n, e_eq_one, div_eq_iff hn,
    mul_comm _ (n : ℝ), -forall_exists_index]
  norm_cast
  exact fun _ ↦ id

/-- Indexing of the complex characters of `ZMod n`. `AddChar.zmod n x` is the character sending `y`
to `e ^ (2 * π * i * x * y / n)`. -/
def zmod (n : ℕ) (x : ZMod n) : AddChar (ZMod n) Circle :=
  (zmodAux n).compAddMonoidHom <| AddMonoidHom.mulLeft x

@[simp] lemma zmod_apply (n : ℕ) (x y : ℤ) :
    (zmod n x) (y : ZMod n) = e (x * y / n) := by
  simp [zmod, ← Int.cast_mul x y, -Int.cast_mul]

@[simp] lemma zmod_zero (n : ℕ) : zmod n 0 = 1 := by
  refine DFunLike.ext _ _ ?_
  rw [ZMod.intCast_surjective.forall]
  rintro y
  simpa using zmod_apply n 0 y

@[simp] lemma zmod_add (n : ℕ) : ∀ x y : ZMod n, zmod n (x + y) = zmod n x * zmod n y := by
  simp only [DFunLike.ext_iff, ZMod.intCast_surjective.forall, ← Int.cast_add, AddChar.mul_apply,
    zmod_apply]
  simp [add_mul, add_div, map_add_eq_mul]

-- probably an evil lemma
-- @[simp] lemma zmod_apply (n : ℕ) (x y : ZMod n) : zmod n x y = e (x * y / n) :=
-- by simp [addChar.zmod, ZMod.coe_mul]

lemma zmod_injective (hn : n ≠ 0) : Injective (zmod n) := by
  simp_rw [Injective, ZMod.intCast_surjective.forall]
  rintro x y h
  replace hn : (n : ℝ) ≠ 0 := by positivity
  simpa only [Int.cast_one, mul_one, one_mul, e_inj, AddCommGroup.div_modEq_div hn,
    AddCommGroup.intCast_modEq_intCast', AddCommGroup.modEq_iff_int_modEq,
    CharP.intCast_eq_intCast (ZMod n) n] using (zmod_apply _ _ _).symm.trans <|
    (DFunLike.congr_fun h ((1 : ℤ) : ZMod n)).trans <| zmod_apply _ _ _

@[simp] lemma zmod_inj (hn : n ≠ 0) {x y : ZMod n} : zmod n x = zmod n y ↔ x = y :=
  (zmod_injective hn).eq_iff

def zmodHom (n : ℕ) : AddChar (ZMod n) (AddChar (ZMod n) Circle) where
  toFun := zmod n
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

def mkZModAux {ι : Type} [DecidableEq ι] (n : ι → ℕ) (u : ∀ i, ZMod (n i)) :
    AddChar (⨁ i, ZMod (n i)) Circle :=
  AddChar.directSum fun i ↦ zmod (n i) (u i)

lemma mkZModAux_injective {ι : Type} [DecidableEq ι] {n : ι → ℕ} (hn : ∀ i, n i ≠ 0) :
    Injective (mkZModAux n) :=
  AddChar.directSum_injective.comp fun f g h ↦ by simpa [Function.funext_iff, hn] using h

/-- The circle-valued characters of a finite abelian group are the same as its complex-valued
characters. -/
def circleEquivComplex [Finite α] : AddChar α Circle ≃+ AddChar α ℂ where
  toFun ψ := toMonoidHomEquiv.symm <| coeHom.comp ψ.toMonoidHom
  invFun ψ :=
    { toFun := fun a ↦ (⟨ψ a, mem_sphere_zero_iff_norm.2 <| ψ.norm_apply _⟩ : Circle)
      map_zero_eq_one' := by simp [Circle]
      map_add_eq_mul' := fun a b ↦ by ext : 1; simp [map_add_eq_mul] }
  left_inv ψ := by ext : 1; simp
  right_inv ψ := by ext : 1; simp
  map_add' ψ χ := rfl

@[simp] lemma card_eq [Fintype α] : card (AddChar α ℂ) = card α := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' : ∀ i, n i ≠ 0 := fun i ↦ by have := hn i; positivity
  let f : α → AddChar α ℂ := fun a ↦ coeHom.compAddChar ((mkZModAux n <| e a).compAddMonoidHom e)
  have hf : Injective f := circleEquivComplex.injective.comp
    ((compAddMonoidHom_injective_left _ e.surjective).comp <| (mkZModAux_injective hn').comp <|
      DFunLike.coe_injective.comp <| e.injective.comp Additive.ofMul.injective)
  exact (card_addChar_le _ _).antisymm (Fintype.card_le_of_injective _ hf)

/-- `ZMod n` is (noncanonically) isomorphic to its group of characters. -/
def zmodAddEquiv (hn : n ≠ 0) : ZMod n ≃+ AddChar (ZMod n) ℂ := by
  haveI : NeZero n := ⟨hn⟩
  refine AddEquiv.ofBijective
    (circleEquivComplex.toAddMonoidHom.comp <| AddChar.toAddMonoidHom <| zmodHom n) ?_
  rw [Fintype.bijective_iff_injective_and_card, card_eq]
  exact ⟨circleEquivComplex.injective.comp <| zmod_injective hn, rfl⟩

@[simp] lemma zmodAddEquiv_apply [NeZero n] (x : ZMod n) :
    zmodAddEquiv (NeZero.ne _) x = circleEquivComplex (zmod n x) := rfl

section Finite
variable (α) [Finite α]

/-- Complex-valued characters of a finite abelian group `α` form a basis of `α → ℂ`. -/
def complexBasis : Basis (AddChar α ℂ) ℂ (α → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) <| by
    cases nonempty_fintype α; rw [card_eq, Module.finrank_fintype_fun_eq_card]

@[simp, norm_cast]
lemma coe_complexBasis : ⇑(complexBasis α) = ((⇑) : AddChar α ℂ → α → ℂ) := by
  rw [complexBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

variable {α}

@[simp]
lemma complexBasis_apply (ψ : AddChar α ℂ) : complexBasis α ψ = ψ := by rw [coe_complexBasis]

lemma exists_apply_ne_zero : (∃ ψ : AddChar α ℂ, ψ a ≠ 1) ↔ a ≠ 0 := by
  refine ⟨?_, fun ha ↦ ?_⟩
  · rintro ⟨ψ, hψ⟩ rfl
    exact hψ ψ.map_zero_eq_one
  classical
  by_contra! h
  let f : α → ℂ := fun b ↦ if a = b then 1 else 0
  have h₀ := congr_fun ((complexBasis α).sum_repr f) 0
  have h₁ := congr_fun ((complexBasis α).sum_repr f) a
  simp only [complexBasis_apply, Fintype.sum_apply, Pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_eq_one, if_pos rfl, if_neg ha, f] at h₀ h₁
  exact one_ne_zero (h₁.symm.trans h₀)

lemma forall_apply_eq_zero : (∀ ψ : AddChar α ℂ, ψ a = 1) ↔ a = 0 := by
  simpa using exists_apply_ne_zero.not

lemma doubleDualEmb_injective : Injective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) :=
  doubleDualEmb.ker_eq_bot_iff.1 <| eq_bot_iff.2 fun a ha ↦
    forall_apply_eq_zero.1 fun ψ ↦ by simpa using DFunLike.congr_fun ha (Additive.ofMul ψ)

lemma doubleDualEmb_bijective : Bijective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) := by
  cases nonempty_fintype α
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨doubleDualEmb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]
lemma doubleDualEmb_inj : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = doubleDualEmb b ↔ a = b :=
  doubleDualEmb_injective.eq_iff

@[simp] lemma doubleDualEmb_eq_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = 0 ↔ a = 0 := by
  rw [← map_zero doubleDualEmb, doubleDualEmb_inj]

lemma doubleDualEmb_ne_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) ≠ 0 ↔ a ≠ 0 :=
  doubleDualEmb_eq_zero.not

/-- The double dual isomorphism. -/
def doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ :=
  AddEquiv.ofBijective _ doubleDualEmb_bijective

@[simp]
lemma coe_doubleDualEquiv : ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ) = doubleDualEmb := rfl

@[simp] lemma doubleDualEmb_doubleDualEquiv_symm_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEmb (doubleDualEquiv.symm a) = a :=
  doubleDualEquiv.apply_symm_apply _

@[simp] lemma doubleDualEquiv_symm_doubleDualEmb_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEquiv.symm (doubleDualEmb a) = a := doubleDualEquiv.symm_apply_apply _

end Finite

lemma sum_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    ∑ ψ : AddChar α ℂ, ψ a = if a = 0 then (Fintype.card α : ℂ) else 0 := by
  simpa using sum_eq_ite (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ)

lemma expect_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    𝔼 ψ : AddChar α ℂ, ψ a = if a = 0 then 1 else 0 := by
  simpa using expect_eq_ite (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ)

lemma sum_apply_eq_zero_iff_ne_zero [Finite α] : ∑ ψ : AddChar α ℂ, ψ a = 0 ↔ a ≠ 0 := by
  classical
  cases nonempty_fintype α
  rw [sum_apply_eq_ite, Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

lemma sum_apply_ne_zero_iff_eq_zero [Finite α] : ∑ ψ : AddChar α ℂ, ψ a ≠ 0 ↔ a = 0 :=
  sum_apply_eq_zero_iff_ne_zero.not_left

lemma expect_apply_eq_zero_iff_ne_zero [Finite α] : 𝔼 ψ : AddChar α ℂ, ψ a = 0 ↔ a ≠ 0 := by
  classical
  cases nonempty_fintype α
  rw [expect_apply_eq_ite, one_ne_zero.ite_eq_right_iff]

lemma expect_apply_ne_zero_iff_eq_zero [Finite α] : 𝔼 ψ : AddChar α ℂ, ψ a ≠ 0 ↔ a = 0 :=
  expect_apply_eq_zero_iff_ne_zero.not_left

end AddChar
