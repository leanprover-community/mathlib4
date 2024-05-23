/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Nonempty

#align_import data.two_pointing from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Two-pointings

This file defines `TwoPointing α`, the type of two pointings of `α`. A two-pointing is the data of
two distinct terms.

This is morally a Type-valued `Nontrivial`. Another type which is quite close in essence is `Sym2`.
Categorically speaking, `prod` is a cospan in the category of types. This forms the category of
bipointed types. Two-pointed types form a full subcategory of those.

## References

* [nLab, *Coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

open Function

variable {α β : Type*}

/-- Two-pointing of a type. This is a Type-valued termed `Nontrivial`. -/
@[ext]
structure TwoPointing (α : Type*) extends α × α where
  /-- `fst` and `snd` are distinct terms -/
  fst_ne_snd : fst ≠ snd
  deriving DecidableEq
#align two_pointing TwoPointing
#align two_pointing.ext TwoPointing.ext
#align two_pointing.ext_iff TwoPointing.ext_iff

initialize_simps_projections TwoPointing (+toProd, -fst, -snd)

namespace TwoPointing

variable (p : TwoPointing α) (q : TwoPointing β)

theorem snd_ne_fst : p.snd ≠ p.fst :=
  p.fst_ne_snd.symm
#align two_pointing.snd_ne_fst TwoPointing.snd_ne_fst

/-- Swaps the two pointed elements. -/
@[simps]
def swap : TwoPointing α :=
  ⟨(p.snd, p.fst), p.snd_ne_fst⟩
#align two_pointing.swap TwoPointing.swap
#align two_pointing.swap_to_prod TwoPointing.swap_toProd

theorem swap_fst : p.swap.fst = p.snd := rfl
#align two_pointing.swap_fst TwoPointing.swap_fst

theorem swap_snd : p.swap.snd = p.fst := rfl
#align two_pointing.swap_snd TwoPointing.swap_snd

@[simp]
theorem swap_swap : p.swap.swap = p := rfl
#align two_pointing.swap_swap TwoPointing.swap_swap

theorem to_nontrivial : Nontrivial α :=
  ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩
#align two_pointing.to_nontrivial TwoPointing.to_nontrivial

instance [Nontrivial α] : Nonempty (TwoPointing α) :=
  let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩

@[simp]
theorem nonempty_two_pointing_iff : Nonempty (TwoPointing α) ↔ Nontrivial α :=
  ⟨fun ⟨p⟩ ↦ p.to_nontrivial, fun _ => inferInstance⟩
#align two_pointing.nonempty_two_pointing_iff TwoPointing.nonempty_two_pointing_iff

section Pi

variable (α) [Nonempty α]

/-- The two-pointing of constant functions. -/
def pi : TwoPointing (α → β) where
  fst _ := q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd (congr_fun h (Classical.arbitrary α))
#align two_pointing.pi TwoPointing.pi

@[simp]
theorem pi_fst : (q.pi α).fst = const α q.fst :=
  rfl
#align two_pointing.pi_fst TwoPointing.pi_fst

@[simp]
theorem pi_snd : (q.pi α).snd = const α q.snd :=
  rfl
#align two_pointing.pi_snd TwoPointing.pi_snd

end Pi

/-- The product of two two-pointings. -/
def prod : TwoPointing (α × β) where
  fst := (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)
#align two_pointing.prod TwoPointing.prod

@[simp]
theorem prod_fst : (p.prod q).fst = (p.fst, q.fst) :=
  rfl
#align two_pointing.prod_fst TwoPointing.prod_fst

@[simp]
theorem prod_snd : (p.prod q).snd = (p.snd, q.snd) :=
  rfl
#align two_pointing.prod_snd TwoPointing.prod_snd

/-- The sum of two pointings. Keeps the first point from the left and the second point from the
right. -/
protected def sum : TwoPointing (Sum α β) :=
  ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩
#align two_pointing.sum TwoPointing.sum

@[simp]
theorem sum_fst : (p.sum q).fst = Sum.inl p.fst :=
  rfl
#align two_pointing.sum_fst TwoPointing.sum_fst

@[simp]
theorem sum_snd : (p.sum q).snd = Sum.inr q.snd :=
  rfl
#align two_pointing.sum_snd TwoPointing.sum_snd

/-- The `false`, `true` two-pointing of `Bool`. -/
protected def bool : TwoPointing Bool :=
  ⟨(false, true), Bool.false_ne_true⟩
#align two_pointing.bool TwoPointing.bool

@[simp]
theorem bool_fst : TwoPointing.bool.fst = false := rfl
#align two_pointing.bool_fst TwoPointing.bool_fst

@[simp]
theorem bool_snd : TwoPointing.bool.snd = true := rfl
#align two_pointing.bool_snd TwoPointing.bool_snd

instance : Inhabited (TwoPointing Bool) :=
  ⟨TwoPointing.bool⟩

/-- The `False`, `True` two-pointing of `Prop`. -/
protected def prop : TwoPointing Prop :=
  ⟨(False, True), false_ne_true⟩
#align two_pointing.Prop TwoPointing.prop

@[simp]
theorem prop_fst : TwoPointing.prop.fst = False :=
  rfl
#align two_pointing.Prop_fst TwoPointing.prop_fst

@[simp]
theorem prop_snd : TwoPointing.prop.snd = True :=
  rfl
#align two_pointing.Prop_snd TwoPointing.prop_snd

end TwoPointing
