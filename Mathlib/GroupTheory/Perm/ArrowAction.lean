/-
Copyright (c) 2023 Junyan Xu, Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
-- import Mathlib.Data.Set.Card

/-!  Subgroup of `Equiv.Perm α` preserving a function `p : α → ι`

Let `α` and `ι` by types.

* `DomMulAct.mem_stabilizer_iff` proves that the stabilizer
  of `Equiv.Perm α` of `p : α → ι` is the subgroup of `g : Equiv.Perm α`
  such that `p ∘ g = p`.

* `DomMulAct.stabilizerMulEquiv` is the `MulEquiv` from
  the MulOpposite of this stabilizer to the product,
  for `i : ι`, of `Equiv.Perm {a // p a = i}`.

-/

variable {α ι : Type*} {p : α → ι}

open Equiv MulAction

namespace DomMulAct

lemma mem_stabilizer_iff {g : DomMulAct (Perm α)} :
    g ∈ stabilizer (DomMulAct (Perm α)) p ↔ p ∘ (DomMulAct.mk.symm g :) = p := by
  simp only [MulAction.mem_stabilizer_iff]; rfl

/-- The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) p`
  to the product of the `Equiv.Perm {a // p a = i} -/
def stabilizerEquiv_invFun (g : ∀ i, Perm {a // p a = i}) (a : α) : α := g (p a) ⟨a, rfl⟩

lemma stabilizerEquiv_invFun_eq (g : ∀ i, Perm {a // p a = i}) {a : α} {i : ι} (h : p a = i) :
    stabilizerEquiv_invFun g a = g i ⟨a, h⟩ := by subst h; rfl

lemma comp_stabilizerEquiv_invFun (g : ∀ i, Perm {a // p a = i}) (a : α) :
    p (stabilizerEquiv_invFun g a) = p a :=
  (g (p a) ⟨a, rfl⟩).prop

/-- The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) p`
  to the product of the `Equiv.Perm {a | p a = i} (as an `Equiv.Perm α`) -/
def stabilizerEquiv_invFun_aux (g : ∀ i, Perm {a // p a = i}) : Perm α where
  toFun := stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i ↦ (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| p a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| p a).right_inv _)

variable (p)

/-- The `MulEquiv` from the `MulOpposite` of `MulAction.stabilizer (DomMulAct (Perm α)) p`
  to the product of the `Equiv.Perm {a // p a = i}` -/
def stabilizerMulEquiv : (stabilizer (DomMulAct (Perm α)) p)ᵐᵒᵖ ≃* (∀ i, Perm {a // p a = i}) where
  toFun g i := Perm.subtypePerm (DomMulAct.mk.symm g.unop) fun a ↦ by
    rw [← Function.comp_apply (f := p), DomMulAct.mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨DomMulAct.mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply, symm_apply_apply, Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  left_inv g := rfl
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' g h := by rfl

lemma stabilizerMulEquiv_apply (g : (stabilizer (DomMulAct (Perm α)) p)ᵐᵒᵖ) {a : α} {i : ι} (h : p a = i) :
    ((stabilizerMulEquiv p)) g i ⟨a, h⟩ = (DomMulAct.mk.symm g.unop : Equiv.Perm α) a := rfl

end DomMulAct
