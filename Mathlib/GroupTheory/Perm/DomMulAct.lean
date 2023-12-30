/-
Copyright (c) 2023 Junyan Xu, Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm


/-!  Subgroup of `Equiv.Perm α` preserving a function

Let `α` and `ι` by types and let `p : α → ι`

* `DomMulAct.mem_stabilizer_iff` proves that the stabilizer of `p : α → ι`
  in `(Equiv.Perm α)ᵈᵐᵃ` is the set of `g : (Equiv.Perm α)ᵈᵐᵃ` such that `p ∘ (mk.symm g) = p`.

  The natural equivalence from `stabilizer (Perm α)ᵈᵐᵃ p` to `{ g : Perm α // p ∘ g = p }`
  can be obtained as `subtypeEquiv mk.symm (fun _ => mem_stabilizer_iff)`

* `DomMulAct.stabilizerMulEquiv` is the `MulEquiv` from
  the MulOpposite of this stabilizer to the product,
  for `i : ι`, of `Equiv.Perm {a // p a = i}`.

* Under `Fintype α` and `Fintype ι`, `DomMulAct.stabilizer_card p` computes
  the cardinality of the type of permutations preserving `p` :
  `Nat.card {f : Perm α // p ∘ f = p} =
    Finset.univ.prod fun i => (Nat.card {a // p a = i}).factorial `

-/

variable {α ι : Type*} {p : α → ι}

open Equiv MulAction

namespace DomMulAct

lemma mem_stabilizer_iff {g : (Perm α)ᵈᵐᵃ} :
    g ∈ stabilizer (Perm α)ᵈᵐᵃ p ↔ p ∘ (mk.symm g :) = p := by
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

/-- The `MulEquiv` from the `MulOpposite` of `MulAction.stabilizer (Perm α)ᵈᵐᵃ p`
  to the product of the `Equiv.Perm {a // p a = i}` -/
def stabilizerMulEquiv : (stabilizer (Perm α)ᵈᵐᵃ p)ᵐᵒᵖ ≃* (∀ i, Perm {a // p a = i}) where
  toFun g i := Perm.subtypePerm (mk.symm g.unop) fun a ↦ by
    rw [← Function.comp_apply (f := p), mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply, symm_apply_apply, Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  left_inv g := rfl
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' g h := by rfl

variable {p}

lemma stabilizerMulEquiv_apply (g : (stabilizer (Perm α)ᵈᵐᵃ p)ᵐᵒᵖ) {a : α} {i : ι} (h : p a = i) :
    ((stabilizerMulEquiv p)) g i ⟨a, h⟩ = (mk.symm g.unop : Equiv.Perm α) a := rfl

section Fintype

variable [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

/-- The cardinality of the type of permutations preserving a function -/
theorem stabilizer_card:
    Nat.card {f : Perm α // p ∘ f = p} =
      Finset.univ.prod fun i => (Nat.card {a // p a = i}).factorial := by
  rw [Nat.card_congr (subtypeEquiv mk ?_), Nat.card_congr MulOpposite.opEquiv,
    Nat.card_congr (DomMulAct.stabilizerMulEquiv p).toEquiv, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card.symm]
  · intro g
    rw [DomMulAct.mem_stabilizer_iff, symm_apply_apply]

end Fintype

end DomMulAct
