/-
Copyright (c) 2023 Junyan Xu, Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Antoine Chambert-Loir
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite


/-!  Subgroup of `Equiv.Perm α` preserving a function

Let `α` and `ι` by types and let `f : α → ι`

* `DomMulAct.mem_stabilizer_iff` proves that the stabilizer of `f : α → ι`
  in `(Equiv.Perm α)ᵈᵐᵃ` is the set of `g : (Equiv.Perm α)ᵈᵐᵃ` such that `f ∘ (mk.symm g) = f`.

  The natural equivalence from `stabilizer (Perm α)ᵈᵐᵃ f` to `{ g : Perm α // p ∘ g = f }`
  can be obtained as `subtypeEquiv mk.symm (fun _ => mem_stabilizer_iff)`

* `DomMulAct.stabilizerMulEquiv` is the `MulEquiv` from
  the MulOpposite of this stabilizer to the product,
  for `i : ι`, of `Equiv.Perm {a // f a = i}`.

* Under `Fintype α` and `Fintype ι`, `DomMulAct.stabilizer_card p` computes
  the cardinality of the type of permutations preserving `p` :
  `Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})!`.

-/

variable {α ι : Type*} {f : α → ι}

open Equiv MulAction

namespace DomMulAct

lemma mem_stabilizer_iff {g : (Perm α)ᵈᵐᵃ} :
    g ∈ stabilizer (Perm α)ᵈᵐᵃ f ↔ f ∘ (mk.symm g :) = f := by
  simp only [MulAction.mem_stabilizer_iff]; rfl

/-- The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) f`
  to the product of the `Equiv.Perm {a // f a = i} -/
def stabilizerEquiv_invFun (g : ∀ i, Perm {a // f a = i}) (a : α) : α := g (f a) ⟨a, rfl⟩

lemma stabilizerEquiv_invFun_eq (g : ∀ i, Perm {a // f a = i}) {a : α} {i : ι} (h : f a = i) :
    stabilizerEquiv_invFun g a = g i ⟨a, h⟩ := by subst h; rfl

lemma comp_stabilizerEquiv_invFun (g : ∀ i, Perm {a // f a = i}) (a : α) :
    f (stabilizerEquiv_invFun g a) = f a :=
  (g (f a) ⟨a, rfl⟩).prop

/-- The `invFun` component of `MulEquiv` from `MulAction.stabilizer (Perm α) p`
  to the product of the `Equiv.Perm {a | f a = i} (as an `Equiv.Perm α`) -/
def stabilizerEquiv_invFun_aux (g : ∀ i, Perm {a // f a = i}) : Perm α where
  toFun := stabilizerEquiv_invFun g
  invFun := stabilizerEquiv_invFun (fun i ↦ (g i).symm)
  left_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun g a)]
    exact congr_arg Subtype.val ((g <| f a).left_inv _)
  right_inv a := by
    rw [stabilizerEquiv_invFun_eq _ (comp_stabilizerEquiv_invFun _ a)]
    exact congr_arg Subtype.val ((g <| f a).right_inv _)

variable (f)

/-- The `MulEquiv` from the `MulOpposite` of `MulAction.stabilizer (Perm α)ᵈᵐᵃ f`
  to the product of the `Equiv.Perm {a // f a = i}` -/
def stabilizerMulEquiv : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ ≃* (∀ i, Perm {a // f a = i}) where
  toFun g i := Perm.subtypePerm (mk.symm g.unop) fun a ↦ by
    rw [← Function.comp_apply (f := f), mem_stabilizer_iff.mp g.unop.prop]
  invFun g := ⟨mk (stabilizerEquiv_invFun_aux g), by
    ext a
    rw [smul_apply, symm_apply_apply, Perm.smul_def]
    apply comp_stabilizerEquiv_invFun⟩
  left_inv g := rfl
  right_inv g := by ext i a; apply stabilizerEquiv_invFun_eq
  map_mul' g h := rfl

variable {f}

lemma stabilizerMulEquiv_apply (g : (stabilizer (Perm α)ᵈᵐᵃ f)ᵐᵒᵖ) {a : α} {i : ι} (h : f a = i) :
    ((stabilizerMulEquiv f)) g i ⟨a, h⟩ = (mk.symm g.unop : Equiv.Perm α) a := rfl

section Fintype

variable [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

open Nat

variable (f)

/-- The cardinality of the type of permutations preserving a function -/
theorem stabilizer_card:
    Fintype.card {g : Perm α // f ∘ g = f} = ∏ i, (Fintype.card {a // f a = i})! := by
  -- rewriting via Nat.card because Fintype instance is not found
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (subtypeEquiv mk fun _ ↦ ?_),
    Nat.card_congr MulOpposite.opEquiv,
    Nat.card_congr (DomMulAct.stabilizerMulEquiv f).toEquiv, Nat.card_pi]
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  · rfl

end Fintype

end DomMulAct
