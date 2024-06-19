/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Relation.Trans

/-!
# Notation, basic datatypes and type classes

This file contains alignments from lean 3 `init.core`.
-/

set_option autoImplicit true

#align id id -- align this first so idDelta doesn't take priority
#align id_delta id

#align opt_param optParam
#align out_param outParam

#align id_rhs id
#align punit PUnit
#align punit.star PUnit.unit
#align unit Unit
#align unit.star Unit.unit

#align thunk Thunk

#align true True
#align false False
#align empty Empty
#align eq Eq

-- Note: we do not currently auto-align constants.
#align quot Quot
#align quot.mk Quot.mk
#align quot.lift Quot.lift
#align quot.ind Quot.ind

#align heq HEq
#align prod Prod
#align prod.fst Prod.fst
#align prod.snd Prod.snd
#align pprod PProd
#align pprod.fst PProd.fst
#align pprod.snd PProd.snd

#align and.left And.left
#align and.right And.right
#align and.elim_left And.left
#align and.elim_right And.right

-- TODO
-- attribute [elab_as_elim, subst] Eq.subst

attribute [trans] Eq.trans
attribute [symm] Eq.symm

#align eq.subst Eq.subst
#align eq.refl Eq.refl
#align eq.symm Eq.symm
#align eq.trans Eq.trans

def Prod.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂

def PProd.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂

#align sum Sum
#align sum.inl Sum.inl
#align sum.inr Sum.inr

#align psum PSum
#align psum.inl PSum.inl
#align psum.inr PSum.inr

#align or.intro_right Or.intro_rightₓ -- reorder implicits

#align sigma Sigma
#align sigma.fst Sigma.fst
#align sigma.snd Sigma.snd

#align psigma PSigma
#align psigma.fst PSigma.fst
#align psigma.snd PSigma.snd

#align bool Bool
#align bool.ff Bool.false
#align bool.tt Bool.true

#align subtype Subtype
#align subtype.val Subtype.val
#align subtype.property Subtype.property

#align decidable Decidable
#align decidable_pred DecidablePred
#align decidable_rel DecidableRel
#align decidable_eq DecidableEq

#align option Option

#align list List
#align list.nil List.nil
#align list.cons List.cons

#align nat Nat

-- attribute [pp_using_anonymous_constructor] Sigma PSigma Subtype PProd And

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.
#align has_add Add
#align has_mul Mul
#align has_neg Neg
#align has_sub Sub
#align has_div Div
#align has_dvd Dvd
#align has_mod Mod
#align has_le LE
#align has_le.le LE.le
#align has_lt LT
#align has_lt.lt LT.lt
#align has_append Append

#align has_andthen AndThen

#align has_union Union
#align has_equiv HasEquivₓ -- universe levels don't match
#align has_inter Inter
#align has_sdiff SDiff

#align has_subset HasSubset
#align has_subset.subset HasSubset.Subset
#align has_ssubset HasSSubset
#align has_ssubset.ssubset HasSSubset.SSubset
#align has_emptyc EmptyCollection
#align has_emptyc.emptyc EmptyCollection.emptyCollection
#align has_insert Insert
#align has_singleton Singleton
#align has_sep Sep
#align has_mem Membership
#align has_pow Pow

#align gt GT.gt
#align ge GE.ge

#align is_lawful_singleton IsLawfulSingleton

attribute [simp] insert_emptyc_eq

#align has_sizeof SizeOf
#align has_sizeof.sizeof SizeOf.sizeOf
#align sizeof SizeOf.sizeOf

#align nat_add_zero Nat.add_zero

-- Combinator calculus
namespace Combinator

def I (a : α) := a
def K (a : α) (_b : β) := a
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

end Combinator

#align function.const_apply Function.const_apply
#align function.comp_apply Function.comp_apply
