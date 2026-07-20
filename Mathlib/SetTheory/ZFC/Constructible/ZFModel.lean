/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.ModelTheory.SetTheory.ZF
public import Mathlib.SetTheory.ZFC.Constructible.Infinity
public import Mathlib.SetTheory.ZFC.Constructible.PowerSet
public import Mathlib.SetTheory.ZFC.Constructible.Replacement

/-!
# The constructible universe is a model of ZF

This file packages the closure, reflection, bounding, and ordinal results for
the constructible universe into Mathlib's canonical first-order theory of ZF.
The Separation and Replacement schemes range over every formula in
`FirstOrder.Language.setTheory`.
-/

@[expose] public section

universe u

namespace Constructible.Model

/-- The membership structure induced on `L` is a model of Mathlib's canonical ZF theory. -/
theorem lCarrier_models_ZF :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZF := by
  rw [FirstOrder.Language.Theory.model_ZF_iff]
  intro ax
  cases ax with
  | extensionality =>
      change forall x y : LCarrier.{u},
        (forall z : LCarrier.{u}, z.1 ∈ x.1 <-> z.1 ∈ y.1) -> x = y
      exact fun _ _ => lCarrier_extensionality
  | emptySet =>
      change exists e : LCarrier.{u},
        forall x : LCarrier.{u}, x.1 ∉ e.1
      exact ⟨emptyLCarrier, not_mem_emptyLCarrier⟩
  | pairing =>
      change forall x y : LCarrier.{u}, exists p : LCarrier.{u},
        forall z : LCarrier.{u}, z.1 ∈ p.1 <-> z = x ∨ z = y
      exact fun x y => ⟨pairLCarrier x y, mem_pairLCarrier_iff x y⟩
  | union =>
      change forall x : LCarrier.{u}, exists union : LCarrier.{u},
        forall z : LCarrier.{u}, z.1 ∈ union.1 <->
          exists y : LCarrier.{u}, y.1 ∈ x.1 /\ z.1 ∈ y.1
      exact fun x => ⟨sUnionLCarrier x, mem_sUnionLCarrier_iff x⟩
  | powerSet =>
      change forall a : LCarrier.{u}, exists p : LCarrier.{u},
        forall x : LCarrier.{u}, x.1 ∈ p.1 <->
          forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∈ a.1
      intro a
      rcases exists_powerSetLCarrier a with ⟨p, hp⟩
      refine ⟨p, fun x => (hp x).trans ?_⟩
      constructor
      · intro h z hz
        exact h hz
      · intro h z hz
        exact h ⟨z, mem_L_of_mem hz x.2⟩ hz
  | infinity =>
      change exists w : LCarrier.{u},
        (exists e : LCarrier.{u}, e.1 ∈ w.1 /\
          forall z : LCarrier.{u}, z.1 ∉ e.1) /\
        forall x : LCarrier.{u}, x.1 ∈ w.1 ->
          exists s : LCarrier.{u}, s.1 ∈ w.1 /\
            forall z : LCarrier.{u}, z.1 ∈ s.1 <-> z.1 ∈ x.1 ∨ z = x
      exact lCarrier_infinity
  | foundation =>
      change forall x : LCarrier.{u},
        (exists y : LCarrier.{u}, y.1 ∈ x.1) ->
          exists y : LCarrier.{u}, y.1 ∈ x.1 /\
            forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∉ y.1
      exact lCarrier_foundation
  | separation n phi =>
      change forall (params : Fin n -> LCarrier.{u}) (a : LCarrier.{u}),
        exists b : LCarrier.{u}, forall x : LCarrier.{u},
          x.1 ∈ b.1 <-> x.1 ∈ a.1 /\ phi.Realize (Fin.snoc params x)
      exact exists_separationFormula.{u} (n := n) phi
  | replacement n phi =>
      change forall (params : Fin n -> LCarrier.{u}) (a : LCarrier.{u}),
        (forall x : LCarrier.{u}, x.1 ∈ a.1 ->
          ExistsUnique fun y : LCarrier.{u} =>
            phi.Realize (Fin.snoc (Fin.snoc params x) y)) ->
        exists b : LCarrier.{u}, forall y : LCarrier.{u},
          y.1 ∈ b.1 <-> exists x : LCarrier.{u}, x.1 ∈ a.1 /\
            phi.Realize (Fin.snoc (Fin.snoc params x) y)
      exact exists_replacementFormula.{u} (n := n) phi

end Constructible.Model
