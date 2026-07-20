/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Rudimentary
public import Mathlib.SetTheory.ZFC.Constructible.Ordinals

/-!
# Internal ZF codes for rudimentary terms

This file encodes the external inductive syntax `RudimentaryTerm alpha` by
genuine `ZFSet`s.  A variable encoding `rho` supplies the internal code for
each variable:

* `var a` is coded by the triple `⟨0, rho a, ∅⟩`;
* `app i left right` is coded by
  `⟨1, i, ⟨code left, code right⟩⟩`.

All pairs and triples are Kuratowski pairs.  The encoding is injective when
`rho` is injective, and its values are constructible when the variable codes
are constructible.
-/

@[expose] public section

universe u v

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/-- The node tag used for variables. -/
def varTag : ZFSet.{v} :=
  (0 : Ordinal.{v}).toZFSet

/-- The node tag used for applications. -/
def appTag : ZFSet.{v} :=
  (1 : Ordinal.{v}).toZFSet

/-- The internal finite-ordinal code of one of the nine rudimentary operations. -/
def operationCode (i : Fin 9) : ZFSet.{v} :=
  (i.1 : Ordinal.{v}).toZFSet

/--
Encode a rudimentary term as a genuine ZF set, relative to codes for its
variables.
-/
def zfCode {alpha : Type u} (rho : alpha -> ZFSet.{v}) :
    RudimentaryTerm alpha -> ZFSet.{v}
  | .var a => triple varTag (rho a) ∅
  | .app i left right =>
      triple appTag (operationCode i)
        (ZFSet.pair (zfCode rho left) (zfCode rho right))

@[simp]
theorem zfCode_var {alpha : Type u} (rho : alpha -> ZFSet.{v}) (a : alpha) :
    zfCode rho (.var a) = triple varTag (rho a) ∅ :=
  rfl

@[simp]
theorem zfCode_app {alpha : Type u} (rho : alpha -> ZFSet.{v})
    (i : Fin 9) (left right : RudimentaryTerm alpha) :
    zfCode rho (.app i left right) =
      triple appTag (operationCode i)
        (ZFSet.pair (zfCode rho left) (zfCode rho right)) :=
  rfl

/-- The two constructor tags have distinct internal codes. -/
theorem varTag_ne_appTag :
    (varTag : ZFSet.{v}) ≠ appTag := by
  intro h
  exact zero_ne_one (Ordinal.toZFSet_injective h)

/-- The finite-ordinal operation code remembers the operation index. -/
theorem operationCode_injective :
    Function.Injective (operationCode : Fin 9 -> ZFSet.{v}) := by
  intro i j h
  apply Fin.ext
  exact Nat.cast_injective (Ordinal.toZFSet_injective h)

/-- An injective variable coding induces an injective internal term coding. -/
theorem zfCode_injective {alpha : Type u} {rho : alpha -> ZFSet.{v}}
    (hrho : Function.Injective rho) :
    Function.Injective (zfCode rho) := by
  intro first second hcode
  induction first generalizing second with
  | var a =>
      cases second with
      | var b =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with ⟨hvariable, _hempty⟩
          exact congrArg RudimentaryTerm.var (hrho hvariable)
      | app j left right =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag)
  | app i left right ihLeft ihRight =>
      cases second with
      | var b =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag.symm)
      | app j left' right' =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with ⟨hoperation, hchildren⟩
          rcases ZFSet.pair_inj.mp hchildren with ⟨hleft, hright⟩
          have hij : i = j := operationCode_injective hoperation
          have hl : left = left' := ihLeft hleft
          have hr : right = right' := ihRight hright
          cases hij
          cases hl
          cases hr
          rfl

/-- A Kuratowski triple of constructible sets is constructible. -/
theorem triple_mem_L {x y z : ZFSet.{v}}
    (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    triple x y z ∈ L := by
  exact orderedPair_mem_L hx (orderedPair_mem_L hy hz)

/-- The variable constructor tag belongs to `L`. -/
theorem varTag_mem_L : (varTag : ZFSet.{v}) ∈ L :=
  ordinal_toZFSet_mem_L 0

/-- The application constructor tag belongs to `L`. -/
theorem appTag_mem_L : (appTag : ZFSet.{v}) ∈ L :=
  ordinal_toZFSet_mem_L 1

/-- Every finite operation code belongs to `L`. -/
theorem operationCode_mem_L (i : Fin 9) :
    (operationCode i : ZFSet.{v}) ∈ L :=
  ordinal_toZFSet_mem_L (i.1 : Ordinal.{v})

/--
Every internal term code is constructible when every supplied variable code
is constructible.
-/
theorem zfCode_mem_L {alpha : Type u} {rho : alpha -> ZFSet.{v}}
    (hrho : forall a, rho a ∈ L) (term : RudimentaryTerm alpha) :
    zfCode rho term ∈ L := by
  induction term with
  | var a =>
      exact triple_mem_L varTag_mem_L (hrho a) empty_mem_L
  | app i left right ihLeft ihRight =>
      exact triple_mem_L appTag_mem_L (operationCode_mem_L i)
        (orderedPair_mem_L ihLeft ihRight)

end

end RudimentaryTerm

end Constructible.Godel
