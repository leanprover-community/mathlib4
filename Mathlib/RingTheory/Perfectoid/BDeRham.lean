/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# The de Rham Period Ring $\mathbb{B}_{dR}^+$ and $\mathbb{B}_{dR}$

In this file, we define the de Rham period ring $\mathbb{B}_{dR}^+$ and
the de Rham ring $\mathbb{B}_{dR}$. We define a generalized version of
these period rings following Scholze. When `R` is the ring of integers
of `ℂₚ` (`PadicComplexInt`), they coincide with the classical de Rham period rings.

## Main definitions

* `BDeRhamPlus` : The period ring $\mathbb{B}_{dR}^+$.
* `BDeRham` : The period ring $\mathbb{B}_{dR}$.

## TODO

1. Extend the θ map to $\mathbb{B}_{dR}^+$
2. Show that $\mathbb{B}_{dR}^+$ is a discrete valuation ring.
3. Show that ker θ is principal when the base ring is integral perfectoid.

Currently, the period ring `BDeRhamPlus` takes the ring of integers `R` as the input.
After the perfectoid theory is developed, we can modify it to
take a perfectoid field as the input.

## Reference

* [Fontaine, *Sur Certains Types de Représentations p-Adiques du Groupe de Galois d'un Corps Local;
  Construction d'un Anneau de Barsotti-Tate*][fontaine1982certains]
* [Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps]
* [Scholze, *p-adic Hodge theory for rigid-analytic varieties*][scholze2013adic]

## Tags
Period rings, p-adic Hodge theory
-/

@[expose] public section

universe u

open Ideal WittVector

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

local notation "𝕎 " A:100 => WittVector p A
local notation A "♭" => PreTilt A p

noncomputable section

/--
The Fontaine's θ map inverting `p`. Note that if `p = 0` in `R`, then this is the zero map.
-/
def fontaineThetaInvertP :
    Localization.Away (p : 𝕎 R♭) →+* Localization.Away (p : R) :=
  Localization.awayLift ((algebraMap R _).comp (fontaineTheta R p)) (p : 𝕎 R♭)
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : R))

/--
The de Rham period ring $\mathbb{B}_{dR}^+$ for general perfectoid ring.
It is the completion of `𝕎 R♭` inverting `p` with respect to the kernel of
the Fontaine's θ map. When $R = \mathcal{O}_{\mathbb{C}_p}$, it coincides
with the classical de Rham period ring. Note that if `p = 0` in `R`,
then this
definition is the zero ring.
-/
def BDeRhamPlus : Type u :=
  AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) (Localization.Away (p : 𝕎 R♭))
deriving CommRing

/--
The de Rham period ring $\mathbb{B}_{dR}$ for general perfectoid ring.
It is defined as $\mathbb{B}_{dR}^+$ inverting the generators of the ideal `ker θ`.
Mathematically, this is equivalent to inverting *a* generator of the ideal `ker θ`
after we show that it is principal.
When $R = \mathcal{O}_{\mathbb{C}_p}$, it coincides
with the classical de Rham period ring.
Note that if `p = 0` in `R`, then this definition is the zero ring.
-/
def BDeRham : Type u :=
  Localization (M := BDeRhamPlus R p) <| Submonoid.closure <|
    AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP R p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP R p)) = Ideal.span {a}}

local notation "𝔹_dR^+(" R ")" => BDeRhamPlus R p
local notation "𝔹_dR(" R ")" => BDeRham R p

end
