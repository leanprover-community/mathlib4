/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!

# The de Rham Period Ring \(\mathbb{B}_dR^+\) and \(\mathbb{B}_dR\)

In this file, we define the de Rham period ring \(\mathbb{B}_dR^+\) and
the de Rham ring \(\mathbb{B}_dR\). We define a generalized version of these period rings following Scholze. When `O` is the ring of integers of `ℂ_p`, they coincide with the classical de Rham period rings.

## Main definitions

* `BDeRhamPlus` : The period ring \(\mathbb{B}_dR^+\).

* `BDeRham` : The period ring \(\mathbb{B}_dR\).

## TODO

1. Extend the θ map to \(\mathbb{B}_dR^+\)
2. Show that \(\mathbb{B}_dR^+\) is a discrete valuation ring.

## Reference

* [Scholze, *p-adic Hodge theory for rigid-analytic varieties*][scholze2013adic]

## Tags
de Rham Representation, Period Rings
-/

universe u

open Ideal WittVector

variable {O : Type u} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

local notation A "^♭" => PreTilt A p
local notation "𝕎" => WittVector p

noncomputable section

/--
The Fontaine's θ map inverting `p`. Note that if `p = 0` in `O`, then this is the zero map.
-/
def fontaineThetaInvertP :
    Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭)) →+* Localization.Away (p : O) :=
  Localization.awayLift ((algebraMap O _).comp fontaineTheta) (p : 𝕎 (O^♭))
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O))

variable (O p)

/--
The de Rham period ring \(\mathbb{B}_dR^+\) for general perfectoid ring.
It is the completion of `𝕎 (O^♭)` inverting `p` with respect to the kernel of
the Fontaine's θ map. When \(O = \mathcal{O}_{\mathbb{C}_p}\), it coincides
with the classical de Rham period ring. Note that if `p = 0` in `O`,
then this
definition is the zero ring.
-/
def BDeRhamPlus : Type u :=
  AdicCompletion (R := (Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭))))
      (RingHom.ker fontaineThetaInvertP) (Localization.Away (M := 𝕎 (O^♭)) (p : 𝕎 (O^♭)))

instance : CommRing (BDeRhamPlus O p) := AdicCompletion.instCommRing _

/--
The de Rham period ring \(\mathbb{B}_dR\) for general perfectoid ring.
It is the fraction field of \(\mathbb{B}_dR^+\).
When \(O = \mathcal{O}_{\mathbb{C}_p}\), it coincides
with the classical de Rham period ring. Note that if `p = 0` in `O`,
then this
definition is the zero ring.
-/
def BDeRham : Type u := FractionRing (BDeRhamPlus O p)

instance : CommRing (BDeRham O p) :=
  inferInstanceAs <| CommRing (FractionRing (BDeRhamPlus O p))

local notation "𝔹_dR^+(" O ")" => BDeRhamPlus O p

local notation "𝔹_dR(" O ")" => BDeRham O p

end
