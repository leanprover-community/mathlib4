/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.HahnSeries

/-!
# Vertex algebras

In this file we introduce vertex algebras using Hahn series.

## Definitions

* NonAssocNonUnitalVertexRing : This is an `AddCommGroup` `V` with linear map `V ⊗ V → V((z))`.
*

## Main results


## References

G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328

-/

universe u v

variable {V : Type u}

class NonAssocNonUnitalVertexRing (V : Type u) extends AddCommGroup V where
  Y : V →+ V →+ HahnSeries ℤ V
