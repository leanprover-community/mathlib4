/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Basic
/-!
# `ℂ` satisfies the Tietze extension theorem

We provide this result here in order to avoid pulling unnecessary imports into either of
`Topology.TietzeExtension` or `Analysis.Complex.Basic`.
-/

instance Complex.instTietzeExtension : TietzeExtension ℂ :=
  .of_homeo equivRealProdClm.toHomeomorph
