/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Sheaves.Init

/-!

# Local properties satisfying fpqc descent

In this file we provide instances that show that the following local properties satisfy fpqc
descent:

- locally of finite type
- locally of finite presentation
- smooth
- formally unramified
- étale

-/

public section

open CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry

instance : DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FiniteType.codescendsAlong_faithfullyFlat

instance : DescendsAlong @LocallyOfFinitePresentation (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FinitePresentation.codescendsAlong_faithfullyFlat

instance : DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Smooth.codescendsAlong_faithfullyFlat

instance : DescendsAlong @FormallyUnramified (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat

instance : DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Etale.codescendsAlong_faithfullyFlat

end AlgebraicGeometry
