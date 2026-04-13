/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.Etale.Descent

/-!

# Etale satisfies fpqc descent

In this file we provide instances that show that the following properties satisfy fpqc descent:

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
