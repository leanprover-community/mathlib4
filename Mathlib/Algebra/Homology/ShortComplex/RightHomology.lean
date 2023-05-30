/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

/-! RightHomology of short complexes

In this file, we define the dual notions to those defined in
`Algebra.Homology.ShortComplex.LeftHomology`. In particular, if `S : ShortComplex C` is
a short complex consisting of two composable maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such
that `f ≫ g = 0`, we define `h : S.RightHomologyData` to be the datum of morphisms
`p : X₂ ⟶ Q` and `ι : H ⟶ Q` such that `Q` identifies to the cokernel of `f` and `H`
to the kernel of the induced map `g' : Q ⟶ X₃`.

-/

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type _} [Category C] [HasZeroMorphisms C]
  (S : ShortComplex C)

/-- A right homology data for a short complex `S` consists of morphisms `p : S.X₂ ⟶ Q` and
`ι : H ⟶ Q` such that `p` identifies `Q` to the kernel of `f : S.X₁ ⟶ S.X₂`,
and that `ι` identifies `H` to the kernel of the induced map `g' : Q ⟶ S.X₃` --/
structure RightHomologyData where
  /-- a choice of cokernel of `S.f : S.X₁ ⟶ S.X₂`-/
  Q : C
  /-- a choice of kernel of the induced morphism `S.g' : S.Q ⟶ X₃`-/
  H : C
  /-- the projection from `S.X₂` -/
  p : S.X₂ ⟶ Q
  /-- the inclusion of the (right) homology in the chosen cokernel of `S.f` -/
  ι : H ⟶ Q
  /-- the cokernel condition for `p` -/
  wp : S.f ≫ p = 0
  /-- `p : S.X₂ ⟶ Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂` -/
  hp : IsColimit (CokernelCofork.ofπ p wp)
  /-- the kernel condition for `ι` -/
  wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0
  /-- `ι : H ⟶ Q` is a kernel of `S.g' : Q ⟶ S.X₃` -/
  hι : IsLimit (KernelFork.ofι ι wι)

initialize_simps_projections RightHomologyData (-hp, -hι)

end ShortComplex

end CategoryTheory
