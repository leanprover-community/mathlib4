/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Toric.GroupScheme.SchemeOver
import Toric.Mathlib.Algebra.Category.CommAlg.Basic
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# The correspondence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful and has affine group schemes as essential image.

We want to show that Hopf algebras correspond to affine group schemes. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, one solution would be to build the left, top and right edges of the following
diagram so that the bottom edge can be obtained by composing the three.

```
  Cogrp Mod_R ≌ Grp AffSch_{Spec R} ≌ Aff Grp Sch_{Spec R}
      ↑ ↓                                      ↑ ↓
R-Hopf algebras         ≃       Affine group schemes over Spec R
```

If we do not care about going back from affine group schemes over `Spec R` to `R`-Hopf algebras
(eg because all our affine group schemes are given as the `Spec` of some algebra), then we can
follow the following simpler diagram:

```
  Cogrp Mod_R   ⥤        Grp Sch_{Spec R}
      ↑ ↓                        ↓
R-Hopf algebras → Affine group schemes over Spec R
```
where the top `≌` comes from the essentially surjective functor `Cogrp Mod_R ⥤ Grp Sch_{Spec R}`,
so that in particular we do not easily know that its inverse is given by `Γ`.
-/

open AlgebraicGeometry Scheme CategoryTheory Opposite Limits Mon_Class Grp_Class

universe u
variable {R : CommRingCat.{u}}

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

Ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup object under `R`, and vice versa,
are already provided in `Toric.Hopf.HopfAlg`.

### Top edge: `Spec` as a functor on Hopf algebras

In this section we construct `Spec` as a functor from `R`-Hopf algebras to affine group schemes over
`Spec R`.
-/

section topEdge

variable (R) in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R`. -/
noncomputable abbrev algSpec : (CommAlg R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

-- FIXME: Neither `inferInstance` nor `by unfold algSpec; infer_instance` work in the following 3.
-- TODO: Do a MWE once `CommAlg` is in mathlib
instance algSpec.instPreservesLimits : PreservesLimits (algSpec R) :=
  inferInstanceAs <| PreservesLimits <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is full on `R`-algebras. -/
instance algSpec.instFull : (algSpec R).Full :=
  inferInstanceAs <| Functor.Full <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is faithful on `R`-algebras. -/
instance algSpec.instFaithful : (algSpec R).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is fully faithful on `R`-algebras, with inverse `Gamma`. -/
noncomputable def algSpec.fullyFaithful : (algSpec R).FullyFaithful :=
  ((commAlgEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp <|
    Spec.fullyFaithful.over _

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
noncomputable abbrev hopfSpec : Grp_ (CommAlg R)ᵒᵖ ⥤ Grp_ (Over <| Spec R) := (algSpec R).mapGrp

/-- `Spec` is full on `R`-Hopf algebras. -/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/-- `Spec` is fully faithful on `R`-Hopf algebras, with inverse `Gamma`. -/
noncomputable def hopfSpec.fullyFaithful : (hopfSpec R).FullyFaithful :=
  algSpec.fullyFaithful.mapGrp

end topEdge

/-!
### Right edge: The essential image of `Spec` on Hopf algebras

In this section we show that the essential image of `R`-Hopf algebras under `Spec` is precisely
affine group schemes over `Spec R`.
-/

section rightEdge

/-- The essential image of `R`-algebras under `Spec` is precisely affine schemes over `Spec R`. -/
@[simp]
lemma essImage_algSpec {G : Over <| Spec R} : (algSpec R).essImage G ↔ IsAffine G.left := by
  simp [algSpec]
  rw [Functor.essImage_overPost] -- not sure why `simp` doesn't use this already
  simp

/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
lemma essImage_hopfSpec {G : Grp_ (Over <| Spec R)} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left := by
  rw [Functor.essImage_mapGrp, essImage_algSpec]

end rightEdge
