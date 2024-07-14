/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nick Kuhn, Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
/-!

# Sheaves on CompHaus are equivalent to sheaves on Stonean

The forgetful functor from extremally disconnected spaces `Stonean` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `Stonean` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Since Stonean spaces are the projective objects in `CompHaus`, which has enough projectives,
and the notions of effective epimorphism, epimorphism and surjective continuous map are equivalent
in `CompHaus` and `Stonean`, we can use the general setup in
`Mathlib.CategoryTheory.Sites.Coherent.SheafComparison` to deduce the equivalence of categories.
We give the corresponding statements for `Profinite` as well.

## Main results

* `Condensed.StoneanCompHaus.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
* `Condensed.StoneanProfinite.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `Profinite`.
* `Condensed.ProfiniteCompHaus.equivalence`: the equivalence from coherent sheaves on `Profinite` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
-/

universe u

open CategoryTheory Limits

namespace Condensed

namespace StoneanCompHaus

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' Stonean.toCompHaus A

end StoneanCompHaus

namespace StoneanProfinite

instance : Stonean.toProfinite.PreservesEffectiveEpis where
  preserves f h :=
    ((Profinite.effectiveEpi_tfae _).out 0 2).mpr (((Stonean.effectiveEpi_tfae _).out 0 2).mp h)

instance : Stonean.toProfinite.ReflectsEffectiveEpis where
  reflects f h :=
    ((Stonean.effectiveEpi_tfae f).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

/--
An effective presentation of an `X : Profinite` with respect to the inclusion functor from `Stonean`
-/
noncomputable def stoneanToProfiniteEffectivePresentation (X : Profinite) :
    Stonean.toProfinite.EffectivePresentation X where
  p := X.presentation
  f := Profinite.presentation.π X
  effectiveEpi := ((Profinite.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

instance : Stonean.toProfinite.EffectivelyEnough where
  presentation X := ⟨stoneanToProfiniteEffectivePresentation X⟩

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `Profinite`. -/
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toProfinite.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Sheaf (coherentTopology Profinite) A :=
  coherentTopology.equivalence' Stonean.toProfinite A

end StoneanProfinite

namespace ProfiniteCompHaus

/-- The equivalence from coherent sheaves on `Profinite` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' profiniteToCompHaus A

end ProfiniteCompHaus

variable {A : Type*} [Category A] (X : Condensed.{u} A)

lemma isSheafProfinite
    [∀ Y, HasLimitsOfShape (StructuredArrow Y profiniteToCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Profinite)
    (profiniteToCompHaus.op ⋙ X.val) :=
  ((ProfiniteCompHaus.equivalence A).inverse.obj X).cond

lemma isSheafStonean
    [∀ Y, HasLimitsOfShape (StructuredArrow Y Stonean.toCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Stonean)
    (Stonean.toCompHaus.op ⋙ X.val) :=
  ((StoneanCompHaus.equivalence A).inverse.obj X).cond

end Condensed
