/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

## TODO:

- define the small étale site

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

/-- Big étale site: the étale pretopology on the category of schemes. -/
def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @IsEtale

/-- Big étale site: the étale topology on the category of schemes. -/
abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  etalePretopology.toGrothendieck

lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_le_grothendieckTopology
  intro X Y f hf
  infer_instance

end AlgebraicGeometry.Scheme
