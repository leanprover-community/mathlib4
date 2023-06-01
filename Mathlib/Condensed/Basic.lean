/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

/-!

# Condensed Objects

This file defines the category of condensed objects in a category `C`.

## Implementation Details

We use the coherent Grothendieck topology on `CompHaus`, and define condensed objects in `C` to
be `C`-valued sheaves, with respect to this Grothendieck topology.

In future work, we will define similar Grothendieck topologies on the category of profinite sets
and extremally disconnected sets, and show that the three categories are equivalent (under
suitable assumptions on `C`).

Note: Our definition more closely resembles "Pyknotic objects" in the sense of Barwick-Haine,
as we do not impose cardinality bounds, and manage universes carefully instead.

-/

open CategoryTheory Limits

open CategoryTheory

universe u

def Condensed (C : Type _) [Category C] :=
  Sheaf (coherentTopology CompHaus.{u}) C

instance {C : Type _} [Category C] : Category (Condensed.{u} C) :=
  show Category (Sheaf _ _) from inferInstance
