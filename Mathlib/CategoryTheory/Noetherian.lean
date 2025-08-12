/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Artinian and noetherian categories

An artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.

A noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.

Note: In the file, `CategoryTheory.Subobject.ArtinianObject`,
it is shown that any nonzero Artinian object has a simple subobject.

## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
-/


namespace CategoryTheory

open CategoryTheory.Limits

@[deprecated (since := "2025-07-11")] alias NoetherianObject := IsNoetherianObject
@[deprecated (since := "2025-07-11")] alias ArtinianObject := IsArtinianObject

variable (C : Type*) [Category C]

/-- A category is noetherian if it is essentially small and all objects are noetherian. -/
class Noetherian : Prop extends EssentiallySmall C where
  isNoetherianObject : ∀ X : C, IsNoetherianObject X

attribute [instance] Noetherian.isNoetherianObject

/-- A category is artinian if it is essentially small and all objects are artinian. -/
class Artinian : Prop extends EssentiallySmall C where
  isArtinianObject : ∀ X : C, IsArtinianObject X

attribute [instance] Artinian.isArtinianObject

open Subobject

end CategoryTheory
