/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather
-/
import Std.Tactic.Lint.Frontend
import Std.Tactic.Lint.Misc

/-!
# Bundled types

`bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `category` instances for these in `category_theory/unbundled_hom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `category_theory/bundled_hom.lean` (for categories with bundled homs, e.g. monoids).
-/

universe u v

namespace CategoryTheory

variable {c d : Type u → Type v} {α : Type u}

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  /-- The underlying type of the bundled type -/
  α : Type u
  /-- The corresponding instance of the bundled type class -/
  str : c α := by infer_instance

namespace Bundled

-- This is needed so that we can ask for an instance of `c α` below even though Lean doens't know
-- that `c α` is a typeclass.
set_option checkBinderAnnotations false

-- Usually explicit instances will provide their own version of this, e.g. `Mon.of` and `Top.of`.
/-- A generic function for lifting a type equipped with an instance to a bundled object. -/
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩

set_option checkBinderAnnotations true

instance : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl

/-
`bundled.map` is reducible so that, if we define a category

  def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring)

instance search is able to "see" that a morphism R ⟶ S in Ring is really
a (semi)ring homomorphism from R.α to S.α, and not merely from
`(bundled.map @ring.to_semiring R).α` to `(bundled.map @ring.to_semiring S).α`.

TODO: Once at least one use of this has been ported, check if this still needs to be reducible in
Lean 4.
-/
/-- Map over the bundled structure -/
def map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩

end Bundled

end CategoryTheory
