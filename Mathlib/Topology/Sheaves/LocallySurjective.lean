/-
Copyright (c) 2022 Sam van Gool and Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Jake Levinson

! This file was ported from Lean 3 source module topology.sheaves.locally_surjective
! leanprover-community/mathlib commit fb7698eb37544cbb66292b68b40e54d001f8d1a9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.Topology.Sheaves.Stalks
import Mathbin.CategoryTheory.Sites.Surjective

/-!

# Locally surjective maps of presheaves.

Let `X` be a topological space, `ℱ` and `𝒢` presheaves on `X`, `T : ℱ ⟶ 𝒢` a map.

In this file we formulate two notions for what it means for
`T` to be locally surjective:

  1. For each open set `U`, each section `t : 𝒢(U)` is in the image of `T`
     after passing to some open cover of `U`.

  2. For each `x : X`, the map of *stalks* `Tₓ : ℱₓ ⟶ 𝒢ₓ` is surjective.

We prove that these are equivalent.

-/


universe v u

noncomputable section

open CategoryTheory

open TopologicalSpace

open Opposite

namespace TopCat.Presheaf

section LocallySurjective

attribute [local instance] concrete_category.has_coe_to_fun

attribute [local instance] concrete_category.has_coe_to_sort

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {X : TopCat.{v}}

variable {ℱ 𝒢 : X.Presheaf C}

/-- A map of presheaves `T : ℱ ⟶ 𝒢` is **locally surjective** if for any open set `U`,
section `t` over `U`, and `x ∈ U`, there exists an open set `x ∈ V ⊆ U` and a section `s` over `V`
such that `$T_*(s_V) = t|_V$`.

See `is_locally_surjective_iff` below.
-/
def IsLocallySurjective (T : ℱ ⟶ 𝒢) :=
  CategoryTheory.IsLocallySurjective (Opens.grothendieckTopology X) T
#align Top.presheaf.is_locally_surjective TopCat.Presheaf.IsLocallySurjective

theorem isLocallySurjective_iff (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔
      ∀ (U t), ∀ x ∈ U, ∃ (V : _) (ι : V ⟶ U), (∃ s, T.app _ s = t |_ₕ ι) ∧ x ∈ V :=
  Iff.rfl
#align Top.presheaf.is_locally_surjective_iff TopCat.Presheaf.isLocallySurjective_iff

section SurjectiveOnStalks

variable [Limits.HasColimits C] [Limits.PreservesFilteredColimits (forget C)]

/-- An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective. -/
theorem locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔ ∀ x : X, Function.Surjective ((stalkFunctor C x).map T) :=
  by
  constructor <;> intro hT
  · /- human proof:
        Let g ∈ Γₛₜ 𝒢 x be a germ. Represent it on an open set U ⊆ X
        as ⟨t, U⟩. By local surjectivity, pass to a smaller open set V
        on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
        Then the germ of s maps to g -/
    -- Let g ∈ Γₛₜ 𝒢 x be a germ.
    intro x g
    -- Represent it on an open set U ⊆ X as ⟨t, U⟩.
    obtain ⟨U, hxU, t, rfl⟩ := 𝒢.germ_exist x g
    -- By local surjectivity, pass to a smaller open set V
    -- on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    rcases hT U t x hxU with ⟨V, ι, ⟨s, h_eq⟩, hxV⟩
    -- Then the germ of s maps to g.
    use ℱ.germ ⟨x, hxV⟩ s
    convert stalk_functor_map_germ_apply V ⟨x, hxV⟩ T s
    simpa [h_eq] using germ_res_apply 𝒢 ι ⟨x, hxV⟩ t
  · /- human proof:
        Let U be an open set, t ∈ Γ ℱ U a section, x ∈ U a point.
        By surjectivity on stalks, the germ of t is the image of
        some germ f ∈ Γₛₜ ℱ x. Represent f on some open set V ⊆ X as ⟨s, V⟩.
        Then there is some possibly smaller open set x ∈ W ⊆ V ∩ U on which
        we have T(s) |_ W = t |_ W. -/
    intro U t x hxU
    set t_x := 𝒢.germ ⟨x, hxU⟩ t with ht_x
    obtain ⟨s_x, hs_x : ((stalk_functor C x).map T) s_x = t_x⟩ := hT x t_x
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.germ_exist x s_x
    -- rfl : ℱ.germ x s = s_x
    have key_W :=
      𝒢.germ_eq x hxV hxU (T.app _ s) t
        (by
          convert hs_x
          symm
          convert stalk_functor_map_germ_apply _ _ _ s)
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W
    refine' ⟨W, hWU, ⟨ℱ.map hWV.op s, _⟩, hxW⟩
    convert h_eq
    simp only [← comp_apply, T.naturality]
#align Top.presheaf.locally_surjective_iff_surjective_on_stalks TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks

end SurjectiveOnStalks

end LocallySurjective

end TopCat.Presheaf

