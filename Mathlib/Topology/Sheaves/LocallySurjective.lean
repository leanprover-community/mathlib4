/-
Copyright (c) 2022 Sam van Gool and Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Jake Levinson
-/
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Sites.Surjective

#align_import topology.sheaves.locally_surjective from "leanprover-community/mathlib"@"fb7698eb37544cbb66292b68b40e54d001f8d1a9"

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

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {X : TopCat.{v}}

variable {ℱ 𝒢 : X.Presheaf C}

/-- A map of presheaves `T : ℱ ⟶ 𝒢` is **locally surjective** if for any open set `U`,
section `t` over `U`, and `x ∈ U`, there exists an open set `x ∈ V ⊆ U` and a section `s` over `V`
such that `$T_*(s_V) = t|_V$`.

See `TopCat.Presheaf.isLocallySurjective_iff` below.
-/
def IsLocallySurjective (T : ℱ ⟶ 𝒢) :=
  CategoryTheory.IsLocallySurjective (Opens.grothendieckTopology X) T
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_locally_surjective TopCat.Presheaf.IsLocallySurjective

theorem isLocallySurjective_iff (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔
      ∀ (U t), ∀ x ∈ U, ∃ (V : _) (ι : V ⟶ U), (∃ s, T.app _ s = t |_ₕ ι) ∧ x ∈ V :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_locally_surjective_iff TopCat.Presheaf.isLocallySurjective_iff

section SurjectiveOnStalks

variable [Limits.HasColimits C] [Limits.PreservesFilteredColimits (forget C)]

/-- An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective. -/
theorem locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔ ∀ x : X, Function.Surjective ((stalkFunctor C x).map T) := by
  constructor <;> intro hT
  -- ⊢ IsLocallySurjective T → ∀ (x : ↑X), Function.Surjective ↑((stalkFunctor C x) …
                  -- ⊢ ∀ (x : ↑X), Function.Surjective ↑((stalkFunctor C x).map T)
                  -- ⊢ IsLocallySurjective T
  · /- human proof:
        Let g ∈ Γₛₜ 𝒢 x be a germ. Represent it on an open set U ⊆ X
        as ⟨t, U⟩. By local surjectivity, pass to a smaller open set V
        on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
        Then the germ of s maps to g -/
    -- Let g ∈ Γₛₜ 𝒢 x be a germ.
    intro x g
    -- ⊢ ∃ a, ↑((stalkFunctor C x).map T) a = g
    -- Represent it on an open set U ⊆ X as ⟨t, U⟩.
    obtain ⟨U, hxU, t, rfl⟩ := 𝒢.germ_exist x g
    -- ⊢ ∃ a, ↑((stalkFunctor C x).map T) a = ↑(germ 𝒢 { val := x, property := hxU }) t
    -- By local surjectivity, pass to a smaller open set V
    -- on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    rcases hT U t x hxU with ⟨V, ι, ⟨s, h_eq⟩, hxV⟩
    -- ⊢ ∃ a, ↑((stalkFunctor C x).map T) a = ↑(germ 𝒢 { val := x, property := hxU }) t
    -- Then the germ of s maps to g.
    use ℱ.germ ⟨x, hxV⟩ s
    -- ⊢ ↑((stalkFunctor C x).map T) (↑(germ ℱ { val := x, property := hxV }) s) = ↑( …
    -- Porting note: `convert` went too deep and swapped LHS and RHS of the remaining goal relative
    -- to lean 3.
    convert stalkFunctor_map_germ_apply V ⟨x, hxV⟩ T s using 1
    -- ⊢ ↑(germ 𝒢 { val := x, property := hxU }) t = ↑(Limits.colimit.ι ((OpenNhds.in …
    simpa [h_eq] using (germ_res_apply 𝒢 ι ⟨x, hxV⟩ t).symm
    -- 🎉 no goals
  · /- human proof:
        Let U be an open set, t ∈ Γ ℱ U a section, x ∈ U a point.
        By surjectivity on stalks, the germ of t is the image of
        some germ f ∈ Γₛₜ ℱ x. Represent f on some open set V ⊆ X as ⟨s, V⟩.
        Then there is some possibly smaller open set x ∈ W ⊆ V ∩ U on which
        we have T(s) |_ W = t |_ W. -/
    intro U t x hxU
    -- ⊢ ∃ U_1 f, (imageSieve T t).arrows f ∧ x ∈ U_1
    set t_x := 𝒢.germ ⟨x, hxU⟩ t with ht_x
    -- ⊢ ∃ U_1 f, (imageSieve T t).arrows f ∧ x ∈ U_1
    obtain ⟨s_x, hs_x : ((stalkFunctor C x).map T) s_x = t_x⟩ := hT x t_x
    -- ⊢ ∃ U_1 f, (imageSieve T t).arrows f ∧ x ∈ U_1
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.germ_exist x s_x
    -- ⊢ ∃ U_1 f, (imageSieve T t).arrows f ∧ x ∈ U_1
    -- rfl : ℱ.germ x s = s_x
    have key_W := 𝒢.germ_eq x hxV hxU (T.app _ s) t <| by
      convert hs_x using 1
      symm
      convert stalkFunctor_map_germ_apply _ _ _ s
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W
    -- ⊢ ∃ U_1 f, (imageSieve T t).arrows f ∧ x ∈ U_1
    refine' ⟨W, hWU, ⟨ℱ.map hWV.op s, _⟩, hxW⟩
    -- ⊢ ↑(NatTrans.app T (op W)) (↑(ℱ.map hWV.op) s) = ↑(𝒢.map hWU.op) t
    convert h_eq using 1
    -- ⊢ ↑(NatTrans.app T (op W)) (↑(ℱ.map hWV.op) s) = ↑(𝒢.map hWV.op) (↑(NatTrans.a …
    simp only [← comp_apply, T.naturality]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.locally_surjective_iff_surjective_on_stalks TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks

end SurjectiveOnStalks

end LocallySurjective

end TopCat.Presheaf
