/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Limits
public import Mathlib.CategoryTheory.Inserter.LocallySmall
public import Mathlib.CategoryTheory.Presentable.Comma

/-!
# Inserter categories are accessible

-/

namespace CategoryTheory.Inserter

universe w

/- The setup for accessibility of inserter categories, from Positetski’s paper:
`F G : K ⥤ L` are a parallel pair of κ-accessible functors between κ-accessible categories
where `F` in addition preserves κ-presentable objects. A given infinite cardinal Λ < κ such
that both `K` and `L` have colimits of Λ-chains is given, and we assume that `F` and `G` preserve
these colimits. Here, we realize `Λ` as a well-founded linear order directly
(instead of using `Cardinal.ord.ToType`). -/

-- Recall everything in the section below private.
section

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G]



end

/-- Let `Λ < κ` be a pair of infinite cardinals, such that `κ` is regular. Assume that
- `K` and `L` are `κ`-accessible categories with colimits of `Λ`-chains.
- `F G : C ⥤ D` are `κ`-accessible functors preserving colimits of `Λ`-chains and with `F`
  preserving `κ`-presentable objects.
Then the category `Inserter F G` is κ-accessible.

Note that if `K` and `L` are `κ`-accessible, and `F`, `G` are `κ`-accessible with `F` preserving
`κ`-presentable objects, then as `κ` is sharply less than `κ⁺`, one can show that the pair `κ < κ⁺`
satisfies the conditions above, and hence `Inserter F G` is `κ⁺` accessible in this situation. -/
public theorem isCardinalAccessibleCategory
    {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G] :
    IsCardinalAccessibleCategory (Inserter F G) κ :=
  sorry

end CategoryTheory.Inserter
