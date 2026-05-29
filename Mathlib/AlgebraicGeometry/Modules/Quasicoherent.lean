/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasicoherent Sheaves

A module `M : X.Modules` is quasicoherent if it locally admits a presentation.

-/

public section

open CategoryTheory

instance {X Y : TopCat} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f).PreservesOneHypercovers
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
  intro U E
  constructor
  · simpa [PreOneHypercover.map, PreZeroHypercover.sieve₀_map] using
      (coverPreserving_opens_map f).cover_preserve E.mem₀
  · intro i₁ i₂ W p₁ p₂ _ x hx
    obtain ⟨V, _, hq, hxV⟩ := E.mem₁ i₁ i₂ (W := E.X i₁ ⊓ E.X i₂)
      (homOfLE inf_le_left) (homOfLE inf_le_right) (Subsingleton.elim _ _) (f x)
      ⟨p₁.le hx, p₂.le hx⟩
    obtain ⟨j, h, -, -⟩ := hq
    exact ⟨(TopologicalSpace.Opens.map f).obj V ⊓ W, homOfLE inf_le_right,
      ⟨j, homOfLE fun y hy ↦ h.le hy.1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
      ⟨hxV, hx⟩⟩

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a quasicoherent sheaf is quasicoherent -/
instance {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := SheafOfModules.IsQuasicoherent.pullback _

/-- The pullback of a locally free sheaf is locally free -/
instance {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) [M.IsLocallyFree] :
    ((pullback f).obj M).IsLocallyFree := SheafOfModules.IsLocallyFree.pullback _

end AlgebraicGeometry.Scheme.Modules
