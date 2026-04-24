/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Functors to `ComposableArrows C 1`

-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable (C : Type u) [Category.{v} C]

/-- The functor `ComposableArrows C n ⥤ ComposableArrows C 1`
which sends `S` to `mk₁ (S.map' i j)` when `i`, `j` and `n`
are such that `i ≤ j` and `j ≤ n`. -/
@[simps]
def functorArrows (i j n : ℕ) (hij : i ≤ j := by lia) (hj : j ≤ n := by lia) :
    ComposableArrows C n ⥤ ComposableArrows C 1 where
  obj S := mk₁ (S.map' i j)
  map {S S'} φ := homMk₁ (φ.app _) (φ.app _) (φ.naturality _)

#adaptation_note /-- Proof repaired after leanprover/lean4#13363.
The `app` subproof used to be just
```
(by simp [← Functor.map_comp])
```
and the `naturality` field was not necessary, and was proved by the `auto_param`.
The replacement proof is a short-term fix, and we request that the authors/maintainers of
this file review the proof, and either approve it by removing this adaptation note, revise
the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
needs addressing. -/
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `functorArrows C i j n ⟶ functorArrows C i' j' n`
when `i ≤ i'` and `j ≤ j'`. -/
@[simps]
def mapFunctorArrows (i j i' j' n : ℕ)
    (_ : i ≤ j := by lia) (_ : i' ≤ j' := by lia)
    (_ : i ≤ i' := by lia) (_ : j ≤ j' := by lia)
    (_ : j' ≤ n := by lia) :
    functorArrows C i j n ⟶ functorArrows C i' j' n where
  app S := homMk₁ (S.map' i i') (S.map' j j')
    (by change S.map' i j ≫ S.map' j j' = S.map' i i' ≫ S.map' i' j'; simp [← Functor.map_comp])
  naturality {X Y} f := by
    apply hom_ext₁
    · change f.app ⟨i, _⟩ ≫ Y.map' i i' = X.map' i i' ≫ f.app ⟨i', _⟩
      simp [← NatTrans.naturality]
    · change f.app ⟨j, _⟩ ≫ Y.map' j j' = X.map' j j' ≫ f.app ⟨j', _⟩
      simp [← NatTrans.naturality]

end ComposableArrows

end CategoryTheory
