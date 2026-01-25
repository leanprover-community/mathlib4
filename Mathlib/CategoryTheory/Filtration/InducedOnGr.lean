/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.Opposed

/-!
## Induced filtrations on graded pieces

For decreasing `ℤ`-filtrations `F` and `G` on `X` in an abelian category, Deligne (1.2.1)
defines an induced filtration on the graded piece `Gr_G^q(X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace Filtration

namespace DecFiltration

variable {X : C}

section

variable [Abelian C]

/-- The `p`-th step of the filtration induced by `F` on `Gr_G^q(X)` (Deligne 1.2.1). -/
noncomputable def inducedOnGrStep
    (F G : Filtration.DecFiltration (C := C) X) (q p : ℤ) : Subobject (G.gr q) :=
  FilteredObject.imageSubobject (C := C) (G.grπ q)
    ((Subobject.pullback (G.inj (Opposite.op q))).obj (F.step p))

/-- The filtration induced by `F` on the graded piece `Gr_G^q(X)` (Deligne 1.2.1). -/
noncomputable def inducedOnGr
    (F G : Filtration.DecFiltration (C := C) X) (q : ℤ) :
    Filtration.DecFiltration (C := C) (G.gr q) :=
by
  classical
  refine Filtration.DecFiltration.ofAntitone (C := C) (X := G.gr q)
    (fun p => inducedOnGrStep (C := C) (X := X) F G q p) ?_
  intro p p' hp
  have hIdx : (Opposite.op p' : ℤᵒᵖ) ⟶ (Opposite.op p : ℤᵒᵖ) := by
    exact (homOfLE (show p ≤ p' from hp)).op
  have hF : F.step p' ≤ F.step p := by
    simpa [Filtration.DecFiltration.step] using (F.subobject_le_of_hom hIdx)
  have hPull :
      (Subobject.pullback (G.inj (Opposite.op q))).obj (F.step p') ≤
        (Subobject.pullback (G.inj (Opposite.op q))).obj (F.step p) :=
    (Subobject.pullback (G.inj (Opposite.op q))).monotone hF
  exact FilteredObject.imageSubobject_mono (C := C) (G.grπ q) hPull

/-- Unfolding lemma for `inducedOnGr`: its `p`-th step is `inducedOnGrStep`. -/
@[simp]
lemma inducedOnGr_step
    (F G : Filtration.DecFiltration (C := C) X) (q p : ℤ) :
    (inducedOnGr (C := C) (X := X) F G q).step p = inducedOnGrStep (C := C) (X := X) F G q p := by
  simp [inducedOnGr, inducedOnGrStep, Filtration.DecFiltration.step, Filtration.subobject,
    Filtration.inj, Filtration.DecFiltration.ofAntitone, FilteredObject.imageSubobject,
    Subobject.mk_arrow]

end

end DecFiltration

end Filtration

end CategoryTheory
