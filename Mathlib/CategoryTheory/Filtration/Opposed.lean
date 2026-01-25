/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module


public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.CategoryTheory.Abelian.Basic

@[expose] public section

/-!
## Opposed filtrations (Deligne, *Théorie de Hodge II*, §1.2.1–§1.2.3)

This file is compatible with the filtration design via `ι ⥤ MonoOver X`:

* a decreasing `ℤ`-filtration on `X` is a functor `ℤᵒᵖ ⥤ MonoOver X`.

In Deligne §1.2, the key categorical invariant of two filtrations is the bigraded object

`Gr_F^p Gr_G^q(X)`

whose vanishing off the diagonal `p+q=n` defines the `n`-opposed condition (1.2.3).

At this stage we define the **symmetric Zassenhaus quotient**

`(F^p ∩ G^q) / ( (F^{p+1} ∩ G^q) + (F^p ∩ G^{q+1}) )`

as an object of `C`, and use it to define `IsNOpposed`.

The Zassenhaus isomorphisms identifying this with iterated graded objects, and the
splitting lemma (Deligne 1.2.5), are developed elsewhere.

-/

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

/-- The Zassenhaus (symmetric) bigraded piece attached to two decreasing `ℤ`-filtrations
`F` and `G`.

It is defined as the cokernel of the inclusion

`(F^{p+1} ∩ G^q) + (F^p ∩ G^{q+1}) ⟶ (F^p ∩ G^q)`.

This is canonically isomorphic to both `Gr_F^p (Gr_G^q X)` and `Gr_G^q (Gr_F^p X)`
(the Zassenhaus / butterfly lemma), which is established elsewhere.
-/
noncomputable def gr₂ (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) : C := by
  classical
  let Xpq : Subobject X := F.step p ⊓ G.step q
  let Ypq : Subobject X := (F.step (p + 1) ⊓ G.step q) ⊔ (F.step p ⊓ G.step (q + 1))
  have hY : Ypq ≤ Xpq := by
    refine sup_le ?_ ?_
    · -- `F^{p+1} ∩ G^q ≤ F^p ∩ G^q`.
      have hp : (Opposite.op (p + 1) : ℤᵒᵖ) ⟶ (Opposite.op p : ℤᵒᵖ) := by
        exact (homOfLE (show p ≤ p + 1 from
          le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op
      have hF : F.step (p + 1) ≤ F.step p := by
        simpa [Filtration.DecFiltration.step] using (F.subobject_le_of_hom hp)
      exact inf_le_inf hF le_rfl
    · -- `F^p ∩ G^{q+1} ≤ F^p ∩ G^q`.
      have hq : (Opposite.op (q + 1) : ℤᵒᵖ) ⟶ (Opposite.op q : ℤᵒᵖ) := by
        exact (homOfLE (show q ≤ q + 1 from
          le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op
      have hG : G.step (q + 1) ≤ G.step q := by
        simpa [Filtration.DecFiltration.step] using (G.subobject_le_of_hom hq)
      exact inf_le_inf le_rfl hG
  exact cokernel ((Ypq).ofLE Xpq hY)

/-- Deligne's `n`-opposed condition (1.2.3), expressed using `gr₂`.

Two filtrations are `n`-opposed if `gr₂ F G p q` vanishes whenever `p + q ≠ n`.
-/
def IsNOpposed (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (gr₂ (C := C) (X := X) F G p q)

/-- Deligne's `n`-opposed condition for **finite** filtrations.

This keeps `IsNOpposed` as the bare vanishing predicate, and bundles Deligne's finiteness
hypotheses (Deligne 1.2.3) into a single definition.
-/
def IsNOpposedFinite (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  Filtration.DecFiltration.IsFinite (C := C) (X := X) F ∧
    Filtration.DecFiltration.IsFinite (C := C) (X := X) G ∧
      IsNOpposed (C := C) (X := X) F G n

lemma isFinite_left_of_isNOpposedFinite {F G : Filtration.DecFiltration (C := C) X} {n : ℤ}
    (h : IsNOpposedFinite (C := C) (X := X) F G n) :
    Filtration.DecFiltration.IsFinite (C := C) (X := X) F :=
  h.1

lemma isFinite_right_of_isNOpposedFinite {F G : Filtration.DecFiltration (C := C) X} {n : ℤ}
    (h : IsNOpposedFinite (C := C) (X := X) F G n) :
    Filtration.DecFiltration.IsFinite (C := C) (X := X) G :=
  h.2.1

lemma isNOpposed_of_isNOpposedFinite {F G : Filtration.DecFiltration (C := C) X} {n : ℤ}
    (h : IsNOpposedFinite (C := C) (X := X) F G n) :
    IsNOpposed (C := C) (X := X) F G n :=
  h.2.2

/-- Convenience lemma: if `F` and `G` are `n`-opposed, then `gr₂ F G p q` is zero off the diagonal.
-/
lemma isZero_gr₂_of_IsNOpposed {F G : Filtration.DecFiltration (C := C) X} {n p q : ℤ}
    (h : IsNOpposed (C := C) (X := X) F G n) (hpq : p + q ≠ n) :
    IsZero (gr₂ (C := C) (X := X) F G p q) :=
  h p q hpq

end

end DecFiltration

end Filtration

end CategoryTheory
