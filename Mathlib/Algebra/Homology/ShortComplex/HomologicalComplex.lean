/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# The short complexes attached to homological complexes

In this file, we define a functor
`shortComplexFunctor C c i : HomologicalComplex C c ⥤ ShortComplex C`.
By definition, the image of a homological complex `K` by this functor
is the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`.

When the homology refactor is completed (TODO @joelriou), the homology
of a homological complex `K` in degree `i` shall be the homology
of the short complex `(shortComplexFunctor C c i).obj K`, which can be
abbreviated as `K.sc i`.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
@[simps]
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
@[simps!]
noncomputable def shortComplexFunctor (i : ι) :=
  shortComplexFunctor' C c (c.prev i) i (c.next i)

/-- The natural isomorphism `shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k`
when `c.prev j = i` and `c.next j = k`. -/
@[simps!]
noncomputable def natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by aesop_cat) (by aesop_cat)) (by aesop_cat)
        -- 🎉 no goals
                       -- 🎉 no goals
                                       -- 🎉 no goals

variable {C c}
variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (ψ : L ⟶ M)

/-- The short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
abbrev sc' (i j k : ι) := (shortComplexFunctor' C c i j k).obj K

/-- The short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
noncomputable abbrev sc (i : ι) := (shortComplexFunctor C c i).obj K

/-- The canonical isomorphism `K.sc j ≅ K.sc' i j k` when `c.prev j = i` and `c.next j = k`. -/
noncomputable abbrev isoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    K.sc j ≅ K.sc' i j k := (natIsoSc' C c i j k hi hk).app K

end HomologicalComplex
