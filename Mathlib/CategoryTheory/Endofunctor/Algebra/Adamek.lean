/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra.ChainShift
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Adamek's initial algebra theorem

Given an endofunctor `F : C ⥤ C` on a category with an initial object `X`,
if the initial chain `X → F(X) → F²(X) → ⋯` has a colimit `L` and `F`
preserves this colimit, then `L` carries the structure of an initial
`F`-algebra. The algebra structure map `F(L) → L` is an isomorphism
(by Lambek's lemma applied to the initial algebra).

## Main definitions

- `CategoryTheory.Endofunctor.Algebra.adamek` : the `F`-algebra on the colimit `L`
- `CategoryTheory.Endofunctor.Algebra.adamekHom` : the unique algebra homomorphism from the
  Adamek algebra to any other algebra
- `CategoryTheory.Endofunctor.Algebra.adamekFromInitial` : the Adamek algebra constructed from
  `HasColimit` and `PreservesColimit` instances
- `CategoryTheory.Endofunctor.Algebra.adamekFixedPoint` : the colimit of the initial chain as
  a fixed point of `F`, i.e. the isomorphism `F(L) ≅ L` (Lambek's lemma)

## Main results

- `CategoryTheory.Endofunctor.Algebra.adamek_isInitial` : the Adamek algebra is initial in
  `Endofunctor.Algebra F`
- `CategoryTheory.Endofunctor.Algebra.adamekFromInitial_isInitial` : initiality from
  `HasColimit` and `PreservesColimit` instances

## References

- [J. Adamek, *Free algebras and automata realizations in the language of categories and
  functors*][adamek1974]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor

universe v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C)

namespace Algebra

section

variable {X : C} (hX : IsInitial X)

/-- The Adamek algebra: the colimit of the initial chain, equipped with the
algebra structure map `F(L) → L` obtained from the preserved colimit. -/
@[simps a]
noncomputable def adamek (c : Cocone (initialChain F hX)) (hc : IsColimit c)
    [PreservesColimit (initialChain F hX) F] : Endofunctor.Algebra F where
  a := c.pt
  str := (isColimitOfPreserves F hc).desc (shiftCocone F hX c)

/-- The structure map commutes with the colimit inclusions:
`F.map (ι_n) ≫ str = ι_{n+1}`. -/
@[reassoc]
lemma adamekStr_fac {c : Cocone (initialChain F hX)} (hc : IsColimit c)
    [PreservesColimit (initialChain F hX) F] (n : ℕ) :
    F.map (c.ι.app n) ≫ (adamek F hX c hc).str = c.ι.app (n + 1) :=
  (isColimitOfPreserves F hc).fac (shiftCocone F hX c) n

/-! ### Algebra cocone -/

/-- The `n`-th leg of the algebra cocone: the unique map `F^n(X) → B.a`. -/
noncomputable def algebraCoconeApp (B : Endofunctor.Algebra F) :
    (n : ℕ) → (F.iterate n).obj X ⟶ B.a
  | 0 => hX.to B.a
  | n + 1 => F.map (algebraCoconeApp B n) ≫ B.str

@[simp]
lemma algebraCoconeApp_zero (B : Endofunctor.Algebra F) :
    algebraCoconeApp F hX B 0 = hX.to B.a := rfl

@[simp]
lemma algebraCoconeApp_succ (B : Endofunctor.Algebra F) (n : ℕ) :
    algebraCoconeApp F hX B (n + 1) =
    F.map (algebraCoconeApp F hX B n) ≫ B.str := rfl

/-- The successor map of the initial chain composes with the next algebra cocone leg
to give the current one. -/
lemma iterateMap_comp_algebraCoconeApp (B : Endofunctor.Algebra F) (n : ℕ) :
    iterateMap (hX.to (F.obj X)) n ≫ algebraCoconeApp F hX B (n + 1) =
    algebraCoconeApp F hX B n := by
  induction n with
  | zero => exact hX.hom_ext _ _
  | succ k ih =>
    change F.map (iterateMap (hX.to (F.obj X)) k) ≫
      (F.map (algebraCoconeApp F hX B (k + 1)) ≫ B.str) =
      F.map (algebraCoconeApp F hX B k) ≫ B.str
    rw [← Category.assoc, ← F.map_comp, ih]

/-- Given an `F`-algebra `(B, β)`, define the cocone over the initial chain with point `B`. -/
noncomputable def algebraCocone (B : Endofunctor.Algebra F) :
    Cocone (initialChain F hX) where
  pt := B.a
  ι := NatTrans.ofSequence
    (fun n => algebraCoconeApp F hX B n)
    (fun n => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
        initialChain_map_succ]
      exact iterateMap_comp_algebraCoconeApp F hX B n)

@[simp]
lemma algebraCocone_ι_app (B : Endofunctor.Algebra F) (n : ℕ) :
    (algebraCocone F hX B).ι.app n = algebraCoconeApp F hX B n := rfl

/-! ### Initiality -/

section Initiality

variable {c : Cocone (initialChain F hX)} (hc : IsColimit c)
variable [PreservesColimit (initialChain F hX) F]

/-- The unique algebra homomorphism from the Adamek algebra to any other algebra. -/
noncomputable def adamekHom (B : Endofunctor.Algebra F) :
    adamek F hX _ hc ⟶ B where
  f := hc.desc (algebraCocone F hX B)
  h := by
    apply (isColimitOfPreserves F hc).hom_ext
    intro n
    simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app]
    conv_lhs => erw [← Category.assoc, ← F.map_comp, hc.fac (algebraCocone F hX B) n]
    conv_rhs => erw [← Category.assoc, adamekStr_fac F hX hc n,
      hc.fac (algebraCocone F hX B) (n + 1)]
    rfl

@[simp]
lemma adamekHom_f (B : Endofunctor.Algebra F) :
    (adamekHom F hX hc B).f = hc.desc (algebraCocone F hX B) := rfl

/-- Any algebra homomorphism from the Adamek algebra equals the canonical one. -/
lemma adamekHom_unique (B : Endofunctor.Algebra F)
    (g : adamek F hX _ hc ⟶ B) :
    g = adamekHom F hX hc B := by
  ext
  apply hc.uniq (algebraCocone F hX B)
  intro n
  induction n with
  | zero => exact hX.hom_ext _ _
  | succ n ih =>
    rw [show c.ι.app (n + 1) = F.map (c.ι.app n) ≫ (adamek F hX c hc).str from
      (adamekStr_fac F hX hc n).symm]
    erw [Category.assoc, g.h.symm]
    conv_lhs => erw [← Category.assoc, ← F.map_comp, ih]
    rfl

/-- **Adamek's Initial Algebra Theorem.** The colimit of the initial chain,
equipped with the algebra structure from the preserved colimit,
is an initial object in the category of `F`-algebras. -/
noncomputable def adamek_isInitial :
    IsInitial (adamek F hX _ hc) :=
  IsInitial.ofUniqueHom
    (fun B => adamekHom F hX hc B)
    (fun B g => adamekHom_unique F hX hc B g)

end Initiality

end

/-! ### Convenience API from `HasColimit` and `PreservesColimit` -/

section Connection

variable [HasInitial C]
variable [HasColimit (initialChain F initialIsInitial)]
variable [PreservesColimit (initialChain F initialIsInitial) F]

/-- The Adamek initial algebra constructed from `HasColimit` and `PreservesColimit` instances. -/
noncomputable def adamekFromInitial : Endofunctor.Algebra F :=
  adamek F initialIsInitial
    (colimit.cocone (initialChain F initialIsInitial))
    (colimit.isColimit (initialChain F initialIsInitial))

/-- The Adamek algebra constructed from instances is initial. -/
noncomputable def adamekFromInitial_isInitial :
    IsInitial (adamekFromInitial F) :=
  adamek_isInitial F initialIsInitial
    (colimit.isColimit (initialChain F initialIsInitial))

/-- The colimit of the initial chain is a fixed point of `F`: `F(L) ≅ L`.
This is Lambek's lemma applied to the Adamek initial algebra. -/
noncomputable def adamekFixedPoint :
    F.obj (colimit (initialChain F initialIsInitial)) ≅
    colimit (initialChain F initialIsInitial) := by
  haveI : IsIso (adamekFromInitial F).str :=
    Endofunctor.Algebra.Initial.str_isIso (adamekFromInitial_isInitial F)
  change F.obj (adamekFromInitial F).a ≅ (adamekFromInitial F).a
  exact asIso (adamekFromInitial F).str

end Connection

end Algebra

end CategoryTheory.Endofunctor
