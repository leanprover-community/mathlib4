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

Given an endofunctor `F : C ⥤ C` on a category with an initial object,
if the initial chain `⊥ → F(⊥) → F²(⊥) → ⋯` has a colimit `L` and `F`
preserves this colimit, then `L` carries the structure of an initial
`F`-algebra. The algebra structure map `F(L) → L` is an isomorphism
(by Lambek's lemma applied to the initial algebra).

## Main definitions

- `CategoryTheory.Endofunctor.Algebra.adamek` : the `F`-algebra on the colimit `L`
- `CategoryTheory.Endofunctor.Algebra.adamekHom` : the unique algebra homomorphism from the
  Adamek algebra to any other algebra
- `CategoryTheory.Endofunctor.Algebra.adamekFromInitial` : the Adamek algebra constructed from
  `HasColimit` and `PreservesColimit` instances
- `CategoryTheory.Endofunctor.Algebra.adamekStructureIso` : the isomorphism `F(L) ≅ L`
  (Lambek's lemma)
- `CategoryTheory.Endofunctor.Algebra.adamekFixedPoint` : the colimit as a fixed point of `F`

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
variable (F : C ⥤ C) [HasInitial C]

/-! ### Algebra structure on the colimit -/

section AlgebraConstruction

variable {c : Cocone (initialChain F)} (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- The colimit of `F` applied to the initial chain is a colimit (by preservation). -/
noncomputable def preservedColimit :
    IsColimit (F.mapCocone c) :=
  isColimitOfPreserves F hc

/-- The algebra structure map `F(L) → L` for the Adamek algebra. -/
noncomputable def adamekStr : F.obj c.pt ⟶ c.pt :=
  (preservedColimit F hc).desc (shiftCocone F c)

/-- The structure map commutes with the colimit inclusions:
`F.map (ι_n) ≫ adamekStr = ι_{n+1}`. -/
@[reassoc]
lemma adamekStr_fac (n : ℕ) :
    F.map (c.ι.app n) ≫ adamekStr F hc = c.ι.app (n + 1) :=
  (preservedColimit F hc).fac (shiftCocone F c) n

end AlgebraConstruction

namespace Algebra

section AlgebraDefinition

variable (c : Cocone (initialChain F)) (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- The Adamek algebra: the colimit of the initial chain, equipped with the
algebra structure map `F(L) → L` obtained from the preserved colimit. -/
noncomputable def adamek : Endofunctor.Algebra F where
  a := c.pt
  str := adamekStr F hc

@[simp]
lemma adamek_a : (adamek F c hc).a = c.pt := rfl

@[simp]
lemma adamek_str : (adamek F c hc).str = adamekStr F hc := rfl

end AlgebraDefinition

/-! ### Algebra cocone and initiality -/

section AlgebraCoconeApp

/-- The `n`-th leg of the algebra cocone: the unique map `F^n(⊥) → B.a`. -/
noncomputable def algebraCoconeApp (B : Endofunctor.Algebra F) :
    (n : ℕ) → iterateObj F n ⟶ B.a
  | 0 => initial.to B.a
  | n + 1 => F.map (algebraCoconeApp B n) ≫ B.str

@[simp]
lemma algebraCoconeApp_zero (B : Endofunctor.Algebra F) :
    algebraCoconeApp F B 0 = initial.to B.a := rfl

@[simp]
lemma algebraCoconeApp_succ (B : Endofunctor.Algebra F) (n : ℕ) :
    algebraCoconeApp F B (n + 1) =
    F.map (algebraCoconeApp F B n) ≫ B.str := rfl

/-- The successor map of the chain composes with the next algebra cocone leg
to give the current one: `iterateMap k ≫ f_{k+1} = f_k`. -/
lemma iterateMap_comp_algebraCoconeApp (B : Endofunctor.Algebra F) (k : ℕ) :
    iterateMap F k ≫ algebraCoconeApp F B (k + 1) = algebraCoconeApp F B k := by
  induction k with
  | zero => exact initial.hom_ext _ _
  | succ k ih =>
    change F.map (iterateMap F k) ≫ (F.map (algebraCoconeApp F B (k + 1)) ≫ B.str) =
      F.map (algebraCoconeApp F B k) ≫ B.str
    rw [← Category.assoc, ← F.map_comp, ih]

end AlgebraCoconeApp

section Initiality

variable {c : Cocone (initialChain F)} (hc : IsColimit c)
variable [PreservesColimit (initialChain F) F]

/-- Given an `F`-algebra `(B, β)`, define the cocone over the initial chain with point `B`. -/
noncomputable def algebraCocone (B : Endofunctor.Algebra F) :
    Cocone (initialChain F) where
  pt := B.a
  ι :=
  { app := fun n => algebraCoconeApp F B n
    naturality := by
      intro m n α
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      have hle := leOfHom α
      rw [show (initialChain F).map α = (initialChain F).map (homOfLE hle) from
        congr_arg _ (Subsingleton.elim _ _)]
      induction hle with
      | refl =>
        rw [show (homOfLE (le_refl m) : (m : ℕ) ⟶ m) = 𝟙 _ from Subsingleton.elim _ _]
        rw [Functor.map_id, Category.id_comp]
      | @step k hle' ih =>
        rw [show (homOfLE (Nat.le.step hle') : (m : ℕ) ⟶ (k + 1)) =
          (homOfLE hle' : (m : ℕ) ⟶ k) ≫
          (homOfLE (Nat.le_add_right k 1) : (k : ℕ) ⟶ (k + 1)) from
          Subsingleton.elim _ _]
        simp only [Functor.map_comp, Category.assoc, initialChain_map_succ]
        -- Goal: ... ≫ iterateMap F k ≫ algebraCoconeApp F B k.succ = ...
        erw [iterateMap_comp_algebraCoconeApp F B k]
        exact ih (homOfLE hle') }

omit [PreservesColimit (initialChain F) F] in
@[simp]
lemma algebraCocone_ι_app (B : Endofunctor.Algebra F) (n : ℕ) :
    (algebraCocone F B).ι.app n = algebraCoconeApp F B n := rfl

/-- The unique algebra homomorphism from the Adamek algebra to any other algebra. -/
noncomputable def adamekHom (B : Endofunctor.Algebra F) :
    adamek F _ hc ⟶ B where
  f := hc.desc (algebraCocone F B)
  h := by
    apply (preservedColimit F hc).hom_ext
    intro n
    simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app]
    -- Goal: F.map (c.ι.app n) ≫ F.map (desc) ≫ B.str =
    --       F.map (c.ι.app n) ≫ (adamek ...).str ≫ desc
    -- Both sides equal algebraCoconeApp F B (n + 1)
    -- LHS: reassociate and fold F.map_comp
    conv_lhs => erw [← Category.assoc, ← F.map_comp, hc.fac (algebraCocone F B) n]
    -- RHS: unfold adamek str and use fac
    conv_rhs => erw [adamek_str, ← Category.assoc, adamekStr_fac F hc n,
      hc.fac (algebraCocone F B) (n + 1)]
    rfl

@[simp]
lemma adamekHom_f (B : Endofunctor.Algebra F) :
    (adamekHom F hc B).f = hc.desc (algebraCocone F B) := rfl

/-- Any algebra homomorphism from the Adamek algebra equals the canonical one. -/
lemma adamekHom_unique (B : Endofunctor.Algebra F)
    (g : adamek F _ hc ⟶ B) :
    g = adamekHom F hc B := by
  ext
  apply hc.uniq (algebraCocone F B)
  intro n
  induction n with
  | zero => exact initial.hom_ext _ _
  | succ n ih =>
    rw [show c.ι.app (n + 1) = F.map (c.ι.app n) ≫ adamekStr F hc from
      (adamekStr_fac F hc n).symm]
    erw [Category.assoc]
    have hg : adamekStr F hc ≫ g.f = F.map g.f ≫ B.str := by
      have := g.h; simp only [adamek_str] at this; exact this.symm
    erw [hg]
    conv_lhs => erw [← Category.assoc, ← F.map_comp, ih]
    rfl

/-- **Adamek's Initial Algebra Theorem.** The colimit of the initial chain,
equipped with the algebra structure from the preserved colimit,
is an initial object in the category of `F`-algebras. -/
noncomputable def adamek_isInitial :
    IsInitial (adamek F _ hc) :=
  IsInitial.ofUniqueHom
    (fun B => adamekHom F hc B)
    (fun B g => adamekHom_unique F hc B g)

end Initiality

/-! ### Convenience API from `HasColimit` and `PreservesColimit` -/

section Connection

variable [HasColimit (initialChain F)]
variable [PreservesColimit (initialChain F) F]

/-- The standard colimit cocone for the initial chain. -/
noncomputable def standardCocone : Cocone (initialChain F) :=
  colimit.cocone (initialChain F)

/-- The standard colimit is indeed a colimit. -/
noncomputable def standardIsColimit : IsColimit (standardCocone F) :=
  colimit.isColimit (initialChain F)

/-- The Adamek initial algebra constructed from `HasColimit` and `PreservesColimit` instances. -/
noncomputable def adamekFromInitial : Endofunctor.Algebra F :=
  adamek F (standardCocone F) (standardIsColimit F)

/-- The Adamek algebra constructed from instances is initial. -/
noncomputable def adamekFromInitial_isInitial :
    IsInitial (adamekFromInitial F) :=
  adamek_isInitial F (standardIsColimit F)

/-- The structure map of the initial algebra is an isomorphism: `F(L) ≅ L`.
This is Lambek's lemma applied to the Adamek initial algebra. -/
noncomputable def adamekStructureIso :
    F.obj (adamekFromInitial F).a ≅ (adamekFromInitial F).a := by
  haveI : IsIso (adamekFromInitial F).str :=
    Endofunctor.Algebra.Initial.str_isIso (adamekFromInitial_isInitial F)
  exact asIso (adamekFromInitial F).str

/-- The colimit of the initial chain is a fixed point of `F`: `F(L) ≅ L`. -/
noncomputable def adamekFixedPoint :
    F.obj (colimit (initialChain F)) ≅ colimit (initialChain F) :=
  adamekStructureIso F

end Connection

end Algebra

end CategoryTheory.Endofunctor
