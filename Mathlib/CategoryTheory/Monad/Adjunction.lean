/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Monad.Algebra

#align_import category_theory.monad.adjunction from "leanprover-community/mathlib"@"ea3009f6c1a37dc031f741382dbb3ed93c965620"

/-!
# Adjunctions and monads

We develop the basic relationship between adjunctions and monads.

Given an adjunction `h : L ⊣ R`, we have `h.toMonad : Monad C` and `h.toComonad : Comonad D`.
We then have
`Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.algebra`
sending `Y : D` to the Eilenberg-Moore algebra for `L ⋙ R` with underlying object `R.obj X`,
and dually `Comonad.comparison`.

We say `R : D ⥤ C` is `MonadicRightAdjoint`, if it is a right adjoint and its `Monad.comparison`
is an equivalence of categories. (Similarly for `ComonadicLeftAdjoint`.)

Finally we prove that reflective functors are `MonadicRightAdjoint`.
-/


namespace CategoryTheory

open Category

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

namespace Adjunction

/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
-- Porting note: Specifying simps projections manually to match mathlib3 behavior.
@[simps! coe η μ]
def toMonad (h : L ⊣ R) : Monad C where
  toFunctor := L ⋙ R
  η' := h.unit
  μ' := whiskerRight (whiskerLeft L h.counit) R
  assoc' X := by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit' X := by
    dsimp
    rw [← R.map_comp]
    simp
#align category_theory.adjunction.to_monad CategoryTheory.Adjunction.toMonad

/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a comonad on
the category `D`.
-/
-- Porting note: Specifying simps projections manually to match mathlib3 behavior.
@[simps coe ε δ]
def toComonad (h : L ⊣ R) : Comonad D where
  toFunctor := R ⋙ L
  ε' := h.counit
  δ' := whiskerRight (whiskerLeft R h.unit) L
  coassoc' X := by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit' X := by
    dsimp
    rw [← L.map_comp]
    simp
#align category_theory.adjunction.to_comonad CategoryTheory.Adjunction.toComonad

/-- The monad induced by the Eilenberg-Moore adjunction is the original monad.  -/
@[simps!]
def adjToMonadIso (T : Monad C) : T.adj.toMonad ≅ T :=
  MonadIso.mk (NatIso.ofComponents fun X => Iso.refl _)
#align category_theory.adjunction.adj_to_monad_iso CategoryTheory.Adjunction.adjToMonadIso

/-- The comonad induced by the Eilenberg-Moore adjunction is the original comonad. -/
@[simps!]
def adjToComonadIso (G : Comonad C) : G.adj.toComonad ≅ G :=
  ComonadIso.mk (NatIso.ofComponents fun X => Iso.refl _)
#align category_theory.adjunction.adj_to_comonad_iso CategoryTheory.Adjunction.adjToComonadIso

/--
Given an adjunction `L ⊣ R`, if `L ⋙ R` is abstractly isomorphic to the identity functor, then the
unit is an isomorphism.
-/
def unitAsIsoOfIso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) :  𝟭 C ≅ L ⋙ R where
  hom := adj.unit
  inv :=  i.hom ≫ (adj.toMonad.transport i).μ
  hom_inv_id := by
    rw [← assoc]
    ext X
    exact (adj.toMonad.transport i).right_unit X
  inv_hom_id := by
    rw [assoc, ← Iso.eq_inv_comp, comp_id, ← id_comp i.inv, Iso.eq_comp_inv, assoc,
      NatTrans.id_comm]
    ext X
    exact (adj.toMonad.transport i).right_unit X

lemma isIso_unit_of_iso  (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit :=
  (inferInstanceAs (IsIso (unitAsIsoOfIso adj i).hom))

/--
Given an adjunction `L ⊣ R`, if `L ⋙ R` is isomorphic to the identity functor, then `L` is
fully faithful.
-/
noncomputable def fullyFaithfulLOfCompIsoId (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : L.FullyFaithful :=
  haveI := adj.isIso_unit_of_iso i
  adj.fullyFaithfulLOfIsIsoUnit

/--
Given an adjunction `L ⊣ R`, if `R ⋙ L` is abstractly isomorphic to the identity functor, then the
counit is an isomorphism.
-/
def counitAsIsoOfIso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R ⋙ L ≅ 𝟭 D where
  hom := adj.counit
  inv := (adj.toComonad.transport j).δ ≫ j.inv
  hom_inv_id := by
    rw [← assoc, Iso.comp_inv_eq, id_comp, ← comp_id j.hom, ← Iso.inv_comp_eq, ← assoc,
      NatTrans.id_comm]
    ext X
    exact (adj.toComonad.transport j).right_counit X
  inv_hom_id := by
    rw [assoc]
    ext X
    exact (adj.toComonad.transport j).right_counit X

lemma isIso_counit_of_iso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit :=
  inferInstanceAs (IsIso (counitAsIsoOfIso adj j).hom)

/--
Given an adjunction `L ⊣ R`, if `R ⋙ L` is isomorphic to the identity functor, then `R` is
fully faithful.
-/
noncomputable def fullyFaithfulROfCompIsoId (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R.FullyFaithful :=
  haveI := adj.isIso_counit_of_iso j
  adj.fullyFaithfulROfIsIsoCounit

end Adjunction

/-- Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
def Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.Algebra where
  obj X :=
    { A := R.obj X
      a := R.map (h.counit.app X)
      assoc := by
        dsimp
        rw [← R.map_comp, ← Adjunction.counit_naturality, R.map_comp] }
  map f :=
    { f := R.map f
      h := by
        dsimp
        rw [← R.map_comp, Adjunction.counit_naturality, R.map_comp] }
#align category_theory.monad.comparison CategoryTheory.Monad.comparison

/-- The underlying object of `(Monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
def Monad.comparisonForget (h : L ⊣ R) : Monad.comparison h ⋙ h.toMonad.forget ≅ R where
  hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.monad.comparison_forget CategoryTheory.Monad.comparisonForget

theorem Monad.left_comparison (h : L ⊣ R) : L ⋙ Monad.comparison h = h.toMonad.free :=
  rfl
#align category_theory.monad.left_comparison CategoryTheory.Monad.left_comparison

instance [R.Faithful] (h : L ⊣ R) : (Monad.comparison h).Faithful where
  map_injective {_ _} _ _ w := R.map_injective (congr_arg Monad.Algebra.Hom.f w : _)

instance (T : Monad C) : (Monad.comparison T.adj).Full where
  map_surjective {_ _} f := ⟨⟨f.f, by simpa using f.h⟩, rfl⟩

instance (T : Monad C) : (Monad.comparison T.adj).EssSurj where
  mem_essImage X :=
    ⟨{  A := X.A
        a := X.a
        unit := by simpa using X.unit
        assoc := by simpa using X.assoc },
    ⟨Monad.Algebra.isoMk (Iso.refl _)⟩⟩

/--
Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
def Comonad.comparison (h : L ⊣ R) : C ⥤ h.toComonad.Coalgebra where
  obj X :=
    { A := L.obj X
      a := L.map (h.unit.app X)
      coassoc := by
        dsimp
        rw [← L.map_comp, ← Adjunction.unit_naturality, L.map_comp] }
  map f :=
    { f := L.map f
      h := by
        dsimp
        rw [← L.map_comp]
        simp }
#align category_theory.comonad.comparison CategoryTheory.Comonad.comparison

/-- The underlying object of `(Comonad.comparison L).obj X` is just `L.obj X`.
-/
@[simps]
def Comonad.comparisonForget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    Comonad.comparison h ⋙ h.toComonad.forget ≅ L where
  hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.comonad.comparison_forget CategoryTheory.Comonad.comparisonForget

theorem Comonad.left_comparison (h : L ⊣ R) : R ⋙ Comonad.comparison h = h.toComonad.cofree :=
  rfl
#align category_theory.comonad.left_comparison CategoryTheory.Comonad.left_comparison

instance Comonad.comparison_faithful_of_faithful [L.Faithful] (h : L ⊣ R) :
    (Comonad.comparison h).Faithful where
  map_injective {_ _} _ _ w := L.map_injective (congr_arg Comonad.Coalgebra.Hom.f w : _)
#align category_theory.comonad.comparison_faithful_of_faithful CategoryTheory.Comonad.comparison_faithful_of_faithful

instance (G : Comonad C) : (Comonad.comparison G.adj).Full where
  map_surjective f := ⟨⟨f.f, by simpa using f.h⟩, rfl⟩

instance (G : Comonad C) : (Comonad.comparison G.adj).EssSurj where
  mem_essImage X :=
    ⟨{  A := X.A
        a := X.a
        counit := by simpa using X.counit
        coassoc := by simpa using X.coassoc },
      ⟨Comonad.Coalgebra.isoMk (Iso.refl _)⟩⟩

/-- A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `Monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class MonadicRightAdjoint (R : D ⥤ C) where
  /-- a choice of left adjoint for `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R
  eqv : (Monad.comparison adj).IsEquivalence
#align category_theory.monadic_right_adjoint CategoryTheory.MonadicRightAdjoint

/-- The left adjoint functor to `R` given by `[MonadicRightAdjoint R]`. -/
def monadicLeftAdjoint (R : D ⥤ C) [MonadicRightAdjoint R] : C ⥤ D :=
  MonadicRightAdjoint.L (R := R)

/-- The adjunction `monadicLeftAdjoint R ⊣ R` given by `[MonadicRightAdjoint R]`. -/
def monadicAdjunction (R : D ⥤ C) [MonadicRightAdjoint R] :
    monadicLeftAdjoint R ⊣ R :=
  MonadicRightAdjoint.adj

instance (R : D ⥤ C) [MonadicRightAdjoint R] :
    (Monad.comparison (monadicAdjunction R)).IsEquivalence :=
  MonadicRightAdjoint.eqv

instance (R : D ⥤ C) [MonadicRightAdjoint R] : R.IsRightAdjoint :=
  (monadicAdjunction R).isRightAdjoint

noncomputable instance (T : Monad C) : MonadicRightAdjoint T.forget where
  adj := T.adj
  eqv := { }

/--
A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `Comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class ComonadicLeftAdjoint (L : C ⥤ D) where
  /-- a choice of right adjoint for `L` -/
  R : D ⥤ C
  /-- `L` is a right adjoint -/
  adj : L ⊣ R
  eqv : (Comonad.comparison adj).IsEquivalence
#align category_theory.comonadic_left_adjoint CategoryTheory.ComonadicLeftAdjoint

/-- The right adjoint functor to `L` given by `[ComonadicLeftAdjoint L]`. -/
def comonadicRightAdjoint (L : C ⥤ D) [ComonadicLeftAdjoint L] : D ⥤ C :=
  ComonadicLeftAdjoint.R (L := L)

/-- The adjunction `L ⊣ comonadicRightAdjoint L` given by `[ComonadicLeftAdjoint L]`. -/
def comonadicAdjunction (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    L ⊣ comonadicRightAdjoint L :=
  ComonadicLeftAdjoint.adj

instance (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    (Comonad.comparison (comonadicAdjunction L)).IsEquivalence :=
  ComonadicLeftAdjoint.eqv

instance (L : C ⥤ D) [ComonadicLeftAdjoint L] : L.IsLeftAdjoint :=
  (comonadicAdjunction L).isLeftAdjoint

noncomputable instance (G : Comonad C) : ComonadicLeftAdjoint G.forget where
  adj := G.adj
  eqv := { }

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
instance μ_iso_of_reflective [Reflective R] : IsIso (reflectorAdjunction R).toMonad.μ := by
  dsimp
  infer_instance
#align category_theory.μ_iso_of_reflective CategoryTheory.μ_iso_of_reflective

attribute [instance] MonadicRightAdjoint.eqv
attribute [instance] ComonadicLeftAdjoint.eqv

namespace Reflective

instance [Reflective R] (X : (reflectorAdjunction R).toMonad.Algebra) :
    IsIso ((reflectorAdjunction R).unit.app X.A) :=
  ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [Functor.id_obj]
        rw [← (reflectorAdjunction R).unit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [unit_obj_eq_map_unit, ← Functor.map_comp, ← Functor.map_comp]
        erw [X.unit]
        simp⟩⟩⟩

instance comparison_essSurj [Reflective R] :
    (Monad.comparison (reflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(reflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Monad.Algebra.isoMk ?_ ?_
  · exact asIso ((reflectorAdjunction R).unit.app X.A)
  dsimp only [Functor.comp_map, Monad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Monad.comparison_obj_A, Adjunction.toMonad_coe]
  rw [← cancel_epi ((reflectorAdjunction R).unit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, comp_id]
  apply (X.unit_assoc _).symm
#align category_theory.reflective.comparison_ess_surj CategoryTheory.Reflective.comparison_essSurj

lemma comparison_full [R.Full] {L : C ⥤ D} (adj : L ⊣ R):
    (Monad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by aesop_cat⟩
#align category_theory.reflective.comparison_full CategoryTheory.Reflective.comparison_full

end Reflective

namespace Coreflective

instance [Coreflective R] (X : (coreflectorAdjunction R).toComonad.Coalgebra) :
    IsIso ((coreflectorAdjunction R).counit.app X.A) :=
  ⟨⟨X.a,
      ⟨by
        dsimp only [Functor.id_obj]
        rw [← (coreflectorAdjunction R).counit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [counit_obj_eq_map_counit, ← Functor.map_comp, ← Functor.map_comp]
        erw [X.counit]
        simp, X.counit⟩⟩⟩

instance comparison_essSurj [Coreflective R] :
    (Comonad.comparison (coreflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(coreflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Comonad.Coalgebra.isoMk ?_ ?_
  · exact (asIso ((coreflectorAdjunction R).counit.app X.A)).symm
  dsimp only [Functor.comp_map, Comonad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Comonad.comparison_obj_A, Adjunction.toComonad_coe]
  rw [← cancel_epi ((coreflectorAdjunction R).counit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp
  have := Adjunction.counit_naturality (coreflectorAdjunction R) X.a
  rw [← Category.assoc]
  let adj := (coreflectorAdjunction R)
  change (adj.counit.app X.A ≫ X.a) ≫ R.map (adj.unit.app ((coreflector R).obj X.A)) =
    R.map (adj.unit.app ((coreflector R).obj X.A))
  sorry

lemma comparison_full [R.Full] {L : C ⥤ D} (adj : R ⊣ L):
    (Comonad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by aesop_cat⟩

end Coreflective

-- It is possible to do this computably since the construction gives the data of the inverse, not
-- just the existence of an inverse on each object.
-- see Note [lower instance priority]
/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
instance (priority := 100) monadicOfReflective [Reflective R] :
    MonadicRightAdjoint R where
  adj := reflectorAdjunction R
  eqv := { full := Reflective.comparison_full _ }
#align category_theory.monadic_of_reflective CategoryTheory.monadicOfReflective

instance (priority := 100) comonadicOfReflective [Coreflective R] :
    ComonadicLeftAdjoint R where
  adj := coreflectorAdjunction R
  eqv := { full := Coreflective.comparison_full _ }

end CategoryTheory
