/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The stabilizer of an object acts as outer endomorphisms on its endomorphism monoid

If `X : C` is an object in a category `C`, we define the stabilizer of `X` to be the submonoid
of endofunctors `F : End C` for which `F.obj X` is isomorphic to `X`. We construct an action of
the stabilizer on `End X` as outer endomorphisms, i.e. an action by endomorphisms that is
well-defined only up to conjugation (inner automorphisms).

This is the categorical core of, and will be used to construct, the Dehn–Nielsen–Baer isomorphism
between extended mapping class groups of surfaces and outer automorphism groups of fundamental
groups.
-/

@[expose] public section

namespace CategoryTheory

variable (C : Cat)

open Cat.Hom in
/-- `isIsomorphicSetoid` as a congruence relation on the endofunctor monoid of a category. -/
def natIsoCon : Con (End C) where
  toSetoid := isIsomorphicSetoid (C ⟶ C)
  mul' := fun ⟨e⟩ ⟨e'⟩ ↦ ⟨isoMk <| NatIso.hcomp (toNatIso e') (toNatIso e)⟩

variable {C}

/-- The stabilizer up to isomorphism of an object in a category. -/
def stabilizer (X : C) : Submonoid (End C) where
  carrier := {F | Nonempty (F.toFunctor.obj X ≅ X)}
  mul_mem' := fun {F _G} ⟨eF⟩ ⟨eG⟩ ↦ ⟨(F.1.mapIso eG).trans eF⟩
  one_mem' := ⟨.refl X⟩

/-- `isIsomorphicSetoid` as a congruence relation on the stabilizer of an object in a category. -/
def natIsoConStabilizer (X : C) : Con (stabilizer X) := (natIsoCon C).comap (↑) fun _ _ ↦ rfl

lemma toOuterEndEnd_eq {X : C} {F : C ⥤ C} {f : End X →* End (F.obj X)}
    (e e' : F.obj X ≅ X) : (⟦.comp e.conj f⟧ : Monoid.OuterEnd (End X)) = ⟦.comp e'.conj f⟧ :=
  Quotient.sound ⟨(Aut.unitsEndEquivAut X).symm (e'.symm ≪≫ e), by
    ext; exact (Iso.trans_conj ..).trans congr(e.conj $(e'.conj.left_inv _))⟩

/-- The natural homomorphism from the stabilizer of an object `X` to the outer endomorphism monoid
of the endomorphism monoid of `X`. -/
@[simps] noncomputable def toOuterEndEnd {X : C} : stabilizer X →* Monoid.OuterEnd (End X) where
  toFun F := ⟦.comp F.2.some.conj <| F.1.toFunctor.mapEnd X⟧
  map_one' := Quotient.sound ⟨(Aut.unitsEndEquivAut X).symm _, rfl⟩
  map_mul' F G := (toOuterEndEnd_eq _ (F.1.toFunctor.mapIso G.2.some ≪≫ F.2.some :)).trans <|
    congr_arg (⟦·⟧) <| MonoidHom.ext fun _ ↦ (Iso.trans_conj ..).trans <|
    congr_arg F.2.some.conj <| (Functor.map_conj ..).symm

/-- Isomorphic endofunctors in the stabilizer induce the same outer endomorphism. -/
lemma toOuterEndEnd_eq_of_iso {X : C} {F G : stabilizer X} (e : F.1.toFunctor ≅ G.1.toFunctor) :
    toOuterEndEnd F = toOuterEndEnd G :=
  (toOuterEndEnd_eq _ (e.app X ≪≫ G.2.some)).trans <|
    congr_arg (⟦·⟧) <| MonoidHom.ext fun _ ↦ by simp [Iso.conj_apply]

noncomputable def quotientToOuterEndEnd {X : C} :
    (natIsoConStabilizer X).Quotient →* Monoid.OuterEnd (End X) :=
  Con.lift _ toOuterEndEnd fun _ _ ⟨e⟩ ↦ toOuterEndEnd_eq_of_iso (Cat.Hom.toNatIso e)

end CategoryTheory
