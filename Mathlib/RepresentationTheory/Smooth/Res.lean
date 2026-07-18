/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Smooth.SmRep
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Induction

This file defines the restriction functor, the coinduced functor and the induced functor between
categories of smooth representations, and also proves the adjunctions.

## Main definitions

* `Representation.Smooth.SmRep.resFunctor`
* `Representation.Smooth.SmRep.coindFunctor`
* `Representation.Smooth.SmRep.indFunctor`

## Implementation notes

The restriction functor `SmRep.res` is defined for continuous group morphisms `H →ₜ* G`, fitting
into a strictly commutative diagram of functors
  Rep k G   --- Rep.res --->  Rep k H
     ∧                           ∧
     |                           |
     ι (natural inclusion)       ι (natural inclusion)
     |                           |
  SmRep k G -- SmRep.res --> SmRep k H.

The coinduced functor `SmRep.coind` is defined for arbitrary group morphisms `H →* G`, by cutting
out the smooth vectors from the naive coinduced representations. In other words, we have
  `SmRep.coind = ι (natural inclusion) ⋙ Rep.coind ⋙ smVec (taking smooth vectors).`
When `H` is a subgroup of G, this is also known as the "smooth induction functor" in literature.

The induced functor `SmRep.ind` is defined for group morphism `H →* G` which is an open map, fitting
into a strictly commutative diagram of functors
  Rep k H   --- Rep.ind --->  Rep k G
     ∧                           ∧
     |                           |
     ι (natural inclusion)       ι (natural inclusion)
     |                           |
  SmRep k H -- SmRep.ind --> SmRep k G.
When `H` is a compact (or compact modulo center) open subgroup of `G`, this functor is also known as
the "compact induction functor" in literature.

The adjunctions are then formally obtained by combining the adjunctions in `Rep`, the adjunction
  `ι (natural inclusion) ⊣ smVec (taking smooth vectors)`, and the commutative diagrams above.

-/

@[expose] public section

universe t u v w
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type w} [Group H] [TopologicalSpace H]

open CategoryTheory

namespace Representation.Smooth

section representation

variable {k : Type u} [Semiring k]
variable {V : Type t} [AddCommMonoid V] [Module k V]

instance instIsSmooth_comp {ρ : Representation k G V} [h : IsSmooth ρ] {s : H →ₜ* G} :
    IsSmooth (ρ.comp s.1) := by
  rw [isSmooth_iff]
  exact fun v => s.2.isOpen_preimage (stabilizer ρ v) (h.smooth v)

/-- The maximal smooth subrepresentation in the coinduced representation. -/
@[reducible]
def smoothCoind (s : H →* G) (ρ : Representation k H V) :
    Representation k G (smoothVectors (coind s ρ)).toSubmodule :=
  (smoothVectors (coind s ρ)).toRepresentation

variable {k : Type u} [CommRing k]
variable {V : Type t} [AddCommGroup V] [Module k V]
variable {s : H →* G}

lemma isSmoothVector_IndVMk {ρ : Representation k H V} {v : V} (h_isOpen : IsOpenMap s) (g : G)
    (hv : IsSmoothVector ρ v) :
    IsSmoothVector (ind s ρ) (IndV.mk s ρ g v) := by
  have h_sub :
      ((stabilizer ρ v).map s).map (MulAut.conj g⁻¹) ≤ stabilizer (ind s ρ) (IndV.mk s ρ g v) := by
    simp only [SetLike.le_def, Subgroup.mem_map, mem_stabilizer, forall_exists_index, and_imp]
    intro _ _ _ h_stab rfl h_conj
    rw [← h_conj,MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, ind_map_conj_mk, h_stab]
  have h_open : IsOpen (((stabilizer ρ v).map s).map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
    convert ((isOpenMap_mul_right g).comp (isOpenMap_mul_left g⁻¹)) _ (h_isOpen _ hv)
    ext; simp
  exact Subgroup.isOpen_mono h_sub h_open

lemma isSmooth_openMap_ind (h_isOpen : IsOpenMap s) (ρ : Representation k H V) [h_sm : IsSmooth ρ] :
    IsSmooth (Representation.ind s ρ) := by
  rw [isSmooth_iff]
  intro w
  refine IndV.induction_on w ?_ ?_
  · intro g v
    exact isSmoothVector_IndVMk h_isOpen g (h_sm.smooth v)
  · exact fun _ _ hx hy => isSmoothVector_add hx hy

end representation

namespace SmRep

section res

variable {k : Type u} [Ring k]
variable (s : H →ₜ* G)

/-- Restriction of a smooth representation along `H →ₜ* G`. -/
abbrev res (A : SmRep.{t} k G) :
    SmRep.{t} k H := mk (Rep.res s.1 A.rep)

/-- The map restricting morphisms between smooth representations along `H →ₜ* G`. -/
abbrev resMap {A B : SmRep.{t} k G} (f : A ⟶ B) :
    res s A ⟶ res s B := homMk (Rep.resMap s.1 f.hom)

omit [IsTopologicalGroup G] in
lemma res_eq_of_comp (A : SmRep.{t} k G) :
    (res s A) = of ((A.ρ).comp s.1) := rfl

/-- The restriction functor of pulling back smooth representations along `H →ₜ* G`. -/
abbrev resFunctor : SmRep.{t} k G ⥤ SmRep.{t} k H where
  obj := res s
  map := resMap s

/-- An auxiliary restriction functor. -/
abbrev resFunctorAux :
    SmRep.{t} k G ⥤ Rep.{t} k H := ι ⋙ Rep.resFunctor s.1

/-- The isomorphism between `resFunctor ⋙ ι` and `resFunctorAux`. -/
abbrev resFunctorAuxIso :
    resFunctorAux.{t} s ≅ resFunctor.{t} s ⋙ ι (k := k)  := Iso.refl _

end res

section coind

variable {k : Type u} [CommRing k]

/-- The coinduced functor pushing smooth representations along `H →* G`, obtained by taking smooth
vectors from `Rep.coind`. This is often called the "smooth induction functor" in literature. -/
noncomputable abbrev coindFunctor (s : H →* G) :
    SmRep.{t} k H ⥤ SmRep.{max t v} k G := ι ⋙ Rep.coindFunctor k s ⋙ smVec

/-- The coinduced smooth representations along `H →* G`. -/
noncomputable abbrev coind (s : H →* G) (A : SmRep.{t} k H) :
    SmRep.{max t v} k G := (coindFunctor s).obj A

/-- The coinduced map pushing morphisms between smooth representations along `H →* G`. -/
noncomputable abbrev coindMap (s : H →* G) {A B : SmRep.{t} k H} (f : A ⟶ B) :
    coind s A ⟶ coind s B := (coindFunctor s).map f

lemma coind_eq_of_smoothCoind (s : H →* G) (A : SmRep.{t} k H) :
    coind s A = of (smoothCoind s A.ρ) := rfl

/-- Auxiliary ambient resCoindAdjunction. -/
noncomputable abbrev resCoindAdjunctionAux (s : H →ₜ* G) :
    resFunctorAux s ⊣ Rep.coindFunctor k s.1 ⋙ smVec.{max t v} :=
  (smVecAdjunction).comp (Rep.resCoindAdjunction k s.1)

/-- The adjunction between `resFunctor` and `coindFunctor`. -/
noncomputable def resCoindAdjunction (s : H →ₜ* G) :
    resFunctor s ⊣ coindFunctor.{max v t} s.1 (k := k) :=
  Adjunction.restrictFullyFaithful
    (adj := resCoindAdjunctionAux s)
    (hiC := Functor.FullyFaithful.id (SmRep k G))
    (hiD := (smoothProperty k H).fullyFaithfulι)
    (comm1 := (Functor.leftUnitor (resFunctorAux s)).trans (resFunctorAuxIso s))
    (comm2 := (Functor.rightUnitor (coindFunctor s.1)).symm)

end coind

section ind

variable {k : Type u} [CommRing k]
variable (s : H →* G) (isOpen : IsOpenMap s)

/-- The induced representation along an open map `H →* G`. -/
noncomputable abbrev ind (A : SmRep.{t} k H) :
    SmRep.{max u v t} k G := ⟨Rep.ind s A.rep, isSmooth_openMap_ind isOpen A.ρ⟩

/-- The induced map pushing morphisms between smooth representations along an open map `H →* G`. -/
noncomputable abbrev indMap {A B : SmRep.{t} k H} (f : A ⟶ B) :
    ind s isOpen A  ⟶ ind s isOpen B
  := homMk (Rep.indMap s f.hom)

/-- The induced functor pushing smooth representations along an open map `H →* G`. This is often
called the "compact induction functor" in literature when it specializes to open compact subgorups.
-/
noncomputable abbrev indFunctor : SmRep.{t} k H ⥤ SmRep.{max u v t} k G where
  obj A := ind s isOpen A
  map f := homMk (Rep.indMap s f.hom)

lemma ind_eq_of_ind (A : SmRep.{t} k H) :
    ind s isOpen A = of (Representation.ind s A.ρ) (h := isSmooth_openMap_ind isOpen A.ρ) := rfl

/-- An auxiliary induced functor. -/
noncomputable abbrev indFunctorAux :
    SmRep.{t} k H ⥤ Rep.{max u v t} k G := ι ⋙ Rep.indFunctor k s

/-- The isomorphism between `indFunctor` and `indFunctorAux`. -/
noncomputable abbrev indFunctorAuxIso :
    indFunctorAux.{t} s ≅ indFunctor.{t} s isOpen ⋙ ι (k := k) := Iso.refl _

/-- The adjunction between `indFunctor` and `resFunctor`. -/
noncomputable def indResAdjunction (s : H →ₜ* G) {isOpen : IsOpenMap s.1} :
    indFunctor.{max u v t} s.1 isOpen (k := k) ⊣ resFunctor.{max u v t} s :=
  Adjunction.restrictFullyFaithful
    (adj := Rep.indResAdjunction.{t} k s.1)
    (hiC := (smoothProperty k H).fullyFaithfulι)
    (hiD := (smoothProperty k G).fullyFaithfulι)
    (comm1 := indFunctorAuxIso s.1 isOpen)
    (comm2 := resFunctorAuxIso s)

end ind

end SmRep

end Representation.Smooth
