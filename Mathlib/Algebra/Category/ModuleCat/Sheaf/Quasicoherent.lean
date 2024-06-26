/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Quasicoherent sheaves

A sheaf of modules is quasi-coherent if it admits locally a presentation as the
cokernel of a morphism between coproducts of copies of the sheaf of rings.
When these coproducts are finite, we say that the sheaf is of finite presentation.

## References

* https://stacks.math.columbia.edu/tag/01BD

-/

universe u v' u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}


variable {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

variable (M : SheafOfModules.{u} R)

section

variable [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- A global presentation of a sheaf of modules `M` consists of a family `generators.s`
of sections `s` which generate `M`, and a family of sections which generate
the kernel of the morphism `generators.π : free (generators.I) ⟶ M`. -/
structure Presentation where
  /-- generators -/
  generators : M.GeneratingSections
  /-- relations -/
  relations : (kernel generators.π).GeneratingSections

end


variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrp.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrp.{u}]

/-- This structure contains the data of a family of objects `X i` which cover
the terminal object, and of a presentation of `M.over (X i)` for all `i`. -/
structure QuasicoherentData where
  /-- the index type of the covering -/
  I : Type u'
  /-- a family of objects which cover the terminal object -/
  X : I → C
  coversTop : J.CoversTop X
  /-- a presentation of the sheaf of modules `M.over (X i)` for any `i : I` -/
  presentation (i : I) : (M.over (X i)).Presentation

namespace QuasicoherentData

variable {M}

/-- If `M` is quasicoherent, it is locally generated by sections. -/
@[simps]
def localGeneratorsData (q : M.QuasicoherentData) : M.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

end QuasicoherentData

/-- A sheaf of modules is quasi-coherent if it is locally the cokernel of a
morphism between coproducts of copies of the sheaf of rings. -/
class IsQuasicoherent : Prop where
  nonempty_quasicoherentData : Nonempty M.QuasicoherentData

/-- A sheaf of modules is quasi-coherent if it is locally the cokernel of a
morphism between coproducts of finitely many copies of the sheaf of rings.. -/
class IsFinitePresentation : Prop where
  exists_quasicoherentData :
    ∃ (σ : M.QuasicoherentData), ∀ (i : σ.I), (Finite (σ.presentation i).generators.I ∧
      Finite (σ.presentation i).relations.I)

section

variable [h : M.IsFinitePresentation]

/-- A choice of local presentations when `M` is a sheaf of modules of finite presentation. -/
noncomputable def quasicoherentDataOfIsFinitePresentation : M.QuasicoherentData :=
  h.exists_quasicoherentData.choose

-- the next two instances are terribly slow
instance (i : M.quasicoherentDataOfIsFinitePresentation.I) :
    Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).generators.I :=
  (h.exists_quasicoherentData.choose_spec i).1

instance (i : M.quasicoherentDataOfIsFinitePresentation.I) :
    Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
  (h.exists_quasicoherentData.choose_spec i).2

end

instance [M.IsFinitePresentation] : M.IsFiniteType where
  exists_localGeneratorsData :=
    ⟨M.quasicoherentDataOfIsFinitePresentation.localGeneratorsData,
      by intro; dsimp; infer_instance⟩

end SheafOfModules
