import Mathlib

namespace complex

open CategoryTheory

structure Complex where
  X : ℤ → AddCommGrp
  d : ∀ i, X i ⟶ X (i+1)
  d_comp : ∀ i, d i ≫ d (i+1) = 0

example (C : Complex) (i : ℤ) : C.d i ≫ C.d (i+1) = 0 := by
  exact C.d_comp _

-- example (C : Complex) (i : ℤ) : C.d (i+1) ≫ C.d (i+2) = 0 := by
--   exact C.d_comp _

#check HomologicalComplex

#check CochainComplex

#check HomologicalComplex.homology

end complex

section sheaf_coho

open AlgebraicGeometry CategoryTheory Limits

variable {A : Type*} [Category A] {X : Scheme}

instance : HasFiniteLimits (Scheme.OpenCover X) := sorry

/-- This is an open in the Zariski topology -/
structure OpenOver (X : Scheme) where
  dom : Scheme
  f : dom ⟶ X
  isOpen : IsOpenImmersion f := by infer_instance

/-- `f.f` is the inclusion of the open set, that is an open immersion -/
instance (f : OpenOver X) : IsOpenImmersion f.f := f.isOpen

/-- Open sets form a category -/
instance : Category (OpenOver X) :=
  InducedCategory.category fun f => Over.mk f.f

/-- There is a functor that forgets we are talking about schemes -/
def OpenOver.toOpens (X : Scheme) : OpenOver X ⥤ TopologicalSpace.Opens X where
  obj f := f.f.opensRange
  map e := LE.le.hom <| sorry

/-- If `F` is a presheaf on `X` we also have a presheaf on `OpenOver X` -/
def TopCat.Presheaf.openImmersionFunctor (F : TopCat.Presheaf A X) :
    (OpenOver X)ᵒᵖ ⥤ A :=
  (OpenOver.toOpens X).op ⋙ F

/-- If `U` is an open cover of `X` indexed by a set `J` and `j` is an element of `J`, we get
an open set associated to `j` -/
def AlgebraicGeometry.Scheme.OpenCover.toOpenOver (U : Scheme.OpenCover X) (j : U.J) :
    OpenOver X where
  f := U.map j

/-- A morphism of open covers induces a morphisms between open sets. -/
def Scheme.OpenCover.mapToOpenOver {U V : Scheme.OpenCover X} (e : U ⟶ V) (j : U.J) :
    U.toOpenOver j ⟶ V.toOpenOver (e.idx j) where
  left := e.app _
  right := 𝟙 _
  w := e.w _

/-- If `F` is a presheaf on `X` we also have a presheaf on `Scheme.OpenCover X` -/
noncomputable
def Scheme.OpenCover.inducedFunctor [HasProducts A] (F : TopCat.Presheaf A X) :
    (Scheme.OpenCover X)ᵒᵖ ⥤ A where
  obj U := piObj fun j : U.unop.J => F.obj <| .op <|
    (OpenOver.toOpens X).obj <| U.unop.toOpenOver j
  map := fun {U V} f => Pi.lift fun j =>
    Pi.π _ (f.unop.idx j) ≫ F.map (Quiver.Hom.op <| (OpenOver.toOpens X).map <|
      Scheme.OpenCover.mapToOpenOver f.unop _)
  map_id := sorry
  map_comp := sorry

/-- The Cech complex of a presheaf on a scheme `X` with respect to an open cover `U` -/
noncomputable
def Scheme.OpenCover.cechComplex [HasProducts A] [Preadditive A]
    (U : Scheme.OpenCover X) (F : TopCat.Presheaf A X) : CochainComplex A ℕ :=
  let e : U ⟶ ⊤_ _ := terminal.from U
  let e := Arrow.mk e
  let e := e.cechNerve
  let e : CosimplicialObject _ := e.rightOp ⋙ Scheme.OpenCover.inducedFunctor F
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj e

end sheaf_coho
