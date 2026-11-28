import Mathlib.Tactic.Simps.Generalized
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Yoneda

/-! # Tests for `simps!!`: CW complexes and chosen corepresentations -/

/-! ### CW complexes -/

namespace SimpsGenCW

open Topology Metric Set RelCWComplex

variable {X : Type*} [TopologicalSpace X] {C D : Set X}

@[simps!! -isSimp, instance_reducible]
noncomputable def subcx [T2Space X] [RelCWComplex C D] (E : Subcomplex C) : RelCWComplex E D :=
  RelCWComplex.Subcomplex.instRelCWComplex E

section
variable [T2Space X] [RelCWComplex C D] (E : Subcomplex C) (n : ℕ) (i : E.I n)

-- the right-hand sides are cells of `C` (by `RelCWComplex.Subcomplex.openCell_eq`, …), not their
-- unfolding `map n i '' ball 0 1`
example : @openCell _ _ (E : Set X) D (subcx E) n i = openCell (C := C) n i :=
  subcx_openCell E n i
example : @closedCell _ _ (E : Set X) D (subcx E) n i = closedCell (C := C) n i :=
  subcx_closedCell E n i
example : @cellFrontier _ _ (E : Set X) D (subcx E) n i = cellFrontier (C := C) n i :=
  subcx_cellFrontier E n i
end

open Lean Elab Command in
-- check the statements syntactically, not up to unfolding `openCell`
run_cmd liftTermElabM do
  for (n, c) in [(``subcx_openCell, ``openCell), (``subcx_closedCell, ``closedCell),
      (``subcx_cellFrontier, ``cellFrontier)] do
    let some (_, _, rhs) := (← Meta.forallTelescope (← getConstInfo n).type fun _ b => pure b).eq?
      | throwError "{n} is not an equation"
    unless rhs.isAppOf c do throwError "the right-hand side of {n} is not an application of {c}"


end SimpsGenCW

/-! ### Chosen corepresentations -/

namespace SimpsGenCorepr

open CategoryTheory

variable {C : Type*} [Category* C]

/-- A chosen corepresentation of a functor. -/
class ChosenCorepr (F : C ⥤ Type*) where
  /-- The corepresenting object. -/
  obj : C
  /-- The corepresentation. -/
  corepBy : F.CorepresentableBy obj

/-- The corepresenting object. -/
abbrev coreprObj (F : C ⥤ Type*) [c : ChosenCorepr F] : C := c.obj

/-- See `coreprObj`. -/
def ChosenCorepr.Simps.coreprObj (F : C ⥤ Type*) [c : ChosenCorepr F] : C :=
  SimpsGenCorepr.coreprObj F

initialize_simps_projections ChosenCorepr (obj → coreprObj)

/-- The universal element of the chosen corepresentation. -/
@[simps_proj]
abbrev coreprElem (F : C ⥤ Type*) [c : ChosenCorepr F] : F.obj (coreprObj F) :=
  c.corepBy.homEquiv (𝟙 _)

@[simps!! -isSimp]
instance instTop : ChosenCorepr (forget TopCat) where
  obj := TopCat.of PUnit
  corepBy.homEquiv := { toFun f := f ⟨⟩, invFun y := TopCat.ofHom <| .const _ y }

-- as with `simps!`, the instance name is dropped, and `obj` is unfolded through `TopCat.of`
example : ↑(coreprObj (forget TopCat.{0})) = PUnit := coreprObj_carrier
example : coreprElem (forget TopCat.{0}) = PUnit.unit := coreprElem_def

end SimpsGenCorepr
