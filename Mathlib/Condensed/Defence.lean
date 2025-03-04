import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Condensed.AB
import Mathlib.Condensed.Discrete.Characterization
import Mathlib.Condensed.Solid
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Category.Profinite.Nobeling
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.NoetherianSpace
-- import Mathlib.Algebra.Category.ModuleCat.Products

noncomputable section

universe u

open Condensed CategoryTheory

namespace CondensedAb

def of (X : Type u) [AddCommGroup X] : CondensedAb :=
  (Condensed.discrete _).obj (ModuleCat.of (ULift.{u+1} ℤ) (ULift.{u+1} X))

abbrev IsSolid (X : CondensedAb.{u}) : Prop := CondensedMod.IsSolid (ULift ℤ) X

set_option quotPrecheck false
notation3 "ℤ[" S "]" => (profiniteFree (ULift ℤ)).obj S
notation3 "ℤ[" S "]◾" => (profiniteSolid (ULift ℤ)).obj S

def solidification (S : Profinite.{u}) : ℤ[S] ⟶ ℤ[S]◾ :=
  (profiniteSolidification (ULift ℤ)).app S

notation3 "ε" S => solidification S

notation3 "(*)" => Opposite.op (CompHaus.of PUnit)


variable (S : Profinite.{u})
#check ℤ[S]
#check ℤ[S]◾
#check ε S

open scoped MonoidalClosed.FunctorCategory

instance : MonoidalCategory (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat (ULift.{u+1} ℤ))) :=
  Sheaf.monoidalCategory _ _

instance : MonoidalCategory CondensedAb.{u} := Sheaf.monoidalCategory _ _

instance : MonoidalClosed (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat (ULift.{u+1} ℤ))) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalClosed CondensedAb.{u} := inferInstanceAs (MonoidalClosed (Sheaf _ _))

instance : ((coherentTopology CompHaus.{u}).W (A := ModuleCat (ULift.{u+1} ℤ))).IsMonoidal :=
  inferInstance

instance : SymmetricCategory (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat (ULift.{u+1} ℤ))) :=
  sorry -- We need to generalize the API for monoidal localizations to the symmetric case

instance : SymmetricCategory CondensedAb.{u} := inferInstanceAs (SymmetricCategory (Sheaf _ _))

end CondensedAb

end

/-!

-- section General

-- variable (R : Type*) [Ring R] (M : ModuleCat R) [Module.Free R M]

-- open Classical in
-- def freeIsoCoprod :
--     M ≅ ∐ (fun (i : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R) :=
--   (Module.Free.chooseBasis R M).repr.toModuleIso ≪≫
--     (finsuppLequivDFinsupp (ModuleCat.of R R)).toModuleIso ≪≫
--       (ModuleCat.coprodIsoDirectSum
--         (fun (i : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R)).symm

-- -- def ModuleCat.freeCofan :
-- --     Cofan (fun (i : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R) := by
-- --   refine Cofan.mk
-- --     M
-- --     (ModuleCat.ofHom ((Module.Free.chooseBasis R M).repr.symm : _ →ₗ[R] _))


-- end General
-/
