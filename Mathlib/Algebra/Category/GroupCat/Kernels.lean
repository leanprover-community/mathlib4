/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn
-/
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The concrete (co)kernels in the category of abelian groups are categorical (co)kernels.
-/

namespace AddCommGroupCat

open AddMonoidHom CategoryTheory Limits QuotientAddGroup

universe u

variable {G H : AddCommGroupCat.{u}} (f : G ⟶ H)

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := of f.ker) f.ker.subtype <| ext fun x => x.casesOn fun _ hx => hx

/-- The kernel of a group homomorphism is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit <| kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => (by exact Fork.ι s : _ →+ G).codRestrict _ fun c => f.mem_ker.mpr <|
      by exact DFunLike.congr_fun s.condition c)
    (fun _ => by rfl)
    (fun _ _ h => ext fun x => Subtype.ext_iff_val.mpr <| by exact DFunLike.congr_fun h x)

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := of <| H ⧸ f.range) (mk' f.range) <| ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit <| cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s => lift _ _ <| (range_le_ker_iff _ _).mpr <| CokernelCofork.condition s)
    (fun _ => rfl)
    (fun _ _ h => have : Epi (cokernelCocone f).π := (epi_iff_surjective _).mpr <| mk'_surjective _
      (cancel_epi _).mp <| by simpa only [parallelPair_obj_one] using h)

end AddCommGroupCat
