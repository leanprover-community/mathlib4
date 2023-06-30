import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

open CategoryTheory Limits QuotientAddGroup WalkingParallelPair

universe u

namespace AddCommGroupCat

variable {G H : AddCommGroupCat.{u}} (f : G ⟶ H)

-- TODO: relocate theorem
theorem range_le_ker_iff {G H I : AddCommGroupCat.{u}} {f : G →+ H} {g : H →+ I} :
    f.range ≤ g.ker ↔ g.comp f = 0 :=
  ⟨fun h => AddMonoidHom.ext fun x => h ⟨x, rfl⟩,
    by rintro h _ ⟨x', rfl⟩; exact FunLike.congr_fun h x'⟩

-- TODO: relocate theorem
theorem ker_le_range_iff {G H I : AddCommGroupCat.{u}} {f : G →+ H} {g : H →+ I} :
   g.ker ≤ f.range ↔ (QuotientAddGroup.mk' f.range).comp g.ker.subtype = 0 :=
  ⟨fun h => AddMonoidHom.ext fun ⟨_, hx⟩ => (eq_zero_iff _).mpr <| h hx,
    fun h x hx => (eq_zero_iff _).mp <| by exact FunLike.congr_fun h ⟨x, hx⟩⟩

-- TODO: relocate instance
instance : HasZeroMorphisms AddCommGroupCat := HasZeroMorphisms.mk

-- TODO: relocate instance
instance : AddSubmonoidClass (AddSubgroup G) ((parallelPair f 0).obj WalkingParallelPair.zero) where
  add_mem := fun s {_ _} => AddSubgroup.add_mem s
  zero_mem := AddSubgroup.zero_mem

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := of f.ker) f.ker.subtype <| ext fun x => Subtype.casesOn x fun _ hx => hx

/-- The kernel of a group homomorphism is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit <| kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => AddMonoidHom.codRestrict (Fork.ι s) _ <| fun c => (AddMonoidHom.mem_ker _).2 <|
      FunLike.congr_fun (KernelFork.condition s) c)
    (fun _ => rfl)
    (fun _ _ h => ext $ fun x => Subtype.ext_iff_val.2 $ FunLike.congr_fun h x)

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := of $ H ⧸ f.range) (mk' f.range) <| ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

instance : Epi <| Cofork.π <| cokernelCocone f :=
  (epi_iff_surjective _).mpr <| mk'_surjective f.range

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit <| cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s => lift f.range (Cofork.π s) <| range_le_ker_iff.2 <| CokernelCofork.condition s)
    (fun _ => rfl)
    (fun s m h => (cancel_epi _).1 <| by simpa only [parallelPair_obj_one])

end AddCommGroupCat
