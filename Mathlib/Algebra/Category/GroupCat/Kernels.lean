import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

open AddMonoidHom CategoryTheory Limits QuotientAddGroup WalkingParallelPair

universe u

namespace AddCommGroupCat

variable {G H : AddCommGroupCat.{u}} (f : G ⟶ H)

instance : HasZeroMorphisms AddCommGroupCat := HasZeroMorphisms.mk

instance : AddSubmonoidClass (AddSubgroup G) ((parallelPair f 0).obj WalkingParallelPair.zero) where
  add_mem := fun s {_ _} => AddSubgroup.add_mem s
  zero_mem := AddSubgroup.zero_mem

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := of f.ker) f.ker.subtype <| ext fun x => Subtype.casesOn x fun _ hx => hx

/-- The kernel of a group homomorphism is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit <| kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => codRestrict (Fork.ι s) _ <| fun c => (mem_ker _).2 <|
      FunLike.congr_fun (KernelFork.condition s) c)
    (fun _ => rfl)
    (fun _ _ h => ext $ fun x => Subtype.ext_iff_val.2 $ FunLike.congr_fun h x)

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := of $ H ⧸ f.range) (mk' f.range) <| ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

theorem range_le_ker_iff {I : AddCommGroupCat.{u}} {f : G →+ H} {g : H →+ I} :
    f.range ≤ g.ker ↔ g.comp f = 0 := by
    constructor
    · intro h
      aesop_cat
    · intro h x hx
      cases' hx with x' hx
      have := FunLike.congr_fun h x'
      simp at this
      rw [hx] at this
      exact this

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit <| cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s => lift f.range (Cofork.π s) <| range_le_ker_iff.2 <| CokernelCofork.condition s)
    (fun _ => rfl)
    (fun _ _ h => by
      ext x
      simp
      rw [QuotientAddGroup.lift]
      sorry)

end AddCommGroupCat
