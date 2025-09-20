/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Extension

/-!
# Central extensions of Lie algebras

Given a Lie algebra `L` over a commutative ring `R`, and an abelian Lie algebra `C` over `R`, a
central extension of `L` by `C` is a Lie algebra `M` over `R` equipped with a surjective
homomorphism `f : M →ₗ[R] L` and an `R`-isomorphism from `C` to the kernel of `f`. A central
extension is `R`-split if the structure maps on `M` induce an `R`-module decomposition into a direct
sum of `L` and `C`. In this case, we can describe `M` as a direct sum with bracket given by a
2-cocycle. Two `R`-split central extensions are isomorphic if and only if the 2-cocycles differ by
a coboundary.

A projective `R`-linear representation of a Lie algebra `L` over `R` is an `R`-module `M` with a
linear map `ρ : L → End R M` such that `ρ [x,y] = c(x,y) ρ x ρ y` or something.

## Main definitions (Todo for now)

* Central extension
* `R`-split
* split
* projective representations

## Main results

* cocycle description
* cohomological criterion for triviality

## References

* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- extensions are chapter 1 section 7, cohomology is Exercises section 3 (p116, near end of book)


## Tags

lie ring, lie algebra, central extension
-/

suppress_compilation

namespace LieAlgebra.Extension

variable {R L M N V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M] (S : Extension R N M)

instance : LieRing S.L := S.instLieRing
instance : LieAlgebra R S.L := S.instLieAlgebra

/-- An extension is central if the image of the left map commutes with the whole Lie algebra. -/
def IsCentral : Prop :=
  LieModule.IsTrivial S.L S.proj.ker

lemma bracket_eq_zero_of_isCentral (h : S.IsCentral) (x y : S.L) (hy : y ∈ S.proj.ker) :
    ⁅x, y⁆ = 0 := by
  have _ : LieModule.IsTrivial S.L S.proj.ker := h
  have hxyhy := LieModule.IsTrivial.trivial x (⟨y, hy⟩ : S.proj.ker)
  have : ⁅x, (⟨y, hy⟩: S.proj.ker)⁆ = ⁅x, y⁆ := rfl
  rw [← this]
  exact ZeroMemClass.coe_eq_zero.mpr hxyhy

lemma bracket_eq_of_sub_mem_kernel (h : S.IsCentral) (x y z : S.L) (hyz : y - z ∈ S.proj.ker) :
    ⁅x, y⁆ = ⁅x, z⁆ := by
  rw [← sub_eq_zero, ← lie_sub]
  exact S.bracket_eq_zero_of_isCentral h x (y - z) hyz

section TwoCocycleTriv

variable [AddCommGroup V] [Module R V] (c : twoCocycleTriv R L V)

lemma isCentral_ofTwoCocycleTriv :
    (ofTwoCocycleTriv c).IsCentral := by
  dsimp only [IsCentral]
  rw [LieModule.trivial_iff_le_maximal_trivial]
  intro x hx
  simp_all only [LieHom.mem_ker, LieModule.mem_maxTrivSubmodule, Extension.ofTwoCocycleTriv]
  intro y
  simp_all only [IsExtension.extension_L, IsExtension.extension_instLieRing,
    IsExtension.extension_instLieAlgebra, IsExtension.extension_proj, bracket_ofTwoCocycleTriv]
  rw [show x = (x.1, x.2) by rfl, twoCocycleTrivProj] at hx
  simp [show x.1 = 0 by exact hx, Prod.mk_zero_zero]

end TwoCocycleTriv

/-- A Lie algebra homomorphism is a central extension if it is surjective and the kernel lies in the
center. The center condition is equivalent to the kernel being a trivial module for the adjoint
adjoint action. -/
class IsCentralExtension (f : M →ₗ⁅R⁆ L) : Prop where
  protected surjective : Function.Surjective f
  protected central : LieModule.IsTrivial M f.ker

lemma surjective_of_central_extension (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] :
    Function.Surjective f := IsCentralExtension.surjective

lemma central_of_central_extension (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] :
    LieModule.IsTrivial M f.ker := IsCentralExtension.central

/-!
I think module-splitting should not take Lie-theoretic information, and only be a linear-algebraic
object. `Algebra.Module.Projective` doesn't define splittings - only uses conditions like
`s.comp i = LinearMap.id`. Perhaps I should use the same.

/-- A module-splitting is a surjective Lie algebra homomorphism equipped with a linear isomorphism
from the source to the direct sum of the kernel and the target. This should be revised to the usual
notion of splitting of a surjection. -/
structure ModuleSplitting (f : M →ₗ⁅R⁆ L) where
  protected surj : Prop := Function.Surjective f
  /-- The section on the right. -/
  protected sectRight : L →ₗ[R] M
  protected lInvRight : Function.LeftInverse f sectRight
  protected sectLeft : M →ₗ[R] f.ker
  protected rInvLeft : Function.RightInverse (LinearMap.ker f.toLinearMap).subtype sectLeft

lemma bracket_sub_bracket_mem_kernel (f : M →ₗ⁅R⁆ L) (a : ModuleSplitting f) (x y : L) :
    ⁅a.sectRight x, a.sectRight y⁆ - a.sectRight ⁅x, y⁆ ∈ LinearMap.ker f.toLinearMap := by
  simp [a.lInvRight x, a.lInvRight y, a.lInvRight ⁅x,y⁆]

lemma bracket_bracket_section_eq (f : M →ₗ⁅R⁆ L) (a : ModuleSplitting f) (x y : L) (z : M) :
    ⁅z, ⁅a.sectRight x, a.sectRight y⁆⁆ = ⁅z, a.sectRight ⁅x, y⁆⁆ := by
  have := S.bracket_eq_of_sub_mem_kernel
  sorry

-- bracket with element of kernel is zero, when extension is central!
-- bracket with `⁅a.sectRight x, a.sectRight y⁆` equals bracket with `a.sectRight ⁅x, y⁆`.

/-- Make a 2-cocycle from a module-split central extension. -/
def cocycle_of_splitting (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] (a : ModuleSplitting f) :
    twoCocycle R L f.ker where
  val : twoCochain R L f.ker := {
    toBilin := {
      toFun l₁ := {
          toFun := fun l₂ ↦ a.sectLeft ⁅a.sectRight l₁, a.sectRight l₂⁆
          map_add' x y := by ext; simp
          map_smul' := by simp }
      map_add' x y := by ext; simp
      map_smul' r x := by ext; simp }
      --(((bracketLinear R M M).compl₂ (a.sectRight)).compl₂ a.sectLeft.comp).comp a.sectRight
      -- [(a,b),(c,d)] = (cocycle(b,d),[b, d]) : use a.sectLeft.comp
    alt x := by ext; simp }
  property := by
    ext x y z
    simp only [d₂₃_apply_apply, LinearMap.coe_mk, AddHom.coe_mk, LieSubmodule.coe_add,
      LinearMap.zero_apply, Pi.zero_apply, ZeroMemClass.coe_zero]
    have := lie_jacobi (a.sectRight x) (a.sectRight y) (a.sectRight z)


-- /--Make a module-split central extension from a 2-cocycle (with trivial coefficients)-/
--def splitting_of_cocycle (f : 2-cocycle L V) : L × V →ₗ⁅R⁆ L where


def twoCocycleTrivOfCentralExtension [LieRing M] [LieAlgebra R M] (E : Extension R M L)
    (s : L →ₗ[R] E.L) (p : E.L →ₗ[R] M) (h : Function.LeftInverse E.proj s) :
    twoCocycleTriv R L M where
  toFun := {
    toFun l₁ := {
        toFun l₂ := p ⁅s l₁, s l₂⁆
        map_add' x y := by simp
        map_smul' r x := by simp }
    map_add' x y := by ext; simp
    map_smul' r x := by ext; simp
  }
  map_eq_zero_of_eq' x := by simp
  cocycle x y z := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ← map_add]
    have hproj : ⁅s x, s ⁅y, z⁆⁆ - (⁅s ⁅x, y⁆, s z⁆ + ⁅s y, s ⁅x, z⁆⁆) ∈
        LinearMap.ker E.proj.toLinearMap := by
      have hlie := LieRing.leibniz_lie x y z
      rw [← h ⁅x, y⁆, ← h ⁅y, z⁆, ← h ⁅x, z⁆] at hlie
      nth_rw 1 [← h x] at hlie
      nth_rw 2 [← h z] at hlie
      nth_rw 3 [← h y] at hlie
      rw [← LieHom.map_lie, ← LieHom.map_lie, ← LieHom.map_lie, ← LieHom.map_add] at hlie
      exact LinearMap.sub_mem_ker_iff.mpr hlie
    have : E.proj ⁅s x, s ⁅y, z⁆⁆ = E.proj (⁅s ⁅x, y⁆, s z⁆ + ⁅s y, s ⁅x, z⁆⁆) := by
      rwa [LinearMap.sub_mem_ker_iff] at hproj



    sorry
-/
end Extension

end LieAlgebra
