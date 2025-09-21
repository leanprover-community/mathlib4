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

/-- An extension is central if the kernel of projection lies in the center. -/
def IsCentral : Prop :=
  S.proj.ker ≤ LieAlgebra.center R S.L

lemma IsCentral_iff : S.IsCentral ↔ LieModule.IsTrivial S.L S.proj.ker :=
  (LieModule.trivial_iff_le_maximal_trivial R S.L S.L S.proj.ker).symm

lemma bracket_eq_zero_of_isCentral (h : S.IsCentral) (x y : S.L) (hy : y ∈ S.proj.ker) :
    ⁅x, y⁆ = 0 :=
  h hy x

lemma bracket_eq_of_sub_mem_kernel (h : S.IsCentral) (x y z : S.L) (hyz : y - z ∈ S.proj.ker) :
    ⁅x, y⁆ = ⁅x, z⁆ := by
  rw [← sub_eq_zero, ← lie_sub]
  exact S.bracket_eq_zero_of_isCentral h x (y - z) hyz

@[simp]
lemma comp_eq_id {s : M →ₗ[R] S.L} (hs : S.proj.toLinearMap ∘ₗ s = LinearMap.id)
    (x : M) :
    S.proj (s x) = x := by
  simp [show S.proj (s x) = S.proj.toLinearMap.comp s x by rfl, hs]

lemma bracket_sub_bracket_mem_kernel {s : M →ₗ[R] S.L} (hs : S.proj.toLinearMap ∘ₗ s = LinearMap.id)
    (x y : M) :
    ⁅s x, s y⁆ - s ⁅x, y⁆ ∈ LinearMap.ker S.proj.toLinearMap := by
  simp [hs]

section ofTwoCocycle

variable [AddCommGroup V] [Module R V] (c : twoCocycle R L V)

lemma isCentral_ofTwoCocycle :
    (ofTwoCocycle c).IsCentral := by
  rw [IsCentral_iff, LieModule.trivial_iff_le_maximal_trivial]
  intro x hx
  simp_all only [LieHom.mem_ker, LieModule.mem_maxTrivSubmodule, Extension.ofTwoCocycle]
  intro y
  simp_all only [IsExtension.extension_L, IsExtension.extension_instLieRing,
    IsExtension.extension_instLieAlgebra, IsExtension.extension_proj, bracket_ofTwoCocycleAlg]
  rw [show x = ofProd c (x.carrier.1, x.carrier.2) by rfl, twoCocycleProj] at hx
  simp [show x.carrier.1 = 0 by exact hx, Prod.mk_zero_zero]

/-- Construct a cocycle from a module-split central extension. -/
def twoCocycleOfSplitting (E : Extension R N M) (hE : E.IsCentral) {s : M →ₗ[R] E.L}
    (hs : E.proj.toLinearMap ∘ₗ s = LinearMap.id) (p : E.L →ₗ[R] N) :
    twoCocycle R M N where
  val := {
    toBilin := {
      toFun a := {
          toFun b := p ⁅s a, s b⁆
          map_add' _ _ := by simp
          map_smul' _ _ := by simp }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    alt _ := by simp }
  property := by
    ext x y z
    simp only [d₂₃_apply_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
      Pi.ofNat_apply]
    have := lie_jacobi (s x) (s y) (s z)
    rw [E.bracket_eq_of_sub_mem_kernel hE (s x) ⁅s y, s z⁆ (s ⁅y, z⁆),
      E.bracket_eq_of_sub_mem_kernel hE (s y) ⁅s z, s x⁆ (s ⁅z, x⁆),
      E.bracket_eq_of_sub_mem_kernel hE (s z) ⁅s x, s y⁆ (s ⁅x, y⁆)] at this
    · simp [← map_add, this]
    · exact E.bracket_sub_bracket_mem_kernel hs x y
    · exact E.bracket_sub_bracket_mem_kernel hs z x
    · exact E.bracket_sub_bracket_mem_kernel hs y z

-- shearing a splitting by a translation yields a difference of coboundary?
-- make a correspondence with cohomology!!

end ofTwoCocycle

/-!
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
-/

end Extension

end LieAlgebra
