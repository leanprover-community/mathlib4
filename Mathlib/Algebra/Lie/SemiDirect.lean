/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Extension

/-!
# Semi-direct products

This file defines the semi-direct sum of Lie algebras. These are the infinitesimal counterpart of
semidirect products of (Lie) groups. Given two Lie algebras `H` and `G` over `R` as well as a Lie
algebra homomorphism  `ψ : G → LieDerivation  R H H`, the underlying set of the semidirect sum is
`H × G`, however the bracket is twisted by `ψ`. In this file we show that `SemiDirectSum H G ψ` is
itself a Lie algebra and that it fits into an exact sequence `H → (SemiDirectSum H G ψ) → G`, i.e.
forms an extension of `G`.


## References

* https://en.wikipedia.org/wiki/Lie_algebra_extension#By_semidirect_sum

-/


@[expose] public section

namespace LieAlgebra

/--
The semi-direct sum of two Lie algebras `H` and `G` over `R`, relative to A Lie algebra homomorphism
`ψ: G → Liederivation R H H `. As a set it just `H × G`, however the Lie bracket is twisted by `ψ`.
-/
@[nolint unusedArguments]
structure SemiDirectSum {R : Type*} [CommRing R] (H : Type*) [LieRing H] [LieAlgebra R H]
    (G : Type*) [LieRing G] [LieAlgebra R G] (_ : G →ₗ⁅R⁆ LieDerivation R H H) where
  left : H
  right : G

@[inherit_doc]
notation:35 H " ⋊⁅" ψ:35 "⁆ " G:35 => SemiDirectSum H G ψ


namespace SemiDirectSum

variable {R : Type*} [CommRing R]
variable {G : Type*} [LieRing G] [LieAlgebra R G]
variable {H : Type*} [LieRing H] [LieAlgebra R H]
variable (ψ : G →ₗ⁅R⁆ (LieDerivation R H H))

variable {ψ} in
/-- As raw types, the semidirect product is just a product. -/
def toProd : H ⋊⁅ψ⁆ G ≃ H × G where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl


instance : AddCommGroup (H ⋊⁅ψ⁆ G) := toProd.addCommGroup

@[simp] lemma toProd_zero : (0 : H ⋊⁅ψ⁆ G).toProd = 0 := rfl
@[simp] lemma toProd_add (x y : H ⋊⁅ψ⁆ G) : (x + y).toProd = x.toProd + y.toProd := rfl
@[simp] lemma toProd_sub (x y : H ⋊⁅ψ⁆ G) : (x - y).toProd = x.toProd - y.toProd := rfl
@[simp] lemma toProd_neg (x : H ⋊⁅ψ⁆ G) : (-x).toProd = -x.toProd := rfl

instance : Module R (H ⋊⁅ψ⁆ G) := by
  unfold SemiDirectSum
  infer_instance


instance : Bracket (H ⋊⁅ψ⁆ G) (H ⋊⁅ψ⁆ G) where
  bracket x y := (⁅x.1, y.1⁆ + (ψ x.2) y.1 - (ψ y.2) x.1, ⁅x.2, y.2⁆)


instance : LieRing (H ⋊⁅ψ⁆ G) where
  add_lie _ _ _ := by
    unfold SemiDirectSum
    simp [Bracket.bracket]
    grind
  lie_add _ _ _:= by
    unfold SemiDirectSum
    simp [Bracket.bracket]
    grind
  lie_self _ := by
    unfold SemiDirectSum
    simp [Bracket.bracket]
  leibniz_lie x y z:= by
    unfold SemiDirectSum
    simp only [Bracket.bracket, lie_sub, lie_add, map_sub, map_add, LieDerivation.apply_lie_eq_sub,
      LieHom.map_lie, LieDerivation.coeFn_coe, Module.End.smul_def, LieDerivation.mk_coe,
      LinearMap.coe_mk, AddHom.coe_mk, sub_lie, add_lie, lie_lie, Prod.mk_add_mk, sub_add_cancel,
      Prod.mk.injEq, and_true]
    apply sub_eq_zero.mp
    abel_nf
    rw [←lie_skew]
    abel_nf
    rw [←lie_skew]
    abel_nf


instance : LieAlgebra R (H ⋊⁅ψ⁆ G) where
  lie_smul r x y := by
    unfold SemiDirectSum
    simp only [Bracket.bracket, Prod.smul_fst, lie_smul, map_smul, Prod.smul_snd,
      LieDerivation.coe_smul, Pi.smul_apply, Prod.smul_mk, Prod.mk.injEq, and_true]
    rw [← smul_add,← smul_sub]


/-- The canonical inclusion of H into the semi-direct sum H ⋊⁅ψ⁆ G. -/
def inclusion : H →ₗ⁅R⁆ (H ⋊⁅ψ⁆ G) where
  toLinearMap := LinearMap.inl R H G
  map_lie' := by
    intros x y
    unfold SemiDirectSum
    simp [Bracket.bracket]


/-- The canonical projection from the semi-direct sum H ⋊⁅ψ⁆ G to G. -/
def projection : (H ⋊⁅ψ⁆ G) →ₗ⁅R⁆ G where
  toLinearMap := LinearMap.snd R H G
  map_lie' := by
    unfold SemiDirectSum
    intros x y
    simp [Bracket.bracket]


instance : LieAlgebra.IsExtension (inclusion ψ) (projection ψ)  where
  ker_eq_bot := by
    simp only [LieHom.ker_eq_bot]
    exact LinearMap.inl_injective
  range_eq_top := by
    simp only [LieHom.range_eq_top]
    exact LinearMap.snd_surjective
  exact := by
    refine (LieHom.range_eq_ker_iff (inclusion ψ) (projection ψ)).mpr ?_
    refine Function.Exact.of_comp_of_mem_range rfl ?_
    refine fun x a ↦ ?_
    use x.1
    unfold inclusion
    exact Prod.ext rfl (id (Eq.symm a))

end SemiDirectSum

end LieAlgebra

end
