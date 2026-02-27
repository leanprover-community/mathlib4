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
The semi-direct sum of two Lie algebras `H` and `G` over `R`, relative to a Lie algebra homomorphism
`ψ: G → Liederivation R H H `. As a set it just `H × G`, however the Lie bracket is twisted by `ψ`.
-/
@[ext] structure SemiDirectSum {R : Type*} [CommRing R] (H : Type*) [LieRing H] [LieAlgebra R H]
    (G : Type*) [LieRing G] [LieAlgebra R G] (_ : G →ₗ⁅R⁆ LieDerivation R H H) where
  /-- The element of H -/
  left : H
  /-- The element of G -/
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

instance : Module R (H ⋊⁅ψ⁆ G) := toProd.module R

@[simp] lemma toProd_smul (t : R) (x : H ⋊⁅ψ⁆ G) : (t • x).toProd = t • x.toProd := rfl

instance : Bracket (H ⋊⁅ψ⁆ G) (H ⋊⁅ψ⁆ G) where
  bracket x y := toProd.symm
    (⁅x.toProd.1, y.toProd.1⁆ + ψ x.toProd.2 y.toProd.1 - ψ y.toProd.2 x.toProd.1,
     ⁅x.toProd.2, y.toProd.2⁆)

lemma lie_def (x y : H ⋊⁅ψ⁆ G) :
    ⁅x, y⁆ = toProd.symm
      (⁅x.toProd.1, y.toProd.1⁆ + ψ x.toProd.2 y.toProd.1 - ψ y.toProd.2 x.toProd.1,
       ⁅x.toProd.2, y.toProd.2⁆) :=
  rfl

@[simp]
lemma toProd_lie (x y : H ⋊⁅ψ⁆ G) :
    toProd ⁅x, y⁆ =
      (⁅x.toProd.1, y.toProd.1⁆ + ψ x.toProd.2 y.toProd.1 - ψ y.toProd.2 x.toProd.1,
       ⁅x.toProd.2, y.toProd.2⁆) := by
  simp [lie_def]

lemma zero_eq_mk : (0 : H ⋊⁅ψ⁆ G) = ⟨0, 0⟩ := rfl
lemma add_eq_mk (x y : H ⋊⁅ψ⁆ G) : x + y = ⟨x.left + y.left, x.right + y.right⟩ := rfl
lemma sub_eq_mk (x y : H ⋊⁅ψ⁆ G) : x - y = ⟨x.left - y.left, x.right - y.right⟩ := rfl
lemma neg_eq_mk (x : H ⋊⁅ψ⁆ G) : -x = ⟨-x.left, -x.right⟩ := rfl
lemma smul_eq_mk (t : R) (x : H ⋊⁅ψ⁆ G) : t • x = ⟨t • x.left, t • x.right⟩ := rfl
lemma lie_eq_mk (x y : H ⋊⁅ψ⁆ G) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩ :=
  rfl

instance : LieRing (H ⋊⁅ψ⁆ G) where
  add_lie _ _ _ := toProd.injective <| by simp; abel
  lie_add _ _ _:= toProd.injective <| by simp; abel
  lie_self _ := toProd.injective <| by simp
  leibniz_lie _ _ _ := toProd.injective <| by simp; grind [lie_skew]

instance : LieAlgebra R (H ⋊⁅ψ⁆ G) where
  lie_smul _ _ _ := toProd.injective <| by
    simp [toProd_smul, smul_sub, smul_add]

/-- The canonical inclusion of H into the semi-direct sum H ⋊⁅ψ⁆ G. -/
def inl : H →ₗ⁅R⁆ H ⋊⁅ψ⁆ G where
  toFun x := toProd.symm (x, 0)
  map_add' _ _ := toProd.injective <| by simp
  map_smul' _ _ := toProd.injective <| by simp
  map_lie' := toProd.injective <| by simp

/-- The canonical inclusion of G into the semi-direct sum H ⋊⁅ψ⁆ G. -/
def inr : G →ₗ⁅R⁆ H ⋊⁅ψ⁆ G where
  toFun x := toProd.symm (0, x)
  map_add' _ _ := toProd.injective <| by simp
  map_smul' _ _ := toProd.injective <| by simp
  map_lie' := toProd.injective <| by simp

@[simp]
lemma inl_injective : Function.Injective (inl ψ) := by intro; simp [inl]

/-- The canonical projection of the semi-direct sum H ⋊⁅ψ⁆ G to G. -/
def projr : H ⋊⁅ψ⁆ G →ₗ⁅R⁆ G where
  toFun x := x.toProd.snd
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/-- The canonical projection of the semi-direct sum H ⋊⁅ψ⁆ G to G.
It is not, in general, a Lie algebra homomorphism, just a linear map. -/
def projl : H ⋊⁅ψ⁆ G →ₗ[R] H where
  toFun x := x.toProd.fst
  map_add' _ _ := by simp
  map_smul' _ _ := by simp



@[simp] lemma inl_eq_mk (x : H) : inl ψ x = ⟨x, 0⟩ := rfl
@[simp] lemma inr_eq_mk (x : G) : inr ψ x = ⟨0, x⟩ := rfl

@[simp] lemma projr_mk (x : H ⋊⁅ψ⁆ G) : projr ψ x = x.right := rfl
lemma projr_inl_apply {x : H} : projr ψ (inl ψ x) = 0 := by simp
lemma projr_inr_apply {x : G} : projr ψ (inr ψ x) = x := by simp

@[simp]
lemma projr_surjective : Function.Surjective (projr ψ) :=
  fun x ↦ ⟨inr ψ x, by simp⟩

instance : LieAlgebra.IsExtension (inl ψ) (projr ψ) where
  ker_eq_bot := by simp [LieHom.ker_eq_bot]
  range_eq_top := by simp [LieHom.range_eq_top]
  exact := by ext ⟨x, y⟩; aesop

end SemiDirectSum
end LieAlgebra
end
