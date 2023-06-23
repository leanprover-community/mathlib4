/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.clifford_algebra.even
! leanprover-community/mathlib commit 9264b15ee696b7ca83f13c8ad67c83d6eb70b730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# The universal property of the even subalgebra

## Main definitions

* `clifford_algebra.even Q`: The even subalgebra of `clifford_algebra Q`.
* `clifford_algebra.even_hom`: The type of bilinear maps that satisfy the universal property of the
  even subalgebra
* `clifford_algebra.even.lift`: The universal property of the even subalgebra, which states
  that every bilinear map `f` with `f v v = Q v` and `f u v * f v w = Q v • f u w` is in unique
  correspondence with an algebra morphism from `clifford_algebra.even Q`.

## Implementation notes

The approach here is outlined in "Computing with the universal properties of the Clifford algebra
and the even subalgebra" (to appear).

The broad summary is that we have two tricks available to us for implementing complex recursors on
top of `clifford_algebra.lift`: the first is to use morphisms as the output type, such as
`A = module.End R N` which is how we obtained `clifford_algebra.foldr`; and the second is to use
`N = (N', S)` where `N'` is the value we wish to compute, and `S` is some auxiliary state passed
between one recursor invocation and the next.
For the universal property of the even subalgebra, we apply a variant of the first trick again by
choosing `S` to itself be a submodule of morphisms.
-/


namespace CliffordAlgebra

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

-- put this after `Q` since we want to talk about morphisms from `clifford_algebra Q` to `A` and
-- that order is more natural
variable {A B : Type _} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

open scoped DirectSum

variable (Q)

/-- The even submodule `clifford_algebra.even_odd Q 0` is also a subalgebra. -/
def even : Subalgebra R (CliffordAlgebra Q) :=
  (evenOdd Q 0).toSubalgebra SetLike.GradedMonoid.one_mem fun x y hx hy =>
    add_zero (0 : ZMod 2) ▸ SetLike.GradedMonoid.mul_mem hx hy
#align clifford_algebra.even CliffordAlgebra.even

@[simp]
theorem even_toSubmodule : (even Q).toSubmodule = evenOdd Q 0 :=
  rfl
#align clifford_algebra.even_to_submodule CliffordAlgebra.even_toSubmodule

variable (A)

/-- The type of bilinear maps which are accepted by `clifford_algebra.even.lift`. -/
@[ext]
structure EvenHom : Type max u_2 u_3 where
  bilin : M →ₗ[R] M →ₗ[R] A
  contract (m : M) : bilin m m = algebraMap R A (Q m)
  contract_mid (m₁ m₂ m₃ : M) : bilin m₁ m₂ * bilin m₂ m₃ = Q m₂ • bilin m₁ m₃
#align clifford_algebra.even_hom CliffordAlgebra.EvenHom

variable {A Q}

/-- Compose an `even_hom` with an `alg_hom` on the output. -/
@[simps]
def EvenHom.compr₂ (g : EvenHom Q A) (f : A →ₐ[R] B) : EvenHom Q B where
  bilin := g.bilin.compr₂ f.toLinearMap
  contract m := (f.congr_arg <| g.contract _).trans <| f.commutes _
  contract_mid m₁ m₂ m₃ :=
    (f.map_mul _ _).symm.trans <| (f.congr_arg <| g.contract_mid _ _ _).trans <| f.map_smul _ _
#align clifford_algebra.even_hom.compr₂ CliffordAlgebra.EvenHom.compr₂

variable (Q)

/-- The embedding of pairs of vectors into the even subalgebra, as a bilinear map. -/
@[simps bilin_apply_apply_coe]
def even.ι : EvenHom Q (even Q) where
  bilin :=
    LinearMap.mk₂ R (fun m₁ m₂ => ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_evenOdd_zero _ _ _⟩)
      (fun _ _ _ => by simp only [LinearMap.map_add, add_mul]; rfl)
      (fun _ _ _ => by simp only [LinearMap.map_smul, smul_mul_assoc]; rfl)
      (fun _ _ _ => by simp only [LinearMap.map_add, mul_add]; rfl) fun _ _ _ => by
      simp only [LinearMap.map_smul, mul_smul_comm]; rfl
  contract m := Subtype.ext <| ι_sq_scalar Q m
  contract_mid m₁ m₂ m₃ :=
    Subtype.ext <|
      calc
        ι Q m₁ * ι Q m₂ * (ι Q m₂ * ι Q m₃) = ι Q m₁ * (ι Q m₂ * ι Q m₂ * ι Q m₃) := by
          simp only [mul_assoc]
        _ = Q m₂ • (ι Q m₁ * ι Q m₃) := by rw [Algebra.smul_def, ι_sq_scalar, Algebra.left_comm]
#align clifford_algebra.even.ι CliffordAlgebra.even.ι

instance : Inhabited (EvenHom Q (even Q)) :=
  ⟨even.ι Q⟩

variable (f : EvenHom Q A)

/-- Two algebra morphisms from the even subalgebra are equal if they agree on pairs of generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem even.algHom_ext ⦃f g : even Q →ₐ[R] A⦄ (h : (even.ι Q).compr₂ f = (even.ι Q).compr₂ g) :
    f = g := by
  rw [even_hom.ext_iff] at h 
  ext ⟨x, hx⟩
  refine' even_induction _ _ _ _ _ hx
  · intro r
    exact (f.commutes r).trans (g.commutes r).symm
  · intro x y hx hy ihx ihy
    have := congr_arg₂ (· + ·) ihx ihy
    exact (f.map_add _ _).trans (this.trans <| (g.map_add _ _).symm)
  · intro m₁ m₂ x hx ih
    have := congr_arg₂ (· * ·) (LinearMap.congr_fun (LinearMap.congr_fun h m₁) m₂) ih
    exact (f.map_mul _ _).trans (this.trans <| (g.map_mul _ _).symm)
#align clifford_algebra.even.alg_hom_ext CliffordAlgebra.even.algHom_ext

variable {Q}

namespace Even.Lift

/-- An auxiliary submodule used to store the half-applied values of `f`.
This is the span of elements `f'` such that `∃ x m₂, ∀ m₁, f' m₁ = f m₁ m₂ * x`.  -/
private def S : Submodule R (M →ₗ[R] A) :=
  Submodule.span R
    {f' | ∃ x m₂, f' = LinearMap.lcomp R _ (f.bilin.flip m₂) (LinearMap.mulRight R x)}

/-- An auxiliary bilinear map that is later passed into `clifford_algebra.fold`. Our desired result
is stored in the `A` part of the accumulator, while auxiliary recursion state is stored in the `S f`
part. -/
private def f_fold : M →ₗ[R] A × s f →ₗ[R] A × s f :=
  LinearMap.mk₂ R
    (fun m acc =>
      /- We could write this `snd` term in a point-free style as follows, but it wouldn't help as we
        don't have any prod or subtype combinators to deal with n-linear maps of this degree.
        ```lean
        (linear_map.lcomp R _ (algebra.lmul R A).to_linear_map.flip).comp $
          (linear_map.llcomp R M A A).flip.comp f.flip : M →ₗ[R] A →ₗ[R] M →ₗ[R] A)
        ```
        -/
      (Acc.2 m,
        ⟨(LinearMap.mulRight R Acc.1).comp (f.bilin.flip m), Submodule.subset_span <| ⟨_, _, rfl⟩⟩))
    (fun m₁ m₂ a =>
      Prod.ext (LinearMap.map_add _ m₁ m₂)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (m₁ + m₂) * a.1 = f.bilin m₃ m₁ * a.1 + f.bilin m₃ m₂ * a.1 by
              rw [map_add, add_mul]))
    (fun c m a =>
      Prod.ext (LinearMap.map_smul _ c m)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (c • m) * a.1 = c • (f.bilin m₃ m * a.1) by
              rw [LinearMap.map_smul, smul_mul_assoc]))
    (fun m a₁ a₂ => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun m₃ => mul_add _ _ _))
    fun c m a => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun m₃ => mul_smul_comm _ _ _)

@[simp]
private theorem fst_f_fold_f_fold (m₁ m₂ : M) (x : A × s f) :
    (fFold f m₁ (fFold f m₂ x)).fst = f.bilin m₁ m₂ * x.fst :=
  rfl

@[simp]
private theorem snd_f_fold_f_fold (m₁ m₂ m₃ : M) (x : A × s f) :
    ((fFold f m₁ (fFold f m₂ x)).snd : M →ₗ[R] A) m₃ = f.bilin m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ :=
  rfl

private theorem f_fold_f_fold (m : M) (x : A × s f) : fFold f m (fFold f m x) = Q m • x := by
  obtain ⟨a, ⟨g, hg⟩⟩ := x
  ext : 2
  · change f.bilin m m * a = Q m • a
    rw [Algebra.smul_def, f.contract]
  · ext m₁
    change f.bilin _ _ * g m = Q m • g m₁
    apply Submodule.span_induction' _ _ _ _ hg
    · rintro _ ⟨b, m₃, rfl⟩
      change f.bilin _ _ * (f.bilin _ _ * b) = Q m • (f.bilin _ _ * b)
      rw [← smul_mul_assoc, ← mul_assoc, f.contract_mid]
    · change f.bilin m₁ m * 0 = Q m • 0
      rw [MulZeroClass.mul_zero, smul_zero]
    · rintro x hx y hy ihx ihy
      rw [LinearMap.add_apply, LinearMap.add_apply, mul_add, smul_add, ihx, ihy]
    · rintro x hx c ihx
      rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm, ihx, smul_comm]

/-- The final auxiliary construction for `clifford_algebra.even.lift`. This map is the forwards
direction of that equivalence, but not in the fully-bundled form. -/
@[simps (config := { attrs := [] }) apply]
def aux (f : EvenHom Q A) : CliffordAlgebra.even Q →ₗ[R] A := by
  refine' _ ∘ₗ (Even Q).val.toLinearMap
  exact LinearMap.fst _ _ _ ∘ₗ foldr Q (f_fold f) (f_fold_f_fold f) (1, 0)
#align clifford_algebra.even.lift.aux CliffordAlgebra.even.Lift.aux

@[simp]
theorem aux_one : aux f 1 = 1 :=
  congr_arg Prod.fst (foldr_one _ _ _ _)
#align clifford_algebra.even.lift.aux_one CliffordAlgebra.even.Lift.aux_one

@[simp]
theorem aux_ι (m₁ m₂ : M) : aux f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans
    (by
      rw [foldr_ι, foldr_ι]
      exact mul_one _)
#align clifford_algebra.even.lift.aux_ι CliffordAlgebra.even.Lift.aux_ι

@[simp]
theorem aux_algebraMap (r) (hr) : aux f ⟨algebraMap R _ r, hr⟩ = algebraMap R _ r :=
  (congr_arg Prod.fst (foldr_algebraMap _ _ _ _ _)).trans (Algebra.algebraMap_eq_smul_one r).symm
#align clifford_algebra.even.lift.aux_algebra_map CliffordAlgebra.even.Lift.aux_algebraMap

@[simp]
theorem aux_mul (x y : even Q) : aux f (x * y) = aux f x * aux f y := by
  cases x
  cases y
  refine' (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans _
  dsimp only
  refine' even_induction Q _ _ _ _ x_property
  · intro r
    rw [foldr_algebra_map, aux_algebra_map]
    exact Algebra.smul_def r _
  · intro x y hx hy ihx ihy
    rw [LinearMap.map_add, Prod.fst_add, ihx, ihy, ← add_mul, ← LinearMap.map_add]
    rfl
  · rintro m₁ m₂ x (hx : x ∈ Even Q) ih
    rw [aux_apply, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold, ih, ← mul_assoc,
      Subtype.coe_mk, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_f_fold_f_fold]
    rfl
#align clifford_algebra.even.lift.aux_mul CliffordAlgebra.even.Lift.aux_mul

end Even.Lift

open Even.Lift

variable (Q) {A}

/-- Every algebra morphism from the even subalgebra is in one-to-one correspondence with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts across
multiplication. -/
@[simps symm_apply_bilin]
def even.lift : EvenHom Q A ≃ (CliffordAlgebra.even Q →ₐ[R] A) where
  toFun f := AlgHom.ofLinearMap (aux f) (aux_one f) (aux_mul f)
  invFun F := (even.ι Q).compr₂ F
  left_inv f := EvenHom.ext _ _ <| LinearMap.ext₂ <| even.Lift.aux_ι f
  right_inv F := even.algHom_ext Q <| EvenHom.ext _ _ <| LinearMap.ext₂ <| even.Lift.aux_ι _
#align clifford_algebra.even.lift CliffordAlgebra.even.lift

@[simp]
theorem even.lift_ι (f : EvenHom Q A) (m₁ m₂ : M) :
    even.lift Q f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  even.Lift.aux_ι _ _ _
#align clifford_algebra.even.lift_ι CliffordAlgebra.even.lift_ι

end CliffordAlgebra

