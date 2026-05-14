/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Universal property of the tensor product

Given any bilinear map `f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂`, there is a unique semilinear map
`TensorProduct.lift f : TensorProduct R M N →ₛₗ[σ₁₂] P₂` whose composition with the canonical
bilinear map `TensorProduct.mk` is the given bilinear map `f`.  Uniqueness is shown in the theorem
`TensorProduct.lift.unique`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section Module

variable {M N}

/-- Lift an `R`-balanced map to the tensor product.
A map `f : M →+ N →+ P` additive in both components is `R`-balanced, or middle linear with respect
to `R`, if scalar multiplication in either argument is equivalent, `f (r • m) n = f m (r • n)`.
Note that strictly the first action should be a right-action by `R`, but for now `R` is commutative
so it doesn't matter. -/
-- TODO: use this to implement `lift` and `SMul.aux`. For now we do not do this as it causes
-- performance issues elsewhere.
def liftAddHom (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) :
    M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2)) <|
    AddCon.addConGen_le fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
        (AddCon.ker_rel _).2 <| by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]

@[simp]
theorem liftAddHom_tmul (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) (m : M) (n : N) :
    liftAddHom f hf (m ⊗ₜ n) = f m n :=
  rfl

end Module

variable [Module R P] [Module R Q]

section UniversalProperty

variable {M N}
variable (f : M →ₗ[R] N →ₗ[R] P)
variable (f' : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂)

/-- Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def liftAux : M ⊗[R] N →+ P₂ :=
  liftAddHom (LinearMap.toAddMonoidHom'.comp <| f'.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smulₛₗ₂, map_smulₛₗ]

theorem liftAux_tmul (m n) : liftAux f' (m ⊗ₜ n) = f' m n :=
  rfl

variable {f f'}

@[simp]
theorem liftAux.smulₛₗ (r : R) (x) : liftAux f' (r • x) = σ₁₂ r • liftAux f' x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f' p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f').map_add, ih1, ih2, smul_add]

theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
  liftAux.smulₛₗ _ _

variable (f') in
/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`.

This works for semilinear maps. -/
def lift : M ⊗[R] N →ₛₗ[σ₁₂] P₂ :=
  { liftAux f' with map_smul' := liftAux.smulₛₗ }

@[simp]
theorem lift.tmul (x y) : lift f' (x ⊗ₜ y) = f' x y :=
  rfl

@[simp]
theorem lift.tmul' (x y) : (lift f').1 (x ⊗ₜ y) = f' x y :=
  rfl

theorem ext' {g h : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add, h.map_add, ihx, ihy]

theorem lift.unique {g : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = f' x y) : g = lift f' :=
  ext' fun m n => by rw [H, lift.tmul]

theorem lift_mk : lift (mk R M N) = LinearMap.id :=
  Eq.symm <| lift.unique fun _ _ => rfl

theorem lift_compr₂ₛₗ [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (h : P₂ →ₛₗ[σ₂₃] P₃) :
    lift (f'.compr₂ₛₗ h) = h.comp (lift f') :=
  Eq.symm <| lift.unique fun _ _ => by simp

theorem lift_compr₂ (g : P →ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp

theorem lift_mk_compr₂ₛₗ (g : M ⊗ N →ₛₗ[σ₁₂] P₂) : lift ((mk R M N).compr₂ₛₗ g) = g := by
  rw [lift_compr₂ₛₗ g, lift_mk, LinearMap.comp_id]

theorem lift_mk_compr₂ (f : M ⊗ N →ₗ[R] P) : lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f, lift_mk, LinearMap.comp_id]

/-- This used to be an `@[ext]` lemma, but it fails very slowly when the `ext` tactic tries to apply
it in some cases, notably when one wants to show equality of two linear maps. The `@[ext]`
attribute is now added locally where it is needed. Using this as the `@[ext]` lemma instead of
`TensorProduct.ext'` allows `ext` to apply lemmas specific to `M →ₗ _` and `N →ₗ _`.

See note [partially-applied ext lemmas]. -/
theorem ext {g h : M ⊗ N →ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) :
    g = h := by
  rw [← lift_mk_compr₂ₛₗ g, H, lift_mk_compr₂ₛₗ]

attribute [local ext high] ext

variable (M N P₂ σ₁₂) in
/-- Linearly constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurry : (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] P₂ where
  toFun := lift
  map_add' f g := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
theorem uncurry_apply (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    uncurry σ₁₂ M N P₂ f (m ⊗ₜ n) = f m n := rfl

variable (M N P₂ σ₁₂)

/-- A linear equivalence constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift.equiv : (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] P₂ :=
  { uncurry σ₁₂ M N P₂ with
    invFun := fun f => (mk R M N).compr₂ₛₗ f }

@[simp]
theorem lift.equiv_apply (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lift.equiv σ₁₂ M N P₂ f (m ⊗ₜ n) = f m n :=
  uncurry_apply f m n

@[simp]
theorem lift.equiv_symm_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    (lift.equiv σ₁₂ M N P₂).symm f m n = f (m ⊗ₜ n) :=
  rfl

/-- Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`. -/
def lcurry : (M ⊗[R] N →ₛₗ[σ₁₂] P₂) →ₗ[R₂] M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂ :=
  (lift.equiv σ₁₂ M N P₂).symm

variable {M N P₂ σ₁₂}

@[simp]
theorem lcurry_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lcurry σ₁₂ M N P₂ f m n = f (m ⊗ₜ n) :=
  rfl

/-- Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`. -/
def curry (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂ :=
  lcurry σ₁₂ M N P₂ f

@[simp]
theorem curry_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) : curry f m n = f (m ⊗ₜ n) :=
  rfl

theorem curry_injective :
    Function.Injective (curry : (M ⊗[R] N →ₛₗ[σ₁₂] P₂) → M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) :=
  fun _ _ H => ext H

theorem ext_threefold {g h : M ⊗[R] N ⊗[R] P →ₛₗ[σ₁₂] P₂}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext x y z
  exact H x y z

theorem ext_threefold' {g h : M ⊗[R] (N ⊗[R] P) →ₛₗ[σ₁₂] P₂}
    (H : ∀ x y z, g (x ⊗ₜ (y ⊗ₜ z)) = h (x ⊗ₜ (y ⊗ₜ z))) : g = h := by
  ext x y z
  exact H x y z

-- We'll need this one for checking the pentagon identity!
theorem ext_fourfold {g h : M ⊗[R] N ⊗[R] P ⊗[R] Q →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, g (w ⊗ₜ x ⊗ₜ y ⊗ₜ z) = h (w ⊗ₜ x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext w x y z
  exact H w x y z

/-- Two semilinear maps `(M ⊗ N) ⊗ (P ⊗ Q) → P₂` which agree on all elements of the
form `(m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)` are equal. -/
theorem ext_fourfold' {φ ψ : M ⊗[R] N ⊗[R] (P ⊗[R] Q) →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, φ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z)) = ψ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z))) : φ = ψ := by
  ext m n p q
  exact H m n p q

/-- Two semilinear maps `M ⊗ (N ⊗ P) ⊗ Q → P₂` which agree on all elements of the
form `m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q` are equal. -/
theorem ext_fourfold'' {φ ψ : M ⊗[R] (N ⊗[R] P) ⊗[R] Q →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, φ (w ⊗ₜ (x ⊗ₜ y) ⊗ₜ z) = ψ (w ⊗ₜ (x ⊗ₜ y) ⊗ₜ z)) : φ = ψ := by
  ext m n p q
  exact H m n p q

end UniversalProperty

variable {M N}
section

variable (R M N)

/-- The tensor product of modules is commutative, up to linear equivalence. -/
protected def comm : M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
  LinearEquiv.ofLinear (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)

@[simp]
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
lemma comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M := rfl

theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

-- Why is the `toLinearMap` necessary ? And why is this slow ?
lemma lift_comp_comm_eq (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) :
    lift f ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = lift f.flip :=
  ext rfl

attribute [local ext high] ext in
@[simp] lemma comm_trans_comm :
    TensorProduct.comm R N M ≪≫ₗ TensorProduct.comm R M N = .refl _ _ := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

lemma comm_comp_comm :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id := by
  simp

@[simp]
lemma comm_comp_comm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc, comm_comp_comm, LinearMap.id_comp]

@[simp] theorem comm_comm (x) :
    TensorProduct.comm R M N (TensorProduct.comm R N M x) = x :=
  congr($(comm_trans_comm _ _ _) x)

end

section CompatibleSMul

variable (R) (A S M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [CommSemiring A] [Module A M] [Module A N] [SMulCommClass R A M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [SMulCommClass A S M]
  [CompatibleSMul R A M N]

/-- If M and N are both R- and A-modules and their actions on them commute,
and if the A-action on `M ⊗[R] N` can switch between the two factors, then there is a
canonical S-linear map from `M ⊗[A] N` to `M ⊗[R] N`,
where `S` is any other ring acting on `M` and whose action commutes with the `A` and `R`-actions. -/
def mapOfCompatibleSMul : M ⊗[A] N →ₗ[S] M ⊗[R] N where
  __ :=
    lift (σ₁₂ := RingHom.id A)
    { toFun := fun m ↦
      { __ := mk R M N m
        map_smul' := fun _ _ ↦ (smul_tmul _ _ _).symm }
      map_add' := fun _ _ ↦ LinearMap.ext <| by simp
      map_smul' := fun _ _ ↦ rfl }
  map_smul' s x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y => simp [smul_tmul']

@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R A S M N (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl

/- The map `mapOfCompatibleSMul` is surjective. Its kernel is characterized by the Lemma
`TensorProduct.ker_mapOfCompatibleSMul`. -/
theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R A S M N) :=
  fun x ↦ x.induction_on (⟨0, map_zero _⟩) (fun m n ↦ ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by simpa using congr($hx + $hy)⟩

attribute [local instance] SMulCommClass.symm

@[deprecated "with (S := R)" (since := "2026-02-21")]
alias mapOfCompatibleSMul' := mapOfCompatibleSMul

/-- If the R- and A-actions on M and N satisfy `CompatibleSMul` both ways,
then `M ⊗[A] N` is canonically isomorphic to `M ⊗[R] N` as `S`-modules,
where `S` is any other ring acting on `M` and whose action commutes with the `A` and `R`-actions. -/
def equivOfCompatibleSMul [CompatibleSMul A R M N] : M ⊗[A] N ≃ₗ[S] M ⊗[R] N where
  __ := mapOfCompatibleSMul R A S M N
  invFun := mapOfCompatibleSMul A R S M N
  left_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')

end CompatibleSMul

end TensorProduct

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R) in
/-- Auxiliary function to defining negation multiplication on tensor product. -/
def Neg.aux : M ⊗[R] N →ₗ[R] M ⊗[R] N :=
  lift <| (mk R M N).comp (-LinearMap.id)

instance neg : Neg (M ⊗[R] N) where
  neg := Neg.aux R

protected theorem neg_add_cancel (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx, hy, add_zero]

instance addCommGroup : AddCommGroup (M ⊗[R] N) where
  neg_add_cancel := fun x => TensorProduct.neg_add_cancel x
  zsmul := (· • ·)
  zsmul_zero' := by simp
  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]
  zsmul_neg' := fun n x => by
    change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
    rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,
      ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
    rfl

theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  rfl

theorem tmul_neg (m : M) (p : P) : m ⊗ₜ (-p) = -m ⊗ₜ[R] p :=
  (mk R M P _).map_neg _

theorem tmul_sub (m : M) (p₁ p₂ : P) : m ⊗ₜ (p₁ - p₂) = m ⊗ₜ[R] p₁ - m ⊗ₜ[R] p₂ :=
  (mk R M P _).map_sub _ _

theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _

/-- While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.toIntModule`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instance through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance CompatibleSMul.int : CompatibleSMul R ℤ M P :=
  ⟨fun r m p =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩

instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

end TensorProduct

end Ring
