/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Associators and unitors for tensor products of modules over a commutative ring.

-/

suppress_compilation

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {A M N P Q S T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)

namespace TensorProduct

variable [Module R P]

variable {M N}

section

variable (R M)

/-- The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
protected def lid : R ⊗[R] M ≃ₗ[R] M :=
  LinearEquiv.ofLinear (lift <| LinearMap.lsmul R M) (mk R R M 1) (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

end

@[simp]
theorem lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R ⊗ M → M) (r ⊗ₜ m) = r • m :=
  rfl

@[simp]
theorem lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 ⊗ₜ m :=
  rfl

lemma includeRight_lid {S : Type*} [Semiring S] [Algebra R S] (m : R ⊗[R] M) :
    (1 : S) ⊗ₜ[R] (TensorProduct.lid R M) m =
      (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap) m := by
  suffices ∀ m, (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 ⊗ₜ[R] m by
    simp [← this]
  intros; simp

section

variable (R M)

/-- The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
protected def rid : M ⊗[R] R ≃ₗ[R] M :=
  LinearEquiv.ofLinear
    (lift <| .flip (LinearMap.lsmul R M))
    (mk R M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext <| by ext; simp)

end

@[simp]
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m ⊗ₜ r) = r • m :=
  rfl

@[simp]
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m ⊗ₜ 1 :=
  rfl

@[simp]
theorem comm_trans_lid :
    TensorProduct.comm R M R ≪≫ₗ TensorProduct.lid R M = TensorProduct.rid R M :=
  LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

@[simp]
theorem comm_trans_rid :
    TensorProduct.comm R R M ≪≫ₗ TensorProduct.rid R M = TensorProduct.lid R M :=
  LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

variable (R) in
theorem lid_eq_rid : TensorProduct.lid R R = TensorProduct.rid R R :=
  LinearEquiv.toLinearMap_injective <| ext' mul_comm

section CompatibleSMul

variable (R A M N) [CommSemiring A] [Module A M] [Module A N]
  [CompatibleSMul R A M N] [Module R A] [SMulCommClass R A A] [CompatibleSMul R A A M]
  [CompatibleSMul A R A M]

/-- If the R- and A- action on A and M satisfy `CompatibleSMul` both ways,
then `A ⊗[R] M` is canonically isomorphic to `M`. -/
def lidOfCompatibleSMul : A ⊗[R] M ≃ₗ[A] M :=
  (equivOfCompatibleSMul R A A M).symm ≪≫ₗ TensorProduct.lid _ _

theorem lidOfCompatibleSMul_tmul (a m) : lidOfCompatibleSMul R A M (a ⊗ₜ[R] m) = a • m := rfl

end CompatibleSMul

open LinearMap

section

variable (R M N P)

attribute [local ext high] ext in
/-- The associator for tensor product of R-modules, as a linear equivalence. -/
protected def assoc : (M ⊗[R] N) ⊗[R] P ≃ₗ[R] M ⊗[R] N ⊗[R] P :=
  LinearEquiv.ofLinear
    (lift <| lift <| lcurry _ _ _ _ ∘ₗ mk _ _ _)
    (lift <| uncurry _ _ _ _ ∘ₗ curry (mk R _ _))
    (by ext; rfl)
    (by ext; rfl)

end

@[simp]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P) (m ⊗ₜ n ⊗ₜ p) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P).symm (m ⊗ₜ (n ⊗ₜ p)) = m ⊗ₜ n ⊗ₜ p :=
  rfl

/-- Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `(M ⊗ N) ⊗ P`
with `M ⊗ (N ⊗ P)` and `(Q ⊗ S) ⊗ T` with `Q ⊗ (S ⊗ T)`, then this lemma states that
`f ⊗ (g ⊗ h) = (f ⊗ g) ⊗ h`. -/
lemma map_map_comp_assoc_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map f (map g h) ∘ₗ TensorProduct.assoc R M N P =
      TensorProduct.assoc R Q S T ∘ₗ map (map f g) h :=
  ext <| ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

lemma map_map_assoc (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : (M ⊗[R] N) ⊗[R] P) :
    map f (map g h) (TensorProduct.assoc R M N P x) =
      TensorProduct.assoc R Q S T (map (map f g) h x) :=
  DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _

/-- Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `M ⊗ (N ⊗ P)`
with `(M ⊗ N) ⊗ P` and `Q ⊗ (S ⊗ T)` with `(Q ⊗ S) ⊗ T`, then this lemma states that
`(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)`. -/
lemma map_map_comp_assoc_symm_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map (map f g) h ∘ₗ (TensorProduct.assoc R M N P).symm =
      (TensorProduct.assoc R Q S T).symm ∘ₗ map f (map g h) :=
  ext <| LinearMap.ext fun _ => ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

lemma map_map_assoc_symm (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : M ⊗[R] (N ⊗[R] P)) :
    map (map f g) h ((TensorProduct.assoc R M N P).symm x) =
      (TensorProduct.assoc R Q S T).symm (map f (map g h) x) :=
  DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _


section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']

variable (R M N P Q)

/-- A tensor product analogue of `mul_left_comm`. -/
def leftComm : M ⊗[R] N ⊗[R] P ≃ₗ[R] N ⊗[R] M ⊗[R] P :=
  let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

variable {M N P Q}

@[simp]
theorem leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl

@[simp]
theorem leftComm_symm_tmul (m : M) (n : N) (p : P) :
    (leftComm R M N P).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

variable (M N P) in
attribute [local ext high] ext in
/-- A tensor product analogue of `mul_right_comm`. -/
def rightComm : (M ⊗[R] N) ⊗[R] P ≃ₗ[R] (M ⊗[R] P) ⊗[R] N :=
  LinearEquiv.ofLinear
    (lift (lift (LinearMap.lflip ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
    (lift (lift (LinearMap.lflip ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
  (by ext; rfl) (by ext; rfl)

@[simp]
theorem rightComm_tmul (m : M) (n : N) (p : P) :
    rightComm R M N P ((m ⊗ₜ n) ⊗ₜ p) = (m ⊗ₜ p) ⊗ₜ n :=
  rfl

@[simp]
theorem rightComm_symm : (rightComm R M N P).symm = rightComm R M P N := rfl

variable (M N P Q)

/-- This special case is worth defining explicitly since it is useful for defining multiplication
on tensor products of modules carrying multiplications (e.g., associative rings, Lie rings, ...).

E.g., suppose `M = P` and `N = Q` and that `M` and `N` carry bilinear multiplications:
`M ⊗ M → M` and `N ⊗ N → N`. Using `map`, we can define `(M ⊗ M) ⊗ (N ⊗ N) → M ⊗ N` which, when
combined with this definition, yields a bilinear multiplication on `M ⊗ N`:
`(M ⊗ N) ⊗ (M ⊗ N) → M ⊗ N`. In particular we could use this to define the multiplication in
the `TensorProduct.semiring` instance (currently defined "by hand" using `TensorProduct.mul`).

See also `mul_mul_mul_comm`. -/
def tensorTensorTensorComm : (M ⊗[R] N) ⊗[R] P ⊗[R] Q ≃ₗ[R] (M ⊗[R] P) ⊗[R] N ⊗[R] Q :=
  (TensorProduct.assoc R (M ⊗[R] N) P Q).symm
    ≪≫ₗ congr (TensorProduct.rightComm R M N P) (.refl R Q)
    ≪≫ₗ TensorProduct.assoc R (M ⊗[R] P) N Q

variable {M N P Q}

@[simp]
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q :=
  rfl

theorem tensorTensorTensorComm_comp_map {V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
    (f : M →ₗ[R] S) (g : N →ₗ[R] T) (h : P →ₗ[R] V) (j : Q →ₗ[R] W) :
    tensorTensorTensorComm R S T V W ∘ₗ map (map f g) (map h j) =
      map (map f h) (map g j) ∘ₗ tensorTensorTensorComm R M N P Q :=
  ext_fourfold' fun _ _ _ _ => rfl

variable (M N P Q)

/-- This special case is useful for describing the interplay between `dualTensorHomEquiv` and
composition of linear maps.

E.g., composition of linear maps gives a map `(M → N) ⊗ (N → P) → (M → P)`, and applying
`dual_tensor_hom_equiv.symm` to the three hom-modules gives a map
`(M.dual ⊗ N) ⊗ (N.dual ⊗ P) → (M.dual ⊗ P)`, which agrees with the application of `contractRight`
on `N ⊗ N.dual` after the suitable rebracketting.
-/
def tensorTensorTensorAssoc : (M ⊗[R] N) ⊗[R] P ⊗[R] Q ≃ₗ[R] (M ⊗[R] N ⊗[R] P) ⊗[R] Q :=
  (TensorProduct.assoc R (M ⊗[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)

variable {M N P Q}

@[simp]
theorem tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorAssoc R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q :=
  rfl

@[simp]
theorem tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R M N P Q).symm (m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ n ⊗ₜ (p ⊗ₜ q) :=
  rfl

end

end TensorProduct

open scoped TensorProduct

variable [Module R P]

namespace LinearMap

variable {N}

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

open TensorProduct (assoc lid rid)

lemma lTensor_tensor (f : P →ₗ[R] Q) :
    lTensor (M ⊗[R] N) f = (assoc R M N Q).symm ∘ₗ (f.lTensor N).lTensor M ∘ₗ assoc R M N P :=
  TensorProduct.ext <| TensorProduct.ext rfl

theorem rTensor_tensor : rTensor (M ⊗[R] N) g =
    assoc R Q M N ∘ₗ rTensor N (rTensor M g) ∘ₗ (assoc R P M N).symm :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ TensorProduct.ext rfl

open TensorProduct

theorem lid_comp_rTensor (f : N →ₗ[R] R) :
    (lid R M).comp (rTensor M f) = lift ((lsmul R M).comp f) := ext' fun _ _ ↦ rfl

lemma rid_comp_lTensor (f : M →ₗ[R] R) :
    (rid R N).comp (lTensor N f) = lift ((lsmul R N).flip.compl₂ f) := ext' fun _ _ ↦ rfl

end LinearMap
