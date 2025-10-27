/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Maps between tensor products of R-algebras

This file provides results about maps between tensor products of `R`-algebras.

## Main declarations

- the structure isomorphisms
  * `Algebra.TensorProduct.lid : R ⊗[R] A ≃ₐ[R] A`
  * `Algebra.TensorProduct.rid : A ⊗[R] R ≃ₐ[S] A` (usually used with `S = R` or `S = A`)
  * `Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `Algebra.TensorProduct.assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`
- `Algebra.TensorProduct.liftEquiv`: a universal property for the tensor product of algebras.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct

namespace Module.End

open LinearMap

variable (R M N : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The map `LinearMap.lTensorHom` which sends `f ↦ 1 ⊗ f` as a morphism of algebras. -/
@[simps!]
def lTensorAlgHom : Module.End R M →ₐ[R] Module.End R (N ⊗[R] M) :=
  .ofLinearMap (lTensorHom (M := N)) (lTensor_id N M) (lTensor_mul N)

/-- The map `LinearMap.rTensorHom` which sends `f ↦ f ⊗ 1` as a morphism of algebras. -/
@[simps!]
def rTensorAlgHom : Module.End R M →ₐ[R] Module.End R (M ⊗[R] N) :=
  .ofLinearMap (rTensorHom (M := N)) (rTensor_id N M) (rTensor_mul N)

end Module.End

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
We build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra S C]
variable [Semiring D] [Algebra R D]

/-- To check a linear map preserves multiplication, it suffices to check it on pure tensors. See
`algHomOfLinearMapTensorProduct` for a bundled version. -/
lemma _root_.LinearMap.map_mul_of_map_mul_tmul {f : A ⊗[R] B →ₗ[S] C}
    (hf : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (x y : A ⊗[R] B) : f (x * y) = f x * f y :=
  f.map_mul_iff.2 (by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    letI : Algebra R C := RestrictScalars.algebra R S C
    letI : IsScalarTower R S C := RestrictScalars.isScalarTower R S C
    ext
    dsimp
    exact hf _ _ _ _) x y

/-- Build an algebra morphism from a linear map out of a tensor product, and evidence that on pure
tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  AlgHom.ofLinearMap f h_one (f.map_mul_of_map_mul_tmul h_mul)

@[simp]
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl

/-- Build an algebra equivalence from a linear equivalence out of a tensor product, and evidence
that on pure tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) h_mul h_one, f with }

@[simp]
theorem algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTensorProduct f h_mul h_one : A ⊗[R] B ≃ₐ[S] C) x = f x :=
  rfl

variable [Algebra R C]
/-- Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTripleTensorProduct (f : A ⊗[R] B ⊗[R] C ≃ₗ[R] D)
    (h_mul :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (h_one : f (((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = 1) :
    A ⊗[R] B ⊗[R] C ≃ₐ[R] D :=
  AlgEquiv.ofLinearEquiv f h_one <| f.map_mul_iff.2 <| by
    ext
    dsimp
    exact h_mul _ _ _ _ _ _

@[simp]
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTripleTensorProduct f h_mul h_one : A ⊗[R] B ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl

section lift
variable [IsScalarTower R S C]

/-- The forward direction of the universal property of tensor products of algebras; any algebra
morphism from the tensor product can be factored as the product of two algebra morphisms that
commute.

See `Algebra.TensorProduct.liftEquiv` for the fact that every morphism factors this way. -/
def lift (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) : (A ⊗[R] B) →ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C →ₗ[S] C) →ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
      LinearMap.flip <| (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [map_mul, map_mul, (hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [map_one, map_one, one_mul])

@[simp]
theorem lift_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a ⊗ₜ b) = f a * g b :=
  rfl

@[simp]
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun _ _ => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A ⊗[R] B) := by
  ext <;> simp

@[simp]
theorem lift_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
  AlgHom.ext <| by simp

@[simp]
theorem lift_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
  AlgHom.ext <| by simp

/-- The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requirement for graded
algebra. -/
@[simps]
def liftEquiv : {fg : (A →ₐ[S] C) × (B →ₐ[R] C) // ∀ x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A ⊗[R] B) →ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

end lift

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
variable [Semiring F] [Algebra R F]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected nonrec def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])

@[simp] theorem lid_toLinearEquiv :
    (TensorProduct.lid R A).toLinearEquiv = _root_.TensorProduct.lid R A := rfl

variable {R} {A} in
@[simp]
theorem lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r ⊗ₜ a) = r • a := rfl

variable {A} in
@[simp]
theorem lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 ⊗ₜ a := rfl

variable (S)

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.

Note that if `A` is commutative this can be instantiated with `S = A`.
-/
protected nonrec def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun a₁ a₂ r₁ r₂ => smul_mul_smul_comm r₁ a₁ r₂ a₂ |>.symm)
    (one_smul R _)

@[simp] theorem rid_toLinearEquiv :
    (TensorProduct.rid R S A).toLinearEquiv = AlgebraTensorModule.rid R S A := rfl

variable {R A} in
@[simp]
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl

variable {A} in
@[simp]
theorem rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a ⊗ₜ 1 := rfl

section CompatibleSMul

variable (R S A B : Type*) [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
variable [SMulCommClass R S A] [CompatibleSMul R S A B]

/-- If A and B are both R- and S-algebras and their actions on them commute,
and if the S-action on `A ⊗[R] B` can switch between the two factors, then there is a
canonical S-algebra homomorphism from `A ⊗[S] B` to `A ⊗[R] B`. -/
def mapOfCompatibleSMul : A ⊗[S] B →ₐ[S] A ⊗[R] B :=
  .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul R S A B) rfl fun x ↦
    x.induction_on (by simp) (fun _ _ y ↦ y.induction_on (by simp) (by simp)
      fun _ _ h h' ↦ by simp only [mul_add, map_add, h, h'])
      fun _ _ h h' _ ↦ by simp only [add_mul, map_add, h, h']

@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R S A B (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl

theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R S A B) :=
  _root_.TensorProduct.mapOfCompatibleSMul_surjective R S A B

attribute [local instance] SMulCommClass.symm

/-- `mapOfCompatibleSMul R S A B` is also A-linear. -/
def mapOfCompatibleSMul' : A ⊗[S] B →ₐ[R] A ⊗[R] B :=
  .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul' R S A B) rfl
    (map_mul <| mapOfCompatibleSMul R S A B)

/-- If the R- and S-actions on A and B satisfy `CompatibleSMul` both ways,
then `A ⊗[S] B` is canonically isomorphic to `A ⊗[R] B`. -/
def equivOfCompatibleSMul [CompatibleSMul S R A B] : A ⊗[S] B ≃ₐ[S] A ⊗[R] B where
  __ := mapOfCompatibleSMul R S A B
  invFun := mapOfCompatibleSMul S R A B
  __ := _root_.TensorProduct.equivOfCompatibleSMul R S A B

variable [Algebra R S] [CompatibleSMul R S S A] [CompatibleSMul S R S A]
omit [SMulCommClass R S A]

/-- If the R- and S- action on S and A satisfy `CompatibleSMul` both ways,
then `S ⊗[R] A` is canonically isomorphic to `A`. -/
def lidOfCompatibleSMul : S ⊗[R] A ≃ₐ[S] A :=
  (equivOfCompatibleSMul R S S A).symm.trans (TensorProduct.lid _ _)

theorem lidOfCompatibleSMul_tmul (s a) : lidOfCompatibleSMul R S A (s ⊗ₜ[R] a) = s • a := rfl

instance {R M N : Type*} [CommSemiring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module ℚ M] [Module ℚ N] : CompatibleSMul R ℚ M N where
  smul_tmul q m n := by
    suffices q.den • ((q • m) ⊗ₜ[R] n) = q.den • (m ⊗ₜ[R] (q • n)) from
      smul_right_injective (M ⊗[R] N) (c := q.den) q.den_nz <| by norm_cast
    rw [smul_tmul', ← tmul_smul, ← smul_assoc, ← smul_assoc, nsmul_eq_mul, Rat.den_mul_eq_num]
    norm_cast
    rw [smul_tmul]

end CompatibleSMul

section

variable (B)

unseal mul in
/-- The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl

@[simp] theorem comm_toLinearEquiv :
    (Algebra.TensorProduct.comm R A B).toLinearEquiv = _root_.TensorProduct.comm R A B := rfl

variable {A B} in
@[simp]
theorem comm_tmul (a : A) (b : B) :
    TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a :=
  rfl

variable {A B} in
@[simp]
theorem comm_symm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b :=
  rfl

theorem comm_symm :
    (TensorProduct.comm R A B).symm = TensorProduct.comm R B A := by
  ext; rfl

@[simp]
lemma comm_comp_includeLeft :
    (TensorProduct.comm R A B : A ⊗[R] B →ₐ[R] B ⊗[R] A).comp includeLeft = includeRight := rfl

@[simp]
lemma comm_comp_includeRight :
    (TensorProduct.comm R A B : A ⊗[R] B →ₐ[R] B ⊗[R] A).comp includeRight = includeLeft := rfl

theorem adjoin_tmul_eq_top : adjoin R { t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t } = ⊤ :=
  top_le_iff.mp <| (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

end

section

variable {R A}

unseal mul in
theorem assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
    (TensorProduct.assoc R A B C) ((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) ⊗ₜ[R] (c₁ * c₂)) =
      (TensorProduct.assoc R A B C) (a₁ ⊗ₜ[R] b₁ ⊗ₜ[R] c₁) *
        (TensorProduct.assoc R A B C) (a₂ ⊗ₜ[R] b₂ ⊗ₜ[R] c₂) :=
  rfl

theorem assoc_aux_2 : (TensorProduct.assoc R A B C) (1 ⊗ₜ[R] 1 ⊗ₜ[R] 1) = 1 :=
  rfl

variable (R A C D)

/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : A ⊗[S] C ⊗[R] D ≃ₐ[S] A ⊗[S] (C ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S S A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

@[simp] theorem assoc_toLinearEquiv :
    (TensorProduct.assoc R S A C D).toLinearEquiv = AlgebraTensorModule.assoc R S S A C D := rfl

variable {A C D}

@[simp]
theorem assoc_tmul (a : A) (b : C) (c : D) :
    TensorProduct.assoc R S A C D ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl

@[simp]
theorem assoc_symm_tmul (a : A) (b : C) (c : D) :
    (TensorProduct.assoc R S A C D).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c := rfl

end

section

variable (T A B : Type*) [CommSemiring T] [CommSemiring A] [CommSemiring B]
  [Algebra R T] [Algebra R A] [Algebra R B] [Algebra T A] [IsScalarTower R T A] [Algebra S A]
  [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A]

/-- The natural isomorphism `A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B`. -/
def cancelBaseChange : A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp)

@[simp]
lemma cancelBaseChange_tmul (a : A) (s : S) (b : B) :
    Algebra.TensorProduct.cancelBaseChange R S T A B (a ⊗ₜ (s ⊗ₜ b)) = (s • a) ⊗ₜ b :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]
lemma cancelBaseChange_symm_tmul (a : A) (b : B) :
    (Algebra.TensorProduct.cancelBaseChange R S T A B).symm (a ⊗ₜ b) = a ⊗ₜ (1 ⊗ₜ b) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b

end

variable {R S A}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[S] C) (g : B →ₐ[R] D) : A ⊗[R] B →ₐ[S] C ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])

@[simp]
theorem map_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] D) (a : A) (b : B) : map f g (a ⊗ₜ b) = f a ⊗ₜ g b :=
  rfl

@[simp]
theorem map_id : map (.id S A) (.id R B) = .id S _ :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

theorem map_comp
    (f₂ : C →ₐ[S] E) (f₁ : A →ₐ[S] C) (g₂ : D →ₐ[R] F) (g₁ : B →ₐ[R] D) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

lemma map_id_comp (g₂ : D →ₐ[R] F) (g₁ : B →ₐ[R] D) :
    map (AlgHom.id S A) (g₂.comp g₁) = (map (AlgHom.id S A) g₂).comp (map (AlgHom.id S A) g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

lemma map_comp_id
    (f₂ : C →ₐ[S] E) (f₁ : A →ₐ[S] C) :
    map (f₂.comp f₁) (AlgHom.id R E) = (map f₂ (AlgHom.id R E)).comp (map f₁ (AlgHom.id R E)) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]
theorem map_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).comp includeLeft = includeLeft.comp f :=
  AlgHom.ext <| by simp

@[simp]
theorem map_restrictScalars_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    ((map f g).restrictScalars R).comp includeRight = includeRight.comp g :=
  AlgHom.ext <| by simp

@[simp]
theorem map_comp_includeRight (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (map f g).comp includeRight = includeRight.comp g :=
  map_restrictScalars_comp_includeRight f g

theorem map_range (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).range := by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul, ← mul_one (f a), ← one_mul (g b), ← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [← map_comp_includeLeft f g, ← map_comp_includeRight f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)

lemma comm_comp_map (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (TensorProduct.comm R C D : C ⊗[R] D →ₐ[R] D ⊗[R] C).comp (Algebra.TensorProduct.map f g) =
    (Algebra.TensorProduct.map g f).comp (TensorProduct.comm R A B).toAlgHom := by
  ext <;> rfl

lemma comm_comp_map_apply (f : A →ₐ[R] C) (g : B →ₐ[R] D) (x) :
    TensorProduct.comm R C D (Algebra.TensorProduct.map f g x) =
    (Algebra.TensorProduct.map g f) (TensorProduct.comm R A B x) :=
  congr($(comm_comp_map f g) x)

/-- Construct an isomorphism between tensor products of an S-algebra with an R-algebra
from S- and R- isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : A ⊗[R] B ≃ₐ[S] C ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)

@[simp] theorem congr_toLinearEquiv (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) :
    (Algebra.TensorProduct.congr f g).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr f.toLinearEquiv g.toLinearEquiv := rfl

@[simp]
theorem congr_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    congr f g x = (map (f : A →ₐ[S] C) (g : B →ₐ[R] D)) x :=
  rfl

@[simp]
theorem congr_symm_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : C →ₐ[S] A) (g.symm : D →ₐ[R] B)) x :=
  rfl

@[simp]
theorem congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl :=
  AlgEquiv.coe_algHom_injective <| map_id

theorem congr_trans
    (f₁ : A ≃ₐ[S] C) (f₂ : C ≃ₐ[S] E) (g₁ : B ≃ₐ[R] D) (g₂ : D ≃ₐ[R] F) :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  AlgEquiv.coe_algHom_injective <| map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom

theorem congr_symm (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : congr f.symm g.symm = (congr f g).symm := rfl

variable (R A B C) in
/-- Tensor product of algebras analogue of `mul_left_comm`.

This is the algebra version of `TensorProduct.leftComm`. -/
def leftComm : A ⊗[R] (B ⊗[R] C) ≃ₐ[R] B ⊗[R] (A ⊗[R] C) :=
  (Algebra.TensorProduct.assoc R R A B C).symm.trans <|
    (congr (Algebra.TensorProduct.comm R A B) .refl).trans <| TensorProduct.assoc R R B A C

@[simp]
theorem leftComm_tmul (m : A) (n : B) (p : C) :
    leftComm R A B C (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl

@[simp]
theorem leftComm_symm_tmul (m : A) (n : B) (p : C) :
    (leftComm R A B C).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
theorem leftComm_toLinearEquiv : ↑(leftComm R A B C) = _root_.TensorProduct.leftComm R A B C :=
  LinearEquiv.toLinearMap_injective (by ext; rfl)

variable [CommSemiring T] [Algebra R T] [Algebra T A] [IsScalarTower R T A] [SMulCommClass S T A]
  [Algebra S T] [IsScalarTower S T A] [CommSemiring R'] [Algebra R R'] [Algebra R' T] [Algebra R' A]
  [Algebra R' B] [IsScalarTower R R' A] [SMulCommClass S R' A] [SMulCommClass R' S A]
  [IsScalarTower R' T A] [IsScalarTower R R' B]

variable (R R' S T A B C D) in
/-- Tensor product of algebras analogue of `mul_mul_mul_comm`.

This is the algebra version of `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`. -/
def tensorTensorTensorComm : A ⊗[R'] B ⊗[S] (C ⊗[R] D) ≃ₐ[T] A ⊗[S] C ⊗[R'] (B ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D)
    rfl (LinearMap.map_mul_iff _ |>.mpr <| by ext; simp)

@[simp]
theorem tensorTensorTensorComm_tmul (m : A) (n : B) (p : C) (q : D) :
    tensorTensorTensorComm R R' S T A B C D (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
theorem tensorTensorTensorComm_symm_tmul (m : A) (n : C) (p : B) (q : D) :
    (tensorTensorTensorComm R R' S T A B C D).symm (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R R' S T A B C D).symm = tensorTensorTensorComm R S R' T A C B D := by
  ext; rfl

theorem tensorTensorTensorComm_toLinearEquiv :
    (tensorTensorTensorComm R R' S T A B C D).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D := rfl

@[simp]
theorem toLinearEquiv_tensorTensorTensorComm :
    (tensorTensorTensorComm R R R R A B C D).toLinearEquiv =
      _root_.TensorProduct.tensorTensorTensorComm R A B C D := by
  apply LinearEquiv.toLinearMap_injective
  ext; simp

lemma map_bijective {f : A →ₐ[R] B} {g : C →ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  _root_.TensorProduct.map_bijective hf hg

lemma includeLeft_bijective (h : Function.Bijective (algebraMap R B)) :
    Function.Bijective (includeLeft : A →ₐ[S] A ⊗[R] B) := by
  have : (includeLeft : A →ₐ[S] A ⊗[R] B).comp (TensorProduct.rid R S A).toAlgHom =
      map (.id S A) (Algebra.ofId R B) := by ext; simp
  rw [← Function.Bijective.of_comp_iff _ (TensorProduct.rid R S A).bijective]
  convert_to Function.Bijective (map (.id R A) (Algebra.ofId R B))
  · exact DFunLike.coe_fn_eq.mpr this
  · exact Algebra.TensorProduct.map_bijective Function.bijective_id h

lemma includeRight_bijective (h : Function.Bijective (algebraMap R A)) :
    Function.Bijective (includeRight : B →ₐ[R] A ⊗[R] B) := by
  rw [← Function.Bijective.of_comp_iff' (TensorProduct.comm R A B).bijective]
  exact Algebra.TensorProduct.includeLeft_bijective (S := R) h

end

end Monoidal


section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/-- If `A`, `B`, `C` are `R`-algebras, `A` and `C` are also `S`-algebras (forming a tower as
`·/S/R`), then the product map of `f : A →ₐ[S] C` and `g : B →ₐ[R] C` is an `S`-algebra
homomorphism.

This is just a special case of `Algebra.TensorProduct.lift` for when `C` is commutative. -/
abbrev productLeftAlgHom (f : A →ₐ[S] C) (g : B →ₐ[R] C) : A ⊗[R] B →ₐ[S] C :=
  lift f g (fun _ _ => Commute.all _ _)

lemma tmul_one_eq_one_tmul (r : R) : algebraMap R A r ⊗ₜ[R] 1 = 1 ⊗ₜ algebraMap R B r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

end

section

variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]
variable [Algebra R A] [Algebra R B] [Algebra R S]
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)
variable (R)

/-- `LinearMap.mul'` as an `AlgHom` over the algebra. -/
def lmul'' : S ⊗[R] S →ₐ[S] S :=
  algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x ↦ x.induction_on (by simp)
        (fun _ _ ↦ by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy ↦ by simp_all [mul_add] }
    (fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) <| by simp

theorem lmul''_eq_lid_comp_mapOfCompatibleSMul :
    lmul'' R = (TensorProduct.lid S S).toAlgHom.comp (mapOfCompatibleSMul' _ _ _ _) := by
  ext; rfl

/-- `LinearMap.mul'` as an `AlgHom` over the base ring. -/
def lmul' : S ⊗[R] S →ₐ[R] S := (lmul'' R).restrictScalars R

variable {R}

theorem lmul'_toLinearMap : (lmul' R : _ →ₐ[R] S).toLinearMap = LinearMap.mul' R S :=
  rfl

@[simp]
theorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=
  rfl

@[simp]
theorem lmul'_comp_includeLeft : (lmul' R : _ →ₐ[R] S).comp includeLeft = AlgHom.id R S :=
  AlgHom.ext <| mul_one

@[simp]
theorem lmul'_comp_includeRight : (lmul' R : _ →ₐ[R] S).comp includeRight = AlgHom.id R S :=
  AlgHom.ext <| one_mul

lemma lmul'_comp_map (f : A →ₐ[R] S) (g : B →ₐ[R] S) :
    (lmul' R).comp (map f g) = lift f g (fun _ _ ↦ .all _ _) := by ext <;> rfl

variable (R S) in
/-- If multiplication by elements of S can switch between the two factors of `S ⊗[R] S`,
then `lmul''` is an isomorphism. -/
def lmulEquiv [CompatibleSMul R S S S] : S ⊗[R] S ≃ₐ[S] S :=
  .ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft <| AlgHom.ext fun x ↦ x.induction_on
    (by simp) (fun x y ↦ show (x * y) ⊗ₜ[R] 1 = x ⊗ₜ[R] y by
      rw [mul_comm, ← smul_eq_mul, smul_tmul, smul_eq_mul, mul_one])
    fun _ _ hx hy ↦ by simp_all [add_tmul]

theorem lmulEquiv_eq_lidOfCompatibleSMul [CompatibleSMul R S S S] :
    lmulEquiv R S = lidOfCompatibleSMul R S S :=
  AlgEquiv.coe_algHom_injective <| by ext; rfl

/-- If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.

This is a special case of `Algebra.TensorProduct.productLeftAlgHom` for when the two base rings are
the same.
-/
def productMap : A ⊗[R] B →ₐ[R] S := productLeftAlgHom f g

theorem productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.map f g) := by
  ext <;> rfl

@[simp]
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := rfl

theorem productMap_left_apply (a : A) : productMap f g (a ⊗ₜ 1) = f a := by
  simp

@[simp]
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

theorem productMap_right_apply (b : B) :
    productMap f g (1 ⊗ₜ b) = g b := by simp

@[simp]
theorem productMap_right : (productMap f g).comp includeRight = g :=
  lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap_eq_comp_map, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp,
    ← AlgHom.range_comp,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, lmul'_comp_includeLeft, lmul'_comp_includeRight,
    AlgHom.id_comp, AlgHom.id_comp]

end

end TensorProduct

end Algebra

namespace LinearMap

variable (R A M N : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Module
open scoped TensorProduct

/-- The natural linear map $A ⊗ \text{Hom}_R(M, N) → \text{Hom}_A (M_A, N_A)$,
where $M_A$ and $N_A$ are the respective modules over $A$ obtained by extension of scalars.

See `LinearMap.tensorProductEnd` for this map specialized to endomorphisms,
and bundled as `A`-algebra homomorphism. -/
@[simps!]
def tensorProduct : A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) :=
  TensorProduct.AlgebraTensorModule.lift <|
  { toFun := fun a ↦ a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

/-- The natural `A`-algebra homomorphism $A ⊗ (\text{End}_R M) → \text{End}_A (A ⊗ M)$,
where `M` is an `R`-module, and `A` an `R`-algebra. -/
@[simps!]
def tensorProductEnd : A ⊗[R] (End R M) →ₐ[A] End A (A ⊗[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g ↦ by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, Module.End.mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, Module.End.one_eq_id,
        lTensor_id, LinearMap.id_apply])

end LinearMap

namespace Module

variable {R S A M N : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [Module R M] [Module S M] [Module A M] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S M]

/-- The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` to
the `TensorProduct.map f g`, the tensor product of the two maps.

This is an `AlgHom` version of `TensorProduct.AlgebraTensorModule.homTensorHomMap`. Like that
definition, this is generalized across many different rings; namely a tower of algebras `A/S/R`. -/
def endTensorEndAlgHom : End A M ⊗[R] End R N →ₐ[S] End A (M ⊗[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)

theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f ⊗ₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl

end Module
