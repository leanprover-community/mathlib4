import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Aesop


open MvPolynomial RingQuot

noncomputable section
universe u
variable (R L : Type u) {RL : Type u} [CommRing R]
         [AddCommMonoid L] [Module R L]
         [CommRing RL] [Algebra R RL]

         {L' : Type u} [CommRing L'] [Algebra R L']
local notation "ι" => TensorAlgebra.ι R

inductive SymRel : (TensorAlgebra R L) → (TensorAlgebra R L) → Prop where
  | mul_comm (x y : L) : SymRel (ι x * ι y) (ι y * ι x)


abbrev SymmetricAlgebra := RingQuot (SymRel R L)


variable {R} {L} in
structure IsSymmetricAlgebra (iota : L →ₗ[R] RL) : Prop where
  ex_map {A : Type u} [CommRing A] [Algebra R A] (φ : L →ₗ[R] A)
    : ∃! φ' : RL →ₐ[R] A, φ = φ'.toLinearMap ∘ₗ iota



local notation "𝔖" => SymmetricAlgebra


namespace SymmetricAlgebra

instance : CommRing (𝔖 R L) where
  mul_comm a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => by
      apply Quot.ind _ a; apply Quot.ind _ b; intro a b;
      rw [mul_quot, mul_quot]
      suffices h : ∀ (x : TensorAlgebra R L),
      (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * a)⟩ : (RingQuot (SymRel R L))) =
       ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (a * x)⟩ by
        exact (h b)
      let P : TensorAlgebra R L → TensorAlgebra R L → Prop :=
       fun x y ↦ (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * y)⟩ : (RingQuot (SymRel R L))) =
        ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (y * x)⟩
      have P_smul (r : R) (x : TensorAlgebra R L) : P x (algebraMap R (TensorAlgebra R L) r) := by
        unfold P; rw [Algebra.commutes]
      have P_mul (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x * y) := by
        unfold P at h1 h2 ⊢
        rw [← mul_quot, ← mul_quot, ← mul_quot, ← mul_quot,
            ← mul_assoc, mul_quot, h1, ← mul_quot, mul_assoc, mul_quot, h2, ← mul_quot, mul_assoc]
      have P_add (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x + y) := by
        unfold P at h1 h2 ⊢
        rw [mul_add, add_mul, ← add_quot, ← add_quot, h1, h2]
      have P_symm {x y : TensorAlgebra R L} (h : P x y) : P y x := h.symm
      have P_base (x y : L) : P (ι x) (ι y) := by
        unfold P
        rw [Quot.sound (Rel.of (SymRel.mul_comm x y))]
      apply TensorAlgebra.induction (C := fun y ↦ ∀ (x : TensorAlgebra R L), P x y) _ _ _ _ a
      · intro r; exact P_smul r
      · intro x; apply TensorAlgebra.induction
        · intro r; exact P_symm (P_smul r (ι x))
        · intro y; exact P_base y x
        · intro a1 a2 h1 h2; exact P_symm (P_mul a1 a2 (ι x) (P_symm h1) (P_symm h2))
        · intro a1 a2 h1 h2; exact P_symm (P_add a1 a2 (ι x) (P_symm h1) (P_symm h2))
      · intro a1 a2 h1 h2 x; exact P_mul a1 a2 x (h1 x) (h2 x)
      · intro a1 a2 h1 h2 x; exact P_add a1 a2 x (h1 x) (h2 x)


abbrev mkAlgHom : TensorAlgebra R L →ₐ[R] 𝔖 R L := RingQuot.mkAlgHom R (SymRel R L)

def iota : L →ₗ[R] 𝔖 R L := (mkAlgHom R L).toLinearMap.comp (TensorAlgebra.ι R (M := L))

end SymmetricAlgebra

namespace IsSymmetricAlgebra
/-
This says that the symmetric algebra over R of the zero module
(here defined as any module which has at most one element) must be isomorphic
as an R algebra to R.
-/
def baseRingOfZeroModule (hm : Subsingleton L) :
   IsSymmetricAlgebra (R := R) (L := L) (RL := R) 0 where
    ex_map := by
      intro a b c φ
      have hφ : φ = 0 := by exact Subsingleton.eq_zero φ
      let φ' : R →ₐ[R] a := Algebra.ofId R a
      use φ'
      constructor
      · rw [hφ]
        ext x
        simp only [LinearMap.zero_apply, LinearMap.comp_zero]
      ·  intro ψ hψ
         exact Algebra.ext_id_iff.mpr trivial

open SymmetricAlgebra in
def SymmetricAlgebra.isSymmetricAlgebra : IsSymmetricAlgebra (iota R L) where
  ex_map := by
    intro alg com halg φ
    let tensorphi : TensorAlgebra R L →ₐ[R] alg := TensorAlgebra.lift R φ

    let res : ∀ ⦃x y : TensorAlgebra R L⦄, SymRel R L x y → tensorphi x = tensorphi y := by
        intro x y h
        induction h
        case mul_comm x y =>
          simp only [map_mul]
          rw [@NonUnitalCommSemiring.mul_comm]

    use (RingQuot.liftAlgHom (S := R) (s := SymRel R L) (B := alg)) ⟨TensorAlgebra.lift R φ, res⟩
    constructor
    · unfold iota
      have teneq := TensorAlgebra.lift.eq_1 (M := L) (A := alg) R
      have quoteq := RingQuot.eq_liftAlgHom_comp_mkAlgHom R (TensorAlgebra.lift R φ)
      ext a
      simp
    · intro a b
      apply RingQuot.liftAlgHom_unique
      exact
        (TensorAlgebra.lift_unique φ (a.comp (RingQuot.mkAlgHom R (SymRel R L)))).mp
          (id (Eq.symm b))

--variable {R L}
variable {L}

/-
{M M' : Type u} [AddCommMonoid M] [Module R M]
         {RM : Type u}
         [CommRing RM] [Algebra R RM] [CommRing M'] [Algebra R M']
-/
 def lift {iM : L →ₗ[R] RL} (salg : IsSymmetricAlgebra iM) (phi : L →ₗ[R] L') : RL →ₐ[R] L' :=
  (salg.ex_map phi).choose


theorem lift_spec {iM : L →ₗ[R] RL} (salg : IsSymmetricAlgebra iM) (phi : L →ₗ[R] L') :
         phi = (lift R salg phi).toLinearMap ∘ₗ iM := by
  exact (salg.ex_map phi).choose_spec.1

theorem comp_spec {M : Type u} [AddCommMonoid M] [Module R M]
         {RM RM' : Type u}
         [CommRing RM] [Algebra R RM] [CommRing RM'] [Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M →ₗ[R] RM'}
         (salg : IsSymmetricAlgebra iM) (salg' : IsSymmetricAlgebra iM') :
  iM = ((AlgHom.comp (lift _ salg' iM) (lift _ salg iM')).toLinearMap) ∘ₗ iM := by
  rw [AlgHom.comp_toLinearMap]
  rw [LinearMap.comp_assoc]
  rw [← lift_spec _ salg iM']
  exact lift_spec _ salg' iM

def isomorphismInvariant {M : Type u} [AddCommMonoid M] [Module R M]
         {RM RM' : Type u}
         [CommRing RM] [Algebra R RM] [CommRing RM'] [Algebra R RM']
         {iM : M →ₗ[R] RM} {iM' : M →ₗ[R] RM'}
         (salg : IsSymmetricAlgebra iM) (salg' : IsSymmetricAlgebra iM')
         : RM ≃ₐ[R] RM' where
    toFun : RM →ₐ[R] RM' := lift R salg iM'
    invFun : RM' →ₐ[R] RM := lift R salg' iM

    left_inv := by
      rw [@Function.leftInverse_iff_comp]
      let φ := lift R salg iM'
      let ψ := lift R salg' iM

      have h1 : iM' = φ ∘ₗ iM := (salg.ex_map iM').choose_spec.1
      have h2 : iM = ψ ∘ₗ iM' := (salg'.ex_map iM).choose_spec.1
      have h3 : ((AlgHom.comp ψ φ).toLinearMap) ∘ iM = (AlgHom.id R RM).toLinearMap ∘ₗ iM := by
        nth_rw 2 [h2]
        rw [h1]
        simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.toLinearMap_id,
          LinearMap.id_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom]
        exact rfl

      have comp_spec := comp_spec _ salg salg'

      have prop1 : iM = (AlgHom.comp ψ φ).toLinearMap ∘ₗ iM := by exact comp_spec
      have prop2 : iM = (AlgHom.id R RM).toLinearMap ∘ₗ iM := by exact rfl



      have h_unique := (salg.ex_map iM).unique prop1 prop2

      have eq: (AlgHom.comp ψ φ) = (AlgHom.id R RM) := by exact h_unique
      unfold φ ψ at eq
      have : (AlgHom.id R RM) = (id : RM → RM) := by rfl
      have this1 : ⇑(lift R salg' iM) ∘ ⇑(lift R salg iM') = (AlgHom.comp ψ φ) := by rfl
      rw [←this, this1, eq]

    right_inv := by
      rw [@Function.rightInverse_iff_comp]
      let φ := lift R salg iM'
      let ψ := lift R salg' iM
      have h1 : iM' = φ ∘ₗ iM := (salg.ex_map iM').choose_spec.1
      have h2 : iM = ψ ∘ₗ iM' := (salg'.ex_map iM).choose_spec.1
      have h3 : ((AlgHom.comp φ ψ).toLinearMap) ∘ iM' = (AlgHom.id R RM').toLinearMap ∘ₗ iM' := by
        nth_rw 2 [h1]
        rw [h2]
        simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.toLinearMap_id,
          LinearMap.id_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom]
        rfl

      have comp_spec := comp_spec _ salg' salg

      have prop1 : iM' = (AlgHom.comp φ ψ).toLinearMap ∘ₗ iM' := by exact comp_spec
      have prop2 : iM' = (AlgHom.id R RM').toLinearMap ∘ₗ iM' := by exact rfl


      have h_unique := (salg'.ex_map iM').unique prop1 prop2

      have eq: (AlgHom.comp φ ψ) = (AlgHom.id R RM') := by exact h_unique
      unfold φ ψ at eq
      have : (AlgHom.id R RM') = (id : RM' → RM') := by rfl
      have this1 : ⇑(lift R salg iM') ∘ ⇑(lift R salg' iM) = (AlgHom.comp φ ψ) := by rfl
      rw [←this, this1, eq]
    map_mul' := by simp only [map_mul, implies_true]
    map_add' := by simp only [map_add, implies_true]
    commutes' := by simp only [AlgHom.commutes, implies_true]



open TensorProduct

def symalgOfProductOfTensorProduct {M₁ M₂ : Type u}
            [AddCommMonoid M₁] [Module R M₁]
            [AddCommMonoid M₂] [Module R M₂]
         {RM RM₁ RM₂ : Type u}
         [CommRing RM] [Algebra R RM] [CommRing RM₁] [Algebra R RM₁]
         [CommRing RM₂] [Algebra R RM₂]
         {iM : M₁ × M₂ →ₗ[R] RM} {iM₁ : M₁ →ₗ[R] RM₁} {iM₂ : M₂ →ₗ[R] RM₂}
         (salg₁ : IsSymmetricAlgebra iM₁) (salg₂ : IsSymmetricAlgebra iM₂)
         : RM₁ ⊗[R] RM₂ →ₐ[R] RM := by
  let φ₁ : M₁ →ₗ[R] RM := LinearMap.comp iM (LinearMap.prod LinearMap.id 0)
  let φ₂ : M₂ →ₗ[R] RM := LinearMap.comp iM (LinearMap.prod 0 LinearMap.id)

  let φ₁_alg : RM₁ →ₐ[R] RM := (salg₁.ex_map φ₁).exists.choose
  let φ₂_alg : RM₂ →ₐ[R] RM := (salg₂.ex_map φ₂).exists.choose

  let bilin_map : RM₁ →ₗ[R] RM₂ →ₗ[R] RM := by
    refine LinearMap.mk₂ R (fun x y => φ₁_alg x * φ₂_alg y) ?_ ?_ ?_ ?_
    · intros x y z
      simp only [map_add]
      exact RightDistribClass.right_distrib (φ₁_alg x) (φ₁_alg y) (φ₂_alg z)
    · intros r x y
      simp [Algebra.smul_def, mul_assoc]
    · intros x y z
      simp [add_mul]
      exact LeftDistribClass.left_distrib (φ₁_alg x) (φ₂_alg y) (φ₂_alg z)
    · intros r x y
      simp [Algebra.smul_def, mul_assoc]
      exact Algebra.left_comm (φ₁_alg x) r (φ₂_alg y)
  let lin_map : RM₁ ⊗[R] RM₂ →ₗ[R] RM := TensorProduct.lift bilin_map
  exact Algebra.TensorProduct.productMap φ₁_alg φ₂_alg




variable (I : Type u) (basis_I : Basis I R L)

def basisToPoly : L →ₗ[R] MvPolynomial I R :=
    Basis.constr basis_I R (fun i ↦ MvPolynomial.X i)

/--
Given a basis I of an R-module L, the polynomial ring with variables generated by the elements
of I satisfies the universal property of a symmetric algebra of L
-/
theorem mvPolynomial : IsSymmetricAlgebra (basisToPoly R I basis_I) where
  ex_map := by
    intro alg b c φ
    simp[basisToPoly]

    use MvPolynomial.aeval (R := R) (fun i => φ (basis_I i))
    constructor
    · apply Basis.ext basis_I
      intro i
      simp

    · simp
      intro f hf
      apply MvPolynomial.algHom_ext
      intro i
      simp only [aeval_X]
      rw [hf]
      simp only [LinearMap.coe_comp, LieHom.coe_toLinearMap, AlgHom.coe_toLieHom,
        Function.comp_apply, Basis.constr_basis]
      simp only [AlgHom.toLinearMap_apply]
