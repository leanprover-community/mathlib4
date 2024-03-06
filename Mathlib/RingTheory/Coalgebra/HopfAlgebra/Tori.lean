import Mathlib.RingTheory.Coalgebra.HopfAlgebra.Cat
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Coalgebra.HopfAlgebra.Gm
import Mathlib.RingTheory.Coalgebra.HopfAlgebra.Monoidal
import Mathlib.RingTheory.Coalgebra.Bialgebra.ChangeOfRings
universe v u
set_option autoImplicit false
section Split
open scoped AddMonoidAlgebra LaurentPolynomial
section

variable (R : Type u) [CommSemiring R] (A : Type v) [Semiring A] [HopfAlgebra R A]

abbrev rankNSplitTorus (n : ℕ) :=
  AddMonoidAlgebra R (Fin n → ℤ)

class IsRankNSplitTorus (n : ℕ) : Prop where
  out : Nonempty (A ≃b[R] rankNSplitTorus R n)

noncomputable def IsRankNSplitTorus.equivSplit (n : ℕ) [IsRankNSplitTorus R A n] :
    A ≃b[R] rankNSplitTorus R n :=
  Classical.choice IsRankNSplitTorus.out

class IsSplitTorus : Prop where
  out : ∃ n, IsRankNSplitTorus R A n

def isSplitTorusOfRank (n : ℕ) [IsRankNSplitTorus R A n] :
  IsSplitTorus R A := ⟨n, by infer_instance⟩

noncomputable def IsSplitTorus.rank [IsSplitTorus R A] : ℕ :=
  Classical.choose (IsSplitTorus.out (R := R) (A := A))

instance [IsSplitTorus R A] : IsRankNSplitTorus R A (IsSplitTorus.rank R A) :=
  Classical.choose_spec (IsSplitTorus.out (R := R) (A := A))

noncomputable def IsSplitTorus.equivSplit [IsSplitTorus R A] :
    A ≃b[R] rankNSplitTorus R (IsSplitTorus.rank R A) :=
  IsRankNSplitTorus.equivSplit R A _

end

open scoped TensorProduct

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] (A : Type u) [Ring A] [HopfAlgebra R A]

class IsRankNSplitOver (n : ℕ) extends IsRankNSplitTorus S (S ⊗[R] A) n : Prop

class IsSplitOver extends IsSplitTorus S (S ⊗[R] A) : Prop

def isSplitOverOfRank (n : ℕ) [IsRankNSplitOver R S A n] :
    IsSplitOver R S A where
  out := ⟨n, by infer_instance⟩

def IsRankNSplitOver.ofIsScalarTower (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] (n : ℕ) [IsRankNSplitOver R S A n] :
  IsRankNSplitOver R S' A n := sorry

def IsSplitOver.ofIsScalarTower (S' : Type u) [CommRing S'] [Algebra R S']
    [Algebra S S'] [IsScalarTower R S S'] [IsSplitOver R S A] :
  IsSplitOver R S' A := sorry

variable (k : Type u) [Field k] (X : Type u) [Ring X] [HopfAlgebra k X]

class IsRankNAlgebraicTorus (n : ℕ) extends
    IsRankNSplitOver k (AlgebraicClosure k) X n

class IsAlgebraicTorus extends IsSplitOver k (AlgebraicClosure k) X

def IsRankNAlgebraicTorus.ofIsAlgClosure (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] (n : ℕ)
    [IsRankNSplitOver k K X n] : IsRankNAlgebraicTorus k X n := sorry

def IsAlgebraicTorus.ofIsAlgClosure (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] (n : ℕ)
    [IsSplitOver k K X] : IsAlgebraicTorus k X := sorry

instance (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] (n : ℕ)
    [IsRankNAlgebraicTorus k X n] : IsRankNSplitOver k K X n := sorry

instance (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    [IsAlgebraicTorus k X] : IsSplitOver k K X := sorry

section hmmm

variable (F K A : Type*) [Field F] [Field K] [Algebra F K] [CommRing A] [Algebra F A]

theorem Module.Flat.iff_rTensor_injective''
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Flat R M ↔ ∀ {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N]
      [Module R P] (f : N →ₗ[R] P) (hf : Function.Injective f),
      Function.Injective (f.rTensor M) := sorry

instance : Algebra.Flat F A := ⟨Module.Flat.of_free F A⟩

/- need Stacks 00QP -/

end hmmm
noncomputable section lol
section
variable (R A B α : Type*) [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B]
open TensorProduct

def finsuppTensorLeft :
    (α →₀ A) ⊗[R] B ≃ₗ[R] α →₀ A ⊗[R] B :=
  TensorProduct.congr (LinearEquiv.refl _ _)
    (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm ≪≫ₗ
  finsuppTensorFinsupp R A B α Unit ≪≫ₗ
  Finsupp.domLCongr (Equiv.prodUnique α Unit)

def finsuppTensorRight :
    A ⊗[R] (α →₀ B) ≃ₗ[R] α →₀ A ⊗[R] B :=
  TensorProduct.congr (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm
    (LinearEquiv.refl _ _) ≪≫ₗ
  finsuppTensorFinsupp R A B Unit α ≪≫ₗ
  Finsupp.domLCongr (Equiv.uniqueProd α Unit)

variable {R A B α}
open Finsupp
@[simp] lemma finsuppTensorLeft_tmul_single
    (a : α) (x : A) (y : B) :
    finsuppTensorLeft R A B α (Finsupp.single a x ⊗ₜ y) =
      Finsupp.single a (x ⊗ₜ y) := by
    simp only [finsuppTensorLeft, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply,
      LinearEquiv.finsuppUnique_symm_apply, PUnit.default_eq_unit, finsuppTensorFinsupp_single,
      domLCongr_apply, domCongr_apply, equivMapDomain_single, Equiv.coe_prodUnique]

@[simp] lemma finsuppTensorLeft_symm_single_tmul
    (a : α) (x : A) (y : B) :
    (finsuppTensorLeft R A B α).symm (Finsupp.single a (x ⊗ₜ y)) =
      Finsupp.single a x ⊗ₜ y := by
  simp only [finsuppTensorLeft, LinearEquiv.trans_symm, domLCongr_symm, LinearEquiv.trans_apply,
    domLCongr_apply, domCongr_apply, equivMapDomain_single, Equiv.prodUnique_symm_apply,
    PUnit.default_eq_unit, finsuppTensorFinsupp_symm_single, congr_symm_tmul, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, LinearEquiv.symm_symm, LinearEquiv.finsuppUnique_apply, single_eq_same]

@[simp] lemma finsuppTensorRight_tmul_single
    (a : α) (x : A) (y : B) :
    finsuppTensorRight R A B α (x ⊗ₜ Finsupp.single a y) =
      Finsupp.single a (x ⊗ₜ y) := by
    simp only [finsuppTensorRight, LinearEquiv.trans_apply, congr_tmul,
      LinearEquiv.finsuppUnique_symm_apply, PUnit.default_eq_unit, LinearEquiv.refl_apply,
      finsuppTensorFinsupp_single, domLCongr_apply, domCongr_apply, equivMapDomain_single,
      Equiv.coe_uniqueProd]

@[simp] lemma finsuppTensorRight_symm_single_tmul
    (a : α) (x : A) (y : B) :
    (finsuppTensorRight R A B α).symm (Finsupp.single a (x ⊗ₜ y)) =
      x ⊗ₜ Finsupp.single a y := by
  simp only [finsuppTensorRight, LinearEquiv.trans_symm, domLCongr_symm, LinearEquiv.trans_apply,
    domLCongr_apply, domCongr_apply, equivMapDomain_single, Equiv.uniqueProd_symm_apply,
    PUnit.default_eq_unit, finsuppTensorFinsupp_symm_single, congr_symm_tmul, LinearEquiv.symm_symm,
    LinearEquiv.finsuppUnique_apply, single_eq_same, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
end

end lol
section Action
variable (F : Type u) [Field F] (A : Type u) [CommRing A] [HopfAlgebra F A]

open Field
local notation "G_F" => absoluteGaloisGroup F
local notation "Fbar" => AlgebraicClosure F
