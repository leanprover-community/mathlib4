import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.QuotientNoetherian

variable (R A : Type*) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]

local notation:max R"[" S "]" => (Algebra.adjoin R (S : Finset A) : Subalgebra R A)

section

variable {R A}

lemma Algebra.adjoin_isNoetherian (S : Finset A) :
    IsNoetherianRing R[S] := by
  let P := (MvPolynomial S R)
  haveI : IsNoetherianRing P := MvPolynomial.isNoetherianRing
  have eq1 : (MvPolynomial.aeval Subtype.val).range = R[S] := adjoin_eq_range R S.toSet |>.symm
  have eq2 : (MvPolynomial.aeval Subtype.val : P →ₐ[R] A).toRingHom.range = R[S].toSubring
  · ext a
    simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_range, RingHom.coe_coe,
      Subalgebra.mem_toSubring]
    rw [← eq1]
    simp only [AlgHom.mem_range]
    rfl
  have eq3 := RingHom.quotientKerEquivRange (MvPolynomial.aeval Subtype.val : P →ₐ[R] A).toRingHom
  rw [eq2] at eq3
  exact isNoetherianRing_of_ringEquiv (f := eq3)

end

section

variable [DecidableEq A]
variable (S : Finset A) (s : A) (hS : Algebra.adjoin R (insert s S) = (⊤ : Subalgebra R A))
variable (M : Type*) [AddCommMonoid M] [Module A M]

instance : IsNoetherianRing R[S] :=
  Algebra.adjoin_isNoetherian (R := R) S

instance : Module R[S] M :=
Module.compHom M ({
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := by intros; rfl
  map_zero' := rfl
  map_add' := by intros; rfl
} : R[S] →+* A)

lemma Algebra.adjoin_smul_def (a : R[S]) (m : M) : a • m = (a : A) • m := rfl

instance : Algebra A R[insert s S] :=
  RingHom.toAlgebra
  { toFun := fun a ↦ ⟨a,  sorry⟩
    map_one' := by sorry
    map_mul' := by sorry
    map_zero' := by sorry
    map_add' := by sorry }

instance :  IsScalarTower A R[insert s S] M where
  smul_assoc a x m := show (a • (x : A)) • m = a • (x : A) • m from smul_assoc _ _ _

instance [Module.Finite A M] : Module.Finite R[insert s S] M :=
  Module.Finite.of_restrictScalars_finite (R := A) (A := R[insert s S]) _

example (ann : ∀ (m : M), s • m = 0) : Algebra A R[S] :=
  RingHom.toAlgebra
  { toFun := fun a ↦ ⟨a,  sorry⟩
    map_one' := by sorry
    map_mul' := by sorry
    map_zero' := by sorry
    map_add' := by sorry }


lemma Algebra.adjoin_module_finite_of_annihilating [Module.Finite A M]
  (ann : ∀ (m : M), s • m = 0) : Module.Finite R[S] M := sorry


end
