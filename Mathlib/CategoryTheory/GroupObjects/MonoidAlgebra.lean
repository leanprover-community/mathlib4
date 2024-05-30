import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.HopfAlgebra

noncomputable section
variable {R A X : Type*} [CommSemiring R]

namespace MonoidAlgebra

section
variable [Semiring A] [Module R A]

def lsingle (i : X) : A →ₗ[R] MonoidAlgebra A X :=
  Finsupp.lsingle i

lemma lsingle_def (i : X) :
    lsingle (R := R) (A := A) i = Finsupp.lsingle i := rfl

lemma lsingle_apply (i : X) (a : A) :
    lsingle (R := R) i a = single i a := rfl

@[ext]
theorem lhom_ext {B : Type*} [AddCommMonoid B] [Module R B]
    {f g : MonoidAlgebra A X →ₗ[R] B}
    (h : ∀ a b, f (single a b) = g (single a b)) : f = g :=
  Finsupp.lhom_ext h

variable [Coalgebra R A]

variable (R X A) in
instance instCoalgebra : Coalgebra R (MonoidAlgebra A X) := Finsupp.instCoalgebra R X A

@[simp]
lemma counit_single (x : X) (a : A) :
    Coalgebra.counit (MonoidAlgebra.single x a) = Coalgebra.counit (R := R) a :=
  Finsupp.counit_single _ _ _ _ _

@[simp]
lemma comul_single (x : X) (a : A) :
    Coalgebra.comul (MonoidAlgebra.single x a)
      = (TensorProduct.map (lsingle x) (lsingle x) : _ →ₗ[R] _)
      (Coalgebra.comul a) := Finsupp.comul_single _ _ _ _ _

end

variable [Ring A]

variable (R A X) in
instance instBialgebra [Bialgebra R A] [Monoid X] : Bialgebra R (MonoidAlgebra A X) :=
  { instCoalgebra R A X with
    counit_one := by
      simp only [one_def, counit_single, Bialgebra.counit_one]
    mul_compr₂_counit := lhom_ext fun a b => lhom_ext fun c d => by
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', single_mul_single, counit_single,
        Bialgebra.counit_mul, LinearMap.compl₁₂_apply]
    comul_one := by
      simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        TensorProduct.map_tmul, lsingle_apply]
    mul_compr₂_comul := lhom_ext fun a b => lhom_ext fun c d => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul d) with ⟨t, ht⟩
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', single_mul_single, comul_single,
        Bialgebra.comul_mul, hs, ht, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        map_sum, TensorProduct.map_tmul, lsingle_apply, LinearMap.compl₁₂_apply,
        LinearMap.coeFn_sum, Finset.sum_apply, Finset.sum_comm (s := s)] }

variable (R A X) in
def antipode [HopfAlgebra R A] [Group X] :
    MonoidAlgebra A X →ₗ[R] MonoidAlgebra A X :=
  Finsupp.lsum R fun g => Finsupp.lsingle g⁻¹ ∘ₗ HopfAlgebra.antipode

@[simp]
lemma antipode_single  [HopfAlgebra R A] [Group X] (g : X) (a : A) :
    antipode R A X (single g a)
      = single g⁻¹ (HopfAlgebra.antipode (R := R) a) := by
  simp only [MonoidAlgebra, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

@[simps!]
instance instHopfAlgebra [HopfAlgebra R A] [Group X] : HopfAlgebra R (MonoidAlgebra A X) :=
  { instBialgebra R A X with
    antipode := antipode R A X
    mul_antipode_rTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.rTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, mul_left_inv, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (R := R), ← map_sum (lsingle (R := R) (1 : X)),
        HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (repr := hs)]
    mul_antipode_lTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.lTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, mul_right_inv, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (R := R), ← map_sum (lsingle (R := R) (1 : X)),
        HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (repr := hs)] }

end MonoidAlgebra

namespace AddMonoidAlgebra

section
variable [Semiring A] [Module R A]

def lsingle (i : X) : A →ₗ[R] AddMonoidAlgebra A X :=
  Finsupp.lsingle i

lemma lsingle_def (i : X) :
    lsingle (R := R) (A := A) i = Finsupp.lsingle i := rfl

lemma lsingle_apply (i : X) (a : A) :
    lsingle (R := R) i a = single i a := rfl

@[ext]
theorem lhom_ext {B : Type*} [AddCommMonoid B] [Module R B]
    {f g : AddMonoidAlgebra A X →ₗ[R] B}
    (h : ∀ a b, f (single a b) = g (single a b)) : f = g :=
  Finsupp.lhom_ext h

variable [Coalgebra R A]

variable (R X A) in
instance instCoalgebra : Coalgebra R (AddMonoidAlgebra A X) := Finsupp.instCoalgebra R X A

@[simp]
lemma counit_single (x : X) (a : A) :
    Coalgebra.counit (AddMonoidAlgebra.single x a) = Coalgebra.counit (R := R) a :=
  Finsupp.counit_single _ _ _ _ _

@[simp]
lemma comul_single (x : X) (a : A) :
    Coalgebra.comul (AddMonoidAlgebra.single x a)
      = (TensorProduct.map (lsingle x) (lsingle x) : _ →ₗ[R] _)
      (Coalgebra.comul a) := Finsupp.comul_single _ _ _ _ _

end

variable [Ring A]

variable (R A X) in
instance instBialgebra [Bialgebra R A] [AddMonoid X] :
    Bialgebra R (AddMonoidAlgebra A X) :=
  { instCoalgebra R A X with
    counit_one := by
      simp only [one_def, counit_single, Bialgebra.counit_one]
    mul_compr₂_counit := lhom_ext fun a b => lhom_ext fun c d => by
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', single_mul_single, counit_single,
        Bialgebra.counit_mul, LinearMap.compl₁₂_apply]
    comul_one := by
      simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        TensorProduct.map_tmul, lsingle_apply]
    mul_compr₂_comul := lhom_ext fun a b => lhom_ext fun c d => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul d) with ⟨t, ht⟩
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', single_mul_single, comul_single,
        Bialgebra.comul_mul, hs, ht, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        map_sum, TensorProduct.map_tmul, lsingle_apply, LinearMap.compl₁₂_apply,
        LinearMap.coeFn_sum, Finset.sum_apply, Finset.sum_comm (s := s)] }

variable (R A X) in
def antipode [HopfAlgebra R A] [AddGroup X] :
    AddMonoidAlgebra A X →ₗ[R] AddMonoidAlgebra A X :=
  Finsupp.lsum R fun g => Finsupp.lsingle (-g) ∘ₗ HopfAlgebra.antipode

@[simp]
lemma antipode_single [HopfAlgebra R A] [AddGroup X] (g : X) (a : A) :
    antipode R A X (single g a)
      = single (-g) (HopfAlgebra.antipode (R := R) a) := by
  simp only [AddMonoidAlgebra, antipode, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index]
  rfl

@[simps!]
instance instHopfAlgebra [HopfAlgebra R A] [AddGroup X] : HopfAlgebra R (AddMonoidAlgebra A X) :=
  { instBialgebra R A X with
    antipode := antipode R A X
    mul_antipode_rTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.rTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, add_left_neg, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (R := R), ← map_sum (lsingle (R := R) (0 : X)),
        HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (repr := hs)]
    mul_antipode_lTensor_comul := lhom_ext fun a b => by
      rcases TensorProduct.exists_finset (R := R) (Coalgebra.comul b) with ⟨s, hs⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, comul_single, hs, map_sum,
        TensorProduct.map_tmul, lsingle_apply, LinearMap.lTensor_tmul, antipode_single,
        LinearMap.mul'_apply, single_mul_single, add_right_neg, counit_single,
        Algebra.linearMap_apply, coe_algebraMap]
      simp only [← lsingle_apply (R := R), ← map_sum (lsingle (R := R) (0 : X)),
        HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (repr := hs)] }

end AddMonoidAlgebra
