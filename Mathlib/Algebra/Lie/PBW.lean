import Mathlib.RingTheory.FilteredAlgebra
import Mathlib.Algebra.Lie.Free
import Mathlib.LinearAlgebra.TensorAlgebra.Grading

universe u v w

namespace PBW

variable {R : Type u} {L : Type v} {ι : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]

#check TensorAlgebra.gradedAlgebra

suppress_compilation
-- abbrev foo : ℕ → Submodule R (TensorAlgebra R L) :=
--   FilteredAlgebra.ofGraded ((LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ ·))

-- abbrev algHom := UniversalEnvelopingAlgebra.mkAlgHom R L

-- lemma surjF : Function.Surjective (algHom R L) :=
--   RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R L)

-- abbrev fee : ℕ → Submodule R (UniversalEnvelopingAlgebra R L) :=
--   (Submodule.map (algHom R L).toLinearMap).comp (foo R L)


-- noncomputable instance instFA : FilteredAlgebra (fee R L) :=
--   FilteredAlgebra.instPushforwardOfFiltered (foo R L) (algHom R L) (surjF R L)


-- noncomputable def TensorHom : DirectSum ℕ (FilteredAlgebra.assocGAlgebra (foo R L)) →ₐ[R]
--   DirectSum ℕ (FilteredAlgebra.assocGAlgebra (fee R L)) :=
--     FilteredAlgebra.betweenGraded (foo R L) (fee R L) (algHom R L) <|
--     FilteredAlgebra.pushforwardOfFiltered_respects (foo R L) (algHom R L)

-- -- will need to rename later
-- lemma TensorHom_surj : Function.Surjective <| TensorHom R L :=
--   FilteredAlgebra.betweenGraded_surjOfSurj (foo R L) (fee R L) (algHom R L) <|
--   FilteredAlgebra.pushforwardOfFiltered_respects (foo R L) (algHom R L)



--  match instDecidableLe_mathlib i j with
--   | isTrue _ => by
--     intro k
--     exact (MvPolynomial.X i) * (MvPolynomial.X j)
--   | isFalse _ => by
--     intro k
--     let p := Finsupp.sum (b.repr ⁅b i, b j⁆) (fun i r =>
--       r • (MvPolynomial.X i) : ι → R → MvPolynomial ι R)
--     --let r :=
--     exact (MvPolynomial.X i) * (MvPolynomial.X j) + Finsupp.sum (b.repr ⁅b i, b j⁆) (fun i r =>
--       r • (MvPolynomial.X i))



-- noncomputable instance instGCommRing :
--   DirectSum.GCommRing (FilteredAlgebra.assocGAlgebra (fee R L)) where
--   mul_comm := by
--     rintro ⟨n,a⟩ ⟨m,b⟩
--     sorry


def bracketAUX [LinearOrder ι] (b : Basis ι R L) : ι → ι → MvPolynomial ι R := fun i j =>
  match instDecidableLe_mathlib i j with
  | isTrue _ => (MvPolynomial.X i) * (MvPolynomial.X j)
  | isFalse _ => (MvPolynomial.X i) * (MvPolynomial.X j) + Finsupp.sum (b.repr ⁅b i, b j⁆) (
    fun i r => r • (MvPolynomial.X i))


def bracketAUX₂  [LinearOrder ι] (b : Basis ι R L) : ι → (ι →₀ ℕ) → MvPolynomial ι R := fun i f => by

  sorry


#check Basis.constr
instance instLieRingModule (B : Basis ι R L) : LieRingModule L (MvPolynomial ι R) where
  bracket x y := by

    sorry
  add_lie := sorry
  lie_add := sorry
  leibniz_lie := sorry

-- def test : sorry := by
--   let G := gr R L
--   letI : Semiring G := inferInstance
--   letI : Ring G := inferInstance
--   letI : Algebra R G := inferInstance

--   sorry

-- noncomputable instance instComm : CommRing (gr R L) where
--   zsmul n x := sorry
--   add_left_neg := sorry
--   mul_comm := sorry

--abbrev instFilteredUAE : FilteredAlgebra (UniversalEnvelopingAlgebra R L) := sorry

--abbrev assocGradedUAE := FilteredAlgebra.assocGAlgebra

end PBW
