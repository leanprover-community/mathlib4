import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.RingOfDefinition.Utils
import Mathlib.RingTheory.RingOfDefinition

universe u v w t

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type v}
variable {S : Type w} [CommRing S] [Algebra R S]

class IsRingModel {R₀ : Type t} [CommRing R₀] (f : R₀ →+* R) (D : Set (MvPolynomial ι R)) : Prop where
  coeffs : MvPolynomial.Set.coefficients D ⊆ Set.range f

class IsFaithfulRingModel {R₀ : Type t} [CommRing R₀] (f : R₀ →+* R) (D : Set (MvPolynomial ι R)) extends
    IsRingModel f D where
  inj : Function.Injective f

class IsSubringModel (R₀ : Subring R) (D : Set (MvPolynomial ι R)) : Prop where
  out : IsRingModel (SubringClass.subtype R₀) D

instance (R₀ : Subring R) (D : Set (MvPolynomial ι R)) [IsSubringModel R₀ D] :
    IsFaithfulRingModel (SubringClass.subtype R₀) D where
  coeffs := IsSubringModel.out.coeffs
  inj := Subtype.val_injective

structure RingModel (D : Set (MvPolynomial ι R)) where
  R₀ : Type v
  ring : CommRing R₀
  D₀ : Set (MvPolynomial ι R₀)
  f : R₀ →+* R
  hf : Set.MapsTo (MvPolynomial.map f) D₀ D

structure FaithfulRingModel (D : Set (MvPolynomial ι R)) where
  R₀ : Subring R
  coeffs : MvPolynomial.Set.coefficients D ⊆ R₀

variable {D : Set (MvPolynomial ι R)}

instance (M : FaithfulRingModel D) : CoeDep (FaithfulRingModel D) M (Subring R) where
  coe := M.R₀

instance (M : FaithfulRingModel D) : CoeDep (FaithfulRingModel D) M (Type _) where
  coe := M.R₀

def FaithfulRingModel.D₀ (M : FaithfulRingModel D) : Set (MvPolynomial ι M) :=
  (MvPolynomial.map (SubringClass.subtype M.R₀)) ⁻¹' D

lemma FaithfulRingModel.mapsTo (M : FaithfulRingModel D) :
    Set.MapsTo (MvPolynomial.map (SubringClass.subtype M.R₀)) M.D₀ D :=
  Set.mapsTo_preimage (MvPolynomial.map (SubringClass.subtype M.R₀)) D

lemma FaithfulRingModel.injective (M : FaithfulRingModel D) :
    Function.Injective M.mapsTo.restrict := by
  rw [Set.MapsTo.restrict_inj]
  apply Set.injOn_of_injective
  apply MvPolynomial.map_injective
  exact Subtype.val_injective

lemma FaithfulRingModel.surjective (M : FaithfulRingModel D) :
    Function.Surjective M.mapsTo.restrict := by
  intro ⟨d, hd⟩
  have hc : MvPolynomial.coefficients d ⊆ M.R₀ := sorry
  sorry

noncomputable def FaithfulRingModel.equiv (M : FaithfulRingModel D) : M.D₀ ≃ D :=
  Equiv.ofBijective M.mapsTo.restrict ⟨M.injective, M.surjective⟩
