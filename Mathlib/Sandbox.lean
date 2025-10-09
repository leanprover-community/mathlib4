import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Localization.Integral

variable (R S A : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field A]
  [Algebra R S] [NoZeroSMulDivisors R S] [Algebra R A] [NoZeroSMulDivisors R A]
  [Algebra S A] [NoZeroSMulDivisors S A] [IsScalarTower R S A]

noncomputable section

namespace IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R) (FractionRing S) A

--- Prove this? -- Should follow from `FractionRing.liftAlgebra`
variable [Algebra (FractionRing S)
  (IntermediateField.normalClosure (FractionRing R) (FractionRing S) A)]

local instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra

local instance [Algebra L E] : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

def normalClosure [Algebra L E] := integralClosure S E

instance : Algebra R (normalClosure R S A) :=
  ((algebraMap S (normalClosure R S A)).comp (algebraMap R S)).toAlgebra

instance : IsScalarTower R S (normalClosure R S A) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
      (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)

instance : FaithfulSMul R (normalClosure R S A) :=
  (faithfulSMul_iff_algebraMap_injective R (normalClosure R S A) ).mpr <|
      (FaithfulSMul.algebraMap_injective S (normalClosure R S A)).comp
        (FaithfulSMul.algebraMap_injective R S)

local instance [FiniteDimensional L E] : IsFractionRing (normalClosure R S A) E :=
    integralClosure.isFractionRing_of_finite_extension L E

end IsDedekindDomain
