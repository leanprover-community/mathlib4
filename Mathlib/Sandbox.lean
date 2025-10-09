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

local instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra

-- We give this instance explicitely since otherwise Lean takes a long time to find it
local instance : Algebra L E := normalClosure.algebra _ _ _

local instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

def normalClosure [Algebra L E] := integralClosure S E

local notation3 "T" => normalClosure R S A

instance : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra

instance : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl

local instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
      (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)

instance : FaithfulSMul R T :=
  (faithfulSMul_iff_algebraMap_injective R T).mpr <|
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

local instance [FiniteDimensional L E] : IsFractionRing T E :=
    integralClosure.isFractionRing_of_finite_extension L E


end IsDedekindDomain
