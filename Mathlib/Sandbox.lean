import Mathlib.RingTheory.DedekindDomain.IntegralClosure

namespace IsDedekindDomain


noncomputable section normalClosure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S]

noncomputable local instance :
  Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra _ _

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))

scoped instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra

scoped instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

def normalClosure : Type _ := integralClosure S E

local notation3 "T" => normalClosure R S

instance : CommRing T := inferInstanceAs (CommRing (integralClosure S E))

instance : IsDomain T := inferInstanceAs (IsDomain (integralClosure S E))

instance : Nontrivial T := inferInstanceAs (Nontrivial (integralClosure S E))

instance : Algebra S T := inferInstanceAs (Algebra S (integralClosure S E))

scoped instance : Algebra T E := inferInstanceAs (Algebra (integralClosure S E) E)

instance : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra

scoped instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

scoped instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E

instance : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl

scoped instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

scoped instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E

scoped instance : IsScalarTower R T E :=  IsScalarTower.to₁₃₄ R S T E

scoped instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
      (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)

instance : NoZeroSMulDivisors S T := Subalgebra.noZeroSMulDivisors_bot (integralClosure S E)

instance : FaithfulSMul R T :=
  (faithfulSMul_iff_algebraMap_injective R T).mpr <|
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

variable [Module.Finite R S]

scoped instance : FiniteDimensional L E := Module.Finite.right K L E

scoped instance : IsFractionRing T E :=
  integralClosure.isFractionRing_of_finite_extension L E

instance : IsIntegrallyClosed T :=
  integralClosure.isIntegrallyClosedOfFiniteExtension L

variable [PerfectField (FractionRing R)]

local instance : Algebra.IsSeparable L E :=
  Algebra.isSeparable_tower_top_of_isSeparable K L E

instance : IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E) (f := (FractionRing.algEquiv R K).symm)
      (g := (FractionRing.algEquiv T E).symm) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

variable [IsDedekindDomain S]

instance : Module.Finite S T :=
  IsIntegralClosure.finite S L E T

instance : Module.Finite R T :=
  Module.Finite.trans S T

instance : IsDedekindDomain T :=
  integralClosure.isDedekindDomain S L E

end IsDedekindDomain.normalClosure
