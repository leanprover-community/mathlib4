/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Normal closure of an extension of domains

We define the normal closure of an extension of domains `R ⊆ S` as a domain `T` such that
`R ⊆ S ⊆ T` and the extension `Frac T / Frac R` is Galois, and prove several instances about it.

Under the hood, `T` is defined as the `integralClosure` of `S` inside the
`IntermediateField.normalClosure` of the extension `Frac S / Frac R` inside the `AlgebraicClosure`
of `Frac S`. In particular, if `S` is a Dedekind domain, then `T` is also a Dedekind domain.

# Technical notes
* Many instances are proved about the `IntermediateField.normalClosure` of the extension
`Frac S / Frac R` inside the `AlgebraicClosure` of `Frac S`. However these are only needed for the
construction of `T` and to prove some results about it. Therefore, these instances are scoped.
* `Ring.NormalClosure` is defined as a type rather than a `Subalgebra` for performance reasons
(and thus we need to provide explicit instances for it). Although, defining at a `Subalgebra`
does not cause timeouts in this file, it does slow down considerably its compilation and
does trigger timeouts in applications.
-/

namespace Ring

noncomputable section normalClosure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S]

/--
We register this specific instance as a local instance rather than making
`FractionRing.listAlgebra` a local instance because the latter causes timeouts since
it is too general.
-/
local instance : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra _ _

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))


/--
This is a local instance since it is only used in this file to construct `Ring.normalClosure`.
-/
local instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra

local instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

/--
The normal closure of an extension of domains `R ⊆ S`. It is defined as a domain `T` such that
`R ⊆ S ⊆ T` and `Frac T / Frac R` is Galois. -/
def NormalClosure : Type _ := integralClosure S E

local notation3 "T" => NormalClosure R S

instance : CommRing T := inferInstanceAs (CommRing (integralClosure S E))

instance : IsDomain T := inferInstanceAs (IsDomain (integralClosure S E))

instance : Nontrivial T := inferInstanceAs (Nontrivial (integralClosure S E))

instance : Algebra S T := inferInstanceAs (Algebra S (integralClosure S E))

/--
This is a local instance since it is only used in this file to construct `Ring.normalClosure`.
-/
local instance : Algebra T E := inferInstanceAs (Algebra (integralClosure S E) E)

instance : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra

local instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E

instance : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E

local instance : IsScalarTower R T E :=  IsScalarTower.to₁₃₄ R S T E

local instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
      (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)

instance : NoZeroSMulDivisors S T := Subalgebra.noZeroSMulDivisors_bot (integralClosure S E)

instance : FaithfulSMul R T :=
  (faithfulSMul_iff_algebraMap_injective R T).mpr <|
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

variable [Module.Finite R S]

local instance : FiniteDimensional L E := Module.Finite.right K L E

local instance : IsFractionRing T E :=
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

end Ring.normalClosure
