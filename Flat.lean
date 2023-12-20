--import Mathlib.Tactic
import Mathlib.RingTheory.Flat
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

-- import Mathlib.Algebra.DirectSum.Module
-- import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
-- import Mathlib.LinearAlgebra.FreeModule.Basic
-- import Mathlib.Algebra.Module.Projective

/-
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
-/

universe u v w

-- #check Ideal
-- theorem iff_Ideal : Flat R M ↔ ∀ {I : Ideal R}, Injective (TensorProduct.lift ((lsmul R M).comp I.subtype)) := by
--   constructor
--   · intro h₁ I
--     by_contra h₂
--     have h₃ : ∃ (a b : I ⊗[R] M), (a ≠ b) ∧ (TensorProduct.lift ((lsmul R M).comp I.subtype) a
--       = TensorProduct.lift ((lsmul R M).comp I.subtype) b) := by sorry
--     obtain ⟨a, b, h₂, h₃⟩ := h₃
--     have S : Set R := sorry
--     --have J := Ideal.span S
--     sorry
--   · intro h₁
--     constructor
--     intro _ _
--     simp [h₁]

open TensorProduct

open LinearMap

open CategoryTheory

open CategoryTheory.Limits

open Functor

namespace ModuleCat

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def rTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj N := of R (N ⊗[R] M)
  map f := ofHom <| rTensor M f
  map_id N := rTensor_id M N
  map_comp f g := rTensor_comp M g f

noncomputable def lTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj N := of R (M ⊗[R] N)
  map f := ofHom <| lTensor M f
  map_id N := lTensor_id M N
  map_comp f g := lTensor_comp M g f

instance rTensorFunctorPreservesZeroMorphisms : PreservesZeroMorphisms (rTensorFunctor R M) where
  map_zero := fun _ _ => rTensor_zero M

instance lTensorFunctorPreservesZeroMorphisms : PreservesZeroMorphisms (lTensorFunctor R M) where
  map_zero := fun _ _ => lTensor_zero M

instance rTensorFunctorPreservesFiniteColimits : PreservesFiniteColimits (rTensorFunctor R M) where
  preservesFiniteColimits J := sorry

instance lTensorFunctorPreservesFiniteColimits : PreservesFiniteColimits (lTensorFunctor R M) where
  preservesFiniteColimits J := sorry

noncomputable def rTensorFunctorRightExact : ModuleCat.{v} R ⥤ᵣ ModuleCat.{v} R :=
  RightExactFunctor.of (rTensorFunctor R M)

noncomputable def lTensorFunctorRightExact : ModuleCat.{v} R ⥤ᵣ ModuleCat.{v} R :=
  RightExactFunctor.of (lTensorFunctor R M)

end ModuleCat





namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)

def Flat : Prop :=
  @Module.Flat R S _ _ f.toModule

end RingHom

namespace Module

namespace Flat

-- def injective (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
--    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
--     (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M)

-- lemma iff_injective

-- variable (T : Type w)

-- better name?

variable (R : Type u) (S : Type v) (M : Type w)
[CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup M]
[Module R M] [Module S M] [IsScalarTower R S M]

#check Equiv.comp_injective
#check EquivLike
--LinearAlgebra.TensorProduct.Tower.assoc
lemma of_flat_hom [hM : Flat S M] [hS : Flat R S] : Flat R M := by
    rw [iff_rTensor_injective' R M]
    rw [iff_rTensor_injective' R S] at hS
    rw [iff_rTensor_injective' S M] at hM
    intro I
    let hS := hS I
    let J := @Ideal.span S _ <| LinearMap.range (TensorProduct.lift ((lsmul R S).comp I.subtype))
    let hM := hM J
    -- have h : (TensorProduct.lift ((lsmul R S).comp I.subtype)).comp <|
    --   TensorProduct.lift ((lsmul S M).comp J.subtype) = TensorProduct.lift ((lsmul R M).comp I.subtype)
    let e₁ := (AlgebraTensorModule.assoc R S S M S I).restrictScalars R
    --letI := k S R R I S M
    --letI := AlgebraTensorModule.leftComm
    let e₂ := (TensorProduct.lid S M).restrictScalars R
    --let σ₃ := (TensorProduct.lid S M).toLinearMap
    let e₃ := TensorProduct.lid R (S ⊗[S] M)
    let e := e₃ ≪≫ₗ e₂
    sorry


lemma iff_rTensorFunctorPreservesFiniteLimits :  Flat R M ↔
  Nonempty (PreservesFiniteLimits (ModuleCat.rTensorFunctor R M)) := by
  sorry

end Flat

end Module

namespace RingHom

namespace Flat

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)

--idk where to put
-- lemma of_preserves_flatness (M : Type w) [CommRing S] [AddCommGroup M]
--   [Module S M] [Module.Flat S M] (h : f.Flat) : @Module.Flat R M _ _ <| Module.compHom M f :=
--   sorry

def PreservesInjectiveness : Prop :=
    @Module.Flat.rTensor_preserves_injectiveness R S _ _ f.toModule

variable (R : Type u) (S : Type v) [CommRing R] [Ring S]

lemma id : Flat (RingHom.id R) := Module.Flat.self R

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)


-- it seems some stuff may have been defined in the wrong way
lemma iff_PreservesInjectiveness [UnivLE.{u, v}] :
  f.Flat ↔ PreservesInjectiveness f :=
    @Module.Flat.iff_rTensor_preserves_injectiveness R _ S _ f.toModule _

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [Ring T]

lemma comp {g : S →+* T} {f : R →+* S} (hg : g.Flat) (hf : f.Flat) :
  --[UnivLE.{u, v}] [UnivLE.{v, w}] [UnivLE.{u, w}]
  Flat (RingHom.comp g f) :=
    @Module.Flat.of_flat_hom R S T _ _  f.toAlgebra _ (g.comp f).toModule g.toModule (sorry) hg hf

end Flat

end RingHom





namespace Module

open Localization

--namespace Flat

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

--class or def?
class FaithfullyFlat extends Flat R M where
  faithful : ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  --faithful := ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⧸ (m • ⊤ : Submodule R M)

namespace FaithfullyFlat

instance self : FaithfullyFlat R R where
  faithful m _ := Equiv.nontrivial (TensorProduct.lid R (R ⧸ m)).toEquiv

--Faithfully flat iff relfects exact sequences (maybe put in cat file)
def ReflectsExact : Prop := sorry

--Faithfully flat iff tensor with any R-module is nonzero
def TensorNonzero : Prop :=
  ∀ {N : Type v} [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N)

-- Faithfully flat iff tensor with all prime residues is nonzero
def PrimeResidues : Prop :=
  ∀ ⦃p : Ideal R⦄ (_ : p.IsPrime), Nontrivial <| M ⊗[R] FractionRing (R ⧸ p)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime p)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime p)).comp
  -- (algebraMap R <| Localization.AtPrime p)).toModule

-- Faithfully flat iff tensor with all maximal residues is nonzero
-- def MaximalResidues : Prop :=
--   ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime m)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime m)).comp
  -- (algebraMap R <| Localization.AtPrime m)).toModule

variable (R : Type u) (S : Type v) (M : Type w)
[CommRing R] [CommRing S]
[Algebra R S] [AddCommGroup M]
[Module R M] [Module S M] [IsScalarTower R S M]

def of_faithfully_flat_hom [hM : FaithfullyFlat S M] [hS : FaithfullyFlat R S] :
  FaithfullyFlat R M where
    out := (Flat.of_flat_hom R S M).out
    faithful m hm := by
      let e₁ := (TensorProduct.lid S M).restrictScalars R
      let e₂ := TensorProduct.lid R (S ⊗[S] M)
      let e3 := e₂ ≪≫ₗ e₁
      sorry

end FaithfullyFlat

--end Flat

end Module

namespace RingHom

--namespace Flat

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] (f : R →+* S)

def FaithfullyFlat :=
  @Module.FaithfullyFlat R S _ _ f.toModule

namespace FaithfullyFlat

lemma id (R : Type u) [CommRing R] : FaithfullyFlat (RingHom.id R) := Module.FaithfullyFlat.self R

variable  {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [Ring T] (f : R →+* S)

lemma comp {g : S →+* T} {f : R →+* S} (hg : g.FaithfullyFlat) (hf : f.FaithfullyFlat) :
  FaithfullyFlat (g.comp f) :=
    @Module.FaithfullyFlat.of_faithfully_flat_hom
      R S T _ _ f.toAlgebra _ (g.comp f).toModule g.toModule (sorry) hg hf

end FaithfullyFlat

--end Flat

end RingHom
