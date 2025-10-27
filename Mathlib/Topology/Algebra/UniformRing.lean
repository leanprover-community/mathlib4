/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Completion of topological rings:

This file endows the completion of a topological ring with a ring structure.
More precisely, the instance `UniformSpace.Completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`IsUniformAddGroup`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`UniformSpace.Completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `UniformSpace.Completion.extensionHom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `Completion R`.
* `UniformSpace.Completion.mapRingHom`: promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `Completion R` to `Completion S`.

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/

@[expose] public section

noncomputable section

universe u
namespace UniformSpace.Completion

open IsDenseInducing UniformSpace Function

section one_and_mul
variable (α : Type*) [Ring α] [UniformSpace α]

instance one : One (Completion α) :=
  ⟨(1 : α)⟩

instance mul : Mul (Completion α) :=
  ⟨curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

@[norm_cast]
theorem coe_one : ((1 : α) : Completion α) = 1 :=
  rfl

@[simp] lemma coe_eq_one_iff [T0Space α] {x : α} : (x : Completion α) = 1 ↔ x = 1 :=
  Completion.coe_inj

end one_and_mul

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α]

@[norm_cast]
theorem coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

variable [IsUniformAddGroup α]

instance : ContinuousMul (Completion α) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : α →+ α →+ α).compr₂ toCompl
    have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
    have di : IsDenseInducing (toCompl : α → Completion α) := isDenseInducing_coe
    exact (di.extend_Z_bilin di this :)

instance ring : Ring (Completion α) :=
  { AddMonoidWithOne.unary, (inferInstanceAs (AddCommGroup (Completion α))),
      (inferInstanceAs (Mul (Completion α))), (inferInstanceAs (One (Completion α))) with
    zero_mul := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_const.mul continuous_id) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, zero_mul]
    mul_zero := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_id.mul continuous_const) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, mul_zero]
    one_mul := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_const.mul continuous_id) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, one_mul]
    mul_one := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_id.mul continuous_const) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, mul_one]
    mul_assoc := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
            (continuous_snd.comp continuous_snd))
          (continuous_fst.mul
            ((continuous_fst.comp continuous_snd).mul
              (continuous_snd.comp continuous_snd))))
                fun a b c => by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]
    left_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (continuous_fst.mul
            (Continuous.add (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd)))
          (Continuous.add (continuous_fst.mul (continuous_fst.comp continuous_snd))
            (continuous_fst.mul (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_add]
    right_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          ((Continuous.add continuous_fst (continuous_fst.comp continuous_snd)).mul
            (continuous_snd.comp continuous_snd))
          (Continuous.add (continuous_fst.mul (continuous_snd.comp continuous_snd))
            ((continuous_fst.comp continuous_snd).mul
              (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mul] }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
@[simps]
def coeRingHom : α →+* Completion α where
  toFun := (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul

theorem continuous_coeRingHom : Continuous (coeRingHom : α → Completion α) :=
  continuous_coe α

variable {β : Type u} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

/-- The completion extension as a ring morphism. -/
def extensionHom [CompleteSpace β] [T0Space β] : Completion α →+* β :=
  have hf' : Continuous (f : α →+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        simp_rw [← coe_add, extension_coe hf, f.map_add]
    map_one' := by rw [← coe_one, extension_coe hf, f.map_one]
    map_mul' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_mul)
          ((continuous_extension.comp continuous_fst).mul
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        simp_rw [← coe_mul, extension_coe hf, f.map_mul] }

theorem extensionHom_coe [CompleteSpace β] [T0Space β] (a : α) :
    Completion.extensionHom f hf a = f a := by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    UniformSpace.Completion.extension_coe <| uniformContinuous_addMonoidHom_of_continuous hf]

instance topologicalRing : IsTopologicalRing (Completion α) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul

/-- The completion map as a ring morphism. -/
def mapRingHom (hf : Continuous f) : Completion α →+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)

theorem mapRingHom_apply {x : UniformSpace.Completion α} :
    UniformSpace.Completion.mapRingHom f hf x = UniformSpace.Completion.map f x := rfl

variable {f}

theorem mapRingHom_coe (hf : UniformContinuous f) (a : α) :
    mapRingHom f hf.continuous a = f a := by
  rw [mapRingHom_apply, map_coe hf]

section Algebra

variable (A : Type*) [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  (R : Type*) [CommSemiring R] [Algebra R A] [UniformContinuousConstSMul R A]

@[simp]
theorem map_smul_eq_mul_coe (r : R) :
    Completion.map (r • ·) = ((algebraMap R A r : Completion A) * ·) := by
  ext x
  refine Completion.induction_on x ?_ fun a => ?_
  · exact isClosed_eq Completion.continuous_map (continuous_mul_left _)
  · simp_rw [map_coe (uniformContinuous_const_smul r) a, Algebra.smul_def, coe_mul]

instance algebra : Algebra R (Completion A) where
  algebraMap := (UniformSpace.Completion.coeRingHom : A →+* Completion A).comp (algebraMap R A)
  commutes' := fun r x =>
    Completion.induction_on x (isClosed_eq (continuous_mul_left _) (continuous_mul_right _))
      fun a => by
      simpa only [coe_mul] using congr_arg ((↑) : A → Completion A) (Algebra.commutes r a)
  smul_def' := fun r x => congr_fun (map_smul_eq_mul_coe A R r) x

theorem algebraMap_def (r : R) :
    algebraMap R (Completion A) r = (algebraMap R A r : Completion A) :=
  rfl

end Algebra

section CommRing

variable (R : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

instance commRing : CommRing (Completion R) :=
  { Completion.ring with
    mul_comm := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }

/-- A shortcut instance for the common case -/
instance algebra' : Algebra R (Completion R) := by infer_instance

end CommRing

end UniformSpace.Completion

namespace UniformSpace

variable {α : Type*}

-- TODO: move (some of) these results to the file about topological rings
theorem inseparableSetoid_ring (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α] :
    inseparableSetoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoid.ext fun x y =>
    addGroup_inseparable_iff.trans <| .trans (by rfl) (Submodule.quotientRel_def _).symm

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an homeomorphism between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotHomeomorphRingQuot (α) [CommRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    SeparationQuotient α ≃ₜ α ⧸ (⊥ : Ideal α).closure where
  toEquiv := Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
  continuous_toFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id
  continuous_invFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id

instance commRing [CommRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    CommRing (SeparationQuotient α) :=
  (sepQuotHomeomorphRingQuot _).commRing

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotRingEquivRingQuot (α) [CommRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    SeparationQuotient α ≃+* α ⧸ (⊥ : Ideal α).closure :=
  (sepQuotHomeomorphRingQuot _).ringEquiv

instance topologicalRing [CommRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    IsTopologicalRing (SeparationQuotient α) where
  toContinuousAdd :=
    (sepQuotHomeomorphRingQuot α).isInducing.continuousAdd (sepQuotRingEquivRingQuot α)
  toContinuousMul :=
    (sepQuotHomeomorphRingQuot α).isInducing.continuousMul (sepQuotRingEquivRingQuot α)
  toContinuousNeg :=
    (sepQuotHomeomorphRingQuot α).isInducing.continuousNeg <|
      map_neg (sepQuotRingEquivRingQuot α)

end UniformSpace

section UniformExtension

variable {α : Type*} [UniformSpace α] [Semiring α]
variable {β : Type*} [UniformSpace β] [Semiring β] [IsTopologicalSemiring β]
variable {γ : Type*} [UniformSpace γ] [Semiring γ] [IsTopologicalSemiring γ]
variable [T2Space γ] [CompleteSpace γ]

/-- The dense inducing extension as a ring homomorphism. -/
noncomputable def IsDenseInducing.extendRingHom {i : α →+* β} {f : α →+* γ}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) : β →+* γ where
  toFun := (ue.isDenseInducing dr).extend f
  map_one' := by
    convert IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 1
    exacts [i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 0 <;>
    simp only [map_zero]
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y => DenseRange.induction_on₂ dr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (Continuous.comp h continuous_add)
        ((h.comp continuous_fst).add (h.comp continuous_snd))
    · simp_rw [← i.map_add, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous _,
        ← f.map_add]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y => DenseRange.induction_on₂ dr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (Continuous.comp h continuous_mul)
        ((h.comp continuous_fst).mul (h.comp continuous_snd))
    · simp_rw [← i.map_mul, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous _,
        ← f.map_mul]

end UniformExtension
