/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.uniform_ring
! leanprover-community/mathlib commit 9a59dcb7a2d06bf55da57b9030169219980660cd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Topology.Algebra.GroupCompletion
import Mathbin.Topology.Algebra.Ring.Ideal

/-!
# Completion of topological rings:

This files endows the completion of a topological ring with a ring structure.
More precisely the instance `uniform_space.completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`uniform_add_group`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`uniform_space.completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `uniform_space.completion.extension_hom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `completion R`.
* `uniform_space.completion.map_ring_hom` : promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `completion R` to `completion S`.

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/


open Classical Set Filter TopologicalSpace AddCommGroup

open Classical

noncomputable section

universe u

namespace UniformSpace.Completion

open DenseInducing UniformSpace Function

variable (α : Type _) [Ring α] [UniformSpace α]

instance : One (Completion α) :=
  ⟨(1 : α)⟩

instance : Mul (Completion α) :=
  ⟨curry <| (denseInducing_coe.Prod denseInducing_coe).extend (coe ∘ uncurry (· * ·))⟩

@[norm_cast]
theorem coe_one : ((1 : α) : Completion α) = 1 :=
  rfl
#align uniform_space.completion.coe_one UniformSpace.Completion.coe_one

variable {α} [TopologicalRing α]

@[norm_cast]
theorem coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((denseInducing_coe.Prod denseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm
#align uniform_space.completion.coe_mul UniformSpace.Completion.coe_mul

variable [UniformAddGroup α]

theorem continuous_mul : Continuous fun p : Completion α × Completion α => p.1 * p.2 :=
  by
  let m := (AddMonoidHom.mul : α →+ α →+ α).compr₂ to_compl
  have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
  have di : DenseInducing (to_compl : α → completion α) := dense_inducing_coe
  convert di.extend_Z_bilin di this
  ext ⟨x, y⟩
  rfl
#align uniform_space.completion.continuous_mul UniformSpace.Completion.continuous_mul

theorem Continuous.mul {β : Type _} [TopologicalSpace β] {f g : β → Completion α}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun b => f b * g b :=
  continuous_mul.comp (hf.prod_mk hg : _)
#align uniform_space.completion.continuous.mul UniformSpace.Completion.Continuous.mul

instance : Ring (Completion α) :=
  { AddMonoidWithOne.unary, Completion.addCommGroup, Completion.hasMul α,
    Completion.hasOne
      α with
    one_mul := fun a =>
      Completion.induction_on a
        (isClosed_eq (Continuous.mul continuous_const continuous_id) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, one_mul]
    mul_one := fun a =>
      Completion.induction_on a
        (isClosed_eq (Continuous.mul continuous_id continuous_const) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, mul_one]
    mul_assoc := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (Continuous.mul (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (Continuous.mul continuous_fst
            (Continuous.mul (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]
    left_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (Continuous.mul continuous_fst
            (Continuous.add (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd)))
          (Continuous.add (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
            (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_add]
    right_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (Continuous.mul (Continuous.add continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (Continuous.add (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))
            (Continuous.mul (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mul] }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coeRingHom : α →+* Completion α :=
  ⟨coe, coe_one α, fun a b => coe_mul a b, coe_zero, fun a b => coe_add a b⟩
#align uniform_space.completion.coe_ring_hom UniformSpace.Completion.coeRingHom

theorem continuous_coeRingHom : Continuous (coeRingHom : α → Completion α) :=
  continuous_coe α
#align uniform_space.completion.continuous_coe_ring_hom UniformSpace.Completion.continuous_coeRingHom

variable {β : Type u} [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

/-- The completion extension as a ring morphism. -/
def extensionHom [CompleteSpace β] [SeparatedSpace β] : Completion α →+* β :=
  have hf' : Continuous (f : α →+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, f.map_add]
    map_one' := by rw [← coe_one, extension_coe hf, f.map_one]
    map_mul' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_mul)
          ((continuous_extension.comp continuous_fst).mul
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, f.map_mul] }
#align uniform_space.completion.extension_hom UniformSpace.Completion.extensionHom

instance top_ring_compl : TopologicalRing (Completion α)
    where
  continuous_add := continuous_add
  continuous_mul := continuous_mul
#align uniform_space.completion.top_ring_compl UniformSpace.Completion.top_ring_compl

/-- The completion map as a ring morphism. -/
def mapRingHom (hf : Continuous f) : Completion α →+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)
#align uniform_space.completion.map_ring_hom UniformSpace.Completion.mapRingHom

section Algebra

variable (A : Type _) [Ring A] [UniformSpace A] [UniformAddGroup A] [TopologicalRing A] (R : Type _)
  [CommSemiring R] [Algebra R A] [UniformContinuousConstSMul R A]

@[simp]
theorem map_smul_eq_mul_coe (r : R) :
    Completion.map ((· • ·) r) = (· * ·) (algebraMap R A r : Completion A) :=
  by
  ext x
  refine' completion.induction_on x _ fun a => _
  · exact isClosed_eq completion.continuous_map (continuous_mul_left _)
  · rw [map_coe (uniform_continuous_const_smul r) a, Algebra.smul_def, coe_mul]
#align uniform_space.completion.map_smul_eq_mul_coe UniformSpace.Completion.map_smul_eq_mul_coe

instance : Algebra R (Completion A) :=
  {
    (UniformSpace.Completion.coeRingHom : A →+* Completion A).comp
      (algebraMap R
        A) with
    commutes' := fun r x =>
      Completion.induction_on x (isClosed_eq (continuous_mul_left _) (continuous_mul_right _))
        fun a => by
        simpa only [coe_mul] using congr_arg (coe : A → completion A) (Algebra.commutes r a)
    smul_def' := fun r x => congr_fun (map_smul_eq_mul_coe A R r) x }

theorem algebraMap_def (r : R) :
    algebraMap R (Completion A) r = (algebraMap R A r : Completion A) :=
  rfl
#align uniform_space.completion.algebra_map_def UniformSpace.Completion.algebraMap_def

end Algebra

section CommRing

variable (R : Type _) [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]

instance : CommRing (Completion R) :=
  { Completion.ring with
    mul_comm := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }

/-- A shortcut instance for the common case -/
instance algebra' : Algebra R (Completion R) := by infer_instance
#align uniform_space.completion.algebra' UniformSpace.Completion.algebra'

end CommRing

end UniformSpace.Completion

namespace UniformSpace

variable {α : Type _}

theorem ring_sep_rel (α) [CommRing α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    separationSetoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoid.ext fun x y =>
    (addGroup_separationRel x y).trans <| Iff.trans (by rfl) (Submodule.quotientRel_r_def _).symm
#align uniform_space.ring_sep_rel UniformSpace.ring_sep_rel

theorem ring_sep_quot (α : Type u) [r : CommRing α] [UniformSpace α] [UniformAddGroup α]
    [TopologicalRing α] : Quotient (separationSetoid α) = (α ⧸ (⊥ : Ideal α).closure) := by
  rw [@ring_sep_rel α r] <;> rfl
#align uniform_space.ring_sep_quot UniformSpace.ring_sep_quot

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotEquivRingQuot (α) [r : CommRing α] [UniformSpace α] [UniformAddGroup α]
    [TopologicalRing α] : Quotient (separationSetoid α) ≃ α ⧸ (⊥ : Ideal α).closure :=
  Quotient.congrRight fun x y =>
    (addGroup_separationRel x y).trans <| Iff.trans (by rfl) (Submodule.quotientRel_r_def _).symm
#align uniform_space.sep_quot_equiv_ring_quot UniformSpace.sepQuotEquivRingQuot

-- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer
instance commRing [CommRing α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    CommRing (Quotient (separationSetoid α)) := by rw [ring_sep_quot α] <;> infer_instance
#align uniform_space.comm_ring UniformSpace.commRing

instance topologicalRing [CommRing α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (Quotient (separationSetoid α)) :=
  by
  convert topologicalRing_quotient (⊥ : Ideal α).closure <;> try apply ring_sep_rel
  simp [UniformSpace.commRing]
#align uniform_space.topological_ring UniformSpace.topologicalRing

end UniformSpace

section UniformExtension

variable {α : Type _} [UniformSpace α] [Semiring α]

variable {β : Type _} [UniformSpace β] [Semiring β] [TopologicalSemiring β]

variable {γ : Type _} [UniformSpace γ] [Semiring γ] [TopologicalSemiring γ]

variable [T2Space γ] [CompleteSpace γ]

/-- The dense inducing extension as a ring homomorphism. -/
noncomputable def DenseInducing.extendRingHom {i : α →+* β} {f : α →+* γ} (ue : UniformInducing i)
    (dr : DenseRange i) (hf : UniformContinuous f) : β →+* γ
    where
  toFun := (ue.DenseInducing dr).extend f
  map_one' := by
    convert DenseInducing.extend_eq (ue.dense_inducing dr) hf.continuous 1
    exacts[i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert DenseInducing.extend_eq (ue.dense_inducing dr) hf.continuous 0
    exacts[i.map_zero.symm, f.map_zero.symm]
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).Continuous
    refine' fun x y => DenseRange.induction_on₂ dr _ (fun a b => _) x y
    ·
      exact
        isClosed_eq (Continuous.comp h continuous_add)
          ((h.comp continuous_fst).add (h.comp continuous_snd))
    ·
      simp_rw [← i.map_add, DenseInducing.extend_eq (ue.dense_inducing dr) hf.continuous _, ←
        f.map_add]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).Continuous
    refine' fun x y => DenseRange.induction_on₂ dr _ (fun a b => _) x y
    ·
      exact
        isClosed_eq (Continuous.comp h continuous_mul)
          ((h.comp continuous_fst).mul (h.comp continuous_snd))
    ·
      simp_rw [← i.map_mul, DenseInducing.extend_eq (ue.dense_inducing dr) hf.continuous _, ←
        f.map_mul]
#align dense_inducing.extend_ring_hom DenseInducing.extendRingHom

end UniformExtension

