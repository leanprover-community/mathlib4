/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.Ring.Ideal

#align_import topology.algebra.uniform_ring from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!
# Completion of topological rings:

This files endows the completion of a topological ring with a ring structure.
More precisely the instance `UniformSpace.Completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`UniformAddGroup`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`UniformSpace.Completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `UniformSpace.Completion.extensionHom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `Completion R`.
* `UniformSpace.Completion.mapRingHom` : promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `Completion R` to `Completion S`.

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/


open Classical Set Filter TopologicalSpace AddCommGroup

open Classical

noncomputable section

universe u
namespace UniformSpace.Completion

open DenseInducing UniformSpace Function

section one_and_mul
variable (α : Type*) [Ring α] [UniformSpace α]

instance one : One (Completion α) :=
  ⟨(1 : α)⟩

instance mul : Mul (Completion α) :=
  ⟨curry <| (denseInducing_coe.prod denseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

@[norm_cast]
theorem coe_one : ((1 : α) : Completion α) = 1 :=
  rfl
#align uniform_space.completion.coe_one UniformSpace.Completion.coe_one

end one_and_mul

variable {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α]

@[norm_cast]
theorem coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((denseInducing_coe.prod denseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm
#align uniform_space.completion.coe_mul UniformSpace.Completion.coe_mul

variable [UniformAddGroup α]

theorem continuous_mul : Continuous fun p : Completion α × Completion α => p.1 * p.2 := by
  let m := (AddMonoidHom.mul : α →+ α →+ α).compr₂ toCompl
  -- ⊢ Continuous fun p => p.fst * p.snd
  have : Continuous fun p : α × α => m p.1 p.2 := by
    apply (continuous_coe α).comp _
    simp only [AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft]
    exact _root_.continuous_mul
  have di : DenseInducing (toCompl : α → Completion α) := denseInducing_coe
  -- ⊢ Continuous fun p => p.fst * p.snd
  convert di.extend_Z_bilin di this
  -- 🎉 no goals
#align uniform_space.completion.continuous_mul UniformSpace.Completion.continuous_mul

theorem Continuous.mul {β : Type*} [TopologicalSpace β] {f g : β → Completion α}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun b => f b * g b :=
  Continuous.comp continuous_mul (Continuous.prod_mk hf hg : _)
#align uniform_space.completion.continuous.mul UniformSpace.Completion.Continuous.mul

instance ring : Ring (Completion α) :=
  { AddMonoidWithOne.unary, (inferInstanceAs (AddCommGroup (Completion α))),
      (inferInstanceAs (Mul (Completion α))), (inferInstanceAs (One (Completion α))) with
    zero_mul := fun a =>
      Completion.induction_on a
        (isClosed_eq (Continuous.mul continuous_const continuous_id) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, zero_mul]
                    -- 🎉 no goals
    mul_zero := fun a =>
      Completion.induction_on a
        (isClosed_eq (Continuous.mul continuous_id continuous_const) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, mul_zero]
                    -- 🎉 no goals
    one_mul := fun a =>
      Completion.induction_on a
        (isClosed_eq (Continuous.mul continuous_const continuous_id) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, one_mul]
        -- 🎉 no goals
    mul_one := fun a =>
      Completion.induction_on a
        (isClosed_eq (Continuous.mul continuous_id continuous_const) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, mul_one]
        -- 🎉 no goals
    mul_assoc := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (Continuous.mul (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (Continuous.mul continuous_fst
            (Continuous.mul (continuous_fst.comp continuous_snd)
                                -- 🎉 no goals
              (continuous_snd.comp continuous_snd))))
                fun a b c => by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]
    left_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (Continuous.mul continuous_fst
                        -- 🎉 no goals
            (Continuous.add (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd)))
          (Continuous.add (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
            (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_add]
    right_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (Continuous.mul (Continuous.add continuous_fst (continuous_fst.comp continuous_snd))
                        -- 🎉 no goals
            (continuous_snd.comp continuous_snd))
          (Continuous.add (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))
            (Continuous.mul (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd))))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mul] }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coeRingHom : α →+* Completion α where
  toFun := (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul
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
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
                    -- 🎉 no goals
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        simp_rw [← coe_add, extension_coe hf, f.map_add]
                   -- 🎉 no goals
        -- 🎉 no goals
    map_one' := by rw [← coe_one, extension_coe hf, f.map_one]
    map_mul' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_mul)
          ((continuous_extension.comp continuous_fst).mul
            (continuous_extension.comp continuous_snd)))
        -- 🎉 no goals
        fun a b => by
        simp_rw [← coe_mul, extension_coe hf, f.map_mul] }
#align uniform_space.completion.extension_hom UniformSpace.Completion.extensionHom

instance topologicalRing : TopologicalRing (Completion α) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul
#align uniform_space.completion.top_ring_compl UniformSpace.Completion.topologicalRing

/-- The completion map as a ring morphism. -/
def mapRingHom (hf : Continuous f) : Completion α →+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)
#align uniform_space.completion.map_ring_hom UniformSpace.Completion.mapRingHom

section Algebra

variable (A : Type*) [Ring A] [UniformSpace A] [UniformAddGroup A] [TopologicalRing A] (R : Type*)
  [CommSemiring R] [Algebra R A] [UniformContinuousConstSMul R A]

@[simp]
theorem map_smul_eq_mul_coe (r : R) :
    Completion.map ((· • ·) r) = (· * ·) (algebraMap R A r : Completion A) := by
  ext x
  -- ⊢ Completion.map ((fun x x_1 => x • x_1) r) x = (fun x x_1 => x * x_1) (↑((fun …
  refine' Completion.induction_on x _ fun a => _
  -- ⊢ IsClosed {a | Completion.map ((fun x x_1 => x • x_1) r) a = (fun x x_1 => x  …
  · exact isClosed_eq Completion.continuous_map (continuous_mul_left _)
    -- 🎉 no goals
  · simp_rw [map_coe (uniformContinuous_const_smul r) a, Algebra.smul_def, coe_mul]
    -- 🎉 no goals
#align uniform_space.completion.map_smul_eq_mul_coe UniformSpace.Completion.map_smul_eq_mul_coe

instance algebra : Algebra R (Completion A) :=
  { (UniformSpace.Completion.coeRingHom : A →+* Completion A).comp (algebraMap R A) with
    commutes' := fun r x =>
      Completion.induction_on x (isClosed_eq (continuous_mul_left _) (continuous_mul_right _))
        fun a => by
        simpa only [coe_mul] using congr_arg ((↑) : A → Completion A) (Algebra.commutes r a)
        -- 🎉 no goals
    smul_def' := fun r x => congr_fun (map_smul_eq_mul_coe A R r) x }

theorem algebraMap_def (r : R) :
    algebraMap R (Completion A) r = (algebraMap R A r : Completion A) :=
  rfl
#align uniform_space.completion.algebra_map_def UniformSpace.Completion.algebraMap_def

end Algebra

section CommRing

variable (R : Type*) [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]

instance commRing : CommRing (Completion R) :=
  { Completion.ring with
    mul_comm := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }
                      -- 🎉 no goals

/-- A shortcut instance for the common case -/
instance algebra' : Algebra R (Completion R) := by infer_instance
                                                   -- 🎉 no goals
#align uniform_space.completion.algebra' UniformSpace.Completion.algebra'

end CommRing

end UniformSpace.Completion

namespace UniformSpace

variable {α : Type*}

theorem ring_sep_rel (α) [CommRing α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    separationSetoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoid.ext fun x y =>
    (addGroup_separationRel x y).trans <| Iff.trans (by rfl) (Submodule.quotientRel_r_def _).symm
                                                        -- 🎉 no goals
#align uniform_space.ring_sep_rel UniformSpace.ring_sep_rel

theorem ring_sep_quot (α : Type u) [r : CommRing α] [UniformSpace α] [UniformAddGroup α]
    [TopologicalRing α] : Quotient (separationSetoid α) = (α ⧸ (⊥ : Ideal α).closure) := by
  rw [@ring_sep_rel α r]
  -- ⊢ Quotient (Submodule.quotientRel (Ideal.closure ⊥)) = (α ⧸ Ideal.closure ⊥)
  rfl
  -- 🎉 no goals
#align uniform_space.ring_sep_quot UniformSpace.ring_sep_quot

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotEquivRingQuot (α) [r : CommRing α] [UniformSpace α] [UniformAddGroup α]
    [TopologicalRing α] : Quotient (separationSetoid α) ≃ α ⧸ (⊥ : Ideal α).closure :=
  Quotient.congrRight fun x y =>
    (addGroup_separationRel x y).trans <| Iff.trans (by rfl) (Submodule.quotientRel_r_def _).symm
                                                        -- 🎉 no goals
#align uniform_space.sep_quot_equiv_ring_quot UniformSpace.sepQuotEquivRingQuot

-- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer
instance commRing [CommRing α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    CommRing (Quotient (separationSetoid α)) := by
  rw [ring_sep_quot α]; infer_instance
  -- ⊢ CommRing (α ⧸ Ideal.closure ⊥)
                        -- 🎉 no goals
#align uniform_space.comm_ring UniformSpace.commRing

instance topologicalRing [CommRing α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (Quotient (separationSetoid α)) := by
  convert topologicalRing_quotient (⊥ : Ideal α).closure
  <;> (try congr; apply ring_sep_rel)
       -- 🎉 no goals
       -- 🎉 no goals
       -- ⊢ HEq commRing (Ideal.Quotient.commRing (Ideal.closure ⊥))
  simp [commRing]
  -- 🎉 no goals
#align uniform_space.topological_ring UniformSpace.topologicalRing

end UniformSpace

section UniformExtension

variable {α : Type*} [UniformSpace α] [Semiring α]

variable {β : Type*} [UniformSpace β] [Semiring β] [TopologicalSemiring β]

variable {γ : Type*} [UniformSpace γ] [Semiring γ] [TopologicalSemiring γ]

variable [T2Space γ] [CompleteSpace γ]

/-- The dense inducing extension as a ring homomorphism. -/
noncomputable def DenseInducing.extendRingHom {i : α →+* β} {f : α →+* γ} (ue : UniformInducing i)
    (dr : DenseRange i) (hf : UniformContinuous f) : β →+* γ where
  toFun := (ue.denseInducing dr).extend f
  map_one' := by
    convert DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous 1
    -- ⊢ 1 = ↑i 1
    exacts [i.map_one.symm, f.map_one.symm]
    -- 🎉 no goals
  map_zero' := by
    convert DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous 0 <;>
    -- ⊢ 0 = ↑i 0
    simp only [map_zero]
    -- 🎉 no goals
    -- 🎉 no goals
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    -- ⊢ ∀ (x y : β), OneHom.toFun (↑{ toOneHom := { toFun := extend (_ : DenseInduci …
    refine' fun x y => DenseRange.induction_on₂ dr _ (fun a b => _) x y
    -- ⊢ IsClosed {q | OneHom.toFun (↑{ toOneHom := { toFun := extend (_ : DenseInduc …
    · exact isClosed_eq (Continuous.comp h continuous_add)
    -- ⊢ ∀ (x y : β), OneHom.toFun { toFun := extend (_ : DenseInducing ↑i) ↑f, map_o …
        ((h.comp continuous_fst).add (h.comp continuous_snd))
    -- ⊢ IsClosed {q | OneHom.toFun { toFun := extend (_ : DenseInducing ↑i) ↑f, map_ …
    · simp_rw [← i.map_add, DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous _,
        ← f.map_add]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine' fun x y => DenseRange.induction_on₂ dr _ (fun a b => _) x y
    · exact isClosed_eq (Continuous.comp h continuous_mul)
        ((h.comp continuous_fst).mul (h.comp continuous_snd))
    · simp_rw [← i.map_mul, DenseInducing.extend_eq (ue.denseInducing dr) hf.continuous _,
        ← f.map_mul]
#align dense_inducing.extend_ring_hom DenseInducing.extendRingHom

end UniformExtension
