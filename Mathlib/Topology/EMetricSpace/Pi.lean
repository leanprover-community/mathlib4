/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Pi

/-!
# Indexed product of extended metric spaces
-/

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

open EMetric

section Pi

open Finset

variable {π : β → Type*} [Fintype β]

instance [∀ b, EDist (π b)] : EDist (∀ b, π b) where
  edist f g := Finset.sup univ fun b => edist (f b) (g b)

theorem edist_pi_def [∀ b, EDist (π b)] (f g : ∀ b, π b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl

theorem edist_le_pi_edist [∀ b, EDist (π b)] (f g : ∀ b, π b) (b : β) :
    edist (f b) (g b) ≤ edist f g :=
  le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)

theorem edist_pi_le_iff [∀ b, EDist (π b)] {f g : ∀ b, π b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by simp only [Finset.mem_univ, forall_const]

theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) ≤ edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl

@[simp]
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun _ : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudoEMetricSpacePi [∀ b, PseudoEMetricSpace (π b)] : PseudoEMetricSpace (∀ b, π b) where
  edist_self f := bot_unique <| Finset.sup_le <| by simp
  edist_comm f g := by simp [edist_pi_def, edist_comm]
  edist_triangle _ g _ := edist_pi_le_iff.2 fun b => le_trans (edist_triangle _ (g b) _)
    (add_le_add (edist_le_pi_edist _ _ _) (edist_le_pi_edist _ _ _))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [Pi.uniformity, PseudoEMetricSpace.uniformity_edist, comap_iInf, gt_iff_lt,
      preimage_setOf_eq, comap_principal, edist_pi_def]
    rw [iInf_comm]; congr; funext ε
    rw [iInf_comm]; congr; funext εpos
    simp [setOf_forall, εpos]

end Pi

variable {γ : Type w} [EMetricSpace γ]

section Pi

open Finset

variable {π : β → Type*} [Fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetricSpacePi [∀ b, EMetricSpace (π b)] : EMetricSpace (∀ b, π b) :=
  .ofT0PseudoEMetricSpace _

end Pi
