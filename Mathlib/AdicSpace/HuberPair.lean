import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

universe u

open Topology TopologicalSpace

structure HuberRing.ringOfDefinition (R₀ : Type u) (R : Type u)
    [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] extends Algebra R₀ R where
  emb : IsOpenEmbedding (_root_.algebraMap R₀ R)
  J : Ideal R₀
  fg : J.FG
  adic : IsAdic J

class HuberRing (R : Type u) extends CommRing R, TopologicalSpace R, IsTopologicalRing R where
  pod : ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : TopologicalSpace R₀) (_ : IsTopologicalRing R₀),
    Nonempty (HuberRing.ringOfDefinition R₀ R)

instance (R : Type u) [HuberRing R] : NonarchimedeanAddGroup R := by
  rcases HuberRing.pod (R := R) with ⟨A₀, _, _, _, _, emb, J, _, _⟩
  have h₁ := J.nonarchimedean
  have : NonarchimedeanRing A₀ := by
    convert h₁
  apply NonarchimedeanAddGroup.nonarchimedean_of_emb (algebraMap A₀ R : A₀ →+ R) emb

instance (R : Type u) [HuberRing R] : NonarchimedeanRing R where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- For every neighbourhood U of 0 ∈ A,
there exists a pair of definition (A₀, J) such that J ⊆ U. -/
lemma HuberRing.exists_pod_subset (A : Type u) [HuberRing A] (U : Set A) (hU : U ∈ nhds (0 : A)) :
  ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : TopologicalSpace A₀)
    (_ : IsTopologicalRing A₀) (rod : ringOfDefinition A₀ A),
    letI := rod.toAlgebra
    (algebraMap A₀ A) '' (rod.J) ⊆ U := by
  obtain ⟨A₀, _, _, _, ⟨⟨alg, emb, J, fin, top⟩⟩⟩ := HuberRing.pod (R := A)
  obtain ⟨_, H⟩ := isAdic_iff.mp top
  obtain ⟨n, hn⟩ := H (algebraMap A₀ A ⁻¹' U) (emb.continuous.tendsto _ (by simpa using hU))
  refine ⟨A₀, _, _, _, ⟨⟨alg, emb, J ^ (n + 1), Submodule.FG.pow fin _,
    is_ideal_adic_pow top (by grind)⟩, ?_⟩⟩
  simpa using .trans (Ideal.pow_le_pow_right (by grind)) hn

structure IsRingOfIntegralElements (R₀ : Type u) (R : Type u)
    [CommRing R₀] [TopologicalSpace R₀] [HuberRing R] [Algebra R₀ R] : Prop extends
    IsIntegrallyClosedIn R₀ R, IsOpenEmbedding (algebraMap R₀ R) where
  is_power_bounded (r : R₀) : ∀ U ∈ nhds (0 : R), ∃ V ∈ nhds (0 : R),
    ∀ n : ℕ, ∀ v ∈ V, v * (algebraMap R₀ R r) ^ n ∈ U

lemma IsRingOfIntegralElements.isTopologicalRing {R₀ : Type u} {R : Type u}
    [CommRing R₀] [TopologicalSpace R₀] [HuberRing R] [Algebra R₀ R]
    (h : IsRingOfIntegralElements R₀ R) : IsTopologicalRing R₀ where
  continuous_add := by
    rw [h.toIsEmbedding.continuous_iff]
    change Continuous (fun (p : R₀ × R₀) ↦ algebraMap R₀ R (p.1 + p.2))
    simp only [map_add]
    apply Continuous.add
    · apply h.continuous.comp
      exact continuous_fst
    · apply h.continuous.comp
      exact continuous_snd
  continuous_mul := by
    rw [h.toIsEmbedding.continuous_iff]
    change Continuous (fun (p : R₀ × R₀) ↦ algebraMap R₀ R (p.1 * p.2))
    simp only [map_mul]
    apply Continuous.mul
    · apply h.continuous.comp
      exact continuous_fst
    · apply h.continuous.comp
      exact continuous_snd
  continuous_neg := by
    rw [h.toIsEmbedding.continuous_iff]
    change Continuous (fun (p : R₀) ↦ algebraMap R₀ R (-p))
    simp only [map_neg]
    exact h.continuous.neg

structure HuberPair where
  plus : Type u
  carrier : Type u
  [ring : CommRing plus]
  [topologicalSpace : TopologicalSpace plus]
  [huber : HuberRing carrier]
  [algebra : Algebra plus carrier]
  int : IsRingOfIntegralElements plus carrier

namespace HuberPair

instance : CoeSort HuberPair (Type u) where
  coe := carrier

variable (A : HuberPair)

instance : HuberRing A := A.huber

instance : CommRing A.plus := A.ring

instance : TopologicalSpace A.plus := A.topologicalSpace

instance : Algebra A.plus A := A.algebra

instance : IsTopologicalRing A.plus := A.int.isTopologicalRing

end HuberPair
