/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Maps on homogeneous ideals

In this file we define `HomogeneousIdeal.map` and `HomogeneousIdeal.comap`.
-/

@[expose] public section

variable {A B C σ τ ω ι F G : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [SetLike σ A] [SetLike τ B] [SetLike ω C]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddSubmonoidClass ω C]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)

namespace HomogeneousIdeal

/-- Map a homogeneous ideal along a graded ring homomorphism. The underlying ideal is
(definitionally) equal to `Ideal.map`. -/
def map (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal ℬ where
  __ := I.toIdeal.map f
  is_homogeneous' i b hb := by
    rw [Ideal.map] at hb
    induction hb using Submodule.span_induction generalizing i with
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_directSumDecompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
      exact sum_mem fun ij hij ↦ Ideal.mul_mem_left _ _ <| ih _

/-- Pull back a homogeneous ideal along a graded ring homomorphism.
The underlying ideal is (definitionally) equal to `Ideal.comap`, whose underlying set is
definitionally equal to the preimage. -/
def comap (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap, HomogeneousIdeal.mem_iff, f.map_directSumDecompose]
    exact I.2 _ ha

variable {I I₁ I₂ I₃ : HomogeneousIdeal 𝒜} {J J₁ J₂ J₃ : HomogeneousIdeal ℬ}
  {K : HomogeneousIdeal 𝒞}

lemma map_le_iff_le_comap : I.map f ≤ J ↔ I ≤ J.comap f := Ideal.map_le_iff_le_comap

alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦
  map_le_iff_le_comap f

@[mono, aesop safe apply] lemma map_mono : Monotone (map f) := (gc_map_comap f).monotone_l

@[mono] lemma comap_mono : Monotone (comap f) := (gc_map_comap f).monotone_u

@[simp] lemma toIdeal_comap : (J.comap f).toIdeal = J.toIdeal.comap f := rfl

@[simp] lemma coe_comap : J.comap f = f ⁻¹' J := rfl

@[simp] lemma toIdeal_map : (I.map f).toIdeal = I.toIdeal.map f := rfl

instance isPrime_comap [J.toIdeal.IsPrime] : (J.comap f).toIdeal.IsPrime :=
  inferInstanceAs (J.toIdeal.comap f).IsPrime -- this shows that the simpNF already has the instance

@[simp] lemma map_id : I.map (GradedRingHom.id 𝒜) = I := ext <| Ideal.map_id _

lemma map_map : (I.map f).map g = I.map (g.comp f) := ext <| Ideal.map_map _ _

lemma map_comp : I.map (g.comp f) = (I.map f).map g := (map_map f g).symm

@[simp] lemma comap_id : I.comap (GradedRingHom.id 𝒜) = I := rfl

lemma comap_comap : (K.comap g).comap f = K.comap (g.comp f) := rfl

end HomogeneousIdeal
