import Mathlib.AdicSpace.HuberPair
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

universe u

open Topology TopologicalSpace

def Spv (R : Type u) [CommRing R] : Type u := ValuativeRel R

def Spv.outΓ₀ {R : Type u} [CommRing R] (v : Spv R) : Type u :=
  letI : ValuativeRel R := v
  ValuativeRel.ValueGroupWithZero R

noncomputable instance {R : Type u} [CommRing R] (v : Spv R) :
    LinearOrderedCommGroupWithZero v.outΓ₀ := by
  dsimp [Spv.outΓ₀]
  infer_instance

noncomputable def Spv.out {R : Type u} [CommRing R] (v : Spv R) : Valuation R (v.outΓ₀) :=
  letI : ValuativeRel R := v
  ValuativeRel.valuation R

noncomputable instance (R : Type u) [CommRing R] :
    CoeFun (Spv R) (fun v ↦ (R → Spv.outΓ₀ v)) where
  coe v := (v.out : R → v.outΓ₀)

noncomputable def Spv.lift {R : Type u} [CommRing R] {X : Type*}
    (f : ∀ ⦃Γ₀ : Type u⦄ [LinearOrderedCommGroupWithZero Γ₀], Valuation R Γ₀ → X) (v : Spv R) : X :=
  f (out v)

def Spv.basicOpen {R : Type u} [CommRing R] (r s : R) : Set (Spv R) :=
  {v | v r ≤ v s ∧ v s ≠ 0}

instance (R : Type u) [CommRing R] : TopologicalSpace (Spv R) :=
  TopologicalSpace.generateFrom {U | ∃ r s, U = Spv.basicOpen r s}

def ValuativeRel.inducedTopology (R : Type u) [CommRing R] [ValuativeRel R] : TopologicalSpace R :=
  let t : TopologicalSpace (ValuativeRel.ValueGroupWithZero R) := {
    IsOpen s := 0 ∉ s ∨ ∃ γ, γ ≠ 0 ∧ {x | x < γ} ⊆ s
    isOpen_univ := Or.inr ⟨1, by simp⟩
    isOpen_inter s t := by
      rintro (hs | ⟨γs, hs⟩) (ht | ⟨γt, ht⟩)
      all_goals try tauto_set
      right
      refine ⟨min γs γt, by simp_all [min_eq_iff], fun _ _ ↦ ⟨?_, ?_⟩⟩
      · apply hs.2
        simp_all
      · apply ht.2
        simp_all
    isOpen_sUnion s hs := by
      simp only [Set.mem_sUnion, not_exists, not_and, ne_eq]
      by_cases h : ∀ x ∈ s, 0 ∉ x
      · simp_all
      right
      push_neg at h
      obtain ⟨x, hx, h₀⟩ := h
      specialize hs x hx
      simp only [h₀, not_true_eq_false, ne_eq, false_or] at hs
      obtain ⟨γ, hγ⟩ := hs
      refine ⟨γ, hγ.1, fun _ _ ↦ ?_⟩
      aesop }
  TopologicalSpace.induced (valuation R) t

class ValuativeRel.IsContinuous (R : Type u) [CommRing R] [ValuativeRel R]
    [t : TopologicalSpace R] : Prop where
  induced_le  : ValuativeRel.inducedTopology R ≤ t

def Spv.IsContinuous {R : Type u} [CommRing R] [t : TopologicalSpace R] (v : Spv R) : Prop :=
  letI : ValuativeRel R := v
  ValuativeRel.IsContinuous R

def ValuativeRel.comap {R S : Type*} [CommRing R] [CommRing S] (v : ValuativeRel S) (f : R →+* S) :
    ValuativeRel R where
  rel x y := f x ≤ᵥ f y
  rel_total x y := by exact rel_total (f x) (f y)
  rel_trans hxy hyz := by apply rel_trans hxy hyz
  rel_add _ _ := by
    simp only [map_add]
    apply rel_add
    all_goals assumption
  rel_mul_right _ _ := by
    simp only [map_mul]
    apply rel_mul_right
    assumption
  rel_mul_cancel {x y z} h₁ h₂ := by
    simp only [map_mul] at h₂
    simp only [map_zero] at h₁
    apply rel_mul_cancel (z := f z)
    all_goals assumption
  not_rel_one_zero := by
    simp only [map_one, map_zero]
    apply not_rel_one_zero

nonrec def Spv.comap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (v : Spv S) : Spv R :=
  v.comap f

def spa (A : HuberPair) : Type u :=
  {v : Spv A // v.IsContinuous ∧ ∀ r : A.plus, v (algebraMap A.plus A r) ≤ 1}

instance {A : HuberPair} : CoeOut (spa A) (Spv A) := ⟨Subtype.val⟩

noncomputable instance {A : HuberPair} :
    CoeFun (spa A) (fun (v : spa A) ↦ (A → Spv.outΓ₀ (v : Spv A))) where
  coe v := ((v : Spv A).out : A → (v : Spv A).outΓ₀)
