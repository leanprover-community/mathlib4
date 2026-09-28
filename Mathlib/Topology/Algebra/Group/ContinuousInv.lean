/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuous inversion

Topological results for continuous inversion and negation, including the associated homeomorphisms
and lattice operations on topologies.
-/

@[expose] public section

open Set Filter Topology Pointwise

variable {G H α : Type*}

/-!
### `ContinuousInv` and `ContinuousNeg`
-/

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

@[to_additive]
theorem ContinuousInv.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Group α]
    [DivisionMonoid β] [MonoidHomClass F α β] [tβ : TopologicalSpace β] [ContinuousInv β] (f : F) :
    @ContinuousInv α (tβ.induced f) _ := by
  let _tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_inv]
  fun_prop

@[to_additive]
protected theorem Specializes.inv {x y : G} (h : x ⤳ y) : (x⁻¹) ⤳ (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
protected theorem Inseparable.inv {x y : G} (h : Inseparable x y) : Inseparable (x⁻¹) (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
protected theorem Specializes.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : x ⤳ y) : ∀ m : ℤ, (x ^ m) ⤳ (y ^ m)
  | .ofNat n => by simpa using h.pow n
  | .negSucc n => by simpa using (h.pow (n + 1)).inv

@[to_additive]
protected theorem Inseparable.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : Inseparable x y) (m : ℤ) :
    Inseparable (x ^ m) (y ^ m) :=
  (h.specializes.zpow m).antisymm (h.specializes'.zpow m)

@[to_additive]
instance : ContinuousInv (ULift G) :=
  ⟨continuous_uliftUp.comp (continuous_inv.comp continuous_uliftDown)⟩

@[to_additive]
theorem continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.continuousOn

@[to_additive]
theorem continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.continuousWithinAt

@[to_additive]
theorem continuousAt_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.continuousAt

@[to_additive]
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuousAt_inv

@[to_additive]
instance OrderDual.instContinuousInv : ContinuousInv Gᵒᵈ := ‹ContinuousInv G›

@[to_additive]
instance Prod.continuousInv [TopologicalSpace H] [Inv H] [ContinuousInv H] :
    ContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prodMk continuous_inv.snd'⟩

variable {ι : Type*}

@[to_additive]
instance Pi.continuousInv {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, ContinuousInv (C i)] : ContinuousInv (∀ i, C i) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

/-- A version of `Pi.continuousInv` for non-dependent functions. It is needed because sometimes
Lean fails to use `Pi.continuousInv` for non-dependent functions. -/
@[to_additive
  /-- A version of `Pi.continuousNeg` for non-dependent functions. It is needed
  because sometimes Lean fails to use `Pi.continuousNeg` for non-dependent functions. -/]
instance Pi.has_continuous_inv' : ContinuousInv (ι → G) :=
  Pi.continuousInv

@[to_additive]
instance (priority := 100) continuousInv_of_discreteTopology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousInv_of_indiscreteTopology [TopologicalSpace H] [Inv H]
    [IndiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
instance (priority := 100) continuousDiv_of_discreteTopology [TopologicalSpace H] [Div H]
    [DiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousDiv_of_indiscreteTopology [TopologicalSpace H] [Div H]
    [IndiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
instance (priority := 100) isTopologicalGroup_of_discreteTopology
    [TopologicalSpace H] [Group H] [DiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias topologicalGroup_of_discreteTopology := isTopologicalGroup_of_discreteTopology

@[to_additive]
instance (priority := 100) isTopologicalGroup_of_indiscreteTopology
    [TopologicalSpace H] [Group H] [IndiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias topologicalGroup_of_indiscreteTopology := isTopologicalGroup_of_indiscreteTopology

section PointwiseLimits

variable (G₁ G₂ : Type*) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
theorem isClosed_setOfPred_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_inv := isClosed_setOfPred_map_inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_neg := isClosed_setOfPred_map_neg

end PointwiseLimits

instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H) where
  continuous_neg := @continuous_inv H _ _ _

instance [TopologicalSpace H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H) where
  continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] {s : Set G}

@[to_additive (attr := simp)]
theorem tendsto_inv_iff {l : Filter α} {m : α → G} {a : G} :
    Tendsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, Tendsto.inv⟩

@[to_additive]
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv_eq_inv]
  exact hs.image continuous_inv

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive /-- Negation in a topological group as a homeomorphism. -/]
protected def Homeomorph.inv (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
    [ContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with }

@[to_additive (attr := simp)]
lemma Homeomorph.symm_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    (Homeomorph.inv G).symm = Homeomorph.inv G := rfl

@[to_additive (attr := simp)]
lemma Homeomorph.coe_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    ⇑(Homeomorph.inv G) = Inv.inv := rfl

@[to_additive]
theorem nhds_inv (a : G) : 𝓝 a⁻¹ = (𝓝 a)⁻¹ :=
  ((Homeomorph.inv G).map_nhds_eq a).symm

@[to_additive]
theorem isOpenMap_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isOpenMap

@[to_additive]
theorem isClosedMap_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isClosedMap

variable {G}

@[to_additive]
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
theorem inv_closure : ∀ s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[to_additive (attr := simp)]
lemma continuous_inv_iff : Continuous f⁻¹ ↔ Continuous f := (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]
lemma continuousAt_inv_iff : ContinuousAt f⁻¹ x ↔ ContinuousAt f x :=
  (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]
lemma continuousOn_inv_iff : ContinuousOn f⁻¹ s ↔ ContinuousOn f s :=
  (Homeomorph.inv G).comp_continuousOn_iff _ _

@[to_additive] alias ⟨Continuous.of_inv, _⟩ := continuous_inv_iff
@[to_additive] alias ⟨ContinuousAt.of_inv, _⟩ := continuousAt_inv_iff
@[to_additive] alias ⟨ContinuousOn.of_inv, _⟩ := continuousOn_inv_iff

@[to_additive (attr := simp)]
theorem Filter.inv_nhdsNE {a : G} : (𝓝[≠] a)⁻¹ = 𝓝[≠] (a⁻¹) := by
  convert! (Homeomorph.inv G).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort*} [Inv G]

@[to_additive]
theorem continuousInv_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @ContinuousInv G t _) : @ContinuousInv G (sInf ts) _ :=
  letI := sInf ts
  { continuous_inv :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }

@[to_additive]
theorem continuousInv_iInf {ts' : ι' → TopologicalSpace G}
    (h' : ∀ i, @ContinuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
    (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

@[to_additive]
theorem Topology.IsInducing.continuousInv {G H : Type*} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [ContinuousInv H] {f : G → H} (hf : IsInducing f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G :=
  ⟨hf.continuous_iff.2 <| by simpa only [Function.comp_def, hf_inv] using hf.continuous.fun_inv⟩
