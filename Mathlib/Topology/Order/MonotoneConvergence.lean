/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form "if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`", as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `IsLUB`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `Prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

@[expose] public section

open Filter Set Function
open scoped Topology

variable {α β : Type*}

/-- We say that `α` is a `SupConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → ∞` (formally, at the filter `Filter.atTop`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atTop_isLUB`.

This property holds for linear orders with order topology as well as their products. -/
class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    ∀ (a : α) (s : Set α), IsLUB s a → Tendsto ((↑) : s → α) atTop (𝓝 a)

/-- We say that `α` is an `InfConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `Filter.atBot`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atBot_isGLB`.

This property holds for linear orders with order topology as well as their products. -/
class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞` -/
  tendsto_coe_atBot_isGLB :
    ∀ (a : α) (s : Set α), IsGLB s a → Tendsto ((↑) : s → α) atBot (𝓝 a)

instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ where
  tendsto_coe_atTop_isLUB a s ha := by
    have ha' : IsGLB (toDual ⁻¹' s) (ofDual a) := by
      constructor
      · intro x hx; exact ha.1 (by simpa using hx)
      · intro b hb; exact ha.2 (fun x hx => hb (by simpa using hx))
    have h := InfConvergenceClass.tendsto_coe_atBot_isGLB (ofDual a) (toDual ⁻¹' s) ha'
    -- h : Tendsto (Subtype.val : ↑(toDual ⁻¹' s) → α) atBot (𝓝 (ofDual a))
    -- We need: Tendsto (Subtype.val : ↑s → αᵒᵈ) atTop (𝓝 a)
    -- Define the identification map φ : ↑(toDual ⁻¹' s) → ↑s
    let φ : ↑(toDual ⁻¹' s) → ↑s := fun ⟨x, hx⟩ => ⟨toDual x, hx⟩
    -- Show φ sends atBot to atTop
    have hφ : Tendsto φ atBot atTop := by
      rw [Filter.tendsto_atTop]
      intro ⟨b, hb⟩
      refine mem_of_superset (Filter.mem_atBot (⟨ofDual b, by simpa using hb⟩ : ↑(toDual ⁻¹' s)))
        fun ⟨x, hx⟩ hle => ?_
      -- hle : x ≤ ofDual b in α, so toDual x ≥ b in αᵒᵈ, i.e., b ≤ toDual x
      exact hle
    -- Subtype.val ∘ φ = toDual ∘ Subtype.val
    have hfact : (Subtype.val : ↑s → αᵒᵈ) ∘ φ = toDual ∘ (Subtype.val : ↑(toDual ⁻¹' s) → α) :=
      funext fun ⟨x, hx⟩ => rfl
    -- Compose: Tendsto (toDual ∘ Subtype.val) atBot (𝓝 a)
    have h2 : Tendsto ((Subtype.val : ↑s → αᵒᵈ) ∘ φ) atBot (𝓝 a) := by
      rw [hfact, show a = toDual (ofDual a) from (toDual_ofDual a).symm]
      exact continuous_toDual.continuousAt.tendsto.comp h
    -- Define the inverse ψ : ↑s → ↑(toDual ⁻¹' s)
    let ψ : ↑s → ↑(toDual ⁻¹' s) := fun ⟨y, hy⟩ =>
      ⟨ofDual y, by change toDual (ofDual y) ∈ s; rwa [toDual_ofDual]⟩
    -- φ ∘ ψ = id
    have hφψ : φ ∘ ψ =ᶠ[atTop] id :=
      Filter.Eventually.of_forall fun ⟨y, hy⟩ => Subtype.ext (by simp [φ, ψ])
    -- ψ sends atTop to atBot
    have hψ : Tendsto ψ atTop atBot := by
      rw [Filter.tendsto_atBot]
      intro ⟨b, hb⟩
      refine mem_of_superset (Filter.mem_atTop (⟨toDual b, hb⟩ : ↑s))
        fun ⟨y, hy⟩ hle => ?_
      -- hle : toDual b ≤ y in αᵒᵈ, i.e., ofDual y ≤ b in α
      exact hle
    -- Now: map φ atBot = atTop
    have hmap : Filter.map φ atBot = atTop :=
      le_antisymm hφ (le_map_of_right_inverse hφψ hψ)
    -- h2 : Tendsto (Subtype.val ∘ φ) atBot (𝓝 a)
    -- which is: map Subtype.val (map φ atBot) ≤ 𝓝 a
    -- Since map φ atBot = atTop, this is: Tendsto Subtype.val atTop (𝓝 a)
    change Tendsto Subtype.val atTop (𝓝 a)
    rw [show atTop = Filter.map φ atBot from hmap.symm]
    exact h2

instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ where
  tendsto_coe_atBot_isGLB a s ha := by
    have ha' : IsLUB (toDual ⁻¹' s) (ofDual a) := by
      constructor
      · intro x hx; exact ha.1 (by simpa using hx)
      · intro b hb; exact ha.2 (fun x hx => hb (by simpa using hx))
    have h := SupConvergenceClass.tendsto_coe_atTop_isLUB (ofDual a) (toDual ⁻¹' s) ha'
    -- h : Tendsto (Subtype.val : ↑(toDual ⁻¹' s) → α) atTop (𝓝 (ofDual a))
    -- We need: Tendsto (Subtype.val : ↑s → αᵒᵈ) atBot (𝓝 a)
    let φ : ↑(toDual ⁻¹' s) → ↑s := fun ⟨x, hx⟩ => ⟨toDual x, hx⟩
    have hφ : Tendsto φ atTop atBot := by
      rw [Filter.tendsto_atBot]
      intro ⟨b, hb⟩
      refine mem_of_superset (Filter.mem_atTop (⟨ofDual b, by simpa using hb⟩ : ↑(toDual ⁻¹' s)))
        fun ⟨x, hx⟩ hle => ?_
      -- hle : ofDual b ≤ x in α, so toDual x ≤ b in αᵒᵈ
      exact hle
    have hfact : (Subtype.val : ↑s → αᵒᵈ) ∘ φ = toDual ∘ (Subtype.val : ↑(toDual ⁻¹' s) → α) :=
      funext fun ⟨x, hx⟩ => rfl
    have h2 : Tendsto ((Subtype.val : ↑s → αᵒᵈ) ∘ φ) atTop (𝓝 a) := by
      rw [hfact, show a = toDual (ofDual a) from (toDual_ofDual a).symm]
      exact continuous_toDual.continuousAt.tendsto.comp h
    let ψ : ↑s → ↑(toDual ⁻¹' s) := fun ⟨y, hy⟩ =>
      ⟨ofDual y, by change toDual (ofDual y) ∈ s; rwa [toDual_ofDual]⟩
    have hφψ : φ ∘ ψ =ᶠ[atBot] id :=
      Filter.Eventually.of_forall fun ⟨y, hy⟩ => Subtype.ext (by simp [φ, ψ])
    have hψ : Tendsto ψ atBot atTop := by
      rw [Filter.tendsto_atTop]
      intro ⟨b, hb⟩
      refine mem_of_superset (Filter.mem_atBot (⟨toDual b, hb⟩ : ↑s))
        fun ⟨y, hy⟩ hle => ?_
      -- hle : y ≤ toDual b in αᵒᵈ, i.e., b ≤ ofDual y in α
      exact hle
    have hmap : Filter.map φ atTop = atBot :=
      le_antisymm hφ (le_map_of_right_inverse hφψ hψ)
    change Tendsto Subtype.val atBot (𝓝 a)
    rw [show atBot = Filter.map φ atTop from hmap.symm]
    exact h2

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    exact (eventually_ge_atTop c).mono fun x hx => bc.trans_le hx
  · exact Eventually.of_forall fun x => (ha.1 x.2).trans_lt hb

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · exact Eventually.of_forall fun x => hb.trans_le (ha.1 x.2)
  · rcases ha.exists_between hb with ⟨c, hcs, _, hcb⟩
    lift c to s using hcs
    exact (eventually_le_atBot c).mono fun x hx =>
      show (x : α) < b from LE.le.trans_lt (α := α) hx hcb

section

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atBot atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact tendsto_atBot_atTop_of_antitone (fun _ _ h => h_anti h)
    fun b => b.2.imp fun a ha => ha.ge

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atBot atBot from
    (InfConvergenceClass.tendsto_coe_atBot_isGLB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atBot_atBot fun b => b.2.imp fun a ha => ha.le

theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atBot from
    (InfConvergenceClass.tendsto_coe_atBot_isGLB _ _ ha).comp this
  exact tendsto_atTop_atBot_of_antitone (fun _ _ h => h_anti h)
    fun b => b.2.imp fun a ha => ha.le

end IsGLB

section CiSup

variable [ConditionallyCompleteLattice α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  cases isEmpty_or_nonempty ι
  exacts [tendsto_of_isEmpty, tendsto_atTop_isLUB h_mono (isLUB_ciSup hbdd)]

theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by
  cases isEmpty_or_nonempty ι
  exacts [tendsto_of_isEmpty, tendsto_atBot_isLUB h_anti (isLUB_ciSup hbdd)]

end CiSup

section CiInf

variable [ConditionallyCompleteLattice α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by
  cases isEmpty_or_nonempty ι
  exacts [tendsto_of_isEmpty, tendsto_atBot_isGLB h_mono (isGLB_ciInf hbdd)]

theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by
  cases isEmpty_or_nonempty ι
  exacts [tendsto_of_isEmpty, tendsto_atTop_isGLB h_anti (isGLB_ciInf hbdd)]

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

end iInf

end

instance Prod.supConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [SupConvergenceClass α] [SupConvergenceClass β] : SupConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod, ← range_restrict, ← range_restrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.restrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.restrict s) h.2
  exact A.prodMk_nhds B

instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isGLB_prod, ← range_restrict, ← range_restrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atBot (𝓝 a) :=
    tendsto_atBot_isGLB (monotone_fst.restrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atBot (𝓝 b) :=
    tendsto_atBot_isGLB (monotone_snd.restrict s) h.2
  exact A.prodMk_nhds B

instance Pi.supConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_restrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).restrict _) (h i)

instance Pi.infConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isGLB_pi, ← range_restrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atBot_isGLB ((monotone_eval _).restrict _) (h i)

instance Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι → α) :=
  supConvergenceClass

instance Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι → α) :=
  Pi.infConvergenceClass

theorem tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H

@[deprecated (since := "2026-01-22")] alias tendsto_of_monotone := tendsto_atTop_of_monotone

theorem tendsto_atTop_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atTop atBot ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddBelow (range f) then Or.inr ⟨_, tendsto_atTop_ciInf h_mono H⟩
  else Or.inl <| tendsto_atTop_atBot_of_antitone h_mono fun b => by
    rcases not_bddBelow_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩; exact ⟨N, le_of_lt hN⟩

@[deprecated (since := "2026-01-22")] alias tendsto_of_antitone := tendsto_atTop_of_antitone

theorem tendsto_atBot_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atBot atBot ∨ ∃ l, Tendsto f atBot (𝓝 l) := by
  classical
  exact if H : BddBelow (range f) then Or.inr ⟨_, tendsto_atBot_ciInf h_mono H⟩
  else Or.inl <| tendsto_atBot_atBot_of_monotone' h_mono H

theorem tendsto_atBot_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atBot atTop ∨ ∃ l, Tendsto f atBot (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atBot_ciSup h_mono H⟩
  else Or.inl <| tendsto_atBot_atTop_of_antitone h_mono fun b => by
    rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩; exact ⟨N, le_of_lt hN⟩

theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

theorem tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMinOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Antitone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_antitone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atBot_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

/-! The next family of results, such as `isLUB_of_tendsto_atTop` and `iSup_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `Filter.atTop`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`IsLUB.isLUB_of_tendsto`, `IsGLB.isGLB_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/

theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.le_of_tendsto ha ((eventually_le_atBot b).mono fun _ hxy => hf hxy)

theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.le_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_le_atBot b).mono fun _ hxy => hf hxy)

theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.le_of_tendsto ha b
  · exact fun _ hb => ge_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.le_of_tendsto ha b
  · exact fun _ hb => ge_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) → iSup f = a :=
  tendsto_nhds_unique (tendsto_atTop_iSup hf)

theorem iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) → iInf f = a :=
  tendsto_nhds_unique (tendsto_atTop_iInf hf)

theorem iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i) :=
  ge_antisymm
    (iInf_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iInf_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i) :=
  ge_antisymm
    (iInf_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iInf_mono' fun i => ⟨φ i, le_rfl⟩)
