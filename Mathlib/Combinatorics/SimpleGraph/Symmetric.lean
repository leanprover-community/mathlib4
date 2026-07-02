/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Representation
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Tactic.Group

/-!
# Symmetric graphs and Lorimer's theorem

A *symmetric* (arc-transitive) graph is a coset graph `Sab(G, H, HaH)` where `a` is an
involution not in `H`. This file proves both directions of Lorimer's theorem:
the forward direction shows `Sab(G, H, HaH)` is arc-transitive when `a² = 1` and `a ∉ H`,
and the reverse direction shows every arc-transitive graph's connection set is a single
double coset `HaH` where `a` swaps an arc.

## Main definitions

* `doubleCoset_isConnectionSet` — `HaH` is a valid connection set when `a² = 1, a ∉ H`
* `sabidussiSymmetricGraph` — the coset graph `Sab(G, H, HaH)`

## Main results

* `lorimer_forward` — `Sab(G, H, HaH)` is arc-transitive when `a² = 1, a ∉ H`
* `connectionSet_eq_doubleCoset` — under arc-transitivity, the connection set is a single
  double coset
* `lorimer_reverse` — every arc-transitive graph has an arc-swapping involution `a` with
  `a ∉ Gᵥ`, `a² ∈ Gᵥ`, and `D = GᵥaGᵥ`

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798, Chapter 2 §§3–4.
* Lorimer, *Vertex-transitive graphs*, 1984.
-/

@[expose] public section

variable {G : Type*} [Group G]

private theorem inv_eq_self_of_sq_eq_one {a : G} (ha : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_left (by rwa [← sq])

open DoubleCoset in
/-- `HaH` is a valid connection set when `a² = 1` and `a ∉ H`. -/
theorem doubleCoset_isConnectionSet (H : Subgroup G) (a : G)
    (ha_sq : a ^ 2 = 1) (ha_not : a ∉ H) :
    IsConnectionSet H (doubleCoset a (H : Set G) H) where
  double_coset_stable := by
    intro d hd k₁ hk₁ k₂ hk₂
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hd
    exact mem_doubleCoset.mpr
      ⟨k₁ * h₁, H.mul_mem hk₁ hh₁, h₂ * k₂, H.mul_mem hh₂ hk₂, by group⟩
  inv_mem := by
    intro d hd
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hd
    have ha_inv := inv_eq_self_of_sq_eq_one ha_sq
    refine mem_doubleCoset.mpr ⟨h₂⁻¹, H.inv_mem hh₂, h₁⁻¹, H.inv_mem hh₁, ?_⟩
    calc (h₁ * a * h₂)⁻¹ = h₂⁻¹ * a⁻¹ * h₁⁻¹ := by group
      _ = h₂⁻¹ * a * h₁⁻¹ := by rw [ha_inv]
  disjoint := by
    rw [Set.disjoint_left]
    intro g hg hgH
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hg
    have : a = h₁⁻¹ * (h₁ * a * h₂) * h₂⁻¹ := by group
    rw [this] at ha_not
    exact ha_not (H.mul_mem (H.mul_mem (H.inv_mem hh₁) hgH) (H.inv_mem hh₂))

section Lorimer

variable (H : Subgroup G) (a : G) (ha_sq : a ^ 2 = 1) (ha_not : a ∉ H)

/-- The coset graph `Sab(G, H, HaH)` for an involution `a ∉ H`. -/
noncomputable abbrev sabidussiSymmetricGraph :=
  SimpleGraph.cosetGraph H (DoubleCoset.doubleCoset a (H : Set G) H)
    (doubleCoset_isConnectionSet H a ha_sq ha_not)

/-- Local transitivity at the identity coset. -/
private theorem locallyTransitive_at_one :
    IsLocallyTransitive G (G ⧸ H) (sabidussiSymmetricGraph H a ha_sq ha_not)
      ((1 : G) : G ⧸ H) := by
  intro w₁ w₂ hw₁ hw₂
  revert hw₁ hw₂
  refine Quotient.inductionOn₂ w₁ w₂ fun y₁ y₂ hy₁ hy₂ => ?_
  change (1 : G)⁻¹ * y₁ ∈ _ at hy₁; change (1 : G)⁻¹ * y₂ ∈ _ at hy₂
  simp only [inv_one, one_mul] at hy₁ hy₂
  obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy₁
  obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy₂
  refine ⟨h₂ * h₁⁻¹, ?_, ?_⟩
  · change (h₂ * h₁⁻¹) • ((1 : G) : G ⧸ H) = (1 : G)
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
    apply QuotientGroup.eq.mpr
    show (h₂ * h₁⁻¹)⁻¹ * 1 ∈ H
    simp only [mul_one, mul_inv_rev, inv_inv]
    exact H.mul_mem hh₁ (H.inv_mem hh₂)
  · change (h₂ * h₁⁻¹) • ((h₁ * a * k₁ : G) : G ⧸ H) = (h₂ * a * k₂ : G)
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have ha_inv := inv_eq_self_of_sq_eq_one ha_sq
    suffices h : (h₂ * h₁⁻¹ * (h₁ * a * k₁))⁻¹ * (h₂ * a * k₂) = k₁⁻¹ * k₂ by
      rw [h]; exact H.mul_mem (H.inv_mem hk₁) hk₂
    calc (h₂ * h₁⁻¹ * (h₁ * a * k₁))⁻¹ * (h₂ * a * k₂)
        = (h₂ * a * k₁)⁻¹ * (h₂ * a * k₂) := by congr 1; group
      _ = k₁⁻¹ * a⁻¹ * (h₂⁻¹ * (h₂ * a * k₂)) := by group
      _ = k₁⁻¹ * a⁻¹ * (a * k₂) := by rw [show h₂⁻¹ * (h₂ * a * k₂) = a * k₂ from by group]
      _ = k₁⁻¹ * (a⁻¹ * a) * k₂ := by group
      _ = k₁⁻¹ * k₂ := by rw [ha_inv]; simp [← sq, ha_sq]

/-- Local transitivity at any vertex, transported from `⟦1⟧`. -/
private theorem locallyTransitive_everywhere :
    ∀ q : G ⧸ H,
      IsLocallyTransitive G (G ⧸ H) (sabidussiSymmetricGraph H a ha_sq ha_not) q := by
  intro q w₁ w₂ hw₁ hw₂
  set Γ := sabidussiSymmetricGraph H a ha_sq ha_not
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ((1 : G) : G ⧸ H) q
  have hw₁' : Γ.Adj ((1 : G) : G ⧸ H) (g⁻¹ • w₁) := by
    have := (@GraphAction.adj_smul_iff G _ _ _ Γ _ g⁻¹ q w₁).mpr hw₁
    rwa [← hg, inv_smul_smul] at this
  have hw₂' : Γ.Adj ((1 : G) : G ⧸ H) (g⁻¹ • w₂) := by
    have := (@GraphAction.adj_smul_iff G _ _ _ Γ _ g⁻¹ q w₂).mpr hw₂
    rwa [← hg, inv_smul_smul] at this
  obtain ⟨h, hfix, hsend⟩ :=
    locallyTransitive_at_one H a ha_sq ha_not (g⁻¹ • w₁) (g⁻¹ • w₂) hw₁' hw₂'
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · calc (g * h * g⁻¹) • q = g • (h • (g⁻¹ • q)) := by simp [mul_smul]
      _ = g • (h • ((1 : G) : G ⧸ H)) := by rw [← hg, inv_smul_smul]
      _ = g • ((1 : G) : G ⧸ H) := by rw [hfix]
      _ = q := hg
  · calc (g * h * g⁻¹) • w₁ = g • (h • (g⁻¹ • w₁)) := by simp [mul_smul]
      _ = g • (g⁻¹ • w₂) := by rw [hsend]
      _ = w₂ := smul_inv_smul g w₂

/-- **Lorimer's Theorem (forward direction)**: `Sab(G, H, HaH)` is arc-transitive
when `a² = 1` and `a ∉ H`. -/
theorem lorimer_forward :
    IsArcTransitive G (G ⧸ H) (sabidussiSymmetricGraph H a ha_sq ha_not) :=
  isArcTransitive_of_vertexTransitive_locallyTransitive _
    (locallyTransitive_everywhere H a ha_sq ha_not)

end Lorimer

/-! ### Lorimer's theorem (reverse direction) -/

/-- Under arc-transitivity, the stabilizer acts transitively on neighbors. -/
theorem stabilizer_transitive_on_neighbors {V : Type*} [MulAction G V]
    (Γ : SimpleGraph V) [IsArcTransitive G V Γ]
    (v : V) {w u : V} (hw : Γ.Adj v w) (hu : Γ.Adj v u) :
    ∃ h ∈ MulAction.stabilizer G v, h • w = u := by
  obtain ⟨g, hgv, hgw⟩ := @IsArcTransitive.arc_transitive G V _ _ Γ _ v w v u hw hu
  exact ⟨g, MulAction.mem_stabilizer_iff.mpr hgv, hgw⟩

/-- Under arc-transitivity, the connection set is a single double coset `HaH`. -/
theorem connectionSet_eq_doubleCoset {V : Type*} [MulAction G V]
    (Γ : SimpleGraph V) [IsArcTransitive G V Γ]
    (v : V) {a : G} (ha : a ∈ connectionSet G Γ v) :
    connectionSet G Γ v =
      DoubleCoset.doubleCoset a (MulAction.stabilizer G v : Set G)
        (MulAction.stabilizer G v) := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, hh, hhw⟩ := @stabilizer_transitive_on_neighbors G _ V _ Γ _ v _ _ ha hg
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨h, hh, (g⁻¹ * (h * a))⁻¹,
      (MulAction.stabilizer G v).inv_mem (by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hhw, inv_smul_smul]),
      by group⟩
  · intro hg
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    exact connectionSet.double_coset_stable v ha hh₁ hh₂

/-- **Lorimer's Theorem (reverse direction)**: Every arc-transitive graph's connection
set is a single `(H,H)`-double coset, determined by the arc-swapping element.

Combined with `sabidussiIso`, this shows every arc-transitive graph
is `Sab(G, stabilizer G v, HaH)` where `a` swaps an arc `(v,w)`. -/
theorem lorimer_reverse {V : Type*} [MulAction G V]
    (Γ : SimpleGraph V) [IsArcTransitive G V Γ]
    (v w : V) (hvw : Γ.Adj v w) :
    ∃ a : G, a • v = w ∧ a • w = v ∧ a ∉ MulAction.stabilizer G v ∧
      a ^ 2 ∈ MulAction.stabilizer G v ∧
      connectionSet G Γ v =
        DoubleCoset.doubleCoset a (MulAction.stabilizer G v : Set G)
          (MulAction.stabilizer G v) := by
  obtain ⟨a, hav, haw⟩ :=
    @IsArcTransitive.arc_transitive G V _ _ Γ _ v w w v hvw (Γ.symm hvw)
  refine ⟨a, hav, haw, ?_, ?_, ?_⟩
  · intro hmem
    rw [MulAction.mem_stabilizer_iff] at hmem
    rw [hmem] at hav
    exact Γ.loopless.irrefl v (hav ▸ hvw)
  · rw [MulAction.mem_stabilizer_iff, sq, mul_smul, hav, haw]
  · exact connectionSet_eq_doubleCoset Γ v (by
      simp only [connectionSet, Set.mem_setOf_eq, hav]; exact hvw)
