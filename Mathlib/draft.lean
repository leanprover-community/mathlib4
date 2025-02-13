import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Order.LiminfLimsup

open Topology Filter Set

theorem Filter.isBoundedUnder_map_iff {ι κ X : Type*} {r : X → X → Prop}
    {f : ι → X} {φ : κ → ι} {𝓕 : Filter κ} :
    (map φ 𝓕).IsBoundedUnder r f ↔ 𝓕.IsBoundedUnder r (f ∘ φ) :=
  Iff.rfl

theorem Filter.Tendsto.isBoundedUnder_comp {ι κ X : Type*} {r : X → X → Prop}
    {f : ι → X} {φ : κ → ι} {𝓕 : Filter ι} {𝓖 : Filter κ} (φ_tendsto : Tendsto φ 𝓖 𝓕)
    (𝓕_bounded : 𝓕.IsBoundedUnder r f) :
    𝓖.IsBoundedUnder r (f ∘ φ) :=
  isBoundedUnder_map_iff.mp (𝓕_bounded.mono φ_tendsto)

theorem disjoint_atTop_iff_isBounded_le {X : Type*}
    [LinearOrder X] [Nonempty X] [NoMaxOrder X] (𝓕 : Filter X) :
    Disjoint 𝓕 atTop ↔ 𝓕.IsBounded (· ≤ ·) := by
  simp [atTop_basis_Ioi.disjoint_iff_right, IsBounded, compl_Ioi, Iic, eventually_iff]

@[to_additive]
theorem UniformGroup.cauchy_iff_tendsto {G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter G) :
    Cauchy 𝓕 ↔ NeBot 𝓕 ∧ Tendsto (fun p ↦ p.1 / p.2) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [Cauchy, uniformity_eq_comap_nhds_one_swapped, ← tendsto_iff_comap]

@[to_additive]
theorem UniformGroup.cauchy_iff_tendsto' {G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter G) [h : NeBot 𝓕] :
    Cauchy 𝓕 ↔ Tendsto (fun p ↦ p.1 / p.2) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_iff_tendsto, h]

@[to_additive]
theorem UniformGroup.cauchy_iff_tendsto_swapped {G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter G) :
    Cauchy 𝓕 ↔ NeBot 𝓕 ∧ Tendsto (fun p ↦ p.2 / p.1) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [Cauchy, uniformity_eq_comap_nhds_one, ← tendsto_iff_comap]

@[to_additive]
theorem UniformGroup.cauchy_iff_tendsto_swapped' {G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter G) [h : NeBot 𝓕] :
    Cauchy 𝓕 ↔ Tendsto (fun p ↦ p.2 / p.1) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_iff_tendsto_swapped, h]

@[to_additive]
theorem UniformGroup.cauchy_map_iff_tendsto {ι G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter ι)
    (f : ι → G) :
    Cauchy (map f 𝓕) ↔ NeBot 𝓕 ∧ Tendsto (fun p ↦ f p.1 / f p.2) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_map_iff, uniformity_eq_comap_nhds_one_swapped, Function.comp_def]

@[to_additive]
theorem UniformGroup.cauchy_map_iff_tendsto' {ι G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter ι)
    (f : ι → G) [NeBot 𝓕] :
    Cauchy (map f 𝓕) ↔ Tendsto (fun p ↦ f p.1 / f p.2) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_map_iff', uniformity_eq_comap_nhds_one_swapped, Function.comp_def]

@[to_additive]
theorem UniformGroup.cauchy_map_iff_tendsto_swapped {ι G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter ι)
    (f : ι → G) [NeBot 𝓕] :
    Cauchy (map f 𝓕) ↔ Tendsto (fun p ↦ f p.2 / f p.1) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_map_iff', uniformity_eq_comap_nhds_one, Function.comp_def]

@[to_additive]
theorem UniformGroup.cauchy_map_iff_tendsto_swapped' {ι G : Type*}
    [Group G] [UniformSpace G] [UniformGroup G] (𝓕 : Filter ι)
    (f : ι → G) [NeBot 𝓕] :
    Cauchy (map f 𝓕) ↔ Tendsto (fun p ↦ f p.2 / f p.1) (𝓕 ×ˢ 𝓕) (𝓝 1) := by
  simp [cauchy_map_iff', uniformity_eq_comap_nhds_one, Function.comp_def]

open NormedAddCommGroup

-- in Mathlib.Analysis.Normed.Group.Basic
lemma NormedAddCommGroup.disjoint_nhds {E : Type*} [SeminormedAddGroup E] (x : E) (f : Filter E) :
    Disjoint f (𝓝 x) ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y - x‖ := by
  simp [NormedAddCommGroup.nhds_basis_norm_lt x|>.disjoint_iff_right, compl_setOf, eventually_iff]

-- in Mathlib.Analysis.Normed.Group.Basic
lemma NormedAddCommGroup.disjoint_nhds_zero {E : Type*} [SeminormedAddGroup E] (f : Filter E) :
    Disjoint f (𝓝 0) ↔ ∃ δ > 0, ∀ᶠ x in f, δ ≤ ‖x‖ := by
  simpa using NormedAddCommGroup.disjoint_nhds (0 : E) f

theorem disjoint_cobounded_iff_isBoundedUnder_le_norm {E : Type*}
    [SeminormedAddCommGroup E] {𝓕 : Filter E} :
    Disjoint 𝓕 (Bornology.cobounded E) ↔ 𝓕.IsBoundedUnder (· ≤ ·) (‖·‖) := by
  simp [← comap_norm_atTop, disjoint_comap_iff_map, disjoint_atTop_iff_isBounded_le,
        IsBoundedUnder]

open Uniformity Bornology

variable {F : Type*} [NormedField F]

open scoped Pointwise in
instance NormedField.instCompletableTopField : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp <| .symm <| disjoint_iff.mpr hn
    have f_bounded : f.IsBoundedUnder (· ≤ ·) (‖·⁻¹‖) :=
      ⟨δ⁻¹, hδ.mono fun x hx ↦ le_inv_of_le_inv₀ δ_pos (by simpa using hx)⟩
    have f_nonzero : ∀ᶠ x in f, x ≠ 0 := hδ.mono fun x hx ↦ by simpa using δ_pos.trans_le hx
    have : ∀ᶠ p in f ×ˢ f, p.1⁻¹ * (p.2 - p.1) * p.2⁻¹ = p.1⁻¹ - p.2⁻¹ := by
      filter_upwards [f_nonzero.prod_mk f_nonzero] with ⟨x, y⟩ ⟨hx, hy⟩
      simp [mul_sub, sub_mul, hx, hy]
    rw [UniformAddGroup.cauchy_iff_tendsto_swapped] at hc
    rw [UniformAddGroup.cauchy_map_iff_tendsto, ← tendsto_congr' this]
    exact ⟨hc.1, .zero_mul_isBoundedUnder_le
      (isBoundedUnder_le_mul_tendsto_zero (tendsto_fst.isBoundedUnder_comp f_bounded) hc.2)
      (tendsto_snd.isBoundedUnder_comp f_bounded)⟩

open scoped Pointwise in
instance NormedField.instCompletableTopField' : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    rw [← disjoint_iff] at hn

    have := hc.1 -- register that `f` is nontrivial
    have f_nonzero : ∀ᶠ x in f, x ≠ 0 := by
      simpa [← principal_singleton] using hn.mono (pure_le_nhds 0) le_rfl
    have f_bounded : Disjoint f⁻¹ (cobounded F) :=
      tendsto_map.disjoint (by simpa [inv_inv f] using hn.symm) tendsto_inv₀_cobounded
    replace f_bounded : f.IsBoundedUnder (· ≤ ·) (‖·⁻¹‖) := by
      rwa [disjoint_cobounded_iff_isBoundedUnder_le_norm] at f_bounded
    have : ∀ᶠ p in f ×ˢ f, p.1⁻¹ * (p.2 - p.1) * p.2⁻¹ = p.1⁻¹ - p.2⁻¹ := by
      filter_upwards [f_nonzero.prod_mk f_nonzero] with ⟨x, y⟩ ⟨hx, hy⟩
      simp [mul_sub, sub_mul, hx, hy]
    rw [UniformAddGroup.cauchy_iff_tendsto_swapped'] at hc
    rw [UniformAddGroup.cauchy_map_iff_tendsto', ← tendsto_congr' this]
    refine .zero_mul_isBoundedUnder_le
      (isBoundedUnder_le_mul_tendsto_zero (tendsto_fst.isBoundedUnder_comp f_bounded) hc)
      (tendsto_snd.isBoundedUnder_comp f_bounded)

-- in Mathlib.Order.Filter.Bases
lemma Filter.HasBasis.inf_eq_bot_iff {α : Type*} {f g : Filter α} {ι : Type*} {p : ι → Prop}
    {s : ι → Set α}
  (hf : f.HasBasis p s) : f ⊓ g = ⊥ ↔ ∃ i, ∃ V ∈ g, p i ∧ s i ∩ V = ∅ := by
  convert (hf.inf g.basis_sets).eq_bot_iff
  aesop

open Topology Set

-- in Mathlib.Analysis.Normed.Group.Basic
lemma NormedAddCommGroup.nhds_inf_eq_bot {E : Type*} [SeminormedAddGroup E] (x : E) (f : Filter E) :
    𝓝 x ⊓ f = ⊥ ↔ ∃ δ > 0, ∃ V ∈ f, ∀ y ∈ V, δ ≤ ‖y - x‖ := by
  rw [NormedAddCommGroup.nhds_basis_norm_lt x|>.inf_eq_bot_iff]
  constructor
  · rintro ⟨δ, V, hV, δ_pos, h⟩
    refine ⟨δ, δ_pos, V, hV, fun y hy ↦ ?_⟩
    by_contra! hy'
    exact eq_empty_iff_forall_not_mem.1 h y (mem_inter hy' hy)
  · rintro ⟨δ, δ_pos, V, V_in, hV⟩
    refine ⟨δ, V, V_in, δ_pos,
      eq_empty_iff_forall_not_mem.2 fun y hy ↦ lt_irrefl _ <| hy.1.trans_le <| hV y hy.2⟩

-- in Mathlib.Analysis.Normed.Group.Basic
lemma NormedAddCommGroup.nhds_zero_inf_eq_bot {E : Type*} [SeminormedAddGroup E] (f : Filter E) :
    𝓝 0 ⊓ f = ⊥ ↔ ∃ δ > 0, ∃ V ∈ f, ∀ x ∈ V, δ ≤ ‖x‖ := by
  simpa using NormedAddCommGroup.nhds_inf_eq_bot (0 : E) f

open NormedAddCommGroup Filter

variable {F : Type*} [NormedField F]

instance NormedField.instCompletableTopField' : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    rcases nhds_zero_inf_eq_bot _ |>.1 hn with ⟨δ, δ_pos, V, V_in, hδV⟩
    rw [uniformity_basis_dist.cauchy_iff] at *
    rcases hc with ⟨hne, hsmall⟩
    refine ⟨hne.map _, fun ε ε_pos ↦ ?_⟩
    rcases hsmall (δ*ε*δ) (by positivity) with ⟨U, U_in, hU⟩
    use (·⁻¹) ⁻¹' (U ∩ V), mem_map.2 (by simp [U_in, V_in]), fun x hx y hy ↦ ?_
    have hx' : ‖x‖ ≤ δ⁻¹ := le_inv_of_le_inv₀ δ_pos (by simpa using hδV x⁻¹ hx.2)
    have hy' : ‖y‖ ≤ δ⁻¹ := le_inv_of_le_inv₀ δ_pos (by simpa using hδV y⁻¹ hy.2)
    have xne : x ≠ 0 := by simpa using δ_pos.trans_le (hδV x⁻¹ hx.2)
    have yne : y ≠ 0 := by simpa using δ_pos.trans_le (hδV y⁻¹ hy.2)
    calc
      ‖x - y‖ = ‖x*(y⁻¹ - x⁻¹)*y‖ := by field_simp ; ring
      _       = ‖x‖ * ‖y⁻¹ - x⁻¹‖ * ‖y‖ := by simp
      _       = ‖x‖ * ‖x⁻¹ - y⁻¹‖ * ‖y‖ := by rw [norm_sub_rev]
      _       ≤ δ⁻¹ * ‖x⁻¹ - y⁻¹‖ * δ⁻¹ := by gcongr
      _       < δ⁻¹ * (δ*ε*δ) * δ⁻¹ := by gcongr ; exact hU _ hx.1 _ hy.1
      _       = ε := by field_simp
