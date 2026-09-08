/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Neighborhoods in topological groups

Translation formulas and neighborhood bases at one, continuity criteria for homomorphisms,
extensionality and construction results for topological groups, and the multiplicative
neighborhood homomorphism.
-/

@[expose] public section

open Set Filter Function Topology Pointwise

variable {G : Type*}

section IsTopologicalGroup

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive exists_nhds_half_neg]
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v / w ∈ s := by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this

@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp

@[to_additive]
theorem nhds_translation_inv_mul (x : G) : comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp

@[to_additive (attr := simp)]
theorem map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x := by simp

@[to_additive (attr := simp)]
theorem map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x) :=
  (Homeomorph.mulRight x).map_nhds_eq y

@[to_additive]
theorem map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x := by simp

@[to_additive]
theorem Filter.HasBasis.nhds_of_one {ι : Sort*} {p : ι → Prop} {s : ι → Set G}
    (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) :
    HasBasis (𝓝 x) p fun i => { y | y / x ∈ s i } := by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _

@[to_additive]
theorem Filter.HasBasis.nhds_of_one' {ι : Sort*} {p : ι → Prop} {s : ι → Set G}
    (hb : (𝓝 1).HasBasis p s) (x : G) :
    (𝓝 x).HasBasis p fun i ↦ x • (s i) := by
  rw [← map_mul_left_nhds_one x]
  exact hb.map (x * ·)

@[to_additive]
theorem Filter.HasBasis.nhds_one_inv {ι : Sort*} {p : ι → Prop} {U : ι → Set G}
    (hU : (𝓝 1).HasBasis p U) : (𝓝 1).HasBasis p fun i ↦ (U i)⁻¹ := by
  simpa [← nhds_inv] using hU.inv

@[to_additive]
theorem mem_closure_iff_nhds_one {x : G} {s : Set G} :
    x ∈ closure s ↔ ∀ U ∈ (𝓝 1 : Filter G), ∃ y ∈ s, y / x ∈ U := by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_ofPred, id]

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`)
from a topological group to a topological monoid is continuous
provided that it is continuous at one.

This version assumes that `f x → 1` as `x → 1`,
saving a rewrite of `f 1 = 1` compared to `continuous_of_continuousAt_one` in some cases.
See also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero.

  This version assumes that `f x → 0` as `x → 0`,
  saving a rewrite of `f 0 = 0` compared to `continuous_of_continuousAt_zero` in some cases.
  See also `uniformContinuous_of_continuousAt_zero`. -/]
theorem continuous_of_tendsto_nhds_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : Tendsto f (𝓝 1) (𝓝 1)) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x ↦ by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, Function.comp_def,
      map_mul, mul_one] using hf.const_mul (f x)

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero. See also
  `uniformContinuous_of_continuousAt_zero`. -/]
theorem continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : ContinuousAt f 1) :
    Continuous f :=
  continuous_of_tendsto_nhds_one f <| by simpa using hf.tendsto

@[to_additive continuous_of_continuousAt_zero₂]
theorem continuous_of_continuousAt_one₂ {H M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H →* M)
    (hf : ContinuousAt (fun x : G × H ↦ f x.1 x.2) (1, 1))
    (hl : ∀ x, ContinuousAt (f x) 1) (hr : ∀ y, ContinuousAt (f · y) 1) :
    Continuous (fun x : G × H ↦ f x.1 x.2) := continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, Function.comp_def, map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]
lemma IsTopologicalGroup.isInducing_iff_nhds_one
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {F : Type*}
    [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    Topology.IsInducing f ↔ 𝓝 (1 : G) = (𝓝 (1 : H)).comap f := by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x ↦ ?_⟩
  rw [← nhds_translation_mul_inv, ← nhds_translation_mul_inv (f x), Filter.comap_comap, hf,
    Filter.comap_comap]
  congr 1
  ext; simp

@[to_additive]
lemma IsTopologicalGroup.isOpenMap_iff_nhds_one
    {H : Type*} [Monoid H] [TopologicalSpace H] [ContinuousConstSMul H H]
    {F : Type*} [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    IsOpenMap f ↔ 𝓝 1 ≤ .map f (𝓝 1) := by
  refine ⟨fun H ↦ map_one f ▸ H.nhds_le 1, fun h ↦ IsOpenMap.of_nhds_le fun x ↦ ?_⟩
  have : Filter.map (f x * ·) (𝓝 1) = 𝓝 (f x) := by
    simpa [-Homeomorph.map_nhds_eq, Units.smul_def] using!
      (Homeomorph.smul ((toUnits x).map (MonoidHomClass.toMonoidHom f))).map_nhds_eq (1 : H)
  rw [← map_mul_left_nhds_one x, Filter.map_map, Function.comp_def, ← this]
  refine (Filter.map_mono h).trans ?_
  simp [Function.comp_def]

-- TODO: unify with `QuotientGroup.isOpenQuotientMap_mk`
/-- Let `A` and `B` be topological groups, and let `φ : A → B` be a continuous surjective group
homomorphism. Assume furthermore that `φ` is a quotient map (i.e., `V ⊆ B`
is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an open map. -/
@[to_additive /-- Let `A` and `B` be topological additive groups, and let `φ : A → B` be a
continuous surjective additive group homomorphism. Assume furthermore that `φ` is a quotient map
(i.e., `V ⊆ B` is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an
open map. -/]
lemma MonoidHom.isOpenQuotientMap_of_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F}
    (hφ : IsQuotientMap φ) : IsOpenQuotientMap φ where
    surjective := hφ.surjective
    continuous := hφ.continuous
    isOpenMap := by
      -- We need to check that if `U ⊆ A` is open then `φ⁻¹ (φ U)` is open.
      intro U hU
      rw [← hφ.isOpen_preimage]
      -- It suffices to show that `φ⁻¹ (φ U) = ⋃ (U * k⁻¹)` as `k` runs through the kernel of `φ`,
      -- as `U * k⁻¹` is open because `x ↦ x * k` is continuous.
      -- Remark: here is where we use that we have groups not monoids (you cannot avoid
      -- using both `k` and `k⁻¹` at this point).
      suffices ⇑φ ⁻¹' ⇑φ '' U = ⋃ k ∈ ker (φ : A →* B), (fun x ↦ x * k) ⁻¹' U by
        exact this ▸ isOpen_biUnion (fun k _ ↦ Continuous.isOpen_preimage (by fun_prop) _ hU)
      ext x
      -- But this is an elementary calculation.
      constructor
      · rintro ⟨y, hyU, hyx⟩
        apply Set.mem_iUnion_of_mem (x⁻¹ * y)
        simp_all
      · rintro ⟨_, ⟨k, rfl⟩, _, ⟨(hk : φ k = 1), rfl⟩, hx⟩
        use x * k, hx
        rw [map_mul, hk, mul_one]

@[to_additive]
lemma MonoidHom.isOpenQuotientMap_iff_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F} :
    IsOpenQuotientMap φ ↔ IsQuotientMap φ :=
  ⟨fun hf => hf.isQuotientMap, MonoidHom.isOpenQuotientMap_of_isQuotientMap⟩

@[to_additive]
theorem IsTopologicalGroup.ext {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  TopologicalSpace.ext_nhds fun x ↦ by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]

@[to_additive]
theorem IsTopologicalGroup.ext_iff {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩

@[to_additive]
theorem ContinuousInv.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G := by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, Function.comp_def, mul_assoc,
    mul_inv_rev, inv_mul_cancel_left] using this

@[to_additive]
theorem IsTopologicalGroup.of_nhds_one' {G : Type*} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : IsTopologicalGroup G :=
  { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl, ←
              map_map, ← hleft, hright, map_map]
            simp) }

@[to_additive]
theorem IsTopologicalGroup.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)) : IsTopologicalGroup G := by
  refine IsTopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : ∀ x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [Function.comp_def] using hleft _

@[to_additive]
theorem IsTopologicalGroup.of_comm_of_nhds_one {G : Type*} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1)) : IsTopologicalGroup G :=
  IsTopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using! tendsto_id)

variable (G) in
/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → Set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`QuotientGroup.completeSpace_right`. -/
@[to_additive
  /-- Any first countable topological additive group has an antitone neighborhood basis
  `u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`.
  The existence of such a neighborhood basis is a key tool
  for `QuotientAddGroup.completeSpace_right`. -/]
theorem IsTopologicalGroup.exists_antitone_basis_nhds_one [FirstCountableTopology G] :
    ∃ u : ℕ → Set G, (𝓝 1).HasAntitoneBasis u ∧ ∀ n, u (n + 1) * u (n + 1) ⊆ u n := by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, Prod.exists,
    forall_true_left] at this
  have event_mul : ∀ n : ℕ, ∀ᶠ m in atTop, u m * u m ⊆ u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩

end IsTopologicalGroup

section NhdsMul

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x, ← map_mul_right_nhds_one y, ← map₂_mul, map₂_map_left,
        map₂_map_right]

/-- On a topological group, `𝓝 : G → Filter G` can be promoted to a `MulHom`. -/
@[to_additive (attr := simps)
  /-- On an additive topological group, `𝓝 : G → Filter G` can be promoted to an `AddHom`. -/]
def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _

end

end NhdsMul
