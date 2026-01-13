/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Irreducibility and Galois Groups of Selmer Polynomials

This file shows that the Selmer polynomial `X ^ n - X - 1` is irreducible with Galois group `S_n`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.
- `X_pow_sub_X_sub_one_gal`: The Selmer polynomial `X ^ n - X - 1` has Galois group `S_n`.
-/

public section

section Inertia

open scoped Pointwise

-- PR #30666
section ram

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

lemma NumberField.exists_not_isUramifiedAt_int (H : 1 < Module.finrank ℚ K) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P :=
  sorry

end ram

section ram

open IsGaloisGroup

open NumberField

-- PR #30666
theorem Ideal.IsMaximal.ne_bot_of_isIntegral_int {R : Type*} [CommRing R]
    [CharZero R] [Algebra.IsIntegral ℤ R] (I : Ideal R) [hI : I.IsMaximal] : I ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hI <|
    Int.not_isField ∘ isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ R)

theorem NumberField.supr_inertia_eq_top (K : Type*) [Field K] [NumberField K]
    (G : Type*) [Group G] [MulSemiringAction G K] [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have : Finite G := IsGaloisGroup.finite G ℚ K
  set H : Subgroup G := ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H
  suffices Module.finrank ℚ F ≤ 1 by
    rw [eq_top_iff, ← fixingSubgroup_fixedPoints G ℚ K H, ← le_fixedPoints_iff_le_fixingSubgroup,
      fixedPoints_top, le_bot_iff, ← IntermediateField.finrank_eq_one_iff]
    exact le_antisymm this Module.finrank_pos
  suffices h : ∀ (m : Ideal (𝓞 F)) (hm : m.IsMaximal), Algebra.IsUnramifiedAt ℤ m by
    contrapose! h
    obtain ⟨p, h1, h2, h3⟩ := NumberField.exists_not_isUramifiedAt_int (𝒪 := 𝓞 F) h
    exact ⟨p, h1, h3⟩
  intro m _
  have hm2 := Ideal.IsMaximal.ne_bot_of_isIntegral_int m
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hm2]
  obtain ⟨m, hm, ⟨rfl⟩⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) m
  rw [Ideal.under_under]
  have hm1 := Ideal.IsMaximal.ne_bot_of_isIntegral_int (m.under ℤ)
  have h : m.toAddSubgroup.inertia G ≤ H :=
    le_iSup (fun m : MaximalSpectrum (𝓞 K) ↦ m.asIdeal.toAddSubgroup.inertia G) ⟨m, hm⟩
  replace h : Nat.card (m.toAddSubgroup.inertia H) = Nat.card (m.toAddSubgroup.inertia G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h, Subgroup.card_subtype,
      AddSubgroup.subgroupOf_inertia]
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.field (m.under (𝓞 F))
  let := Ideal.Quotient.field (m.under ℤ)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) (m.under (𝓞 F)) hm2 m,
    Ideal.card_inertia_eq_ramificationIdxIn (G := G) (m.under ℤ) hm1 m,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under (𝓞 F)) m H,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under ℤ) m G] at h
  have key := Ideal.ramificationIdx_algebra_tower (Ideal.map_ne_bot_of_ne_bot hm2)
    (Ideal.map_ne_bot_of_ne_bot hm1) Ideal.map_comap_le
  rwa [h, right_eq_mul₀ (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver m hm1)] at key

def MaximalSpectrum.equiv {R S : Type*} [CommSemiring R] [CommSemiring S] (e : R ≃+* S) :
    MaximalSpectrum R ≃ MaximalSpectrum S where
  toFun m := ⟨m.asIdeal.map e, Ideal.map_isMaximal_of_equiv e⟩
  invFun m := ⟨m.asIdeal.comap e, Ideal.comap_isMaximal_of_equiv e⟩
  left_inv m := by simp [Ideal.comap_map_of_bijective e e.bijective]
  right_inv m := by simp [Ideal.map_comap_eq_self_of_equiv]

-- generalize from `𝓞 K` to `IsIntegralClosure`?
theorem genthm (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K]
    (G : Type*) [Group G] [MulSemiringAction G K]
    [MulSemiringAction G R] [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum R, m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  rw [← NumberField.supr_inertia_eq_top K G]
  refine (MaximalSpectrum.equiv (IsIntegralClosure.equiv ℤ (𝓞 K) K R).symm).iSup_congr fun m ↦ ?_
  ext
  simp [MaximalSpectrum.equiv]
  sorry

end ram

end Inertia

namespace Polynomial

section Moore

instance {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] (f : R[X])
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S] :
    MulAction G (f.rootSet S) where
  smul g x := ⟨g • x.1, by
    rw [mem_rootSet', aeval_smul, smul_eq_zero_iff_eq, ← mem_rootSet']
    exact x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

theorem rootSet.coe_smul
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    {f : R[X]}
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) (x : f.rootSet S) : (g • x : f.rootSet S) = g • (x : S) := rfl

theorem Function.Surjective.card_le_card_add_one_iff
    {α β : Type*} [Finite α] {f : α → β} (hf : Function.Surjective f) :
    Nat.card α ≤ Nat.card β + 1 ↔ ∀ a b c d,
      f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α) := by
  rcases isEmpty_or_nonempty α
  · simp
  let g := Function.surjInv hf
  rw [← Set.ncard_range_of_injective (Function.injective_surjInv hf),
    ← Set.ncard_add_ncard_compl (Set.range g), add_le_add_iff_left]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Set.ncard_le_one_iff_subset_singleton] at h
    obtain ⟨x, hx⟩ := h
    suffices ∀ a b : α, f a = f b → a ≠ b → a = x ∨ a = g (f x) by grind
    intro a b hfab hab
    by_cases ha : a ∈ Set.range g
    · obtain ⟨a, rfl⟩ := ha
      rw [Function.surjInv_eq hf] at hfab
      subst hfab
      by_cases hb : b ∈ Set.range g
      · obtain ⟨b, rfl⟩ := hb
        rw [Function.surjInv_eq hf] at hab
        contradiction
      · exact Or.inr (congrArg (fun y ↦ g (f y)) (hx hb))
    · exact Or.inl (hx ha)
  · rw [Set.ncard_le_one]
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, ← ne_eq]
    intro a ha b hb
    simpa [(ha (f b)).symm] using congrArg (a ∈ ·) (h a (g (f a)) b (g (f b))
      (Function.surjInv_eq hf (f a)).symm (Function.surjInv_eq hf (f b)).symm
      (ha (f a)).symm (hb (f b)).symm)

theorem Set.ncard_le_ncard_image_add_one_iff {α β : Type*} (s : Set α) [Finite s] (f : α → β) :
    s.ncard ≤ (f '' s).ncard + 1 ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α) := by
  simpa [Subtype.ext_iff, ← Set.image_val_inj, Set.image_insert_eq] using
    Function.Surjective.card_le_card_add_one_iff (Set.surjective_mapsTo_image_restrict f s)

theorem tada
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (f : R[X]) (hmon : f.Monic) [DecidableEq (f.rootSet S)]
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (m : MaximalSpectrum S) (hf : (f.map (algebraMap R S)).Splits)
    (h : (f.rootSet S).ncard ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1) :
    ∀ g ∈ m.asIdeal.toAddSubgroup.inertia G,
      MulAction.toPermHom G (f.rootSet S) g = 1 ∨
        (MulAction.toPermHom G (f.rootSet S) g).IsSwap := by
  intro g hg
  let π : S →ₐ[R] S ⧸ m.asIdeal := Ideal.Quotient.mkₐ R m.asIdeal
  have hπ (x : S) (hx : x ∈ f.rootSet S): π x ∈ f.rootSet (S ⧸ m.asIdeal) := by
    rw [hmon.mem_rootSet, aeval_algHom_apply, aeval_eq_zero_of_mem_rootSet hx, map_zero]
  have hπ (x : S) : π (g • x) = π x := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g • x) x).mpr (hg x)
  rw [or_iff_not_imp_left, Equiv.ext_iff, not_forall]
  rintro ⟨x, hx : g • x ≠ x⟩
  refine ⟨g • x, x, hx, ?_⟩
  ext z
  rw [Equiv.swap_apply_def]
  have h0 : f.rootSet (S ⧸ m.asIdeal) = π '' f.rootSet S := by
    classical
    have key := Monic.roots_map_of_card_eq_natDegree (hmon.map (algebraMap R S))
      (π : S →+* S ⧸ m.asIdeal) hf.natDegree_eq_card_roots.symm
    rw [map_map, π.comp_algebraMap] at key
    simp [rootSet, aroots, ← key, Multiset.toFinset_map]
  rw [h0] at h
  split_ifs with hz hz'
  · subst hz
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, SetLike.coe_eq_coe]
    have key := (Set.ncard_le_ncard_image_add_one_iff (f.rootSet S) π).mp h
      (g • g • x) (g • g • x).2 (g • x) (g • x).2 (g • x) (g • x).2 x x.2 (by simp [hπ])
      (by simp [hπ]) (by simpa [← rootSet.coe_smul]) (by simpa [← rootSet.coe_smul])
    grind [rootSet.coe_smul]
  · simp [hz']
  · simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, SetLike.coe_eq_coe]
    have key := (Set.ncard_le_ncard_image_add_one_iff (f.rootSet S) π).mp h
      (g • z) (g • z).2 z z.2 (g • x) (g • x).2 x x.2 (by simp [hπ]) (by simp [hπ])
    grind [rootSet.coe_smul, SetLike.coe_eq_coe]

theorem tada' {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] (f : R[X])
    (hf : f.Monic) (hf' : (f.map (algebraMap R S)).Splits)
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    [MulAction.IsPretransitive G (f.rootSet S)]
    (hG : ⨆ m : MaximalSpectrum S, m.asIdeal.toAddSubgroup.inertia G = ⊤)
    (h : ∀ m : MaximalSpectrum S, (f.rootSet S).ncard ≤ (f.rootSet (S ⧸ m.asIdeal)).ncard + 1) :
    Function.Surjective (MulAction.toPermHom G (f.rootSet S)) := by
  classical
  apply surjective_of_isSwap_of_isPretransitive'
    (⋃ m : MaximalSpectrum S, m.asIdeal.toAddSubgroup.inertia G)
  · intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨m, hm⟩ := hσ
    have := tada f hf G m hf' (h m) σ hm
    exact this
  · simpa only [Subgroup.closure_iUnion, Subgroup.closure_eq, Subgroup.closure_diff_one]

open Equiv Pointwise

open IntermediateField

attribute [-instance] Polynomial.Gal.galActionAux -- should be local to PolynomialGaloisGroup.lean

attribute [-instance] Gal.smul Gal.galAction -- todo: redefine in more general semiring context

attribute [local instance] Gal.splits_ℚ_ℂ

open NumberField

theorem _root_.Polynomial.Splits.of_splits_map_of_injective {R : Type*} [CommRing R] {f : R[X]}
    {S : Type*} [CommRing S] [IsDomain S] (i : R →+* S) (hi : Function.Injective i)
    (hf : Splits (f.map i)) (hi : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Splits f := by
  choose j hj using hi
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ ↦ id, map_injective i hi ?_⟩
  conv_lhs => rw [hf.eq_prod_roots, leadingCoeff_map_of_injective hi]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]

theorem _root_.Polynomial.ncard_rootSet_le {R : Type*}
    (S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] (f : R[X]) : (f.rootSet S).ncard ≤ f.natDegree := by
  classical
  grw [rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact f.card_roots_map_le_natDegree

theorem tada'' (f₀ : ℤ[X]) (hf₀ : Monic f₀) (hf₀' : Irreducible f₀)
    (h : ∀ (F : Type) [Field F], (f₀.map (algebraMap ℤ F)).Splits →
      f₀.natDegree ≤ (f₀.rootSet F).ncard + 1) :
    -- condition on at most on root collision mod p :
    Function.Bijective (Gal.galActionHom (f₀.map (algebraMap ℤ ℚ)) ℂ) := by
  classical
  let f : ℚ[X] := f₀.map (algebraMap ℤ ℚ)
  have hf : Monic f := hf₀.map (algebraMap ℤ ℚ)
  have hf' : Irreducible f := hf₀.irreducible_iff_irreducible_map_fraction_map.mp hf₀'
  let K := f.SplittingField
  -- have : Fact (f.map (algebraMap ℚ K)).Splits := ⟨SplittingField.splits f⟩
  have : NumberField K := by constructor
  have : IsGalois ℚ K := by constructor
  let R := 𝓞 K
  let G := f.Gal
  have h_transitive := Gal.galAction_isPretransitive f ℂ hf'
  let e := Polynomial.Gal.rootsEquivRoots f ℂ
  have he : Gal.galActionHom f ℂ = e.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom G (f.rootSet K)) := by
    ext; simp [Gal.galActionHom, Polynomial.Gal.smul_def, G, K, e]
  -- switch immediately from `f.rootSet ℂ` to `f.rootSet R`
  have hφ : Set.MapsTo (algebraMap R K) (f₀.rootSet R) (f.rootSet K) := by
    intro x hx
    rw [hf.mem_rootSet, aeval_map_algebraMap, aeval_algebraMap_apply,
      aeval_eq_zero_of_mem_rootSet hx, map_zero]
  let φ : f₀.rootSet R → f.rootSet K := hφ.restrict
  have hφ1 : ∀ g : G, ∀ x : f₀.rootSet R, φ (g • x) = g • φ x := by
    intro g x
    ext
    rfl
  have hφ2 : Function.Bijective (hφ.restrict) := by
    rw [Function.Bijective, hφ.restrict_inj, hφ.restrict_surjective_iff]
    refine ⟨RingOfIntegers.coe_injective.injOn, ?_⟩
    intro x hx
    have h0 : aeval x f₀ = 0 := by
      rwa [mem_rootSet, aeval_map_algebraMap, and_iff_right hf.ne_zero] at hx
    let y : integralClosure ℤ K := ⟨x, f₀, hf₀, h0⟩
    refine ⟨y, ?_, rfl⟩
    rw [mem_rootSet, and_iff_right hf₀.ne_zero]
    simpa using (aeval_algebraMap_apply K y f₀).symm.trans h0
  let e' := Equiv.ofBijective hφ.restrict hφ2
  have he' : MulAction.toPermHom G (f.rootSet K) = e'.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom G (f₀.rootSet R)) := by
    ext g x
    obtain ⟨y, rfl⟩ := e'.surjective x
    simp
    rfl
  suffices Function.Surjective (MulAction.toPermHom G (f₀.rootSet R)) by
    use Polynomial.Gal.galActionHom_injective f ℂ
    rw [he, he']
    exact (e.permCongrHom.toEquiv.comp_surjective _).mpr
      ((e'.permCongrHom.toEquiv.comp_surjective _).mpr this)
  replace h_transitive : MulAction.IsPretransitive G (f₀.rootSet R) := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨g, hg⟩ := h_transitive.exists_smul_eq (e (e' x)) (e (e' y))
    refine ⟨g, e'.injective (e.injective ?_)⟩
    rw [← hg]
    rw [MonoidHom.ext_iff] at he
    specialize he g
    rw [Equiv.ext_iff] at he
    specialize he (e (e' x))
    simp at he
    exact he.symm
  have h1 : (f₀.map (algebraMap ℤ R)).Splits := by
    have h : (f.map (algebraMap ℚ K)).Splits := SplittingField.splits f
    rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ R K, ← map_map] at h
    refine h.of_splits_map_of_injective (algebraMap R K) RingOfIntegers.coe_injective ?_
    intro x hx
    rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ ℚ K, ← map_map] at hx
    obtain ⟨y, hy⟩ := hφ2.2 ⟨x, (by
      rw [hf.mem_rootSet] -- some sort of mem_rootSet_iff_mem_roots_map lemma?
      rwa [mem_roots_iff_aeval_eq_zero, aeval_map_algebraMap] at hx
      exact (hf.map (algebraMap ℚ K)).ne_zero
    )⟩
    exact ⟨y, Subtype.ext_iff.mp hy⟩
  have : IsGaloisGroup G ℚ K := IsGaloisGroup.of_isGalois ℚ K
  refine tada' (S := R) f₀ hf₀ h1 G (NumberField.supr_inertia_eq_top K G) fun m ↦ ?_
  let := Ideal.Quotient.field m.asIdeal
  refine le_trans (f₀.ncard_rootSet_le R) (h (R ⧸ m.asIdeal) ?_)
  rw [IsScalarTower.algebraMap_eq ℤ R (R ⧸ m.asIdeal), ← Polynomial.map_map]
  exact h1.map _

end Moore

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [pow_zero, pow_one, or_true, true_or]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, right_eq_add] at h1)
  · exact one_ne_zero (by rwa [key, left_eq_add] at h1)
  · exact z_ne_zero (eq_zero_of_pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ, Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp ▸ (trinomial_monic zero_lt_one hn).isPrimitive

open Equiv Pointwise

open IntermediateField

attribute [local instance] Gal.splits_ℚ_ℂ

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  rcases le_or_gt n 1 with hn | hn
  · have : Subsingleton ((X ^ n - X - 1 : ℚ[X]).rootSet ℂ) := by
      apply Finset.card_le_one_iff_subsingleton_coe.mp
      grw [Multiset.toFinset_card_le, card_roots', natDegree_map_le, natDegree_sub_le,
        natDegree_sub_le, natDegree_X_pow, natDegree_X, natDegree_one, hn, max_self, Nat.max_zero]
    have : Unique ((X ^ n - X - 1 : ℚ[X]).Gal) := by
      refine Gal.uniqueGalOfSplits _ (Splits.of_natDegree_le_one (by compute_degree!))
    apply Unique.bijective
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have h := tada'' (X ^ n - X - 1) (hp ▸ trinomial_monic zero_lt_one hn)
    (X_pow_sub_X_sub_one_irreducible hn.ne') ?_
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · classical
    intro F _ hF
    have := hF.natDegree_eq_card_roots
    rw [Monic.natDegree_map (hp ▸ trinomial_monic zero_lt_one hn)] at this
    rw [this]
    rw [rootSet_def, aroots_def, Set.ncard_coe_finset]
    rw [Multiset.card_le_card_toFinset_add_one_iff]
    have h : ∀ x : F, 1 < (map (algebraMap ℤ F) (X ^ n - X - 1)).roots.count x →
        x = n / (1 - n) ∧ x ≠ 0 := by
      intro x hx
      rw [count_roots, one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
        (Monic.map _ (hp ▸ trinomial_monic zero_lt_one hn)).ne_zero] at hx
      have hx0 := hx 0 one_pos.le
      have hx1 := hx 1 le_rfl
      simp [derivative_X_pow, sub_eq_iff_eq_add] at hx0 hx1
      rw [pow_sub_of_lt x hn, pow_one, hx0] at hx1
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx1
      rw [← mul_assoc, mul_inv_eq_one₀ hx0] at hx1
      rw [mul_add, mul_one, eq_comm, ← sub_eq_iff_eq_add, ← one_sub_mul, mul_comm] at hx1
      refine ⟨eq_div_of_mul_eq ?_ hx1, hx0⟩
      rw [sub_ne_zero]
      rintro hn0
      rw [← hn0] at hx1
      simp at hx1
    intro x y hx hy
    have hx' := h x hx
    replace hy := h y hy
    use hx'.1.trans hy.1.symm
    refine le_antisymm ?_ hx
    rw [count_roots]
    by_contra! hx''
    replace hx'' := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hx''
    simp [derivative_X_pow, Nat.cast_sub hn.le, sub_eq_zero, hx'.2] at hx''
    grind

end Polynomial
