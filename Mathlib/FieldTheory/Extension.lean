/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Junyan Xu
-/
import Mathlib.Data.Fintype.Order
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Extension of field embeddings

`IntermediateField.exists_algHom_of_adjoin_splits'` is the main result: if E/L/F is a tower of
field extensions, K is another extension of F, and `f` is an embedding of L/F into K/F, such
that the minimal polynomials of a set of generators of E/L splits in K (via `f`), then `f`
extends to an embedding of E/F into K/F.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

open Polynomial

namespace IntermediateField

variable (F E K : Type*) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/-- Lifts `L → K` of `F → K` -/
structure Lifts where
  /-- The domain of a lift. -/
  carrier : IntermediateField F E
  /-- The lifted RingHom, expressed as an AlgHom. -/
  emb : carrier →ₐ[F] K

variable {F E K}

namespace Lifts

instance : PartialOrder (Lifts F E K) where
  le L₁ L₂ := ∃ h : L₁.carrier ≤ L₂.carrier, ∀ x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ ↦ ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃, h₂₃', h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁⟩ ⟨L₂, e₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'

noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le, fun x ↦ by
    obtain ⟨x, rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgHom.coe_coe, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

variable {L₁ L₂ : Lifts F E K}

theorem le_iff : L₁ ≤ L₂ ↔
    ∃ h : L₁.carrier ≤ L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb := by
  simp_rw [AlgHom.ext_iff]; rfl

theorem eq_iff_le_carrier_eq : L₁ = L₂ ↔ L₁ ≤ L₂ ∧ L₁.carrier = L₂.carrier :=
  ⟨fun eq ↦ ⟨eq.le, congr_arg _ eq⟩, fun ⟨le, eq⟩ ↦ le.antisymm ⟨eq.ge, fun x ↦ (le.2 ⟨x, _⟩).symm⟩⟩

theorem eq_iff : L₁ = L₂ ↔
    ∃ h : L₁.carrier = L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb := by
  rw [eq_iff_le_carrier_eq, le_iff]
  exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.le, h.2⟩, h.1⟩⟩

theorem lt_iff_le_carrier_ne : L₁ < L₂ ↔ L₁ ≤ L₂ ∧ L₁.carrier ≠ L₂.carrier := by
  rw [lt_iff_le_and_ne, and_congr_right]; intro h; simp_rw [Ne, eq_iff_le_carrier_eq, h, true_and]

theorem lt_iff : L₁ < L₂ ↔
    ∃ h : L₁.carrier < L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb := by
  rw [lt_iff_le_carrier_ne, le_iff]
  exact ⟨fun h ↦ ⟨h.1.1.lt_of_ne h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.le, h.2⟩, h.1.ne⟩⟩

theorem le_of_carrier_le_iSup {ι} {ρ : ι → Lifts F E K} {σ τ : Lifts F E K}
    (hσ : ∀ i, ρ i ≤ σ) (hτ : ∀ i, ρ i ≤ τ) (carrier_le : σ.carrier ≤ ⨆ i, (ρ i).carrier) :
    σ ≤ τ :=
  le_iff.mpr ⟨carrier_le.trans (iSup_le fun i ↦ (hτ i).1), algHom_ext_of_eq_adjoin _
      (carrier_le.antisymm (iSup_le fun i ↦ (hσ i).1)|>.trans <| iSup_eq_adjoin _ _) fun x hx ↦
    have ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    ((hτ i).2 ⟨x, hx⟩).trans ((hσ i).2 ⟨x, hx⟩).symm⟩

/-- `σ : L →ₐ[F] K` is an extendible lift ("extendible pair" in [Isaacs1980]) if for every
intermediate field `M` that is finite-dimensional over `L`, `σ` extends to some `M →ₐ[F] K`.
In our definition we only require `M` to be finitely generated over `L`, which is equivalent
if the ambient field `E` is algebraic over `F` (which is the case in our main application).
We also allow the domain of the extension to be an intermediate field that properly contains `M`,
since one can always restrict the domain to `M`. -/
def IsExtendible (σ : Lifts F E K) : Prop :=
  ∀ S : Finset E, ∃ τ ≥ σ, (S : Set E) ⊆ τ.carrier

section Chain
variable (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c)

/-- The union of a chain of lifts. -/
noncomputable def union : Lifts F E K :=
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ ↦ .inl bot_le
  have dir : Directed (· ≤ ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h ↦
    AlgHom.ext fun x ↦ (hc.total i.2 j.2).elim (fun hij ↦ (hij.snd x).symm) fun hji ↦ by
      rw [AlgHom.comp_apply, ← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x])
    _ rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

theorem le_union ⦃σ : Lifts F E K⦄ (hσ : σ ∈ c) : σ ≤ union c hc :=
  have hσ := Set.mem_insert_of_mem ⊥ hσ
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  ⟨le_iSup t ⟨σ, hσ⟩, fun x ↦ by
    dsimp only [union, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·))
      (i := ⟨σ, hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ, hσ⟩)⟩

theorem carrier_union : (union c hc).carrier = ⨆ i : c, i.1.carrier :=
  le_antisymm (iSup_le <| by rintro ⟨i, rfl | hi⟩; exacts [bot_le, le_iSup_of_le ⟨i, hi⟩ le_rfl]) <|
    iSup_le fun i ↦ le_iSup_of_le ⟨i, .inr i.2⟩ le_rfl

/-- A chain of lifts has an upper bound. -/
theorem exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c) :
    ∃ ub, ∀ a ∈ c, a ≤ ub := ⟨_, le_union c hc⟩

theorem union_isExtendible [alg : Algebra.IsAlgebraic F E]
    [Nonempty c] (hext : ∀ σ ∈ c, σ.IsExtendible) :
    (union c hc).IsExtendible := fun S ↦ by
  let Ω := adjoin F (S : Set E) →ₐ[F] K
  have ⟨ω, hω⟩ : ∃ ω : Ω, ∀ π : c, ∃ θ ≥ π.1, ⟨_, ω⟩ ≤ θ ∧ θ.carrier = π.1.1 ⊔ adjoin F S := by
    by_contra!; choose π hπ using this
    have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ ↦ (alg.isIntegral).1 _
    have ⟨π₀, hπ₀⟩ := hc.directed.finite_le π
    have ⟨θ, hθπ, hθ⟩ := hext _ π₀.2 S
    rw [← adjoin_le_iff] at hθ
    let θ₀ := θ.emb.comp (inclusion hθ)
    have := (hπ₀ θ₀).trans hθπ
    exact hπ θ₀ ⟨_, θ.emb.comp <| inclusion <| sup_le this.1 hθ⟩
      ⟨le_sup_left, this.2⟩ ⟨le_sup_right, fun _ ↦ rfl⟩ rfl
  choose θ ge hθ eq using hω
  have : IsChain (· ≤ ·) (Set.range θ) := by
    simp_rw [← restrictScalars_adjoin_eq_sup, restrictScalars_adjoin] at eq
    rintro _ ⟨π₁, rfl⟩ _ ⟨π₂, rfl⟩ -
    wlog h : π₁ ≤ π₂ generalizing π₁ π₂
    · exact (this _ _ <| (hc.total π₁.2 π₂.2).resolve_left h).symm
    refine .inl (le_iff.mpr ⟨?_, algHom_ext_of_eq_adjoin _ (eq _) ?_⟩)
    · rw [eq, eq]; exact adjoin.mono _ _ _ (Set.union_subset_union_left _ h.1)
    rintro x (hx|hx)
    · change (θ π₂).emb (inclusion (ge π₂).1 <| inclusion h.1 ⟨x, hx⟩) =
        (θ π₁).emb (inclusion (ge π₁).1 ⟨x, hx⟩)
      rw [(ge π₁).2, (ge π₂).2, h.2]
    · change (θ π₂).emb (inclusion (hθ π₂).1 ⟨x, subset_adjoin _ _ hx⟩) =
        (θ π₁).emb (inclusion (hθ π₁).1 ⟨x, subset_adjoin _ _ hx⟩)
      rw [(hθ π₁).2, (hθ π₂).2]
  refine ⟨union _ this, le_of_carrier_le_iSup (fun π ↦ le_union c hc π.2)
    (fun π ↦ (ge π).trans <| le_union _ _ ⟨_, rfl⟩) (carrier_union _ _).le, ?_⟩
  simp_rw [carrier_union, iSup_range', eq]
  exact (subset_adjoin _ _).trans (SetLike.coe_subset_coe.mpr <|
    le_sup_right.trans <| le_iSup_of_le (Classical.arbitrary _) le_rfl)

end Chain

theorem nonempty_algHom_of_exist_lifts_finset [alg : Algebra.IsAlgebraic F E]
    (h : ∀ S : Finset E, ∃ σ : Lifts F E K, (S : Set E) ⊆ σ.carrier) :
    Nonempty (E →ₐ[F] K) := by
  have : (⊥ : Lifts F E K).IsExtendible := fun S ↦ have ⟨σ, hσ⟩ := h S; ⟨σ, bot_le, hσ⟩
  have ⟨ϕ, hϕ⟩ := zorn_le₀ {ϕ : Lifts F E K | ϕ.IsExtendible}
    fun c hext hc ↦ (isEmpty_or_nonempty c).elim
      (fun _ ↦ ⟨⊥, this, fun ϕ hϕ ↦ isEmptyElim (⟨ϕ, hϕ⟩ : c)⟩)
      fun _ ↦ ⟨_, union_isExtendible c hc hext, le_union c hc⟩
  suffices ϕ.carrier = ⊤ from ⟨ϕ.emb.comp <| ((equivOfEq this).trans topEquiv).symm⟩
  by_contra!
  obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt this.lt_top
  let _ : Algebra ϕ.carrier K := ϕ.emb.toAlgebra
  let Λ := ϕ.carrier⟮α⟯ →ₐ[ϕ.carrier] K
  have := finiteDimensional_adjoin (S := {α}) fun _ _ ↦ ((alg.tower_top ϕ.carrier).isIntegral).1 _
  let L (σ : Λ) : Lifts F E K := ⟨ϕ.carrier⟮α⟯.restrictScalars F, σ.restrictScalars F⟩
  have hL (σ : Λ) : ϕ < L σ := lt_iff.mpr
    ⟨by simpa only [L, restrictScalars_adjoin_eq_sup, left_lt_sup, adjoin_simple_le_iff],
      AlgHom.coe_ringHom_injective σ.comp_algebraMap⟩
  have ⟨(ϕ_ext : ϕ.IsExtendible), ϕ_max⟩ := maximal_iff_forall_gt.mp hϕ
  simp_rw [Set.mem_setOf, IsExtendible] at ϕ_max; push_neg at ϕ_max
  choose S hS using fun σ : Λ ↦ ϕ_max (hL σ)
  classical
  have ⟨θ, hθϕ, hθ⟩ := ϕ_ext ({α} ∪ Finset.univ.biUnion S)
  simp_rw [Finset.coe_union, Set.union_subset_iff, Finset.coe_singleton, Set.singleton_subset_iff,
    Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.iUnion_subset_iff] at hθ
  have : ϕ.carrier⟮α⟯.restrictScalars F ≤ θ.carrier := by
    rw [restrictScalars_adjoin_eq_sup, sup_le_iff, adjoin_simple_le_iff]; exact ⟨hθϕ.1, hθ.1⟩
  exact hS ⟨(θ.emb.comp <| inclusion this).toRingHom, hθϕ.2⟩ θ ⟨this, fun _ ↦ rfl⟩ (hθ.2 _)

/-- Given a lift `x` and an integral element `s : E` over `x.carrier` whose conjugates over
`x.carrier` are all in `K`, we can extend the lift to a lift whose carrier contains `s`. -/
theorem exists_lift_of_splits' (x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrier s)
    (h2 : (minpoly x.carrier s).Splits x.emb.toRingHom) : ∃ y, x ≤ y ∧ s ∈ y.carrier :=
  have I2 := (minpoly.degree_pos h1).ne'
  letI : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  letI : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let φ : carrier →ₐ[x.carrier] K := ((algHomAdjoinIntegralEquiv x.carrier h1).symm
    ⟨rootOfSplits x.emb.toRingHom h2 I2, by
      rw [mem_aroots, and_iff_right (minpoly.ne_zero h1)]
      exact map_rootOfSplits x.emb.toRingHom h2 I2⟩)
  ⟨⟨carrier, (@algHomEquivSigma F x.carrier carrier K _ _ _ _ _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)).symm ⟨x.emb, φ⟩⟩,
    ⟨fun z hz ↦ algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩

/-- Given an integral element `s : E` over `F` whose `F`-conjugates are all in `K`,
any lift can be extended to one whose carrier contains `s`. -/
theorem exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.carrier :=
  exists_lift_of_splits' x h1.tower_top <| h1.minpoly_splits_tower_top' <| by
    rwa [← x.emb.comp_algebraMap] at h2

end Lifts

section

private theorem exists_algHom_adjoin_of_splits'' {L : IntermediateField F E}
    (f : L →ₐ[F] K) (hK : ∀ s ∈ S, IsIntegral L s ∧ (minpoly L s).Splits f.toRingHom) :
    ∃ φ : adjoin L S →ₐ[F] K, φ.restrictDomain L = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ ↦ Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| (le_extendScalars_iff hfφ.1 <| adjoin L S).mp <|
    adjoin_le_iff.mpr fun s h ↦ ?_), AlgHom.ext hfφ.2⟩
  letI := (inclusion hfφ.1).toAlgebra
  letI : SMul L φ.carrier := Algebra.toSMul
  have : IsScalarTower L φ.carrier E := ⟨fun x y ↦ smul_assoc x (y : E)⟩
  have := φ.exists_lift_of_splits' (hK s h).1.tower_top ((hK s h).1.minpoly_splits_tower_top' ?_)
  · obtain ⟨y, h1, h2⟩ := this
    exact (hφ h1).1 h2
  · convert (hK s h).2; ext; apply hfφ.2

variable {L : Type*} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]
  (f : L →ₐ[F] K) (hK : ∀ s ∈ S, IsIntegral L s ∧ (minpoly L s).Splits f.toRingHom)

include hK in
theorem exists_algHom_adjoin_of_splits' :
    ∃ φ : adjoin L S →ₐ[F] K, φ.restrictDomain L = f := by
  let L' := (IsScalarTower.toAlgHom F L E).fieldRange
  let f' : L' →ₐ[F] K := f.comp (AlgEquiv.ofInjectiveField _).symm.toAlgHom
  have := exists_algHom_adjoin_of_splits'' f' (S := S) fun s hs ↦ ?_
  · obtain ⟨φ, hφ⟩ := this; refine ⟨φ.comp <|
      inclusion (?_ : (adjoin L S).restrictScalars F ≤ (adjoin L' S).restrictScalars F), ?_⟩
    · simp_rw [← SetLike.coe_subset_coe, coe_restrictScalars, adjoin_subset_adjoin_iff]
      exact ⟨subset_adjoin_of_subset_left S (F := L'.toSubfield) le_rfl, subset_adjoin _ _⟩
    · ext x
      let y := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) x
      refine Eq.trans congr($hφ y) ?_
      simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply, f']
      exact congr_arg f (AlgEquiv.symm_apply_apply _ _)
  letI : Algebra L L' := (AlgEquiv.ofInjectiveField _).toRingHom.toAlgebra
  have : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨(hK s hs).1.tower_top, (hK s hs).1.minpoly_splits_tower_top' ?_⟩
  convert (hK s hs).2
  ext
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply, f']
  exact congr_arg f (AlgEquiv.symm_apply_apply _ _)

include hK in
theorem exists_algHom_of_adjoin_splits' (hS : adjoin L S = ⊤) :
    ∃ φ : E →ₐ[F] K, φ.restrictDomain L = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits' f hK
  ⟨φ.comp (((equivOfEq hS).trans topEquiv).symm.toAlgHom.restrictScalars F), hφ⟩

theorem exists_algHom_of_splits' (hK : ∀ s : E, IsIntegral L s ∧ (minpoly L s).Splits f.toRingHom) :
    ∃ φ : E →ₐ[F] K, φ.restrictDomain L = f :=
  exists_algHom_of_adjoin_splits' f (fun x _ ↦ hK x) (adjoin_univ L E)

end

variable (hK : ∀ s ∈ S, IsIntegral F s ∧ (minpoly F s).Splits (algebraMap F K))
  (hK' : ∀ s : E, IsIntegral F s ∧ (minpoly F s).Splits (algebraMap F K))
  {L : IntermediateField F E} (f : L →ₐ[F] K) (hL : L ≤ adjoin F S) {x : E} {y : K}

section
include hK

theorem exists_algHom_adjoin_of_splits : ∃ φ : adjoin F S →ₐ[F] K, φ.comp (inclusion hL) = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ ↦ Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| adjoin_le_iff.mpr fun s hs ↦ ?_), ?_⟩
  · rcases φ.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    exact (hφ h1).1 h2
  · ext; apply hfφ.2

theorem nonempty_algHom_adjoin_of_splits : Nonempty (adjoin F S →ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_adjoin_of_splits hK (⊥ : Lifts F E K).emb bot_le; ⟨φ⟩

variable (hS : adjoin F S = ⊤)

include hS in
theorem exists_algHom_of_adjoin_splits : ∃ φ : E →ₐ[F] K, φ.comp L.val = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK f (hS.symm ▸ le_top)
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

include hS in
theorem nonempty_algHom_of_adjoin_splits : Nonempty (E →ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_of_adjoin_splits hK (⊥ : Lifts F E K).emb hS; ⟨φ⟩

variable (hx : x ∈ adjoin F S) (hy : aeval y (minpoly F x) = 0)
include hy

theorem exists_algHom_adjoin_of_splits_of_aeval : ∃ φ : adjoin F S →ₐ[F] K, φ ⟨x, hx⟩ = y := by
  have := isAlgebraic_adjoin (fun s hs ↦ (hK s hs).1)
  have ix : IsAlgebraic F _ := Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : adjoin F S)
  rw [isAlgebraic_iff_isIntegral, isIntegral_iff] at ix
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK ((algHomAdjoinIntegralEquiv F ix).symm
    ⟨y, mem_aroots.mpr ⟨minpoly.ne_zero ix, hy⟩⟩) (adjoin_simple_le_iff.mpr hx)
  exact ⟨φ, (DFunLike.congr_fun hφ <| AdjoinSimple.gen F x).trans <|
    algHomAdjoinIntegralEquiv_symm_apply_gen F ix _⟩

include hS in
theorem exists_algHom_of_adjoin_splits_of_aeval : ∃ φ : E →ₐ[F] K, φ x = y :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK (hS ▸ mem_top) hy
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩


include hK'

end

section
include hK'

theorem exists_algHom_of_splits : ∃ φ : E →ₐ[F] K, φ.comp L.val = f :=
  exists_algHom_of_adjoin_splits (fun x _ ↦ hK' x) f (adjoin_univ F E)

theorem nonempty_algHom_of_splits : Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_adjoin_splits (fun x _ ↦ hK' x) (adjoin_univ F E)

theorem exists_algHom_of_splits_of_aeval (hy : aeval y (minpoly F x) = 0) :
    ∃ φ : E →ₐ[F] K, φ x = y :=
  exists_algHom_of_adjoin_splits_of_aeval (fun x _ ↦ hK' x) (adjoin_univ F E) hy

end

end IntermediateField

section Algebra.IsAlgebraic

/-- Let `K/F` be an algebraic extension of fields and `L` a field in which all the minimal
polynomial over `F` of elements of `K` splits. Then, for `x ∈ K`, the images of `x` by the
`F`-algebra morphisms from `K` to `L` are exactly the roots in `L` of the minimal polynomial
of `x` over `F`. -/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits {F K : Type*} (L : Type*)
    [Field F] [Field K] [Field L] [Algebra F L] [Algebra F K]
    (hA : ∀ x : K, (minpoly F x).Splits (algebraMap F L))
    [Algebra.IsAlgebraic F K] (x : K) :
    (Set.range fun (ψ : K →ₐ[F] L) => ψ x) = (minpoly F x).rootSet L := by
  ext a
  rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
  refine ⟨fun ⟨ψ, hψ⟩ ↦ ?_, fun ha ↦ IntermediateField.exists_algHom_of_splits_of_aeval
    (fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, hA x⟩) ha⟩
  rw [← hψ, Polynomial.aeval_algHom_apply ψ x, minpoly.aeval, map_zero]

end Algebra.IsAlgebraic
