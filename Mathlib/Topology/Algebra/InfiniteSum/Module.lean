/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov, Frédéric Dupuis
-/
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Module.Equiv

/-! # Infinite sums in topological vector spaces -/

variable {α β γ δ : Type*}

open Filter Finset Function

section ConstSMul

variable [Monoid γ] [TopologicalSpace α] [AddCommMonoid α] [DistribMulAction γ α]
  [ContinuousConstSMul γ α] {f : β → α} {L : Filter (Finset β)}

theorem HasSumFilter.const_smul {a : α} (b : γ) (hf : HasSumFilter L f a) :
    HasSumFilter L (fun i ↦ b • f i) (b • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α _) <| continuous_const_smul _

theorem SummableFilter.const_smul (b : γ) (hf : SummableFilter L f) :
    SummableFilter L fun i ↦ b • f i :=
  (hf.hasSumFilter.const_smul _).summableFilter

/-- Infinite sums commute with scalar multiplication. Version for scalars living in a `Monoid`, but
  requiring a summability hypothesis. -/
protected theorem SummableFilter.tsumFilter_const_smul [T2Space α] [L.NeBot] (b : γ)
    (hf : SummableFilter L f) : ∑'[L] i, b • f i = b • ∑'[L] i, f i :=
  (hf.hasSumFilter.const_smul _).tsumFilter_eq

@[deprecated (since := "2025-04-12")] alias tsum_const_smul := SummableFilter.tsumFilter_const_smul

/-- Infinite sums commute with scalar multiplication. Version for scalars living in a `Group`, but
  not requiring any summability hypothesis. -/
lemma tsumFilter_const_smul' {γ : Type*} [Group γ] [DistribMulAction γ α] [ContinuousConstSMul γ α]
    [T2Space α] [L.NeBot] (g : γ) : ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i := by
  by_cases hf : SummableFilter L f
  · exact hf.tsumFilter_const_smul g
  rw [tsumFilter_eq_zero_of_not_summableFilter hf]
  simp only [smul_zero]
  let mul_g : α ≃+ α := DistribMulAction.toAddEquiv α g
  apply tsumFilter_eq_zero_of_not_summableFilter
  change ¬ SummableFilter L (mul_g ∘ f)
  rwa [SummableFilter.map_iff_of_equiv mul_g]
  · apply continuous_const_smul
  · apply continuous_const_smul

/-- Infinite sums commute with scalar multiplication. Version for scalars living in a
  `DivisionRing`; no summability hypothesis. This could be made to work for a
  `[GroupWithZero γ]` if there was such a thing as `DistribMulActionWithZero`. -/
lemma tsumFilter_const_smul'' {γ : Type*} [DivisionSemiring γ] [Module γ α]
    [ContinuousConstSMul γ α] [T2Space α] [L.NeBot] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact tsumFilter_const_smul' (Units.mk0 g hg)

end ConstSMul



variable {ι κ R R₂ M M₂ : Type*}

section SMulConst

variable [Semiring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousSMul R M] {f : ι → R} {L : Filter (Finset ι)}

theorem HasSumFilter.smul_const {r : R} (hf : HasSumFilter L f r) (a : M) :
    HasSumFilter L (fun z ↦ f z • a) (r • a) :=
  hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)

theorem SummableFilter.smul_const (hf : SummableFilter L f) (a : M) :
    SummableFilter L fun z ↦ f z • a :=
  (hf.hasSumFilter.smul_const _).summableFilter

protected theorem SummableFilter.tsumFilter_smul_const [T2Space M] [L.NeBot]
    (hf : SummableFilter L f) (a : M) : ∑'[L] z, f z • a = (∑'[L] z, f z) • a :=
  (hf.hasSumFilter.smul_const _).tsumFilter_eq

@[deprecated (since := "2025-04-12")] alias tsum_smul_const := SummableFilter.tsumFilter_smul_const

end SMulConst

/-!
Note we cannot derive the `mul` lemmas from these `smul` lemmas, as the `mul` versions do not
require associativity, but `Module` does.
-/
section tsum_smul_tsum

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace R] [TopologicalSpace M] [T3Space M]
variable [ContinuousAdd M] [ContinuousSMul R M]
variable {f : ι → R} {g : κ → M} {s : R} {t u : M}

theorem HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 • g x.2) u) : s • t = u :=
  have key₁ : HasSum (fun i ↦ f i • t) (s • t) := hf.smul_const t
  have this : ∀ i : ι, HasSum (fun c : κ ↦ f i • g c) (f i • t) := fun i ↦ hg.const_smul (f i)
  have key₂ : HasSum (fun i ↦ f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

theorem HasSum.smul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 • g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 • g x.2) (s • t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

/-- Scalar product of two infinites sums indexed by arbitrary types. -/
theorem tsum_smul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 • g x.2) :
    ((∑' x, f x) • ∑' y, g y) = ∑' z : ι × κ, f z.1 • g z.2 :=
  hf.hasSum.smul_eq hg.hasSum hfg.hasSum

end tsum_smul_tsum

section HasSum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] {σ : R →+* R₂} {σ' : R₂ →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] {L : Filter (Finset ι)}

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearMap.hasSumFilter {f : ι → M} (φ : M →SL[σ] M₂) {x : M}
    (hf : HasSumFilter L f x) : HasSumFilter L (fun b : ι ↦ φ (f b)) (φ x) := by
  simpa only using hf.map φ.toLinearMap.toAddMonoidHom φ.continuous

alias HasSumFilter.mapL := ContinuousLinearMap.hasSumFilter

protected theorem ContinuousLinearMap.summableFilter {f : ι → M} (φ : M →SL[σ] M₂)
    (hf : SummableFilter L f) : SummableFilter L fun b : ι ↦ φ (f b) :=
  (φ.hasSumFilter hf.hasSumFilter).summableFilter

alias Summable.mapL := ContinuousLinearMap.summableFilter

protected theorem ContinuousLinearMap.map_tsumFilter [T2Space M₂] [L.NeBot] {f : ι → M}
    (φ : M →SL[σ] M₂) (hf : SummableFilter L f) : φ (∑'[L] z, f z) = ∑'[L] z, φ (f z) :=
  (φ.hasSumFilter hf.hasSumFilter).tsumFilter_eq.symm

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.hasSumFilter {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    HasSumFilter L (fun b : ι ↦ e (f b)) y ↔ HasSumFilter L f (e.symm y) :=
  ⟨fun h ↦ by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →SL[σ'] M),
    fun h ↦ by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →SL[σ] M₂).hasSumFilter h⟩

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.hasSumFilter' {f : ι → M} (e : M ≃SL[σ] M₂) {x : M} :
    HasSumFilter L (fun b : ι ↦ e (f b)) (e x) ↔ HasSumFilter L f x := by
  rw [e.hasSumFilter, ContinuousLinearEquiv.symm_apply_apply]

protected theorem ContinuousLinearEquiv.summableFilter {f : ι → M} (e : M ≃SL[σ] M₂) :
    (SummableFilter L fun b : ι ↦ e (f b)) ↔ SummableFilter L f :=
  ⟨fun hf ↦ (e.hasSumFilter.1 hf.hasSumFilter).summableFilter, (e : M →SL[σ] M₂).summableFilter⟩

theorem ContinuousLinearEquiv.tsumFilter_eq_iff [T2Space M] [T2Space M₂] [L.NeBot] {f : ι → M}
    (e : M ≃SL[σ] M₂) {y : M₂} : (∑'[L] z, e (f z)) = y ↔ ∑'[L] z, f z = e.symm y := by
  by_cases hf : SummableFilter L f
  · exact
     ⟨fun h ↦ (e.hasSumFilter.mp ((e.summableFilter.mpr hf).hasSumFilter_iff.mpr h)).tsumFilter_eq,
      fun h ↦ (e.hasSumFilter.mpr (hf.hasSumFilter_iff.mpr h)).tsumFilter_eq⟩
  · have hf' : ¬SummableFilter L fun z ↦ e (f z) := fun h ↦ hf (e.summableFilter.mp h)
    rw [tsumFilter_eq_zero_of_not_summableFilter hf, tsumFilter_eq_zero_of_not_summableFilter hf']
    refine ⟨?_, fun H ↦ ?_⟩
    · rintro rfl
      simp
    · simpa using congr_arg (fun z ↦ e z) H

protected theorem ContinuousLinearEquiv.map_tsumFilter [T2Space M] [T2Space M₂] [L.NeBot]
    {f : ι → M} (e : M ≃SL[σ] M₂) : e (∑'[L] z, f z) = ∑'[L] z, e (f z) := by
  refine symm (e.tsumFilter_eq_iff.mpr ?_)
  rw [e.symm_apply_apply _]

end HasSum



section automorphize

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] {R : Type*}
  [DivisionRing R] [Module R M] [ContinuousConstSMul R M]

/-- Given a group `α` acting on a type `β`, and a function `f : β → M`, we "automorphize" `f` to a
  function `β ⧸ α → M` by summing over `α` orbits, `b ↦ ∑' (a : α), f(a • b)`. -/
@[to_additive /-- Given an additive group `α` acting on a type `β`, and a function `f : β → M`,
  we automorphize `f` to a function `β ⧸ α → M` by summing over `α` orbits,
  `b ↦ ∑' (a : α), f(a • b)`. -/]
noncomputable def MulAction.automorphize [Group α] [MulAction α β] (f : β → M) :
    Quotient (MulAction.orbitRel α β) → M := by
  refine @Quotient.lift _ _ (_) (fun b ↦ ∑' (a : α), f (a • b)) ?_
  intro b₁ b₂ ⟨a, (ha : a • b₂ = b₁)⟩
  simp only
  rw [← ha]
  convert (Equiv.mulRight a).tsum_eq (fun a' ↦ f (a' • b₂)) using 1
  simp only [Equiv.coe_mulRight]
  congr
  ext
  congr 1
  simp only [mul_smul]

-- we can't use `to_additive`, because it tries to translate `•` into `+ᵥ`

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
lemma MulAction.automorphize_smul_left [Group α] [MulAction α β] (f : β → M)
    (g : Quotient (MulAction.orbitRel α β) → R) :
    MulAction.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (MulAction.automorphize f : Quotient (MulAction.orbitRel α β) → M) := by
  ext x
  apply @Quotient.inductionOn' β (MulAction.orbitRel α β) _ x _
  intro b
  simp only [automorphize, Pi.smul_apply', comp_apply]
  set π : β → Quotient (MulAction.orbitRel α β) := Quotient.mk (MulAction.orbitRel α β)
  have H₁ : ∀ a : α, π (a • b) = π b := by
    intro a
    apply (@Quotient.eq _ (MulAction.orbitRel α β) (a • b) b).mpr
    use a
  change ∑' a : α, g (π (a • b)) • f (a • b) = g (π b) • ∑' a : α, f (a • b)
  simp_rw [H₁]
  exact tsumFilter_const_smul'' _

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
lemma AddAction.automorphize_smul_left [AddGroup α] [AddAction α β] (f : β → M)
    (g : Quotient (AddAction.orbitRel α β) → R) :
    AddAction.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (AddAction.automorphize f : Quotient (AddAction.orbitRel α β) → M) := by
  ext x
  apply @Quotient.inductionOn' β (AddAction.orbitRel α β) _ x _
  intro b
  simp only [automorphize, Pi.smul_apply', comp_apply]
  set π : β → Quotient (AddAction.orbitRel α β) := Quotient.mk (AddAction.orbitRel α β)
  have H₁ : ∀ a : α, π (a +ᵥ b) = π b := by
    intro a
    apply (@Quotient.eq _ (AddAction.orbitRel α β) (a +ᵥ b) b).mpr
    use a
  change ∑' a : α, g (π (a +ᵥ b)) • f (a +ᵥ b) = g (π b) • ∑' a : α, f (a +ᵥ b)
  simp_rw [H₁]
  exact tsumFilter_const_smul'' _

section

variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- Given a subgroup `Γ` of a group `G`, and a function `f : G → M`, we "automorphize" `f` to a
  function `G ⧸ Γ → M` by summing over `Γ` orbits, `g ↦ ∑' (γ : Γ), f(γ • g)`. -/
@[to_additive /-- Given a subgroup `Γ` of an additive group `G`, and a function `f : G → M`, we
  automorphize `f` to a function `G ⧸ Γ → M` by summing over `Γ` orbits,
  `g ↦ ∑' (γ : Γ), f(γ • g)`. -/]
noncomputable def QuotientGroup.automorphize (f : G → M) : G ⧸ Γ → M := MulAction.automorphize f

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
lemma QuotientGroup.automorphize_smul_left (f : G → M) (g : G ⧸ Γ → R) :
    (QuotientGroup.automorphize ((g ∘ (@Quotient.mk' _ (_)) : G → R) • f) : G ⧸ Γ → M)
      = g • (QuotientGroup.automorphize f : G ⧸ Γ → M) :=
  MulAction.automorphize_smul_left f g

end

section

variable {G : Type*} [AddGroup G] {Γ : AddSubgroup G}

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
lemma QuotientAddGroup.automorphize_smul_left (f : G → M) (g : G ⧸ Γ → R) :
    QuotientAddGroup.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (QuotientAddGroup.automorphize f : G ⧸ Γ → M) :=
  AddAction.automorphize_smul_left f g

end

end automorphize
