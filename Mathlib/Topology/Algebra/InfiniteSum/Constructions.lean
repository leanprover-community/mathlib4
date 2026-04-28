/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.Star

/-!
# Topological sums and functorial constructions

Lemmas on the interaction of `tprod`, `tsum`, `HasProd`, `HasSum` etc. with products, Sigma and Pi
types, `MulOpposite`, etc.

-/

public section

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ : Type*} {L : SummationFilter β}


/-! ## Product, Sigma and Pi types -/

section ProdDomain

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
theorem hasProd_pi_single [DecidableEq β] (b : β) (a : α) : HasProd (Pi.mulSingle b a) a := by
  convert hasProd_ite_eq (L := .unconditional β) b a
  simp [Pi.mulSingle_apply]

@[to_additive (attr := simp)]
theorem tprod_pi_single [DecidableEq β] (b : β) (a : α) : ∏' b', Pi.mulSingle b a b' = a := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive tsum_setProd_singleton_left]
lemma tprod_setProd_singleton_left (b : β) (t : Set γ) (f : β × γ → α) :
    (∏' x : {b} ×ˢ t, f x) = ∏' c : t, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.singleton_prod, tprod_image _ (Prod.mk_right_injective b).injOn]

@[to_additive tsum_setProd_singleton_right]
lemma tprod_setProd_singleton_right (s : Set β) (c : γ) (f : β × γ → α) :
    (∏' x : s ×ˢ {c}, f x) = ∏' b : s, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.prod_singleton, tprod_image _ (Prod.mk_left_injective c).injOn]

@[to_additive Summable.prod_symm]
theorem Multipliable.prod_symm {f : β × γ → α} (hf : Multipliable f) :
    Multipliable fun p : γ × β ↦ f p.swap :=
  (Equiv.prodComm γ β).multipliable_iff.2 hf

end ProdDomain

section ProdCodomain

variable [CommMonoid α] [TopologicalSpace α] [CommMonoid γ] [TopologicalSpace γ]

@[to_additive HasSum.prodMk]
theorem HasProd.prodMk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasProd f a L)
    (hg : HasProd g b L) : HasProd (fun x ↦ (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ L := by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prodMk_nhds hf hg]

end ProdCodomain

section ContinuousMul

variable [CommMonoid α] [TopologicalSpace α] [ContinuousMul α]

section Sum

@[to_additive]
lemma HasProd.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    {f : α ⊕ β → M} {a b : M}
    (h₁ : HasProd (f ∘ Sum.inl) a) (h₂ : HasProd (f ∘ Sum.inr) b) : HasProd f (a * b) := by
  have : Tendsto ((∏ b ∈ ·, f b) ∘ sumEquiv.symm) (atTop.map sumEquiv) (nhds (a * b)) := by
    rw [Finset.sumEquiv.map_atTop, ← prod_atTop_atTop_eq]
    convert (tendsto_mul.comp (nhds_prod_eq (x := a) (y := b) ▸ Tendsto.prodMap h₁ h₂))
    ext s
    simp
  simpa [Tendsto, ← Filter.map_map] using this

@[to_additive /-- For the statement that `tsum` commutes with `Finset.sum`,
  see `Summable.tsum_finsetSum`. -/]
protected lemma Multipliable.tprod_sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {f : α ⊕ β → M} (h₁ : Multipliable (f ∘ .inl))
    (h₂ : Multipliable (f ∘ .inr)) : ∏' i, f i = (∏' i, f (.inl i)) * (∏' i, f (.inr i)) :=
  (h₁.hasProd.sum h₂.hasProd).tprod_eq

@[to_additive]
lemma Multipliable.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    (f : α ⊕ β → M) (h₁ : Multipliable (f ∘ Sum.inl)) (h₂ : Multipliable (f ∘ Sum.inr)) :
    Multipliable f :=
  ⟨_, .sum h₁.hasProd h₂.hasProd⟩

end Sum

section RegularSpace

variable [RegularSpace α]

@[to_additive]
theorem HasProd.sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasProd f a) (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) : HasProd g a := by
  classical
  refine (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr ?_
  rintro s ⟨hs, hsc⟩
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage, Finset.le_iff_subset] at hu
  have : Tendsto (fun t : Finset (Σ b, γ b) ↦ ∏ p ∈ t with p.1 ∈ bs, f p) atTop
      (𝓝 <| ∏ b ∈ bs, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finsetProd _ fun b _ ↦ ?_
    change
      Tendsto (fun t ↦ (fun t ↦ ∏ s ∈ t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  refine hsc.mem_of_tendsto this (eventually_atTop.2 ⟨u, fun t ht ↦ hu _ fun x hx ↦ ?_⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩

/-- If a function `f` on `β × γ` has product `a` and for each `b` the restriction of `f` to
`{b} × γ` has product `g b`, then the function `g` has product `a`. -/
@[to_additive HasSum.prod_fiberwise /-- If a series `f` on `β × γ` has sum `a` and for each `b` the
restriction of `f` to `{b} × γ` has sum `g b`, then the series `g` has sum `a`. -/]
theorem HasProd.prod_fiberwise {f : β × γ → α} {g : β → α} {a : α} (ha : HasProd f a)
    (hf : ∀ b, HasProd (fun c ↦ f (b, c)) (g b)) : HasProd g a :=
  HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf

@[to_additive]
theorem Multipliable.sigma' {γ : β → Type*} {f : (Σ b : β, γ b) → α} (ha : Multipliable f)
    (hf : ∀ b, Multipliable fun c ↦ f ⟨b, c⟩) : Multipliable fun b ↦ ∏' c, f ⟨b, c⟩ :=
  (ha.hasProd.sigma fun b ↦ (hf b).hasProd).multipliable

end RegularSpace

section T3Space

variable [T3Space α]

@[to_additive]
theorem HasProd.sigma_of_hasProd {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasProd g a) (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) (hf' : Multipliable f) :
    HasProd f a := by simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd

@[to_additive]
protected theorem Multipliable.tprod_sigma' {γ : β → Type*} {f : (Σ b : β, γ b) → α}
    (h₁ : ∀ b, Multipliable fun c ↦ f ⟨b, c⟩) (h₂ : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  (h₂.hasProd.sigma fun b ↦ (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod']
protected theorem Multipliable.tprod_prod' {f : β × γ → α} (h : Multipliable f)
    (h₁ : ∀ b, Multipliable fun c ↦ f (b, c)) :
    ∏' p, f p = ∏' (b) (c), f (b, c) :=
  (h.hasProd.prod_fiberwise fun b ↦ (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod_uncurry]
protected theorem Multipliable.tprod_prod_uncurry {f : β → γ → α}
    (h : Multipliable (Function.uncurry f)) (h₁ : ∀ b, Multipliable fun c ↦ f b c) :
    ∏' p : β × γ, uncurry f p = ∏' (b) (c), f b c :=
  (h.hasProd.prod_fiberwise fun b ↦ (h₁ b).hasProd).tprod_eq.symm

@[to_additive]
protected theorem Multipliable.tprod_comm' {f : β → γ → α} (h : Multipliable (Function.uncurry f))
    (h₁ : ∀ b, Multipliable (f b)) (h₂ : ∀ c, Multipliable fun b ↦ f b c) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c := by
  rw [← h.tprod_prod_uncurry h₁, ← h.prod_symm.tprod_prod_uncurry h₂,
    ← (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl

end T3Space

end ContinuousMul

section CompleteSpace

variable [CommGroup α] [UniformSpace α] [IsUniformGroup α]

@[to_additive]
theorem HasProd.of_sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α} {a : α}
    (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) (hg : HasProd g a)
    (h : CauchySeq (fun (s : Finset (Σ b : β, γ b)) ↦ ∏ i ∈ s, f i)) :
    HasProd f a := by
  classical
  apply le_nhds_of_cauchy_adhp h
  simp only [← mapClusterPt_def, mapClusterPt_iff_frequently, frequently_atTop, ge_iff_le,
    le_eq_subset]
  intro u hu s
  rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
  obtain ⟨t0, st0, ht0⟩ : ∃ t0, ∏ i ∈ t0, g i ∈ v ∧ s.image Sigma.fst ⊆ t0 := by
    have A : ∀ᶠ t0 in (atTop : Filter (Finset β)), ∏ i ∈ t0, g i ∈ v := hg (v_open.mem_nhds hv)
    exact (A.and (Ici_mem_atTop _)).exists
  have L : Tendsto (fun t : Finset (Σ b, γ b) ↦ ∏ p ∈ t with p.1 ∈ t0, f p) atTop
      (𝓝 <| ∏ b ∈ t0, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finsetProd _ fun b _ ↦ ?_
    change
      Tendsto (fun t ↦ (fun t ↦ ∏ s ∈ t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  have : ∃ t, ∏ p ∈ t with p.1 ∈ t0, f p ∈ v ∧ s ⊆ t :=
    ((Tendsto.eventually_mem L (v_open.mem_nhds st0)).and (Ici_mem_atTop _)).exists
  obtain ⟨t, tv, st⟩ := this
  refine ⟨{p ∈ t | p.1 ∈ t0}, fun x hx ↦ ?_, vu tv⟩
  simpa only [mem_filter, st hx, true_and] using ht0 (mem_image_of_mem Sigma.fst hx)

variable [CompleteSpace α]

@[to_additive]
theorem Multipliable.sigma_factor {γ : β → Type*} {f : (Σ b : β, γ b) → α}
    (ha : Multipliable f) (b : β) :
    Multipliable fun c ↦ f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective

@[to_additive]
theorem Multipliable.sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α} (ha : Multipliable f) :
    Multipliable fun b ↦ ∏' c, f ⟨b, c⟩ :=
  ha.sigma' fun b ↦ ha.sigma_factor b

@[to_additive Summable.prod_factor]
theorem Multipliable.prod_factor {f : β × γ → α} (h : Multipliable f) (b : β) :
    Multipliable fun c ↦ f (b, c) :=
  h.comp_injective fun _ _ h ↦ (Prod.ext_iff.1 h).2

@[to_additive Summable.prod]
lemma Multipliable.prod {f : β × γ → α} (h : Multipliable f) :
    Multipliable fun b ↦ ∏' c, f (b, c) :=
  ((Equiv.sigmaEquivProd β γ).multipliable_iff.mpr h).sigma

@[to_additive]
lemma HasProd.tprod_fiberwise [T2Space α] {f : β → α} {a : α} (hf : HasProd f a) (g : β → γ) :
    HasProd (fun c : γ ↦ ∏' b : g ⁻¹' {c}, f b) a :=
  (((Equiv.sigmaFiberEquiv g).hasProd_iff).mpr hf).sigma <|
    fun _ ↦ ((hf.multipliable.subtype _).hasProd_iff).mpr rfl

section CompleteT0Space

variable [T0Space α]

@[to_additive]
protected theorem Multipliable.tprod_sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α}
    (ha : Multipliable f) : ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  Multipliable.tprod_sigma' (fun b ↦ ha.sigma_factor b) ha

@[to_additive Summable.tsum_prod]
protected theorem Multipliable.tprod_prod {f : β × γ → α} (h : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  h.tprod_prod' h.prod_factor

@[to_additive]
protected theorem Multipliable.tprod_comm {f : β → γ → α} (h : Multipliable (Function.uncurry f)) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c :=
  h.tprod_comm' h.prod_factor h.prod_symm.prod_factor

end CompleteT0Space

end CompleteSpace

section Pi

variable {ι : Type*} {X : α → Type*} [∀ x, CommMonoid (X x)] [∀ x, TopologicalSpace (X x)]
  {L : SummationFilter ι}

@[to_additive]
theorem Pi.hasProd {f : ι → ∀ x, X x} {g : ∀ x, X x} :
    HasProd f g L ↔ ∀ x, HasProd (fun i ↦ f i x) (g x) L := by
  simp only [HasProd, tendsto_pi_nhds, prod_apply]

@[to_additive]
theorem Pi.multipliable {f : ι → ∀ x, X x} :
    Multipliable f L ↔ ∀ x, Multipliable (fun i ↦ f i x) L := by
  simp only [Multipliable, Pi.hasProd, Classical.skolem]

@[to_additive]
theorem tprod_apply [L.NeBot] [∀ x, T2Space (X x)] {f : ι → ∀ x, X x} {x : α}
    (hf : Multipliable f L) : (∏'[L] i, f i) x = ∏'[L] i, f i x :=
  (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm

end Pi


/-! ## Multiplicative opposite -/

section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α} {a : α}

theorem HasSum.op (hf : HasSum f a L) : HasSum (fun a ↦ op (f a)) (op a) L :=
  (hf.map (@opAddEquiv α _) continuous_op :)

theorem Summable.op (hf : Summable f L) : Summable (op ∘ f) L :=
  hf.hasSum.op.summable

theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) :
    HasSum (fun a ↦ unop (f a)) (unop a) L :=
  (hf.map (@opAddEquiv α _).symm continuous_unop :)

theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f L) : Summable (unop ∘ f) L :=
  hf.hasSum.unop.summable

@[simp]
theorem hasSum_op : HasSum (fun a ↦ op (f a)) (op a) L ↔ HasSum f a L :=
  ⟨HasSum.unop, HasSum.op⟩

@[simp]
theorem hasSum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a ↦ unop (f a)) (unop a) L ↔ HasSum f a L :=
  ⟨HasSum.op, HasSum.unop⟩

@[simp]
theorem summable_op : (Summable (fun a ↦ op (f a)) L) ↔ Summable f L :=
  ⟨Summable.unop, Summable.op⟩

theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable (fun a ↦ unop (f a)) L) ↔ Summable f L :=
  ⟨Summable.op, Summable.unop⟩

theorem tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x) :=
  (opHomeomorph.isClosedEmbedding.map_tsum f (g := opAddEquiv)).symm

theorem tsum_unop [T2Space α] {f : β → αᵐᵒᵖ} : ∑'[L] x, unop (f x) = unop (∑'[L] x, f x) :=
  op_injective tsum_op.symm

end MulOpposite

/-! ## Interaction with the star -/

section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

theorem HasSum.star (h : HasSum f a L) : HasSum (fun b ↦ star (f b)) (star a) L := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star

theorem Summable.star (hf : Summable f L) : Summable (fun b ↦ star (f b)) L :=
  hf.hasSum.star.summable

theorem Summable.ofStar (hf : Summable (fun b ↦ Star.star (f b)) L) : Summable f L := by
  simpa only [star_star] using hf.star

@[simp]
theorem summable_star_iff : Summable (fun b ↦ star (f b)) L ↔ Summable f L :=
  ⟨Summable.ofStar, Summable.star⟩

@[simp]
theorem summable_star_iff' : Summable (star f) L ↔ Summable f L :=
  summable_star_iff

theorem tsum_star [T2Space α] : star (∑'[L] b, f b) = ∑'[L] b, star (f b) :=
  Function.LeftInverse.map_tsum (g := starAddEquiv) f continuous_star continuous_star star_star

end ContinuousStar
