/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Star

/-!
# Topological sums and functorial constructions

Lemmas on the interaction of `tprod`, `tsum`, `HasProd`, `HasSum` etc with products, Sigma and Pi
types, `MulOpposite`, etc.

-/

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ δ : Type*}


/-! ## Product, Sigma and Pi types -/

section ProdDomain

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
theorem hasProd_pi_single [DecidableEq β] (b : β) (a : α) : HasProd (Pi.mulSingle b a) a := by
  convert hasProd_ite_eq b a
  simp [Pi.mulSingle_apply]
#align has_sum_pi_single hasSum_pi_single

@[to_additive (attr := simp)]
theorem tprod_pi_single [DecidableEq β] (b : β) (a : α) : ∏' b', Pi.mulSingle b a b' = a := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']
#align tsum_pi_single tsum_pi_single

@[to_additive tsum_setProd_singleton_left]
lemma tprod_setProd_singleton_left (b : β) (t : Set γ) (f : β × γ → α) :
    (∏' x : {b} ×ˢ t, f x) = ∏' c : t, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.singleton_prod, tprod_image _ ((Prod.mk.inj_left b).injOn _)]

@[to_additive tsum_setProd_singleton_right]
lemma tprod_setProd_singleton_right (s : Set β) (c : γ) (f : β × γ → α) :
    (∏' x : s ×ˢ {c}, f x) = ∏' b : s, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.prod_singleton, tprod_image _ ((Prod.mk.inj_right c).injOn _)]

@[to_additive Summable.prod_symm]
theorem Multipliable.prod_symm {f : β × γ → α} (hf : Multipliable f) :
    Multipliable fun p : γ × β ↦ f p.swap :=
  (Equiv.prodComm γ β).multipliable_iff.2 hf
#align summable.prod_symm Summable.prod_symm

end ProdDomain

section ProdCodomain

variable [CommMonoid α] [TopologicalSpace α] [CommMonoid γ] [TopologicalSpace γ]

@[to_additive HasSum.prod_mk]
theorem HasProd.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ}
    (hf : HasProd f a) (hg : HasProd g b) : HasProd (fun x ↦ (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ := by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prod_mk_nhds hf hg]
#align has_sum.prod_mk HasSum.prod_mk

end ProdCodomain

section ContinuousMul

variable [CommMonoid α] [TopologicalSpace α] [ContinuousMul α]

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
  simp only [Set.mem_preimage, ge_iff_le, Finset.le_iff_subset] at hu
  have : Tendsto (fun t : Finset (Σb, γ b) ↦ ∏ p ∈ t.filter fun p ↦ p.1 ∈ bs, f p) atTop
      (𝓝 <| ∏ b ∈ bs, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finset_prod _ fun b _ ↦ ?_
    change
      Tendsto (fun t ↦ (fun t ↦ ∏ s ∈ t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  refine hsc.mem_of_tendsto this (eventually_atTop.2 ⟨u, fun t ht ↦ hu _ fun x hx ↦ ?_⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩
#align has_sum.sigma HasSum.sigma

/-- If a function `f` on `β × γ` has product `a` and for each `b` the restriction of `f` to
`{b} × γ` has product `g b`, then the function `g` has product `a`. -/
@[to_additive HasSum.prod_fiberwise "If a series `f` on `β × γ` has sum `a` and for each `b` the
restriction of `f` to `{b} × γ` has sum `g b`, then the series `g` has sum `a`."]
theorem HasProd.prod_fiberwise {f : β × γ → α} {g : β → α} {a : α} (ha : HasProd f a)
    (hf : ∀ b, HasProd (fun c ↦ f (b, c)) (g b)) : HasProd g a :=
  HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf
#align has_sum.prod_fiberwise HasSum.prod_fiberwise

@[to_additive]
theorem Multipliable.sigma' {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Multipliable f)
    (hf : ∀ b, Multipliable fun c ↦ f ⟨b, c⟩) : Multipliable fun b ↦ ∏' c, f ⟨b, c⟩ :=
  (ha.hasProd.sigma fun b ↦ (hf b).hasProd).multipliable
#align summable.sigma' Summable.sigma'

end RegularSpace

section T3Space

variable [T3Space α]

@[to_additive]
theorem HasProd.sigma_of_hasProd {γ : β → Type*} {f : (Σb : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasProd g a) (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) (hf' : Multipliable f) :
    HasProd f a := by simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd
#align has_sum.sigma_of_has_sum HasSum.sigma_of_hasSum

@[to_additive]
theorem tprod_sigma' {γ : β → Type*} {f : (Σb : β, γ b) → α}
    (h₁ : ∀ b, Multipliable fun c ↦ f ⟨b, c⟩) (h₂ : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  (h₂.hasProd.sigma fun b ↦ (h₁ b).hasProd).tprod_eq.symm
#align tsum_sigma' tsum_sigma'

@[to_additive tsum_prod']
theorem tprod_prod' {f : β × γ → α} (h : Multipliable f)
    (h₁ : ∀ b, Multipliable fun c ↦ f (b, c)) :
    ∏' p, f p = ∏' (b) (c), f (b, c) :=
  (h.hasProd.prod_fiberwise fun b ↦ (h₁ b).hasProd).tprod_eq.symm
#align tsum_prod' tsum_prod'

@[to_additive]
theorem tprod_comm' {f : β → γ → α} (h : Multipliable (Function.uncurry f))
    (h₁ : ∀ b, Multipliable (f b)) (h₂ : ∀ c, Multipliable fun b ↦ f b c) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c := by
  erw [← tprod_prod' h h₁, ← tprod_prod' h.prod_symm h₂,
      ← (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl
#align tsum_comm' tsum_comm'

end T3Space

end ContinuousMul

section CompleteSpace

variable [CommGroup α] [UniformSpace α] [UniformGroup α] [CompleteSpace α]

@[to_additive]
theorem Multipliable.sigma_factor {γ : β → Type*} {f : (Σb : β, γ b) → α}
    (ha : Multipliable f) (b : β) :
    Multipliable fun c ↦ f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective
#align summable.sigma_factor Summable.sigma_factor

@[to_additive]
theorem Multipliable.sigma {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Multipliable f) :
    Multipliable fun b ↦ ∏' c, f ⟨b, c⟩ :=
  ha.sigma' fun b ↦ ha.sigma_factor b
#align summable.sigma Summable.sigma

@[to_additive Summable.prod_factor]
theorem Multipliable.prod_factor {f : β × γ → α} (h : Multipliable f) (b : β) :
    Multipliable fun c ↦ f (b, c) :=
  h.comp_injective fun _ _ h ↦ (Prod.ext_iff.1 h).2
#align summable.prod_factor Summable.prod_factor

@[to_additive]
lemma HasProd.tprod_fiberwise [T2Space α] {f : β → α} {a : α} (hf : HasProd f a) (g : β → γ) :
    HasProd (fun c : γ ↦ ∏' b : g ⁻¹' {c}, f b) a :=
  (((Equiv.sigmaFiberEquiv g).hasProd_iff).mpr hf).sigma <|
    fun _ ↦ ((hf.multipliable.subtype _).hasProd_iff).mpr rfl

section CompleteT0Space

variable [T0Space α]

@[to_additive]
theorem tprod_sigma {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  tprod_sigma' (fun b ↦ ha.sigma_factor b) ha
#align tsum_sigma tsum_sigma

@[to_additive tsum_prod]
theorem tprod_prod {f : β × γ → α} (h : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  tprod_prod' h h.prod_factor
#align tsum_prod tsum_prod

@[to_additive]
theorem tprod_comm {f : β → γ → α} (h : Multipliable (Function.uncurry f)) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c :=
  tprod_comm' h h.prod_factor h.prod_symm.prod_factor
#align tsum_comm tsum_comm

end CompleteT0Space

end CompleteSpace

section Pi

variable {ι : Type*} {π : α → Type*} [∀ x, CommMonoid (π x)] [∀ x, TopologicalSpace (π x)]

@[to_additive]
theorem Pi.hasProd {f : ι → ∀ x, π x} {g : ∀ x, π x} :
    HasProd f g ↔ ∀ x, HasProd (fun i ↦ f i x) (g x) := by
  simp only [HasProd, tendsto_pi_nhds, prod_apply]
#align pi.has_sum Pi.hasSum

@[to_additive]
theorem Pi.multipliable {f : ι → ∀ x, π x} : Multipliable f ↔ ∀ x, Multipliable fun i ↦ f i x := by
  simp only [Multipliable, Pi.hasProd, Classical.skolem]
#align pi.summable Pi.summable

@[to_additive]
theorem tprod_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Multipliable f) :
    (∏' i, f i) x = ∏' i, f i x :=
  (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm
#align tsum_apply tsum_apply

end Pi


/-! ## Multiplicative opposite -/

section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α} {a : α}

theorem HasSum.op (hf : HasSum f a) : HasSum (fun a ↦ op (f a)) (op a) :=
  (hf.map (@opAddEquiv α _) continuous_op : _)
#align has_sum.op HasSum.op

theorem Summable.op (hf : Summable f) : Summable (op ∘ f) :=
  hf.hasSum.op.summable
#align summable.op Summable.op

theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a) :
    HasSum (fun a ↦ unop (f a)) (unop a) :=
  (hf.map (@opAddEquiv α _).symm continuous_unop : _)
#align has_sum.unop HasSum.unop

theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f) : Summable (unop ∘ f) :=
  hf.hasSum.unop.summable
#align summable.unop Summable.unop

@[simp]
theorem hasSum_op : HasSum (fun a ↦ op (f a)) (op a) ↔ HasSum f a :=
  ⟨HasSum.unop, HasSum.op⟩
#align has_sum_op hasSum_op

@[simp]
theorem hasSum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a ↦ unop (f a)) (unop a) ↔ HasSum f a :=
  ⟨HasSum.op, HasSum.unop⟩
#align has_sum_unop hasSum_unop

@[simp]
theorem summable_op : (Summable fun a ↦ op (f a)) ↔ Summable f :=
  ⟨Summable.unop, Summable.op⟩
#align summable_op summable_op

-- Porting note: This theorem causes a loop easily in Lean 4, so the priority should be `low`.
@[simp low]
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable fun a ↦ unop (f a)) ↔ Summable f :=
  ⟨Summable.op, Summable.unop⟩
#align summable_unop summable_unop

theorem tsum_op [T2Space α] :
    ∑' x, op (f x) = op (∑' x, f x) := by
  by_cases h : Summable f
  · exact h.hasSum.op.tsum_eq
  · have ho := summable_op.not.mpr h
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, op_zero]
#align tsum_op tsum_op

theorem tsum_unop [T2Space α] {f : β → αᵐᵒᵖ} :
    ∑' x, unop (f x) = unop (∑' x, f x) :=
  op_injective tsum_op.symm
#align tsum_unop tsum_unop

end MulOpposite

/-! ## Interaction with the star -/

section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

theorem HasSum.star (h : HasSum f a) : HasSum (fun b ↦ star (f b)) (star a) := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star
#align has_sum.star HasSum.star

theorem Summable.star (hf : Summable f) : Summable fun b ↦ star (f b) :=
  hf.hasSum.star.summable
#align summable.star Summable.star

theorem Summable.ofStar (hf : Summable fun b ↦ Star.star (f b)) : Summable f := by
  simpa only [star_star] using hf.star
#align summable.of_star Summable.ofStar

@[simp]
theorem summable_star_iff : (Summable fun b ↦ star (f b)) ↔ Summable f :=
  ⟨Summable.ofStar, Summable.star⟩
#align summable_star_iff summable_star_iff

@[simp]
theorem summable_star_iff' : Summable (star f) ↔ Summable f :=
  summable_star_iff
#align summable_star_iff' summable_star_iff'

theorem tsum_star [T2Space α] : star (∑' b, f b) = ∑' b, star (f b) := by
  by_cases hf : Summable f
  · exact hf.hasSum.star.tsum_eq.symm
  · rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.ofStar hf),
      star_zero]
#align tsum_star tsum_star

end ContinuousStar
