/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Logic.Encodable.Lattice
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.Algebra.Star

#align_import topology.algebra.infinite_sum.basic from "leanprover-community/mathlib"@"3b1890e71632be9e3b2086ab512c3259a7e9a3ef"

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `HasSum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

set_option autoImplicit true


noncomputable section

open Classical Filter Finset Function

open BigOperators Classical Topology

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section HasSum

variable [AddCommMonoid α] [TopologicalSpace α]

/-- Infinite sum on a topological monoid

The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def HasSum (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β => ∑ b in s, f b) atTop (𝓝 a)
#align has_sum HasSum

/-- `Summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def Summable (f : β → α) : Prop :=
  ∃ a, HasSum f a
#align summable Summable

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise. -/
irreducible_def tsum {β} (f : β → α) :=
  if h : Summable f then
  /- Note that the sum might not be uniquely defined if the topology is not separated.
  When the support of `f` is finite, we make the most reasonable choice to use the finite sum over
  the support. Otherwise, we choose arbitrarily an `a` satisfying `HasSum f a`. -/
    if (support f).Finite then finsum f
    else Classical.choose h
  else 0
#align tsum tsum

-- see Note [operator precedence of big operators]
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

theorem HasSum.summable (h : HasSum f a) : Summable f :=
  ⟨a, h⟩
#align has_sum.summable HasSum.summable

/-- Constant zero function has sum `0` -/
theorem hasSum_zero : HasSum (fun _ => 0 : β → α) 0 := by simp [HasSum, tendsto_const_nhds]
                                                          -- 🎉 no goals
#align has_sum_zero hasSum_zero

theorem hasSum_empty [IsEmpty β] : HasSum f 0 := by
  convert @hasSum_zero α β _ _
  -- 🎉 no goals
#align has_sum_empty hasSum_empty

theorem summable_zero : Summable (fun _ => 0 : β → α) :=
  hasSum_zero.summable
#align summable_zero summable_zero

theorem summable_empty [IsEmpty β] : Summable f :=
  hasSum_empty.summable
#align summable_empty summable_empty

theorem tsum_eq_zero_of_not_summable (h : ¬Summable f) : ∑' b, f b = 0 := by simp [tsum_def, h]
                                                                             -- 🎉 no goals
#align tsum_eq_zero_of_not_summable tsum_eq_zero_of_not_summable

theorem summable_congr (hfg : ∀ b, f b = g b) : Summable f ↔ Summable g :=
  iff_of_eq (congr_arg Summable <| funext hfg)
#align summable_congr summable_congr

theorem Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g :=
  (summable_congr hfg).mp hf
#align summable.congr Summable.congr

theorem HasSum.hasSum_of_sum_eq {g : γ → α}
    (h_eq :
      ∀ u : Finset γ,
        ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
    (hf : HasSum g a) : HasSum f a :=
  le_trans (map_atTop_finset_sum_le_of_sum_eq h_eq) hf
#align has_sum.has_sum_of_sum_eq HasSum.hasSum_of_sum_eq

theorem hasSum_iff_hasSum {g : γ → α}
    (h₁ :
      ∀ u : Finset γ,
        ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
    (h₂ :
      ∀ v : Finset β,
        ∃ u : Finset γ, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ ∑ b in v', f b = ∑ x in u', g x) :
    HasSum f a ↔ HasSum g a :=
  ⟨HasSum.hasSum_of_sum_eq h₂, HasSum.hasSum_of_sum_eq h₁⟩
#align has_sum_iff_has_sum hasSum_iff_hasSum

theorem Function.Injective.hasSum_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 0) : HasSum (f ∘ g) a ↔ HasSum f a := by
  simp only [HasSum, Tendsto, comp_apply, hg.map_atTop_finset_sum_eq hf]
  -- 🎉 no goals
#align function.injective.has_sum_iff Function.Injective.hasSum_iff

theorem Function.Injective.summable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 0) : Summable (f ∘ g) ↔ Summable f :=
  exists_congr fun _ => hg.hasSum_iff hf
#align function.injective.summable_iff Function.Injective.summable_iff

@[simp] theorem hasSum_extend_zero {g : β → γ} (hg : Injective g) :
    HasSum (extend g f 0) a ↔ HasSum f a := by
  rw [← hg.hasSum_iff, extend_comp hg]
  -- ⊢ ∀ (x : γ), ¬x ∈ Set.range g → extend g f 0 x = 0
  exact extend_apply' _ _
  -- 🎉 no goals

@[simp] theorem summable_extend_zero {g : β → γ} (hg : Injective g) :
    Summable (extend g f 0) ↔ Summable f :=
  exists_congr fun _ => hasSum_extend_zero hg

theorem hasSum_subtype_iff_of_support_subset {s : Set β} (hf : support f ⊆ s) :
    HasSum (f ∘ (↑) : s → α) a ↔ HasSum f a :=
  Subtype.coe_injective.hasSum_iff <| by simpa using support_subset_iff'.1 hf
                                         -- 🎉 no goals
#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subset

theorem hasSum_subtype_iff_indicator {s : Set β} :
    HasSum (f ∘ (↑) : s → α) a ↔ HasSum (s.indicator f) a := by
  rw [← Set.indicator_range_comp, Subtype.range_coe,
    hasSum_subtype_iff_of_support_subset Set.support_indicator_subset]
#align has_sum_subtype_iff_indicator hasSum_subtype_iff_indicator

theorem summable_subtype_iff_indicator {s : Set β} :
    Summable (f ∘ (↑) : s → α) ↔ Summable (s.indicator f) :=
  exists_congr fun _ => hasSum_subtype_iff_indicator
#align summable_subtype_iff_indicator summable_subtype_iff_indicator

@[simp]
theorem hasSum_subtype_support : HasSum (f ∘ (↑) : support f → α) a ↔ HasSum f a :=
  hasSum_subtype_iff_of_support_subset <| Set.Subset.refl _
#align has_sum_subtype_support hasSum_subtype_support

theorem hasSum_fintype [Fintype β] (f : β → α) : HasSum f (∑ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
#align has_sum_fintype hasSum_fintype

protected theorem Finset.hasSum (s : Finset β) (f : β → α) :
    HasSum (f ∘ (↑) : (↑s : Set β) → α) (∑ b in s, f b) := by
  rw [← sum_attach]
  -- ⊢ HasSum (f ∘ Subtype.val) (∑ x in attach s, f ↑x)
  exact hasSum_fintype _
  -- 🎉 no goals
#align finset.has_sum Finset.hasSum

protected theorem Finset.summable (s : Finset β) (f : β → α) :
    Summable (f ∘ (↑) : (↑s : Set β) → α) :=
  (s.hasSum f).summable
#align finset.summable Finset.summable

protected theorem Set.Finite.summable {s : Set β} (hs : s.Finite) (f : β → α) :
    Summable (f ∘ (↑) : s → α) := by
  have := hs.toFinset.summable f
  -- ⊢ Summable (f ∘ Subtype.val)
  rwa [hs.coe_toFinset] at this
  -- 🎉 no goals
#align set.finite.summable Set.Finite.summable

/-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum` `∑ b in s, f b`. -/
theorem hasSum_sum_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : HasSum f (∑ b in s, f b) :=
  (hasSum_subtype_iff_of_support_subset <| support_subset_iff'.2 hf).1 <| s.hasSum f
#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zero

theorem summable_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : Summable f :=
  (hasSum_sum_of_ne_finset_zero hf).summable
#align summable_of_ne_finset_zero summable_of_ne_finset_zero

theorem summable_of_finite_support (h : (support f).Finite) : Summable f := by
  apply summable_of_ne_finset_zero (s := h.toFinset); simp
  -- ⊢ ∀ (b : β), ¬b ∈ Set.Finite.toFinset h → f b = 0
                                                      -- 🎉 no goals

theorem Summable.hasSum (ha : Summable f) : HasSum f (∑' b, f b) := by
  simp only [tsum_def, ha, dite_true]
  -- ⊢ HasSum f (if Set.Finite (support fun b => f b) then ∑ᶠ (b : β), f b else Cla …
  by_cases H : (support f).Finite
  -- ⊢ HasSum f (if Set.Finite (support fun b => f b) then ∑ᶠ (b : β), f b else Cla …
  · simp [H, hasSum_sum_of_ne_finset_zero, finsum_eq_sum]
    -- 🎉 no goals
  · simpa [H] using Classical.choose_spec ha
    -- 🎉 no goals
#align summable.has_sum Summable.hasSum

theorem hasSum_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) : HasSum f (f b) :=
  suffices HasSum f (∑ b' in {b}, f b') by simpa using this
                                           -- 🎉 no goals
                                     -- 🎉 no goals
  hasSum_sum_of_ne_finset_zero <| by simpa [hf]
#align has_sum_single hasSum_single

theorem hasSum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    HasSum (fun b' => if b' = b then a else 0) a := by
  convert @hasSum_single _ _ _ _ (fun b' => if b' = b then a else 0) b (fun b' hb' => if_neg hb')
  -- ⊢ a = if b = b then a else 0
  exact (if_pos rfl).symm
  -- 🎉 no goals
#align has_sum_ite_eq hasSum_ite_eq

theorem hasSum_pi_single [DecidableEq β] (b : β) (a : α) : HasSum (Pi.single b a) a := by
  convert hasSum_ite_eq b a
  -- ⊢ Pi.single b a x✝ = if x✝ = b then a else 0
  simp [Pi.single_apply]
  -- 🎉 no goals
#align has_sum_pi_single hasSum_pi_single

theorem Equiv.hasSum_iff (e : γ ≃ β) : HasSum (f ∘ e) a ↔ HasSum f a :=
  e.injective.hasSum_iff <| by simp
                               -- 🎉 no goals
#align equiv.has_sum_iff Equiv.hasSum_iff

theorem Function.Injective.hasSum_range_iff {g : γ → β} (hg : Injective g) :
    HasSum (fun x : Set.range g => f x) a ↔ HasSum (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasSum_iff.symm
#align function.injective.has_sum_range_iff Function.Injective.hasSum_range_iff

theorem Equiv.summable_iff (e : γ ≃ β) : Summable (f ∘ e) ↔ Summable f :=
  exists_congr fun _ => e.hasSum_iff
#align equiv.summable_iff Equiv.summable_iff

theorem Summable.prod_symm {f : β × γ → α} (hf : Summable f) : Summable fun p : γ × β => f p.swap :=
  (Equiv.prodComm γ β).summable_iff.2 hf
#align summable.prod_symm Summable.prod_symm

theorem Equiv.hasSum_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : HasSum f a ↔ HasSum g a := by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  -- ⊢ HasSum f a ↔ HasSum g a
  rw [← hasSum_subtype_support, ← this, e.hasSum_iff, hasSum_subtype_support]
  -- 🎉 no goals
#align equiv.has_sum_iff_of_support Equiv.hasSum_iff_of_support

theorem hasSum_iff_hasSum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasSum f a ↔ HasSum g a :=
  Iff.symm <|
    Equiv.hasSum_iff_of_support
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun _ _ h => Subtype.ext <| hi <| Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun _ hx => Subtype.ext hx⟩)
      hfg
#align has_sum_iff_has_sum_of_ne_zero_bij hasSum_iff_hasSum_of_ne_zero_bij

theorem Equiv.summable_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : Summable f ↔ Summable g :=
  exists_congr fun _ => e.hasSum_iff_of_support he
#align equiv.summable_iff_of_support Equiv.summable_iff_of_support

protected theorem HasSum.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : HasSum f a) {G}
    [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) : HasSum (g ∘ f) (g a) :=
  have : (g ∘ fun s : Finset β => ∑ b in s, f b) = fun s : Finset β => ∑ b in s, g (f b) :=
    funext <| map_sum g _
  show Tendsto (fun s : Finset β => ∑ b in s, g (f b)) atTop (𝓝 (g a)) from
    this ▸ (hg.tendsto a).comp hf
#align has_sum.map HasSum.map

protected theorem Summable.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : Summable f) {G}
    [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) : Summable (g ∘ f) :=
  (hf.hasSum.map g hg).summable
#align summable.map Summable.map

protected theorem Summable.map_iff_of_leftInverse [AddCommMonoid γ] [TopologicalSpace γ] {G G'}
    [AddMonoidHomClass G α γ] [AddMonoidHomClass G' γ α] (g : G) (g' : G') (hg : Continuous g)
    (hg' : Continuous g') (hinv : Function.LeftInverse g' g) : Summable (g ∘ f) ↔ Summable f :=
  ⟨fun h => by
    have := h.map _ hg'
    -- ⊢ Summable f
    rwa [← Function.comp.assoc, hinv.id] at this, fun h => h.map _ hg⟩
    -- 🎉 no goals
#align summable.map_iff_of_left_inverse Summable.map_iff_of_leftInverse

/-- A special case of `Summable.map_iff_of_leftInverse` for convenience -/
protected theorem Summable.map_iff_of_equiv [AddCommMonoid γ] [TopologicalSpace γ] {G}
    [AddEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (AddEquivClass.toEquivLike.inv g : γ → α)) : Summable (g ∘ f) ↔ Summable f :=
  Summable.map_iff_of_leftInverse g (g : α ≃+ γ).symm hg hg' (AddEquivClass.toEquivLike.left_inv g)
#align summable.map_iff_of_equiv Summable.map_iff_of_equiv

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
theorem HasSum.tendsto_sum_nat {f : ℕ → α} (h : HasSum f a) :
    Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) :=
  h.comp tendsto_finset_range
#align has_sum.tendsto_sum_nat HasSum.tendsto_sum_nat

theorem HasSum.unique {a₁ a₂ : α} [T2Space α] : HasSum f a₁ → HasSum f a₂ → a₁ = a₂ :=
  tendsto_nhds_unique
#align has_sum.unique HasSum.unique

theorem Summable.hasSum_iff_tendsto_nat [T2Space α] {f : ℕ → α} {a : α} (hf : Summable f) :
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) := by
  refine' ⟨fun h => h.tendsto_sum_nat, fun h => _⟩
  -- ⊢ HasSum f a
  rw [tendsto_nhds_unique h hf.hasSum.tendsto_sum_nat]
  -- ⊢ HasSum f (∑' (b : ℕ), f b)
  exact hf.hasSum
  -- 🎉 no goals
#align summable.has_sum_iff_tendsto_nat Summable.hasSum_iff_tendsto_nat

theorem Function.Surjective.summable_iff_of_hasSum_iff {α' : Type*} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : Summable f ↔ Summable g :=
  hes.exists.trans <| exists_congr <| @he
#align function.surjective.summable_iff_of_has_sum_iff Function.Surjective.summable_iff_of_hasSum_iff

variable [ContinuousAdd α]

theorem HasSum.add (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun b => f b + g b) (a + b) := by
  dsimp only [HasSum] at hf hg ⊢
  -- ⊢ Tendsto (fun s => ∑ b in s, (f b + g b)) atTop (𝓝 (a + b))
  simp_rw [sum_add_distrib]
  -- ⊢ Tendsto (fun s => ∑ x in s, f x + ∑ x in s, g x) atTop (𝓝 (a + b))
  exact hf.add hg
  -- 🎉 no goals
#align has_sum.add HasSum.add

theorem Summable.add (hf : Summable f) (hg : Summable g) : Summable fun b => f b + g b :=
  (hf.hasSum.add hg.hasSum).summable
#align summable.add Summable.add

theorem hasSum_sum {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasSum (f i) (a i)) → HasSum (fun b => ∑ i in s, f i b) (∑ i in s, a i) :=
  Finset.induction_on s (by simp only [hasSum_zero, sum_empty, forall_true_iff]) <| by
                            -- 🎉 no goals
    -- Porting note: with some help, `simp` used to be able to close the goal
    simp (config := { contextual := true }) only [mem_insert, forall_eq_or_imp, not_false_iff,
      sum_insert, and_imp]
    exact fun x s _ IH hx h ↦ hx.add (IH h)
    -- 🎉 no goals
#align has_sum_sum hasSum_sum

theorem summable_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun b => ∑ i in s, f i b :=
  (hasSum_sum fun i hi => (hf i hi).hasSum).summable
#align summable_sum summable_sum

theorem HasSum.add_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasSum (f ∘ (↑) : s → α) a)
    (hb : HasSum (f ∘ (↑) : t → α) b) : HasSum (f ∘ (↑) : (s ∪ t : Set β) → α) (a + b) := by
  rw [hasSum_subtype_iff_indicator] at *
  -- ⊢ HasSum (Set.indicator (s ∪ t) f) (a + b)
  rw [Set.indicator_union_of_disjoint hs]
  -- ⊢ HasSum (fun a => Set.indicator s f a + Set.indicator t f a) (a + b)
  exact ha.add hb
  -- 🎉 no goals
#align has_sum.add_disjoint HasSum.add_disjoint

theorem hasSum_sum_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasSum (f ∘ (↑) : t i → α) (a i)) :
    HasSum (f ∘ (↑) : (⋃ i ∈ s, t i) → α) (∑ i in s, a i) := by
  simp_rw [hasSum_subtype_iff_indicator] at *
  -- ⊢ HasSum (Set.indicator (⋃ (i : ι) (_ : i ∈ s), t i) f) (∑ i in s, a i)
  rw [Set.indicator_finset_biUnion _ _ hs]
  -- ⊢ HasSum (fun a => ∑ i in s, Set.indicator (t i) f a) (∑ i in s, a i)
  exact hasSum_sum hf
  -- 🎉 no goals
#align has_sum_sum_disjoint hasSum_sum_disjoint

theorem HasSum.add_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasSum (f ∘ (↑) : s → α) a)
    (hb : HasSum (f ∘ (↑) : t → α) b) : HasSum f (a + b) := by
  simpa [← hs.compl_eq] using
    (hasSum_subtype_iff_indicator.1 ha).add (hasSum_subtype_iff_indicator.1 hb)
#align has_sum.add_is_compl HasSum.add_isCompl

theorem HasSum.add_compl {s : Set β} (ha : HasSum (f ∘ (↑) : s → α) a)
    (hb : HasSum (f ∘ (↑) : (sᶜ : Set β) → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl hb
#align has_sum.add_compl HasSum.add_compl

theorem Summable.add_compl {s : Set β} (hs : Summable (f ∘ (↑) : s → α))
    (hsc : Summable (f ∘ (↑) : (sᶜ : Set β) → α)) : Summable f :=
  (hs.hasSum.add_compl hsc.hasSum).summable
#align summable.add_compl Summable.add_compl

theorem HasSum.compl_add {s : Set β} (ha : HasSum (f ∘ (↑) : (sᶜ : Set β) → α) a)
    (hb : HasSum (f ∘ (↑) : s → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl.symm hb
#align has_sum.compl_add HasSum.compl_add

theorem HasSum.even_add_odd {f : ℕ → α} (he : HasSum (fun k => f (2 * k)) a)
    (ho : HasSum (fun k => f (2 * k + 1)) b) : HasSum f (a + b) := by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  -- ⊢ HasSum f (a + b)
  replace he := this.hasSum_range_iff.2 he
  -- ⊢ HasSum f (a + b)
  replace ho := ((add_left_injective 1).comp this).hasSum_range_iff.2 ho
  -- ⊢ HasSum f (a + b)
  refine' he.add_isCompl _ ho
  -- ⊢ IsCompl (Set.range ((fun x x_1 => x * x_1) 2)) (Set.range ((fun x => x + 1)  …
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
  -- 🎉 no goals
#align has_sum.even_add_odd HasSum.even_add_odd

theorem Summable.compl_add {s : Set β} (hs : Summable (f ∘ (↑) : (sᶜ : Set β) → α))
    (hsc : Summable (f ∘ (↑) : s → α)) : Summable f :=
  (hs.hasSum.compl_add hsc.hasSum).summable
#align summable.compl_add Summable.compl_add

theorem Summable.even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) : Summable f :=
  (he.hasSum.even_add_odd ho.hasSum).summable
#align summable.even_add_odd Summable.even_add_odd

theorem HasSum.sigma [RegularSpace α] {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasSum f a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) : HasSum g a := by
  refine' (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr _
  -- ⊢ ∀ (ib : Set α), ib ∈ 𝓝 a ∧ IsClosed ib → ∃ ia, True ∧ ∀ (x : Finset β), x ∈  …
  rintro s ⟨hs, hsc⟩
  -- ⊢ ∃ ia, True ∧ ∀ (x : Finset β), x ∈ Set.Ici ia → ∑ b in x, g b ∈ id s
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  -- ⊢ ∃ ia, True ∧ ∀ (x : Finset β), x ∈ Set.Ici ia → ∑ b in x, g b ∈ id s
  use u.image Sigma.fst, trivial
  -- ⊢ ∀ (x : Finset β), x ∈ Set.Ici (image Sigma.fst u) → ∑ b in x, g b ∈ id s
  intro bs hbs
  -- ⊢ ∑ b in bs, g b ∈ id s
  simp only [Set.mem_preimage, ge_iff_le, Finset.le_iff_subset] at hu
  -- ⊢ ∑ b in bs, g b ∈ id s
  have : Tendsto (fun t : Finset (Σb, γ b) => ∑ p in t.filter fun p => p.1 ∈ bs, f p) atTop
      (𝓝 <| ∑ b in bs, g b) := by
    simp only [← sigma_preimage_mk, sum_sigma]
    refine' tendsto_finset_sum _ fun b _ => _
    change
      Tendsto (fun t => (fun t => ∑ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  refine' hsc.mem_of_tendsto this (eventually_atTop.2 ⟨u, fun t ht => hu _ fun x hx => _⟩)
  -- ⊢ x ∈ filter (fun p => p.fst ∈ bs) t
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩
  -- 🎉 no goals
#align has_sum.sigma HasSum.sigma

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
theorem HasSum.prod_fiberwise [RegularSpace α] {f : β × γ → α} {g : β → α} {a : α} (ha : HasSum f a)
    (hf : ∀ b, HasSum (fun c => f (b, c)) (g b)) : HasSum g a :=
  HasSum.sigma ((Equiv.sigmaEquivProd β γ).hasSum_iff.2 ha) hf
#align has_sum.prod_fiberwise HasSum.prod_fiberwise

theorem Summable.sigma' [RegularSpace α] {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Summable f)
    (hf : ∀ b, Summable fun c => f ⟨b, c⟩) : Summable fun b => ∑' c, f ⟨b, c⟩ :=
  (ha.hasSum.sigma fun b => (hf b).hasSum).summable
#align summable.sigma' Summable.sigma'

theorem HasSum.sigma_of_hasSum [T3Space α] {γ : β → Type*} {f : (Σb : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasSum g a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) (hf' : Summable f) :
    HasSum f a := by simpa [(hf'.hasSum.sigma hf).unique ha] using hf'.hasSum
                     -- 🎉 no goals
#align has_sum.sigma_of_has_sum HasSum.sigma_of_hasSum

/-- Version of `HasSum.update` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that `f.update` has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
theorem HasSum.update' {α β : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] {f : β → α} {a a' : α} (hf : HasSum f a) (b : β) (x : α)
    (hf' : HasSum (update f b x) a') : a + x = a' + f b := by
  have : ∀ b', f b' + ite (b' = b) x 0 = update f b x b' + ite (b' = b) (f b) 0 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using add_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.add (hasSum_ite_eq b x)
  -- ⊢ a + x = a' + f b
  simp_rw [this] at h
  -- ⊢ a + x = a' + f b
  exact HasSum.unique h (hf'.add (hasSum_ite_eq b (f b)))
  -- 🎉 no goals
#align has_sum.update' HasSum.update'

/-- Version of `hasSum_ite_sub_hasSum` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that the `ite` expression has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
theorem eq_add_of_hasSum_ite {α β : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] {f : β → α} {a : α} (hf : HasSum f a) (b : β) (a' : α)
    (hf' : HasSum (fun n => ite (n = b) 0 (f n)) a') : a = a' + f b := by
  refine' (add_zero a).symm.trans (hf.update' b 0 _)
  -- ⊢ HasSum (update f b 0) a'
  convert hf'
  -- ⊢ update f b 0 x✝ = if x✝ = b then 0 else f x✝
  apply update_apply
  -- 🎉 no goals
#align eq_add_of_has_sum_ite eq_add_of_hasSum_ite

end HasSum

section tsum

variable [AddCommMonoid α] [TopologicalSpace α] {f g : β → α} {a a₁ a₂ : α}

theorem tsum_congr_subtype (f : β → α) {s t : Set β} (h : s = t) :
    ∑' x : s, f x = ∑' x : t, f x := by rw [h]
                                        -- 🎉 no goals
#align tsum_congr_subtype tsum_congr_subtype

theorem tsum_eq_finsum (hf : (support f).Finite) :
    ∑' b, f b = ∑ᶠ b, f b := by simp [tsum_def, summable_of_finite_support hf, hf]
                                -- 🎉 no goals

theorem tsum_eq_sum {s : Finset β} (hf : ∀ (b) (_ : b ∉ s), f b = 0) :
    ∑' b, f b = ∑ b in s, f b := by
  have I : support f ⊆ s := by
    intros x hx
    contrapose! hx
    rw [nmem_support]
    exact hf _ hx
  simp [tsum_def, summable_of_ne_finset_zero hf, Set.Finite.subset (finite_toSet s) I]
  -- ⊢ ∑ᶠ (b : β), f b = ∑ b in s, f b
  exact finsum_eq_sum_of_support_subset f I
  -- 🎉 no goals
#align tsum_eq_sum tsum_eq_sum

@[simp]
theorem tsum_zero : ∑' _ : β, (0 : α) = 0 := by rw [tsum_eq_finsum] <;> simp
                                                -- ⊢ ∑ᶠ (b : β), 0 = 0
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
#align tsum_zero tsum_zero
#align tsum_zero' tsum_zero

@[simp]
theorem tsum_empty [IsEmpty β] : ∑' b, f b = 0 := by
  rw [tsum_eq_sum (s := (∅ : Finset β))] <;> simp
  -- ⊢ ∑ b in ∅, f b = 0
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align tsum_empty tsum_empty

theorem tsum_congr {f g : β → α}
    (hfg : ∀ b, f b = g b) : ∑' b, f b = ∑' b, g b :=
  congr_arg tsum (funext hfg)
#align tsum_congr tsum_congr

theorem tsum_fintype [Fintype β] (f : β → α) : ∑' b, f b = ∑ b, f b := by
  apply tsum_eq_sum; simp
  -- ⊢ ∀ (b : β), ¬b ∈ univ → f b = 0
                     -- 🎉 no goals
#align tsum_fintype tsum_fintype

theorem sum_eq_tsum_indicator (f : β → α) (s : Finset β) :
    ∑ x in s, f x = ∑' x, Set.indicator (↑s) f x :=
  have : ∀ (x) (_ : x ∉ s), Set.indicator (↑s) f x = 0 := fun _ hx =>
    Set.indicator_apply_eq_zero.2 fun hx' => (hx <| Finset.mem_coe.1 hx').elim
  (Finset.sum_congr rfl fun _ hx =>
        (Set.indicator_apply_eq_self.2 fun hx' => (hx' <| Finset.mem_coe.2 hx).elim).symm).trans
    (tsum_eq_sum this).symm
#align sum_eq_tsum_indicator sum_eq_tsum_indicator

theorem tsum_bool (f : Bool → α) : ∑' i : Bool, f i = f False + f True := by
  rw [tsum_fintype, Finset.sum_eq_add] <;> simp
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align tsum_bool tsum_bool

theorem tsum_eq_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) :
    ∑' b, f b = f b := by
  rw [tsum_eq_sum (s := {b}), sum_singleton]
  -- ⊢ ∀ (b_1 : β), ¬b_1 ∈ {b} → f b_1 = 0
  exact fun b' hb' ↦ hf b' (by simpa using hb')
  -- 🎉 no goals
  #align tsum_eq_single tsum_eq_single

theorem tsum_tsum_eq_single (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ (b') (_ : b' ≠ b), f b' c = 0)
    (hfc : ∀ (b' : β) (c' : γ), c' ≠ c → f b' c' = 0) : ∑' (b') (c'), f b' c' = f b c :=
  calc
    ∑' (b') (c'), f b' c' = ∑' b', f b' c := tsum_congr fun b' => tsum_eq_single _ (hfc b')
    _ = f b c := tsum_eq_single _ hfb
#align tsum_tsum_eq_single tsum_tsum_eq_single

@[simp]
theorem tsum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    ∑' b', (if b' = b then a else 0) = a := by
  rw [tsum_eq_single b]
  -- ⊢ (if b = b then a else 0) = a
  · simp
    -- 🎉 no goals
  · intro b' hb'; simp [hb']
    -- ⊢ (if b' = b then a else 0) = 0
                  -- 🎉 no goals
#align tsum_ite_eq tsum_ite_eq

@[simp]
theorem tsum_pi_single [DecidableEq β] (b : β) (a : α) : ∑' b', Pi.single b a b' = a := by
  rw [tsum_eq_single b]
  -- ⊢ Pi.single b a b = a
  · simp
    -- 🎉 no goals
  · intro b' hb'; simp [hb']
    -- ⊢ Pi.single b a b' = 0
                  -- 🎉 no goals
#align tsum_pi_single tsum_pi_single

-- Porting note: Added nolint simpNF, simpNF falsely claims that lhs does not simplify under simp
@[simp, nolint simpNF]
theorem Finset.tsum_subtype (s : Finset β) (f : β → α) :
    ∑' x : { x // x ∈ s }, f x = ∑ x in s, f x := by
  rw [← sum_attach]; exact tsum_fintype _
  -- ⊢ ∑' (x : { x // x ∈ s }), f ↑x = ∑ x in attach s, f ↑x
                     -- 🎉 no goals
#align finset.tsum_subtype Finset.tsum_subtype

theorem Finset.tsum_subtype' (s : Finset β) (f : β → α) :
    ∑' x : (s : Set β), f x = ∑ x in s, f x := by simp
                                                  -- 🎉 no goals
#align finset.tsum_subtype' Finset.tsum_subtype'

-- Porting note: Added nolint simpNF, simpNF falsely claims that lhs does not simplify under simp
@[simp, nolint simpNF]
theorem tsum_singleton (b : β) (f : β → α) : ∑' x : ({b} : Set β), f x = f b := by
  rw [← coe_singleton, Finset.tsum_subtype', sum_singleton]
  -- 🎉 no goals
#align tsum_singleton tsum_singleton

variable [T2Space α]

theorem HasSum.tsum_eq (ha : HasSum f a) : ∑' b, f b = a :=
  (Summable.hasSum ⟨a, ha⟩).unique ha
#align has_sum.tsum_eq HasSum.tsum_eq

theorem Summable.hasSum_iff (h : Summable f) : HasSum f a ↔ ∑' b, f b = a :=
  Iff.intro HasSum.tsum_eq fun eq => eq ▸ h.hasSum
#align summable.has_sum_iff Summable.hasSum_iff

theorem tsum_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    ∑' b : β, (if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' b : β, x b h := by
  by_cases hP : P <;> simp [hP]
  -- ⊢ (∑' (b : β), if h : P then 0 else x b h) = if h : P then 0 else ∑' (b : β),  …
                      -- 🎉 no goals
                      -- 🎉 no goals
#align tsum_dite_right tsum_dite_right

theorem tsum_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    ∑' b : β, (if h : P then x b h else 0) = if h : P then ∑' b : β, x b h else 0 := by
  by_cases hP : P <;> simp [hP]
  -- ⊢ (∑' (b : β), if h : P then x b h else 0) = if h : P then ∑' (b : β), x b h e …
                      -- 🎉 no goals
                      -- 🎉 no goals
#align tsum_dite_left tsum_dite_left

theorem Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum {α' : Type*} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h0 : e 0 = 0) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : ∑' b, f b = e (∑' c, g c) :=
  _root_.by_cases (fun x => (h.mpr x.hasSum).tsum_eq) fun hg : ¬Summable g => by
    have hf : ¬Summable f := mt (hes.summable_iff_of_hasSum_iff @h).1 hg
    -- ⊢ ∑' (b : β), f b = e (∑' (c : γ), g c)
    simp [tsum_def, hf, hg, h0]
    -- 🎉 no goals
#align function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum

theorem tsum_eq_tsum_of_hasSum_iff_hasSum {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasSum f a ↔ HasSum g a) : ∑' b, f b = ∑' c, g c :=
  surjective_id.tsum_eq_tsum_of_hasSum_iff_hasSum rfl @h
#align tsum_eq_tsum_of_has_sum_iff_has_sum tsum_eq_tsum_of_hasSum_iff_hasSum

theorem Equiv.tsum_eq (j : γ ≃ β) (f : β → α) : ∑' c, f (j c) = ∑' b, f b :=
  tsum_eq_tsum_of_hasSum_iff_hasSum j.hasSum_iff
#align equiv.tsum_eq Equiv.tsum_eq

theorem Equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x, g (e x) = f x) : ∑' x, f x = ∑' y, g y :=
  tsum_eq_tsum_of_hasSum_iff_hasSum (hasSum_iff_of_support e he)
#align equiv.tsum_eq_tsum_of_support Equiv.tsum_eq_tsum_of_support

theorem tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : ∑' x, f x = ∑' y, g y :=
  tsum_eq_tsum_of_hasSum_iff_hasSum (hasSum_iff_hasSum_of_ne_zero_bij i hi hf hfg)
#align tsum_eq_tsum_of_ne_zero_bij tsum_eq_tsum_of_ne_zero_bij

/-! ### `tsum` on subsets -/

theorem tsum_subtype (s : Set β) (f : β → α) : ∑' x : s, f x = ∑' x, s.indicator f x :=
  tsum_eq_tsum_of_hasSum_iff_hasSum hasSum_subtype_iff_indicator
#align tsum_subtype tsum_subtype

theorem tsum_subtype_eq_of_support_subset {f : β → α} {s : Set β} (hs : support f ⊆ s) :
    ∑' x : s, f x = ∑' x, f x :=
  tsum_eq_tsum_of_hasSum_iff_hasSum (hasSum_subtype_iff_of_support_subset hs)
#align tsum_subtype_eq_of_support_subset tsum_subtype_eq_of_support_subset

-- Porting note: Added nolint simpNF, simpNF falsely claims that lhs does not simplify under simp
@[simp, nolint simpNF]
theorem tsum_univ (f : β → α) : ∑' x : (Set.univ : Set β), f x = ∑' x, f x :=
  tsum_subtype_eq_of_support_subset <| Set.subset_univ _
#align tsum_univ tsum_univ

theorem tsum_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    ∑' x : g '' s, f x = ∑' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tsum_eq fun x => f x).symm
#align tsum_image tsum_image

theorem tsum_range {g : γ → β} (f : β → α) (hg : Injective g) :
    ∑' x : Set.range g, f x = ∑' x, f (g x) := by
  rw [← Set.image_univ, tsum_image f (hg.injOn _)]
  -- ⊢ ∑' (x : ↑Set.univ), f (g ↑x) = ∑' (x : γ), f (g x)
  simp_rw [← comp_apply (g := g), tsum_univ (f ∘ g)]
  -- 🎉 no goals
#align tsum_range tsum_range

section ContinuousAdd

variable [ContinuousAdd α]

theorem tsum_add (hf : Summable f) (hg : Summable g) :
    ∑' b, (f b + g b) = ∑' b, f b + ∑' b, g b :=
  (hf.hasSum.add hg.hasSum).tsum_eq
#align tsum_add tsum_add

theorem tsum_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    ∑' b, ∑ i in s, f i b = ∑ i in s, ∑' b, f i b :=
  (hasSum_sum fun i hi => (hf i hi).hasSum).tsum_eq
#align tsum_sum tsum_sum

/-- Version of `tsum_eq_add_tsum_ite` for `AddCommMonoid` rather than `AddCommGroup`.
Requires a different convergence assumption involving `Function.update`. -/
theorem tsum_eq_add_tsum_ite' {f : β → α} (b : β) (hf : Summable (update f b 0)) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  calc
    ∑' x, f x = ∑' x, (ite (x = b) (f x) 0 + update f b 0 x) :=
      tsum_congr fun n => by split_ifs with h <;> simp [update_apply, h]
                             -- ⊢ f n = f n + update f b 0 n
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
    _ = ∑' x, ite (x = b) (f x) 0 + ∑' x, update f b 0 x :=
      tsum_add ⟨ite (b = b) (f b) 0, hasSum_single b fun b hb => if_neg hb⟩ hf
    _ = ite (b = b) (f b) 0 + ∑' x, update f b 0 x := by
      congr
      -- ⊢ (∑' (x : β), if x = b then f x else 0) = if b = b then f b else 0
      exact tsum_eq_single b fun b' hb' => if_neg hb'
      -- 🎉 no goals
    _ = f b + ∑' x, ite (x = b) 0 (f x) :=
    by simp only [update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]
       -- 🎉 no goals
#align tsum_eq_add_tsum_ite' tsum_eq_add_tsum_ite'

variable [AddCommMonoid δ] [TopologicalSpace δ] [T3Space δ] [ContinuousAdd δ]

theorem tsum_sigma' {γ : β → Type*} {f : (Σb : β, γ b) → δ} (h₁ : ∀ b, Summable fun c => f ⟨b, c⟩)
    (h₂ : Summable f) : ∑' p, f p = ∑' (b) (c), f ⟨b, c⟩ :=
  (h₂.hasSum.sigma fun b => (h₁ b).hasSum).tsum_eq.symm
#align tsum_sigma' tsum_sigma'

theorem tsum_prod' {f : β × γ → δ} (h : Summable f) (h₁ : ∀ b, Summable fun c => f (b, c)) :
    ∑' p, f p = ∑' (b) (c), f (b, c) :=
  (h.hasSum.prod_fiberwise fun b => (h₁ b).hasSum).tsum_eq.symm
#align tsum_prod' tsum_prod'

theorem tsum_comm' {f : β → γ → δ} (h : Summable (Function.uncurry f)) (h₁ : ∀ b, Summable (f b))
    (h₂ : ∀ c, Summable fun b => f b c) : ∑' (c) (b), f b c = ∑' (b) (c), f b c := by
  erw [← tsum_prod' h h₁, ← tsum_prod' h.prod_symm h₂, ← (Equiv.prodComm γ β).tsum_eq (uncurry f)]
  -- ⊢ ∑' (p : γ × β), uncurry f (Prod.swap p) = ∑' (c : γ × β), uncurry f (↑(Equiv …
  rfl
  -- 🎉 no goals
#align tsum_comm' tsum_comm'

end ContinuousAdd

open Encodable

section Encodable

variable [Encodable γ]

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_iSup_decode₂ [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (s : γ → β) :
    ∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∑' b : γ, m (s b) := by
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).isSome :=by
    intro n h
    generalize decode₂ γ n = foo at *
    cases' foo with b
    · refine' (h <| by simp [m0]).elim
    · exact rfl
  symm
  -- ⊢ ∑' (b : γ), m (s b) = ∑' (i : ℕ), m (⨆ (b : γ) (_ : b ∈ decode₂ γ i), s b)
  refine' tsum_eq_tsum_of_ne_zero_bij (fun a => Option.get _ (H a.1 a.2)) _ _ _
  · dsimp only []
    -- ⊢ ∀ ⦃x y : ↑(support fun i => m (⨆ (b : γ) (_ : b ∈ decode₂ γ i), s b))⦄, Opti …
    rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    -- ⊢ ↑{ val := m, property := hm } = ↑{ val := n, property := hn }
    have := mem_decode₂.1 (Option.get_mem (H n hn))
    -- ⊢ ↑{ val := m, property := hm } = ↑{ val := n, property := hn }
    rwa [← e, mem_decode₂.1 (Option.get_mem (H m hm))] at this
    -- 🎉 no goals
  · intro b h
    -- ⊢ b ∈ Set.range fun a => Option.get (decode₂ γ ↑a) (_ : Option.isSome (decode₂ …
    refine' ⟨⟨encode b, _⟩, _⟩
    -- ⊢ encode b ∈ support fun i => m (⨆ (b : γ) (_ : b ∈ decode₂ γ i), s b)
    · simp only [mem_support, encodek₂] at h ⊢
      -- ⊢ m (⨆ (b_1 : γ) (_ : b_1 ∈ some b), s b_1) ≠ 0
      convert h
      -- ⊢ ⨆ (b_1 : γ) (_ : b_1 ∈ some b), s b_1 = s b
      simp [Set.ext_iff, encodek₂]
      -- 🎉 no goals
    · exact Option.get_of_mem _ (encodek₂ _)
      -- 🎉 no goals
  · rintro ⟨n, h⟩
    -- ⊢ m (s ((fun a => Option.get (decode₂ γ ↑a) (_ : Option.isSome (decode₂ γ ↑a)  …
    dsimp only [Subtype.coe_mk]
    -- ⊢ m (s (Option.get (decode₂ γ n) (_ : Option.isSome (decode₂ γ n) = true))) =  …
    trans
    swap
    rw [show decode₂ γ n = _ from Option.get_mem (H n h)]
    -- ⊢ m (s (Option.get (decode₂ γ n) (_ : Option.isSome (decode₂ γ n) = true))) =  …
    congr
    -- ⊢ s (Option.get (decode₂ γ n) (_ : Option.isSome (decode₂ γ n) = true)) = ⨆ (b …
    simp [ext_iff, -Option.some_get]
    -- 🎉 no goals
#align tsum_supr_decode₂ tsum_iSup_decode₂

/-- `tsum_iSup_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_iUnion_decode₂ (m : Set β → α) (m0 : m ∅ = 0) (s : γ → Set β) :
    ∑' i, m (⋃ b ∈ decode₂ γ i, s b) = ∑' b, m (s b) :=
  tsum_iSup_decode₂ m m0 s
#align tsum_Union_decode₂ tsum_iUnion_decode₂

end Encodable

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/


section Countable

variable [Countable γ]

/-- If a function is countably sub-additive then it is sub-additive on countable types -/
theorem rel_iSup_tsum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_iSup : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : γ → β) :
    R (m (⨆ b : γ, s b)) (∑' b : γ, m (s b)) := by
  cases nonempty_encodable γ
  -- ⊢ R (m (⨆ (b : γ), s b)) (∑' (b : γ), m (s b))
  rw [← iSup_decode₂, ← tsum_iSup_decode₂ _ m0 s]
  -- ⊢ R (m (⨆ (i : ℕ) (b : γ) (_ : b ∈ decode₂ γ i), s b)) (∑' (i : ℕ), m (⨆ (b :  …
  exact m_iSup _
  -- 🎉 no goals
#align rel_supr_tsum rel_iSup_tsum

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_iSup_sum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_iSup : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : δ → β) (t : Finset δ) :
    R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tsum_subtype]
  -- ⊢ R (m (⨆ (x : { d // d ∈ t }), s ↑x)) (∑' (x : { x // x ∈ t }), m (s ↑x))
  exact rel_iSup_tsum m m0 R m_iSup _
  -- 🎉 no goals
#align rel_supr_sum rel_iSup_sum

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_iSup : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s₁ s₂ : β) :
    R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) := by
  convert rel_iSup_tsum m m0 R m_iSup fun b => cond b s₁ s₂
  -- ⊢ s₁ ⊔ s₂ = ⨆ (b : Bool), bif b then s₁ else s₂
  · simp only [iSup_bool_eq, cond]
    -- 🎉 no goals
  · rw [tsum_fintype, Fintype.sum_bool, cond, cond]
    -- 🎉 no goals
#align rel_sup_add rel_sup_add

end Countable

variable [ContinuousAdd α]

theorem tsum_add_tsum_compl {s : Set β} (hs : Summable (f ∘ (↑) : s → α))
    (hsc : Summable (f ∘ (↑) : ↑sᶜ → α)) : ∑' x : s, f x + ∑' x : ↑sᶜ, f x = ∑' x, f x :=
  (hs.hasSum.add_compl hsc.hasSum).tsum_eq.symm
#align tsum_add_tsum_compl tsum_add_tsum_compl

theorem tsum_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ (↑) : s → α))
    (ht : Summable (f ∘ (↑) : t → α)) : ∑' x : ↑(s ∪ t), f x = ∑' x : s, f x + ∑' x : t, f x :=
  (hs.hasSum.add_disjoint hd ht.hasSum).tsum_eq
#align tsum_union_disjoint tsum_union_disjoint

theorem tsum_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Summable (f ∘ (↑) : t i → α)) :
    ∑' x : ⋃ i ∈ s, t i, f x = ∑ i in s, ∑' x : t i, f x :=
  (hasSum_sum_disjoint _ hd fun i hi => (hf i hi).hasSum).tsum_eq
#align tsum_finset_bUnion_disjoint tsum_finset_bUnion_disjoint

theorem tsum_even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) :
    ∑' k, f (2 * k) + ∑' k, f (2 * k + 1) = ∑' k, f k :=
  (he.hasSum.even_add_odd ho.hasSum).tsum_eq.symm
#align tsum_even_add_odd tsum_even_add_odd

end tsum

section TopologicalGroup

variable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]

variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
theorem HasSum.neg (h : HasSum f a) : HasSum (fun b => -f b) (-a) := by
  simpa only using h.map (-AddMonoidHom.id α) continuous_neg
  -- 🎉 no goals
#align has_sum.neg HasSum.neg

theorem Summable.neg (hf : Summable f) : Summable fun b => -f b :=
  hf.hasSum.neg.summable
#align summable.neg Summable.neg

theorem Summable.of_neg (hf : Summable fun b => -f b) : Summable f := by
  simpa only [neg_neg] using hf.neg
  -- 🎉 no goals
#align summable.of_neg Summable.of_neg

theorem summable_neg_iff : (Summable fun b => -f b) ↔ Summable f :=
  ⟨Summable.of_neg, Summable.neg⟩
#align summable_neg_iff summable_neg_iff

theorem HasSum.sub (hf : HasSum f a₁) (hg : HasSum g a₂) :
    HasSum (fun b => f b - g b) (a₁ - a₂) := by
  simp only [sub_eq_add_neg]
  -- ⊢ HasSum (fun b => f b + -g b) (a₁ + -a₂)
  exact hf.add hg.neg
  -- 🎉 no goals
#align has_sum.sub HasSum.sub

theorem Summable.sub (hf : Summable f) (hg : Summable g) : Summable fun b => f b - g b :=
  (hf.hasSum.sub hg.hasSum).summable
#align summable.sub Summable.sub

theorem Summable.trans_sub (hg : Summable g) (hfg : Summable fun b => f b - g b) : Summable f := by
  simpa only [sub_add_cancel] using hfg.add hg
  -- 🎉 no goals
#align summable.trans_sub Summable.trans_sub

theorem summable_iff_of_summable_sub (hfg : Summable fun b => f b - g b) :
    Summable f ↔ Summable g :=
  ⟨fun hf => hf.trans_sub <| by simpa only [neg_sub] using hfg.neg, fun hg => hg.trans_sub hfg⟩
                                -- 🎉 no goals
#align summable_iff_of_summable_sub summable_iff_of_summable_sub

theorem HasSum.update (hf : HasSum f a₁) (b : β) [DecidableEq β] (a : α) :
    HasSum (update f b a) (a - f b + a₁) := by
  convert (hasSum_ite_eq b (a - f b)).add hf
  -- ⊢ Function.update f b a x✝ = (if x✝ = b then a - f b else 0) + f x✝
  rename_i b'
  -- ⊢ Function.update f b a b' = (if b' = b then a - f b else 0) + f b'
  by_cases h : b' = b
  -- ⊢ Function.update f b a b' = (if b' = b then a - f b else 0) + f b'
  · rw [h, update_same]
    -- ⊢ a = (if b = b then a - f b else 0) + f b
    simp [eq_self_iff_true, if_true, sub_add_cancel]
    -- 🎉 no goals
  · simp only [h, update_noteq, if_false, Ne.def, zero_add, not_false_iff]
    -- 🎉 no goals
#align has_sum.update HasSum.update

theorem Summable.update (hf : Summable f) (b : β) [DecidableEq β] (a : α) :
    Summable (update f b a) :=
  (hf.hasSum.update b a).summable
#align summable.update Summable.update

theorem HasSum.hasSum_compl_iff {s : Set β} (hf : HasSum (f ∘ (↑) : s → α) a₁) :
    HasSum (f ∘ (↑) : ↑sᶜ → α) a₂ ↔ HasSum f (a₁ + a₂) := by
  refine' ⟨fun h => hf.add_compl h, fun h => _⟩
  -- ⊢ HasSum (f ∘ Subtype.val) a₂
  rw [hasSum_subtype_iff_indicator] at hf ⊢
  -- ⊢ HasSum (Set.indicator sᶜ f) a₂
  rw [Set.indicator_compl]
  -- ⊢ HasSum (f - Set.indicator s f) a₂
  simpa only [add_sub_cancel'] using h.sub hf
  -- 🎉 no goals
#align has_sum.has_sum_compl_iff HasSum.hasSum_compl_iff

theorem HasSum.hasSum_iff_compl {s : Set β} (hf : HasSum (f ∘ (↑) : s → α) a₁) :
    HasSum f a₂ ↔ HasSum (f ∘ (↑) : ↑sᶜ → α) (a₂ - a₁) :=
  Iff.symm <| hf.hasSum_compl_iff.trans <| by rw [add_sub_cancel'_right]
                                              -- 🎉 no goals
#align has_sum.has_sum_iff_compl HasSum.hasSum_iff_compl

theorem Summable.summable_compl_iff {s : Set β} (hf : Summable (f ∘ (↑) : s → α)) :
    Summable (f ∘ (↑) : ↑sᶜ → α) ↔ Summable f :=
  ⟨fun ⟨_, ha⟩ => (hf.hasSum.hasSum_compl_iff.1 ha).summable, fun ⟨_, ha⟩ =>
    (hf.hasSum.hasSum_iff_compl.1 ha).summable⟩
#align summable.summable_compl_iff Summable.summable_compl_iff

protected theorem Finset.hasSum_compl_iff (s : Finset β) :
    HasSum (fun x : { x // x ∉ s } => f x) a ↔ HasSum f (a + ∑ i in s, f i) :=
  (s.hasSum f).hasSum_compl_iff.trans <| by rw [add_comm]
                                            -- 🎉 no goals
#align finset.has_sum_compl_iff Finset.hasSum_compl_iff

protected theorem Finset.hasSum_iff_compl (s : Finset β) :
    HasSum f a ↔ HasSum (fun x : { x // x ∉ s } => f x) (a - ∑ i in s, f i) :=
  (s.hasSum f).hasSum_iff_compl
#align finset.has_sum_iff_compl Finset.hasSum_iff_compl

protected theorem Finset.summable_compl_iff (s : Finset β) :
    (Summable fun x : { x // x ∉ s } => f x) ↔ Summable f :=
  (s.summable f).summable_compl_iff
#align finset.summable_compl_iff Finset.summable_compl_iff

theorem Set.Finite.summable_compl_iff {s : Set β} (hs : s.Finite) :
    Summable (f ∘ (↑) : ↑sᶜ → α) ↔ Summable f :=
  (hs.summable f).summable_compl_iff
#align set.finite.summable_compl_iff Set.Finite.summable_compl_iff

theorem hasSum_ite_sub_hasSum [DecidableEq β] (hf : HasSum f a) (b : β) :
    HasSum (fun n => ite (n = b) 0 (f n)) (a - f b) := by
  convert hf.update b 0 using 1
  -- ⊢ (fun n => if n = b then 0 else f n) = update f b 0
  · ext n
    -- ⊢ (if n = b then 0 else f n) = update f b 0 n
    rw [Function.update_apply]
    -- 🎉 no goals
  · rw [sub_add_eq_add_sub, zero_add]
    -- 🎉 no goals
#align has_sum_ite_sub_has_sum hasSum_ite_sub_hasSum

section tsum

variable [T2Space α]

theorem tsum_neg : ∑' b, -f b = -∑' b, f b := by
  by_cases hf : Summable f
  -- ⊢ ∑' (b : β), -f b = -∑' (b : β), f b
  · exact hf.hasSum.neg.tsum_eq
    -- 🎉 no goals
  · simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.of_neg hf)]
    -- 🎉 no goals
#align tsum_neg tsum_neg

theorem tsum_sub (hf : Summable f) (hg : Summable g) :
    ∑' b, (f b - g b) = ∑' b, f b - ∑' b, g b :=
  (hf.hasSum.sub hg.hasSum).tsum_eq
#align tsum_sub tsum_sub

theorem sum_add_tsum_compl {s : Finset β} (hf : Summable f) :
    ((∑ x in s, f x) + ∑' x : ↑(s : Set β)ᶜ, f x) = ∑' x, f x :=
  ((s.hasSum f).add_compl (s.summable_compl_iff.2 hf).hasSum).tsum_eq.symm
#align sum_add_tsum_compl sum_add_tsum_compl

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
theorem tsum_eq_add_tsum_ite [DecidableEq β] (hf : Summable f) (b : β) :
    ∑' n, f n = f b + ∑' n, ite (n = b) 0 (f n) := by
  rw [(hasSum_ite_sub_hasSum hf.hasSum b).tsum_eq]
  -- ⊢ ∑' (n : β), f n = f b + (∑' (b : β), f b - f b)
  exact (add_sub_cancel'_right _ _).symm
  -- 🎉 no goals
#align tsum_eq_add_tsum_ite tsum_eq_add_tsum_ite

end tsum

/-!
### Sums on nat

We show the formula `∑ i in range k, f i + ∑' i, f (i + k) = ∑' i, f i`, in
`sum_add_tsum_nat_add`, as well as several results relating sums on `ℕ` and `ℤ`.
-/

section Nat

theorem hasSum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  refine' Iff.trans _ (range k).hasSum_compl_iff
  -- ⊢ HasSum (fun n => f (n + k)) a ↔ HasSum (fun x => f ↑x) a
  rw [← (notMemRangeEquiv k).symm.hasSum_iff]
  -- ⊢ HasSum (fun n => f (n + k)) a ↔ HasSum ((fun x => f ↑x) ∘ ↑(notMemRangeEquiv …
  rfl
  -- 🎉 no goals
#align has_sum_nat_add_iff hasSum_nat_add_iff

theorem summable_nat_add_iff {f : ℕ → α} (k : ℕ) : (Summable fun n => f (n + k)) ↔ Summable f :=
  Iff.symm <|
    (Equiv.addRight (∑ i in range k, f i)).surjective.summable_iff_of_hasSum_iff
      (hasSum_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff

theorem hasSum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) (a - ∑ i in range k, f i) ↔ HasSum f a := by
  simp [hasSum_nat_add_iff]
  -- 🎉 no goals
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

theorem HasSum.sum_range_add [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] {f : ℕ → M}
    {k : ℕ} {a : M} (h : HasSum (fun n ↦ f (n + k)) a) : HasSum f ((∑ i in range k, f i) + a) := by
  refine ((range k).hasSum f).add_compl ?_
  -- ⊢ HasSum (f ∘ Subtype.val) a
  rwa [← (notMemRangeEquiv k).symm.hasSum_iff]
  -- 🎉 no goals

theorem sum_add_tsum_nat_add' [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] [T2Space M]
    {f : ℕ → M} {k : ℕ} (h : Summable (fun n => f (n + k))) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i :=
  h.hasSum.sum_range_add.tsum_eq.symm

theorem sum_add_tsum_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Summable f) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i :=
  sum_add_tsum_nat_add' <| (summable_nat_add_iff k).2 h
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

theorem tsum_eq_zero_add' [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] [T2Space M]
    {f : ℕ → M} (hf : Summable (fun n => f (n + 1))) :
    ∑' b, f b = f 0 + ∑' b, f (b + 1) := by
  simpa only [sum_range_one] using (sum_add_tsum_nat_add' hf).symm
  -- 🎉 no goals

theorem tsum_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Summable f) :
    ∑' b, f b = f 0 + ∑' b, f (b + 1) :=
  tsum_eq_zero_add' <| (summable_nat_add_iff 1).2 hf
#align tsum_eq_zero_add tsum_eq_zero_add

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add [T2Space α] (f : ℕ → α) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  by_cases hf : Summable f
  -- ⊢ Tendsto (fun i => ∑' (k : ℕ), f (k + i)) atTop (𝓝 0)
  · have h₀ : (fun i => ∑' i, f i - ∑ j in range i, f j) = fun i => ∑' k : ℕ, f (k + i) := by
      ext1 i
      rw [sub_eq_iff_eq_add, add_comm, sum_add_tsum_nat_add i hf]
    have h₁ : Tendsto (fun _ : ℕ => ∑' i, f i) atTop (𝓝 (∑' i, f i)) := tendsto_const_nhds
    -- ⊢ Tendsto (fun i => ∑' (k : ℕ), f (k + i)) atTop (𝓝 0)
    simpa only [h₀, sub_self] using Tendsto.sub h₁ hf.hasSum.tendsto_sum_nat
    -- 🎉 no goals
  · convert tendsto_const_nhds (α := α) (β := ℕ) (a := 0) (f := atTop)
    -- ⊢ ∑' (k : ℕ), f (k + x✝) = 0
    rename_i i
    -- ⊢ ∑' (k : ℕ), f (k + i) = 0
    rw [← summable_nat_add_iff i] at hf
    -- ⊢ ∑' (k : ℕ), f (k + i) = 0
    exact tsum_eq_zero_of_not_summable hf
    -- 🎉 no goals
#align tendsto_sum_nat_add tendsto_sum_nat_add

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
theorem HasSum.int_rec {b : α} {f g : ℕ → α} (hf : HasSum f a) (hg : HasSum g b) :
    @HasSum α _ _ _ (@Int.rec (fun _ => α) f g : ℤ → α) (a + b) := by
  -- note this proof works for any two-case inductive
  have h₁ : Injective ((↑) : ℕ → ℤ) := @Int.ofNat.inj
  -- ⊢ HasSum (Int.rec f g) (a + b)
  have h₂ : Injective Int.negSucc := @Int.negSucc.inj
  -- ⊢ HasSum (Int.rec f g) (a + b)
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) _
      exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  exact HasSum.add_isCompl this (h₁.hasSum_range_iff.mpr hf) (h₂.hasSum_range_iff.mpr hg)
  -- 🎉 no goals
#align has_sum.int_rec HasSum.int_rec

theorem HasSum.nonneg_add_neg {b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) := by
  simp_rw [← Int.negSucc_coe] at hneg
  -- ⊢ HasSum f (a + b)
  convert hnonneg.int_rec hneg using 1
  -- ⊢ f = Int.rec (fun n => f ↑n) fun n => f (Int.negSucc n)
  ext (i | j) <;> rfl
  -- ⊢ f (Int.ofNat i) = Int.rec (fun n => f ↑n) (fun n => f (Int.negSucc n)) (Int. …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align has_sum.nonneg_add_neg HasSum.nonneg_add_neg

theorem HasSum.pos_add_zero_add_neg {b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) := by
    intro g hg
    -- ⊢ HasSum g (a + g 0)
    simpa using (hasSum_nat_add_iff _).mp hg
    -- 🎉 no goals
  (this (fun n => f n) hpos).nonneg_add_neg hneg
#align has_sum.pos_add_zero_add_neg HasSum.pos_add_zero_add_neg

theorem summable_int_of_summable_nat {f : ℤ → α} (hp : Summable fun n : ℕ => f n)
    (hn : Summable fun n : ℕ => f (-n)) : Summable f :=
  (HasSum.nonneg_add_neg hp.hasSum <| Summable.hasSum <| (summable_nat_add_iff 1).mpr hn).summable
#align summable_int_of_summable_nat summable_int_of_summable_nat

theorem HasSum.sum_nat_of_sum_int {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {a : α} {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ => f n + f (-n)) (a + f 0) := by
  apply (hf.add (hasSum_ite_eq (0 : ℤ) (f 0))).hasSum_of_sum_eq fun u => ?_
  -- ⊢ ∃ v, ∀ (v' : Finset ℕ), v ⊆ v' → ∃ u', u ⊆ u' ∧ ∑ x in u', (f x + if x = 0 t …
  refine' ⟨u.image Int.natAbs, fun v' hv' => _⟩
  -- ⊢ ∃ u', u ⊆ u' ∧ ∑ x in u', (f x + if x = 0 then f 0 else 0) = ∑ b in v', (f ↑ …
  let u1 := v'.image fun x : ℕ => (x : ℤ)
  -- ⊢ ∃ u', u ⊆ u' ∧ ∑ x in u', (f x + if x = 0 then f 0 else 0) = ∑ b in v', (f ↑ …
  let u2 := v'.image fun x : ℕ => -(x : ℤ)
  -- ⊢ ∃ u', u ⊆ u' ∧ ∑ x in u', (f x + if x = 0 then f 0 else 0) = ∑ b in v', (f ↑ …
  have A : u ⊆ u1 ∪ u2 := by
    intro x hx
    simp only [mem_union, mem_image, exists_prop]
    rcases le_total 0 x with (h'x | h'x)
    · left
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [h'x, Int.coe_natAbs, abs_eq_self]
    · right
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [abs_of_nonpos h'x, Int.coe_natAbs, neg_neg]
  refine' ⟨u1 ∪ u2, A, _⟩
  -- ⊢ ∑ x in u1 ∪ u2, (f x + if x = 0 then f 0 else 0) = ∑ b in v', (f ↑b + f (-↑b))
  calc
    (∑ x in u1 ∪ u2, (f x + ite (x = 0) (f 0) 0)) =
        (∑ x in u1 ∪ u2, f x) + ∑ x in u1 ∩ u2, f x := by
      rw [sum_add_distrib]
      congr 1
      refine' (sum_subset_zero_on_sdiff inter_subset_union _ _).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simp at hx
      · intro x hx
        simp only [mem_inter, mem_image, exists_prop] at hx
        have : x = 0 := by
          apply le_antisymm
          · rcases hx.2 with ⟨a, _, rfl⟩
            simp only [Right.neg_nonpos_iff, Nat.cast_nonneg]
          · rcases hx.1 with ⟨a, _, rfl⟩
            simp only [Nat.cast_nonneg]
        simp only [this, eq_self_iff_true, if_true]
    _ = (∑ x in u1, f x) + ∑ x in u2, f x := sum_union_inter
    _ = (∑ b in v', f b) + ∑ b in v', f (-b) := by simp
    _ = ∑ b in v', (f b + f (-b)) := sum_add_distrib.symm
#align has_sum.sum_nat_of_sum_int HasSum.sum_nat_of_sum_int

end Nat

end TopologicalGroup

section UniformGroup

variable [AddCommGroup α] [UniformSpace α]

/-- The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test** -/
theorem summable_iff_cauchySeq_finset [CompleteSpace α] {f : β → α} :
    Summable f ↔ CauchySeq fun s : Finset β => ∑ b in s, f b :=
  cauchy_map_iff_exists_tendsto.symm
#align summable_iff_cauchy_seq_finset summable_iff_cauchySeq_finset

variable [UniformAddGroup α] {f g : β → α} {a a₁ a₂ : α}

theorem cauchySeq_finset_iff_vanishing :
    (CauchySeq fun s : Finset β => ∑ b in s, f b) ↔
      ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  simp only [CauchySeq, cauchy_map_iff, and_iff_right atTop_neBot, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (· ∘ ·), atTop_neBot, true_and]
  rw [tendsto_atTop']
  -- ⊢ (∀ (s : Set α), s ∈ 𝓝 0 → ∃ a, ∀ (b : Finset β × Finset β), b ≥ a → ∑ b in b …
  constructor
  -- ⊢ (∀ (s : Set α), s ∈ 𝓝 0 → ∃ a, ∀ (b : Finset β × Finset β), b ≥ a → ∑ b in b …
  · intro h e he
    -- ⊢ ∃ s, ∀ (t : Finset β), Disjoint t s → ∑ b in t, f b ∈ e
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    -- ⊢ ∃ s, ∀ (t : Finset β), Disjoint t s → ∑ b in t, f b ∈ e
    use s₁ ∪ s₂
    -- ⊢ ∀ (t : Finset β), Disjoint t (s₁ ∪ s₂) → ∑ b in t, f b ∈ e
    intro t ht
    -- ⊢ ∑ b in t, f b ∈ e
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    -- ⊢ ∑ b in t, f b ∈ e
    simpa only [Finset.sum_union ht.symm, add_sub_cancel'] using h
    -- 🎉 no goals
  · rintro h e he
    -- ⊢ ∃ a, ∀ (b : Finset β × Finset β), b ≥ a → ∑ b in b.snd, f b - ∑ b in b.fst,  …
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩
    -- ⊢ ∃ a, ∀ (b : Finset β × Finset β), b ≥ a → ∑ b in b.snd, f b - ∑ b in b.fst,  …
    rcases h d hd with ⟨s, h⟩
    -- ⊢ ∃ a, ∀ (b : Finset β × Finset β), b ≥ a → ∑ b in b.snd, f b - ∑ b in b.fst,  …
    use (s, s)
    -- ⊢ ∀ (b : Finset β × Finset β), b ≥ (s, s) → ∑ b in b.snd, f b - ∑ b in b.fst,  …
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    -- ⊢ ∑ b in (t₁, t₂).snd, f b - ∑ b in (t₁, t₂).fst, f b ∈ e
    have : ((∑ b in t₂, f b) - ∑ b in t₁, f b) = (∑ b in t₂ \ s, f b) - ∑ b in t₁ \ s, f b := by
      rw [← Finset.sum_sdiff ht₁, ← Finset.sum_sdiff ht₂, add_sub_add_right_eq_sub]
    simp only [this]
    -- ⊢ ∑ b in t₂ \ s, f b - ∑ b in t₁ \ s, f b ∈ e
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)
    -- 🎉 no goals
#align cauchy_seq_finset_iff_vanishing cauchySeq_finset_iff_vanishing

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero (f : β → α) :
    Tendsto (fun s : Finset β => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  by_cases H : Summable f
  -- ⊢ Tendsto (fun s => ∑' (b : { x // ¬x ∈ s }), f ↑b) atTop (𝓝 0)
  · intro e he
    -- ⊢ e ∈ Filter.map (fun s => ∑' (b : { x // ¬x ∈ s }), f ↑b) atTop
    rcases exists_mem_nhds_isClosed_subset he with ⟨o, ho, o_closed, oe⟩
    -- ⊢ e ∈ Filter.map (fun s => ∑' (b : { x // ¬x ∈ s }), f ↑b) atTop
    simp only [le_eq_subset, Set.mem_preimage, mem_atTop_sets, Filter.mem_map, ge_iff_le]
    -- ⊢ ∃ a, ∀ (b : Finset β), a ⊆ b → ∑' (b_1 : { x // ¬x ∈ b }), f ↑b_1 ∈ e
    obtain ⟨s, hs⟩ : ∃ s : Finset β, ∀ t : Finset β, Disjoint t s → (∑ b : β in t, f b) ∈ o :=
      cauchySeq_finset_iff_vanishing.1 (Tendsto.cauchySeq H.hasSum) o ho
    refine' ⟨s, fun a sa => oe _⟩
    -- ⊢ ∑' (b : { x // ¬x ∈ a }), f ↑b ∈ o
    have A : Summable fun b : { x // x ∉ a } => f b := a.summable_compl_iff.2 H
    -- ⊢ ∑' (b : { x // ¬x ∈ a }), f ↑b ∈ o
    refine' IsClosed.mem_of_tendsto o_closed A.hasSum (eventually_of_forall fun b => _)
    -- ⊢ ∑ b in b, (fun b => f ↑b) b ∈ o
    have : Disjoint (Finset.image (fun i : { x // x ∉ a } => (i : β)) b) s := by
      refine' disjoint_left.2 fun i hi his => _
      rcases mem_image.1 hi with ⟨i', _, rfl⟩
      exact i'.2 (sa his)
    convert hs _ this using 1
    -- ⊢ ∑ b in b, (fun b => f ↑b) b = ∑ b in image (fun i => ↑i) b, f b
    rw [sum_image]
    -- ⊢ ∀ (x : { x // ¬x ∈ a }), x ∈ b → ∀ (y : { x // ¬x ∈ a }), y ∈ b → ↑x = ↑y →  …
    intro i _ j _ hij
    -- ⊢ i = j
    exact Subtype.ext hij
    -- 🎉 no goals
  · convert tendsto_const_nhds (α := α) (β := Finset β) (f := atTop) (a := 0)
    -- ⊢ ∑' (b : { x // ¬x ∈ x✝ }), f ↑b = 0
    apply tsum_eq_zero_of_not_summable
    -- ⊢ ¬Summable fun b => f ↑b
    rwa [Finset.summable_compl_iff]
    -- 🎉 no goals
#align tendsto_tsum_compl_at_top_zero tendsto_tsum_compl_atTop_zero

variable [CompleteSpace α]

theorem summable_iff_vanishing :
    Summable f ↔ ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing]
  -- 🎉 no goals
#align summable_iff_vanishing summable_iff_vanishing

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
theorem Summable.summable_of_eq_zero_or_self (hf : Summable f) (h : ∀ b, g b = 0 ∨ g b = f b) :
    Summable g :=
  summable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : ∑ b in t.filter fun b => g b = f b, f b = ∑ b in t, g b :=
        calc
          ∑ b in t.filter fun b => g b = f b, f b = ∑ b in t.filter fun b => g b = f b, g b :=
            Finset.sum_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∑ b in t, g b := by
           {refine' Finset.sum_subset (Finset.filter_subset _ _) _
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
      eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩
#align summable.summable_of_eq_zero_or_self Summable.summable_of_eq_zero_or_self

protected theorem Summable.indicator (hf : Summable f) (s : Set β) : Summable (s.indicator f) :=
  hf.summable_of_eq_zero_or_self <| Set.indicator_eq_zero_or_self _ _
#align summable.indicator Summable.indicator

theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : Injective i) :
    Summable (f ∘ i) := by
  simpa only [Set.indicator_range_comp] using
    (hi.summable_iff (fun x hx => Set.indicator_of_not_mem hx _)).2 (hf.indicator (Set.range i))
#align summable.comp_injective Summable.comp_injective

theorem Summable.subtype (hf : Summable f) (s : Set β) : Summable (f ∘ (↑) : s → α) :=
  hf.comp_injective Subtype.coe_injective
#align summable.subtype Summable.subtype

theorem summable_subtype_and_compl {s : Set β} :
    ((Summable fun x : s => f x) ∧ Summable fun x : ↑sᶜ => f x) ↔ Summable f :=
  ⟨and_imp.2 Summable.add_compl, fun h => ⟨h.subtype s, h.subtype sᶜ⟩⟩
#align summable_subtype_and_compl summable_subtype_and_compl

theorem Summable.sigma_factor {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Summable f) (b : β) :
    Summable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective
#align summable.sigma_factor Summable.sigma_factor

theorem Summable.sigma {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    Summable fun b => ∑' c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b
#align summable.sigma Summable.sigma

theorem Summable.prod_factor {f : β × γ → α} (h : Summable f) (b : β) :
    Summable fun c => f (b, c) :=
  h.comp_injective fun _ _ h => (Prod.ext_iff.1 h).2
#align summable.prod_factor Summable.prod_factor

section LocInstances

-- enable inferring a T3-topological space from a topological group
attribute [local instance] TopologicalAddGroup.t3Space

-- disable getting a T0-space from a T1-space as this causes loops
attribute [-instance] T1Space.t0Space

theorem tsum_sigma [T0Space α] {γ : β → Type*} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    ∑' p, f p = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_sigma' (fun b => ha.sigma_factor b) ha
#align tsum_sigma tsum_sigma

theorem tsum_prod [T0Space α] {f : β × γ → α} (h : Summable f) :
    ∑' p, f p = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_prod' h h.prod_factor
#align tsum_prod tsum_prod

theorem tsum_comm [T0Space α] {f : β → γ → α} (h : Summable (Function.uncurry f)) :
    ∑' (c) (b), f b c = ∑' (b) (c), f b c :=
  tsum_comm' h h.prod_factor h.prod_symm.prod_factor
#align tsum_comm tsum_comm

end LocInstances

theorem tsum_subtype_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Set β) :
    ∑' x : s, f x + ∑' x : ↑sᶜ, f x = ∑' x, f x :=
  ((hf.subtype s).hasSum.add_compl (hf.subtype { x | x ∉ s }).hasSum).unique hf.hasSum
#align tsum_subtype_add_tsum_subtype_compl tsum_subtype_add_tsum_subtype_compl

theorem sum_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Finset β) :
    ∑ x in s, f x + ∑' x : { x // x ∉ s }, f x = ∑' x, f x := by
  rw [← tsum_subtype_add_tsum_subtype_compl hf s]
  -- ⊢ ∑ x in s, f x + ∑' (x : { x // ¬x ∈ s }), f ↑x = ∑' (x : ↑↑s), f ↑x + ∑' (x  …
  simp only [Finset.tsum_subtype', add_right_inj]
  -- ⊢ ∑' (x : { x // ¬x ∈ s }), f ↑x = ∑' (x : ↑(↑s)ᶜ), f ↑x
  rfl
  -- 🎉 no goals
#align sum_add_tsum_subtype_compl sum_add_tsum_subtype_compl

end UniformGroup

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [TopologicalAddGroup G] {f : α → G}

theorem Summable.vanishing (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (0 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∑ k in t, f k) ∈ e := by
  letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  -- ⊢ ∃ s, ∀ (t : Finset α), Disjoint t s → ∑ k in t, f k ∈ e
  letI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
  -- ⊢ ∃ s, ∀ (t : Finset α), Disjoint t s → ∑ k in t, f k ∈ e
  rcases hf with ⟨y, hy⟩
  -- ⊢ ∃ s, ∀ (t : Finset α), Disjoint t s → ∑ k in t, f k ∈ e
  exact cauchySeq_finset_iff_vanishing.1 hy.cauchySeq e he
  -- 🎉 no goals
#align summable.vanishing Summable.vanishing

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem Summable.tendsto_cofinite_zero (hf : Summable f) : Tendsto f cofinite (𝓝 0) := by
  intro e he
  -- ⊢ e ∈ Filter.map f cofinite
  rw [Filter.mem_map]
  -- ⊢ f ⁻¹' e ∈ cofinite
  rcases hf.vanishing he with ⟨s, hs⟩
  -- ⊢ f ⁻¹' e ∈ cofinite
  refine' s.eventually_cofinite_nmem.mono fun x hx => _
  -- ⊢ f x ∈ e
  · simpa using hs {x} (disjoint_singleton_left.2 hx)
    -- 🎉 no goals
#align summable.tendsto_cofinite_zero Summable.tendsto_cofinite_zero

theorem Summable.tendsto_atTop_zero {f : ℕ → G} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  -- ⊢ Tendsto f cofinite (𝓝 0)
  exact hf.tendsto_cofinite_zero
  -- 🎉 no goals
#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zero

theorem Summable.countable_support [TopologicalSpace.FirstCountableTopology G] [T1Space G]
    (hf : Summable f) : f.support.Countable := by
  simpa only [sInter_sets_nhds] using hf.tendsto_cofinite_zero.countable_compl_preimage_sInter_sets
  -- 🎉 no goals

end TopologicalGroup

section ConstSmul

variable [Monoid γ] [TopologicalSpace α] [AddCommMonoid α] [DistribMulAction γ α]
  [ContinuousConstSMul γ α] {f : β → α}

theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a) : HasSum (fun i => b • f i) (b • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α _) <| continuous_const_smul _
#align has_sum.const_smul HasSum.const_smul

theorem Summable.const_smul (b : γ) (hf : Summable f) : Summable fun i => b • f i :=
  (hf.hasSum.const_smul _).summable
#align summable.const_smul Summable.const_smul

theorem tsum_const_smul [T2Space α] (b : γ) (hf : Summable f) : ∑' i, b • f i = b • ∑' i, f i :=
  (hf.hasSum.const_smul _).tsum_eq
#align tsum_const_smul tsum_const_smul

end ConstSmul

/-! ### Product and pi types -/


section Prod

variable [AddCommMonoid α] [TopologicalSpace α] [AddCommMonoid γ] [TopologicalSpace γ]

theorem HasSum.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ := by
  simp [HasSum, ← prod_mk_sum, Filter.Tendsto.prod_mk_nhds hf hg]
  -- 🎉 no goals
#align has_sum.prod_mk HasSum.prod_mk

end Prod

section Pi

variable {ι : Type*} {π : α → Type*} [∀ x, AddCommMonoid (π x)] [∀ x, TopologicalSpace (π x)]

theorem Pi.hasSum {f : ι → ∀ x, π x} {g : ∀ x, π x} :
    HasSum f g ↔ ∀ x, HasSum (fun i => f i x) (g x) := by
  simp only [HasSum, tendsto_pi_nhds, sum_apply]
  -- 🎉 no goals
#align pi.has_sum Pi.hasSum

theorem Pi.summable {f : ι → ∀ x, π x} : Summable f ↔ ∀ x, Summable fun i => f i x := by
  simp only [Summable, Pi.hasSum, skolem]
  -- 🎉 no goals
#align pi.summable Pi.summable

theorem tsum_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Summable f) :
    (∑' i, f i) x = ∑' i, f i x :=
  (Pi.hasSum.mp hf.hasSum x).tsum_eq.symm
#align tsum_apply tsum_apply

end Pi

/-! ### Multiplicative opposite -/


section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α} {a : α}

theorem HasSum.op (hf : HasSum f a) : HasSum (fun a => op (f a)) (op a) :=
  (hf.map (@opAddEquiv α _) continuous_op : _)
#align has_sum.op HasSum.op

theorem Summable.op (hf : Summable f) : Summable (op ∘ f) :=
  hf.hasSum.op.summable
#align summable.op Summable.op

theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a) :
    HasSum (fun a => unop (f a)) (unop a) :=
  (hf.map (@opAddEquiv α _).symm continuous_unop : _)
#align has_sum.unop HasSum.unop

theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f) : Summable (unop ∘ f) :=
  hf.hasSum.unop.summable
#align summable.unop Summable.unop

@[simp]
theorem hasSum_op : HasSum (fun a => op (f a)) (op a) ↔ HasSum f a :=
  ⟨HasSum.unop, HasSum.op⟩
#align has_sum_op hasSum_op

@[simp]
theorem hasSum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a => unop (f a)) (unop a) ↔ HasSum f a :=
  ⟨HasSum.op, HasSum.unop⟩
#align has_sum_unop hasSum_unop

@[simp]
theorem summable_op : (Summable fun a => op (f a)) ↔ Summable f :=
  ⟨Summable.unop, Summable.op⟩
#align summable_op summable_op

-- Porting note: This theorem causes a loop easily in Lean 4, so the priority should be `low`.
@[simp low]
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable fun a => unop (f a)) ↔ Summable f :=
  ⟨Summable.op, Summable.unop⟩
#align summable_unop summable_unop

variable [T2Space α]

theorem tsum_op : ∑' x, MulOpposite.op (f x) = MulOpposite.op (∑' x, f x) := by
  by_cases h : Summable f
  -- ⊢ ∑' (x : β), op (f x) = op (∑' (x : β), f x)
  · exact h.hasSum.op.tsum_eq
    -- 🎉 no goals
  · have ho := summable_op.not.mpr h
    -- ⊢ ∑' (x : β), op (f x) = op (∑' (x : β), f x)
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, MulOpposite.op_zero]
    -- 🎉 no goals
#align tsum_op tsum_op

theorem tsum_unop {f : β → αᵐᵒᵖ} : ∑' x, MulOpposite.unop (f x) = MulOpposite.unop (∑' x, f x) :=
  MulOpposite.op_injective tsum_op.symm
#align tsum_unop tsum_unop

end MulOpposite

/-! ### Interaction with the star -/


section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

theorem HasSum.star (h : HasSum f a) : HasSum (fun b => star (f b)) (star a) := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star
  -- 🎉 no goals
#align has_sum.star HasSum.star

theorem Summable.star (hf : Summable f) : Summable fun b => star (f b) :=
  hf.hasSum.star.summable
#align summable.star Summable.star

theorem Summable.ofStar (hf : Summable fun b => Star.star (f b)) : Summable f := by
  simpa only [star_star] using hf.star
  -- 🎉 no goals
#align summable.of_star Summable.ofStar

@[simp]
theorem summable_star_iff : (Summable fun b => star (f b)) ↔ Summable f :=
  ⟨Summable.ofStar, Summable.star⟩
#align summable_star_iff summable_star_iff

@[simp]
theorem summable_star_iff' : Summable (star f) ↔ Summable f :=
  summable_star_iff
#align summable_star_iff' summable_star_iff'

variable [T2Space α]

theorem tsum_star : star (∑' b, f b) = ∑' b, star (f b) := by
  by_cases hf : Summable f
  -- ⊢ star (∑' (b : β), f b) = ∑' (b : β), star (f b)
  · exact hf.hasSum.star.tsum_eq.symm
    -- 🎉 no goals
  · rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.ofStar hf),
      star_zero]
#align tsum_star tsum_star

end ContinuousStar
