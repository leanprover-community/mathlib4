/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.basic
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Logic.Encodable.Lattice
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.Algebra.Star

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/


noncomputable section

open Classical Filter Finset Function

open BigOperators Classical Topology

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section HasSum

variable [AddCommMonoid α] [TopologicalSpace α]

/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
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

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def Summable (f : β → α) : Prop :=
  ∃ a, HasSum f a
#align summable Summable

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
irreducible_def tsum {β} (f : β → α) :=
  if h : Summable f then Classical.choose h else 0
#align tsum tsum

-- mathport name: «expr∑' , »
notation3"∑' "-- see Note [operator precedence of big operators]
(...)", "r:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

theorem Summable.hasSum (ha : Summable f) : HasSum f (∑' b, f b) := by
  simp [ha, tsum] <;> exact some_spec ha
#align summable.has_sum Summable.hasSum

theorem HasSum.summable (h : HasSum f a) : Summable f :=
  ⟨a, h⟩
#align has_sum.summable HasSum.summable

/-- Constant zero function has sum `0` -/
theorem hasSum_zero : HasSum (fun b => 0 : β → α) 0 := by simp [HasSum, tendsto_const_nhds]
#align has_sum_zero hasSum_zero

theorem hasSum_empty [IsEmpty β] : HasSum f 0 := by convert hasSum_zero
#align has_sum_empty hasSum_empty

theorem summable_zero : Summable (fun b => 0 : β → α) :=
  hasSum_zero.Summable
#align summable_zero summable_zero

theorem summable_empty [IsEmpty β] : Summable f :=
  hasSum_empty.Summable
#align summable_empty summable_empty

theorem tsum_eq_zero_of_not_summable (h : ¬Summable f) : (∑' b, f b) = 0 := by simp [tsum, h]
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
        ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑ x in u', g x) = ∑ b in v', f b)
    (hf : HasSum g a) : HasSum f a :=
  le_trans (map_atTop_finset_sum_le_of_sum_eq h_eq) hf
#align has_sum.has_sum_of_sum_eq HasSum.hasSum_of_sum_eq

theorem hasSum_iff_hasSum {g : γ → α}
    (h₁ :
      ∀ u : Finset γ,
        ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑ x in u', g x) = ∑ b in v', f b)
    (h₂ :
      ∀ v : Finset β,
        ∃ u : Finset γ, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ (∑ b in v', f b) = ∑ x in u', g x) :
    HasSum f a ↔ HasSum g a :=
  ⟨HasSum.hasSum_of_sum_eq h₂, HasSum.hasSum_of_sum_eq h₁⟩
#align has_sum_iff_has_sum hasSum_iff_hasSum

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » set.range[set.range] g) -/
theorem Function.Injective.hasSum_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 0) : HasSum (f ∘ g) a ↔ HasSum f a := by
  simp only [HasSum, tendsto, hg.map_at_top_finset_sum_eq hf]
#align function.injective.has_sum_iff Function.Injective.hasSum_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » set.range[set.range] g) -/
theorem Function.Injective.summable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 0) : Summable (f ∘ g) ↔ Summable f :=
  exists_congr fun _ => hg.hasSum_iff hf
#align function.injective.summable_iff Function.Injective.summable_iff

theorem hasSum_subtype_iff_of_support_subset {s : Set β} (hf : support f ⊆ s) :
    HasSum (f ∘ coe : s → α) a ↔ HasSum f a :=
  Subtype.coe_injective.hasSum_iff <| by simpa using support_subset_iff'.1 hf
#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subset

theorem hasSum_subtype_iff_indicator {s : Set β} :
    HasSum (f ∘ coe : s → α) a ↔ HasSum (s.indicator f) a := by
  rw [← Set.indicator_range_comp, Subtype.range_coe,
    hasSum_subtype_iff_of_support_subset Set.support_indicator_subset]
#align has_sum_subtype_iff_indicator hasSum_subtype_iff_indicator

theorem summable_subtype_iff_indicator {s : Set β} :
    Summable (f ∘ coe : s → α) ↔ Summable (s.indicator f) :=
  exists_congr fun _ => hasSum_subtype_iff_indicator
#align summable_subtype_iff_indicator summable_subtype_iff_indicator

@[simp]
theorem hasSum_subtype_support : HasSum (f ∘ coe : support f → α) a ↔ HasSum f a :=
  hasSum_subtype_iff_of_support_subset <| Set.Subset.refl _
#align has_sum_subtype_support hasSum_subtype_support

theorem hasSum_fintype [Fintype β] (f : β → α) : HasSum f (∑ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
#align has_sum_fintype hasSum_fintype

protected theorem Finset.hasSum (s : Finset β) (f : β → α) :
    HasSum (f ∘ coe : (↑s : Set β) → α) (∑ b in s, f b) :=
  by
  rw [← sum_attach]
  exact hasSum_fintype _
#align finset.has_sum Finset.hasSum

protected theorem Finset.summable (s : Finset β) (f : β → α) :
    Summable (f ∘ coe : (↑s : Set β) → α) :=
  (s.HasSum f).Summable
#align finset.summable Finset.summable

protected theorem Set.Finite.summable {s : Set β} (hs : s.Finite) (f : β → α) :
    Summable (f ∘ coe : s → α) := by
  convert hs.to_finset.summable f <;> simp only [hs.coe_to_finset]
#align set.finite.summable Set.Finite.summable

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∉ » s) -/
/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
theorem hasSum_sum_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : HasSum f (∑ b in s, f b) :=
  (hasSum_subtype_iff_of_support_subset <| support_subset_iff'.2 hf).1 <| s.HasSum f
#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zero

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∉ » s) -/
theorem summable_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : Summable f :=
  (hasSum_sum_of_ne_finset_zero hf).Summable
#align summable_of_ne_finset_zero summable_of_ne_finset_zero

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b' «expr ≠ » b) -/
theorem hasSum_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) : HasSum f (f b) :=
  suffices HasSum f (∑ b' in {b}, f b') by simpa using this
  hasSum_sum_of_ne_finset_zero <| by simpa [hf]
#align has_sum_single hasSum_single

theorem hasSum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    HasSum (fun b' => if b' = b then a else 0) a :=
  by
  convert hasSum_single b _
  · exact (if_pos rfl).symm
  intro b' hb'
  exact if_neg hb'
#align has_sum_ite_eq hasSum_ite_eq

theorem hasSum_pi_single [DecidableEq β] (b : β) (a : α) : HasSum (Pi.single b a) a :=
  show HasSum (fun x => Pi.single b a x) a by simpa only [Pi.single_apply] using hasSum_ite_eq b a
#align has_sum_pi_single hasSum_pi_single

theorem Equiv.hasSum_iff (e : γ ≃ β) : HasSum (f ∘ e) a ↔ HasSum f a :=
  e.Injective.hasSum_iff <| by simp
#align equiv.has_sum_iff Equiv.hasSum_iff

theorem Function.Injective.hasSum_range_iff {g : γ → β} (hg : Injective g) :
    HasSum (fun x : Set.range g => f x) a ↔ HasSum (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasSum_iff.symm
#align function.injective.has_sum_range_iff Function.Injective.hasSum_range_iff

theorem Equiv.summable_iff (e : γ ≃ β) : Summable (f ∘ e) ↔ Summable f :=
  exists_congr fun a => e.hasSum_iff
#align equiv.summable_iff Equiv.summable_iff

theorem Summable.prod_symm {f : β × γ → α} (hf : Summable f) : Summable fun p : γ × β => f p.symm :=
  (Equiv.prodComm γ β).summable_iff.2 hf
#align summable.prod_symm Summable.prod_symm

theorem Equiv.hasSum_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : HasSum f a ↔ HasSum g a :=
  by
  have : (g ∘ coe) ∘ e = f ∘ coe := funext he
  rw [← hasSum_subtype_support, ← this, e.has_sum_iff, hasSum_subtype_support]
#align equiv.has_sum_iff_of_support Equiv.hasSum_iff_of_support

theorem hasSum_iff_hasSum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasSum f a ↔ HasSum g a :=
  Iff.symm <|
    Equiv.hasSum_iff_of_support
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun x y h => Subtype.ext <| hi <| Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun x hx => Subtype.ext hx⟩)
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
    this ▸ (hg.Tendsto a).comp hf
#align has_sum.map HasSum.map

protected theorem Summable.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : Summable f) {G}
    [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) : Summable (g ∘ f) :=
  (hf.HasSum.map g hg).Summable
#align summable.map Summable.map

protected theorem Summable.map_iff_of_leftInverse [AddCommMonoid γ] [TopologicalSpace γ] {G G'}
    [AddMonoidHomClass G α γ] [AddMonoidHomClass G' γ α] (g : G) (g' : G') (hg : Continuous g)
    (hg' : Continuous g') (hinv : Function.LeftInverse g' g) : Summable (g ∘ f) ↔ Summable f :=
  ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp.assoc, hinv.id] at this, fun h => h.map _ hg⟩
#align summable.map_iff_of_left_inverse Summable.map_iff_of_leftInverse

/-- A special case of `summable.map_iff_of_left_inverse` for convenience -/
protected theorem Summable.map_iff_of_equiv [AddCommMonoid γ] [TopologicalSpace γ] {G}
    [AddEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (AddEquivClass.inv g : γ → α)) : Summable (g ∘ f) ↔ Summable f :=
  Summable.map_iff_of_leftInverse g (g : α ≃+ γ).symm hg hg' (AddEquivClass.left_inv g)
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
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) :=
  by
  refine' ⟨fun h => h.tendsto_sum_nat, fun h => _⟩
  rw [tendsto_nhds_unique h hf.has_sum.tendsto_sum_nat]
  exact hf.has_sum
#align summable.has_sum_iff_tendsto_nat Summable.hasSum_iff_tendsto_nat

theorem Function.Surjective.summable_iff_of_hasSum_iff {α' : Type _} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : Summable f ↔ Summable g :=
  hes.exists.trans <| exists_congr <| @he
#align function.surjective.summable_iff_of_has_sum_iff Function.Surjective.summable_iff_of_hasSum_iff

variable [ContinuousAdd α]

theorem HasSum.add (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun b => f b + g b) (a + b) := by
  simp only [HasSum, sum_add_distrib] <;> exact hf.add hg
#align has_sum.add HasSum.add

theorem Summable.add (hf : Summable f) (hg : Summable g) : Summable fun b => f b + g b :=
  (hf.HasSum.add hg.HasSum).Summable
#align summable.add Summable.add

theorem hasSum_sum {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasSum (f i) (a i)) → HasSum (fun b => ∑ i in s, f i b) (∑ i in s, a i) :=
  Finset.induction_on s (by simp only [hasSum_zero, sum_empty, forall_true_iff])
    (by
      simp (config := { contextual := true }) only [HasSum.add, sum_insert, mem_insert,
        forall_eq_or_imp, forall₂_true_iff, not_false_iff, forall_true_iff])
#align has_sum_sum hasSum_sum

theorem summable_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun b => ∑ i in s, f i b :=
  (hasSum_sum fun i hi => (hf i hi).HasSum).Summable
#align summable_sum summable_sum

theorem HasSum.add_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : t → α) b) : HasSum (f ∘ coe : s ∪ t → α) (a + b) :=
  by
  rw [hasSum_subtype_iff_indicator] at *
  rw [Set.indicator_union_of_disjoint hs]
  exact ha.add hb
#align has_sum.add_disjoint HasSum.add_disjoint

theorem hasSum_sum_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasSum (f ∘ coe : t i → α) (a i)) :
    HasSum (f ∘ coe : (⋃ i ∈ s, t i) → α) (∑ i in s, a i) :=
  by
  simp_rw [hasSum_subtype_iff_indicator] at *
  rw [Set.indicator_finset_bunionᵢ _ _ hs]
  exact hasSum_sum hf
#align has_sum_sum_disjoint hasSum_sum_disjoint

theorem HasSum.add_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : t → α) b) : HasSum f (a + b) := by
  simpa [← hs.compl_eq] using
    (hasSum_subtype_iff_indicator.1 ha).add (hasSum_subtype_iff_indicator.1 hb)
#align has_sum.add_is_compl HasSum.add_isCompl

theorem HasSum.add_compl {s : Set β} (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : sᶜ → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl hb
#align has_sum.add_compl HasSum.add_compl

theorem Summable.add_compl {s : Set β} (hs : Summable (f ∘ coe : s → α))
    (hsc : Summable (f ∘ coe : sᶜ → α)) : Summable f :=
  (hs.HasSum.add_compl hsc.HasSum).Summable
#align summable.add_compl Summable.add_compl

theorem HasSum.compl_add {s : Set β} (ha : HasSum (f ∘ coe : sᶜ → α) a)
    (hb : HasSum (f ∘ coe : s → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl.symm hb
#align has_sum.compl_add HasSum.compl_add

theorem HasSum.even_add_odd {f : ℕ → α} (he : HasSum (fun k => f (2 * k)) a)
    (ho : HasSum (fun k => f (2 * k + 1)) b) : HasSum f (a + b) :=
  by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace he := this.has_sum_range_iff.2 he
  replace ho := ((add_left_injective 1).comp this).hasSum_range_iff.2 ho
  refine' he.add_is_compl _ ho
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
#align has_sum.even_add_odd HasSum.even_add_odd

theorem Summable.compl_add {s : Set β} (hs : Summable (f ∘ coe : sᶜ → α))
    (hsc : Summable (f ∘ coe : s → α)) : Summable f :=
  (hs.HasSum.compl_add hsc.HasSum).Summable
#align summable.compl_add Summable.compl_add

theorem Summable.even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) : Summable f :=
  (he.HasSum.even_add_odd ho.HasSum).Summable
#align summable.even_add_odd Summable.even_add_odd

theorem HasSum.sigma [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasSum f a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) : HasSum g a :=
  by
  refine' (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _
  rintro s ⟨hs, hsc⟩
  rcases mem_at_top_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage, ge_iff_le, Finset.le_iff_subset] at hu
  have :
    tendsto (fun t : Finset (Σb, γ b) => ∑ p in t.filterₓ fun p => p.1 ∈ bs, f p) at_top
      (𝓝 <| ∑ b in bs, g b) :=
    by
    simp only [← sigma_preimage_mk, sum_sigma]
    refine' tendsto_finset_sum _ fun b hb => _
    change
      tendsto (fun t => (fun t => ∑ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) at_top (𝓝 (g b))
    exact tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _)
  refine' hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, fun t ht => hu _ fun x hx => _⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩
#align has_sum.sigma HasSum.sigma

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
theorem HasSum.prod_fiberwise [RegularSpace α] {f : β × γ → α} {g : β → α} {a : α} (ha : HasSum f a)
    (hf : ∀ b, HasSum (fun c => f (b, c)) (g b)) : HasSum g a :=
  HasSum.sigma ((Equiv.sigmaEquivProd β γ).hasSum_iff.2 ha) hf
#align has_sum.prod_fiberwise HasSum.prod_fiberwise

theorem Summable.sigma' [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f)
    (hf : ∀ b, Summable fun c => f ⟨b, c⟩) : Summable fun b => ∑' c, f ⟨b, c⟩ :=
  (ha.HasSum.Sigma fun b => (hf b).HasSum).Summable
#align summable.sigma' Summable.sigma'

theorem HasSum.sigma_of_hasSum [T3Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasSum g a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) (hf' : Summable f) :
    HasSum f a := by simpa [(hf'.has_sum.sigma hf).unique ha] using hf'.has_sum
#align has_sum.sigma_of_has_sum HasSum.sigma_of_hasSum

/-- Version of `has_sum.update` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
theorem HasSum.update' {α β : Type _} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] {f : β → α} {a a' : α} (hf : HasSum f a) (b : β) (x : α)
    (hf' : HasSum (f.update b x) a') : a + x = a' + f b :=
  by
  have : ∀ b', f b' + ite (b' = b) x 0 = f.update b x b' + ite (b' = b) (f b) 0 :=
    by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using add_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.add (hasSum_ite_eq b x)
  simp_rw [this] at h
  exact HasSum.unique h (hf'.add (hasSum_ite_eq b (f b)))
#align has_sum.update' HasSum.update'

/-- Version of `has_sum_ite_sub_has_sum` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
theorem eq_add_of_hasSum_ite {α β : Type _} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] {f : β → α} {a : α} (hf : HasSum f a) (b : β) (a' : α)
    (hf' : HasSum (fun n => ite (n = b) 0 (f n)) a') : a = a' + f b :=
  by
  refine' (add_zero a).symm.trans (hf.update' b 0 _)
  convert hf'
  exact funext (f.update_apply b 0)
#align eq_add_of_has_sum_ite eq_add_of_hasSum_ite

end HasSum

section tsum

variable [AddCommMonoid α] [TopologicalSpace α]

theorem tsum_congr_subtype (f : β → α) {s t : Set β} (h : s = t) :
    (∑' x : s, f x) = ∑' x : t, f x := by rw [h]
#align tsum_congr_subtype tsum_congr_subtype

theorem tsum_zero' (hz : IsClosed ({0} : Set α)) : (∑' b : β, (0 : α)) = 0 := by
  classical
    rw [tsum, dif_pos summable_zero]
    suffices ∀ x : α, HasSum (fun b : β => (0 : α)) x → x = 0 by
      exact this _ (Classical.choose_spec _)
    intro x hx
    contrapose! hx
    simp only [HasSum, tendsto_nhds, Finset.sum_const_zero, Filter.mem_atTop_sets, ge_iff_le,
      Finset.le_eq_subset, Set.mem_preimage, not_forall, not_exists, exists_prop, exists_and_right]
    refine' ⟨{0}ᶜ, ⟨is_open_compl_iff.mpr hz, _⟩, fun y => ⟨⟨y, subset_refl _⟩, _⟩⟩
    · simpa using hx
    · simp
#align tsum_zero' tsum_zero'

@[simp]
theorem tsum_zero [T1Space α] : (∑' b : β, (0 : α)) = 0 :=
  tsum_zero' isClosed_singleton
#align tsum_zero tsum_zero

variable [T2Space α] {f g : β → α} {a a₁ a₂ : α}

theorem HasSum.tsum_eq (ha : HasSum f a) : (∑' b, f b) = a :=
  (Summable.hasSum ⟨a, ha⟩).unique ha
#align has_sum.tsum_eq HasSum.tsum_eq

theorem Summable.hasSum_iff (h : Summable f) : HasSum f a ↔ (∑' b, f b) = a :=
  Iff.intro HasSum.tsum_eq fun eq => Eq ▸ h.HasSum
#align summable.has_sum_iff Summable.hasSum_iff

@[simp]
theorem tsum_empty [IsEmpty β] : (∑' b, f b) = 0 :=
  hasSum_empty.tsum_eq
#align tsum_empty tsum_empty

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∉ » s) -/
theorem tsum_eq_sum {f : β → α} {s : Finset β} (hf : ∀ (b) (_ : b ∉ s), f b = 0) :
    (∑' b, f b) = ∑ b in s, f b :=
  (hasSum_sum_of_ne_finset_zero hf).tsum_eq
#align tsum_eq_sum tsum_eq_sum

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » s) -/
theorem sum_eq_tsum_indicator (f : β → α) (s : Finset β) :
    (∑ x in s, f x) = ∑' x, Set.indicator (↑s) f x :=
  have : ∀ (x) (_ : x ∉ s), Set.indicator (↑s) f x = 0 := fun x hx =>
    Set.indicator_apply_eq_zero.2 fun hx' => (hx <| Finset.mem_coe.1 hx').elim
  (Finset.sum_congr rfl fun x hx =>
        (Set.indicator_apply_eq_self.2 fun hx' => (hx' <| Finset.mem_coe.2 hx).elim).symm).trans
    (tsum_eq_sum this).symm
#align sum_eq_tsum_indicator sum_eq_tsum_indicator

theorem tsum_congr {α β : Type _} [AddCommMonoid α] [TopologicalSpace α] {f g : β → α}
    (hfg : ∀ b, f b = g b) : (∑' b, f b) = ∑' b, g b :=
  congr_arg tsum (funext hfg)
#align tsum_congr tsum_congr

theorem tsum_fintype [Fintype β] (f : β → α) : (∑' b, f b) = ∑ b, f b :=
  (hasSum_fintype f).tsum_eq
#align tsum_fintype tsum_fintype

theorem tsum_bool (f : Bool → α) : (∑' i : Bool, f i) = f False + f True := by
  rw [tsum_fintype, Finset.sum_eq_add] <;> simp
#align tsum_bool tsum_bool

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b' «expr ≠ » b) -/
theorem tsum_eq_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) :
    (∑' b, f b) = f b :=
  (hasSum_single b hf).tsum_eq
#align tsum_eq_single tsum_eq_single

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b' c') -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b' «expr ≠ » b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b' c') -/
theorem tsum_tsum_eq_single (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ (b') (_ : b' ≠ b), f b' c = 0)
    (hfc : ∀ (b' : β) (c' : γ), c' ≠ c → f b' c' = 0) : (∑' (b') (c'), f b' c') = f b c :=
  calc
    (∑' (b') (c'), f b' c') = ∑' b', f b' c := tsum_congr fun b' => tsum_eq_single _ (hfc b')
    _ = f b c := tsum_eq_single _ hfb
    
#align tsum_tsum_eq_single tsum_tsum_eq_single

@[simp]
theorem tsum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    (∑' b', if b' = b then a else 0) = a :=
  (hasSum_ite_eq b a).tsum_eq
#align tsum_ite_eq tsum_ite_eq

@[simp]
theorem tsum_pi_single [DecidableEq β] (b : β) (a : α) : (∑' b', Pi.single b a b') = a :=
  (hasSum_pi_single b a).tsum_eq
#align tsum_pi_single tsum_pi_single

theorem tsum_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    (∑' b : β, if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' b : β, x b h := by
  by_cases hP : P <;> simp [hP]
#align tsum_dite_right tsum_dite_right

theorem tsum_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    (∑' b : β, if h : P then x b h else 0) = if h : P then ∑' b : β, x b h else 0 := by
  by_cases hP : P <;> simp [hP]
#align tsum_dite_left tsum_dite_left

theorem Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum {α' : Type _} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h0 : e 0 = 0) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : (∑' b, f b) = e (∑' c, g c) :=
  by_cases (fun this : Summable g => (h.mpr this.HasSum).tsum_eq) fun hg : ¬Summable g =>
    by
    have hf : ¬Summable f := mt (hes.summable_iff_of_hasSum_iff @h).1 hg
    simp [tsum, hf, hg, h0]
#align function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum

theorem tsum_eq_tsum_of_hasSum_iff_hasSum {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasSum f a ↔ HasSum g a) : (∑' b, f b) = ∑' c, g c :=
  surjective_id.tsum_eq_tsum_of_hasSum_iff_hasSum rfl @h
#align tsum_eq_tsum_of_has_sum_iff_has_sum tsum_eq_tsum_of_hasSum_iff_hasSum

theorem Equiv.tsum_eq (j : γ ≃ β) (f : β → α) : (∑' c, f (j c)) = ∑' b, f b :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun a => j.hasSum_iff
#align equiv.tsum_eq Equiv.tsum_eq

theorem Equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x, g (e x) = f x) : (∑' x, f x) = ∑' y, g y :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => e.hasSum_iff_of_support he
#align equiv.tsum_eq_tsum_of_support Equiv.tsum_eq_tsum_of_support

theorem tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : (∑' x, f x) = ∑' y, g y :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => hasSum_iff_hasSum_of_ne_zero_bij i hi hf hfg
#align tsum_eq_tsum_of_ne_zero_bij tsum_eq_tsum_of_ne_zero_bij

/-! ### `tsum` on subsets -/


@[simp]
theorem Finset.tsum_subtype (s : Finset β) (f : β → α) :
    (∑' x : { x // x ∈ s }, f x) = ∑ x in s, f x :=
  (s.HasSum f).tsum_eq
#align finset.tsum_subtype Finset.tsum_subtype

@[simp]
theorem Finset.tsum_subtype' (s : Finset β) (f : β → α) :
    (∑' x : (s : Set β), f x) = ∑ x in s, f x :=
  s.tsum_subtype f
#align finset.tsum_subtype' Finset.tsum_subtype'

theorem tsum_subtype (s : Set β) (f : β → α) : (∑' x : s, f x) = ∑' x, s.indicator f x :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => hasSum_subtype_iff_indicator
#align tsum_subtype tsum_subtype

theorem tsum_subtype_eq_of_support_subset {f : β → α} {s : Set β} (hs : support f ⊆ s) :
    (∑' x : s, f x) = ∑' x, f x :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun x => hasSum_subtype_iff_of_support_subset hs
#align tsum_subtype_eq_of_support_subset tsum_subtype_eq_of_support_subset

@[simp]
theorem tsum_univ (f : β → α) : (∑' x : (Set.univ : Set β), f x) = ∑' x, f x :=
  tsum_subtype_eq_of_support_subset <| Set.subset_univ _
#align tsum_univ tsum_univ

@[simp]
theorem tsum_singleton (b : β) (f : β → α) : (∑' x : ({b} : Set β), f x) = f b :=
  by
  rw [tsum_subtype, tsum_eq_single b]
  · simp
  · intro b' hb'
    rw [Set.indicator_of_not_mem]
    rwa [Set.mem_singleton_iff]
  · infer_instance
#align tsum_singleton tsum_singleton

theorem tsum_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    (∑' x : g '' s, f x) = ∑' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tsum_eq fun x => f x).symm
#align tsum_image tsum_image

theorem tsum_range {g : γ → β} (f : β → α) (hg : Injective g) :
    (∑' x : Set.range g, f x) = ∑' x, f (g x) := by
  rw [← Set.image_univ, tsum_image f (hg.inj_on _), tsum_univ (f ∘ g)]
#align tsum_range tsum_range

section ContinuousAdd

variable [ContinuousAdd α]

theorem tsum_add (hf : Summable f) (hg : Summable g) :
    (∑' b, f b + g b) = (∑' b, f b) + ∑' b, g b :=
  (hf.HasSum.add hg.HasSum).tsum_eq
#align tsum_add tsum_add

theorem tsum_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' b, ∑ i in s, f i b) = ∑ i in s, ∑' b, f i b :=
  (hasSum_sum fun i hi => (hf i hi).HasSum).tsum_eq
#align tsum_sum tsum_sum

/-- Version of `tsum_eq_add_tsum_ite` for `add_comm_monoid` rather than `add_comm_group`.
Requires a different convergence assumption involving `function.update`. -/
theorem tsum_eq_add_tsum_ite' {f : β → α} (b : β) (hf : Summable (f.update b 0)) :
    (∑' x, f x) = f b + ∑' x, ite (x = b) 0 (f x) :=
  calc
    (∑' x, f x) = ∑' x, ite (x = b) (f x) 0 + f.update b 0 x :=
      tsum_congr fun n => by split_ifs <;> simp [Function.update_apply, h]
    _ = (∑' x, ite (x = b) (f x) 0) + ∑' x, f.update b 0 x :=
      tsum_add ⟨ite (b = b) (f b) 0, hasSum_single b fun b hb => if_neg hb⟩ hf
    _ = ite (b = b) (f b) 0 + ∑' x, f.update b 0 x :=
      by
      congr
      exact tsum_eq_single b fun b' hb' => if_neg hb'
    _ = f b + ∑' x, ite (x = b) 0 (f x) := by
      simp only [Function.update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]
    
#align tsum_eq_add_tsum_ite' tsum_eq_add_tsum_ite'

variable [AddCommMonoid δ] [TopologicalSpace δ] [T3Space δ] [ContinuousAdd δ]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_sigma' {γ : β → Type _} {f : (Σb : β, γ b) → δ} (h₁ : ∀ b, Summable fun c => f ⟨b, c⟩)
    (h₂ : Summable f) : (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  (h₂.HasSum.Sigma fun b => (h₁ b).HasSum).tsum_eq.symm
#align tsum_sigma' tsum_sigma'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_prod' {f : β × γ → δ} (h : Summable f) (h₁ : ∀ b, Summable fun c => f (b, c)) :
    (∑' p, f p) = ∑' (b) (c), f (b, c) :=
  (h.HasSum.prod_fiberwise fun b => (h₁ b).HasSum).tsum_eq.symm
#align tsum_prod' tsum_prod'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (c b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_comm' {f : β → γ → δ} (h : Summable (Function.uncurry f)) (h₁ : ∀ b, Summable (f b))
    (h₂ : ∀ c, Summable fun b => f b c) : (∑' (c) (b), f b c) = ∑' (b) (c), f b c :=
  by
  erw [← tsum_prod' h h₁, ← tsum_prod' h.prod_symm h₂, ← (Equiv.prodComm γ β).tsum_eq (uncurry f)]
  rfl
#align tsum_comm' tsum_comm'

end ContinuousAdd

open Encodable

section Encodable

variable [Encodable γ]

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supᵢ_decode₂ [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (s : γ → β) :
    (∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b)) = ∑' b : γ, m (s b) :=
  by
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).isSome :=
    by
    intro n h
    cases' decode₂ γ n with b
    · refine' (h <| by simp [m0]).elim
    · exact rfl
  symm
  refine' tsum_eq_tsum_of_ne_zero_bij (fun a => Option.get (H a.1 a.2)) _ _ _
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    have := mem_decode₂.1 (Option.get_mem (H n hn))
    rwa [← e, mem_decode₂.1 (Option.get_mem (H m hm))] at this
  · intro b h
    refine' ⟨⟨encode b, _⟩, _⟩
    · simp only [mem_support, encodek₂] at h⊢
      convert h
      simp [Set.ext_iff, encodek₂]
    · exact Option.get_of_mem _ (encodek₂ _)
  · rintro ⟨n, h⟩
    dsimp only [Subtype.coe_mk]
    trans
    swap
    rw [show decode₂ γ n = _ from Option.get_mem (H n h)]
    congr
    simp [ext_iff, -Option.some_get]
#align tsum_supr_decode₂ tsum_supᵢ_decode₂

/-- `tsum_supr_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_unionᵢ_decode₂ (m : Set β → α) (m0 : m ∅ = 0) (s : γ → Set β) :
    (∑' i, m (⋃ b ∈ decode₂ γ i, s b)) = ∑' b, m (s b) :=
  tsum_supᵢ_decode₂ m m0 s
#align tsum_Union_decode₂ tsum_unionᵢ_decode₂

end Encodable

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/


section Countable

variable [Countable γ]

/-- If a function is countably sub-additive then it is sub-additive on countable types -/
theorem rel_supᵢ_tsum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : γ → β) :
    R (m (⨆ b : γ, s b)) (∑' b : γ, m (s b)) :=
  by
  cases nonempty_encodable γ
  rw [← supr_decode₂, ← tsum_supᵢ_decode₂ _ m0 s]
  exact m_supr _
#align rel_supr_tsum rel_supᵢ_tsum

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supᵢ_sum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : δ → β) (t : Finset δ) :
    R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) :=
  by
  rw [supᵢ_subtype', ← Finset.tsum_subtype]
  exact rel_supᵢ_tsum m m0 R m_supr _
#align rel_supr_sum rel_supᵢ_sum

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s₁ s₂ : β) :
    R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) :=
  by
  convert rel_supᵢ_tsum m m0 R m_supr fun b => cond b s₁ s₂
  · simp only [supᵢ_bool_eq, cond]
  · rw [tsum_fintype, Fintype.sum_bool, cond, cond]
#align rel_sup_add rel_sup_add

end Countable

variable [ContinuousAdd α]

theorem tsum_add_tsum_compl {s : Set β} (hs : Summable (f ∘ coe : s → α))
    (hsc : Summable (f ∘ coe : sᶜ → α)) : ((∑' x : s, f x) + ∑' x : sᶜ, f x) = ∑' x, f x :=
  (hs.HasSum.add_compl hsc.HasSum).tsum_eq.symm
#align tsum_add_tsum_compl tsum_add_tsum_compl

theorem tsum_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ coe : s → α))
    (ht : Summable (f ∘ coe : t → α)) : (∑' x : s ∪ t, f x) = (∑' x : s, f x) + ∑' x : t, f x :=
  (hs.HasSum.add_disjoint hd ht.HasSum).tsum_eq
#align tsum_union_disjoint tsum_union_disjoint

theorem tsum_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Summable (f ∘ coe : t i → α)) :
    (∑' x : ⋃ i ∈ s, t i, f x) = ∑ i in s, ∑' x : t i, f x :=
  (hasSum_sum_disjoint _ hd fun i hi => (hf i hi).HasSum).tsum_eq
#align tsum_finset_bUnion_disjoint tsum_finset_bUnion_disjoint

theorem tsum_even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) :
    ((∑' k, f (2 * k)) + ∑' k, f (2 * k + 1)) = ∑' k, f k :=
  (he.HasSum.even_add_odd ho.HasSum).tsum_eq.symm
#align tsum_even_add_odd tsum_even_add_odd

end tsum

section TopologicalGroup

variable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]

variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
theorem HasSum.neg (h : HasSum f a) : HasSum (fun b => -f b) (-a) := by
  simpa only using h.map (-AddMonoidHom.id α) continuous_neg
#align has_sum.neg HasSum.neg

theorem Summable.neg (hf : Summable f) : Summable fun b => -f b :=
  hf.HasSum.neg.Summable
#align summable.neg Summable.neg

theorem Summable.of_neg (hf : Summable fun b => -f b) : Summable f := by
  simpa only [neg_neg] using hf.neg
#align summable.of_neg Summable.of_neg

theorem summable_neg_iff : (Summable fun b => -f b) ↔ Summable f :=
  ⟨Summable.of_neg, Summable.neg⟩
#align summable_neg_iff summable_neg_iff

theorem HasSum.sub (hf : HasSum f a₁) (hg : HasSum g a₂) : HasSum (fun b => f b - g b) (a₁ - a₂) :=
  by
  simp only [sub_eq_add_neg]
  exact hf.add hg.neg
#align has_sum.sub HasSum.sub

theorem Summable.sub (hf : Summable f) (hg : Summable g) : Summable fun b => f b - g b :=
  (hf.HasSum.sub hg.HasSum).Summable
#align summable.sub Summable.sub

theorem Summable.trans_sub (hg : Summable g) (hfg : Summable fun b => f b - g b) : Summable f := by
  simpa only [sub_add_cancel] using hfg.add hg
#align summable.trans_sub Summable.trans_sub

theorem summable_iff_of_summable_sub (hfg : Summable fun b => f b - g b) :
    Summable f ↔ Summable g :=
  ⟨fun hf => hf.trans_sub <| by simpa only [neg_sub] using hfg.neg, fun hg => hg.trans_sub hfg⟩
#align summable_iff_of_summable_sub summable_iff_of_summable_sub

theorem HasSum.update (hf : HasSum f a₁) (b : β) [DecidableEq β] (a : α) :
    HasSum (update f b a) (a - f b + a₁) :=
  by
  convert (hasSum_ite_eq b _).add hf
  ext b'
  by_cases h : b' = b
  · rw [h, update_same]
    simp only [eq_self_iff_true, if_true, sub_add_cancel]
  simp only [h, update_noteq, if_false, Ne.def, zero_add, not_false_iff]
#align has_sum.update HasSum.update

theorem Summable.update (hf : Summable f) (b : β) [DecidableEq β] (a : α) :
    Summable (update f b a) :=
  (hf.HasSum.update b a).Summable
#align summable.update Summable.update

theorem HasSum.hasSum_compl_iff {s : Set β} (hf : HasSum (f ∘ coe : s → α) a₁) :
    HasSum (f ∘ coe : sᶜ → α) a₂ ↔ HasSum f (a₁ + a₂) :=
  by
  refine' ⟨fun h => hf.add_compl h, fun h => _⟩
  rw [hasSum_subtype_iff_indicator] at hf⊢
  rw [Set.indicator_compl]
  simpa only [add_sub_cancel'] using h.sub hf
#align has_sum.has_sum_compl_iff HasSum.hasSum_compl_iff

theorem HasSum.hasSum_iff_compl {s : Set β} (hf : HasSum (f ∘ coe : s → α) a₁) :
    HasSum f a₂ ↔ HasSum (f ∘ coe : sᶜ → α) (a₂ - a₁) :=
  Iff.symm <| hf.hasSum_compl_iff.trans <| by rw [add_sub_cancel'_right]
#align has_sum.has_sum_iff_compl HasSum.hasSum_iff_compl

theorem Summable.summable_compl_iff {s : Set β} (hf : Summable (f ∘ coe : s → α)) :
    Summable (f ∘ coe : sᶜ → α) ↔ Summable f :=
  ⟨fun ⟨a, ha⟩ => (hf.HasSum.hasSum_compl_iff.1 ha).Summable, fun ⟨a, ha⟩ =>
    (hf.HasSum.hasSum_iff_compl.1 ha).Summable⟩
#align summable.summable_compl_iff Summable.summable_compl_iff

protected theorem Finset.hasSum_compl_iff (s : Finset β) :
    HasSum (fun x : { x // x ∉ s } => f x) a ↔ HasSum f (a + ∑ i in s, f i) :=
  (s.HasSum f).hasSum_compl_iff.trans <| by rw [add_comm]
#align finset.has_sum_compl_iff Finset.hasSum_compl_iff

protected theorem Finset.hasSum_iff_compl (s : Finset β) :
    HasSum f a ↔ HasSum (fun x : { x // x ∉ s } => f x) (a - ∑ i in s, f i) :=
  (s.HasSum f).hasSum_iff_compl
#align finset.has_sum_iff_compl Finset.hasSum_iff_compl

protected theorem Finset.summable_compl_iff (s : Finset β) :
    (Summable fun x : { x // x ∉ s } => f x) ↔ Summable f :=
  (s.Summable f).summable_compl_iff
#align finset.summable_compl_iff Finset.summable_compl_iff

theorem Set.Finite.summable_compl_iff {s : Set β} (hs : s.Finite) :
    Summable (f ∘ coe : sᶜ → α) ↔ Summable f :=
  (hs.Summable f).summable_compl_iff
#align set.finite.summable_compl_iff Set.Finite.summable_compl_iff

theorem hasSum_ite_sub_hasSum [DecidableEq β] (hf : HasSum f a) (b : β) :
    HasSum (fun n => ite (n = b) 0 (f n)) (a - f b) :=
  by
  convert hf.update b 0 using 1
  · ext n
    rw [Function.update_apply]
  · rw [sub_add_eq_add_sub, zero_add]
#align has_sum_ite_sub_has_sum hasSum_ite_sub_hasSum

section tsum

variable [T2Space α]

theorem tsum_neg : (∑' b, -f b) = -∑' b, f b :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.neg.tsum_eq
  · simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.of_neg hf)]
#align tsum_neg tsum_neg

theorem tsum_sub (hf : Summable f) (hg : Summable g) :
    (∑' b, f b - g b) = (∑' b, f b) - ∑' b, g b :=
  (hf.HasSum.sub hg.HasSum).tsum_eq
#align tsum_sub tsum_sub

theorem sum_add_tsum_compl {s : Finset β} (hf : Summable f) :
    ((∑ x in s, f x) + ∑' x : (↑s : Set β)ᶜ, f x) = ∑' x, f x :=
  ((s.HasSum f).add_compl (s.summable_compl_iff.2 hf).HasSum).tsum_eq.symm
#align sum_add_tsum_compl sum_add_tsum_compl

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
theorem tsum_eq_add_tsum_ite [DecidableEq β] (hf : Summable f) (b : β) :
    (∑' n, f n) = f b + ∑' n, ite (n = b) 0 (f n) :=
  by
  rw [(hasSum_ite_sub_hasSum hf.has_sum b).tsum_eq]
  exact (add_sub_cancel'_right _ _).symm
#align tsum_eq_add_tsum_ite tsum_eq_add_tsum_ite

end tsum

/-!
### Sums on nat

We show the formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in
`sum_add_tsum_nat_add`, as well as several results relating sums on `ℕ` and `ℤ`.
-/


section Nat

theorem hasSum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) :=
  by
  refine' Iff.trans _ (range k).hasSum_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasSum_iff]
  rfl
#align has_sum_nat_add_iff hasSum_nat_add_iff

theorem summable_nat_add_iff {f : ℕ → α} (k : ℕ) : (Summable fun n => f (n + k)) ↔ Summable f :=
  Iff.symm <|
    (Equiv.addRight (∑ i in range k, f i)).Surjective.summable_iff_of_hasSum_iff fun a =>
      (hasSum_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff

theorem hasSum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) (a - ∑ i in range k, f i) ↔ HasSum f a := by
  simp [hasSum_nat_add_iff]
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

theorem sum_add_tsum_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Summable f) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i := by
  simpa only [add_comm] using
    ((hasSum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).HasSum).unique h.has_sum
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

theorem tsum_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Summable f) :
    (∑' b, f b) = f 0 + ∑' b, f (b + 1) := by
  simpa only [sum_range_one] using (sum_add_tsum_nat_add 1 hf).symm
#align tsum_eq_zero_add tsum_eq_zero_add

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add [T2Space α] (f : ℕ → α) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) :=
  by
  by_cases hf : Summable f
  · have h₀ : (fun i => (∑' i, f i) - ∑ j in range i, f j) = fun i => ∑' k : ℕ, f (k + i) :=
      by
      ext1 i
      rw [sub_eq_iff_eq_add, add_comm, sum_add_tsum_nat_add i hf]
    have h₁ : tendsto (fun i : ℕ => ∑' i, f i) at_top (𝓝 (∑' i, f i)) := tendsto_const_nhds
    simpa only [h₀, sub_self] using tendsto.sub h₁ hf.has_sum.tendsto_sum_nat
  · convert tendsto_const_nhds
    ext1 i
    rw [← summable_nat_add_iff i] at hf
    · exact tsum_eq_zero_of_not_summable hf
    · infer_instance
#align tendsto_sum_nat_add tendsto_sum_nat_add

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
theorem HasSum.int_rec {b : α} {f g : ℕ → α} (hf : HasSum f a) (hg : HasSum g b) :
    @HasSum α _ _ _ (@Int.rec (fun _ => α) f g : ℤ → α) (a + b) :=
  by
  -- note this proof works for any two-case inductive
  have h₁ : injective (coe : ℕ → ℤ) := @Int.ofNat.inj
  have h₂ : injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range (coe : ℕ → ℤ)) (Set.range Int.negSucc) :=
    by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) h
      exacts[Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  exact HasSum.add_isCompl this (h₁.has_sum_range_iff.mpr hf) (h₂.has_sum_range_iff.mpr hg)
#align has_sum.int_rec HasSum.int_rec

theorem HasSum.nonneg_add_neg {b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) :=
  by
  simp_rw [← Int.negSucc_coe] at hneg
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl
#align has_sum.nonneg_add_neg HasSum.nonneg_add_neg

theorem HasSum.pos_add_zero_add_neg {b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) :=
    by
    intro g hg
    simpa using (hasSum_nat_add_iff _).mp hg
  (this (fun n => f n) hpos).nonneg_add_neg hneg
#align has_sum.pos_add_zero_add_neg HasSum.pos_add_zero_add_neg

theorem summable_int_of_summable_nat {f : ℤ → α} (hp : Summable fun n : ℕ => f n)
    (hn : Summable fun n : ℕ => f (-n)) : Summable f :=
  (HasSum.nonneg_add_neg hp.HasSum <| Summable.hasSum <| (summable_nat_add_iff 1).mpr hn).Summable
#align summable_int_of_summable_nat summable_int_of_summable_nat

theorem HasSum.sum_nat_of_sum_int {α : Type _} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {a : α} {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ => f n + f (-n)) (a + f 0) :=
  by
  apply (hf.add (hasSum_ite_eq (0 : ℤ) (f 0))).hasSum_of_sum_eq fun u => _
  refine' ⟨u.image Int.natAbs, fun v' hv' => _⟩
  let u1 := v'.image fun x : ℕ => (x : ℤ)
  let u2 := v'.image fun x : ℕ => -(x : ℤ)
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
  calc
    (∑ x in u1 ∪ u2, f x + ite (x = 0) (f 0) 0) = (∑ x in u1 ∪ u2, f x) + ∑ x in u1 ∩ u2, f x :=
      by
      rw [sum_add_distrib]
      congr 1
      refine' (sum_subset_zero_on_sdiff inter_subset_union _ _).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simpa only [mem_sdiff, mem_union, mem_image, neg_eq_zero, or_self_iff, mem_inter,
          and_self_iff, and_not_self_iff] using hx
      · intro x hx
        simp only [mem_inter, mem_image, exists_prop] at hx
        have : x = 0 := by
          apply le_antisymm
          · rcases hx.2 with ⟨a, ha, rfl⟩
            simp only [Right.neg_nonpos_iff, Nat.cast_nonneg]
          · rcases hx.1 with ⟨a, ha, rfl⟩
            simp only [Nat.cast_nonneg]
        simp only [this, eq_self_iff_true, if_true]
    _ = (∑ x in u1, f x) + ∑ x in u2, f x := sum_union_inter
    _ = (∑ b in v', f b) + ∑ b in v', f (-b) := by
      simp only [sum_image, Nat.cast_inj, imp_self, imp_true_iff, neg_inj]
    _ = ∑ b in v', f b + f (-b) := sum_add_distrib.symm
    
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
      ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e :=
  by
  simp only [CauchySeq, cauchy_map_iff, and_iff_right at_top_ne_bot, prod_at_top_at_top_eq,
    uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (· ∘ ·)]
  rw [tendsto_at_top']
  constructor
  · intro h e he
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.sum_union ht.symm, add_sub_cancel'] using h
  · intro h e he
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∑ b in t₂, f b) - ∑ b in t₁, f b) = (∑ b in t₂ \ s, f b) - ∑ b in t₁ \ s, f b := by
      simp only [(Finset.sum_sdiff ht₁).symm, (Finset.sum_sdiff ht₂).symm, add_sub_add_right_eq_sub]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)
#align cauchy_seq_finset_iff_vanishing cauchySeq_finset_iff_vanishing

attribute [local instance] TopologicalAddGroup.t3Space

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero (f : β → α) :
    Tendsto (fun s : Finset β => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) :=
  by
  by_cases H : Summable f
  · intro e he
    rcases exists_mem_nhds_isClosed_subset he with ⟨o, ho, o_closed, oe⟩
    simp only [le_eq_subset, Set.mem_preimage, mem_at_top_sets, Filter.mem_map, ge_iff_le]
    obtain ⟨s, hs⟩ : ∃ s : Finset β, ∀ t : Finset β, Disjoint t s → (∑ b : β in t, f b) ∈ o :=
      cauchySeq_finset_iff_vanishing.1 (tendsto.cauchy_seq H.has_sum) o ho
    refine' ⟨s, fun a sa => oe _⟩
    have A : Summable fun b : { x // x ∉ a } => f b := a.summable_compl_iff.2 H
    apply IsClosed.mem_of_tendsto o_closed A.has_sum (eventually_of_forall fun b => _)
    have : Disjoint (Finset.image (fun i : { x // x ∉ a } => (i : β)) b) s :=
      by
      apply disjoint_left.2 fun i hi his => _
      rcases mem_image.1 hi with ⟨i', hi', rfl⟩
      exact i'.2 (sa his)
    convert hs _ this using 1
    rw [sum_image]
    intro i hi j hj hij
    exact Subtype.ext hij
  · convert tendsto_const_nhds
    ext s
    apply tsum_eq_zero_of_not_summable
    rwa [Finset.summable_compl_iff]
#align tendsto_tsum_compl_at_top_zero tendsto_tsum_compl_atTop_zero

variable [CompleteSpace α]

theorem summable_iff_vanishing :
    Summable f ↔ ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing]
#align summable_iff_vanishing summable_iff_vanishing

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
theorem Summable.summable_of_eq_zero_or_self (hf : Summable f) (h : ∀ b, g b = 0 ∨ g b = f b) :
    Summable g :=
  summable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : (∑ b in t.filterₓ fun b => g b = f b, f b) = ∑ b in t, g b :=
        calc
          (∑ b in t.filterₓ fun b => g b = f b, f b) = ∑ b in t.filterₓ fun b => g b = f b, g b :=
            Finset.sum_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∑ b in t, g b :=
            by
            refine' Finset.sum_subset (Finset.filter_subset _ _) _
            intro b hbt hb
            simp only [(· ∉ ·), Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb
          
      Eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩
#align summable.summable_of_eq_zero_or_self Summable.summable_of_eq_zero_or_self

protected theorem Summable.indicator (hf : Summable f) (s : Set β) : Summable (s.indicator f) :=
  hf.summable_of_eq_zero_or_self <| Set.indicator_eq_zero_or_self _ _
#align summable.indicator Summable.indicator

theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : Injective i) :
    Summable (f ∘ i) :=
  by
  simpa only [Set.indicator_range_comp] using (hi.summable_iff _).2 (hf.indicator (Set.range i))
  exact fun x hx => Set.indicator_of_not_mem hx _
#align summable.comp_injective Summable.comp_injective

theorem Summable.subtype (hf : Summable f) (s : Set β) : Summable (f ∘ coe : s → α) :=
  hf.comp_injective Subtype.coe_injective
#align summable.subtype Summable.subtype

theorem summable_subtype_and_compl {s : Set β} :
    ((Summable fun x : s => f x) ∧ Summable fun x : sᶜ => f x) ↔ Summable f :=
  ⟨and_imp.2 Summable.add_compl, fun h => ⟨h.Subtype s, h.Subtype (sᶜ)⟩⟩
#align summable_subtype_and_compl summable_subtype_and_compl

theorem Summable.sigma_factor {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) (b : β) :
    Summable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective
#align summable.sigma_factor Summable.sigma_factor

theorem Summable.sigma {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    Summable fun b => ∑' c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b
#align summable.sigma Summable.sigma

theorem Summable.prod_factor {f : β × γ → α} (h : Summable f) (b : β) :
    Summable fun c => f (b, c) :=
  h.comp_injective fun c₁ c₂ h => (Prod.ext_iff.1 h).2
#align summable.prod_factor Summable.prod_factor

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_sigma [T1Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_sigma' (fun b => ha.sigma_factor b) ha
#align tsum_sigma tsum_sigma

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_prod [T1Space α] {f : β × γ → α} (h : Summable f) :
    (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_prod' h h.prod_factor
#align tsum_prod tsum_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (c b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_comm [T1Space α] {f : β → γ → α} (h : Summable (Function.uncurry f)) :
    (∑' (c) (b), f b c) = ∑' (b) (c), f b c :=
  tsum_comm' h h.prod_factor h.prod_symm.prod_factor
#align tsum_comm tsum_comm

theorem tsum_subtype_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Set β) :
    ((∑' x : s, f x) + ∑' x : sᶜ, f x) = ∑' x, f x :=
  ((hf.Subtype s).HasSum.add_compl (hf.Subtype { x | x ∉ s }).HasSum).unique hf.HasSum
#align tsum_subtype_add_tsum_subtype_compl tsum_subtype_add_tsum_subtype_compl

theorem sum_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Finset β) :
    ((∑ x in s, f x) + ∑' x : { x // x ∉ s }, f x) = ∑' x, f x :=
  by
  rw [← tsum_subtype_add_tsum_subtype_compl hf s]
  simp only [Finset.tsum_subtype', add_right_inj]
  rfl
#align sum_add_tsum_subtype_compl sum_add_tsum_subtype_compl

end UniformGroup

section TopologicalGroup

variable {G : Type _} [TopologicalSpace G] [AddCommGroup G] [TopologicalAddGroup G] {f : α → G}

theorem Summable.vanishing (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (0 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∑ k in t, f k) ∈ e :=
  by
  letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  letI : UniformAddGroup G := topological_add_commGroup_is_uniform
  rcases hf with ⟨y, hy⟩
  exact cauchySeq_finset_iff_vanishing.1 hy.cauchy_seq e he
#align summable.vanishing Summable.vanishing

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem Summable.tendsto_cofinite_zero (hf : Summable f) : Tendsto f cofinite (𝓝 0) :=
  by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine' s.eventually_cofinite_nmem.mono fun x hx => _
  · simpa using hs {x} (disjoint_singleton_left.2 hx)
#align summable.tendsto_cofinite_zero Summable.tendsto_cofinite_zero

theorem Summable.tendsto_atTop_zero {f : ℕ → G} (hf : Summable f) : Tendsto f atTop (𝓝 0) :=
  by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_zero
#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zero

end TopologicalGroup

section ConstSmul

variable [Monoid γ] [TopologicalSpace α] [AddCommMonoid α] [DistribMulAction γ α]
  [ContinuousConstSMul γ α] {f : β → α}

theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a) : HasSum (fun i => b • f i) (b • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α _) <| continuous_const_smul _
#align has_sum.const_smul HasSum.const_smul

theorem Summable.const_smul (b : γ) (hf : Summable f) : Summable fun i => b • f i :=
  (hf.HasSum.const_smul _).Summable
#align summable.const_smul Summable.const_smul

theorem tsum_const_smul [T2Space α] (b : γ) (hf : Summable f) : (∑' i, b • f i) = b • ∑' i, f i :=
  (hf.HasSum.const_smul _).tsum_eq
#align tsum_const_smul tsum_const_smul

end ConstSmul

/-! ### Product and pi types -/


section Prod

variable [AddCommMonoid α] [TopologicalSpace α] [AddCommMonoid γ] [TopologicalSpace γ]

theorem HasSum.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ := by
  simp [HasSum, ← prod_mk_sum, Filter.Tendsto.prod_mk_nhds hf hg]
#align has_sum.prod_mk HasSum.prod_mk

end Prod

section Pi

variable {ι : Type _} {π : α → Type _} [∀ x, AddCommMonoid (π x)] [∀ x, TopologicalSpace (π x)]

theorem Pi.hasSum {f : ι → ∀ x, π x} {g : ∀ x, π x} :
    HasSum f g ↔ ∀ x, HasSum (fun i => f i x) (g x) := by
  simp only [HasSum, tendsto_pi_nhds, sum_apply]
#align pi.has_sum Pi.hasSum

theorem Pi.summable {f : ι → ∀ x, π x} : Summable f ↔ ∀ x, Summable fun i => f i x := by
  simp only [Summable, Pi.hasSum, skolem]
#align pi.summable Pi.summable

theorem tsum_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Summable f) :
    (∑' i, f i) x = ∑' i, f i x :=
  (Pi.hasSum.mp hf.HasSum x).tsum_eq.symm
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
  hf.HasSum.op.Summable
#align summable.op Summable.op

theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a) :
    HasSum (fun a => unop (f a)) (unop a) :=
  (hf.map (@opAddEquiv α _).symm continuous_unop : _)
#align has_sum.unop HasSum.unop

theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f) : Summable (unop ∘ f) :=
  hf.HasSum.unop.Summable
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

@[simp]
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable fun a => unop (f a)) ↔ Summable f :=
  ⟨Summable.op, Summable.unop⟩
#align summable_unop summable_unop

variable [T2Space α]

theorem tsum_op : (∑' x, MulOpposite.op (f x)) = MulOpposite.op (∑' x, f x) :=
  by
  by_cases h : Summable f
  · exact h.has_sum.op.tsum_eq
  · have ho := summable_op.not.mpr h
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, MulOpposite.op_zero]
#align tsum_op tsum_op

theorem tsum_unop {f : β → αᵐᵒᵖ} : (∑' x, MulOpposite.unop (f x)) = MulOpposite.unop (∑' x, f x) :=
  MulOpposite.op_injective tsum_op.symm
#align tsum_unop tsum_unop

end MulOpposite

/-! ### Interaction with the star -/


section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

theorem HasSum.star (h : HasSum f a) : HasSum (fun b => star (f b)) (star a) := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star
#align has_sum.star HasSum.star

theorem Summable.star (hf : Summable f) : Summable fun b => star (f b) :=
  hf.HasSum.unit.Summable
#align summable.star Summable.star

theorem Summable.of_star (hf : Summable fun b => star (f b)) : Summable f := by
  simpa only [star_star] using hf.star
#align summable.of_star Summable.of_star

@[simp]
theorem summable_star_iff : (Summable fun b => star (f b)) ↔ Summable f :=
  ⟨Summable.of_star, Summable.star⟩
#align summable_star_iff summable_star_iff

@[simp]
theorem summable_star_iff' : Summable (star f) ↔ Summable f :=
  summable_star_iff
#align summable_star_iff' summable_star_iff'

variable [T2Space α]

theorem tsum_star : star (∑' b, f b) = ∑' b, star (f b) :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.star.tsum_eq.symm
  ·
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.of_star hf),
      star_zero]
#align tsum_star tsum_star

end ContinuousStar

