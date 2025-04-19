import Mathlib

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*}

section HasProdUniformlyOn

variable [CommMonoid α] (f : ι → β → α) (g : β → α) (s : Set β)

@[simp]
lemma ofFun_prod (i : Finset ι) :
    ∏ b ∈ i, (UniformOnFun.ofFun {s}) (f b) = (UniformOnFun.ofFun {s}) (∏ b ∈ i, f b) := rfl

variable [ UniformSpace α]


@[to_additive]
def HasProdUniformlyOn : Prop :=
  HasProd (fun i ↦ UniformOnFun.ofFun {s} (f i)) (UniformOnFun.ofFun {s} g)

/-- `MultipliableUniformlyOn f` means that `f` converges uniformly on `s` to some infinite product.
Use `tprodUniformlyOn` to get the value. -/
@[to_additive "`SummableUniformlyOn f` means that `f` converges uniformly on `s` to some
infinite product. Use `tsumUniformlyOn` to get the value."]
def MultipliableUniformlyOn : Prop :=
  ∃ g, HasProdUniformlyOn f g s

open scoped Classical in
/-- `∏ᵘ i, f i` is the product of `f` if it exists and is unconditionally uniformly convergent on
a set `s`, or 1 otherwise. -/
@[to_additive "`∑ᵘ i, f i` is the sum of `f` if it exists and is unconditionally uniformly
convergent on a set `s`, or 0 otherwise."]
noncomputable irreducible_def tprodUniformlyOn :=
  if h : MultipliableUniformlyOn f s then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the multiplicative support of `f` is finite, we make the most reasonable choice to use the
  product over the multiplicative support. Otherwise, we choose arbitrarily an `a` satisfying
  `HasProdUniformlyOn f g s`. -/
    if (mulSupport f).Finite then finprod f
    else h.choose
  else 1

-- see Note [operator precedence of big operators]
@[inherit_doc tprodUniformlyOn]
notation3 "∏ᵘ["s"] "(...)", "r:67:(scoped f => tprodUniformlyOn f s) => r
@[inherit_doc tsumUniformlyOn]
notation3 "∑ᵘ["s"] "(...)", "r:67:(scoped f => tsumUniformlyOn f s) => r

@[to_additive]
theorem HasProdUniformlyOn.multipliable (h : HasProdUniformlyOn f g s) :
  Multipliable (fun i ↦ UniformOnFun.ofFun {s} (f i)) :=
  ⟨(UniformOnFun.ofFun {s} g), h⟩

@[to_additive]
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g s) :
  MultipliableUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
theorem tprod_eq_one_of_not_multipliable2 (h : ¬MultipliableUniformlyOn f s) :
    ∏ᵘ[s] b, f b = 1 := by
  simp [tprodUniformlyOn_def, h]

--check this a reasonable defn
@[to_additive]
lemma HasProdUniformlyOn_iff_TendstoUniformlyOn {f : ι → β → α} {g : β → α} {s : Set β} :
    HasProdUniformlyOn f g s ↔
    TendstoUniformlyOn (fun (s : Finset ι) b ↦ ∏ i ∈ s, f i b) g atTop s := by
  rw [HasProdUniformlyOn, HasProd] at *
  have := UniformOnFun.tendsto_iff_tendstoUniformlyOn
    (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {s}) (f b)))
    (f:= (UniformOnFun.ofFun {s} g)) (p := atTop)
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, forall_eq] at this
  convert this
  next i hi =>
  simp

variable { F : Type*} [NormedCommGroup F] [CompleteSpace F] {u : α → ℝ}

open Metric

variable {a a₁ a₂ : ℝ} {ι : Type*}


/- theorem exists_le_hasProd_of_le {f g : β → ℝ} {r : ℝ} (hgf : ∀ b, g b ≤ f b) (hfr : HasProd f r) :
    ∃ p ≤ r, HasProd g p := by
  have : (∏' b, (g b : ℝ)) ≤ r := by
    refine hasProd_le hgf  --ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)

    --exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
  ⟨p, hpr, ENNReal.hasSum_coe.1 <| Eq ▸ ENNReal.summable.hasSum⟩
  sorry -/


theorem Multipliable.of_nonneg_of_le {f g : β → F} (hgf : ∀ b, ‖g b‖ ≤ ‖f b‖ )
    (hf : Multipliable f) : Multipliable g := by

  obtain ⟨sf, hf⟩ := hf
  simp_rw [Multipliable, HasProd] at *
  use ∏' i, g i
  rw [@tendsto_iff_norm_div_tendsto_zero] at *
  apply Asymptotics.IsLittleO.trans_tendsto _ hf

  sorry

theorem tendstoUniformlyOn_tsum_new {f : α → β → F} (hu : Multipliable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) :
    HasProdUniformlyOn f (fun x => ∏' n, f n x) s := by
  rw [HasProdUniformlyOn_iff_TendstoUniformlyOn]
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have A : Multipliable fun n => ‖f n x‖ :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm, ← sum_add_tsum_subtype_compl A.of_norm t, add_sub_cancel_left]
  apply lt_of_le_of_lt _ ht
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  exact tsum_le_tsum (fun n => hfu _ _ hx) (A.subtype _) (hu.subtype _)


end HasProdUniformlyOn
#min_imports
