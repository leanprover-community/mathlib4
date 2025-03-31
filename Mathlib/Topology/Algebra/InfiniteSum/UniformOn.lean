import Mathlib

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*}

section HasProdUniformlyOn

variable [CommMonoid α] [TopologicalSpace α] [ UniformSpace α]
  (f : ι → β → α) (g : β → α) (s : Set β)

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
theorem tprod_eq_one_of_not_multipliable2 (h : ¬MultipliableUniformlyOn f s) : ∏ᵘ[s] b, f b = 1 := by
  simp [tprodUniformlyOn_def, h]

lemma HasProdUniformlyOn.mk {f : ι → β → α} {g : β → α} {s : Set β} {p : Filter (Finset ι)}
    (h : TendstoUniformlyOn (fun (s : Finset ι) b ↦ ∏ i ∈ s, f i b) g atTop s) (hp : HasProd f g) :
    HasProdUniformlyOn f g s := by
  rw [HasProdUniformlyOn, HasProd] at *
  --rw [← UniformFun.toFun_ofFun g, ← UniformFun.toFun_ofFun (fun s ↦ ∏ b ∈ s, f b)] at hp
  have := UniformOnFun.tendsto_iff_tendstoUniformlyOn (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {s}) (f b)))
    (f:= (UniformOnFun.ofFun {s} g)) (p := atTop)
  rw [this]
  simp
  apply h.congr
  filter_upwards with i x hx
  simp


  sorry

end HasProdUniformlyOn
