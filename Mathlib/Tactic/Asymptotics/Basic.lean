module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Positivity
public import Mathlib

/-!
# Big O and little o notation
Additional things we need to support:

- Other relations rather than just =, for example ≤, =ᶠ[l], ≪. That is,
  `f x ≤ g x + O(1)`
  `n ! =ᶠ[𝓟 {n | n ≠ 0}] (n + O(1)) * f n` i.e. the equation holds on some subset.
  `f x =ᶠ[atTop] (1 + o(1)) * g n` i.e. `f` and `g` are equivalent
  `f x ≪ g x + O(x)`

- Constants that are allowed to depend on some specific subset of the variables, i.e.
  $O_{A, ε}(f(x))$

- Functions in multiple variables.

- Favoured filters in each variable, so we don't have to repeat the filter for each O.

-/

public section

open Real Topology
open Filter

namespace Asymptotics

attribute [refl] isBigO_refl

variable {α β γ δ E : Type*} [SeminormedAddCommGroup E] (l : Filter α)

def bigO (s : Set (α → E)) : Set (α → E) :=
  { f | ∃ (ι : Type) (_ : Fintype ι) (g : ι → (α → E)),
      (∀ i, g i ∈ s) ∧ f =O[l] fun j ↦ ∑ i, ‖g i j‖ }

attribute [push] Classical.skolem

lemma mem_bigO (f : α → E) (s : Set (α → E)) :
    f ∈ bigO l s ↔ ∃ (ι : Type) (_ : Fintype ι) (g : ι → (α → E)),
      (∀ i, g i ∈ s) ∧ f =O[l] fun j ↦ ∑ i, ‖g i j‖ :=
  .rfl

lemma bigO_subset_bigO (s₁ s₂ : Set (α → E)) (h : s₁ ⊆ s₂) : bigO l s₁ ⊆ bigO l s₂ := by
  unfold bigO
  gcongr

@[gcongr]
lemma mem_bigO_mono (s : Set (α → E)) {f g : α → E} (h : f =O[l] g) :
    g ∈ bigO l s → f ∈ bigO l s := by
  simp only [mem_bigO]
  gcongr
  exact h.trans

lemma mem_bigO_empty {f : α → E} : f ∈ bigO l ∅ ↔ f =O[l] fun _ ↦ (0 : ℝ) := by
  rw [mem_bigO]
  constructor
  · rintro ⟨ι, instι, z, hz, hf⟩
    simp only [Set.mem_empty_iff_false] at hz
    have (i : ι) : z i = 0 := by exfalso; exact hz i
    simpa [this] using hf
  · intro h
    use Empty, inferInstance, fun _ _ ↦ 0, nofun
    simpa

lemma subset_bigO (s : Set (α → E)) : s ⊆ bigO l s := by
  intro f hf
  rw [mem_bigO]
  use Unit, inferInstance
  use fun _ ↦ f, fun _ ↦ hf
  simp
  rfl

@[simp, push]
lemma mem_bigO_singleton (f g : α → E) :
    f ∈ bigO l {g} ↔ f =O[l] g := by
  constructor
  · rw [mem_bigO]
    rintro ⟨ι, instι, z, hz, hf⟩
    refine hf.trans ?_
    apply IsBigO.sum
    rintro i -
    apply IsBigO.norm_left
    simp only [Set.mem_singleton_iff] at hz
    rw [hz]
  · intro h
    grw [h, ← subset_bigO]
    exact Set.mem_singleton _

@[simp]
lemma bigO_singleton_subset_bigO_singleton (f g : α → E) :
    bigO l {f} ⊆ bigO l {g} ↔ f =O[l] g := by
  constructor
  · intro h
    have := @h f
    simpa [mem_bigO_singleton, isBigO_refl, forall_const] using this
  · intro h x
    simp only [mem_bigO_singleton]
    intro h'
    exact h'.trans h

@[simp]
lemma bigO_bigO (s : Set (α → ℝ)) : bigO l (bigO l s) = bigO l s := by
  ext f
  constructor
  · rw [mem_bigO]
    rintro ⟨ι, instι, z, hz, hf⟩
    simp_rw [mem_bigO] at hz
    push ∀ _, _ at hz
    obtain ⟨ι', instι', z', hz', hz⟩ := hz
    rw [mem_bigO]
    use (i : ι) × ι' i, inferInstance
    use fun i ↦ z' i.1 i.2, fun i ↦ hz' i.1 i.2
    grw [hf]
    simp_rw [Fintype.sum_sigma]
    convert IsBigO.sum_congr ?_ using 3
    · symm; exact abs_of_nonneg (by positivity)
    rintro i -
    exact IsBigO.abs_left (hz i)
  · gcongr
    apply subset_bigO

def map (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) : Set (α → γ) :=
  { g | ∃ f₁ ∈ s₁, ∃ f₂ ∈ s₂, g = fun x ↦ f₁ x (f₂ x) }

@[simp, push]
lemma mem_map (g : α → γ) (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) :
    g ∈ map s₁ s₂ ↔ ∃ f₁ ∈ s₁, ∃ f₂ ∈ s₂, g = fun x ↦ f₁ x (f₂ x) := .rfl

@[gcongr]
lemma map_subset_map {s₁ s₁' : Set (α → β → γ)} {s₂ s₂' : Set (α → β)}
    (h₁ : s₁ ⊆ s₁') (h₂ : s₂ ⊆ s₂') : map s₁ s₂ ⊆ map s₁' s₂' := by
  rintro g ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  exact ⟨f₁, h₁ hf₁, f₂, h₂ hf₂, rfl⟩

@[push]
lemma singleton_eq_map_singletons (f₁ : α → β → γ) (f₂ : α → β) :
    {fun x ↦ f₁ x (f₂ x)} = map {f₁}  {f₂} := by
  ext g
  simp

/- Written by Claude -/
@[simp, push]
lemma map_iUnion_left {ι : Sort*} (s : ι → Set (α → β → γ)) (t : Set (α → β)) :
    map (⋃ i, s i) t = ⋃ i, map (s i) t := by
  ext g
  simp only [map, Set.mem_setOf_eq, Set.mem_iUnion]
  grind

/- Written by Claude -/
@[simp, push]
lemma map_iUnion_right {ι : Sort*} (s : Set (α → β → γ)) (t : ι → Set (α → β)) :
    map s (⋃ i, t i) = ⋃ i, map s (t i) := by
  ext g
  simp only [map, Set.mem_setOf_eq, Set.mem_iUnion]
  grind

-- Question: Is this meaningful if we replace {fun x ↦ x} with a different `Set (ℝ → ℝ)`?
-- exp x = 1 + O[𝓝 0](x)
lemma exp_at_one :
    map {fun _ ↦ exp} {fun x ↦ x} ⊆
      map (map {fun _ ↦ HAdd.hAdd} {fun _ ↦ 1}) (bigO (𝓝 0) {fun x ↦ x}) := by
  intro y
  push _ ∈ _
  simp only [exists_eq_left]
  rintro rfl
  use fun x ↦ exp x - 1
  constructor
  · simpa using exp_sub_sum_range_isBigO_pow 1
  · ring_nf

lemma exp_at_one_ :
    map {fun _ ↦ exp} {fun x ↦ x} ⊆
      map (map {fun _ ↦ HAdd.hAdd} {fun _ ↦ 1}) (bigO (𝓝 0) {fun x ↦ x}) := by
  intro y
  push _ ∈ _
  simp only [↓existsAndEq, true_and, and_self]
  rintro rfl
  use fun x ↦ exp x - 1
  constructor
  · simpa using exp_sub_sum_range_isBigO_pow 1
  · ring_nf

lemma exp_at_one' {l : Filter ℝ} {f : ℝ → ℝ} (hf : Filter.Tendsto f l (𝓝 0)) :
    map {fun _ ↦ exp} {f} ⊆ map (map {fun _ ↦ HAdd.hAdd} {fun _ ↦ 1}) (bigO l {f}) := by
  intro y
  push _ ∈ _
  simp only [exists_eq_left]
  rintro rfl
  use fun x ↦ exp (f x) - 1
  refine ⟨?_, by ring_nf⟩
  simpa using (exp_sub_sum_range_isBigO_pow 1).comp_tendsto hf

section comp

-- These are helper lemmas for composing a function on both sides of an equation involving bigO s

@[simp, push]
lemma Set.image_comp_map (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) (f : δ → α) :
    Set.image (· ∘ f) (map s₁ s₂) = map (Set.image (· ∘ f) s₁) (Set.image (· ∘ f) s₂) := by
  ext g
  push _ ∈ _
  simp only [↓existsAndEq, and_true, Function.comp_apply]
  constructor
  · simp only [forall_exists_index, and_imp]
    intro f₁ f₂ hf₁ hf₂ rfl
    grind
  · grind

@[simp]
lemma Set.image_comp_isBigO {l' : Filter γ} {g : α → E} {f : γ → α} (hg : Filter.Tendsto f l' l) :
    (bigO l {g}).image (· ∘ f) ⊆ bigO l' {g ∘ f} :=  by
  intro f₀
  push _ ∈ _
  rintro ⟨w, h, rfl⟩
  apply h.comp_tendsto hg

end comp

-- same as exp_at_one' but deduced directly from exp_at_one
lemma exp_at_one'' {l : Filter α} {f : α → ℝ} (hf : Filter.Tendsto f l (𝓝 0)) :
    map {fun _ ↦ exp} {f} ⊆ map (map {fun _ ↦ HAdd.hAdd} {fun _ ↦ 1}) (bigO l {f}) := by
  have h := exp_at_one
  let : Set (ℝ → ℝ) → Set (α → ℝ) := (Set.image (· ∘ f))
  -- Take `h` and compose on the right with `f`, then push into expressions until you
  -- reach bigO.
  rw [← Set.le_iff_subset] at h
  apply_fun this at h
  · simp only [Set.le_eq_subset, this, Set.image_comp_map, Set.image_singleton] at h
    grw [Set.image_comp_isBigO _ hf] at h
    exact h
  · apply Set.monotone_image

lemma exp_at_one_set {l : Filter ℝ} {s : Set (ℝ → ℝ)}
    (hs : ∀ f ∈ s, Filter.Tendsto f l (𝓝 0)) :
    map {fun _ ↦ exp} s ⊆ map (map {fun _ ↦ HAdd.hAdd} {fun _ ↦ 1}) (bigO l s) := by
  /- Written partly using Claude, but I want to see if we can do this more systematically? -/
  conv_lhs => rw [← Set.biUnion_of_singleton s]
  push map
  simp only [Set.iUnion_subset_iff]
  rintro f hf
  grw [exp_at_one'' (hs _ hf), bigO_subset_bigO]
  simp [hf]

lemma map_eq (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) :
    map s₁ s₂ = ⋃ i₁ ∈ s₁, ⋃ i₂ ∈ s₂, {fun x ↦ i₁ x (i₂ x)} := by
  ext x
  simp [map]

lemma singleton_eq_map_singleton_singleton (f : α → β → γ) (a : α → β) :
    ({fun x ↦ f x (a x)} : Set (α → γ)) = map {f} {a} := by
  simp [map_eq]

-- TODO: preserve binder names
macro "magic_tac" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [map_eq, mem_pure, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left,
    Set.mem_iUnion, exists_prop, Set.iUnion_exists, Set.biUnion_and'] $[$loc]?)


lemma asymp_mul_add {E' : Type*} [NormedCommRing E'] {s₁ s₂ s₃ : Set (α → E')} :
    map (map {fun _ ↦ HMul.hMul} s₁) (map (map {fun _ ↦ HAdd.hAdd} s₂) s₃) ⊆
      map (map {fun _ ↦ HAdd.hAdd} (map (map {fun _ ↦ HMul.hMul} s₁) s₂))
        (map (map {fun _ ↦ HMul.hMul} s₁) s₃) := by
  magic_tac
  simp only [Set.iUnion_subset_iff, Set.singleton_subset_iff, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop]
  intro f₁ hf₁ f₂ hf₂ f₃ hf₃
  use f₁, hf₁, f₂, hf₂, f₁, hf₁, f₃, hf₃
  ring_nf

lemma asymp_add_assoc {E' : Type*} [SeminormedAddCommGroup E'] {s₁ s₂ s₃ : Set (α → E')} :
    map (map {fun _ ↦ HAdd.hAdd} (map (map {fun _ ↦ HAdd.hAdd} s₁) s₂)) s₃ =
      map (map {fun _ ↦ HAdd.hAdd} s₁) (map (map {fun _ ↦ HAdd.hAdd} s₂) s₃) := by
  magic_tac
  abel_nf

lemma asymp_add_mul {E' : Type*} [NormedCommRing E'] {s₁ s₂ s₃ : Set (α → E')} :
    map (map {fun _ ↦ HMul.hMul} (map (map {fun _ ↦ HAdd.hAdd} s₁) s₂)) s₃ ⊆
      map (map {fun _ ↦ HAdd.hAdd} (map (map {fun _ ↦ HMul.hMul} s₁) s₃))
        (map (map {fun _ ↦ HMul.hMul} s₂) s₃) := by
  magic_tac
  simp only [Set.iUnion_subset_iff, Set.singleton_subset_iff, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop]
  intro f₁ hf₁ f₂ hf₂ f₃ hf₃
  use f₁, hf₁, f₃, hf₃, f₂, hf₂, f₃, hf₃
  ext x
  ring

lemma bigO_add_bigO (s₁ s₂ : Set (α → E)) :
    map (map ({fun _ ↦ HAdd.hAdd}) (bigO l s₁)) (bigO l s₂) = bigO l (s₁ ∪ s₂) := by
  magic_tac
  ext f
  push _ ∈ _
  simp_rw [mem_bigO]
  constructor
  · rintro ⟨f₁, ⟨ι₁, instι₁, g₁, hg₁, hf₁⟩, f₂, ⟨ι₂, instι₂, g₂, hg₂, hf₂⟩, rfl⟩
    use ι₁ ⊕ ι₂, inferInstance
    use Sum.rec g₁ g₂, by simp [*]
    simp only [Fintype.sum_sum_type]
    convert IsBigO.add_add ?_ ?_ using 3
    · symm; exact abs_of_nonneg (by positivity)
    · symm; exact abs_of_nonneg (by positivity)
    · exact hf₁
    · exact hf₂
  · rintro ⟨ι, instι, g, hg, hf⟩
    rw [isBigO_iff'] at hf
    obtain ⟨c, hc, hf⟩ := hf
    simp (disch := positivity) only [norm_eq_abs, abs_of_nonneg] at hf
    classical
    let ι₁ : Type := {i // g i ∈ s₁}
    let ι₂ : Type := {i // g i ∉ s₁}
    let g₁ := fun j ↦ ∑ i : ι₁, ‖g i j‖
    let g₂ := fun j ↦ ∑ i : ι₂, ‖g i j‖
    have (j : α) : ∑ i : ι, ‖g i j‖ = g₁ j + g₂ j := by
      symm
      rw [Fintype.sum_subtype_add_sum_subtype (f := (‖g · j‖))]
    simp_rw [this] at hf
    use fun j ↦ if g₁ j < g₂ j then 0 else f j
    constructor; swap
    · use ι₁, inferInstance, fun i ↦ g i, fun ⟨i, hi⟩ ↦ by simpa using hi
      simp_rw [isBigO_iff, norm_eq_abs]
      use c * 2
      filter_upwards [hf] with i hf
      by_cases h : g₁ i < g₂ i <;> simp only [h, ↓reduceIte, norm_zero]
      · positivity
      · grw [hf, le_of_not_gt h, ← two_mul, mul_assoc, ← le_abs_self]
    use fun j ↦ if g₁ j < g₂ j then f j else 0
    constructor; swap
    · use ι₂, inferInstance, fun i ↦ g i, fun ⟨i, hi⟩ ↦ by grind
      simp_rw [isBigO_iff, norm_eq_abs]
      use c * 2
      filter_upwards [hf] with i hf
      by_cases h : g₁ i < g₂ i <;> simp only [h, ↓reduceIte, norm_zero]
      · grw [hf, h, ← two_mul, mul_assoc, ← le_abs_self]
      · positivity
    ext i
    by_cases h : g₁ i < g₂ i <;> simp [h]

section RightSerial

def RightSerial (r : α → β → Prop) (s₁ : Set α) (s₂ : Set β) : Prop :=
  ∀ x₁ ∈ s₁, ∃ x₂ ∈ s₂, r x₁ x₂

notation x " RS[" r "] " y => RightSerial r x y

universe u v w

instance (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [Trans r s t] :
  Trans (RightSerial r) (RightSerial s) (RightSerial t) where
  trans hab hbc := by
    simp only [RightSerial] at hab hbc ⊢
    have := @Trans.trans (r := r) (s := s) (t := t) _ _ _ _
    grind

lemma rightSerial_of_subset {r : α → α → Prop} {a b : Set α} (refl : ∀ x, r x x) (hab : a ⊆ b) :
    a RS[r] b := by
  intro x hx
  exact ⟨x, hab hx, refl x⟩

open Lean Meta
@[gcongr_forward]
public meta def _root_.Mathlib.Tactic.GCongr.exactRSOfSubset :
    Mathlib.Tactic.GCongr.ForwardExt where
  eval h goal := do
    let pf ← mkConstWithFreshMVarLevels ``rightSerial_of_subset
    let (xs, _, _) ← forallMetaTelescope (← inferType pf)
    xs.back!.mvarId!.assignIfDefEq h
    goal.assignIfDefEq (mkAppN pf xs)
    let (_, reflGoal) ← xs[4]!.mvarId!.intro `x
    reflGoal.applyRfl

@[refl]
lemma rightSerial_rfl {r : α → α → Prop} [Std.Refl r] {a : Set α} : a RS[r] a :=
  rightSerial_of_subset refl subset_rfl

@[simp]
lemma rightSerial_eq (a b : Set α) : (a RS[Eq] b) ↔ a ⊆ b := by
  unfold RightSerial
  grind

@[simp, gcongr]
lemma RightSerial.singleton_RS_singleton {r : α → α → Prop} (a : α) (b : α) :
    ({a} RS[r] {b}) ↔ r a b := by
  unfold RightSerial
  simp

/- Written by Claude -/
@[gcongr]
lemma RightSerial.iUnion_RS_iUnion {ι : Sort*} {r : α → β → Prop} {s : ι → Set α} {t : ι → Set β}
    (h : ∀ i, s i RS[r] t i) : (⋃ i, s i) RS[r] (⋃ i, t i) := by
  rintro x ⟨_, ⟨i, rfl⟩, hx⟩
  obtain ⟨y, hy, hxy⟩ := h i x hx
  exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, hxy⟩

class MapClass {α β γ : Type*} (r : (α → γ) → (α → γ) → Prop)
    (r₁ : outParam ((α → β → γ) → (α → β → γ) → Prop))
    (r₂ : outParam ((α → β) → (α → β) → Prop)) where
  imp {f₁ f₂ f₁' f₂'} : r₁ f₁ f₁' → r₂ f₂ f₂' → r (fun x ↦ f₁ x (f₂ x)) (fun x ↦ f₁' x (f₂' x))

@[gcongr]
lemma map_rightSerial_map {s₁ s₁' : Set (α → β → γ)} {s₂ s₂' : Set (α → β)}
    {r r₁ r₂} [MapClass r r₁ r₂] (h₁ : s₁ RS[r₁] s₁') (h₂ : s₂ RS[r₂] s₂') :
    map s₁ s₂ RS[r] map s₁' s₂' := by
  rintro g ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  obtain ⟨f₁', hf₁', hff₁⟩ := h₁ f₁ hf₁
  obtain ⟨f₂', hf₂', hff₂⟩ := h₂ f₂ hf₂
  refine ⟨fun x ↦ f₁' x (f₂' x), ⟨f₁', hf₁', f₂', hf₂', rfl⟩, ?_⟩
  exact MapClass.imp hff₁ hff₂

instance :
    MapClass (α := α) (β := β) (γ := γ) (EventuallyEq l) (EventuallyEq l) (EventuallyEq l) where
  imp h₁ h₂ := by
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    simp [hx₁, hx₂]

instance : MapClass (α := α) (β := β) (γ := γ) Eq Eq Eq where
  imp h₁ h₂ := by simp [h₁, h₂]

@[gcongr]
lemma bigO_subset_bigO' {s₁ s₂ : Set (α → ℝ)} (h : s₁ RS[(· =O[l] ·)] s₂) :
    bigO l s₁ ⊆ bigO l s₂ := by
  nth_rw 2 [← bigO_bigO]
  apply bigO_subset_bigO
  intro f hf
  obtain ⟨g, hg, hf⟩ := h f hf
  grw [hf, ← subset_bigO]
  exact hg

@[gcongr]
lemma RightSerial.bigO_mono {s₁ s₂ : Set (α → ℝ)} (h : s₁ RS[(· =O[l] ·)] s₂) :
    bigO l s₁ RS[Eq] bigO l s₂ := by
  rw [rightSerial_eq]
  exact bigO_subset_bigO' l h

lemma mul_bigO {s₁ s₂ : Set (α → ℝ)} :
    map (map ({fun _ ↦ HMul.hMul}) s₁) (bigO l s₂) ⊆
      bigO l (map (map ({fun _ ↦ HMul.hMul}) s₁) s₂) := by
  magic_tac
  intro x
  push _ ∈ _
  rw [mem_bigO] at *
  rintro ⟨p, hp, f, ⟨ι, instι, g, hg, hf⟩, rfl⟩
  use ι, instι
  use fun i x ↦ p x * g i x
  constructor
  · intro i
    push _ ∈ _
    use p, hp, g i, hg i
  · simp_rw [norm_mul, ← Finset.mul_sum]
    apply IsBigO.mul (IsBigO.norm_right (by rfl)) hf

lemma bigO_mul {s₁ s₂ : Set (α → ℝ)} :
    map (map ({fun _ ↦ HMul.hMul}) (bigO l s₁)) s₂ ⊆
      bigO l (map (map ({fun _ ↦ HMul.hMul}) s₁) s₂) := by
  have := mul_bigO (s₁ := s₂) (s₂ := s₁) (l := l)
  magic_tac at *
  convert this using 1 <;>
  · rw [Set.iUnion₂_comm]
    simp_rw [mul_comm]

lemma bigO_mul_bigO {s₁ s₂ : Set (α → ℝ)} :
  map (map {fun _ ↦ HMul.hMul} (bigO l s₁)) (bigO l s₂) ⊆
    bigO l (map (map {fun _ ↦ HMul.hMul} s₁) s₂) := by
  grw [bigO_mul, mul_bigO, bigO_bigO]

end RightSerial

-- O[l](f x) + O[l](f x) = O[l](f x)
lemma bigO_add_bigO_set (f : Set (α → ℝ)) :
    map (map {fun _ ↦ HAdd.hAdd} (bigO l f)) (bigO l f) = bigO l f := by
  rw [bigO_add_bigO, Set.union_self]

lemma bigO_add_bigO_eq_left (s₁ s₂ : Set (α → ℝ)) (h : bigO l s₂ ⊆ bigO l s₁) :
    map (map {fun _ ↦ HAdd.hAdd} (bigO l s₁)) (bigO l s₂) = bigO l s₁ := by
  apply subset_antisymm
  · grw [h, bigO_add_bigO_set]
  · grw [bigO_add_bigO, ← Set.subset_union_left]

lemma bigO_add_bigO_eq_right (s₁ s₂ : Set (α → ℝ)) (h : bigO l s₁ ⊆ bigO l s₂) :
    map (map {fun _ ↦ HAdd.hAdd} (bigO l s₁)) (bigO l s₂) = bigO l s₂ := by
  apply subset_antisymm
  · grw [h, bigO_add_bigO_set]
  · grw [bigO_add_bigO, ← Set.subset_union_right]


section Meta

open Lean Meta

syntax (name := bigONotation) "O[" term "](" term ")" : term

opaque dummyBigO [SeminormedAddCommGroup E] (l : Filter α) (a : E) : E := a

@[term_elab bigONotation]
meta def elabBigO : Elab.Term.TermElab := fun stx expectedType? ↦ do
  match stx with
  | `(O[$l]($e)) => Elab.Term.elabTerm (← `(dummyBigO $l $e)) expectedType?
  | _ => Elab.throwUnsupportedSyntax

meta partial def mappify (fvar : Expr) (e : Expr) : MetaM Expr := do
  match_expr e with
  | dummyBigO α E instNormE l e' =>
    unless ← isDefEq α (← inferType fvar) do
      throwError
        "Filter `{l}` lives in type `{α}`, but is expected to live in type `{← inferType fvar}"
    return mkApp5 (.const ``bigO [← getDecLevel α, ← getDecLevel E])
      α E instNormE l (← mappify fvar e')
  | _ =>
    if let .app f a := e then
      let fType ← inferType f
      if let .forallE _ _ _ .default := fType then
        let f ← mappify fvar f
        let a ← mappify fvar a
        return ← mkAppM ``map #[f, a]
    let e ← mkLambdaFVars #[fvar] e
    let α ← inferType e
    let setα ← mkAppM ``Set #[α]
    mkAppOptM ``singleton #[α, setα, none, e]

meta partial def unmappify (e : Expr) : OptionT MetaM Expr := do
  match_expr e with
  | map _ _ _ f a =>
    let f ← unmappify f
    let a ← unmappify a
    return f.app a
  | singleton _ _ _ f =>
    if let .lam _ _ b _ := f then
      return b
    failure
  | f@bigO α E instE l a =>
    return mkApp5 (.const ``dummyBigO f.constLevels!) α E instE l (← unmappify a)
  | _ => failure

declare_syntax_cat asymp_rel

syntax term "; " term "; " term : asymp_rel

macro a:term:55 " = " b:term:55 : asymp_rel => `(asymp_rel| $a:term; Eq; $b)
macro a:term:55 " ≤ " b:term:55 : asymp_rel => `(asymp_rel| $a:term; LE.le; $b)
macro a:term:55 " =ᶠ[" l:term "] " b:term:55 : asymp_rel => `(asymp_rel| $a:term; Filter.EventuallyEq $l; $b)
macro a:term:55 " ≤ᶠ[" l:term "] " b:term:55 : asymp_rel => `(asymp_rel| $a:term; Filter.EventuallyLE $l; $b)
macro a:term:55 " =O[" l:term "] " b:term:55 : asymp_rel => `(asymp_rel| $a:term; IsBigO $l; $b)
macro a:term:55 " =o[" l:term "] " b:term:55 : asymp_rel => `(asymp_rel| $a:term; IsLittleO $l; $b)
macro a:term:55 " ~[" l:term "] " b:term:55 : asymp_rel => `(asymp_rel| $a:term; IsEquivalent $l; $b)

syntax (name := asympPercent) "asymp% " ident (" : " term)? " => " asymp_rel : term

@[term_elab asympPercent]
meta def elabAsympPercent : Elab.Term.TermElab := fun stx _ ↦ do
  match stx with
  | `(asymp% $x $[: $t?]? => $e) =>
    match ← Elab.liftMacroM <| expandMacros e with
    | `(asymp_rel| $lhs:term; $r; $rhs) =>
      let fvarType ←
        if let some t := t? then
          Elab.Term.elabType t
        else
          Meta.mkFreshTypeMVar
      let type ← mkFreshTypeMVar
      let fnType := Expr.forallE x.getId fvarType type .default
      let r ← Elab.Term.elabTermEnsuringType r
        (Expr.forallE `a fnType (.forallE `a fnType (.sort 0) .default) .default)
      Meta.withLocalDeclD x.getId fvarType fun fvar ↦ do
        let u ← getDecLevel fnType
        let elabSide (stx : Syntax) : Elab.Term.TermElabM Expr := do
          if let `(_) := stx then
            mkFreshExprMVar (some <| .app (.const ``Set [u]) fnType)
          else
            mappify fvar <| ← Elab.Term.elabTermEnsuringType stx type
        return mkApp5 (.const ``RightSerial [u, u]) fnType fnType r (← elabSide lhs) (← elabSide rhs)
    | _ => Elab.throwUnsupportedSyntax
  | _ => Elab.throwUnsupportedSyntax

open PrettyPrinter Delaborator SubExpr in
@[app_delab RightSerial]
meta def delabAsympPercent : Delab := do
  let_expr RightSerial fnType _ r lhs rhs := ← SubExpr.getExpr | failure
  let .forallE name d _ _ := fnType | failure
  let some lhs ← (unmappify lhs).run | failure
  let some rhs ← (unmappify rhs).run | failure
  let (lhs, rhs) ← withLocalDeclD name d fun fvar ↦ do
    let lhs ← withAppFn <| withAppArg <| delab <| lhs.instantiate1 fvar
    let rhs ← withAppArg <| delab <| rhs.instantiate1 fvar
    return (lhs, rhs)
  let d ← withAppFn <| withAppFn <| withAppFn <| delab d
  let rel ← withAppFn <| withAppFn <| withAppArg do
    match_expr r with
    | Eq _ => `(asymp_rel| $lhs:term = $rhs)
    | LE.le _ _=> `(asymp_rel| $lhs:term ≤ $rhs)
    | Filter.EventuallyEq _ _ l' => `(asymp_rel| $lhs:term =ᶠ[$(← delab l')] $rhs)
    | Filter.EventuallyLE _ _ _ l' => `(asymp_rel| $lhs:term ≤ᶠ[$(← delab l')] $rhs)
    -- | IsBigO _  l' => `(asymp_rel| $lhs:term =O[$l':term] $rhs:term)
    -- | IsLittleO _  l' => `(asymp_rel| $lhs:term =o[$l'] $rhs)
    | IsEquivalent _ _ _ l' => `(asymp_rel| $lhs:term ~[$(← delab l')] $rhs)
    | _ =>`(asymp_rel| $lhs:term; $(← delab r); $rhs)
  `(asymp% $(mkIdent name) : $d => $rel)

@[app_unexpander dummyBigO]
meta def dummyBigOUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $l $a) => `(O[$l]($a))
  | _ => throw ()

end Meta

section StandardAsymptotics

-- Isn't this in Mathlib somewhere?
theorem const_isBigO_log_atTop (c : ℝ) : (fun _ ↦ c) =O[atTop] Real.log := by
  rw [IsBigO_def]
  use 1
  simp only [IsBigOWith_def, norm_eq_abs, one_mul, eventually_atTop, ge_iff_le]
  use exp |c|
  intro x hx
  have := Real.log_le_log (by positivity) hx
  grw [← this, Real.log_exp, abs_abs]
  · apply Real.log_nonneg
    conv_lhs => rw [← Real.exp_zero]
    gcongr
    norm_num

-- There doesn't seem to be anything that quite implies this in mathlib.
-- Should be a statement about x^a =O[atTop] x^b.
theorem Real.inv_isBigO_one_atTop : (fun x : ℝ ↦ x⁻¹) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  rw [IsBigO_def]
  use 1
  simp only [IsBigOWith_def, norm_inv, norm_eq_abs, norm_one, mul_one, eventually_atTop, ge_iff_le]
  use 1
  intro x h
  field_simp
  rw [abs_of_nonneg]
  · exact h
  · linarith

theorem Real.log_add_sub_log_isBigO_inv : (fun x ↦ log (x+1) - log x) =O[atTop] fun x ↦ x⁻¹ := by
  have := Real.tendsto_mul_log_one_add_of_tendsto (g := fun x ↦ x⁻¹) (t := 1) ?A
  case A =>
    apply Tendsto.congr' (f₁ := fun _ ↦ 1)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      field_simp
    · simp
  have := (this.isBigO_one ℝ).mul (isBigO_refl (fun x : ℝ ↦ x⁻¹) _)
  simp only [one_mul] at this
  grw [← this]
  apply EventuallyEq.isBigO
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop 10] with x hx hx'
  field_simp
  rw [log_div]
  · linarith
  · positivity

end StandardAsymptotics


-- see: Real.tendsto_mul_log_one_add_of_tendsto with g x = x⁻¹

lemma Real.log_add_one_isBigO_atTop : asymp% x : ℝ => log (x + 1) = log x + O[atTop](x⁻¹) := by
  magic_tac
  simp only [mem_bigO_singleton, rightSerial_eq, Set.singleton_subset_iff, Set.mem_iUnion,
    Set.mem_singleton_iff, exists_prop]
  use (fun x ↦ log (x + 1) - log x), Real.log_add_sub_log_isBigO_inv
  ring_nf

-- lemma exp_at_one''' {l : Filter α} {f : α → ℝ} (hf : Filter.Tendsto f l (𝓝 0)) :
--     asymp% x : α => exp (f x) = 1 + O[l](f x) := by
--   sorry
--     -- map {fun _ ↦ exp} {f} ⊆ map (map {fun _ ↦ HAdd.hAdd} {fun _ ↦ 1}) (bigO l {f}) := by

/-
  (n+1)^(e^(1/n))
  = (n+1)^(1 + O(1/n)) := _
  = exp ( (log n + O(1/n)) * (1 + O(1/n)) ) := _
  = exp (log n + O(log n/n)) := _
  = n * (1 + O(log n/n)) := _
  = n + O(log n) := _
-/
theorem terry :
      asymp% x : ℝ => (x + 1) ^ (exp x⁻¹) =ᶠ[atTop] x + O[atTop](log x) := by
  calc
    -- asymp% n => (n+1)^(exp(1/n)) =ᶠ[atTop] (n+1)^(1 + O(1/n))
    asymp% x : ℝ => (x + 1) ^ (exp x⁻¹) = (x + 1) ^ (1 + O[atTop](x⁻¹)) := by
      -- Can't use exp_at_one_set'' - {f} doesn't match map {fun _ ↦ Inv.inv} {fun x ↦ x}
      grw [exp_at_one_set]
      -- The state here is ugly; I think it's a consequene of how we chose to state exp_at_one_set
      simp only [mem_map, Set.mem_singleton_iff, exists_eq_left, forall_eq]
      exact tendsto_inv_atTop_zero
    asymp% x : ℝ => _ =ᶠ[atTop] exp (Real.log (x + 1) * (1 + O[atTop](x⁻¹))) := by
      magic_tac
      gcongr with f hf
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [exp_mul, exp_log]
      linarith
    -- (n+1)^(1 + O(1/n)) ⊆ exp ( (log n + O(1/n)) * (1 + O(1/n)) )
    asymp% x : ℝ => _ = exp ((log x + O[atTop](x⁻¹)) * (1 + O[atTop](x⁻¹))) := by
      grw [Real.log_add_one_isBigO_atTop]
    -- exp ( (log n + O(1/n)) * (1 + O(1/n)) ) ⊆ exp (log n + O(log n / n))
    asymp% x : ℝ => _ = exp (log x + O[atTop](log x / x)) := by
      -- Pain point: I have to do more rewriting thatn I'd like, and I had to
      -- manually translate some existing lemmas into the language of asymptotics.
      grw [asymp_mul_add, asymp_add_mul, asymp_add_mul, mul_bigO, bigO_mul_bigO, bigO_mul,
        bigO_add_bigO_eq_left, asymp_add_assoc, bigO_add_bigO_eq_right]
      · magic_tac
        ring_nf
        rfl
      · magic_tac
        simp only [mul_one, bigO_singleton_subset_bigO_singleton]
        have := (const_isBigO_log_atTop 1).mul (isBigO_refl (fun x ↦ x⁻¹) _)
        simpa using this
      · magic_tac
        simp only [bigO_singleton_subset_bigO_singleton]
        exact (Real.inv_isBigO_one_atTop.trans (const_isBigO_log_atTop 1)).mul (isBigO_refl _ _)
    -- exp (log n + O(log n / n)) ⊆ n * (1 + O(log n / n))
    asymp% x : ℝ =>_ =ᶠ[atTop] x * exp O[atTop](log x / x) := by
      magic_tac
      gcongr with f
      filter_upwards [eventually_gt_atTop 0]
      intro x hx
      rw [exp_add, exp_log hx]
    asymp% x : ℝ => _ =  x * (1 + O[atTop](log x / x)) := by
      grw [exp_at_one_set (l := atTop), bigO_bigO]
      · pull singleton
        simp only [mem_bigO_singleton]
        intro f hf
        apply hf.trans_tendsto
        have := tendsto_pow_log_div_mul_add_atTop 1 0 1
        simpa [ne_eq, one_ne_zero, not_false_eq_true, pow_one, one_mul, add_zero,
          forall_const] using this
    asymp% x : ℝ => _ = x + x * O[atTop](log x / x) := by
      magic_tac
      ring_nf
      rfl
    asymp% x : ℝ => _ = x + O[atTop](log x) := by
      grw [mul_bigO]
      gcongr
      simp only [RightSerial, mem_map, Set.mem_singleton_iff, exists_eq_left, forall_eq]
      apply Filter.EventuallyEq.isBigO
      filter_upwards [Filter.eventually_ne_atTop 0]
      intros
      field_simp

#print axioms terry

end Asymptotics
