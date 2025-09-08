/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Topology.PartialHomeomorph

/-!
# Further basic lemmas about asymptotics

-/

open Set Topology Filter NNReal

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}
@[simp]
theorem isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [IsBigOWith_def, eventually_principal]

theorem isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  simp_rw [isBigO_iff, eventually_principal]

@[simp]
theorem isLittleO_principal {s : Set α} : f'' =o[𝓟 s] g' ↔ ∀ x ∈ s, f'' x = 0 := by
  refine ⟨fun h x hx ↦ norm_le_zero_iff.1 ?_, fun h ↦ ?_⟩
  · simp only [isLittleO_iff] at h
    have : Tendsto (fun c : ℝ => c * ‖g' x‖) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left
        inf_le_left
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    apply eventually_nhdsWithin_iff.2 (Eventually.of_forall (fun c hc ↦ ?_))
    exact eventually_principal.1 (h hc) x hx
  · apply (isLittleO_zero g' _).congr' ?_ EventuallyEq.rfl
    exact fun x hx ↦ (h x hx).symm

@[simp]
theorem isBigOWith_top : IsBigOWith c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [IsBigOWith_def, eventually_top]

@[simp]
theorem isBigO_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  simp_rw [isBigO_iff, eventually_top]

@[simp]
theorem isLittleO_top : f'' =o[⊤] g' ↔ ∀ x, f'' x = 0 := by
  simp only [← principal_univ, isLittleO_principal, mem_univ, forall_true_left]

section

variable (F)
variable [One F] [NormOneClass F]

theorem isBigOWith_const_one (c : E) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun _x : α => c) fun _x => (1 : F) := by simp [isBigOWith_iff]

theorem isBigO_const_one (c : E) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => (1 : F) :=
  (isBigOWith_const_one F c l).isBigO

theorem isLittleO_const_iff_isLittleO_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun _x => c) ↔ f =o[l] fun _x => (1 : F) :=
  ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc),
   fun h => h.trans_isBigO <| isBigO_const_const _ hc _⟩

@[simp]
theorem isLittleO_one_iff {f : α → E'''} : f =o[l] (fun _x => 1 : α → F) ↔ Tendsto f l (𝓝 0) := by
  simp only [isLittleO_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]

@[simp]
theorem isBigO_one_iff : f =O[l] (fun _x => 1 : α → F) ↔
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ := by
  simp only [isBigO_iff, norm_one, mul_one, IsBoundedUnder, IsBounded, eventually_map]

alias ⟨_, _root_.Filter.IsBoundedUnder.isBigO_one⟩ := isBigO_one_iff

@[simp]
theorem isLittleO_one_left_iff : (fun _x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun _x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      isLittleO_iff_nat_mul_le_aux <| Or.inl fun _x => by simp only [norm_one, zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm

theorem _root_.Filter.Tendsto.isBigO_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun _x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.isBigO_one F

theorem IsBigO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun _x => 1 : α → F) :=
  hfg.trans <| hg.isBigO_one F

/-- The condition `f = O[𝓝[≠] a] 1` is equivalent to `f = O[𝓝 a] 1`. -/
lemma isBigO_one_nhds_ne_iff [TopologicalSpace α] {a : α} :
    f =O[𝓝[≠] a] (fun _ ↦ 1 : α → F) ↔ f =O[𝓝 a] (fun _ ↦ 1 : α → F) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono nhdsWithin_le_nhds⟩
  simp only [isBigO_one_iff, IsBoundedUnder, IsBounded, eventually_map] at h ⊢
  obtain ⟨c, hc⟩ := h
  use max c ‖f a‖
  filter_upwards [eventually_nhdsWithin_iff.mp hc] with b hb
  rcases eq_or_ne b a with rfl | hb'
  · apply le_max_right
  · exact (hb hb').trans (le_max_left ..)

end

theorem isLittleO_const_iff {c : F''} (hc : c ≠ 0) :
    (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isLittleO_const_iff_isLittleO_one ℝ hc).trans (isLittleO_one_iff _)

theorem isLittleO_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c :=
  (isLittleO_const_iff hc).mpr (continuous_id.tendsto 0)

theorem _root_.Filter.IsBoundedUnder.isBigO_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f))
    {c : F''} (hc : c ≠ 0) : f =O[l] fun _x => c :=
  (h.isBigO_one ℝ).trans (isBigO_const_const _ hc _)

theorem isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun _x => c :=
  h.norm.isBoundedUnder_le.isBigO_const hc

theorem IsBigO.isBoundedUnder_le {c : F} (h : f =O[l] fun _x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩

theorem isBigO_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun _x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩

theorem isBigO_const_iff {c : F''} : (f'' =O[l] fun _x => c) ↔
    (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ := by
  refine ⟨fun h => ⟨fun hc => isBigO_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, ?_⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts [(hcf hc).trans_isBigO (isBigO_zero _ _), hf.isBigO_const hc]

theorem isBigO_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ := by
  simp only [isBigO_iff, IsBoundedUnder, IsBounded, eventually_map]
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff₀ <| norm_pos_iff.2 hx).symm

/-- `(fun x ↦ c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ := by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, ?_⟩
    exact hC.bound.mono fun x => (div_le_iff₀' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine IsBigO.of_bound (‖c‖ / b) (hb.mono fun x hx => ?_)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)

theorem IsBigO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  (isLittleO_one_iff ℝ).1 <| hfg.trans_isLittleO <| (isLittleO_one_iff ℝ).2 hg

theorem IsLittleO.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.isBigO.trans_tendsto hg

lemma isLittleO_id_one [One F''] [NeZero (1 : F'')] : (fun x : E'' => x) =o[𝓝 0] (1 : E'' → F'') :=
  isLittleO_id_const one_ne_zero

theorem continuousAt_iff_isLittleO {α : Type*} {E : Type*} [NormedRing E] [NormOneClass E]
    [TopologicalSpace α] {f : α → E} {x : α} :
    (ContinuousAt f x) ↔ (fun (y : α) ↦ f y - f x) =o[𝓝 x] (fun (_ : α) ↦ (1 : E)) := by
  simp [ContinuousAt, ← tendsto_sub_nhds_zero_iff]

/-! ### Multiplication -/

theorem IsBigO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  obtain ⟨c : ℝ, hc₀ : 0 ≤ c, hc : C ≤ c ^ n⟩ :=
    ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).isBigO

/-! ### Scalar multiplication -/

section SMulConst

variable [Module R E'] [IsBoundedSMul R E']

theorem IsBigOWith.const_smul_self (c' : R) :
    IsBigOWith (‖c'‖) l (fun x => c' • f' x) f' :=
  isBigOWith_of_le' _ fun _ => norm_smul_le _ _

theorem IsBigO.const_smul_self (c' : R) : (fun x => c' • f' x) =O[l] f' :=
  (IsBigOWith.const_smul_self _).isBigO

theorem IsBigOWith.const_smul_left (h : IsBigOWith c l f' g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  .trans (.const_smul_self _) h (norm_nonneg _)

theorem IsBigO.const_smul_left (h : f' =O[l] g) (c : R) : (c • f') =O[l] g :=
  let ⟨_b, hb⟩ := h.isBigOWith
  (hb.const_smul_left _).isBigO

theorem IsLittleO.const_smul_left (h : f' =o[l] g) (c : R) : (c • f') =o[l] g :=
  (IsBigO.const_smul_self _).trans_isLittleO h

variable [Module 𝕜 E'] [NormSMulClass 𝕜 E']

theorem isBigO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_left]
  simp only [norm_smul]
  rw [isBigO_const_mul_left_iff cne0, isBigO_norm_left]

theorem isLittleO_const_smul_left {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c • f' x) =o[l] g ↔ f' =o[l] g := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_left]
  simp only [norm_smul]
  rw [isLittleO_const_mul_left_iff cne0, isLittleO_norm_left]

theorem isBigO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c • f' x) ↔ f =O[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_right]
  simp only [norm_smul]
  rw [isBigO_const_mul_right_iff cne0, isBigO_norm_right]

theorem isLittleO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c • f' x) ↔ f =o[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_right]
  simp only [norm_smul]
  rw [isLittleO_const_mul_right_iff cne0, isLittleO_norm_right]

end SMulConst

section SMul

variable [Module R E'] [IsBoundedSMul R E'] [Module 𝕜' F'] [NormSMulClass 𝕜' F']
variable {k₁ : α → R} {k₂ : α → 𝕜'}

theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
    IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_smul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_smul, mul_mul_mul_comm]

theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  obtain ⟨c₁, h₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, h₂⟩ := h₂.isBigOWith
  exact (h₁.smul h₂).isBigO

theorem IsBigO.smul_isLittleO (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.smul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

theorem IsLittleO.smul_isBigO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).smul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x :=
  h₁.smul_isBigO h₂.isBigO

end SMul

section Prod
variable {ι : Type*}

theorem IsBigO.listProd {L : List ι} {f : ι → α → R} {g : ι → α → 𝕜}
    (hf : ∀ i ∈ L, f i =O[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) =O[l] (fun x ↦ (L.map (g · x)).prod) := by
  induction L with
  | nil => simp [isBoundedUnder_const]
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons] at hf ⊢
    exact hf.1.mul (ihL hf.2)

theorem IsBigO.multisetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Multiset ι} {f : ι → α → R} {g : ι → α → 𝕜} (hf : ∀ i ∈ s, f i =O[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) =O[l] (fun x ↦ (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsBigO.listProd hf

theorem IsBigO.finsetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Finset ι} {f : ι → α → R} {g : ι → α → 𝕜}
    (hf : ∀ i ∈ s, f i =O[l] g i) : (∏ i ∈ s, f i ·) =O[l] (∏ i ∈ s, g i ·) :=
  .multisetProd hf

theorem IsLittleO.listProd {L : List ι} {f : ι → α → R} {g : ι → α → 𝕜}
    (h₁ : ∀ i ∈ L, f i =O[l] g i) (h₂ : ∃ i ∈ L, f i =o[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) =o[l] (fun x ↦ (L.map (g · x)).prod) := by
  induction L with
  | nil => simp at h₂
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons, List.exists_mem_cons_iff]
      at h₁ h₂ ⊢
    cases h₂ with
    | inl hi => exact hi.mul_isBigO <| .listProd h₁.2
    | inr hL => exact h₁.1.mul_isLittleO <| ihL h₁.2 hL

theorem IsLittleO.multisetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Multiset ι} {f : ι → α → R} {g : ι → α → 𝕜} (h₁ : ∀ i ∈ s, f i =O[l] g i)
    (h₂ : ∃ i ∈ s, f i =o[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) =o[l] (fun x ↦ (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsLittleO.listProd h₁ h₂

theorem IsLittleO.finsetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Finset ι} {f : ι → α → R} {g : ι → α → 𝕜} (h₁ : ∀ i ∈ s, f i =O[l] g i)
    (h₂ : ∃ i ∈ s, f i =o[l] g i) : (∏ i ∈ s, f i ·) =o[l] (∏ i ∈ s, g i ·) :=
  .multisetProd h₁ h₂

end Prod

/-! ### Relation between `f = o(g)` and `f / g → 0` -/

theorem IsLittleO.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (isLittleO_one_iff 𝕜).mp <| by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_isBigO (isBigO_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]

theorem IsLittleO.tendsto_inv_smul_nhds_zero [Module 𝕜 E'] [NormSMulClass 𝕜 E']
    {f : α → E'} {g : α → 𝕜}
    {l : Filter α} (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero

theorem isLittleO_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (Eventually.of_forall fun _x => one_mul _)⟩

theorem isLittleO_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isLittleO_iff_tendsto' (Eventually.of_forall hgf)

alias ⟨_, isLittleO_of_tendsto'⟩ := isLittleO_iff_tendsto'

alias ⟨_, isLittleO_of_tendsto⟩ := isLittleO_iff_tendsto

theorem isLittleO_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop := by
  simp only [← isLittleO_one_left_iff ℝ]
  exact ⟨(isBigO_const_const (1 : ℝ) hc l).trans_isLittleO,
    (isBigO_const_one ℝ c l).trans_isLittleO⟩

@[simp]
theorem isLittleO_const_left {c : E''} :
    (fun _x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [isLittleO_zero, true_or]
  · simp only [hc, false_or, isLittleO_const_left_of_ne hc]; rfl

@[simp 1001] -- Porting note: increase priority so that this triggers before `isLittleO_const_left`
theorem isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun _x => d) =o[l] fun _x => c) ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [isLittleO_const_left, or_iff_left_iff_imp]
  exact fun h => (this h).elim

@[simp]
theorem isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff

theorem isLittleO_const_id_cobounded (c : F'') :
    (fun _ => c) =o[Bornology.cobounded E''] id :=
  isLittleO_const_left.2 <| .inr tendsto_norm_cobounded_atTop

theorem isLittleO_const_id_atTop (c : E'') : (fun _x : ℝ => c) =o[atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop

theorem isLittleO_const_id_atBot (c : E'') : (fun _x : ℝ => c) =o[atBot] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atBot_atTop

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `NormedField`. -/

section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `IsBigOWith c u v l`.
This does not require any assumptions on `c`, which is why we keep this version along with
`IsBigOWith_iff_exists_eq_mul`. -/
theorem isBigOWith_of_eq_mul {u v : α → R} (φ : α → R) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c)
    (h : u =ᶠ[l] φ * v) :
    IsBigOWith c l u v := by
  simp only [IsBigOWith_def]
  refine h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => ?_)
  simp only [Pi.mul_apply]
  refine (norm_mul_le _ _).trans ?_
  gcongr

theorem isBigOWith_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsBigOWith c l u v ↔ ∃ φ : α → 𝕜, (∀ᶠ x in l, ‖φ x‖ ≤ c) ∧ u =ᶠ[l] φ * v := by
  constructor
  · intro h
    use fun x => u x / v x
    refine ⟨Eventually.mono h.bound fun y hy => ?_, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_le_mul₀ (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact isBigOWith_of_eq_mul φ hφ h

theorem IsBigOWith.exists_eq_mul (h : IsBigOWith c l u v) (hc : 0 ≤ c) :
    ∃ φ : α → 𝕜, (∀ᶠ x in l, ‖φ x‖ ≤ c) ∧ u =ᶠ[l] φ * v :=
  (isBigOWith_iff_exists_eq_mul hc).mp h

theorem isBigO_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ φ : α → 𝕜, l.IsBoundedUnder (· ≤ ·) (norm ∘ φ) ∧ u =ᶠ[l] φ * v := by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact isBigO_iff_isBigOWith.2 ⟨c, isBigOWith_of_eq_mul φ hφ huvφ⟩

alias ⟨IsBigO.exists_eq_mul, _⟩ := isBigO_iff_exists_eq_mul

theorem isLittleO_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ φ : α → 𝕜, Tendsto φ l (𝓝 0) ∧ u =ᶠ[l] φ * v := by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · simp only [IsLittleO_def]
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hφ
    exact isBigOWith_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ

alias ⟨IsLittleO.exists_eq_mul, _⟩ := isLittleO_iff_exists_eq_mul

end ExistsMulEq

/-! ### Miscellaneous lemmas -/

theorem div_isBoundedUnder_of_isBigO {α : Type*} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine ⟨c, eventually_map.2 (hc.bound.mono fun x hx => ?_)⟩
  rw [norm_div]
  exact div_le_of_le_mul₀ (norm_nonneg _) h₀ hx

theorem isBigO_iff_div_isBoundedUnder {α : Type*} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  refine ⟨div_isBoundedUnder_of_isBigO, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine IsBigO.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => ?_)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff₀ (norm_pos_iff.2 hgx)).mp hx₂

theorem isBigO_of_div_tendsto_nhds {α : Type*} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) :
    f =O[l] g :=
  (isBigO_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le

theorem IsLittleO.tendsto_zero_of_tendsto {α E 𝕜 : Type*} [NormedAddCommGroup E] [NormedField 𝕜]
    {u : α → E} {v : α → 𝕜} {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun _x => (1 : 𝕜) by
    rwa [isLittleO_one_iff] at h
  exact huv.trans_isBigO (hv.isBigO_one 𝕜)

theorem isLittleO_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m := by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact IsBigO.mul_isLittleO (isBigO_refl _ _)
    (IsLittleO.pow ((isLittleO_one_iff _).2 tendsto_id) hp0)

theorem isLittleO_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero

theorem isLittleO_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert isLittleO_pow_pow h (𝕜 := 𝕜)
  simp only [pow_one]

theorem isLittleO_norm_pow_id {n : ℕ} (h : 1 < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  have := @isLittleO_norm_pow_norm_pow E' _ _ _ h
  simp only [pow_one] at this
  exact isLittleO_norm_right.mp this

theorem IsBigO.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : n ≠ 0) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]

theorem IsBigO.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : n ≠ 0) : f x₀ = 0 := by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn

theorem isLittleO_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  haveI : Tendsto (fun x => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
    apply tendsto_norm_zero.comp
    rw [← sub_self x₀]
    exact tendsto_id.sub tendsto_const_nhds
  (isLittleO_pow_pow h).comp_tendsto this

theorem isLittleO_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [isLittleO_norm_right, pow_one] using isLittleO_pow_sub_pow_sub x₀ h

theorem IsBigOWith.right_le_sub_of_lt_one {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx => by
      simp only [mem_setOf_eq] at hx ⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff₀, mul_sub, mul_one, mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc

theorem IsBigOWith.right_le_add_of_lt_one {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_one hc).neg_right.of_neg_left.congr rfl (fun _ ↦ rfl) fun x ↦ by
    rw [neg_sub, sub_neg_eq_add]

theorem IsLittleO.right_isBigO_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_one one_half_lt_one).isBigO

theorem IsLittleO.right_isBigO_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_one one_half_lt_one).isBigO

theorem IsLittleO.right_isBigO_add' {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] (f₂ + f₁) :=
  add_comm f₁ f₂ ▸ h.right_isBigO_add

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_isBigO_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [IsBigOWith_def, eventually_cofinite] at hC
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  refine ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => ?_⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  exact fun hx => (div_le_iff₀ (norm_pos_iff.2 h₀)).1 (this _ hx)

theorem isBigO_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ := by
  classical
  exact ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩

theorem bound_of_isBigO_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_isBigO_cofinite <| by rwa [Nat.cofinite_eq_atTop]

theorem isBigO_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, isBigO_cofinite_iff h]

theorem isBigO_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun _n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (isBigO_nat_atTop_iff fun _ h => (one_ne_zero h).elim) <| by
    simp only [norm_one, mul_one]

theorem IsBigO.nat_of_atTop {f : ℕ → E''} {g : ℕ → F''} (hfg : f =O[atTop] g)
    {l : Filter ℕ} (h : ∀ᶠ n in l, g n = 0 → f n = 0) : f =O[l] g := by
  obtain ⟨C, hC_pos, hC⟩ := bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  exact hC fun a ↦ hf (h a)

theorem isBigOWith_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    IsBigOWith C l f g' ↔ ∀ i, IsBigOWith C l (fun x => f x i) g' := by
  have : ∀ x, 0 ≤ C * ‖g' x‖ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [isBigOWith_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]

@[simp]
theorem isBigO_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' := by
  simp only [isBigO_iff_eventually_isBigOWith, ← eventually_all]
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => isBigOWith_pi⟩)

@[simp]
theorem isLittleO_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' := by
  simp +contextual only [IsLittleO_def, isBigOWith_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩

theorem IsBigO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R]
    {f : R → E} {g : R → F} (h : f =O[atTop] g) :
    (fun (n : ℕ) => f n) =O[atTop] (fun n => g n) :=
  IsBigO.comp_tendsto h tendsto_natCast_atTop_atTop

theorem IsLittleO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R]
    {f : R → E} {g : R → F} (h : f =o[atTop] g) :
    (fun (n : ℕ) => f n) =o[atTop] (fun n => g n) :=
  IsLittleO.comp_tendsto h tendsto_natCast_atTop_atTop

theorem isBigO_atTop_iff_eventually_exists {α : Type*} [SemilatticeSup α] [Nonempty α]
    {f : α → E} {g : α → F} : f =O[atTop] g ↔ ∀ᶠ n₀ in atTop, ∃ c, ∀ n ≥ n₀, ‖f n‖ ≤ c * ‖g n‖ := by
  rw [isBigO_iff, exists_eventually_atTop]

theorem isBigO_atTop_iff_eventually_exists_pos {α : Type*}
    [SemilatticeSup α] [Nonempty α] {f : α → G} {g : α → G'} :
    f =O[atTop] g ↔ ∀ᶠ n₀ in atTop, ∃ c > 0, ∀ n ≥ n₀, c * ‖f n‖ ≤ ‖g n‖ := by
  simp_rw [isBigO_iff'', ← exists_prop, Subtype.exists', exists_eventually_atTop]

lemma isBigO_mul_iff_isBigO_div {f g h : α → 𝕜} (hf : ∀ᶠ x in l, f x ≠ 0) :
    (fun x ↦ f x * g x) =O[l] h ↔ g =O[l] (fun x ↦ h x / f x) := by
  rw [isBigO_iff', isBigO_iff']
  refine ⟨fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, H⟩ ↦ ⟨c, hc, ?_⟩⟩ <;>
  · refine H.congr <| Eventually.mp hf <| Eventually.of_forall fun x hx ↦ ?_
    rw [norm_mul, norm_div, ← mul_div_assoc, le_div_iff₀' (norm_pos_iff.mpr hx)]

end Asymptotics

open Asymptotics

theorem summable_of_isBigO {ι E} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ι → E} {g : ι → ℝ} (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨_, hC⟩ := h.isBigOWith
  .of_norm_bounded_eventually (hg.abs.mul_left _) hC.bound

theorem summable_of_isBigO_nat {E} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {g : ℕ → ℝ} (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO hg <| Nat.cofinite_eq_atTop.symm ▸ h

lemma Asymptotics.IsBigO.comp_summable_norm {ι E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {f : E → F} {g : ι → E}
    (hf : f =O[𝓝 0] id) (hg : Summable (‖g ·‖)) : Summable (‖f <| g ·‖) :=
  summable_of_isBigO hg <| hf.norm_norm.comp_tendsto <|
    tendsto_zero_iff_norm_tendsto_zero.2 hg.tendsto_cofinite_zero

namespace PartialHomeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {E : Type*} [Norm E] {F : Type*} [Norm F]

/-- Transfer `IsBigOWith` over a `PartialHomeomorph`. -/
theorem isBigOWith_congr (e : PartialHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} {C : ℝ} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      have := e.continuousAt (e.map_target hb)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg g hx)⟩

/-- Transfer `IsBigO` over a `PartialHomeomorph`. -/
theorem isBigO_congr (e : PartialHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr hb

/-- Transfer `IsLittleO` over a `PartialHomeomorph`. -/
theorem isLittleO_congr (e : PartialHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr hb

end PartialHomeomorph

namespace Homeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {E : Type*} [Norm E] {F : Type*} [Norm F]

open Asymptotics

/-- Transfer `IsBigOWith` over a `Homeomorph`. -/
theorem isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toPartialHomeomorph.isBigOWith_congr trivial

/-- Transfer `IsBigO` over a `Homeomorph`. -/
theorem isBigO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr

/-- Transfer `IsLittleO` over a `Homeomorph`. -/
theorem isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr

end Homeomorph

namespace ContinuousOn

variable {α E F : Type*} [TopologicalSpace α] {s : Set α} {f : α → E} {c : F}

section IsBigO

variable [SeminormedAddGroup E] [Norm F]

protected theorem isBigOWith_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) :
    IsBigOWith (sSup (Norm.norm '' (f '' s)) / ‖c‖) (𝓟 s) f fun _ => c := by
  rw [isBigOWith_principal, div_mul_cancel₀ _ hc]
  exact fun x hx ↦ hs.image_of_continuousOn hf |>.image continuous_norm
   |>.isLUB_sSup (Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩)
   |>.left <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx

protected theorem isBigO_principal (hf : ContinuousOn f s) (hs : IsCompact s)
    (hc : ‖c‖ ≠ 0) : f =O[𝓟 s] fun _ => c :=
  (hf.isBigOWith_principal hs hc).isBigO

end IsBigO

section IsBigORev

variable [NormedAddGroup E] [SeminormedAddGroup F]

protected theorem isBigOWith_rev_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hC : ∀ i ∈ s, f i ≠ 0) (c : F) :
    IsBigOWith (‖c‖ / sInf (Norm.norm '' (f '' s))) (𝓟 s) (fun _ => c) f := by
  refine isBigOWith_principal.mpr fun x hx ↦ ?_
  rw [mul_comm_div]
  replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
  have h_sInf := hs.isGLB_sInf <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩
  refine le_mul_of_one_le_right (norm_nonneg c) <| (one_le_div ?_).mpr <|
    h_sInf.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx
  obtain ⟨_, ⟨x, hx, hCx⟩, hnormCx⟩ := hs.sInf_mem h_sInf.nonempty
  rw [← hnormCx, ← hCx]
  exact (norm_ne_zero_iff.mpr (hC x hx)).symm.lt_of_le (norm_nonneg _)

protected theorem isBigO_rev_principal (hf : ContinuousOn f s)
    (hs : IsCompact s) (hC : ∀ i ∈ s, f i ≠ 0) (c : F) : (fun _ => c) =O[𝓟 s] f :=
  (hf.isBigOWith_rev_principal hs hC c).isBigO

end IsBigORev

end ContinuousOn

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
lemma NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type*}
    [NormedDivisionRing 𝕜] [NormedAddCommGroup 𝔸] [Module 𝕜 𝔸] [IsBoundedSMul 𝕜 𝔸] {l : Filter ι}
    {ε : ι → 𝕜} {f : ι → 𝔸} (hε : Tendsto ε l (𝓝 0)) (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← isLittleO_one_iff 𝕜] at hε ⊢
  simpa using IsLittleO.smul_isBigO hε (hf.isBigO_const (one_ne_zero : (1 : 𝕜) ≠ 0))
