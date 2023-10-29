/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Covering
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UnitInterval
/-!

# The Homotopy lifting property of covering maps

Currently, this file only proves uniqueness of lifting, not existence,
but under some more general conditions than covering maps, in order to
apply to situations such as the monodromy theorem for analytic continuations.
-/

open Topology unitInterval

section Separated

variable {X Y} [TopologicalSpace X]

def SeparatedMap (f : X → Y) : Prop := ∀ x₁ x₂, f x₁ = f x₂ →
    x₁ ≠ x₂ → ∃ s₁ s₂, IsOpen s₁ ∧ IsOpen s₂ ∧ x₁ ∈ s₁ ∧ x₂ ∈ s₂ ∧ Disjoint s₁ s₂

lemma t2space_iff_separatedMap (y : Y) : T2Space X ↔ SeparatedMap fun _ : X ↦ y :=
  ⟨fun ⟨t2⟩ x₁ x₂ _ hne ↦ t2 x₁ x₂ hne, fun sep ↦ ⟨fun x₁ x₂ hne ↦ sep x₁ x₂ rfl hne⟩⟩

lemma T2Space.separatedMap [T2Space X] (f : X → Y) : SeparatedMap f := fun _ _ _ ↦ t2_separation

lemma separatedMap_iff_disjoint_nhds {f : X → Y} : SeparatedMap f ↔
    ∀ x₁ x₂, f x₁ = f x₂ → x₁ ≠ x₂ → Disjoint (𝓝 x₁) (𝓝 x₂) :=
  forall₃_congr fun x x' _ ↦ by simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens x'),
    exists_prop, ← exists_and_left, and_assoc, and_comm, and_left_comm]

lemma separatedMap_iff_nhds {f : X → Y} : SeparatedMap f ↔
    ∀ x₁ x₂, f x₁ = f x₂ → x₁ ≠ x₂ → ∃ s₁ ∈ 𝓝 x₁, ∃ s₂ ∈ 𝓝 x₂, Disjoint s₁ s₂ := by
  simp_rw [separatedMap_iff_disjoint_nhds, Filter.disjoint_iff]

abbrev Pullback {Z} (f : X → Y) (g : Z → Y) := {p : X × Z // f p.1 = g p.2}

open Set Filter in
theorem separatedMap_iff_isClosed_diagonal {f : X → Y} : SeparatedMap f ↔
    IsClosed {p : Pullback f f | p.val.1 = p.val.2} := by
  simp_rw [separatedMap_iff_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq]
  refine forall₄_congr fun x₁ x₂ _ _ ↦ ⟨fun h ↦ ?_, fun ⟨t, ht, t_sub⟩ ↦ ?_⟩
  · simp_rw [← Filter.disjoint_iff, ← compl_diagonal_mem_prod] at h
    exact ⟨_, h, subset_rfl⟩
  · obtain ⟨s₁, h₁, s₂, h₂, s_sub⟩ := mem_prod_iff.mp ht
    exact ⟨s₁, h₁, s₂, h₂, disjoint_left.2 fun x h₁ h₂ ↦ @t_sub ⟨(x, x), rfl⟩ (s_sub ⟨h₁, h₂⟩) rfl⟩

theorem separatedMap_iff_isClosedMap {f : X → Y} :
    SeparatedMap f ↔ IsClosedMap fun x ↦ (⟨(x, x), rfl⟩ : Pullback f f) :=
  separatedMap_iff_isClosed_diagonal.trans <| by
    refine ⟨fun diag_closed s s_closed ↦ ?_, fun closed_map ↦ ?_⟩
    · convert diag_closed.inter ((s_closed.prod s_closed).preimage continuous_subtype_val)
      ext ⟨⟨x₁, x₂⟩, he⟩; constructor
      · rintro ⟨x, hx, he⟩
        simp_rw [Subtype.ext_iff, Prod.mk.inj_iff] at he
        cases he.1; cases he.2; exact ⟨rfl, hx, hx⟩
      · rintro ⟨(rfl : x₁ = x₂), h, _⟩; exact ⟨x₁, h, rfl⟩
    · convert closed_map _ isClosed_univ
      ext ⟨⟨x₁, x₂⟩, he⟩; constructor
      · rintro (rfl : x₁ = x₂); exact ⟨x₁, trivial, rfl⟩
      · rintro ⟨x, -, he⟩
        simp_rw [Subtype.ext_iff, Prod.mk.inj_iff] at he
        exact he.1.symm.trans he.2

theorem t2space_iff_isClosedMap : T2Space X ↔ IsClosedMap fun x : X ↦ (x, x) := by
  let f := fun _ : X ↦ Unit.unit
  let H : {p : X × X // f p.1 = f p.2} ≃ₜ X × X :=
    (Homeomorph.setCongr <| Set.eq_univ_of_forall fun p ↦ rfl).trans (Homeomorph.Set.univ _)
  rw [t2space_iff_separatedMap Unit.unit, separatedMap_iff_isClosedMap]
  exact ⟨fun h ↦ H.isClosedMap.comp h, fun h ↦ H.symm.isClosedMap.comp h⟩

theorem separatedMap.pullback {f : X → Y} (sep : SeparatedMap f) {Z} [TopologicalSpace Z]
    (g : Z → Y) : SeparatedMap (fun p : Pullback f g ↦ p.1.2) := by
  rw [separatedMap_iff_isClosed_diagonal] at sep ⊢
  let f' := fun p : Pullback f g ↦ p.1.2
  let proj : Pullback f' f' → Pullback f f := fun p ↦ ⟨(p.val.1.val.1, p.val.2.val.1),
    (p.val.1.prop.trans <| congr_arg g p.2).trans p.val.2.prop.symm⟩
  have : Continuous proj
  · refine continuous_induced_rng.mpr (continuous_prod_mk.mpr ⟨?_, ?_⟩) <;>
    apply_rules [continuous_fst, continuous_snd, continuous_subtype_val, Continuous.comp]
  convert sep.preimage this; ext ⟨⟨p₁, p₂⟩, he⟩
  simp_rw [Set.mem_setOf, Subtype.ext_iff, Prod.ext_iff]
  exact and_iff_left he

end Separated

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] {p : E → X}

namespace SeparatedMap

variable [PreconnectedSpace A] (sep : SeparatedMap p) (hp : ∀ e : E, ∃ U ∈ 𝓝 e, U.InjOn p)

-- connectedComponent version, without assume PreconnectedSpace ..
/-- If `p` is a locally injective separated map, and `A` is a connected space,
  then two lifts `g₁, g₂ : A → E` of a map `f : A → X` are equal if they agree at one point. -/
theorem eq_of_comp_eq (g₁ g₂ : C(A,E))
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := by
  have := IsClopen.eq_univ (s := {a | g₁ a = g₂ a}) ⟨?_, ?_⟩ ⟨a, ha⟩
  · ext a; apply this.symm ▸ Set.mem_univ a
  /- Since A is connected and s := {a | g₁ a = g₂ a} inhabited by a,
     we just need to show that s is open and closed. -/
  · refine isOpen_iff_mem_nhds.mpr (fun a ha ↦ ?_)
    /- Given a point a where g₁ and g₂ agree,
       take an open neighborhood U of g₁(a) = g₂(a) on which p is injective.
       Then g₁ and g₂ agree on the open neighborhood g₁⁻¹(U) ∩ g₂⁻¹(U) of a. -/
    obtain ⟨U, hU, hi⟩ := hp (g₁ a)
    apply Filter.mem_of_superset (Filter.inter_mem (g₁.2.continuousAt.preimage_mem_nhds hU) <|
      g₂.2.continuousAt.preimage_mem_nhds <| Set.mem_setOf.mp ha ▸ hU)
    exact fun a' ha ↦ hi ha.1 ha.2 (congr_fun he a')
  · simp_rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro a ha
    /- Given a point a where g₁ and g₂ doesn't agree,
       take disjoint neighborhoods U₁ of g₁(a) and U₂ of g₂(a),
       then g₁ and g₂ doesn't agree on any point in the neighborhood g₁⁻¹(U₁) ∩ g₂⁻¹(U₂) of a. -/
    obtain ⟨U₁, h₁, U₂, h₂, disj⟩ := separatedMap_iff_nhds.mp sep _ _ (congr_fun he a) ha
    apply Filter.mem_of_superset (Filter.inter_mem (g₁.2.continuousAt.preimage_mem_nhds h₁) <|
      g₂.2.continuousAt.preimage_mem_nhds h₂) (fun a h ↦ Set.disjoint_iff_forall_ne.mp disj h.1 h.2)

theorem const_of_comp (g : C(A,E)) (he : ∀ a a', p (g a) = p (g a')) (a a') : g a = g a' :=
  FunLike.congr_fun
    (sep.eq_of_comp_eq hp g (ContinuousMap.const A (g a')) (funext fun a ↦ he a a') a' rfl) a

end SeparatedMap

theorem IsCoveringMap.separatedMap (hp : IsCoveringMap p) : SeparatedMap p :=
  fun e₁ e₂ he hne ↦ by
    obtain ⟨_, t, he₁⟩ := hp (p e₁)
    have he₂ := he₁; simp_rw [he] at he₂; rw [← Set.mem_preimage, ← t.source_eq] at he₁ he₂
    refine ⟨t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₁).2}, t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₂).2},
      ?_, ?_, ⟨he₁, rfl⟩, ⟨he₂, rfl⟩, Set.disjoint_left.mpr fun x h₁ h₂ ↦ hne (t.injOn he₁ he₂ ?_)⟩
    iterate 2
      exact t.continuous_toFun.preimage_open_of_open t.open_source
        (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
    refine Prod.ext ?_ (h₁.2.symm.trans h₂.2)
    rwa [t.proj_toFun e₁ he₁, t.proj_toFun e₂ he₂]

lemma IsLocallyHomeomorph.injOn (hp : IsLocallyHomeomorph p) (e : E) :
    ∃ U ∈ 𝓝 e, U.InjOn p := by
  obtain ⟨p, he, rfl⟩ := hp e; exact ⟨p.source, p.open_source.mem_nhds he, p.injOn⟩

theorem IsCoveringMap.eq_of_comp_eq [PreconnectedSpace A] (hp : IsCoveringMap p) (g₁ g₂ : C(A,E))
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hp.separatedMap.eq_of_comp_eq hp.isLocallyHomeomorph.injOn g₁ g₂ he a ha

theorem IsCoveringMap.const_of_comp [PreconnectedSpace A] (hp : IsCoveringMap p) (g : C(A,E))
    (he : ∀ a a', p (g a) = p (g a')) (a a') : g a = g a' :=
  hp.separatedMap.const_of_comp hp.isLocallyHomeomorph.injOn g he a a'

lemma lebesgue_number_lemma_unitInterval {ι} {c : ι → Set I} (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : Set.univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧
      (∀ n, ∃ i, Set.Icc (t n) (t <| n + 1) ⊆ c i) ∧ ∃ n, ∀ m ≥ n, t m = 1 := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  refine ⟨fun n ↦ Set.projIcc 0 1 zero_le_one (n * (δ/2)), ?_, fun n m hnm ↦ ?_, fun n ↦ ?_, ?_⟩
  · dsimp only; rw [Nat.cast_zero, zero_mul, Set.projIcc_left]; rfl
  · apply Set.monotone_projIcc
    rw [mul_le_mul_right (div_pos δ_pos zero_lt_two)]
    exact_mod_cast hnm
  · obtain ⟨i, hsub⟩ := ball_subset (Set.projIcc 0 1 zero_le_one (n * (δ/2))) trivial
    refine ⟨i, fun x hx ↦ hsub ?_⟩
    rw [Metric.mem_ball]
    apply (abs_eq_self.mpr _).trans_lt
    · apply (sub_le_sub_right _ _).trans_lt
      on_goal 3 => exact hx.2
      refine (max_sub_max_le_max _ _ _ _).trans_lt (max_lt (by rwa [sub_zero]) ?_)
      refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt ?_ ?_)
      · rwa [sub_self, abs_zero]
      · rw [← sub_mul, Nat.cast_succ, add_sub_cancel', one_mul, abs_lt]
        constructor <;> linarith only [δ_pos]
    · exact sub_nonneg_of_le hx.1
  · refine ⟨Nat.ceil (δ/2)⁻¹, fun n hn ↦ (Set.projIcc_eq_right zero_lt_one).mpr ?_⟩
    rwa [GE.ge, Nat.ceil_le, inv_pos_le_iff_one_le_mul (div_pos δ_pos zero_lt_two)] at hn

instance : BoundedOrder I := Set.Icc.boundedOrder zero_le_one

-- generalize to IsLocallyHomeomorphOn?
/-- If `p : E → X` is a local homeomorphism, and if `g : I × A → E` is a lift of `f : C(I × A, X)`
  continuous on `{0} × A ∪ I × {a}` for some `a : A`, then there exists a neighborhood `N ∈ 𝓝 a`
  and `g' : I × A → E` continuous on `I × N` that agrees with `g` on `{0} × A ∪ I × {a}`.
  The proof follows Hatcher, Proof of Theorem 1.7, p.30.

  This lemma should also be true for an arbitrary space in place of `I` if `A` is locally connected
  and `p` is a separated map, which guarantees uniqueness and therefore well-definedness
  on the intersections. -/
theorem IsLocallyHomeomorph.exists_lift_nhds (hp : IsLocallyHomeomorph p)
    {f : C(I × A, X)} {g : I × A → E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (a : A) (cont_a : Continuous (g ⟨·, a⟩)) :
    ∃ N ∈ 𝓝 a, ∃ g' : I × A → E, ContinuousOn g' (Set.univ ×ˢ N) ∧ p ∘ g' = f ∧
      (∀ a, g' (0, a) = g (0, a)) ∧ ∀ t, g' (t, a) = g (t, a) := by
  /- For every `e : E`, we can upgrade `p` to a LocalHomeomorph `q e` around `e`. -/
  choose q mem_source hpq using hp
  obtain ⟨t, t_0, t_mono, t_sub, n_max, h_max⟩ := lebesgue_number_lemma_unitInterval
    (fun e ↦ (q e).open_source.preimage cont_a)
    fun t _ ↦ Set.mem_iUnion.mpr ⟨g (t, a), mem_source _⟩
  suffices : ∀ n, ∃ N, a ∈ N ∧ IsOpen N ∧ ∃ g' : I × A → E, ContinuousOn g' (Set.Icc 0 (t n) ×ˢ N) ∧
    p ∘ g' = f ∧ (∀ a, g' (0, a) = g (0, a)) ∧ ∀ t' ≤ t n, g' (t', a) = g (t', a)
  · obtain ⟨N, haN, N_open, hN⟩ := this n_max
    simp_rw [h_max _ le_rfl] at hN
    refine ⟨N, N_open.mem_nhds haN, ?_⟩; convert hN
    · rw [eq_comm, Set.eq_univ_iff_forall]; exact fun t ↦ ⟨bot_le, le_top⟩
    · rw [imp_iff_right]; exact le_top
  refine Nat.rec ⟨_, Set.mem_univ a, isOpen_univ, g, ?_, g_lifts, fun a ↦ rfl, fun _ _ ↦ rfl⟩
    (fun n ⟨N, haN, N_open, g', cont_g', g'_lifts, g'_0, g'_a⟩ ↦ ?_)
  · refine (cont_0.comp continuous_snd).continuousOn.congr (fun ta ⟨ht, _⟩ ↦ ?_)
    rw [t_0, Set.Icc_self, Set.mem_singleton_iff] at ht; rw [← ta.eta, ht]; rfl
  obtain ⟨e, h_sub⟩ := t_sub n
  have : Set.Icc (t n) (t (n+1)) ×ˢ {a} ⊆ f ⁻¹' (q e).target
  · rintro ⟨t0, a'⟩ ⟨ht, ha⟩
    rw [Set.mem_singleton_iff] at ha; dsimp only at ha
    rw [← g_lifts, hpq e, ha]
    exact (q e).map_source (h_sub ht)
  obtain ⟨u, v, -, v_open, hu, hav, huv⟩ := generalized_tube_lemma isClosed_Icc.isCompact
    isCompact_singleton ((q e).open_target.preimage f.continuous) this
  classical
  refine ⟨_, ?_, v_open.inter <| (cont_g'.comp (Continuous.Prod.mk <| t n).continuousOn
      fun a ha ↦ ⟨?_, ha⟩).preimage_open_of_open N_open (q e).open_source,
    fun ta ↦ if ta.1 ≤ t n then g' ta else if f ta ∈ (q e).target then (q e).symm (f ta) else g ta,
    ContinuousOn.if (fun ta ⟨⟨_, hav, _, ha⟩, hfr⟩ ↦ ?_) (cont_g'.mono fun ta ⟨hta, ht⟩ ↦ ?_) ?_,
    ?_, fun a ↦ ?_, fun t0 htn1 ↦ ?_⟩
  · refine ⟨Set.singleton_subset_iff.mp hav, haN, ?_⟩
    change g' (t n, a) ∈ (q e).source; rw [g'_a _ le_rfl]
    exact h_sub ⟨le_rfl, t_mono n.le_succ⟩
  · rw [← t_0]; exact ⟨t_mono n.zero_le, le_rfl⟩
  · have ht := Set.mem_setOf.mp (frontier_le_subset_eq continuous_fst continuous_const hfr)
    have : f ta ∈ (q e).target := huv ⟨hu (by rw [ht]; exact ⟨le_rfl, t_mono n.le_succ⟩), hav⟩
    rw [if_pos this]
    apply (q e).injOn (by rw [← ta.eta, ht]; exact ha) ((q e).map_target this)
    rw [(q e).right_inv this, ← hpq e]; exact congr_fun g'_lifts ta
  · rw [closure_le_eq continuous_fst continuous_const] at ht
    exact ⟨⟨hta.1.1, ht⟩, hta.2.2.1⟩
  · simp_rw [not_le]; exact (ContinuousOn.congr ((q e).continuous_invFun.comp f.2.continuousOn
      fun _ h ↦ huv ⟨hu ⟨h.2, h.1.1.2⟩, h.1.2.1⟩)
      fun _ h ↦ if_pos <| huv ⟨hu ⟨h.2, h.1.1.2⟩, h.1.2.1⟩).mono
        (Set.inter_subset_inter_right _ <| closure_lt_subset_le continuous_const continuous_fst)
  · ext ta; rw [Function.comp_apply]; split_ifs with _ hv
    · exact congr_fun g'_lifts ta
    · rw [hpq e, (q e).right_inv hv]
    · exact congr_fun g_lifts ta
  · rw [← g'_0]; exact if_pos bot_le
  · dsimp only; split_ifs with htn hf
    · exact g'_a t0 htn
    · apply (q e).injOn ((q e).map_target hf) (h_sub ⟨le_of_not_ge htn, htn1⟩)
      rw [(q e).right_inv hf, ← hpq e]; exact (congr_fun g_lifts _).symm
    · rfl

theorem IsLocallyHomeomorph.continuous_lift (loc_homeo : IsLocallyHomeomorph p)
    (sep : SeparatedMap p) (f : C(I × A, X)) {g : I × A → E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (cont_A : ∀ a, Continuous (g ⟨·, a⟩)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro ⟨t, a⟩
  obtain ⟨N, haN, g', cont_g', g'_lifts, g'_0, -⟩ :=
    loc_homeo.exists_lift_nhds g_lifts cont_0 a (cont_A a)
  refine (cont_g'.congr fun ⟨t, a⟩ ⟨_, ha⟩ ↦ ?_).continuousAt (prod_mem_nhds Filter.univ_mem haN)
  refine FunLike.congr_fun (sep.eq_of_comp_eq loc_homeo.injOn ⟨_, cont_A a⟩
    ⟨_, cont_g'.comp_continuous (Continuous.Prod.mk_left a) (fun _ ↦ ⟨trivial, ha⟩)⟩
    ?_ 0 (g'_0 a).symm) t
  ext t; apply congr_fun (g_lifts.trans g'_lifts.symm)

namespace IsCoveringMap
variable (hp : IsCoveringMap p)

section path_lifting
variable (γ : C(I,X)) (e : E) (γ_0 : γ 0 = p e)

/-- The path lifting property (existence and uniqueness) for covering maps. -/
theorem exists_path_lifts : ∃ Γ : C(I,E), p ∘ Γ = γ ∧ Γ 0 = e := by
  have := hp; choose _ q mem_base using this
  obtain ⟨t, t_0, t_mono, t_sub, n_max, h_max⟩ := lebesgue_number_lemma_unitInterval
    (fun x ↦ (q x).open_baseSet.preimage γ.continuous) fun t _ ↦ Set.mem_iUnion.2 ⟨γ t, mem_base _⟩
  suffices : ∀ n, ∃ Γ : I → E, ContinuousOn Γ (Set.Icc 0 (t n)) ∧
    (Set.Icc 0 (t n)).EqOn (p ∘ Γ) γ ∧ Γ 0 = e
  · obtain ⟨Γ, cont, eqOn, Γ_0⟩ := this n_max; rw [h_max _ le_rfl] at cont eqOn
    exact ⟨⟨Γ, continuous_iff_continuousOn_univ.mpr
      (by convert cont; rw [eq_comm, Set.eq_univ_iff_forall]; exact fun t ↦ ⟨bot_le, le_top⟩)⟩,
      funext fun _ ↦ eqOn ⟨bot_le, le_top⟩, Γ_0⟩
  refine Nat.rec ⟨fun _ ↦ e, continuous_const.continuousOn, fun t ht ↦ ?_, rfl⟩
    fun n ⟨Γ, cont, eqOn, Γ_0⟩ ↦ ?_
  · rw [t_0, Set.Icc_self] at ht; cases ht; exact γ_0.symm
  obtain ⟨x, t_sub⟩ := t_sub n
  refine ⟨fun s ↦ if s ≤ t n then Γ s else (q x).invFun (γ s, (q x (Γ (t n))).2),
    ContinuousOn.if (fun s hs ↦ ?_) (cont.mono fun _ h ↦ ?_) ?_, fun s hs ↦ ?_, ?_⟩
  · have pΓtn : p (Γ (t n)) = γ (t n) := eqOn ⟨t_0 ▸ t_mono n.zero_le, le_rfl⟩
    cases frontier_Iic_subset _ hs.2
    rw [← pΓtn]
    refine ((q x).symm_apply_mk_proj ?_).symm
    rw [(q x).mem_source, pΓtn]
    exact t_sub ⟨le_rfl, t_mono n.le_succ⟩
  · rw [closure_le_eq continuous_id' continuous_const] at h; exact ⟨h.1.1, h.2⟩
  · apply (q x).continuous_invFun.comp ((Continuous.Prod.mk_left _).comp γ.2).continuousOn
    simp_rw [not_le, (q x).target_eq]; intro s h
    exact ⟨t_sub ⟨closure_lt_subset_le continuous_const continuous_subtype_val h.2, h.1.2⟩, trivial⟩
  · rw [Function.comp_apply]; split_ifs with h
    exacts [eqOn ⟨hs.1, h⟩, (q x).proj_symm_apply' (t_sub ⟨le_of_not_le h, hs.2⟩)]
  · dsimp only; rwa [if_pos (t_0 ▸ t_mono n.zero_le)]

noncomputable def liftPath : C(I,E) := (hp.exists_path_lifts γ e γ_0).choose

lemma liftPath_lifts : p ∘ hp.liftPath γ e γ_0 = γ := (hp.exists_path_lifts γ e γ_0).choose_spec.1
lemma liftPath_zero : hp.liftPath γ e γ_0 0 = e := (hp.exists_path_lifts γ e γ_0).choose_spec.2

variable {γ e}
lemma eq_liftPath_iff {Γ : I → E} : Γ = hp.liftPath γ e γ_0 ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e :=
  have lifts := hp.liftPath_lifts γ e γ_0
  have zero := hp.liftPath_zero γ e γ_0
  ⟨fun h ↦ h ▸ ⟨(hp.liftPath γ e γ_0).2, lifts, zero⟩, fun ⟨Γ_cont, Γ_lifts, Γ_0⟩ ↦
    FunLike.coe_fn_eq.mpr <| hp.eq_of_comp_eq ⟨Γ, Γ_cont⟩
      (hp.liftPath γ e γ_0) (Γ_lifts ▸ lifts.symm) 0 (Γ_0 ▸ zero.symm)⟩

lemma eq_liftPath_iff' {Γ : C(I,E)} : Γ = hp.liftPath γ e γ_0 ↔ p ∘ Γ = γ ∧ Γ 0 = e := by
  simp_rw [← FunLike.coe_fn_eq, eq_liftPath_iff, and_iff_right (ContinuousMap.continuous _)]

end path_lifting

section homotopy_lifting
variable (H : C(I × A, X)) (f : C(A, E)) (H_0 : ∀ a, H (0, a) = p (f a))

/-- The existence of `liftHomotopy` satisfying `liftHomotopy_lifts` and `liftHomotopy_zero` is
  the homotopy lifting property for covering maps.
  In other words, a covering map is a Hurewicz fibration. -/
@[simps] noncomputable def liftHomotopy : C(I × A, E) where
  toFun ta := hp.liftPath (H.comp <| (ContinuousMap.id I).prodMk <| ContinuousMap.const I ta.2)
    (f ta.2) (H_0 ta.2) ta.1
  continuous_toFun := hp.isLocallyHomeomorph.continuous_lift hp.separatedMap H
    (by ext ⟨t, a⟩; exact congr_fun (hp.liftPath_lifts _ _ _) t)
    (by convert f.continuous with a; exact hp.liftPath_zero _ _ _)
    fun a ↦ by dsimp only; exact (hp.liftPath _ _ _).2

lemma liftHomotopy_lifts : p ∘ hp.liftHomotopy H f H_0 = H :=
  funext fun ⟨t, _⟩ ↦ congr_fun (hp.liftPath_lifts _ _ _) t

lemma liftHomotopy_zero (a : A) : hp.liftHomotopy H f H_0 (0, a) = f a := hp.liftPath_zero _ _ _

variable {H f}
lemma eq_liftHomotopy_iff (H' : I × A → E) : H' = hp.liftHomotopy H f H_0 ↔
    (∀ a, Continuous (H' ⟨·, a⟩)) ∧ p ∘ H' = H ∧ ∀ a, H' (0, a) = f a := by
  refine ⟨?_, fun ⟨H'_cont, H'_lifts, H'_0⟩ ↦ funext fun ⟨t, a⟩ ↦ ?_⟩
  · rintro rfl; refine ⟨fun a ↦ ?_, hp.liftHomotopy_lifts H f H_0, hp.liftHomotopy_zero H f H_0⟩
    simp_rw [liftHomotopy_apply]; exact (hp.liftPath _ _ <| H_0 a).2
  · apply congr_fun ((hp.eq_liftPath_iff _).mpr ⟨H'_cont a, _, H'_0 a⟩) t
    ext ⟨t, a⟩; exact congr_fun H'_lifts _

lemma eq_liftHomotopy_iff' (H' : C(I × A, E)) :
    H' = hp.liftHomotopy H f H_0 ↔ p ∘ H' = H ∧ ∀ a, H' (0, a) = f a := by
  simp_rw [← FunLike.coe_fn_eq, eq_liftHomotopy_iff]
  exact and_iff_right fun a ↦ H'.2.comp (Continuous.Prod.mk_left a)

variable {f₀ f₁ : C(A, X)} {S : Set A} (F : f₀.HomotopyRel f₁ S)

--lemma liftHomotopy_homotopyRel_apply_eq {f' : C(I, E)} (hf' :) :

open ContinuousMap in
noncomputable def liftHomotopyRel [PreconnectedSpace A]
    {f₀' f₁' : C(A, E)} (he : ∃ a ∈ S, f₀' a = f₁' a)
    (h₀ : p ∘ f₀' = f₀) (h₁ : p ∘ f₁' = f₁) : f₀'.HomotopyRel f₁' S :=
  have F_0 : ∀ a, F (0, a) = p (f₀' a) := fun a ↦ (F.apply_zero a).trans (congr_fun h₀ a).symm
  { toContinuousMap := hp.liftHomotopy F f₀' F_0
    map_zero_left := hp.liftHomotopy_zero F f₀' F_0
    map_one_left := by
      obtain ⟨a, ha, he⟩ := he
      simp_rw [toFun_eq_coe, ← curry_apply]
      apply FunLike.congr_fun (hp.eq_of_comp_eq _ f₁' _ a _)
      · ext a; rw [h₁, Function.comp_apply, curry_apply]
        exact (congr_fun (hp.liftHomotopy_lifts F f₀' _) (1, a)).trans (F.apply_one a)
      · rw [curry_apply, liftHomotopy_apply, hp.const_of_comp _ _ 1 0]
        · exact (hp.liftPath_zero _ _ _).trans he
        · intro t t'
          simp_rw [← p.comp_apply, hp.liftPath_lifts]
          exact (F.prop t a ha).1.trans (F.prop t' a ha).1.symm
    prop' := fun t a ha ↦ by
      dsimp? }



end homotopy_lifting

-- IsGaloisCoveringWith ... arbitrary G with ContinuousConstSmul ..
-- IsGaloisCovering ... G := deck transformations ..


def _root_.ContinuousMap.HomotopyRel.compContinuousMap {X Y Z} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z)) {f₀ : C(X, Y)} {f₁ : C(X, Y)}
    {S : Set X} (F : f₀.HomotopyRel f₁ S) : (g.comp f₀).HomotopyRel (g.comp f₁) S where
  toHomotopy := F.hcomp (ContinuousMap.Homotopy.refl g)
  prop' t x hx := ⟨congr_arg g (F.prop t x hx).1, congr_arg g (F.prop t x hx).2⟩

theorem homotopicRel_iff (hp : IsCoveringMap p) {f₀ f₁ : C(A, E)} {S : Set A} :
    f₀.HomotopicRel f₁ S ↔ (ContinuousMap.comp ⟨p, hp.continuous⟩ f₀).HomotopicRel
      (ContinuousMap.comp ⟨p, hp.continuous⟩ f₁) S :=
  ⟨Nonempty.map (ContinuousMap.HomotopyRel.compContinuousMap _), _⟩

end homotopy_lifting



-- show that lifts of two paths homotopyRel endpoint have same endpoint ..


  -- forward direction requires HomotopyRel version of ContinuousMap.Homotopy.compContinuousMap
  -- can be used to show injectivity of the morphism on fundamental groups induced by a covering map
  --refine ⟨Nonempty.map fun h ↦ h.compContinuousMap _, ?_⟩

end IsCoveringMap


-- injective on fundamental group
-- lifting criterion : locally path connected
-- can be used to lift `E → X` to an automorphism of `E` .. need image in fundamental group to be normal for lift to always exist ..
-- TODO: construct covering spaces from action of fundamental groupoid .. put topology on it
-- in particular, define universal cover
-- Galois correspondence between subgroups and covering spaces ..
-- Galois covering: CoveringMap with deck transformations acting transitively on fibers
-- alternatively: image of fundamental group is normal subgroup .. normal subgroupoid ..

-- two paths with same left+right endpoints don't necessarily lift to paths with same right endpoints
-- but if there's a homotopy rel endpoints between them, then they necessarily lift to same right endpoint
