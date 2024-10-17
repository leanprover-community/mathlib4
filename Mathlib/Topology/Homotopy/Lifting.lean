/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering
import Mathlib.Topology.UnitInterval
/-!

# The Homotopy lifting property of covering maps

Currently, this file only proves uniqueness of lifting, not existence,
but under some more general conditions than covering maps, in order to
apply to situations such as the monodromy theorem for analytic continuations.
-/

open Topology unitInterval

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] {p : E → X}

-- generalize to IsLocalHomeomorphOn?
/-- If `p : E → X` is a local homeomorphism, and if `g : I × A → E` is a lift of `f : C(I × A, X)`
  continuous on `{0} × A ∪ I × {a}` for some `a : A`, then there exists a neighborhood `N ∈ 𝓝 a`
  and `g' : I × A → E` continuous on `I × N` that agrees with `g` on `{0} × A ∪ I × {a}`.
  The proof follows Hatcher, Proof of Theorem 1.7, p.30.

  This lemma should also be true for an arbitrary space in place of `I` if `A` is locally connected
  and `p` is a separated map, which guarantees uniqueness and therefore well-definedness
  on the intersections. -/
theorem IsLocalHomeomorphOn.exists_lift_nhds {s : Set E} (hp : IsLocalHomeomorphOn p s)
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

namespace IsLocalHomeomorph

variable (homeo : IsLocalHomeomorph p) (sep : IsSeparatedMap p)

theorem continuous_lift (f : C(I × A, X)) {g : I × A → E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (cont_A : ∀ a, Continuous (g ⟨·, a⟩)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro ⟨t, a⟩
  obtain ⟨N, haN, g', cont_g', g'_lifts, g'_0, -⟩ :=
    homeo.exists_lift_nhds g_lifts cont_0 a (cont_A a)
  refine (cont_g'.congr fun ⟨t, a⟩ ⟨_, ha⟩ ↦ ?_).continuousAt (prod_mem_nhds Filter.univ_mem haN)
  refine FunLike.congr_fun (sep.eq_of_comp_eq homeo.injOn ⟨_, cont_A a⟩
    ⟨_, cont_g'.comp_continuous (Continuous.Prod.mk_left a) (fun _ ↦ ⟨trivial, ha⟩)⟩
    ?_ 0 (g'_0 a).symm) t
  ext t; apply congr_fun (g_lifts.trans g'_lifts.symm)

/-- The abstract monodromy theorem: if `γ₀` and `γ₁` are two paths in a topological space `X`,
  `γ` is a homotopy between them relative to the endpoints, and the path at each time step of
  the homotopy, `γ (t, ·)`, lifts to a continuous path `Γ t` through a separated local
  homeomorphism `p : E → X`, starting from some point in `E` independent of `t`. Then the
  endpoints of these lifts are also independent of `t`.

  This can be applied to continuation of analytic functions as follows: for a sheaf of analytic
  function on an analytic manifold `X`, we may consider its étale space `E` (whose points are
  analytic germs) with the natural projection `p : E → X`, which is a local homeomorphism and a
  separated map (because two analytic functions agreeing on a nonempty open set agrees on the
  whole connected component). An analytic continuation of a germ along a path `γ (t, ·) : C(I, X)`
  corresponds to a continuous lift of `γ (t, ·)` to `E` starting from that germ. If `γ` is a
  homotopy and the germ admits continuation along every path `γ (t, ·)`, then the result of the
  continuations are independent of `t`. In particular, if `X` is simply connected and an analytic
  germ at `p : X` admits a continuation along every path in `X` from `p` to `q : X`, then the
  continuation to `q` is independent of the path chosen. -/
theorem monodromy_theorem {γ₀ γ₁ : C(I, X)} (γ : γ₀.HomotopyRel γ₁ {0,1}) (Γ : I → C(I, E))
    (Γ_lifts : ∀ t s, p (Γ t s) = γ (t, s)) (Γ_0 : ∀ t, Γ t 0 = Γ 0 0) (t : I) :
    Γ t 1 = Γ 0 1 := by
  have := homeo.continuous_lift sep (γ.comp .prodSwap) (g := fun st ↦ Γ st.2 st.1) ?_ ?_ ?_
  · apply sep.const_of_comp homeo.injOn ⟨fun t ↦ Γ t 1, this.comp (.Prod.mk 1)⟩
    intro t t'; change p (Γ _ _) = p (Γ _ _); simp_rw [Γ_lifts, γ.eq_fst _ (.inr rfl)]
  · ext; apply Γ_lifts
  · simp_rw [Γ_0]; exact continuous_const
  · exact fun t ↦ (Γ t).2

/-- A map `f` from a path-connected, locally path-connected space `A` to another space `X` lifts
  through a local homeomorphism `p : E → X` if every path `γ` in `A`, the composed path `f ∘ γ`
  in `X` lifts to `E` with endpoint only dependent on the endpoint of `γ` and independent of the
  path chosen. In this theorem, we require that a specific point `a : A` be mapped to a specific
  point `e : E`. -/
/- theorem exists_lift_of_locPathConnectedSpace [PathConnectedSpace A] [LocPathConnectedSpace A]
    (f : C(A, X)) (a : A) (e : E) (he : p e = f a)
    (ex : ∀ γ : C(I, A), γ 0 = a → ∃ Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ ∘ f)
    (uniq : ∀ γ γ' : C(I, A), γ 0 = a ∧ γ' 0 = a ∧  )
-/

end IsLocalHomeomorph

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
  continuous_toFun := hp.IsLocalHomeomorph.continuous_lift hp.separatedMap H
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

open ContinuousMap in
noncomputable def liftHomotopyRel [PreconnectedSpace A]
    {f₀' f₁' : C(A, E)} (he : ∃ a ∈ S, f₀' a = f₁' a)
    (h₀ : p ∘ f₀' = f₀) (h₁ : p ∘ f₁' = f₁) : f₀'.HomotopyRel f₁' S :=
  have F_0 : ∀ a, F (0, a) = p (f₀' a) := fun a ↦ (F.apply_zero a).trans (congr_fun h₀ a).symm
  have rel : ∀ t, ∀ a ∈ S, hp.liftHomotopy F f₀' F_0 (t, a) = f₀' a := fun t a ha ↦ by
    rw [liftHomotopy_apply, hp.const_of_comp _ _ t 0]
    · apply hp.liftPath_zero
    · intro t t'; simp_rw [← p.comp_apply, hp.liftPath_lifts]
      exact (F.prop t a ha).trans (F.prop t' a ha).symm
  { toContinuousMap := hp.liftHomotopy F f₀' F_0
    map_zero_left := hp.liftHomotopy_zero F f₀' F_0
    map_one_left := by
      obtain ⟨a, ha, he⟩ := he
      simp_rw [toFun_eq_coe, ← curry_apply]
      refine FunLike.congr_fun (hp.eq_of_comp_eq _ f₁' ?_ a <| (rel 1 a ha).trans he)
      ext a; rw [h₁, Function.comp_apply, curry_apply]
      exact (congr_fun (hp.liftHomotopy_lifts F f₀' _) (1, a)).trans (F.apply_one a)
    prop' := rel }

/-- Two continuous maps from a preconnected space to the total space of a covering map
  are homotopic relative to a set `S` if and only if their compositions with the covering map
  are homotopic relative to `S`, assuming that they agree at a point in `S`. -/
theorem homotopicRel_iff_comp [PreconnectedSpace A] {f₀ f₁ : C(A, E)} {S : Set A}
    (he : ∃ a ∈ S, f₀ a = f₁ a) : f₀.HomotopicRel f₁ S ↔
      (ContinuousMap.comp ⟨p, hp.continuous⟩ f₀).HomotopicRel (.comp ⟨p, hp.continuous⟩ f₁) S :=
  ⟨fun ⟨F⟩ ↦ ⟨F.compContinuousMap _⟩, fun ⟨F⟩ ↦ ⟨hp.liftHomotopyRel F he rfl rfl⟩⟩

/-- Lifting two paths that are homotopic relative to {0,1}
  starting from the same point also ends up in the same point. -/
theorem liftPath_apply_one_eq_of_homotopicRel {γ₀ γ₁ : C(I, X)}
    (h : γ₀.HomotopicRel γ₁ {0,1}) (e : E) (h₀ : γ₀ 0 = p e) (h₁ : γ₁ 0 = p e) :
    hp.liftPath γ₀ e h₀ 1 = hp.liftPath γ₁ e h₁ 1 := by
  obtain ⟨H⟩ := h
  have := hp.liftHomotopyRel (f₀' := hp.liftPath γ₀ e h₀) (f₁' := hp.liftPath γ₁ e h₁) H
    ⟨0, .inl rfl, by simp_rw [liftPath_zero]⟩ (liftPath_lifts _ _ _ _) (liftPath_lifts _ _ _ _)
  rw [← this.eq_fst 0 (.inr rfl), ← this.eq_snd 0 (.inr rfl)]

/-- A covering map induces an injection on all Hom-sets of the fundamental groupoid,
  in particular on the fundamental group. -/
lemma injective_path_homotopic_mapFn (e₀ e₁ : E) :
    Function.Injective fun γ : Path.Homotopic.Quotient e₀ e₁ ↦ γ.mapFn ⟨p, hp.continuous⟩ := by
  refine Quotient.ind₂ fun γ₀ γ₁ ↦ ?_
  dsimp only
  simp_rw [← Path.Homotopic.map_lift]
  iterate 2 rw [@Quotient.eq _ (_)]
  exact (hp.homotopicRel_iff_comp ⟨0, .inl rfl, γ₀.source.trans γ₁.source.symm⟩).mpr


end homotopy_lifting

open CategoryTheory

@[simps] def monodromy : FundamentalGroupoid X ⥤ Type _ where
  obj x := p ⁻¹' {x}
  map {x₀ x₁} γ := _
  map_id := _
  map_comp := _


end IsCoveringMap

-- define monodromy from fundamental groupoid to fiber ..

-- IsGaloisCoveringWith ... arbitrary G with ContinuousConstSmul ..
-- IsGaloisCovering ... G := deck transformations ..

-- Galois correspondence between subgroups and covering spaces ..
-- Galois covering: CoveringMap with deck transformations acting transitively on fibers
-- alternatively: image of fundamental group is normal subgroup .. normal subgroupoid ..
-- this only works if the base is path-connected ..?


-- work with actual paths? refl, symm, trans

  -- forward direction requires HomotopyRel version of ContinuousMap.Homotopy.compContinuousMap
  -- can be used to show injectivity of the morphism on fundamental groups induced by a covering map
  --refine ⟨Nonempty.map fun h ↦ h.compContinuousMap _, ?_⟩



-- injective on fundamental group
-- lifting criterion : locally path connected
-- can be used to lift `E → X` to an automorphism of `E` .. need image in fundamental group to be normal for lift to always exist ..
-- TODO: construct covering spaces from action of fundamental groupoid .. put topology on it
-- in particular, define universal cover


-- two paths with same left+right endpoints don't necessarily lift to paths with same right endpoints
-- but if there's a homotopy rel endpoints between them, then they necessarily lift to same right endpoint
