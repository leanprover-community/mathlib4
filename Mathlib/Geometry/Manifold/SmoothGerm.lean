import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Topology.Germ

noncomputable section

open Filter Set

open scoped Manifold Topology BigOperators

-- FIXME: move to Manifold/Algebra/SmoothFunctions (yields universe errors)
section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G] [SmoothMul I' G]

@[to_additive]
theorem SmoothMap.coe_prod {ι : Type*} (f : ι → C^∞⟮I, N; I', G⟯) (s : Finset ι) :
    ⇑(∏ i in s, f i) = ∏ i in s, ⇑(f i) :=
  map_prod (SmoothMap.coeFnMonoidHom : C^∞⟮I, N; I', G⟯ →* N → G) f s

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H N] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {N' : Type*} [TopologicalSpace N']
  [ChartedSpace H'' N'] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Type*)
  [AddCommGroup G] [Module ℝ G]

def RingHom.germOfContMDiffMap (x : N) : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ →+* Germ (𝓝 x) ℝ :=
  RingHom.comp (Germ.coeRingHom _) SmoothMap.coeFnRingHom

def smoothGerm (x : N) : Subring (Germ (𝓝 x) ℝ) :=
  (RingHom.germOfContMDiffMap I x).range

instance (x : N) : Coe C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ (smoothGerm I x) :=
  ⟨fun f ↦ ⟨(f : N → ℝ), ⟨f, rfl⟩⟩⟩

@[simp]
theorem smoothGerm.coe_coe (f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (x : N) :
    ((f : smoothGerm I x) : (𝓝 x).Germ ℝ) = (f : (𝓝 x).Germ ℝ) :=
  rfl

@[simp]
theorem smoothGerm.coe_sum {ι} (f : ι → C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (s : Finset ι) (x : N) :
    ((∑ i in s, f i : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) : smoothGerm I x) = ∑ i in s, (f i : smoothGerm I x) :=
  map_sum (RingHom.rangeRestrict (RingHom.germOfContMDiffMap I x)) f s

@[simp]
theorem smoothGerm.coe_eq_coe (f g : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) {x : N} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
    (f : smoothGerm I x) = (g : smoothGerm I x) := by
  ext
  apply Quotient.sound
  exact h

example (x : N) : Module (smoothGerm I x) (Germ (𝓝 x) G) := by infer_instance

example (x : N) : Module (Germ (𝓝 x) ℝ) (Germ (𝓝 x) F) := by infer_instance

-- def linear_map.germ_of_cont_mdiff_map (x : N) :
--   C^∞⟮I, N; 𝓘(ℝ, F), F⟯ →ₛₗ[(germ.coe_ring_hom (𝓝 x) : (N → ℝ) →+* germ (𝓝 x) ℝ).comp (pi.const_ring_hom N ℝ)] germ (𝓝 x) F :=
-- sorry -- linear_map.comp (germ.coe_linear_map _) smooth_map.coe_fn_linear_map
/-
def smooth_germ_vec (x : N) : submodule (smooth_germ I x) (germ (𝓝 x) F) :=
-- linear_map.range (linear_map.germ_of_cont_mdiff_map I F x)
{ carrier := {φ : germ (𝓝 x) F | ∃ f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, φ = (f : N → F)},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

instance (x : N) : has_coe C^∞⟮I, N; 𝓘(ℝ, F), F⟯ (smooth_germ_vec I F x) :=
⟨λ f, ⟨(f : N → F), ⟨f, rfl⟩⟩⟩

variables {I F}

@[elab_as_eliminator]
lemma smooth_germ_vec.induction_on {x : N} {P : germ (𝓝 x) F → Prop}
  (h : ∀  f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, P (f : N → F)) :
  ∀ φ ∈ smooth_germ_vec I F x, P φ :=
begin
  rintros _ ⟨f, rfl⟩,
  apply h
end

@[elab_as_eliminator]
lemma smooth_germ.induction_on {x : N} {P : germ (𝓝 x) ℝ → Prop}
  (h : ∀  f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯, P (f : N → ℝ)) :
  ∀ φ ∈ smooth_germ I x, P φ :=
begin
  rintros _ ⟨f, rfl⟩,
  apply h
end

-- We may also need versions of the above two lemmas for using the coe_to_sort
-- `∀ φ : smooth_germ I x`, maybe even a tactic, but let's wait to see if they are really needed.

lemma convex_smooth_germ_vec (x : N) : convex (smooth_germ I x)
  (smooth_germ_vec I F x : set $ germ (𝓝 x) F) :=
begin
  refine smooth_germ_vec.induction_on _,
  intros f,
  refine smooth_germ_vec.induction_on _,
  rintros g ⟨_, ⟨b, rfl⟩⟩ ⟨_, ⟨c, rfl⟩⟩ hb hc hbc,
  exact ⟨b • f + c • g, rfl⟩,
end
-/
end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] [T2Space M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {HG : Type*} [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ G HG) {N : Type*} [TopologicalSpace N] [ChartedSpace HG N]
  [SmoothManifoldWithCorners IG N]

local notation "𝓒" => ContMDiff I 𝓘(ℝ, F)

local notation "𝓒_on" => ContMDiffOn I 𝓘(ℝ, F)

def smoothGerm.valueOrderRingHom (x : N) : smoothGerm IG x →+*o ℝ :=
  Filter.Germ.valueOrderRingHom.comp <| Subring.orderedSubtype _

def smoothGerm.valueRingHom (x : N) : smoothGerm IG x →+* ℝ :=
  Filter.Germ.valueRingHom.comp <| Subring.subtype _

theorem smoothGerm.valueOrderRingHom_toRingHom (x : N) :
    (smoothGerm.valueOrderRingHom IG x).toRingHom = smoothGerm.valueRingHom IG x :=
  rfl

def Filter.Germ.valueₛₗ {F} [AddCommMonoid F] [Module ℝ F] (x : N) :
    Germ (𝓝 x) F →ₛₗ[smoothGerm.valueRingHom IG x] F :=
  { Filter.Germ.valueAddHom with
    toFun := Filter.Germ.value
    map_smul' := fun φ ψ ↦ (φ : Germ (𝓝 x) ℝ).value_smul ψ }

variable (I)

protected def Filter.Germ.ContMDiffAt' {x : M} (φ : Germ (𝓝 x) N) (n : ℕ∞) : Prop :=
  Quotient.liftOn' φ (fun f ↦ ContMDiffAt I IG n f x) fun f g h ↦
    propext <| by
      constructor
      all_goals refine fun H ↦ H.congr_of_eventuallyEq ?_
      exacts [h.symm, h]

/-- The predicate selecting germs of `cont_mdiff_at` functions.
TODO: merge with the next def that generalizes target space -/
protected nonrec def Filter.Germ.ContMDiffAt {x : M} (φ : Germ (𝓝 x) F) (n : ℕ∞) : Prop :=
  φ.ContMDiffAt' I 𝓘(ℝ, F) n

-- currently unused
nonrec def Filter.Germ.mfderiv {x : M} (φ : Germ (𝓝 x) N) :
    TangentSpace I x →L[ℝ] TangentSpace IG φ.value :=
  @Quotient.hrecOn _ (germSetoid (𝓝 x) N)
    (fun φ : Germ (𝓝 x) N ↦ TangentSpace I x →L[ℝ] TangentSpace IG φ.value) φ
    (fun f ↦ mfderiv I IG f x) fun _f _g hfg ↦ heq_of_eq (EventuallyEq.mfderiv_eq hfg : _)

variable {I}

theorem smoothGerm.contMDiffAt {x : M} (φ : smoothGerm I x) {n : ℕ∞} :
    (φ : Germ (𝓝 x) ℝ).ContMDiffAt I n := by rcases φ with ⟨_, g, rfl⟩; apply g.smooth.of_le le_top

protected nonrec theorem Filter.Germ.ContMDiffAt.add {x : M} {φ ψ : Germ (𝓝 x) F} {n : ℕ∞} :
    φ.ContMDiffAt I n → ψ.ContMDiffAt I n → (φ + ψ).ContMDiffAt I n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg ↦ hf.add hg

protected nonrec theorem Filter.Germ.ContMDiffAt.smul {x : M} {φ : Germ (𝓝 x) ℝ} {ψ : Germ (𝓝 x) F}
    {n : ℕ∞} : φ.ContMDiffAt I n → ψ.ContMDiffAt I n → (φ • ψ).ContMDiffAt I n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg ↦ hf.smul hg

theorem Filter.Germ.ContMDiffAt.sum {x : M} {ι} {s : Finset ι} {n : ℕ∞} {f : ι → Germ (𝓝 x) F}
    (h : ∀ i ∈ s, (f i).ContMDiffAt I n) : (∑ i in s, f i).ContMDiffAt I n := by
  classical
  induction' s using Finset.induction_on with φ s hφs hs
  · rw [Finset.sum_empty]; exact contMDiffAt_const
  simp only [Finset.mem_insert, forall_eq_or_imp] at h
  rw [Finset.sum_insert hφs]
  exact h.1.add (hs h.2)

end

section

variable {E₁ E₂ E₃ E₄ F : Type*}

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]

variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]

variable [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]

variable [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {H₁ M₁ H₂ M₂ H₃ M₃ H₄ M₄ : Type*}

variable [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)

variable [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [SmoothManifoldWithCorners I₁ M₁]

variable [SigmaCompactSpace M₁] [T2Space M₁]

variable [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)

variable [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [SmoothManifoldWithCorners I₂ M₂]

variable [TopologicalSpace H₃] (I₃ : ModelWithCorners ℝ E₃ H₃)

variable [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [SmoothManifoldWithCorners I₃ M₃]

variable [TopologicalSpace H₄] (I₄ : ModelWithCorners ℝ E₄ H₄)

variable [TopologicalSpace M₄] [ChartedSpace H₄ M₄] [SmoothManifoldWithCorners I₄ M₄]

local notation "𝓒" => ContMDiff (I₁.prod I₂) 𝓘(ℝ, F)

local notation "𝓒_on" => ContMDiffOn (I₁.prod I₂) 𝓘(ℝ, F)

open scoped Filter

open Function

-- TODO: generalize the next def?
def Filter.Germ.ContMDiffAtProd {x : M₁} (φ : Germ (𝓝 x) (M₂ → F)) (n : ℕ∞) : Prop :=
  Quotient.liftOn' φ (fun f ↦ ∀ y : M₂, ContMDiffAt (I₁.prod I₂) 𝓘(ℝ, F) n (uncurry f) (x, y))
    fun f g h ↦ propext <| by
        change {x' | f x' = g x'} ∈ 𝓝 x at h
        constructor
        all_goals
          refine fun H y ↦ (H y).congr_of_eventuallyEq ?_
          clear H
          replace h : {x' | f x' = g x'} ×ˢ (univ : Set M₂) ∈ 𝓝 x ×ˢ 𝓝 y := prod_mem_prod h univ_mem
          rw [← nhds_prod_eq] at h
          apply mem_of_superset h
          rintro ⟨x', y'⟩ ⟨hx' : f x' = g x', -⟩
          simp only [mem_setOf_eq, uncurry_apply_pair]
          apply congr_fun
        exacts [hx'.symm, hx']

/- potential generalization of the above
def filter.germ.cont_mdiff_at_comp {x : M₁} (φ : germ (𝓝 x) M₂) (n : ℕ∞)
  (g : M₂ → M₃) (h : M₄ → M₁) : Prop :=
quotient.lift_on' φ (λ f, ∀ y ∈ h⁻¹' {x}, cont_mdiff_at I₄ I₃ n (g ∘ f ∘ h) y) (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventually_eq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_setOf_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)
-/
variable {I₁ I₂}

theorem Filter.Germ.ContMDiffAtProd.add {x : M₁} {φ ψ : Germ (𝓝 x) <| M₂ → F} {n : ℕ∞} :
    φ.ContMDiffAtProd I₁ I₂ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ + ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦ (hf y).add (hg y)

theorem Filter.Germ.ContMDiffAtProd.smul {x : M₁} {φ : Germ (𝓝 x) <| M₂ → ℝ}
    {ψ : Germ (𝓝 x) <| M₂ → F} {n : ℕ∞} :
    φ.ContMDiffAtProd I₁ I₂ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ • ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦ (hf y).smul (hg y)

theorem Filter.Germ.ContMDiffAt.smul_prod {x : M₁} {φ : Germ (𝓝 x) ℝ} {ψ : Germ (𝓝 x) (M₂ → F)}
    {n : ℕ∞} : φ.ContMDiffAt I₁ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ • ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦
    .smul (.comp _ hf contMDiffAt_fst) (hg y)

theorem Filter.Germ.ContMDiffAtProd.sum {x : M₁} {ι} {s : Finset ι} {n : ℕ∞}
    {f : ι → Germ (𝓝 x) (M₂ → F)} (h : ∀ i ∈ s, (f i).ContMDiffAtProd I₁ I₂ n) :
    (∑ i in s, f i).ContMDiffAtProd I₁ I₂ n := by
  classical
  induction' s using Finset.induction_on with φ s hφs hs
  · rw [Finset.sum_empty]; intro y; exact contMDiffAt_const
  simp only [Finset.mem_insert, forall_eq_or_imp] at h
  rw [Finset.sum_insert hφs]
  exact h.1.add (hs h.2)

end
