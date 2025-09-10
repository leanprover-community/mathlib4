/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.restrictScalarsEquiv`: The quotient of `P` as an `S`-submodule is the same
  as the quotient of `P` as an `R`-submodule,
* `Submodule.liftQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂` if the kernel is contained in `p`
* `Submodule.mapQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂ ⧸ q` if the image of `p` is contained
  in `q`

-/

assert_not_exists Cardinal

-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' p'' : Submodule R M)

open LinearMap QuotientAddGroup

namespace Quotient

section Module

variable (S : Type*)

/-- The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,
where `P : Submodule R M`.
-/
def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }

@[simp]
theorem restrictScalarsEquiv_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    restrictScalarsEquiv S P (mk x) = mk x :=
  rfl

@[simp]
theorem restrictScalarsEquiv_symm_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    (restrictScalarsEquiv S P).symm (mk x) = mk x :=
  rfl

end Module

theorem nontrivial_of_lt_top (h : p < ⊤) : Nontrivial (M ⧸ p) := by
  obtain ⟨x, _, notMem_s⟩ := SetLike.exists_of_lt h
  refine ⟨⟨mk x, 0, ?_⟩⟩
  simpa using notMem_s

end Quotient

instance QuotientBot.infinite [Infinite M] : Infinite (M ⧸ (⊥ : Submodule R M)) :=
  Infinite.of_injective Submodule.Quotient.mk fun _x _y h =>
    sub_eq_zero.mp <| (Submodule.Quotient.eq ⊥).mp h

instance QuotientTop.unique : Unique (M ⧸ (⊤ : Submodule R M)) where
  default := 0
  uniq x := Submodule.Quotient.induction_on _ x fun _x =>
    (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top

instance QuotientTop.fintype : Fintype (M ⧸ (⊤ : Submodule R M)) :=
  Fintype.ofSubsingleton 0

variable {p}

theorem subsingleton_quotient_iff_eq_top : Subsingleton (M ⧸ p) ↔ p = ⊤ := by
  constructor
  · rintro h
    refine eq_top_iff.mpr fun x _ => ?_
    have : x - 0 ∈ p := (Submodule.Quotient.eq p).mp (Subsingleton.elim _ _)
    rwa [sub_zero] at this
  · rintro rfl
    infer_instance

theorem unique_quotient_iff_eq_top : Nonempty (Unique (M ⧸ p)) ↔ p = ⊤ :=
  ⟨fun ⟨h⟩ => subsingleton_quotient_iff_eq_top.mp (@Unique.instSubsingleton _ h),
    by rintro rfl; exact ⟨QuotientTop.unique⟩⟩

variable (p)

noncomputable instance Quotient.fintype [Fintype M] (S : Submodule R M) : Fintype (M ⧸ S) :=
  @_root_.Quotient.fintype _ _ _ fun _ _ => Classical.dec _

section

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

theorem strictMono_comap_prod_map :
    StrictMono fun m : Submodule R M ↦ (m.comap p.subtype, m.map p.mkQ) :=
  fun m₁ m₂ ↦ QuotientAddGroup.strictMono_comap_prod_map
    p.toAddSubgroup (a := m₁.toAddSubgroup) (b := m₂.toAddSubgroup)

end

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]
theorem liftQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl

@[simp]
theorem liftQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext; rfl

theorem pi_liftQ_eq_liftQ_pi {ι : Type*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M →ₗ[R] (N i)) {p : Submodule R M} (h : ∀ i, p ≤ ker (f i)) :
    LinearMap.pi (fun i ↦ p.liftQ (f i) (h i)) =
      p.liftQ (LinearMap.pi f) (LinearMap.ker_pi f ▸ le_iInf h) := by
  ext x i
  simp

/-- Special case of `submodule.liftQ` when `p` is the span of `x`. In this case, the condition on
`f` simply becomes vanishing at `x`. -/
def liftQSpanSingleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
  (R ∙ x).liftQ f <| by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]

@[simp]
theorem liftQSpanSingleton_apply (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
    liftQSpanSingleton x f h (Quotient.mk y) = f y :=
  rfl

@[simp]
theorem range_mkQ : range p.mkQ = ⊤ :=
  eq_top_iff'.2 <| by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp]
theorem ker_mkQ : ker p.mkQ = p := by ext; simp

theorem le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p ≤ comap p.mkQ p' := by
  simpa using (comap_mono bot_le : ker p.mkQ ≤ comap p.mkQ p')

@[simp]
theorem mkQ_map_self : map p.mkQ p = ⊥ := by
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ]

@[simp]
theorem comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p ⊔ p' := by simp [comap_map_eq, sup_comm]

@[simp]
theorem map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤ := by
  simp only [LinearMap.map_eq_top_iff p.range_mkQ, sup_comm, ker_mkQ]

variable (q : Submodule R₂ M₂)

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) : M ⧸ p →ₛₗ[τ₁₂] M₂ ⧸ q :=
  p.liftQ (q.mkQ.comp f) <| by simpa [ker_comp] using h

@[simp]
theorem mapQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
    mapQ p q f h (Quotient.mk x) = Quotient.mk (f x) :=
  rfl

theorem mapQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapQ p q f h).comp p.mkQ = q.mkQ.comp f := by
  ext x; rfl

@[simp]
theorem mapQ_zero (h : p ≤ q.comap (0 : M →ₛₗ[τ₁₂] M₂) := (by simp)) :
    p.mapQ q (0 : M →ₛₗ[τ₁₂] M₂) h = 0 := by
  ext
  simp

/-- Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → M₃` inducing
`mapQ f : M ⧸ p → M₂ ⧸ p₂` and `mapQ g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapQ (g ∘ f) = (mapQ g) ∘ (mapQ f)`. -/
theorem mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
    (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : p ≤ p₂.comap f) (hg : p₂ ≤ p₃.comap g)
    (h := hf.trans (comap_mono hg)) :
    p.mapQ p₃ (g.comp f) h = (p₂.mapQ p₃ g hg).comp (p.mapQ p₂ f hf) := by
  ext
  simp

@[simp]
theorem mapQ_id (h : p ≤ p.comap LinearMap.id := (by rw [comap_id])) :
    p.mapQ p LinearMap.id h = LinearMap.id := by
  ext
  simp

theorem mapQ_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
    (h' : p ≤ p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) :
    p.mapQ p (f ^ k) h' = p.mapQ p f h ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    simp only [Module.End.iterate_succ]
    rw [mapQ_comp, ih]

theorem comap_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftQ f h) = (q.comap f).map (mkQ p) :=
  le_antisymm (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
    (by rw [map_le_iff_le_comap, ← comap_comp, liftQ_mkQ])

theorem map_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p)) :
    q.map (p.liftQ f h) = (q.comap p.mkQ).map f :=
  le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
    (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨Quotient.mk x, hxq, rfl⟩)

theorem ker_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f h) = (ker f).map (mkQ p) :=
  comap_liftQ _ _ _ _

theorem range_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) :
    range (p.liftQ f h) = range f := by simpa only [range_eq_map] using map_liftQ _ _ _ _

theorem ker_liftQ_eq_bot (f : M →ₛₗ[τ₁₂] M₂) (h) (h' : ker f ≤ p) : ker (p.liftQ f h) = ⊥ := by
  rw [ker_liftQ, le_antisymm h h', mkQ_map_self]

theorem ker_liftQ_eq_bot' (f : M →ₛₗ[τ₁₂] M₂) (h : p = ker f) :
    ker (p.liftQ f (le_of_eq h)) = ⊥ :=
  ker_liftQ_eq_bot p f h.le h.ge

section

variable {p p' p''}

/-- The linear map from the quotient by a smaller submodule to the quotient by a larger submodule.

This is the `Submodule.Quotient` version of `Quot.Factor`

When the two submodules are of the form `I ^ m • ⊤` and `I ^ n • ⊤` and `n ≤ m`,
please refer to the dedicated version `Submodule.factorPow`. -/
abbrev factor (H : p ≤ p') : M ⧸ p →ₗ[R] M ⧸ p' :=
  mapQ _ _ LinearMap.id H

@[simp]
theorem factor_mk (H : p ≤ p') (x : M) : factor H (mkQ p x) = mkQ p' x :=
  rfl

@[simp]
theorem factor_comp_mk (H : p ≤ p') : (factor H).comp (mkQ p) = mkQ p' := by
  ext x
  rw [LinearMap.comp_apply, factor_mk]

@[simp]
theorem factor_comp (H1 : p ≤ p') (H2 : p' ≤ p'') :
    (factor H2).comp (factor H1) = factor (H1.trans H2) := by
  ext
  simp

@[simp]
theorem factor_comp_apply (H1 : p ≤ p') (H2 : p' ≤ p'') (x : M ⧸ p) :
    factor H2 (factor H1 x) = factor (H1.trans H2) x := by
  rw [← comp_apply]
  simp

lemma factor_surjective (H : p ≤ p') : Function.Surjective (factor H) := by
  intro x
  use Quotient.mk x.out
  exact Quotient.out_eq x

end

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def comapMkQRelIso : Submodule R (M ⧸ p) ≃o Set.Ici p where
  toFun p' := ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
  left_inv p' := map_comap_eq_self <| by simp
  right_inv := fun ⟨q, hq⟩ => Subtype.ext <| by simpa [comap_map_mkQ p]
  map_rel_iff' := comap_le_comap_iff <| range_mkQ _

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· ≤ ·) _)

@[simp]
theorem comapMkQOrderEmbedding_eq (p' : Submodule R (M ⧸ p)) :
    comapMkQOrderEmbedding p p' = comap p.mkQ p' :=
  rfl

theorem span_preimage_eq [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty)
    (h₁ : s ⊆ range f) : span R (f ⁻¹' s) = (span R₂ s).comap f := by
  suffices (span R₂ s).comap f ≤ span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  have hk : ker f ≤ span R (f ⁻¹' s) := by
    let y := Classical.choose h₀
    have hy : y ∈ s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff] at hy
    exact Set.Subset.trans subset_span (span_mono (Set.preimage_mono hy))
  rw [← left_eq_sup] at hk
  rw [coe_range f] at h₁
  rw [hk, ← LinearMap.map_le_map_iff, map_span, map_comap_eq, Set.image_preimage_eq_of_subset h₁]
  exact inf_le_right

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`. -/
@[simps]
def Quotient.equiv {N : Type*} [AddCommGroup N] [Module R N] (P : Submodule R M)
    (Q : Submodule R N) (f : M ≃ₗ[R] N) (hf : P.map f = Q) : (M ⧸ P) ≃ₗ[R] N ⧸ Q :=
  { P.mapQ Q (f : M →ₗ[R] N) fun _ hx => hf ▸ Submodule.mem_map_of_mem hx with
    toFun := P.mapQ Q (f : M →ₗ[R] N) fun _ hx => hf ▸ Submodule.mem_map_of_mem hx
    invFun :=
      Q.mapQ P (f.symm : N →ₗ[R] M) fun x hx => by
        rw [← hf, Submodule.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa
    left_inv := fun x => Submodule.Quotient.induction_on _ x (by simp)
    right_inv := fun x => Submodule.Quotient.induction_on _ x (by simp) }

@[simp]
theorem Quotient.equiv_symm {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (P : Submodule R M) (Q : Submodule R N) (f : M ≃ₗ[R] N)
    (hf : P.map f = Q) :
    (Quotient.equiv P Q f hf).symm =
      Quotient.equiv Q P f.symm ((Submodule.map_symm_eq_iff f).mpr hf) :=
  rfl

@[simp]
theorem Quotient.equiv_trans {N O : Type*} [AddCommGroup N] [Module R N] [AddCommGroup O]
    [Module R O] (P : Submodule R M) (Q : Submodule R N) (S : Submodule R O) (e : M ≃ₗ[R] N)
    (f : N ≃ₗ[R] O) (he : P.map e = Q) (hf : Q.map f = S) (hef : P.map (e.trans f) = S) :
    Quotient.equiv P S (e.trans f) hef =
      (Quotient.equiv P Q e he).trans (Quotient.equiv Q S f hf) := by
  ext
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  rw [mapQ_comp, LinearMap.comp_apply]

end Submodule

open Submodule

namespace LinearMap

section Ring

variable {R M R₂ M₂ R₃ M₃ : Type*}
variable [Ring R] [Ring R₂] [Ring R₃]
variable [AddCommMonoid M] [AddCommGroup M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] [RingHomSurjective τ₁₂]

theorem range_mkQ_comp (f : M →ₛₗ[τ₁₂] M₂) : (range f).mkQ.comp f = 0 :=
  LinearMap.ext fun x => by simp

theorem ker_le_range_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    ker g ≤ range f ↔ (range f).mkQ.comp (ker g).subtype = 0 := by
  rw [← range_le_ker_iff, Submodule.ker_mkQ, Submodule.range_subtype]

/-- An epimorphism is surjective. -/
theorem range_eq_top_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : M₂ →ₗ[R₂] M₂ ⧸ (range f), u.comp f = v.comp f → u = v) : range f = ⊤ := by
  have h₁ : (0 : M₂ →ₗ[R₂] M₂ ⧸ (range f)).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkQ (range f), ← h 0 (range f).mkQ (Eq.trans h₁ (range_mkQ_comp _).symm)]
  exact ker_zero

end Ring

end LinearMap

open LinearMap

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
  LinearEquiv.ofLinear (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _) <|
    p.quot_hom_ext _ LinearMap.id fun _ => rfl

@[simp]
theorem quotEquivOfEqBot_apply_mk (hp : p = ⊥) (x : M) :
    p.quotEquivOfEqBot hp (Quotient.mk x) = x :=
  rfl

@[simp]
theorem quotEquivOfEqBot_symm_apply (hp : p = ⊥) (x : M) :
    (p.quotEquivOfEqBot hp).symm x = (Quotient.mk x) :=
  rfl

@[simp]
theorem coe_quotEquivOfEqBot_symm (hp : p = ⊥) :
    ((p.quotEquivOfEqBot hp).symm : M →ₗ[R] M ⧸ p) = p.mkQ :=
  rfl

@[simp]
theorem Quotient.equiv_refl (P : Submodule R M) (Q : Submodule R M)
    (hf : P.map (LinearEquiv.refl R M : M →ₗ[R] M) = Q) :
    Quotient.equiv P Q (LinearEquiv.refl R M) hf = quotEquivOfEq _ _ (by simpa using hf) :=
  rfl

end Submodule

end Ring

section CommRing

variable {R M M₂ : Type*} {r : R} {x y : M} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R M₂] (p : Submodule R M) (q : Submodule R M₂)

namespace Submodule

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear. -/
def mapQLinear : compatibleMaps p q →ₗ[R] M ⧸ p →ₗ[R] M₂ ⧸ q where
  toFun f := mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl

end Submodule

end CommRing
