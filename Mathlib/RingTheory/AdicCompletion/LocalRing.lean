/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Basic Properties of Complete Local Ring

In this file we prove that for `I` an finitely generated ideal of `R`,
`AdicCompletion I M` is adic complete with respect to `I`. Then we use this to deduce for
Noetherian local ring `R`, `AdicCompletion (maximalIdeal R) R` is always a complete local ring.

-/

public section

variable {R : Type*} [CommRing R]

open Ideal Quotient

theorem isLocalRing_of_isAdicComplete_maximal (m : Ideal R) [m.IsMaximal] [IsAdicComplete m R] :
    IsLocalRing R := by
  refine IsLocalRing.of_unique_max_ideal ⟨m, ‹_›, fun m' hm' ↦ ?_⟩
  symm
  apply Ideal.IsMaximal.eq_of_le ‹_› IsPrime.ne_top'
  exact (IsAdicComplete.le_jacobson_bot m).trans (by
    simpa [Ideal.jacobson_bot] using Ring.jacobson_le_of_isMaximal m')

open IsLocalRing

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

lemma AdicCompletion.ker_eval_eq_range (n : ℕ) : (AdicCompletion.eval I M n).ker =
    (AdicCompletion.map I ((I ^ n) • (⊤ : Submodule R M)).subtype).range.restrictScalars R := by
  let InM := (I ^ n) • (⊤ : Submodule R M)
  have comap_eq (m : ℕ) : (I ^ (m + n) • (⊤ : Submodule R M)).comap InM.subtype =
    (I ^ m) • (⊤ : Submodule R InM) := by
    ext x
    simp [Submodule.mem_smul_top_iff, InM, smul_smul, pow_add]
  let shift (m : ℕ) : InM ⧸ ((I ^ m) • (⊤ : Submodule R InM)) →ₗ[R]
    M ⧸ ((I ^ (m + n) • (⊤ : Submodule R M))) :=
    Submodule.mapQ _ _ InM.subtype (le_of_eq (comap_eq m).symm)
  have shift_inj (m : ℕ) : Function.Injective (shift m) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on
    simp only [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
      shift, ← Submodule.mem_comap, comap_eq] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have shift_comm {m l : ℕ} (hle : m ≤ l) :
    (transitionMap I M (add_le_add_left hle n)).comp (shift l) =
    (shift m).comp (transitionMap I InM hle) := by
    ext x
    simp [shift]
  have shift_range (m : ℕ) : (shift m).range = (transitionMap I M (Nat.le_add_left n m)).ker := by
    ext x
    refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ?_⟩
    · rcases Submodule.Quotient.mk_surjective _ y with ⟨z, hz⟩
      simp [← hy, ← hz, LinearMap.mem_ker, shift]
    · rcases Submodule.Quotient.mk_surjective _ x with ⟨y, hy⟩
      simp only [← hy, LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.id_coe, id_eq,
        Submodule.Quotient.mk_eq_zero] at h
      use Submodule.Quotient.mk ⟨y, h⟩
      simp [shift, hy]
  change _ = ((AdicCompletion.map I InM.subtype).restrictScalars R).range
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have mem (m : ℕ) : x.1 (m + n) ∈ (shift m).range := by
      simpa [shift_range] using hx
    let y_aux (m : ℕ) : InM ⧸ (I ^ m • (⊤ : Submodule R InM)) := Classical.choose (mem m)
    have y_aux_spec (m : ℕ) : (shift m) (y_aux m) = x.1 (m + n) :=
      Classical.choose_spec (mem m)
    refine ⟨⟨y_aux, fun {m n} hle ↦ ?_⟩, ?_⟩
    · apply shift_inj m
      rw [← LinearMap.comp_apply, ← shift_comm hle]
      simp [y_aux_spec]
    · ext m
      simp only [LinearMap.coe_restrictScalars, map_val_apply]
      rw [← x.2 (Nat.le_add_right m n), ← y_aux_spec m]
      rcases Submodule.Quotient.mk_surjective _ (y_aux m) with ⟨z, hz⟩
      simp [← hz, shift]
  · rcases hx with ⟨y, hy⟩
    rcases Submodule.Quotient.mk_surjective _ (y.1 n) with ⟨z, hz⟩
    simp [← hy, ← hz]

lemma LinearMap.lsum_smul_id_range {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → R) (I : Ideal R)
    (eq : Ideal.span (Set.range f) = I) :
    ((LinearMap.lsum R _ R) (fun (i : ι) ↦ (f i) • LinearMap.id)).range =
    I • (⊤ : Submodule R M) := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, hy⟩
    simp only [← hy, lsum_apply, coe_sum, coe_comp, coe_proj, Finset.sum_apply, Function.comp_apply,
      Function.eval, smul_apply, id_coe, id_eq]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    simpa [← eq] using mem_span_range_self
  · refine Submodule.smul_induction_on hx (fun r memr m _ ↦ ?_) (fun x y hx hy ↦ add_mem hx hy)
    rw [← eq] at memr
    refine Submodule.span_induction (fun r hr ↦ ?_) (by simp)
      (fun x y memx memy hx hy ↦ by simpa [add_smul] using add_mem hx hy)
      (fun r s mems mem ↦ by simpa [← smul_smul] using Submodule.smul_mem _ r mem) memr
    rcases hr with ⟨i, hi⟩
    use Pi.single i m
    simp [Pi.single_apply, hi]

lemma AdicCompletion.le_ker_eval (n : ℕ) :
    (I ^ n) • (⊤ : Submodule R _) ≤ (AdicCompletion.eval I M n).ker := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r memr m _ ↦ ?_) (fun x y hx hy ↦ add_mem hx hy)
  simpa using Module.isTorsionBySet_quotient_ideal_smul M (I ^ n) (a := ⟨r, memr⟩)

lemma AdicCompletion.ker_eval (fg : I.FG) (n : ℕ) :
    (AdicCompletion.eval I M n).ker = (I ^ n) • (⊤ : Submodule R _) := by
  have fg' : (I ^ n).FG := fg.pow
  classical
  let _ : Fintype (I ^ n).generators := (Submodule.FG.finite_generators fg').fintype
  let g : ((I ^ n).generators → M) →ₗ[R] M :=
    (LinearMap.lsum R _ R) (fun (r : (I ^ n).generators) ↦ r.1 • LinearMap.id)
  have rg : g.range = (I ^ n) • (⊤ : Submodule R M) := by
    apply LinearMap.lsum_smul_id_range
    simpa using (I ^ n).span_generators
  let gr := g.codRestrict ((I ^ n) • (⊤ : Submodule R M)) (by simp [← rg])
  have surjgr : Function.Surjective gr := by
    intro x
    rcases (Submodule.ext_iff.mp rg x.1).mpr x.2 with ⟨y, hy⟩
    exact ⟨y, SetCoe.ext hy⟩
  have req : (AdicCompletion.map I ((I ^ n) • (⊤ : Submodule R M)).subtype).range =
    ((AdicCompletion.map I g).comp (piEquivOfFintype I _).symm.toLinearMap).range := by
    have : ((I ^ n) • (⊤ : Submodule R M)).subtype.comp gr = g := g.subtype_comp_codRestrict _ _
    rw [LinearEquiv.range_comp, ← this, ← map_comp, LinearMap.range_comp, LinearMap.range_eq_map,
      LinearMap.range_eq_top_of_surjective _ (AdicCompletion.map_surjective I surjgr)]
  have compeq : ((AdicCompletion.map I g).comp
    (piEquivOfFintype I _).symm.toLinearMap).restrictScalars R =
    (LinearMap.lsum R _ R) (fun (r : (I ^ n).generators) ↦ r.1 • LinearMap.id) := by
    ext r x n
    have : (r.1 • (mk I M) x).1 n = r.1 • ((mk I M) x).1 n:= rfl
    simp [piEquivOfFintype, Pi.single_apply, g, this]
  rw [AdicCompletion.ker_eval_eq_range, req, ← LinearMap.range_restrictScalars, compeq]
  apply LinearMap.lsum_smul_id_range
  simpa using (I ^ n).span_generators

lemma AdicCompletion.isAdicComplete (fg : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  haus' x hx := by
    ext n
    simpa using (AdicCompletion.le_ker_eval I M n) ((Submodule.Quotient.mk_eq_zero _).mp (hx n))
  prec' f hf := by
    refine ⟨⟨fun n ↦ (f n).1 n, fun {m l} hle ↦ ?_⟩, fun n ↦ ?_⟩
    · have := (AdicCompletion.le_ker_eval I M m) (SModEq.sub_mem.mp (hf hle))
      simp only [LinearMap.mem_ker, coe_eval, val_sub, Pi.sub_apply, sub_eq_zero] at this
      simp [this]
    · simp [SModEq.sub_mem, ← AdicCompletion.ker_eval I M fg]

lemma AdicCompletion.isAdicComplete_self (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) where
  haus' x hx := by
    ext n
    have mem : x ∈ (eval I R n).ker := by
      apply AdicCompletion.le_ker_eval I R n
      rw [Ideal.smul_top_eq_map, Ideal.map_pow, Submodule.restrictScalars_mem]
      simpa using (Submodule.Quotient.mk_eq_zero _).mp (hx n)
    simpa using mem
  prec' f hf := by
    refine ⟨⟨fun n ↦ (f n).1 n, fun {m l} hle ↦ ?_⟩, fun n ↦ ?_⟩
    · have eq := (SModEq.sub_mem.mp (hf hle))
      simp only [← Ideal.map_pow, smul_eq_mul, mul_top] at eq
      rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at eq
      have := AdicCompletion.le_ker_eval I R m eq
      simp only [smul_eq_mul, eval, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, val_sub,
        Pi.sub_apply, sub_eq_zero] at this
      simpa [this] using (f l).2 hle
    · simp only [smul_eq_mul, mul_top, SModEq.sub_mem, ← Ideal.map_pow]
      rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
      simp [← AdicCompletion.ker_eval I R fg, eval]

lemma AdicCompletion.isMaximal_map (m : Ideal R) [m.IsMaximal] (le : I ≤ m) (fg : I.FG) :
    (m.map (algebraMap R (AdicCompletion I R))).IsMaximal := by
  have compeq : (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
    (Ideal.Quotient.mk I) := by
    ext
    simp
  have kerle : RingHom.ker (evalOneₐ I).toRingHom ≤ m.map (algebraMap R (AdicCompletion I R)) := by
    intro x hx
    have : x ∈ (AdicCompletion.eval I R 1).ker := by
      have eq : I ^ 1 * ⊤ = I := by simp
      simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, RingHom.coe_coe, ← factorₐ_evalₐ_one,
        pow_one, smul_eq_mul, mul_top, le_refl, ← factor_eval_eq_evalₐ, Submodule.mapQ_eq_factor,
        Submodule.factor_eq_factor, factor_comp_apply] at hx
      have : (factor (le_of_eq eq.symm)) ((factor (le_of_eq eq)) ((eval I R 1) x)) = 0 := by
        simp [hx]
      simpa using this
    simp only [smul_eq_mul, AdicCompletion.ker_eval I R fg 1, pow_one, smul_top_eq_map,
      Submodule.restrictScalars_mem] at this
    exact Ideal.map_mono le this
  have : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← compeq, ← Ideal.map_map,
      Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I),
      eq_comm, sup_eq_left]
    exact kerle
  rw [this]
  let _ : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)

instance [IsNoetherianRing R] [IsLocalRing R] : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  @isLocalRing_of_isAdicComplete_maximal _ _
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
    (AdicCompletion.isMaximal_map _ _ (le_refl _) (fg_of_isNoetherianRing (maximalIdeal R)))
    (AdicCompletion.isAdicComplete_self _ (fg_of_isNoetherianRing (maximalIdeal R)))

lemma AdicCompletion.maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm

lemma AdicCompletion.mem_maximalIdeal_iff_eval_one_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ↔ x.1 1 = 0 := by
  have : (AdicCompletion.eval (maximalIdeal R) R 1).ker =
    (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    simp [AdicCompletion.ker_eval _ _ (maximalIdeal R).fg_of_isNoetherianRing]
  rw [maximalIdeal_eq_map, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  simp [← this, eval]

instance [IsNoetherianRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  simp [AdicCompletion.maximalIdeal_eq_map]

instance [IsNoetherianRing R] [IsLocalRing R] : IsAdicComplete
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact AdicCompletion.isAdicComplete_self _ (maximalIdeal R).fg_of_isNoetherianRing

variable (R) in
lemma AdicCompletion.residueField_map_bijective [IsNoetherianRing R] [IsLocalRing R] :
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  rcases residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use residue R z
  rw [IsLocalRing.ResidueField.map_residue, ← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [maximalIdeal_eq_map, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) z - y ∈
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    change (of (maximalIdeal R) R z) - y ∈ _
    rw [← AdicCompletion.ker_eval _ R (maximalIdeal R).fg_of_isNoetherianRing 1]
    simpa [eval, sub_eq_zero] using hz
  simpa using this

lemma AdicCompletion.spanFinrank_maximalIdeal_eq [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  have fg : (maximalIdeal R).FG := fg_of_isNoetherianRing (maximalIdeal R)
  have comapeq : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).comap
    (algebraMap R (AdicCompletion (maximalIdeal R) R)) = maximalIdeal R :=
    ((IsLocalRing.local_hom_TFAE _).out 0 4).mp (by infer_instance)
  let f := Ideal.mapCotangent _ _ (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
    (le_of_eq comapeq.symm)
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    simp only [← hm', mapCotangent_toCotangent, Algebra.ofId_apply, toCotangent_eq_zero,
      maximalIdeal_eq_map, ← Ideal.map_pow, f] at hm
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      ← AdicCompletion.ker_eval _ _ fg] at hm
    have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) m'.1 = of _ R m'.1 := rfl
    simp only [smul_eq_mul, eval, this, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
      of_apply, Submodule.mkQ_apply, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa [← hm', toCotangent_eq_zero] using hm
  have surj : Function.Surjective f := by
    intro m
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
    have lmem : (transitionMap (maximalIdeal R) R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 :=
      m'.1.2 (Nat.le_succ 1)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
      Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, mk_eq_mk, factor_mk, pow_one,
      (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2, eq_zero_iff_mem, mul_top] at lmem
    use (maximalIdeal R).toCotangent ⟨l, lmem⟩
    simp only [mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', toCotangent_eq, f]
    change (of (maximalIdeal R) R l) - m' ∈ _
    simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
    simpa [← AdicCompletion.ker_eval _ _ (maximalIdeal R).fg_of_isNoetherianRing, eval,
      sub_eq_zero] using hl
  have rkeq := rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f ⟨inj, surj⟩).toAddEquiv
    (residueField_map_bijective R) (fun r m ↦ by
      rcases IsLocalRing.residue_surjective r with ⟨s, hs⟩
      simp only [← hs]
      change f (s • m) = _
      rw [map_smul]
      rfl )
  have fg' : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact fg.map _
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg', eq_comm]
  simp [Module.finrank, CotangentSpace, rkeq]
