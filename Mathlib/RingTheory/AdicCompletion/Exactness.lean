/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Filtration

/-!
# Exactness of adic completion

In this file we establish exactness properties of adic completions. In particular we show:

## Main results

- Adic completion preserves surjectivity.
- Over a noetherian ring adic completion is exact on finite modules.

-/

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]
variable {P : Type u} [AddCommGroup P] [Module R P]

section

variable [IsNoetherianRing R] [Module.Finite R N]

open AdicCompletion

theorem AdicCauchySequence.mem_ideal_iff (x : AdicCauchySequence I M) {m n : ℕ}
    (hmn : m ≤ n) (hn : x n ∈ (I ^ m • ⊤ : Submodule R M)) :
    x m ∈ (I ^ m • ⊤ : Submodule R M) :=
  sorry

theorem LinearMap.adicCompletion_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.adicCompletion I) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x
  intro a hx
  let M' : Submodule R N := LinearMap.range f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I M'
  ext n
  simp
  have he (n : ℕ) : ((adicCompletion I f) ((AdicCompletion.mk I M) a)).val n = 0 := by
    rw [hx]
    simp
  simp at he
  have h : f (a (n + k)) ∈ (I ^ (n + k) • ⊤ : Submodule R N) ⊓ M' :=
    ⟨he (n + k), ⟨a (n + k), rfl⟩⟩
  have h' : f (a (n + k)) ∈ (I ^ n • (I ^ k • ⊤ ⊓ M') : Submodule R N) := by
    have : n = n + k - k := by
      simp
    nth_rw 2 [this]
    have  hnk : n + k ≥ k := by
      omega
    rw [← hk (n + k) hnk]
    exact h
  have hincl : I ^ n • (I ^ k • ⊤ ⊓ M') ≤ I ^ n • M' := by
    apply Submodule.smul_mono
    rfl
    apply inf_le_right
  have : a (n + k) ∈ (I ^ n • ⊤ : Submodule R M) := by
    rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M)]
    change f (a (n + k)) ∈ Submodule.map f (I ^ n • ⊤)
    rw [Submodule.map_smul'', Submodule.map_top]
    apply hincl
    exact h'
  have hnk : n ≤ n + k := by
    omega
  apply AdicCauchySequence.mem_ideal_iff I a hnk this

end

section

variable {I} {f : M →ₗ[R] N} (hf : Function.Surjective f)

private noncomputable def LinearMap.adicCompletionPreimageDelta (x : ℕ → N)
    (h : ∀ (n : ℕ), x (n + 1) - x n ∈ (I ^ n • ⊤ : Submodule R N))
    {n : ℕ} {y yₙ : M} (hy : f y = x (n + 1)) (hyₙ : f yₙ = x n) :
    { d : (I ^ n • ⊤ : Submodule R M) | f d = f (yₙ - y) } := by
  have h1 : f (yₙ - y) ∈ (I ^ n • ⊤ : Submodule R N) := by
    rw [map_sub, hyₙ, hy, ← Submodule.neg_mem_iff, neg_sub]
    exact h n
  have h2 : f (yₙ - y) ∈ Submodule.map f (I ^ n • ⊤ : Submodule R M) := by
    rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  choose d p1 p2 using h2
  exact ⟨⟨d, p1⟩, p2⟩

private noncomputable def LinearMap.adicCompletionPreimage (x : ℕ → N)
    (h : ∀ (n : ℕ), x (n + 1) - x n ∈ (I ^ n • ⊤ : Submodule R N)) : (n : ℕ) → f ⁻¹' {x n}
  | .zero => by
      exact ⟨(hf (x 0)).choose, (hf (x 0)).choose_spec⟩
  | .succ n => by
      choose y hy using hf (x (n + 1))
      let ⟨yₙ, (hyₙ : f yₙ = x n)⟩ := adicCompletionPreimage x h n
      let ⟨⟨d', _⟩, (p : f d' = f (yₙ - y))⟩ := adicCompletionPreimageDelta hf x h hy hyₙ
      refine ⟨yₙ - d', ?_⟩
      simpa [p]

private lemma LinearMap.adicCompletionPreimage_comp (x : ℕ → N)
    (h : ∀ (n : ℕ), x (n + 1) - x n ∈ (I ^ n • ⊤ : Submodule R N)) (n : ℕ) :
    (adicCompletionPreimage hf x h (n + 1) : M) -
      adicCompletionPreimage hf x h n ∈ (I ^ n • ⊤ : Submodule R M) := by
  dsimp [adicCompletionPreimage]
  simp

variable (I)

theorem LinearMap.adicCompletion_surjective : Function.Surjective (f.adicCompletion I) := by
  intro y
  apply AdicCompletion.induction_on I N y
  intro b
  let a := LinearMap.adicCompletionPreimage hf b hcomp
  use adicCompletion.mk' I (fun n ↦ (a n : M)) (adicCompletionPreimage_comp hf b hcomp)
  ext n
  simp
  apply congrArg
  exact (a n).property

end

section

variable [IsNoetherianRing R] [Module.Finite R N]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

variable {I}

private noncomputable def LinearMap.adicCompletionExactAuxDelta {k : ℕ}
    (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
    {x : ℕ → N} (h : ∀ (n : ℕ), x (n + 1) - x n ∈ (I ^ n • ⊤ : Submodule R N))
    {n : ℕ} {d : N} (p1 : d ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N))
    {y yₙ : M} (q1 : f y = x (k + n + 1) - d) (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N)) :
    { d : (I ^ n • ⊤ : Submodule R M) | f (yₙ + d) - x (k + n + 1) ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N) } := by
  have h4 : f (y - yₙ) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp [q1]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) ∈ I ^ (k + n) • ⊤
    · abel
    · apply Submodule.sub_mem
      apply Submodule.sub_mem
      exact h (k + n)
      have : (I ^ (k + n + 1) • ⊤ : Submodule R N) ≤ (I ^ (k + n) • ⊤ : Submodule R N) := by
        apply Submodule.smul_mono
        apply Ideal.pow_le_pow_right
        omega
        rfl
      apply this
      exact p1
      exact hyₙ
  have hincl : I ^ (k + n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f)
      ≤ I ^ (k + n - k) • (LinearMap.range f) := by
    apply Submodule.smul_mono
    rfl
    apply inf_le_right
  have h5 : y - yₙ ∈ (I ^ n • ⊤ : Submodule R M) := by
    convert_to y - yₙ ∈ (I ^ (k + n - k) • ⊤ : Submodule R M)
    · simp
    · rw [← Submodule.comap_map_eq_of_injective hf (I ^ (k + n - k) • ⊤ : Submodule R M)]
      change f (y - yₙ) ∈ Submodule.map f (I ^ (k + n - k) • ⊤)
      rw [Submodule.map_smul'', Submodule.map_top]
      apply hincl
      rw [← hkn (k + n) (by omega)]
      exact ⟨h4, ⟨y - yₙ, rfl⟩⟩
  refine ⟨⟨y - yₙ, h5⟩, ?_⟩
  simp [q1, Nat.succ_eq_add_one, Nat.add_assoc]
  exact p1

private noncomputable def LinearMap.adicCompletionExactAux {k : ℕ}
    (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
    (x : ℕ → N)
    (h : ∀ (n : ℕ), x (n + 1) - x n ∈ (I ^ n • ⊤ : Submodule R N))
    (hker : ∀ (n : ℕ), g (x n) ∈ (I ^ n • ⊤ : Submodule R P)) :
    (n : ℕ) → { a : M | f a - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) }
  | .zero => by
      have h2 : g (x k) ∈ Submodule.map g (I ^ k • ⊤ : Submodule R N) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
        exact hker k
      choose d p1 p2 using h2
      have h3 : x k - d ∈ Set.range f := by
        apply (hfg (x k - d)).mp
        simp [p2]
      choose d' q1 using h3
      refine ⟨d', ?_⟩
      simpa [q1]
  | .succ n => by
      have h2 : g (x (k + n + 1)) ∈ Submodule.map g (I ^ (k + n + 1) • ⊤ : Submodule R N) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
        exact hker (k + n + 1)
      choose d p1 p2 using h2
      have h3 : x (k + n + 1) - d ∈ Set.range f := by
        apply (hfg (x (k + n + 1) - d)).mp
        simp [p2]
      choose y' q1 using h3
      let ⟨yₙ, (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N))⟩ :=
        adicCompletionExactAux hkn x h hker n
      let ⟨d, hd⟩ := adicCompletionExactAuxDelta hf hkn h p1 q1 hyₙ
      exact ⟨yₙ + d, hd⟩

private lemma LinearMap.adicCompletionExactAux_comp {k : ℕ}
    (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
    (x : ℕ → N)
    (h : ∀ (n : ℕ), x (n + 1) - x n ∈ (I ^ n • ⊤ : Submodule R N))
    (hker : ∀ (n : ℕ), g (x n) ∈ (I ^ n • ⊤ : Submodule R P)) (n : ℕ) :
    (adicCompletionExactAux hf hfg hg hkn x h hker (n + 1) : M)
      - adicCompletionExactAux hf hfg hg hkn x h hker n ∈ (I ^ n • ⊤ : Submodule R M) := by
  -- very strange: why is this needed ?!
  change (adicCompletionExactAux hf hfg hg hkn x h hker (Nat.succ n) : M) - _ ∈ _
  dsimp only [LinearMap.adicCompletionExactAux]
  simp

variable (I)

/-- adicCompletion over a Noetherian ring is exact on finitely generated modules. -/
theorem LinearMap.adicCompletion_exact :
    Function.Exact (LinearMap.adicCompletion I f) (LinearMap.adicCompletion I g) := by
  intro y
  constructor
  · intro hz
    obtain ⟨b, h, rfl⟩ := adicCompletion.exists_rep' I y
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    have hb (n : ℕ) : adicCompletion.eval I P n ((adicCompletion I g) (adicCompletion.mk' I b h)) = 0 := by
      rw [hz]
      simp
    simp at hb
    let a := adicCompletionExactAux hf hfg hg hk b h hb
    let ha := adicCompletionExactAux_comp hf hfg hg hk b h hb
    let y := adicCompletion.mk' I (fun n ↦ (a n : M)) ha
    use y
    have h1 (n : ℕ) : f (a n) - b (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) :=
      (a n).property
    have h2 (n : ℕ) :
        Submodule.mkQ (I ^ n • ⊤ : Submodule R N) (f (a n)) =
          Submodule.mkQ (I ^ n • ⊤ : Submodule R N) (b (k + n)) := by
      simp
      rw [Submodule.Quotient.eq]
      have hle : (I ^ (k + n) • ⊤ : Submodule R N) ≤ (I ^ n • ⊤ : Submodule R N) := by
        apply Submodule.smul_mono
        apply Ideal.pow_le_pow_right
        omega
        rfl
      apply hle
      exact h1 n
    have hfinal (n : ℕ) :
        Submodule.mkQ (I ^ n • ⊤ : Submodule R N) (f (a n)) =
          Submodule.mkQ (I ^ n • ⊤ : Submodule R N) (b n) := by
      have hle : n ≤ k + n := by omega
      rw [h2, Submodule.mkQ_apply, ← adicCompletion.mk'_eval I b h,
        ← adicCompletion.transitionMap_apply_mk I hle, ← Submodule.mkQ_apply,
        ← adicCompletion.mk'_eval I b h]
      rw [adicCompletion.transitionMap_comp_eval_apply]
    ext n
    simp [-adicCompletion.coe_eval, y]
    simp at hfinal
    exact hfinal n
  · rintro ⟨x, rfl⟩
    obtain ⟨a, h, rfl⟩ := adicCompletion.exists_rep' I x
    ext n
    simp
    change (g ∘ f) (a n) ∈ I ^ n • ⊤
    rw [Function.Exact.comp_eq_zero _ _ hfg]
    simp

end
