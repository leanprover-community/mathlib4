/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Une introduction à Lean par le théorème de Riesz

Je vais expliquer la preuve du théorème de Riesz à l'ordinateur.

Le théorème de Riesz affirme que si un espace vectoriel réel a une boule compacte,
alors il est de dimension finie.

On raisonne par contraposée : si l'espace n'est pas de dimension finie, on va
construire une suite dans la boule de rayon `2` dont tous les points sont à distance
au moins `1`, ce qui contredirait la compacité de la boule.

On construit la suite par récurrence. Supposons les `n` premiers points construits.
Ils engendrent un sous-espace `F` de dimension finie, qui est complet (par équivalence
des normes) donc fermé. Soit `x ∉ F`, et notons `d` sa distance à `F` (qui est positive
par fermeture). On choisit `y ∈ F` avec `dist x y < 2 d`. J'affirme que `d⁻¹ * (x - y)`
convient pour le point suivant. Il est bien de norme au plus `2`. De plus, comme `xᵢ ∈ F`,
on a `y + d * xᵢ ∈ F`. Ainsi,
`d ≤ dist x (y + d * xᵢ)`, soit `d ≤ ‖d * (d⁻¹ * (x - y) - xᵢ)‖`,
et donc `1 ≤ ‖d⁻¹ * (x - y) - xᵢ‖` comme on le voulait.

Pour expliquer cette preuve de 10 lignes à Lean, on va la couper en plusieurs sous-lemmes.
-/

open Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Étant donné un sous-espace vectoriel fermé qui n'est pas tout l'espace, on peut
trouver un point de norme au plus `2` à distance au moins `1` de tout point
du sous-espace. -/
lemma existe_point_loin_de_sousmodule
    (F : Submodule ℝ E) (hF : ∃ x, x ∉ F) (hFc : IsClosed (F : Set E)) :
    ∃ (z : E), ‖z‖ < 2 ∧ (∀ y ∈ F, 1 ≤ ‖z - y‖) := by
  obtain ⟨x, x_pas_dans_F⟩ := hF
  let d := infDist x F
  have hFn : (F : Set E).Nonempty := ⟨0, F.zero_mem⟩
  have d_pos : 0 < d := (IsClosed.not_mem_iff_infDist_pos hFc hFn).1 x_pas_dans_F
  obtain ⟨y₀, hy₀F, hxy₀⟩ : ∃ y ∈ F, dist x y < 2 * d := by
    apply (infDist_lt_iff hFn).1
    exact lt_two_mul_self d_pos
    -- linarith
  let z := d⁻¹ • (x - y₀)
  have Nz : ‖z‖ < 2 := by
    simpa [z, norm_smul, abs_of_nonneg d_pos.le, ← div_eq_inv_mul, div_lt_iff₀ d_pos,
      ← dist_eq_norm]
  have I : ∀ y ∈ F, 1 ≤ ‖z - y‖ := by
    intro y hyF
    have A : d ≤ dist x (y₀ + d • y) := by
      apply infDist_le_dist_of_mem
      exact F.add_mem hy₀F (F.smul_mem _ hyF)
    have B : d⁻¹ * d = 1 := by field_simp [d_pos.ne']
    calc
      1 = d⁻¹ * d                    := B.symm
      _ ≤ d⁻¹ * dist x (y₀ + d • y)  := mul_le_mul_of_nonneg_left A (inv_nonneg.2 d_pos.le)
      _ = d⁻¹ * ‖(x - y₀) - d • y‖   := by rw [dist_eq_norm, sub_sub]
      _ = ‖d⁻¹ • ((x - y₀) - d • y)‖ := by simp [norm_smul, abs_of_nonneg d_pos.le]
      _ = ‖z - y‖                    := by simp_rw [z, smul_sub, smul_smul, B, one_smul]
  exact ⟨z, Nz, I⟩

/-- Dans un espace vectoriel normé réel de dimension infinie, étant donné un ensemble
fini de points, on peut trouver un point de norme au plus `2` à distance au moins `1`
de tous ces points. -/
lemma existe_point_loin_de_fini
    (s : Set E) (hs : Set.Finite s) (h : ¬(FiniteDimensional ℝ E)) :
    ∃ (z : E), ‖z‖ < 2 ∧ (∀ y ∈ s, 1 ≤ ‖z - y‖) := by
  let F := Submodule.span ℝ s
  have : FiniteDimensional ℝ F := Module.finite_def.2
    ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, hs, rfl⟩))
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have hF : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule ℝ E) = F := by ext x; simp [h]
    have : FiniteDimensional ℝ (⊤ : Submodule ℝ E) := by rwa [this]
    refine Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
  obtain ⟨x, x_lt_2, hx⟩ : ∃ (x : E), ‖x‖ < 2 ∧ ∀ (y : E), y ∈ F → 1 ≤ ‖x - y‖ :=
    existe_point_loin_de_sousmodule F hF Fclosed
  exact ⟨x, x_lt_2, fun y hy ↦ hx _ (Submodule.subset_span hy)⟩

/-- Dans un espace vectoriel normé réel de dimension infinie, on peut trouver une
suite de points tous de norme au plus `2` et mutuellement distants d'au moins `1`. -/
lemma existe_suite_loin (h : ¬(FiniteDimensional ℝ E)) :
    ∃ (u : ℕ → E), (∀ n, ‖u n‖ < 2) ∧ (∀ m n, m ≠ n → 1 ≤ ‖u n - u m‖) := by
  have : IsSymm E (fun (x y : E) ↦ 1 ≤ ‖y - x‖) := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply exists_seq_of_forall_finset_exists' (fun (x : E) ↦ ‖x‖ < 2)
    (fun (x : E) (y : E) ↦ 1 ≤ ‖y - x‖)
  intro s _hs
  exact existe_point_loin_de_fini (s : Set E) s.finite_toSet h

/-- Considérons un espace vectoriel normé réel dans lequel la boule fermée de rayon `2` est
compacte. Alors cet espace est de dimension finie. -/
theorem ma_version_de_riesz (h : IsCompact (closedBall (0 : E) 2)) :
    FiniteDimensional ℝ E := by
  by_contra hfin
  obtain ⟨u, u_lt_two, u_far⟩ :
    ∃ (u : ℕ → E), (∀ n, ‖u n‖ < 2) ∧ (∀ m n, m ≠ n → 1 ≤ ‖u n - u m‖) :=
    existe_suite_loin hfin
  have A : ∀ n, u n ∈ closedBall (0 : E) 2 := by
    intro n
    simpa only [norm_smul, dist_zero_right, mem_closedBall] using (u_lt_two n).le
  obtain ⟨x, _hx, φ, φmono, φlim⟩ : ∃ x ∈ closedBall (0 : E) 2, ∃ (φ : ℕ → ℕ),
    StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) := h.tendsto_subseq A
  have B : CauchySeq (u ∘ φ) := φlim.cauchySeq
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → dist ((u ∘ φ) n) ((u ∘ φ) N) < 1 :=
    cauchySeq_iff'.1 B 1 zero_lt_one
  apply lt_irrefl (1 : ℝ)
  calc
  1 ≤ dist (u (φ (N+1))) (u (φ N)) := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul]
    apply u_far
    exact (φmono (Nat.lt_succ_self N)).ne
  _ < 1 := hN (N+1) (Nat.le_succ N)

/- La preuve est finie, et prend environ 100 lignes, soit 10 fois plus que la version
informelle. C'est assez typique. -/

theorem la_vraie_version_de_riesz
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace 𝕜] {r : ℝ}
    (r_pos : 0 < r)  {c : F} (hc : IsCompact (closedBall c r)) :
    FiniteDimensional 𝕜 F :=
  .of_isCompact_closedBall 𝕜 r_pos hc
-- by exact?

/- Pour l'énoncé précédent :
  have : (0 : ℝ) < 2 := zero_lt_two
  exact?
-/

/- Les preuves sont vérifiées par le "noyau". Mais comment se convaincre que les définitions
sont bonnes ? Avec une mauvaise définition, on risque de pouvoir démontrer n'importe quoi. -/

def IsSGCompact {α : Type*} (_s : Set α) : Prop := False

theorem riesz_avec_isSGCompact (h : IsSGCompact (closedBall (0 : E) 2)) :
  FiniteDimensional ℝ E :=
False.elim h

theorem antiriesz_avec_isSGCompact (h : IsSGCompact (closedBall (0 : E) 2)) :
  ¬(FiniteDimensional ℝ E) :=
False.elim h

/- On peut essayer de dérouler les définitions pour voir si elles ont l'air raisonnables. -/

#check IsCompact
#check FiniteDimensional

/- On peut voir si les définitions permettent de démontrer des théorèmes raisonnables. -/

example (n : ℕ) : FiniteDimensional ℝ (Fin n → ℝ) := by infer_instance

example (n : ℕ) : IsCompact (closedBall (0 : Fin n → ℝ) 1) := isCompact_closedBall _ _

example : ¬(IsCompact (Set.univ : Set ℝ)) := noncompact_univ ℝ

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
  ¬(IsCompact (Set.univ : Set E)) := noncompact_univ E
