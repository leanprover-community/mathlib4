import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Filter BigOperators Topology
open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[irreducible]
noncomputable def schwarzianWithin (f : 𝕜 → 𝕜) (s : Set 𝕜) (x : 𝕜) : 𝕜 :=
  (2 * iteratedDerivWithin 3 f s x * derivWithin f s x -
    3 * iteratedDerivWithin 2 f s x ^ 2) / (2 * derivWithin f s x ^ 2)

-- TODO: fix notation so that parentheses aren't required
scoped[Schwarzian] notation3 "𝓢[" s "] " f:100 => schwarzianWithin f s
open Schwarzian

noncomputable def schwarzian (f : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 := (𝓢[univ] f) x

scoped[Schwarzian] notation3 "𝓢" => schwarzian

lemma schwarzianWithin_const_apply (c : 𝕜) (s : Set 𝕜) (x : 𝕜) :
    schwarzianWithin (fun _ ↦ c) s x = 0 := by
  simp [schwarzianWithin]

lemma schwarzian_const_apply (c x : 𝕜) : 𝓢 (fun _ ↦ c) x = 0 :=
  schwarzianWithin_const_apply ..

@[simp]
lemma schwarzianWithin_const (c : 𝕜) : schwarzianWithin (fun _ ↦ c) = 0 := by
  ext
  apply schwarzianWithin_const_apply

@[simp]
lemma schwarzian_const (c : 𝕜) : 𝓢 (fun _ ↦ c) = 0 := funext <| schwarzian_const_apply c

@[simp] -- TODO: drop `[OfNat 𝕜 n]`
lemma schwarzianWithin_ofNat (n : ℕ) [OfNat 𝕜 n] : schwarzianWithin (ofNat(n) : 𝕜 → 𝕜) = 0 :=
  schwarzianWithin_const _

@[simp]
lemma schwarzian_ofNat (n : ℕ) [OfNat 𝕜 n] : 𝓢 (ofNat(n) : 𝕜 → 𝕜) = 0 :=
  schwarzian_const _

lemma schwarzianWithin_id_apply (s : Set 𝕜) (x : 𝕜) : (𝓢[s] id) x = 0 := by
  cases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with
  | inl hs => simp [schwarzianWithin, hs]
  | inr hs => simp [schwarzianWithin]

@[simp] lemma schwarzianWithin_add_const (c : 𝕜) : 𝓢 (λ x, x + c) = 0 :=
funext $ λ x, by simp [schwarzian_def]

@[simp] lemma schwarzian_add_const (c : 𝕜) : 𝓢 (λ x, x + c) = 0 :=
funext $ λ x, by simp [schwarzian_def]

@[simp] lemma schwarzian_const_add (c : 𝕜) : 𝓢 ((+) c) = 0 :=
by simpa only [add_comm] using schwarzian_add_const c

lemma schwarzian_fpow_apply [char_zero 𝕜] (m : ℤ) (hm : m ≠ 0) (x : 𝕜) :
  𝓢 (λ x : 𝕜, x ^ m) x = - (m ^ 2 - 1) / (2 * x ^ 2) :=
begin
  simp [schwarzian_def, finset.prod_range_succ],
  rcases eq_or_ne x 0 with (rfl|hx),
  { rcases eq_or_ne m 1 with (rfl|h₁),
    { simp },
    { simp [zero_fpow _ (sub_ne_zero.2 h₁)] } },
  { rw div_eq_div_iff,
    { have : ∀ y : 𝕜, y ^ (3 : ℤ) = y ^ 3 := λ y, gpow_coe_nat y 3,
      simp only [pow_two, fpow_sub hx, gpow_one, gpow_two, pow_bit1, this],
      have : x ^ m ≠ 0, from fpow_ne_zero m hx,
      field_simp,
      ring },
    { simp [fpow_ne_zero, *] },
    { simp [hx] } }
end

@[simp] lemma schwarzian_fpow [char_zero 𝕜] (m : ℤ) (hm : m ≠ 0):
  𝓢 (λ x : 𝕜, x ^ m) = λ x, - (m ^ 2 - 1) / (2 * x ^ 2) :=
funext (schwarzian_fpow_apply m hm)

@[simp] lemma schwarzian_inv [char_zero 𝕜] : 𝓢 (λ x : 𝕜, x⁻¹) = 0 :=
by simpa using @schwarzian_fpow 𝕜 _ _ (-1) (by simp)

lemma schwarzian_comp_apply (f g : 𝕜 → 𝕜) (x : 𝕜) (hf : times_cont_diff_at 𝕜 3 f (g x))
  (hg : times_cont_diff_at 𝕜 3 g x) :
  𝓢 (f ∘ g) x = (𝓢 f (g x)) * (deriv g x) ^ 2 + 𝓢 g x :=
begin
  have hf' : ∀ᶠ y in 𝓝 x, times_cont_diff_at 𝕜 3 f (g y),
    from hg.continuous_at.eventually hf.eventually,
  replace hg : ∀ᶠ y in 𝓝 x, times_cont_diff_at 𝕜 3 g y, from hg.eventually,
  have hd₁ : deriv (f ∘ g) =ᶠ[𝓝 x] (λ y, deriv f (g y) * deriv g y),
  { refine hf'.mp (hg.mono (λ y hgy hfy, _)),
    exact deriv.comp _ (hfy.differentiable_at dec_trivial) (hgy.differentiable_at dec_trivial) },
  have hd₂ : deriv (deriv (f ∘ g)) =ᶠ[𝓝 x] (λ y, deriv (deriv f) (g y) * (deriv g y) ^ 2 + deriv f (g y) * deriv (deriv g) y),
  simp only [schwarzian_def, div_pow, (∘), nat.iterate],

  
end
