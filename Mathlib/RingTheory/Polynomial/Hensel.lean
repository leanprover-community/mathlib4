
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.SModEq
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.TopologicallyNilpotent


namespace Filter

variable {α β ι} {la : Filter α} {lb : Filter β} {p : ι → Prop}
  {s : ι → Set β} {f : α → β}

theorem Tendsto.congr_of_hasBasis (hlb : lb.HasBasis p s)
    {f g : α → β} (hf : Tendsto f la lb)
    (h : ∀ᶠ x in la, ∀ i, p i → f x ∈ s i → g x ∈ s i) :
    Tendsto g la lb := by
  rw [hlb.tendsto_right_iff] at hf ⊢
  intro i hi
  filter_upwards [h, hf i hi]
  intro x hx
  exact hx i hi

end Filter

namespace Polynomial

variable {R : Type*} [CommRing R]

def newtonsMethodInvSeq (a : R) (x0 : R) : ℕ → R
  | 0 => x0
  | n + 1 =>
    let xn := newtonsMethodInvSeq a x0 n
    2 * xn - a * xn * xn

noncomputable def newtonsMethodMapAux (f : R[X]) (x z : R) : R :=
  ∑ i ∈ (f.derivative.taylor x).support with 1 ≤ i,
    (f.derivative.taylor x).coeff i * (-(f.derivative.eval x * z)) ^ (i - 1)

noncomputable def newtonsMethodMap (f : R[X]) (u : ℕ) (xz : R × R) : R × R :=
  let (x, z) := xz
  ⟨x - f.derivative.eval x * z,
    newtonsMethodInvSeq ((1 - z * newtonsMethodMapAux f x z) ^ 2) 1 u *
      (z ^ 2 * ∑ i ∈ (f.taylor x).support with 2 ≤ i,
        (f.taylor x).coeff i * (-(f.derivative.eval x * z)) ^ (i - 2))⟩

noncomputable def newtonsMethodSeq
    (f : R[X]) (x z : R) (n : ℕ) : R :=
  ((newtonsMethodMap f n)^[n] (x, z)).1

lemma eval_add_linear (f : R[X]) (x y : R) :
    f.eval (x + y) = f.eval x + y *
      ∑ i ∈ (f.taylor x).support with 1 ≤ i, (f.taylor x).coeff i * y ^ (i - 1) := by
  rw [add_comm, ← taylor_eval, eval_eq_sum, sum, ← Finset.sum_filter_add_sum_filter_not _ (· < 1)]
  congr
  · rw [Finset.sum_subset (s₂ := Finset.range 1) (by intro; simp) (by aesop),
      Finset.sum_range_one]
    simp only [taylor_coeff_zero, pow_zero, mul_one]
  · simp only [not_lt, taylor_coeff]
    rw [Finset.mul_sum]
    congr! 1 with i hi
    rw [mul_comm y, mul_assoc, ← pow_succ]
    simp only [Finset.mem_filter, mem_support_iff, ne_eq] at hi
    congr; omega

lemma eval_add_quadratic (f : R[X]) (x y : R) :
    f.eval (x + y) = f.eval x + f.derivative.eval x * y + y ^ 2 *
      ∑ i ∈ (f.taylor x).support with 2 ≤ i, (f.taylor x).coeff i * y ^ (i - 2) := by
  rw [add_comm, ← taylor_eval, eval_eq_sum, sum, ← Finset.sum_filter_add_sum_filter_not _ (· < 2)]
  congr
  · rw [Finset.sum_subset (s₂ := Finset.range 2) (by intro; simp) (by aesop),
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [taylor_coeff_zero, pow_zero, mul_one, taylor_coeff_one]
    ring
  · simp only [not_lt, taylor_coeff]
    rw [Finset.mul_sum]
    congr! 1 with i hi
    rw [mul_comm (y ^ 2), mul_assoc, ← pow_add]
    simp only [Finset.mem_filter, mem_support_iff, ne_eq] at hi
    congr; omega

section Ideal

variable {I : Ideal R}

lemma newtonsMethodInvSeq_spec {a x0 : R}
    (hx0 : a * x0 ≡ 1 [SMOD I]) (n : ℕ) :
    newtonsMethodInvSeq a x0 n ≡ x0 [SMOD I] ∧
      a * newtonsMethodInvSeq a x0 n ≡ 1 [SMOD I ^ 2 ^ n] := by
  induction n with
  | zero => simpa [SModEq.rfl, newtonsMethodInvSeq]
  | succ n ih =>
    rw [newtonsMethodInvSeq, pow_succ, pow_mul]
    constructor
    · grw [ih.1, ← sub_mul, hx0]
      norm_num; rfl
    · simp_rw [SModEq.sub_mem] at ih ⊢
      convert neg_mem (Ideal.pow_mem_pow ih.2 2) using 1
      ring

lemma newtonsMethodInvSeq_succ {a x0 : R}
    (hx0 : a * x0 ≡ 1 [SMOD I]) (n : ℕ) :
    newtonsMethodInvSeq a x0 (n + 1) ≡ newtonsMethodInvSeq a x0 n [SMOD I ^ 2 ^ n] := by
  rw [newtonsMethodInvSeq]
  grw [(newtonsMethodInvSeq_spec hx0 _).2]
  ring_nf
  rfl

lemma newtonsMethodInvSeq_congr {a1 a2 : R} {x1 x2 : R}
    (ha : a1 ≡ a2 [SMOD I]) (hx : x1 ≡ x2 [SMOD I]) (n : ℕ) :
    newtonsMethodInvSeq a1 x1 n ≡ newtonsMethodInvSeq a2 x2 n [SMOD I] := by
  induction n with
  | zero => simpa [SModEq.rfl, newtonsMethodInvSeq]
  | succ n ih =>
    rw [newtonsMethodInvSeq, newtonsMethodInvSeq]
    gcongr

variable {J : Ideal R}

lemma newtonsMethodMap_spec {f : R[X]} {x z : R} {n u : ℕ}
    (hxJ : f.derivative.eval x ∈ J)
    (hz : z ∈ I ^ 2 ^ n)
    (hxz : f.eval x ≡ f.derivative.eval x ^ 2 * z [SMOD J ^ 2 * I ^ 2 ^ u]) :
    let x' := (newtonsMethodMap f u (x, z)).1
    let z' := (newtonsMethodMap f u (x, z)).2
    (∃ a, a ≡ 1 [SMOD I ^ 2 ^ n] ∧ f.derivative.eval x' = f.derivative.eval x * a) ∧
      z' ∈ I ^ 2 ^ (n + 1) ∧
        f.eval x' ≡ f.derivative.eval x' ^ 2 * z' [SMOD J ^ 2 * I ^ 2 ^ u] := by
  simp only [newtonsMethodMap]
  set a := 1 - z * f.newtonsMethodMapAux x z with a_def
  have haI : a ≡ 1 [SMOD I ^ 2 ^ n] := by
    rw [a_def]
    nth_grw 1 [SModEq.zero.mpr hz]
    simp; rfl
  have : a ^ 2 * 1 ≡ 1 [SMOD I] := by
    grw [haI.mono (Ideal.pow_le_self (Nat.two_pow_pos _).ne')]
    simp; rfl
  have ha := newtonsMethodInvSeq_spec this u
  set ia := newtonsMethodInvSeq a 1 u
  have ha' : f.derivative.eval (x - f.derivative.eval x * z) = f.derivative.eval x * a := by
    simp_rw [sub_eq_add_neg, eval_add_linear, a_def, newtonsMethodMapAux]; ring
  constructor
  · simp_rw [ha']
    exact ⟨_, haI, rfl⟩
  constructor
  · apply Ideal.mul_mem_left
    apply Ideal.mul_mem_right
    rw [pow_succ, pow_mul]
    exact Ideal.pow_mem_pow hz _
  rw [ha', sub_eq_add_neg, eval_add_quadratic]
  nth_rw 4 [← mul_neg]
  grw [hxz]
  ring_nf
  rw [SModEq.sub_mem]
  simp_rw [mul_assoc (f.derivative.eval x ^ _), ← mul_sub]
  apply Ideal.mul_mem_mul (Ideal.pow_mem_pow hxJ _)
  rw [← SModEq.sub_mem, mul_assoc _ (a ^ 2)]
  grw [ha.2]
  rw [mul_one]

lemma iterate_newtonsMethodMap_spec {f : R[X]} {x0 z0 : R} {u : ℕ}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 ≡ f.derivative.eval x0 ^ 2 * z0 [SMOD J ^ 2 * I ^ 2 ^ u]) (n : ℕ) :
    let x := ((f.newtonsMethodMap u)^[n] (x0, z0)).1
    let z := ((f.newtonsMethodMap u)^[n] (x0, z0)).2
    (∃ a, a ≡ 1 [SMOD I] ∧ f.derivative.eval x = f.derivative.eval x0 * a) ∧
      f.derivative.eval x ∈ J ∧ z ∈ I ^ 2 ^ n ∧
        f.eval x ≡ f.derivative.eval x ^ 2 * z [SMOD J ^ 2 * I ^ 2 ^ u] := by
  induction n with
  | zero => exact ⟨⟨1, by simp [SModEq.rfl], by simp⟩, hx0J, by simpa, hx0z0⟩
  | succ n ih =>
    obtain ⟨⟨ax, haxI, hxax⟩, hxJ, hz, hxz⟩ := ih
    obtain ⟨⟨a, haI, hxa⟩, hz', hxz'⟩ := newtonsMethodMap_spec hxJ hz hxz
    rw [Function.iterate_succ_apply']
    replace haI := haI.mono (Ideal.pow_le_self (Nat.two_pow_pos _).ne')
    exact ⟨⟨ax * a, by grw [haxI, haI]; simp [SModEq.rfl], by simp [hxa, hxax, mul_assoc]⟩,
      hxa ▸ Ideal.mul_mem_right _ _ hxJ, hz', hxz'⟩

lemma iterate_newtonsMethodMap_succ {f : R[X]} {x0 z0 : R} {u : ℕ}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 ≡ f.derivative.eval x0 ^ 2 * z0 [SMOD J ^ 2 * I ^ 2 ^ u]) (n : ℕ) :
    ((f.newtonsMethodMap u)^[n + 1] (x0, z0)).1 ≡ ((f.newtonsMethodMap u)^[n] (x0, z0)).1
      [SMOD J * I ^ 2 ^ n] := by
  rw [Function.iterate_succ_apply', newtonsMethodMap, SModEq.sub_mem, sub_sub_cancel_left]
  obtain ⟨-, hxJ, hz, hxz⟩ := iterate_newtonsMethodMap_spec hx0J hz0 hx0z0 n
  exact neg_mem (Ideal.mul_mem_mul hxJ hz)

lemma iterate_newtonsMethodMap_succ_spec {f : R[X]} {x0 z0 : R} {n u : ℕ}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 ≡ f.derivative.eval x0 ^ 2 * z0 [SMOD J ^ 2 * I ^ 2 ^ (u + 1)]) :
    ((f.newtonsMethodMap (u + 1))^[n] (x0, z0)).1 ≡
        ((f.newtonsMethodMap u)^[n] (x0, z0)).1 [SMOD J * I ^ 2 ^ u] ∧
      ((f.newtonsMethodMap (u + 1))^[n] (x0, z0)).2 ≡
          ((f.newtonsMethodMap u)^[n] (x0, z0)).2 [SMOD I ^ 2 ^ u] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, newtonsMethodMap]
    set x := ((newtonsMethodMap f u)^[n] (x0, z0)).1 with x_def
    set z := ((newtonsMethodMap f u)^[n] (x0, z0)).2 with z_def
    set x' := ((newtonsMethodMap f (u + 1))^[n] (x0, z0)).1 with x'_def
    set z' := ((newtonsMethodMap f (u + 1))^[n] (x0, z0)).2 with z'_def
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · gcongr 1
      have hx'J : f.derivative.eval x' ∈ J :=
        (iterate_newtonsMethodMap_spec hx0J hz0 hx0z0 n).2.1
      have ih1' : f.derivative.eval x' ≡ f.derivative.eval x [SMOD J * I ^ 2 ^ u] := by gcongr
      rw [SModEq.sub_mem] at ih1' ih2 ⊢
      convert add_mem (Ideal.mul_mem_mul hx'J ih2) (Ideal.mul_mem_right z _ ih1') using 1
      ring
    · have ih1' : x' ≡ x [SMOD I ^ 2 ^ u] := ih1.mono Ideal.mul_le_left
      have (g h : R[X]) (b : ℕ) :
        ∑ i ∈ (g.taylor x').support with b ≤ i, (g.taylor x').coeff i *
            (-(h.eval x' * z')) ^ (i - b) ≡
          ∑ i ∈ (g.taylor x).support with b ≤ i, (g.taylor x).coeff i *
              (-(h.eval x * z)) ^ (i - b) [SMOD I ^ 2 ^ u] := by
        let u := (g.taylor x).support ∪ (g.taylor x').support
        rw [Finset.sum_filter, Finset.sum_filter,
          Finset.sum_subset (s₂ := u) Finset.subset_union_left,
          Finset.sum_subset (s₂ := u) Finset.subset_union_right]
        · simp only [taylor_coeff]
          gcongr; split_ifs <;> gcongr
        · simp +contextual
        · simp +contextual
      gcongr
      · grw [(newtonsMethodInvSeq_succ _ _).mono]
        · apply newtonsMethodInvSeq_congr
          · dsimp [newtonsMethodMapAux]
            gcongr
            exact this _ _ _
          · gcongr
        · rfl
        · rw [mul_one]
          have : z' ∈ I := Ideal.pow_le_self (Nat.two_pow_pos _).ne'
            (iterate_newtonsMethodMap_spec hx0J hz0 hx0z0 n).2.2.1
          nth_grw 1 [SModEq.zero.mpr this]
          simp; rfl
      · exact this _ _ _

lemma newtonsMethodSeq_succ {f : R[X]} {x0 z0 : R}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) (n : ℕ) :
    newtonsMethodSeq f x0 z0 (n + 1) ≡ newtonsMethodSeq f x0 z0 n [SMOD J * I ^ 2 ^ n] := by
  unfold newtonsMethodSeq
  grw [(iterate_newtonsMethodMap_succ_spec hx0J hz0 (of_eq hx0z0)).1,
    iterate_newtonsMethodMap_succ hx0J hz0 (of_eq hx0z0) n]

lemma smodEq_newtonsMethodSeq_newtonsMethodSeq {f : R[X]} {x0 z0 : R}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) (n m : ℕ) :
    newtonsMethodSeq f x0 z0 n ≡ newtonsMethodSeq f x0 z0 m [SMOD J * I ^ 2 ^ (min n m)] := by
  wlog hnm : m ≤ n
  · rw [SModEq.comm, min_comm]
    apply this hx0J hz0 hx0z0
    order
  rw [min_eq_right hnm]
  rw [le_iff_exists_add] at hnm
  obtain ⟨k, rfl⟩ := hnm
  induction k with
  | zero => simp [SModEq.rfl]
  | succ k ih =>
    rw [← add_assoc]
    grw [(newtonsMethodSeq_succ hx0J hz0 hx0z0 (m + k)).mono (Ideal.le_of_dvd _), ih]
    rw [pow_add, pow_mul]
    exact mul_dvd_mul_left _ (dvd_pow_self _ (Nat.two_pow_pos _).ne')

lemma smodEq_newtonsMethodSeq {f : R[X]} {x0 z0 : R}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) (n : ℕ) :
    newtonsMethodSeq f x0 z0 n ≡ x0 [SMOD J * I] := by
  convert smodEq_newtonsMethodSeq_newtonsMethodSeq hx0J hz0 hx0z0 n 0
  simp

lemma eval_newtonsMethodSeq {f : R[X]} {x0 z0 : R}
    (hx0J : f.derivative.eval x0 ∈ J)
    (hz0 : z0 ∈ I)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) (n : ℕ) :
    f.eval (newtonsMethodSeq f x0 z0 n) ∈ J ^ 2 * I ^ 2 ^ n := by
  obtain ⟨-, hxJ, hz, hxz⟩ := iterate_newtonsMethodMap_spec hx0J hz0 (of_eq hx0z0) _
  rw [newtonsMethodSeq, ← SModEq.zero]
  grw [hxz]
  rw [SModEq.zero]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxJ _) hz

end Ideal

lemma tendsto_eval_newtonsMethodInvSeq_nhds_zero [TopologicalSpace R] [IsLinearTopology R R]
    {I : Ideal R} (hfgI : I.FG) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)
    {a x0 : R} (hx0 : a * x0 ≡ 1 [SMOD I]) :
    Filter.Tendsto (fun n ↦ a * newtonsMethodInvSeq a x0 n - 1) .atTop (nhds 0) := by
  rw [(IsLinearTopology.hasBasis_submodule R).tendsto_right_iff]
  intro J hJ
  have hIJ : I ≤ Ideal.radical J := fun x hx ↦ ((hI x hx).eventually_mem hJ).exists
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hfgI
  filter_upwards [(Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop n]
  intro i hi
  exact hn <| Ideal.pow_le_pow_right hi <| SModEq.sub_mem.mp (newtonsMethodInvSeq_spec hx0 _).2

lemma tendsto_eval_newtonsMethodSeq_nhds_zero [TopologicalSpace R] [IsLinearTopology R R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    Filter.Tendsto (fun n ↦ f.eval (newtonsMethodSeq f x0 z0 n)) .atTop (nhds 0) := by
  apply (hz0.comp (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).congr_of_hasBasis
    (IsLinearTopology.hasBasis_submodule R) (.of_forall _)
  intro i I hI hz0I
  simp only [SetLike.mem_coe, Function.comp_apply] at hz0I ⊢
  suffices ⊤ ^ 2 * Ideal.span {z0} ^ 2 ^ i ≤ I from
    this (eval_newtonsMethodSeq Submodule.mem_top (Ideal.mem_span_singleton_self z0) hx0z0 i)
  intro x hx
  rw [Ideal.top_pow, Ideal.top_mul, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  exact Ideal.mem_of_dvd _ hx hz0I

lemma eq_sum_of_sub_mem
    {x : ℕ → R} {z : ℕ → R}
    (h : ∀ n, x (n + 1) - x n ∈ Ideal.span {z n}) :
    ∃ c : ℕ → R, ∀ n, x n = x 0 + ∑ i ∈ .range n, c i * z i := by
  simp_rw [Ideal.mem_span_singleton'] at h
  choose c hc using h
  use c
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih, hc, add_sub_cancel]

lemma newtonsMethodSeq_eq_sum
    {f : R[X]} {x0 z0 : R}
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    ∃ c : ℕ → R, ∀ n, newtonsMethodSeq f x0 z0 n =
      x0 + f.derivative.eval x0 * ∑ i ∈ .range n, c i * z0 ^ 2 ^ i := by
  simp_rw [Finset.mul_sum, mul_left_comm]
  apply eq_sum_of_sub_mem
  intro n
  rw [← SModEq.sub_mem, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  exact newtonsMethodSeq_succ (Ideal.mem_span_singleton_self _) (Ideal.mem_span_singleton_self _)
    hx0z0 _

lemma eval_derivative_newtonsMethodSeq_eq_sum
    {f : R[X]} {x0 z0 : R}
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    ∃ c : ℕ → R, ∀ n, f.derivative.eval (newtonsMethodSeq f x0 z0 n) =
      f.derivative.eval x0 * (1 + ∑ i ∈ .range n, c i * z0 ^ 2 ^ i) := by
  simp_rw [mul_add, mul_one, Finset.mul_sum, mul_left_comm]
  apply eq_sum_of_sub_mem
  intro n
  rw [← SModEq.sub_mem, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  gcongr
  exact newtonsMethodSeq_succ (Ideal.mem_span_singleton_self _) (Ideal.mem_span_singleton_self _)
    (of_eq hx0z0) n

lemma cauchySeq_of_succ_sub_mem [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R]
    {I : Ideal R} (hfgI : I.FG) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)
    {k : ℕ → ℕ} (hk : Filter.Tendsto k .atTop .atTop)
    {f : ℕ → R} (hf : ∀ n, f (n + 1) - f n ∈ I ^ (k n)) :
    CauchySeq f := by
  rw [(IsLinearTopology.hasBasis_submodule R).uniformity_of_nhds_zero.cauchySeq_iff']
  intro J hJ
  have hIJ : I ≤ Ideal.radical J := fun x hx ↦ ((hI x hx).eventually_mem hJ).exists
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hfgI
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hk.eventually_ge_atTop n)
  use N
  suffices ∀ i, f N - f (N + i) ∈ J by simpa [le_iff_exists_add]
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    suffices f (N + (i + 1)) - f (N + i) ∈ J by
      simpa using add_mem ih (neg_mem this)
    rw [← add_assoc]
    exact hn <| Ideal.pow_le_pow_right (hN _ (by omega)) (hf (N + i))

lemma cauchySeq_of_succ_sub_dvd [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R]
    {z : R} (hz : IsTopologicallyNilpotent z)
    {k : ℕ → ℕ} (hk : Filter.Tendsto k .atTop .atTop)
    {f : ℕ → R} (hf : ∀ n, z ^ (k n) ∣ f (n + 1) - f n) :
    CauchySeq f :=
  have hfgI : (Ideal.span {z}).FG := ⟨{z}, by simp⟩
  have hI (x) (hx : x ∈ Ideal.span {z}) : IsTopologicallyNilpotent x := by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact hz.mul_right _
  cauchySeq_of_succ_sub_mem hfgI hI hk (by
    simpa [Ideal.span_singleton_pow, Ideal.mem_span_singleton])

lemma cauchySeq_newtonsMethodInvSeq [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R]
    {I : Ideal R} (hfgI : I.FG) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)
    {a x0 : R} (hx0 : a * x0 ≡ 1 [SMOD I]) :
    CauchySeq (newtonsMethodInvSeq a x0) :=
  cauchySeq_of_succ_sub_mem hfgI hI (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    fun n ↦ SModEq.sub_mem.mp (newtonsMethodInvSeq_succ hx0 n)

noncomputable def newtonsMethodInvLim [TopologicalSpace R]
    (a : R) (x0 : R) : R :=
  limUnder Filter.atTop (newtonsMethodInvSeq a x0)

lemma newtonsMethodInvSeq_tendsto_newtonsMethodInvLim
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    {I : Ideal R} (hfgI : I.FG) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)
    {a x0 : R} (hx0 : a * x0 ≡ 1 [SMOD I]) :
    Filter.Tendsto (newtonsMethodInvSeq a x0) Filter.atTop (nhds (newtonsMethodInvLim a x0)) :=
  (cauchySeq_newtonsMethodInvSeq hfgI hI hx0).tendsto_limUnder

lemma mul_newtonsMethodInvLim_eq_one'
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {I : Ideal R} (hfgI : I.FG) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)
    {a x0 : R} (hx0 : a * x0 ≡ 1 [SMOD I]) :
    a * newtonsMethodInvLim a x0 = 1 := by
  rw [← sub_eq_zero]
  have : Continuous (fun x ↦ a * x - 1) := by fun_prop
  exact tendsto_nhds_unique
    ((this.tendsto _).comp (newtonsMethodInvSeq_tendsto_newtonsMethodInvLim hfgI hI hx0))
    (tendsto_eval_newtonsMethodInvSeq_nhds_zero hfgI hI hx0)

lemma mul_newtonsMethodInvLim_eq_one
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {z0 : R} (hz0 : IsTopologicallyNilpotent z0)
    {a x0 : R} (hx0 : a * x0 ≡ 1 [SMOD Ideal.span {z0}]) :
    a * newtonsMethodInvLim a x0 = 1 := by
  have hfgI : (Ideal.span {z0}).FG := ⟨{z0}, by simp⟩
  have hI (x) (hx : x ∈ Ideal.span {z0}) : IsTopologicallyNilpotent x := by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact hz0.mul_right _
  exact mul_newtonsMethodInvLim_eq_one' hfgI hI hx0

lemma isUnit_of_mul_smodEq_one
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {z0 : R} (hz0 : IsTopologicallyNilpotent z0)
    {a x0 : R} (hx0 : a * x0 ≡ 1 [SMOD Ideal.span {z0}]) :
    IsUnit a :=
  isUnit_of_mul_eq_one _ _ (mul_newtonsMethodInvLim_eq_one hz0 hx0)

lemma cauchySeq_newtonsMethodSeq [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    CauchySeq (newtonsMethodSeq f x0 z0) := by
  apply cauchySeq_of_succ_sub_dvd hz0 (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  intro n
  have := newtonsMethodSeq_succ (trivial : _ ∈ ⊤) (Ideal.mem_span_singleton_self z0) hx0z0 n
  simpa [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using this

noncomputable def newtonsMethodLim [TopologicalSpace R]
    (f : R[X]) (x0 : R) (z0 : R) : R :=
  limUnder Filter.atTop (newtonsMethodSeq f x0 z0)

lemma newtonsMethodSeq_tendsto_newtonsMethodLim
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    Filter.Tendsto (newtonsMethodSeq f x0 z0) Filter.atTop (nhds (newtonsMethodLim f x0 z0)) :=
  (cauchySeq_newtonsMethodSeq hz0 hx0z0).tendsto_limUnder

lemma summable_mul_pow
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {k : ℕ → ℕ} (hk : Filter.Tendsto k .atTop .atTop)
    {z : R} (hz : IsTopologicallyNilpotent z)
    (c : ℕ → R) :
    Summable (fun i ↦ c i * z ^ k i) := by
  rw [summable_iff_vanishing]
  intro S hS
  rw [(IsLinearTopology.hasBasis_submodule R).mem_iff] at hS
  obtain ⟨J, hJ, hJx⟩ := hS
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (hz.eventually_mem hJ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hk.eventually_ge_atTop n)
  refine ⟨Finset.Iio N, fun t ht ↦ hJx (sum_mem fun i hi ↦ ?_)⟩
  have := ht.notMem_of_mem_left_finset hi
  rw [Finset.mem_Iio, not_lt] at this
  exact Ideal.mul_mem_left _ _ (hn _ (hN _ this))

lemma newtonsMethodLim_eq_tsum
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    ∃ c : ℕ → R, Summable (fun i ↦ c i * z0 ^ 2 ^ i) ∧
      newtonsMethodLim f x0 z0 = x0 + f.derivative.eval x0 * ∑' i, c i * z0 ^ 2 ^ i := by
  obtain ⟨c, hc⟩ := newtonsMethodSeq_eq_sum hx0z0
  use c
  have : Summable fun i ↦ c i * z0 ^ 2 ^ i :=
    summable_mul_pow (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two) hz0 _
  use this
  rw [← this.tsum_mul_left, ← sub_eq_iff_eq_add']
  refine tendsto_nhds_unique ?_ (this.mul_left _).tendsto_sum_tsum_nat
  simp_rw [Finset.mul_sum, ← sub_eq_iff_eq_add'] at hc
  simp_rw [← hc, Filter.tendsto_sub_const_iff]
  exact newtonsMethodSeq_tendsto_newtonsMethodLim hz0 hx0z0

lemma isRoot_newtonsMethodLim
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    f.IsRoot (newtonsMethodLim f x0 z0) :=
  tendsto_nhds_unique
    ((f.continuous.tendsto _).comp (newtonsMethodSeq_tendsto_newtonsMethodLim hz0 hx0z0))
    (tendsto_eval_newtonsMethodSeq_nhds_zero hz0 hx0z0)

lemma smodEq_newtonsMethodLim
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    newtonsMethodLim f x0 z0 ≡ x0 [SMOD Ideal.span {f.derivative.eval x0 * z0}] := by
  obtain ⟨c, hc, h⟩ := newtonsMethodLim_eq_tsum hz0 hx0z0
  rw [h, SModEq.sub_mem, add_sub_cancel_left, ← Ideal.span_singleton_mul_span_singleton]
  apply Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
  rw [Ideal.mem_span_singleton]
  have : Summable fun i ↦ c i * z0 ^ (2 ^ i - 1) :=
    summable_mul_pow ((Filter.tendsto_sub_atTop_nat 1).comp
      (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)) hz0 _
  have := this.tsum_mul_right z0
  simp_rw [mul_assoc, ← pow_succ, tsub_add_cancel_of_le Nat.one_le_two_pow] at this
  rw [this]
  exact dvd_mul_left _ _

lemma associated_eval_derivative_newtonsMethodLim
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    Associated (f.derivative.eval (newtonsMethodLim f x0 z0)) (f.derivative.eval x0) := by
  obtain ⟨c, hc⟩ := eval_derivative_newtonsMethodSeq_eq_sum hx0z0
  conv at hc =>
    ext; arg 2; arg 2; arg 2; arg 2; ext
    rw [← tsub_add_cancel_of_le Nat.one_le_two_pow, pow_succ, ← mul_assoc]
  simp_rw [← Finset.sum_mul] at hc
  have tendsto_lhs :=
    (f.derivative.continuous.tendsto _).comp (newtonsMethodSeq_tendsto_newtonsMethodLim hz0 hx0z0)
  have : Summable fun i ↦ c i * z0 ^ (2 ^ i - 1) :=
    summable_mul_pow ((Filter.tendsto_sub_atTop_nat 1).comp
      (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)) hz0 _
  have tendsto_rhs :
      Filter.Tendsto (fun n ↦ f.derivative.eval x0 *
          (1 + (∑ i ∈ Finset.range n, c i * z0 ^ (2 ^ i - 1)) * z0)) .atTop
        (nhds (f.derivative.eval x0 * (1 + (∑' i, c i * z0 ^ (2 ^ i - 1)) * z0))) :=
      (((this.tendsto_sum_tsum_nat.mul_const _).const_add _).const_mul _)
  simp_rw [← hc] at tendsto_rhs
  have : f.derivative.eval (f.newtonsMethodLim x0 z0) =
      f.derivative.eval x0 * (1 + (∑' i, c i * z0 ^ (2 ^ i - 1)) * z0) :=
    tendsto_nhds_unique tendsto_lhs tendsto_rhs
  have hinv :=
    have hx0 :
        (1 + (∑' (i : ℕ), c i * z0 ^ (2 ^ i - 1)) * z0) * 1 ≡ 1 [SMOD Ideal.span {z0}] := by
      rw [mul_one, SModEq.sub_mem, add_sub_cancel_left, Ideal.mem_span_singleton]
      exact dvd_mul_left _ _
    mul_newtonsMethodInvLim_eq_one hz0 hx0
  exact .symm ⟨Units.mkOfMulEqOne _ _ hinv, this.symm⟩

lemma newtonsMethodLim_unique
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0)
    (hf'x0 : f.derivative.eval x0 ∈ nonZeroDivisors R)
    (x : R) (hfx : f.IsRoot x)
    (hx : x ≡ x0 [SMOD Ideal.span {f.derivative.eval x0 * z0}]) :
    x = newtonsMethodLim f x0 z0 := by
  replace hx := hx.trans (smodEq_newtonsMethodLim hz0 hx0z0).symm
  rw [SModEq.sub_mem, Ideal.mem_span_singleton] at hx
  rw [← sub_eq_zero]
  set d := x - newtonsMethodLim f x0 z0
  obtain ⟨q, hq⟩ : ∃ q,
      f.eval (f.newtonsMethodLim x0 z0 + d) =
        f.eval (f.newtonsMethodLim x0 z0) + f.derivative.eval (f.newtonsMethodLim x0 z0) * d +
          d ^ 2 * q :=
    ⟨_, f.eval_add_quadratic (newtonsMethodLim f x0 z0) d⟩
  rw [isRoot_newtonsMethodLim hz0 hx0z0, add_sub_cancel, hfx, zero_add, eq_comm,
    ← eq_neg_iff_add_eq_zero, mul_comm _ q, ← neg_mul] at hq
  obtain ⟨e, he⟩ : f.derivative.eval x0 * z0 * d ∣ f.derivative.eval x0 * d :=
    calc
      _ ∣ d * d := mul_dvd_mul_right hx _
      _ ∣ f.derivative.eval (newtonsMethodLim f x0 z0) * d := by
        rw [hq, pow_two, ← mul_assoc]; exact mul_dvd_mul_right (dvd_mul_left _ _) _
      _ ∣ f.derivative.eval x0 * d :=
        mul_dvd_mul_right (associated_eval_derivative_newtonsMethodLim hz0 hx0z0).dvd _
  rw [mem_nonZeroDivisors_iff] at hf'x0
  rw [mul_right_comm _ _ d, mul_assoc _ z0, ← sub_eq_zero, ← mul_one_sub,
    (isUnit_of_mul_smodEq_one hz0 (x0 := 1)
      (by simp [SModEq.sub_mem, Ideal.mem_span_singleton])).mul_left_eq_zero] at he
  exact hf'x0.1 _ he

theorem hensels_lemma
    [UniformSpace R] [IsUniformAddGroup R] [IsLinearTopology R R] [CompleteSpace R]
    [IsTopologicalSemiring R] [T3Space R]
    {f : R[X]} {x0 z0 : R}
    (hz0 : IsTopologicallyNilpotent z0)
    (hx0z0 : f.eval x0 = f.derivative.eval x0 ^ 2 * z0) :
    ∃ x : R,
      f.IsRoot x ∧
        x ≡ x0 [SMOD Ideal.span {f.derivative.eval x0 * z0}] ∧
          Associated (f.derivative.eval x) (f.derivative.eval x0) ∧
            (f.derivative.eval x0 ∈ nonZeroDivisors R →
              ∀ x', f.IsRoot x' → x' ≡ x0 [SMOD Ideal.span {f.derivative.eval x0 * z0}] →
                x' = x) :=
  ⟨newtonsMethodLim f x0 z0, isRoot_newtonsMethodLim hz0 hx0z0, smodEq_newtonsMethodLim hz0 hx0z0,
    associated_eval_derivative_newtonsMethodLim hz0 hx0z0,
      newtonsMethodLim_unique hz0 hx0z0⟩

end Polynomial
