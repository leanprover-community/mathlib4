import Mathlib.LinearAlgebra.AdicCompletion
import Mathlib.RingTheory.Filtration

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]

def adicCompletion.transitionMap {m n : ℕ} (h : m ≤ n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) := by
  apply Submodule.mapQ _ _ LinearMap.id
  exact Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl

@[simp]
lemma adicCompletion.transitionMap_apply_mk {m n : ℕ} (h : m ≤ n) (x : M) :
    (adicCompletion.transitionMap I h) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp [transitionMap]

lemma adicCompletion.mem (x : ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    x ∈ adicCompletion I M ↔ ∀ {m n : ℕ} (h : m ≤ n), transitionMap I h (x n) = x m := by
  rfl

@[simp]
lemma adicCompletion.transitionMap_comp_eval {m n : ℕ} (h : m ≤ n) :
    adicCompletion.transitionMap I h ∘ₗ adicCompletion.eval I M n = adicCompletion.eval I M m := by
  ext ⟨x, hx⟩
  simp
  rw [adicCompletion.mem] at hx
  rw [hx]

@[simp]
lemma adicCompletion.transitionMap_comp_eval_apply {m n : ℕ} (h : m ≤ n) (x : adicCompletion I M) :
    adicCompletion.transitionMap I h (adicCompletion.eval I M n x) = adicCompletion.eval I M m x := by
  change (adicCompletion.transitionMap I h ∘ₗ adicCompletion.eval I M n) x = adicCompletion.eval I M m x
  simp

def LinearMap.adicCompletionAux (f : M →ₗ[R] N) (n : ℕ) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) := by
  apply Submodule.mapQ _ _ f
  intro x hx
  simp only [Submodule.mem_comap]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr x _
    simp only [LinearMapClass.map_smul]
    apply Submodule.smul_mem_smul hr
    trivial
  · intro x y hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy

@[simp]
lemma LinearMap.adicCompletionAux_apply_mk (f : M →ₗ[R] N) (n : ℕ) (x : M) :
    f.adicCompletionAux I n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := by
  simp [adicCompletionAux]

def LinearMap.adicCompletionAux_comm (f : M →ₗ[R] N) {m n : ℕ} (h : m ≤ n) :
    adicCompletionAux I f m ∘ₗ adicCompletion.transitionMap I h =
      adicCompletion.transitionMap I h ∘ₗ adicCompletionAux I f n := by
  ext x
  simp

def adicCompletion.mk (a : ℕ → M) (hcomp : ∀ {m n : ℕ} (hle : m ≤ n),
    adicCompletion.transitionMap I hle (Submodule.Quotient.mk (a n))
      = Submodule.Quotient.mk (a m)) : adicCompletion I M := ⟨
  fun n ↦ Submodule.Quotient.mk (a n), by
    rw [adicCompletion.mem]
    intro k l hkl
    exact hcomp hkl
  ⟩

@[simp]
lemma adicCompletion.mk_eval (a : ℕ → M) (hcomp : ∀ {m n : ℕ} (hle : m ≤ n),
    adicCompletion.transitionMap I hle (Submodule.Quotient.mk (a n))
      = Submodule.Quotient.mk (a m)) (n : ℕ) :
    adicCompletion.eval I M n (adicCompletion.mk I a hcomp) = Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (a n) :=
  rfl

def adicCompletion.lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), adicCompletion.transitionMap I hle ∘ₗ f n = f m) :
    M →ₗ[R] adicCompletion I N where
  toFun := fun x ↦ ⟨fun n ↦ f n x, by
      rw [adicCompletion.mem]
      intro k l hkl
      change ((transitionMap I hkl) ∘ₗ (f l)) x = _
      rw [h hkl]
    ⟩
  map_add' := by aesop
  map_smul' := by aesop

@[simp]
lemma adicCompletion.lift_eval (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), adicCompletion.transitionMap I hle ∘ₗ f n = f m)
    (n : ℕ) (x : M) :
    adicCompletion.eval I N n (adicCompletion.lift I f h x) = f n x :=
  rfl

def LinearMap.adicCompletion (f : M →ₗ[R] N) :
    adicCompletion I M →ₗ[R] adicCompletion I N := by
  fapply adicCompletion.lift I
  · intro n
    exact adicCompletionAux I f n ∘ₗ adicCompletion.eval I M n
  · intro m n hmn
    rw [← comp_assoc, ← LinearMap.adicCompletionAux_comm, comp_assoc]
    simp

@[simp]
lemma LinearMap.adicCompletion_eval (f : M →ₗ[R] N) (n : ℕ) (x : _root_.adicCompletion I M) :
    adicCompletion.eval I N n (f.adicCompletion I x) = adicCompletionAux I f n (adicCompletion.eval I M n x) :=
  rfl

lemma adicCompletion.zero_iff (x : adicCompletion I M) :
    x = 0 ↔ ∃ (k : ℕ), ∀ {n : ℕ} (_ : k ≤ n), adicCompletion.eval I M n x = 0 := by
  constructor
  · intro hx
    use 0
    intro n _
    rw [hx, map_zero]
  · intro ⟨k, hk⟩
    have (n : ℕ) : eval I M n x = 0 := by
      have : (eval I M (n + k) x) = 0 := hk (by omega)
      have hn : n ≤ n + k := by
        omega
      rw [← adicCompletion.transitionMap_comp_eval I hn]
      simp only [LinearMap.comp_apply]
      rw [this]
      simp
    ext n
    rw [this]
    simp

lemma adicCompletion.zero_iff' (x : adicCompletion I M) :
    x = 0 ↔ ∃ (k : ℕ), ∀ {n : ℕ} (_ : k ≤ n), adicCompletion.eval I M (n - k) x = 0 := by
  constructor
  · intro hx
    use 0
    intro n _
    rw [hx, map_zero]
  · intro ⟨k, hk⟩
    have (n : ℕ) : eval I M n x = 0 := by
      have h : n + k - k = n := by
        simp
      rw [← h]
      exact hk (by omega)
    ext n
    rw [this]
    simp

lemma adicCompletion.inductionOn {p : adicCompletion I M → Prop} (x : adicCompletion I M)
    (h : ∀ (a : ℕ → M) (hcomp : ∀ {m n : ℕ} (hle : m ≤ n),
      adicCompletion.transitionMap I hle (Submodule.Quotient.mk (a n))
        = Submodule.Quotient.mk (a m)), p (adicCompletion.mk I a hcomp)) : p x := by
  have hex (n : ℕ) : ∃ (z : M), Submodule.mkQ (I ^ n • ⊤ : Submodule R M) z = adicCompletion.eval I M n x :=
    Quotient.exists_rep (adicCompletion.eval I M n x)
  choose a ha using hex
  have hcomp {m n : ℕ} (hle : m ≤ n) :
      adicCompletion.transitionMap I hle (Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (a n))
        = Submodule.mkQ (I ^ m • ⊤ : Submodule R M) (a m) := by
    rw [ha, ha]
    simp [-adicCompletion.coe_eval]
  have heq : adicCompletion.mk I a hcomp = x := by
    ext n
    rw [← ha]
    simp
  rw [← heq]
  exact h a hcomp

variable [IsNoetherianRing R] [Module.Finite R N]

theorem LinearMap.adicCompletion_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.adicCompletion I) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply adicCompletion.inductionOn I x
  intro a hcomp hx
  let M' : Submodule R N := LinearMap.range f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I M'
  rw [adicCompletion.zero_iff']
  use k
  intro n hkn
  have he (n : ℕ) : adicCompletion.eval I N n (f.adicCompletion I (adicCompletion.mk I a hcomp)) = 0 := by
    rw [hx]
    simp
  simp only [adicCompletion.mk_eval, Submodule.mkQ_apply]
  simp at he
  have hincl : I ^ (n - k) • (I ^ k • ⊤ ⊓ M') ≤ I ^ (n - k) • M' := by
    apply Submodule.smul_mono
    rfl
    apply inf_le_right
  have : a n ∈ (I ^ (n - k) • ⊤ : Submodule R M) := by
    rw [← Submodule.comap_map_eq_of_injective hf (I ^ (n - k) • ⊤ : Submodule R M)]
    change f (a n) ∈ Submodule.map f (I ^ (n - k) • ⊤)
    rw [Submodule.map_smul'', Submodule.map_top]
    apply hincl
    rw [← hk n hkn]
    exact ⟨he n, ⟨a n, rfl⟩⟩
  rw [← hcomp (by omega : (n - k) ≤ n)]
  simpa
