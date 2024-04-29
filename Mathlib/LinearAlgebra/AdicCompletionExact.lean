import Mathlib.LinearAlgebra.AdicCompletion
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Exact

universe u v w t

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]
variable {P : Type u} [AddCommGroup P] [Module R P]

def adicCompletion.transitionMap {m n : ℕ} (h : m ≤ n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) := by
  apply Submodule.mapQ _ _ LinearMap.id
  exact Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl

@[simp]
lemma adicCompletion.transitionMap_apply_mk {m n : ℕ} (h : m ≤ n) (x : M) :
    (adicCompletion.transitionMap I h) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp [transitionMap]

@[simp]
lemma adicCompletion.transitionMap_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    transitionMap I hmn ∘ₗ transitionMap I hnk = transitionMap (M := M) I (Nat.le_trans hmn hnk) := by
  rw [← LinearMap.cancel_right (Submodule.mkQ_surjective _)]
  ext
  simp

@[simp]
lemma adicCompletion.transitionMap_id {n : ℕ} :
    transitionMap (M := M) I (le_refl n) = LinearMap.id := by
  rw [← LinearMap.cancel_right (Submodule.mkQ_surjective _)]
  ext
  simp

lemma adicCompletion.mem (x : ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    x ∈ adicCompletion I M ↔ ∀ {m n : ℕ} (h : m ≤ n), transitionMap I h (x n) = x m := by
  rfl

lemma adicCompletion.mem' (x : ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    x ∈ adicCompletion I M ↔ ∀ (n : ℕ), transitionMap I (Nat.le_succ n) (x (n + 1)) = x n := by
  rw [adicCompletion.mem]
  constructor
  · intro h n
    exact h _
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
        simp
    | succ n hmn ih =>
        rw [← transitionMap_comp I hmn (by omega)]
        simp [-transitionMap_comp, h n, ih]

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

def adicCompletion.mk' (a : ℕ → M)
    (h : ∀ (n : ℕ), a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M)) :
    adicCompletion I M := ⟨
  fun n ↦ Submodule.Quotient.mk (a n), by
    rw [adicCompletion.mem']
    intro n
    simp only [transitionMap_apply_mk, Submodule.Quotient.eq]
    exact h n
  ⟩

@[simp]
lemma adicCompletion.mk_eval (a : ℕ → M) (hcomp : ∀ {m n : ℕ} (hle : m ≤ n),
    adicCompletion.transitionMap I hle (Submodule.Quotient.mk (a n))
      = Submodule.Quotient.mk (a m)) (n : ℕ) :
    adicCompletion.eval I M n (adicCompletion.mk I a hcomp) = Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (a n) :=
  rfl

@[simp]
lemma adicCompletion.mk'_eval (a : ℕ → M)
    (h : ∀ (n : ℕ), a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M)) (n : ℕ) :
    adicCompletion.eval I M n (adicCompletion.mk' I a h) = Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (a n) :=
  rfl

def adicCompletion.exists_rep' (x : adicCompletion I M) :
    ∃ (a : ℕ → M) (h : ∀ (n : ℕ), a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M)),
    adicCompletion.mk' I a h = x := by
  have hex (n : ℕ) : ∃ (z : M), Submodule.mkQ (I ^ n • ⊤ : Submodule R M) z = adicCompletion.eval I M n x :=
    Quotient.exists_rep (adicCompletion.eval I M n x)
  choose a ha using hex
  use a
  simp only [Submodule.mkQ_apply] at ha
  have h (n : ℕ) : a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M) := by
    rw [← Submodule.Quotient.eq]
    rw [ha n]
    have : Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (a (n + 1)) =
      adicCompletion.transitionMap I (Nat.le_succ n)
      (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule R M) (a (n + 1))) := by
        simp
    change Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (a (n + 1)) = eval I M n x
    rw [this]
    simp only [Submodule.mkQ_apply]
    rw [ha]
    simp [-adicCompletion.coe_eval]
  use h
  ext n
  simp
  exact ha n

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

def adicCompletion.inductionOn {p : adicCompletion I M → Prop} (x : adicCompletion I M)
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

def adicCompletion.inductionOn' {p : adicCompletion I M → Prop} (x : adicCompletion I M)
    (h : ∀ (a : ℕ → M) (hcomp : ∀ (n : ℕ), a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M)),
      p (adicCompletion.mk' I a hcomp)) :
    p x := by
  obtain ⟨a, h1, h2⟩ := adicCompletion.exists_rep' I x
  rw [← h2]
  exact h a h1

section

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
  apply adicCompletion.inductionOn' I y
  intro b hcomp
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


--def adicCompletion.lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
--    (h : ∀ {m n : ℕ} (hle : m ≤ n), adicCompletion.transitionMap I hle ∘ₗ f n = f m) :
--    M →ₗ[R] adicCompletion I N where
--  toFun

def adicCompletion.evalRing (n : ℕ) : adicCompletion I R →ₗ[R] R ⧸ I^n :=
  let f : adicCompletion I R →ₗ[R] R ⧸ (I^n • ⊤ : Submodule R R) :=
    eval I R n
  let g :  R ⧸ (I^n • ⊤ : Submodule R R) →ₗ[R] R ⧸ I^n :=
    have h : (I^n • ⊤ : Submodule R R) = I^n := by
      ext x
      simp
    Ideal.quotientEquivAlgOfEq R h
  g.comp f

open TensorProduct

def adicCompletion.Subring : Subring (∀ n , R ⧸ (I^n • ⊤ : Ideal R)) where
  carrier := adicCompletion I R
  mul_mem' := by
    intro a b ha hb
    intro m n hmn
    simp
    obtain ⟨x, h, hx⟩ := adicCompletion.exists_rep' I ⟨a , ha⟩
    obtain ⟨y, g, gy⟩ := adicCompletion.exists_rep' I ⟨b , hb⟩
    have hx' : (mk' I x h).val = a := by
      rw[hx]
    rw[← hx']
    have hy' : (mk' I y g).val = b := by
      rw[gy]
    rw[← hy']
    have : (mk' I x h).val n = Ideal.Quotient.mk (I^n • ⊤ : Ideal R) (x n) := sorry
    rw[this]
    have : (mk' I y g).val n = Ideal.Quotient.mk (I^n • ⊤ : Ideal R) (y n) := sorry
    rw[this]
    simp
    rw[← _root_.map_mul]
    rw[← Ideal.Quotient.mk_eq_mk]
    erw[Submodule.liftQ_apply]
    simp
    have : (mk' I x h).val m = Ideal.Quotient.mk (I^m • ⊤ : Ideal R) (x m) := sorry
    rw[this]
    have : (mk' I y g).val m = Ideal.Quotient.mk (I^m • ⊤ : Ideal R) (y m) := sorry
    rw[this]
    sorry
    --simp[- Ideal.Quotient.mk_eq_mk]
  one_mem' := sorry
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

instance : CommRing (adicCompletion I R) := sorry
--instance (n : ℕ) : Module (R ⧸ (I^n • ⊤ : Submodule R R)) (M ⧸ (I^n • ⊤ : Submodule R M)) := sorry

/-
def adicCompletion.tensorProductaux (x : adicCompletion I R) : M →ₗ[R] (adicCompletion I M) where
  toFun y := ⟨ fun n ↦ eval I R n x • Submodule.mkQ (I^n • ⊤ : Submodule R M) y,
    by
    obtain ⟨a, h, rfl⟩ := adicCompletion.exists_rep' I x
    intro m n hmn
    simp
    sorry
    /- by
    obtain ⟨a, h, rfl⟩ := adicCompletion.exists_rep' I x
    intro m n hmn
    --apply adicCompletion.inductionOn' I x
    simp -/
    ⟩

noncomputable def adicCompletion.tensorProduct : (adicCompletion I R) ⊗[R] M →ₗ[R] (adicCompletion I M) := by
  apply TensorProduct.lift sorry

-/
