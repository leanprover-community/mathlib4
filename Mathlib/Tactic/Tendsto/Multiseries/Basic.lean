import Mathlib.Tactic.Tendsto.Multiseries.SeqLemmas
import Mathlib.Data.Seq.Seq
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

open Filter Asymptotics Stream' Seq

abbrev Basis := List (ℝ → ℝ)

abbrev PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ tl => Seq (ℝ × PreMS tl)

namespace PreMS

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => default
  | .cons _ _ => default

def leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) : WithBot ℝ :=
  match destruct ms with
  | none => ⊥
  | some ((deg, _), _) => deg

@[simp]
theorem leadingExp_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    leadingExp (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = ⊥ := by
  simp [leadingExp]

@[simp]
theorem leadingExp_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    leadingExp (basis_hd := basis_hd) (basis_tl := basis_tl) (Seq.cons (deg, coef) tl) = deg := by
  simp [leadingExp]

theorem leadingExp_of_head {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    ms.leadingExp = ms.head.elim ⊥ (fun (deg, _) ↦ deg) := by
  apply ms.recOn <;> simp [leadingExp]

theorem leadingExp_eq_bot {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    ms = .nil ↔ ms.leadingExp = ⊥ := by
  apply ms.recOn
  · simp [leadingExp]
  · intros
    simp [leadingExp]

theorem leadingExp_eq_coe {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {deg : ℝ} (h : ms.leadingExp = ↑deg) : ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)), ms = .cons (deg, a.1) a.2 := by
  revert h
  apply ms.recOn
  · intro h
    simp [leadingExp] at h
  · intro (deg', coef) tl h
    simp [leadingExp] at h
    subst h
    use (coef, tl)

scoped instance {basis : _} : Preorder (ℝ × PreMS basis) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := by simp
  le_trans := by
    intro x y z hxy hyz
    simp at *
    trans y.1 <;> assumption

-- TODO: can be simpler??
private theorem lt_iff_lt {basis : _} {deg1 deg2 : ℝ} {coef1 coef2 : PreMS basis} :
    (deg1, coef1) < (deg2, coef2) ↔ deg1 < deg2 := by
  constructor
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h

-- theorem lt_of_leadingExp_gt {}

inductive WellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : WellOrdered ms
| colist {hd : _} {tl : _} (ms : PreMS (hd :: tl))
    (h_coef : ∀ i x, ms.get? i = .some x → x.2.WellOrdered)
    (h_sorted : Seq.Sorted (· > ·) ms) : ms.WellOrdered

theorem WellOrdered.nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    WellOrdered (basis := basis_hd :: basis_tl) .nil := by
  constructor
  · intro i x
    intro h
    simp at h
  · intro i j x y _ h
    simp at h

theorem WellOrdered.cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} (h_coef : coef.WellOrdered) :
    WellOrdered (basis := basis_hd :: basis_tl) <| .cons (deg, coef) .nil := by
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
  · intro i j x y h_lt _ hj
    cases j with
    | zero => simp at h_lt
    | succ k => simp at hj

-- theorem WellOrdered.cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg1 deg2 : ℝ}
--     {coef1 coef2 : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
--     (h_coef1 : coef1.WellOrdered) (h_coef2: coef2.WellOrdered)
--     (h_tl : tl.WellOrdered) (h_lt : deg1 > deg2) :
--     WellOrdered (basis := basis_hd :: basis_tl) (.cons (deg1, coef1) (.cons (deg2, coef2) tl)) := by
--   cases h_tl with | colist _ h_tl_coef h_tl_tl =>
--   constructor
--   · intro i (deg, coef)
--     cases i with
--     | zero =>
--       simp
--       intro _ h
--       exact h ▸ h_coef1
--     | succ j =>
--       cases j with
--       | zero =>
--         simp
--         intro _ h
--         exact h ▸ h_coef2
--       | succ k =>
--         simp
--         simp at h_tl_coef
--         solve_by_elim
--   · intro i j x y h hi hj
--     sorry -- many cases

theorem WellOrdered.cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (h_coef : coef.WellOrdered)
    (h_comp : tl.leadingExp < deg)
    (h_tl : tl.WellOrdered) :
    WellOrdered (basis := basis_hd :: basis_tl) <| .cons (deg, coef) tl := by
  cases h_tl with | colist _ h_tl_coef h_tl_tl =>
  constructor
  · intro i x h
    cases i with
    | zero =>
      simp at h
      rw [← h]
      simpa
    | succ j =>
      simp at h
      simp at h_tl_coef
      solve_by_elim
  · apply Seq.Sorted.cons
    · revert h_comp
      apply tl.recOn
      · simp
      · simp [leadingExp]
        intro a b h
        rwa [lt_iff_lt]
    · exact h_tl_tl

theorem WellOrdered_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)}
    (h : WellOrdered (basis := basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    coef.WellOrdered ∧ tl.leadingExp < deg ∧ tl.WellOrdered := by
  cases h with | colist _ h_coef h_sorted =>
  replace h_sorted := Seq.Sorted_cons h_sorted
  constructor
  · specialize h_coef 0 (deg, coef)
    simpa using h_coef
  constructor
  · revert h_sorted
    apply tl.recOn
    · simp [leadingExp]
    · intro (tl_deg, tl_coef) tl_tl h_sorted
      simp [lt_iff_lt] at h_sorted
      simp [leadingExp]
      exact h_sorted.left
  · constructor
    · intro i x hx
      specialize h_coef (i + 1) x
      simp at h_coef hx
      exact h_coef hx
    · exact h_sorted.right

theorem WellOrdered.coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ ms, motive ms →
      (ms = .nil) ∨
      (
        ∃ deg coef, ∃ (tl : PreMS (basis_hd :: basis_tl)), ms = .cons (deg, coef) tl ∧
        coef.WellOrdered ∧
        tl.leadingExp < deg ∧
        motive tl
      )
    ) {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive ms) : ms.WellOrdered := by
  have h_all : ∀ n, motive (ms.drop n) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [Seq.drop]
      specialize h_survive _ ih
      cases h_survive with
      | inl h_ms_eq =>
        rw [h_ms_eq] at ih ⊢
        simpa
      | inr h =>
        obtain ⟨deg, coef, tl, h_ms_eq, _, _, h_tl⟩ := h
        rw [h_ms_eq]
        simp
        exact h_tl
  constructor
  · intro i x hx
    simp [← head_dropn] at hx
    specialize h_survive _ (h_all i)
    cases h_survive with
    | inl h_ms_eq =>
      rw [h_ms_eq] at hx
      simp at hx
    | inr h =>
      obtain ⟨deg, coef, tl, h_ms_eq, h_coef, h_comp, h_tl⟩ := h
      rw [h_ms_eq] at hx
      simp at hx
      simpa [← hx]
  · refine Seq.Sorted.coind motive ?_ h
    intro hd tl ih
    specialize h_survive _ ih
    simp [Seq.cons_eq_cons] at h_survive
    obtain ⟨deg, coef, tl, ⟨h_hd_eq, h_tl_eq⟩, h_coef, h_comp, h_tl⟩ := h_survive
    subst h_hd_eq h_tl_eq
    constructor
    · revert h_comp
      apply tl.recOn
      · simp
      simp [leadingExp, lt_iff_lt]
    · exact h_tl

def allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) (a : ℝ) :
    Prop :=
  ms.All fun (deg, coef) ↦ deg < a

theorem WellOrdered_allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} {a : ℝ}
    (h_wo : ms.WellOrdered) (h_lt : ms.leadingExp < a) : ms.allLt a := by
  simp only [allLt]
  let motive : PreMS (basis_hd :: basis_tl) → Prop := fun ms =>
    ms.leadingExp < a ∧ ms.WellOrdered
  apply Seq.All.coind motive
  · intro (deg, coef) tl ih
    simp [motive, leadingExp] at ih
    obtain ⟨h_lt, h_wo⟩ := ih
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    constructor
    · exact h_lt
    simp only [motive]
    constructor
    · trans
      · exact h_comp
      · simp [h_lt]
    · exact h_tl_wo
  · simp only [motive]
    constructor
    · exact h_lt
    · exact h_wo

theorem WellOrdered_cons_allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} {a : ℝ}
    (h_wo : WellOrdered (basis := basis_hd :: basis_tl) (Seq.cons (deg, coef) tl))
    (h_lt : deg < a) :
    allLt (basis_hd := basis_hd) (Seq.cons (deg, coef) tl) a := by
  apply WellOrdered_allLt h_wo
  simpa [leadingExp]

def majorated (f basis_hd : ℝ → ℝ) (deg : ℝ) : Prop :=
  ∀ deg', deg < deg' → f =o[atTop] (fun x ↦ (basis_hd x)^deg')

theorem majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {deg : ℝ} (h_eq : g =ᶠ[atTop] f)
    (h : majorated f basis_hd deg) : majorated g basis_hd deg := by
  simp only [majorated] at *
  intro deg' h_deg
  specialize h deg' h_deg
  exact EventuallyEq.trans_isLittleO h_eq h

-- to upstream?
theorem majorated_self {f : ℝ → ℝ} {deg : ℝ}
    (h : Tendsto f atTop atTop) :
    majorated (fun x ↦ (f x)^deg) f deg := by
  simp only [majorated]
  intro deg' h_deg
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun x ↦ f x ^ deg / f x ^ deg') =ᶠ[atTop] fun x ↦ (f x)^(deg - deg') := by
      apply Eventually.mono <| Tendsto.eventually_gt_atTop h 0
      intro x h
      simp only
      rw [← Real.rpow_sub h]
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun x ↦ f x ^ (deg - deg')) = ((fun x ↦ x^(-(deg' - deg))) ∘ f) by ext; simp]
    apply Tendsto.comp _ h
    apply tendsto_rpow_neg_atTop
    linarith
  · apply Eventually.mono <| Tendsto.eventually_gt_atTop h 0
    intro x h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

theorem majorated_of_lt {f basis_hd : ℝ → ℝ} {deg1 deg2 : ℝ}
    (h_lt : deg1 < deg2) (h : majorated f basis_hd deg1) :
    majorated f basis_hd deg2 := by
  simp [majorated] at *
  intro deg' h_deg
  apply h _ (by linarith)

theorem majorated_tendsto_zero_of_neg {f basis_hd : ℝ → ℝ} {deg : ℝ}
    (h_lt : deg < 0) (h : majorated f basis_hd deg) :
    Tendsto f atTop (nhds 0) := by
  simp [majorated] at h
  specialize h 0 (by linarith)
  simpa using h

theorem add_majorated {f g basis_hd : ℝ → ℝ} {f_deg g_deg : ℝ} (hf : majorated f basis_hd f_deg)
    (hg : majorated g basis_hd g_deg) (h_pos : ∀ᶠ x in atTop, 0 < basis_hd x)
    : majorated (f + g) basis_hd (f_deg ⊔ g_deg) := by
  simp only [majorated] at *
  intro deg h_deg
  simp at h_deg
  apply IsLittleO.add
  · exact hf _ h_deg.left
  · exact hg _ h_deg.right

theorem mul_majorated {f g basis_hd : ℝ → ℝ} {f_deg g_deg : ℝ} (hf : majorated f basis_hd f_deg)
    (hg : majorated g basis_hd g_deg) (h_pos : ∀ᶠ x in atTop, 0 < basis_hd x)
    : majorated (f * g) basis_hd (f_deg + g_deg) := by
  simp only [majorated] at *
  intro deg h_deg
  let ε := (deg - f_deg - g_deg) / 2
  specialize hf (f_deg + ε) (by dsimp [ε]; linarith)
  specialize hg (g_deg + ε) (by dsimp [ε]; linarith)
  apply IsLittleO.trans_eventuallyEq (g₁ := fun x ↦ basis_hd x ^ (f_deg + ε) * basis_hd x ^ (g_deg + ε))
  · exact IsLittleO.mul hf hg
  · simp only [EventuallyEq]
    apply Eventually.mono h_pos
    intro x hx
    conv =>
      rhs
      rw [show deg = (f_deg + ε) + (g_deg + ε) by dsimp [ε]; ring_nf]
      rw [Real.rpow_add hx]

noncomputable def partialSumsFrom (Cs : Seq (ℝ → ℝ)) (degs : Seq ℝ) (basis_fun : ℝ → ℝ)
    (init : ℝ → ℝ) : Seq (ℝ → ℝ) :=
  Cs.zip degs |>.fold init fun acc (C, deg) =>
    fun x ↦ acc x + (basis_fun x)^deg * (C x)

noncomputable def partialSums (Cs : Seq (ℝ → ℝ)) (degs : Seq ℝ) (basis_fun : ℝ → ℝ) :
    Seq (ℝ → ℝ) :=
  partialSumsFrom Cs degs basis_fun 0

theorem partialSumsFrom_nil {degs : Seq ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom .nil degs basis_fun init = .cons init .nil := by
  simp [partialSumsFrom]

theorem partialSumsFrom_cons {Cs_hd : ℝ → ℝ} {Cs_tl : Seq (ℝ → ℝ)} {degs_hd : ℝ}
    {degs_tl : Seq ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom (.cons Cs_hd Cs_tl) (.cons degs_hd degs_tl) basis_fun init =
    (.cons init <| partialSumsFrom Cs_tl degs_tl basis_fun
      (fun x ↦ init x + (basis_fun x)^degs_hd * (Cs_hd x))) := by
  simp [partialSumsFrom]

theorem partialSumsFrom_eq_map {Cs : Seq (ℝ → ℝ)} {degs : Seq ℝ} {basis_fun : ℝ → ℝ}
    {init : ℝ → ℝ} (h : Cs.atLeastAsLongAs degs) :
    partialSumsFrom Cs degs basis_fun init =
      (partialSums Cs degs basis_fun).map fun G => init + G := by

  let motive : Seq (ℝ → ℝ) → Seq (ℝ → ℝ) → Prop := fun x y =>
    ∃ Cs degs init D,
      Cs.atLeastAsLongAs degs ∧
      (
        (x = partialSumsFrom Cs degs basis_fun (D + init)) ∧
        (y = (partialSumsFrom Cs degs basis_fun init).map fun G => D + G)
      ) ∨
      (x = .nil ∧ y = .nil)
  apply Seq.Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    obtain ⟨Cs', degs', init', D, ih⟩ := ih
    cases' ih with ih ih
    · left
      obtain ⟨h_alal, h_x_eq, h_y_eq⟩ := ih
      revert h_alal h_x_eq h_y_eq
      apply degs'.recOn
      · simp [partialSums, partialSumsFrom]
        intro h_x_eq h_y_eq
        use D + init'
        use .nil
        constructor
        · assumption
        use .nil
        constructor
        · assumption
        simp [motive]
      · intro degs_hd degs_tl h_alal h_x_eq h_y_eq
        obtain ⟨Cs_hd, Cs_tl, h_Cs⟩ := Seq.atLeastAsLongAs_cons h_alal
        subst h_Cs
        simp [partialSums, partialSumsFrom_cons] at h_x_eq h_y_eq
        use D + init'
        use (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ D x + init' x +
          basis_fun x ^ degs_hd * Cs_hd x)
        use (Seq.map (fun G ↦ D + G) (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ init' x +
          basis_fun x ^ degs_hd * Cs_hd x))
        constructor
        · assumption
        constructor
        · assumption
        simp [motive]
        simp at h_alal
        use Cs_tl
        use degs_tl
        use fun x ↦ init' x + basis_fun x ^ degs_hd * Cs_hd x
        use D
        left
        constructor
        · assumption
        constructor
        · congr
          eta_expand
          simp
          ext
          ring_nf
        rfl
    · right
      exact ih
  · simp [motive]
    use Cs
    use degs
    use 0
    use init
    left
    constructor
    · assumption
    constructor
    · simp
    · simp [partialSums]

-- a non valid occurrence of the datatypes being declared
-- inductive Approximates : (ℝ → ℝ) → (basis : Basis) → PreMS basis → Prop where
-- | const {c : ℝ} {F : ℝ → ℝ} (h : F =ᶠ[atTop] fun _ ↦ c) : Approximates F [] c
-- | colist {F basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl))
--   (Cs : CoList (ℝ → ℝ))
--   (h_coef : (Cs.zip ms).all fun (C, (deg, coef)) => Approximates C basis_tl coef)
--   (h_comp : (partialSums Cs (ms.map fun x => x.1) basis_hd).zip (ms.map fun x => x.1) |>.all
--     fun (ps, deg) => ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[atTop]
--       (fun x ↦ (basis_hd x)^deg')) :
--   Approximates F (basis_hd :: basis_tl) ms

def Approximates (F : ℝ → ℝ) (basis : Basis) (ms : PreMS basis) : Prop :=
  match basis with
  | [] => F =ᶠ[atTop] fun _ ↦ ms
  | List.cons basis_hd basis_tl =>
    ∃ Cs : Seq (ℝ → ℝ),
    Cs.atLeastAsLongAs ms ∧
    ((Cs.zip ms).All fun (C, (_, coef)) => Approximates C basis_tl coef) ∧
    (
      let degs := ms.map fun x => x.1;
      let degs' : Seq (Option ℝ) := (degs.map .some).append (.cons .none .nil);
      (partialSums Cs degs basis_hd).zip degs' |>.All fun (ps, deg?) =>
        match deg? with
        | .some deg =>
          majorated (fun x ↦ F x - ps x) basis_hd deg
        | .none => (fun x ↦ F x - ps x) =ᶠ[atTop] 0
    )

theorem Approximates_nil {F basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : Approximates F (basis_hd :: basis_tl) Seq.nil) :
    F =ᶠ[atTop] 0 := by
  unfold Approximates at h
  obtain ⟨Cs, _, _, h_comp⟩ := h
  simp at h_comp
  apply Seq.all_get at h_comp
  unfold Seq.All at h_comp
  specialize h_comp (n := 0)
  simpa [partialSums, partialSumsFrom] using h_comp

theorem Approximates_cons {F basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : Approximates F (basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    ∃ C,
      Approximates C basis_tl coef ∧
      majorated F basis_hd deg ∧
      Approximates (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl) tl := by
  unfold Approximates at h
  obtain ⟨Cs, h_alal, h_coef, h_comp⟩ := h
  obtain ⟨C, Cs_tl, h_alal⟩ := Seq.atLeastAsLongAs_cons h_alal
  subst h_alal
  use C
  simp at h_coef
  constructor
  · exact h_coef.left
  · constructor
    · simp [partialSums, partialSumsFrom] at h_comp
      exact h_comp.left
    · simp at h_alal
      unfold Approximates
      use Cs_tl
      constructor
      · assumption
      · constructor
        · exact h_coef.right
        · simp [partialSums, partialSumsFrom_cons] at h_comp
          replace h_comp := h_comp.right
          rw [partialSumsFrom_eq_map (Seq.atLeastAsLongAs_map h_alal)] at h_comp
          rw [Seq.map_zip_left] at h_comp
          replace h_comp := Seq.map_all_iff.mp h_comp
          apply Seq.all_mp _ h_comp
          intro (C', deg?)
          simp
          intro h
          ring_nf at h
          ring_nf
          exact h

private structure Approximates_coind_auxT (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (basis_hd : ℝ → ℝ) (basis_tl : Basis) where
  val : PreMS (basis_hd :: basis_tl)
  F : ℝ → ℝ
  h : motive F basis_hd basis_tl val

theorem Approximates.coind' (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ basis_hd basis_tl F ms, motive F basis_hd basis_tl ms →
      (ms = .nil ∧ F =ᶠ[atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (Approximates C basis_tl coef) ∧
        majorated F basis_hd deg ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) basis_hd basis_tl tl)
      )
    ) {basis_hd : ℝ → ℝ} {basis_tl : Basis} {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F basis_hd basis_tl ms) : Approximates F (basis_hd :: basis_tl) ms := by
  simp [Approximates]
  let T := Approximates_coind_auxT motive basis_hd basis_tl
  let g : T → Option ((ℝ → ℝ) × T) := fun ⟨val, F, h⟩ =>
    (val.recOn (motive := fun ms => motive F basis_hd basis_tl ms → Option ((ℝ → ℝ) × T))
    (nil := fun _ => .none)
    (cons := fun (deg, coef) tl =>
      fun h =>
        have spec : ∃ C,
            Approximates C basis_tl coef ∧
            majorated F basis_hd deg ∧
            motive (fun x ↦ F x - basis_hd x ^ deg * C x) basis_hd basis_tl tl := by
          specialize h_survive _ _ _ _ h
          simp [Seq.cons_eq_cons] at h_survive
          obtain ⟨deg_1, coef_1, tl_1, ⟨⟨h_deg, h_coef⟩, h_tl⟩, h_survive⟩ := h_survive
          subst h_deg
          subst h_coef
          subst h_tl
          exact h_survive
        let C := spec.choose
        .some (C, ⟨tl, fun x ↦ F x - (basis_hd x)^deg * (C x), spec.choose_spec.right.right⟩)
    )
    ) h
  let Cs : Seq (ℝ → ℝ) := Seq.corec g ⟨ms, F, h⟩
  use Cs
  constructor
  · let motive' : Seq (ℝ → ℝ) → Seq (ℝ × PreMS basis_tl) → Prop := fun Cs ms =>
      ∃ F h, Cs = (Seq.corec g ⟨ms, F, h⟩)
    apply Seq.atLeastAsLong.coind motive'
    · intro Cs ms ih (deg, coef) tl h_ms_eq
      simp only [motive'] at ih
      obtain ⟨F, h, h_Cs_eq⟩ := ih
      subst h_ms_eq
      rw [Seq.corec_cons] at h_Cs_eq
      pick_goal 2
      · simp [g]
        constructor <;> rfl
      use ?_
      use ?_
      constructor
      · exact h_Cs_eq
      simp only [motive']
      generalize_proofs p1 p2
      use fun x ↦ F x - basis_hd x ^ deg * p1.choose x
      use p2
    · simp only [motive']
      use F
      use h
  · constructor
    · let motive' : Seq ((ℝ → ℝ) × ℝ × PreMS basis_tl) → Prop := fun li =>
        ∃ (ms : Seq (ℝ × PreMS basis_tl)), ∃ F h,
          li = (Seq.corec g ⟨ms, F, h⟩).zip ms
      apply Seq.All.coind motive'
      · intro (C, (deg, coef)) tl ih
        simp only
        simp only [motive'] at ih
        obtain ⟨ms, F, h, h_eq⟩ := ih
        specialize h_survive _ _ _ _ h
        revert h h_eq h_survive
        apply ms.recOn
        · intro h h_eq h_survive
          simp at h_eq
        · intro (ms_deg, ms_coef) ms_tl h h_eq h_survive
          rw [Seq.corec_cons] at h_eq
          pick_goal 2
          · simp [g]
            constructor <;> rfl
          simp [Seq.cons_eq_cons] at h_eq
          obtain ⟨⟨h1, ⟨h2, h3⟩⟩, h_eq⟩ := h_eq
          constructor
          · subst h1
            subst h2
            subst h3
            generalize_proofs p
            exact p.choose_spec.left
          · simp only [motive']
            use ?_
            use ?_
            use ?_
      · simp only [motive']
        use ms
        use F
        use h
    · simp [partialSums]
      let motive' : Seq ((ℝ → ℝ) × Option ℝ) → Prop := fun li =>
        li = .nil ∨ ∃ (ms : Seq (ℝ × PreMS basis_tl)), ∃ G h init,
          li = ((partialSumsFrom (Seq.corec g ⟨ms, G, h⟩) (Seq.map (fun x ↦ x.1) ms) basis_hd init).zip
      ((Seq.map some (Seq.map (fun x ↦ x.1) ms)).append (Seq.cons none Seq.nil))) ∧
      G + init =ᶠ[atTop] F
      apply Seq.All.coind motive'
      · intro (F', deg?) li_tl ih
        simp only [motive'] at ih
        cases ih with
        | inl ih => simp at ih
        | inr ih =>
        obtain ⟨ms, G, h_mot, init, h_eq, hF_eq⟩ := ih
        · simp
          revert h_mot h_eq
          apply ms.recOn
          · intro h_mot h_eq
            rw [Seq.corec_nil] at h_eq
            pick_goal 2
            · simp [g]
            simp [Seq.cons_eq_cons, partialSumsFrom_nil] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            specialize h_survive _ _ _ _ h_mot
            cases h_survive with
            | inr h_survive => simp at h_survive
            | inl h_survive =>
              simp at h_survive
              constructor
              · apply eventuallyEq_iff_sub.mp
                trans
                · exact hF_eq.symm
                conv => rhs; ext x; rw [← zero_add (F' x)]
                apply EventuallyEq.add h_survive
                rfl
              · simp [motive']
          · intro (deg, coef) tl h_mot h_eq
            rw [Seq.corec_cons] at h_eq
            swap
            · simp [g]
              constructor <;> rfl
            simp [Seq.cons_eq_cons, partialSumsFrom_cons] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            constructor
            · intro deg' h_deg
              apply EventuallyEq.trans_isLittleO (f₂ := G)
              · apply eventuallyEq_iff_sub.mpr
                replace hF_eq := eventuallyEq_iff_sub.mp hF_eq.symm
                trans F - (G + F')
                · apply eventuallyEq_iff_sub.mpr
                  eta_expand
                  simp
                  ring_nf!
                  rfl
                · exact hF_eq
              · generalize_proofs h at h_eq
                obtain ⟨_, _, h_comp, _⟩ := h
                apply h_comp _ h_deg
            · simp [motive']
              right
              generalize_proofs h1 h2
              use tl
              use fun x ↦ G x - basis_hd x ^ deg * h1.choose x
              use h2
              use fun x ↦ F' x + basis_hd x ^ deg * h1.choose x
              constructor
              · rfl
              apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs; ext x; rw [show G x + (F' x - F x) = (G x + F' x) - F x by ring]
              apply eventuallyEq_iff_sub.mp
              exact hF_eq
      · simp only [motive']
        right
        use ms
        use F
        use h
        use 0
        constructor
        · rfl
        simp

-- without basis in motive
theorem Approximates.coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ F ms, motive F ms →
      (ms = .nil ∧ F =ᶠ[atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (Approximates C basis_tl coef) ∧
        majorated F basis_hd deg ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) tl)
      )
    ) {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F ms) : Approximates F (basis_hd :: basis_tl) ms := by
  let motive' : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
    fun F' basis_hd' basis_tl' ms' =>
      ∃ (h_hd : basis_hd' = basis_hd) (h_tl : basis_tl' = basis_tl), motive F' (h_tl ▸ (h_hd ▸ ms'))
  apply Approximates.coind' motive'
  · intro basis_hd' basis_tl' F' ms' ih
    simp [motive'] at ih ⊢
    obtain ⟨h_hd, h_tl, ih⟩ := ih
    subst h_hd h_tl
    specialize h_survive F' ms' ih
    cases h_survive with
    | inl h_survive =>
      left
      exact h_survive
    | inr h_survive =>
      right
      obtain ⟨deg, coef, tl, C, h_ms_eq, h_coef, h_comp, h_tl⟩ := h_survive
      use deg
      use coef
      use tl
      constructor
      · exact h_ms_eq
      use C
      constructor
      · exact h_coef
      constructor
      · exact h_comp
      simpa
  · simp [motive']
    assumption

-- Prove with coinduction?
theorem Approximates.nil {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : F =ᶠ[atTop] 0) : Approximates F (basis_hd :: basis_tl) .nil := by
  simp [Approximates]
  use .nil
  simpa [partialSums, partialSumsFrom]

theorem Approximates.cons {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (C : ℝ → ℝ) (h_coef : coef.Approximates C basis_tl)
    (h_comp : majorated F basis_hd deg)
    (h_tl : tl.Approximates (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl)) :
    Approximates F (basis_hd :: basis_tl) (.cons (deg, coef) tl) := by
  simp [Approximates] at h_tl ⊢
  obtain ⟨Cs, h_tl_alal, h_tl_coef, h_tl_comp⟩ := h_tl
  use .cons C Cs
  constructor
  · simpa
  constructor
  · simp
    constructor
    · exact h_coef
    · exact h_tl_coef
  · unfold partialSums at h_tl_comp ⊢
    simp [partialSumsFrom_cons]
    constructor
    · exact h_comp
    · rw [partialSumsFrom_eq_map (Seq.atLeastAsLongAs_map h_tl_alal)] -- copypaste from `Approximates_cons`
      rw [Seq.map_zip_left]
      apply Seq.map_all_iff.mpr
      apply Seq.all_mp _ h_tl_comp
      intro (C', deg?)
      simp
      intro h
      ring_nf at h
      ring_nf
      exact h

---------

theorem Approximates_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {F F' : ℝ → ℝ}
     (h_equiv : F =ᶠ[atTop] F') (h_approx : ms.Approximates F basis) :
    ms.Approximates F' basis :=
  match basis with
  | [] => by
    simp [Approximates] at h_approx
    exact EventuallyEq.trans h_equiv.symm h_approx
  | List.cons basis_hd basis_tl => by
    let motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
      fun F' ms =>
        ∃ F, F =ᶠ[atTop] F' ∧ Approximates F (basis_hd :: basis_tl) ms
    apply Approximates.coind motive
    · intro F' ms ih
      revert ih
      apply ms.recOn
      · intro ih
        left
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := Approximates_nil hF
        constructor
        · rfl
        · exact EventuallyEq.trans h_equiv.symm hF
      · intro (deg, coef) tl ih
        right
        use deg
        use coef
        use tl
        simp
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := Approximates_cons hF
        obtain ⟨C, h_coef, h_comp, h_tl⟩ := hF
        use C
        constructor
        · exact h_coef
        constructor
        · intro deg' h
          apply EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_comp _ h
        · simp [motive]
          use fun x ↦ F x - basis_hd x ^ deg * (C x)
          constructor
          · apply EventuallyEq.sub h_equiv
            apply EventuallyEq.rfl
          · exact h_tl
    · simp only [motive]
      use F

--------------------------------

def const (c : ℝ) (basis : Basis) : PreMS basis :=
  match basis with
  | [] => c
  | List.cons _ basis_tl =>
    .cons (0, const c basis_tl) .nil

def zero (basis) : PreMS basis :=
  match basis with
  | [] => 0
  | List.cons _ _ => .nil

def one (basis : Basis) : PreMS basis :=
  const 1 basis

def monomial (basis : Basis) (n : ℕ) : PreMS basis :=
  match n, basis with
  | 0, [] => 1
  | 0, List.cons basis_hd basis_tl => .cons (1, one _) .nil
  | m + 1, [] => default
  | m + 1, List.cons basis_hd basis_tl => .cons (0, monomial basis_tl m) .nil

instance instZero {basis : Basis} : Zero (PreMS basis) where
  zero := zero basis

end PreMS

structure MS where
  basis : Basis
  val : PreMS basis
  F : ℝ → ℝ
  h_wo : val.WellOrdered
  h_approx : val.Approximates F basis

end TendstoTactic
