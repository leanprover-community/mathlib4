import Mathlib.Tactic.Tendsto.Multiseries.Colist
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

open Filter Asymptotics -- TODO: remove unnecesary prefixes

abbrev Basis := List (ℝ → ℝ)

abbrev PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | _ :: tl => CoList (ℝ × PreMS tl)

namespace PreMS

instance (basis : Basis) : Inhabited (PreMS basis) where
  default := match basis with
  | [] => default
  | _ :: _ => default

def leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) : WithBot ℝ :=
  ms.casesOn'
  (nil := ⊥)
  (cons := fun (deg, _) _ ↦ deg)

@[simp]
theorem leadingExp_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    leadingExp (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = ⊥ := by
  simp [leadingExp]

@[simp]
theorem leadingExp_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    leadingExp (basis_hd := basis_hd) (basis_tl := basis_tl) (CoList.cons (deg, coef) tl) = deg := by
  simp [leadingExp]

theorem leadingExp_of_head {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    ms.leadingExp = ms.head.elim ⊥ (fun (deg, _) ↦ deg) := by
  apply ms.casesOn <;> simp [leadingExp]

theorem leadingExp_eq_bot {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    ms = .nil ↔ ms.leadingExp = ⊥ := by
  apply ms.casesOn
  · simp [leadingExp]
  · intros
    simp [leadingExp]

theorem leadingExp_eq_coe {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {deg : ℝ} (h : ms.leadingExp = ↑deg) : ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)), ms = .cons (deg, a.1) a.2 := by
  revert h
  apply ms.casesOn
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

inductive wellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : wellOrdered ms
| colist {hd : _} {tl : _} (ms : PreMS (hd :: tl))
    (h_coef : ∀ i x, ms.get i = .some x → x.2.wellOrdered)
    (h_sorted : CoList.Sorted (· > ·) ms) : ms.wellOrdered

theorem wellOrdered.nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    wellOrdered (basis := basis_hd :: basis_tl) .nil := by
  constructor
  · intro i x
    intro h
    simp at h
  · intro i j x y _ h
    simp at h

theorem wellOrdered.cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} (h_coef : coef.wellOrdered) :
    wellOrdered (basis := basis_hd :: basis_tl) <| .cons (deg, coef) .nil := by
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

-- theorem wellOrdered.cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg1 deg2 : ℝ}
--     {coef1 coef2 : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
--     (h_coef1 : coef1.wellOrdered) (h_coef2: coef2.wellOrdered)
--     (h_tl : tl.wellOrdered) (h_lt : deg1 > deg2) :
--     wellOrdered (basis := basis_hd :: basis_tl) (.cons (deg1, coef1) (.cons (deg2, coef2) tl)) := by
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

theorem wellOrdered.cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (h_coef : coef.wellOrdered)
    (h_comp : tl.leadingExp < deg)
    (h_tl : tl.wellOrdered) :
    wellOrdered (basis := basis_hd :: basis_tl) <| .cons (deg, coef) tl := by
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
  · apply CoList.Sorted.cons
    · revert h_comp
      apply tl.casesOn
      · simp
      · simp [leadingExp]
        intro a b h
        rwa [lt_iff_lt]
    · exact h_tl_tl

theorem wellOrdered_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)}
    (h : wellOrdered (basis := basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    coef.wellOrdered ∧ tl.leadingExp < deg ∧ tl.wellOrdered := by
  cases h with | colist _ h_coef h_sorted =>
  replace h_sorted := CoList.Sorted_cons h_sorted
  constructor
  · specialize h_coef 0 (deg, coef)
    simpa using h_coef
  constructor
  · revert h_sorted
    apply tl.casesOn
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


theorem wellOrdered.coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ ms, motive ms →
      (ms = .nil) ∨
      (
        ∃ deg coef, ∃ (tl : PreMS (basis_hd :: basis_tl)), ms = .cons (deg, coef) tl ∧
        coef.wellOrdered ∧
        tl.leadingExp < deg ∧
        motive tl
      )
    ) {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive ms) : ms.wellOrdered := by
  have h_all : ∀ n, motive (CoList.tail^[n] ms) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
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
    simp at hx
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
  · refine CoList.Sorted.coind motive ?_ h
    intro hd tl ih
    specialize h_survive _ ih
    simp at h_survive
    obtain ⟨deg, coef, tl, ⟨h_hd_eq, h_tl_eq⟩, h_coef, h_comp, h_tl⟩ := h_survive
    subst h_hd_eq h_tl_eq
    constructor
    · revert h_comp
      apply tl.casesOn
      · simp
      simp [leadingExp, lt_iff_lt]
    · exact h_tl

def allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) (a : ℝ) :
    Prop :=
  ms.all fun (deg, coef) ↦ deg < a

theorem wellOrdered_allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} {a : ℝ}
    (h_wo : ms.wellOrdered) (h_lt : ms.leadingExp < a) : ms.allLt a := by
  simp only [allLt]
  let motive : PreMS (basis_hd :: basis_tl) → Prop := fun ms =>
    ms.leadingExp < a ∧ ms.wellOrdered
  apply CoList.all.coind motive
  · intro (deg, coef) tl ih
    simp [motive, leadingExp] at ih
    obtain ⟨h_lt, h_wo⟩ := ih
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := wellOrdered_cons h_wo
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

theorem wellOrdered_cons_allLt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} {a : ℝ}
    (h_wo : wellOrdered (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl))
    (h_lt : deg < a) :
    allLt (basis_hd := basis_hd) (CoList.cons (deg, coef) tl) a := by
  apply wellOrdered_allLt h_wo
  simpa [leadingExp]

def majorated (f basis_hd : ℝ → ℝ) (deg : ℝ) : Prop :=
  ∀ deg', deg < deg' → f =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')

theorem majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {deg : ℝ} (h_eq : g =ᶠ[Filter.atTop] f)
    (h : majorated f basis_hd deg) : majorated g basis_hd deg := by
  simp only [majorated] at *
  intro deg' h_deg
  specialize h deg' h_deg
  exact Filter.EventuallyEq.trans_isLittleO h_eq h

-- to upstream?
theorem majorated_self {f : ℝ → ℝ} {deg : ℝ}
    (h : Filter.Tendsto f Filter.atTop Filter.atTop) :
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
    (hg : majorated g basis_hd g_deg) (h_pos : ∀ᶠ x in Filter.atTop, 0 < basis_hd x)
    : majorated (f + g) basis_hd (f_deg ⊔ g_deg) := by
  simp only [majorated] at *
  intro deg h_deg
  simp at h_deg
  apply Asymptotics.IsLittleO.add
  · exact hf _ h_deg.left
  · exact hg _ h_deg.right

theorem mul_majorated {f g basis_hd : ℝ → ℝ} {f_deg g_deg : ℝ} (hf : majorated f basis_hd f_deg)
    (hg : majorated g basis_hd g_deg) (h_pos : ∀ᶠ x in Filter.atTop, 0 < basis_hd x)
    : majorated (f * g) basis_hd (f_deg + g_deg) := by
  simp only [majorated] at *
  intro deg h_deg
  let ε := (deg - f_deg - g_deg) / 2
  specialize hf (f_deg + ε) (by dsimp [ε]; linarith)
  specialize hg (g_deg + ε) (by dsimp [ε]; linarith)
  apply Asymptotics.IsLittleO.trans_eventuallyEq (g₁ := fun x ↦ basis_hd x ^ (f_deg + ε) * basis_hd x ^ (g_deg + ε))
  · exact Asymptotics.IsLittleO.mul hf hg
  · simp only [Filter.EventuallyEq]
    apply Filter.Eventually.mono h_pos
    intro x hx
    conv =>
      rhs
      rw [show deg = (f_deg + ε) + (g_deg + ε) by dsimp [ε]; ring_nf]
      rw [Real.rpow_add hx]

noncomputable def partialSumsFrom (Cs : CoList (ℝ → ℝ)) (degs : CoList ℝ) (basis_fun : ℝ → ℝ)
    (init : ℝ → ℝ) : CoList (ℝ → ℝ) :=
  Cs.zip degs |>.fold init fun acc (C, deg) =>
    fun x ↦ acc x + (basis_fun x)^deg * (C x)

noncomputable def partialSums (Cs : CoList (ℝ → ℝ)) (degs : CoList ℝ) (basis_fun : ℝ → ℝ) :
    CoList (ℝ → ℝ) :=
  partialSumsFrom Cs degs basis_fun 0

theorem partialSumsFrom_nil {degs : CoList ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom .nil degs basis_fun init = .cons init .nil := by
  simp [partialSumsFrom]

theorem partialSumsFrom_cons {Cs_hd : ℝ → ℝ} {Cs_tl : CoList (ℝ → ℝ)} {degs_hd : ℝ}
    {degs_tl : CoList ℝ} {basis_fun : ℝ → ℝ} {init : ℝ → ℝ} :
    partialSumsFrom (.cons Cs_hd Cs_tl) (.cons degs_hd degs_tl) basis_fun init =
    (.cons init <| partialSumsFrom Cs_tl degs_tl basis_fun
      (fun x ↦ init x + (basis_fun x)^degs_hd * (Cs_hd x))) := by
  simp [partialSumsFrom]

theorem partialSumsFrom_eq_map {Cs : CoList (ℝ → ℝ)} {degs : CoList ℝ} {basis_fun : ℝ → ℝ}
    {init : ℝ → ℝ} (h : Cs.atLeastAsLongAs degs) :
    partialSumsFrom Cs degs basis_fun init =
      (partialSums Cs degs basis_fun).map fun G => init + G := by

  let motive : CoList (ℝ → ℝ) → CoList (ℝ → ℝ) → Prop := fun x y =>
    ∃ Cs degs init D,
      Cs.atLeastAsLongAs degs ∧
      (
        (x = partialSumsFrom Cs degs basis_fun (D + init)) ∧
        (y = (partialSumsFrom Cs degs basis_fun init).map fun G => D + G)
      ) ∨
      (x = .nil ∧ y = .nil)
  apply CoList.Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    obtain ⟨Cs', degs', init', D, ih⟩ := ih
    cases' ih with ih ih
    · left
      obtain ⟨h_alal, h_x_eq, h_y_eq⟩ := ih
      revert h_alal h_x_eq h_y_eq
      apply degs'.casesOn
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
        obtain ⟨Cs_hd, Cs_tl, h_Cs⟩ := CoList.atLeastAsLongAs_cons h_alal
        subst h_Cs
        simp [partialSums, partialSumsFrom_cons] at h_x_eq h_y_eq
        use D + init'
        use (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ D x + init' x +
          basis_fun x ^ degs_hd * Cs_hd x)
        use (CoList.map (fun G ↦ D + G) (partialSumsFrom Cs_tl degs_tl basis_fun fun x ↦ init' x +
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
-- inductive isApproximation : (ℝ → ℝ) → (basis : Basis) → PreMS basis → Prop where
-- | const {c : ℝ} {F : ℝ → ℝ} (h : F =ᶠ[Filter.atTop] fun _ ↦ c) : isApproximation F [] c
-- | colist {F basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl))
--   (Cs : CoList (ℝ → ℝ))
--   (h_coef : (Cs.zip ms).all fun (C, (deg, coef)) => isApproximation C basis_tl coef)
--   (h_comp : (partialSums Cs (ms.map fun x => x.1) basis_hd).zip (ms.map fun x => x.1) |>.all
--     fun (ps, deg) => ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[Filter.atTop]
--       (fun x ↦ (basis_hd x)^deg')) :
--   isApproximation F (basis_hd :: basis_tl) ms

def isApproximation (F : ℝ → ℝ) (basis : Basis) (ms : PreMS basis) : Prop :=
  match basis with
  | [] => F =ᶠ[Filter.atTop] fun _ ↦ ms
  | basis_hd :: basis_tl =>
    ∃ Cs : CoList (ℝ → ℝ),
    Cs.atLeastAsLongAs ms ∧
    ((Cs.zip ms).all fun (C, (_, coef)) => isApproximation C basis_tl coef) ∧
    (
      let degs := ms.map fun x => x.1;
      let degs' : CoList (Option ℝ) := (degs.map .some).append (.cons .none .nil);
      (partialSums Cs degs basis_hd).zip degs' |>.all fun (ps, deg?) =>
        match deg? with
        | .some deg =>
          -- ∀ deg', deg < deg' → (fun x ↦ F x - ps x) =o[Filter.atTop]
          --   fun x ↦ (basis_hd x)^deg'
          majorated (fun x ↦ F x - ps x) basis_hd deg
        | .none => (fun x ↦ F x - ps x) =ᶠ[Filter.atTop] 0
    )

theorem isApproximation_nil {F basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : isApproximation F (basis_hd :: basis_tl) CoList.nil) :
    F =ᶠ[Filter.atTop] 0 := by
  unfold isApproximation at h
  obtain ⟨Cs, _, _, h_comp⟩ := h
  simp at h_comp
  unfold CoList.all at h_comp
  specialize h_comp 0
  simpa [partialSums, partialSumsFrom] using h_comp

theorem isApproximation_cons {F basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : isApproximation F (basis_hd :: basis_tl) (.cons (deg, coef) tl)) :
    ∃ C,
      isApproximation C basis_tl coef ∧
      -- (∀ deg', deg < deg' → F =o[Filter.atTop] (fun x ↦ (basis_hd x)^deg')) ∧
      majorated F basis_hd deg ∧
      isApproximation (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl) tl := by
  unfold isApproximation at h
  obtain ⟨Cs, h_alal, h_coef, h_comp⟩ := h
  obtain ⟨C, Cs_tl, h_alal⟩ := CoList.atLeastAsLongAs_cons h_alal
  subst h_alal
  use C
  simp [CoList.all_cons] at h_coef
  constructor
  · exact h_coef.left
  · constructor
    · simp [partialSums, partialSumsFrom] at h_comp
      exact h_comp.left
    · simp at h_alal
      unfold isApproximation
      use Cs_tl
      constructor
      · assumption
      · constructor
        · exact h_coef.right
        · simp [partialSums, partialSumsFrom_cons] at h_comp
          replace h_comp := h_comp.right
          rw [partialSumsFrom_eq_map (CoList.atLeastAsLongAs_map h_alal)] at h_comp
          rw [CoList.map_zip_left] at h_comp
          replace h_comp := CoList.map_all_iff.mp h_comp
          apply CoList.all_mp _ h_comp
          intro (C', deg?)
          simp
          intro h
          ring_nf at h
          ring_nf
          exact h

private structure isApproximation_coind_auxT (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (basis_hd : ℝ → ℝ) (basis_tl : Basis) where
  val : PreMS (basis_hd :: basis_tl)
  F : ℝ → ℝ
  h : motive F basis_hd basis_tl val

theorem isApproximation.coind' (motive : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ basis_hd basis_tl F ms, motive F basis_hd basis_tl ms →
      (ms = .nil ∧ F =ᶠ[Filter.atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (isApproximation C basis_tl coef) ∧
        -- (∀ deg', deg < deg' → F =o[Filter.atTop] fun x ↦ (basis_hd x)^deg') ∧
        majorated F basis_hd deg ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) basis_hd basis_tl tl)
      )
    ) {basis_hd : ℝ → ℝ} {basis_tl : Basis} {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F basis_hd basis_tl ms) : isApproximation F (basis_hd :: basis_tl) ms := by
  simp [isApproximation]
  let T := isApproximation_coind_auxT motive basis_hd basis_tl
  let g : T → CoList.OutType (ℝ → ℝ) T := fun ⟨val, F, h⟩ =>
    (val.casesOn (motive := fun ms => motive F basis_hd basis_tl ms → CoList.OutType (ℝ → ℝ) T)
    (nil := fun _ => .nil)
    (cons := fun (deg, coef) tl =>
      fun h =>
        have spec : ∃ C,
            isApproximation C basis_tl coef ∧
            -- (∀ (deg' : ℝ), deg < deg' → F =o[Filter.atTop] fun x ↦ basis_hd x ^ deg') ∧
            majorated F basis_hd deg ∧
            motive (fun x ↦ F x - basis_hd x ^ deg * C x) basis_hd basis_tl tl := by
          specialize h_survive _ _ _ _ h
          simp at h_survive
          obtain ⟨deg_1, coef_1, tl_1, ⟨⟨h_deg, h_coef⟩, h_tl⟩, h_survive⟩ := h_survive
          subst h_deg
          subst h_coef
          subst h_tl
          exact h_survive
        let C := spec.choose
        .cons C ⟨tl, fun x ↦ F x - (basis_hd x)^deg * (C x), spec.choose_spec.right.right⟩
    )
    ) h
  let Cs : CoList (ℝ → ℝ) := CoList.corec g ⟨ms, F, h⟩
  use Cs
  constructor
  · let motive' : CoList (ℝ → ℝ) → CoList (ℝ × PreMS basis_tl) → Prop := fun Cs ms =>
      ∃ F h, Cs = (CoList.corec g ⟨ms, F, h⟩)
    apply CoList.atLeastAsLong.coind motive'
    · intro Cs ms ih (deg, coef) tl h_ms_eq
      simp only [motive'] at ih
      obtain ⟨F, h, h_Cs_eq⟩ := ih
      subst h_ms_eq
      rw [CoList.corec_cons] at h_Cs_eq
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
    · let motive' : CoList ((ℝ → ℝ) × ℝ × PreMS basis_tl) → Prop := fun li =>
        ∃ (ms : CoList (ℝ × PreMS basis_tl)), ∃ F h,
          li = (CoList.corec g ⟨ms, F, h⟩).zip ms
      apply CoList.all.coind motive'
      · intro (C, (deg, coef)) tl ih
        simp only
        simp only [motive'] at ih
        obtain ⟨ms, F, h, h_eq⟩ := ih
        specialize h_survive _ _ _ _ h
        revert h h_eq h_survive
        apply ms.casesOn
        · intro h h_eq h_survive
          simp at h_eq
        · intro (ms_deg, ms_coef) ms_tl h h_eq h_survive
          rw [CoList.corec_cons] at h_eq
          pick_goal 2
          · simp [g]
            constructor <;> rfl
          simp at h_eq
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
      let motive' : CoList ((ℝ → ℝ) × Option ℝ) → Prop := fun li =>
        li = .nil ∨ ∃ (ms : CoList (ℝ × PreMS basis_tl)), ∃ G h init,
          li = ((partialSumsFrom (CoList.corec g ⟨ms, G, h⟩) (CoList.map (fun x ↦ x.1) ms) basis_hd init).zip
      ((CoList.map some (CoList.map (fun x ↦ x.1) ms)).append (CoList.cons none CoList.nil))) ∧
      G + init =ᶠ[Filter.atTop] F
      apply CoList.all.coind motive'
      · intro (F', deg?) li_tl ih
        simp only [motive'] at ih
        cases ih with
        | inl ih => simp at ih
        | inr ih =>
        obtain ⟨ms, G, h_mot, init, h_eq, hF_eq⟩ := ih
        · simp
          revert h_mot h_eq
          apply ms.casesOn
          · intro h_mot h_eq
            rw [CoList.corec_nil] at h_eq
            swap
            · simp [g]
            simp [partialSumsFrom_nil] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            specialize h_survive _ _ _ _ h_mot
            cases h_survive with
            | inr h_survive => simp at h_survive
            | inl h_survive =>
              simp at h_survive
              constructor
              · apply Filter.eventuallyEq_iff_sub.mp
                trans
                · exact hF_eq.symm
                conv => rhs; ext x; rw [← zero_add (F' x)]
                apply Filter.EventuallyEq.add h_survive
                rfl
              · simp [motive']
          · intro (deg, coef) tl h_mot h_eq
            rw [CoList.corec_cons] at h_eq
            swap
            · simp [g]
              constructor <;> rfl
            simp [partialSumsFrom_cons] at h_eq
            obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
            subst h1 h2 h3
            simp
            constructor
            · intro deg' h_deg
              apply Filter.EventuallyEq.trans_isLittleO (f₂ := G)
              · apply Filter.eventuallyEq_iff_sub.mpr
                replace hF_eq := Filter.eventuallyEq_iff_sub.mp hF_eq.symm
                trans F - (G + F')
                · apply Filter.eventuallyEq_iff_sub.mpr
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
              apply Filter.eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs; ext x; rw [show G x + (F' x - F x) = (G x + F' x) - F x by ring]
              apply Filter.eventuallyEq_iff_sub.mp
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
theorem isApproximation.coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop)
    (h_survive : ∀ F ms, motive F ms →
      (ms = .nil ∧ F =ᶠ[Filter.atTop] 0) ∨
      (
        ∃ deg coef tl C, ms = .cons (deg, coef) tl ∧
        (isApproximation C basis_tl coef) ∧
        -- (∀ deg', deg < deg' → F =o[Filter.atTop] fun x ↦ (basis_hd x)^deg') ∧
        majorated F basis_hd deg ∧
        (motive (fun x ↦ F x - (basis_hd x)^deg * (C x)) tl)
      )
    ) {F : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)}
    (h : motive F ms) : isApproximation F (basis_hd :: basis_tl) ms := by
  let motive' : (F : ℝ → ℝ) → (basis_hd : ℝ → ℝ) →
    (basis_tl : Basis) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
    fun F' basis_hd' basis_tl' ms' =>
      ∃ (h_hd : basis_hd' = basis_hd) (h_tl : basis_tl' = basis_tl), motive F' (h_tl ▸ (h_hd ▸ ms'))
  apply isApproximation.coind' motive'
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
theorem isApproximation.nil {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : F =ᶠ[Filter.atTop] 0) : isApproximation F (basis_hd :: basis_tl) .nil := by
  simp [isApproximation]
  use .nil
  simpa [partialSums, partialSumsFrom]

theorem isApproximation.cons {F : ℝ → ℝ} {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (C : ℝ → ℝ) (h_coef : coef.isApproximation C basis_tl)
    (h_comp : majorated F basis_hd deg)
    (h_tl : tl.isApproximation (fun x ↦ F x - (basis_hd x)^deg * (C x)) (basis_hd :: basis_tl)) :
    isApproximation F (basis_hd :: basis_tl) (.cons (deg, coef) tl) := by
  simp [isApproximation] at h_tl ⊢
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
    · rw [partialSumsFrom_eq_map (CoList.atLeastAsLongAs_map h_tl_alal)] -- copypaste from `isApproximation_cons`
      rw [CoList.map_zip_left]
      apply CoList.map_all_iff.mpr
      apply CoList.all_mp _ h_tl_comp
      intro (C', deg?)
      simp
      intro h
      ring_nf at h
      ring_nf
      exact h

---------

theorem isApproximation_of_EventuallyEq {basis : Basis} {ms : PreMS basis} {F F' : ℝ → ℝ}
     (h_equiv : F =ᶠ[Filter.atTop] F') (h_approx : ms.isApproximation F basis) :
    ms.isApproximation F' basis :=
  match basis with
  | [] => by
    simp [isApproximation] at h_approx
    exact Filter.EventuallyEq.trans h_equiv.symm h_approx
  | basis_hd :: basis_tl => by
    let motive : (F : ℝ → ℝ) → (ms : PreMS (basis_hd :: basis_tl)) → Prop :=
      fun F' ms =>
        ∃ F, F =ᶠ[Filter.atTop] F' ∧ isApproximation F (basis_hd :: basis_tl) ms
    apply isApproximation.coind motive
    · intro F' ms ih
      revert ih
      apply ms.casesOn
      · intro ih
        left
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := isApproximation_nil hF
        constructor
        · rfl
        · exact Filter.EventuallyEq.trans h_equiv.symm hF
      · intro (deg, coef) tl ih
        right
        use deg
        use coef
        use tl
        simp
        simp [motive] at ih
        obtain ⟨F, h_equiv, hF⟩ := ih
        replace hF := isApproximation_cons hF
        obtain ⟨C, h_coef, h_comp, h_tl⟩ := hF
        use C
        constructor
        · exact h_coef
        constructor
        · intro deg' h
          apply Filter.EventuallyEq.trans_isLittleO h_equiv.symm
          apply h_comp _ h
        · simp [motive]
          use fun x ↦ F x - basis_hd x ^ deg * (C x)
          constructor
          · apply Filter.EventuallyEq.sub h_equiv
            apply Filter.EventuallyEq.rfl
          · exact h_tl
    · simp only [motive]
      use F

-- Try to prove later
-- theorem EventuallyEq_of_isApproximation {F F' : ℝ → ℝ} {basis : Basis} {ms : PreMS basis}
--     (h_approx : ms.isApproximation F basis) (h_approx' : ms.isApproximation F' basis) :
--     F =ᶠ[Filter.atTop] F' :=
--   match basis with
--   | [] => by
--     simp [isApproximation] at *
--     trans (fun _ ↦ ms)
--     · exact h_approx
--     · exact h_approx'.symm
--   | basis_hd :: basis_tl => by

--     revert h_approx h_approx'
--     apply ms.casesOn
--     · intro h_approx h_approx'
--       replace h_approx := isApproximation_nil h_approx
--       replace h_approx' := isApproximation_nil h_approx'
--       trans (fun _ ↦ 0)
--       · exact h_approx
--       · exact h_approx'.symm
--     · intro (deg, coef) tl h_approx h_approx'
--       replace h_approx := isApproximation_cons h_approx
--       replace h_approx' := isApproximation_cons h_approx'
--       obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
--       obtain ⟨C', h_coef', h_comp', h_tl'⟩ := h_approx'



--   induction ms using PreMS.rec' generalizing F F' basis with
--   | nil =>
--     cases h_approx with | nil _ _ h =>
--     cases h_approx' with | nil _ _ h' =>
--     trans 0
--     · exact h
--     · exact h'.symm
--   | const c =>
--     cases h_approx with | const _ _ h =>
--     cases h_approx' with | const _ _ h' =>
--     trans (fun _ ↦ c)
--     · exact h
--     · exact h'.symm
--   | cons deg coef tl coef_ih tl_ih =>
--     cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
--     cases h_approx' with | cons _ _ _ _ C' _ _ h_coef' h_tl' h_comp' =>
--     have : (fun x ↦ basis_hd x ^ deg * C x) =ᶠ[Filter.atTop] (fun x ↦ basis_hd x ^ deg * C' x) :=
--       Filter.EventuallyEq.mul (by rfl) (coef_ih h_coef h_coef')
--     have := (tl_ih h_tl h_tl').add this
--     simpa using this

---------

def const (c : ℝ) (basis : Basis) : PreMS basis :=
  match basis with
  | [] => c
  | _ :: basis_tl =>
    .cons (0, const c basis_tl) .nil

def zero (basis) : PreMS basis :=
  match basis with
  | [] => 0
  | _ :: _ => .nil

def one (basis : Basis) : PreMS basis :=
  const 1 basis

end PreMS

structure MS where
  basis : Basis
  val : PreMS basis
  F : ℝ → ℝ
  h_wo : val.wellOrdered
  h_approx : val.isApproximation F basis

end TendstoTactic
