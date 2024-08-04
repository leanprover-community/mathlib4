import Mathlib.Tactic.Tendsto.Multiseries.Basic

namespace TendstoTactic

def PreMS.neg (ms : PreMS) : PreMS :=
  match ms with
  | .const c => .const (-c)
  | .nil => .nil
  | .cons deg coef tl => .cons deg coef.neg (.mk fun _ => tl.get.neg)

theorem PreMS.neg_preserve_depth {n : ℕ} {ms : PreMS} (p : ms.hasDepth n) : ms.neg.hasDepth n := by
  induction ms using PreMS.rec' generalizing n with
  | const _ => simpa [PreMS.neg, PreMS.hasDepth] using p
  | nil => simp [PreMS.neg, PreMS.hasDepth]
  | cons deg coef tl coef_ih tl_ih =>
    simp [PreMS.neg]
    cases n with
    | zero => simp [PreMS.hasDepth] at *
    | succ m =>
      simp [PreMS.hasDepth] at *
      constructor
      · exact coef_ih p.left
      · exact tl_ih p.right

theorem PreMS.neg_preserve_wo {ms : PreMS} (p : ms.wellOrdered) : ms.neg.wellOrdered := by
  induction ms using PreMS.rec' with
  | const _ => simp [PreMS.neg, PreMS.wellOrdered]
  | nil => simp [PreMS.neg, PreMS.wellOrdered]
  | cons deg coef tl coef_ih tl_ih =>
    simp [neg, wellOrdered]
    simp [PreMS.wellOrdered] at p
    generalize tl.get = tlg at *
    cases tlg with
    | cons tl_deg _ tl_tl =>
      simp [neg] at tl_ih ⊢
      tauto
    | _ => simp [neg]

def MS.neg {n : ℕ} (ms : MS n) : MS n :=
  ⟨ms.val.neg, ⟨PreMS.neg_preserve_depth ms.property.left, PreMS.neg_preserve_wo ms.property.right⟩⟩

noncomputable def PreMS.add (f g : PreMS) : PreMS :=
  match f, g with
  | .const a, .const b => .const (a + b)
  | .const _, _ => default
  | _, .const _ => default
  | .nil, g => g
  | f, .nil => f
  | .cons deg_f coef_f tl_f, .cons deg_g coef_g tl_g =>
    if deg_g < deg_f then
      .cons deg_f coef_f <| .mk fun _ => PreMS.add tl_f.get (.cons deg_g coef_g tl_g)
    else if deg_f < deg_g then
      .cons deg_g coef_g <| .mk fun _ => PreMS.add (.cons deg_f coef_f tl_f) tl_g.get
    else
      .cons deg_f (PreMS.add coef_f coef_g) <| .mk fun _ => PreMS.add tl_f.get tl_g.get

theorem PreMS.add_preserve_depth {n : ℕ} {a b : PreMS} (pa : a.hasDepth n) (pb : b.hasDepth n) :
    (PreMS.add a b).hasDepth n := by
  induction a using PreMS.rec' generalizing n b with
  | const _ =>
    cases b with
    | const _ => simpa [PreMS.add, PreMS.hasDepth] using pa
    | nil => simp [PreMS.add, PreMS.hasDepth, default]
    | cons _ _ _ => simp [PreMS.add, PreMS.hasDepth, default]
  | nil =>
    cases b with
    | const _ => simpa [PreMS.add, PreMS.hasDepth]
    | nil => simp [PreMS.add, PreMS.hasDepth, default]
    | cons _ _ _ => simpa [PreMS.add, PreMS.hasDepth, default]
  | cons deg_a coef_a tl_a coef_a_ih tl_a_ih =>
    induction b using PreMS.rec' generalizing n with
    | const _ => simp [PreMS.add, PreMS.hasDepth, default]
    | nil => simpa [PreMS.add, PreMS.hasDepth, default]
    | cons deg_b coef_b tl_b _ tl_b_ih =>
      simp [PreMS.add]
      cases n with
      | zero => simp [PreMS.hasDepth] at *
      | succ m =>
        split_ifs with h1 h2 <;> simp [PreMS.hasDepth] at * <;> constructor -- use h1 h2 later for the second part of WF condition
        · exact pa.left
        · apply tl_a_ih pa.right
          simpa [PreMS.hasDepth]
        · exact pb.left
        · apply tl_b_ih _ pb.right
          simpa [PreMS.hasDepth]
        · exact coef_a_ih pa.left pb.left
        · exact tl_a_ih pa.right pb.right

theorem PreMS.add_preserve_wo {a b : PreMS} (pa : a.wellOrdered) (pb : b.wellOrdered) :
    (PreMS.add a b).wellOrdered := by
  induction a using PreMS.rec' generalizing b with
  | const => cases b <;> simp [add, default, wellOrdered]
  | nil =>
    cases b with
    | cons => simpa [add]
    | _ => simp [add, default, wellOrdered]
  | cons deg_a coef_a tl_a coef_a_ih tl_a_ih =>
    induction b using PreMS.rec' with
    | const _ => simp [add, default, wellOrdered]
    | nil => simpa [add]
    | cons deg_b coef_b tl_b _ tl_b_ih =>
      simp [PreMS.add]
      split_ifs with h1 h2
      · sorry
      · sorry
      · sorry
      -- · unfold wellOrdered
        -- cases tl_a.get with
        -- | cons => simp [add, wellOrdered]
        --   simp [wellOrdered] at pa
        --   simp [wellOrdered, add]
        -- | nil => simpa [wellOrdered, add]
        -- | const => simp [wellOrdered, add]

      --   <;> simp [PreMS.hasDepth] at * <;> constructor -- use h1 h2 later for the second part of WF condition
      -- · exact pa.left
      -- · have tl_a_ih : ∀ {n : ℕ} {b : PreMS}, tl_a.get.hasDepth n → b.hasDepth n → (tl_a.get.add b).hasDepth n := tl_a_ih
      --   apply tl_a_ih pa.right
      --   simpa [PreMS.hasDepth]
      -- · exact pb.left
      -- · have tl_b_ih : ∀ {n : ℕ}, (cons deg_a coef_a tl_a).hasDepth n → tl_b.get.hasDepth n → ((cons deg_a coef_a tl_a).add tl_b.get).hasDepth n := tl_b_ih
      --   apply tl_b_ih _ pb.right
      --   simpa [PreMS.hasDepth]
      -- · exact coef_a_ih pa.left pb.left
      -- · exact tl_a_ih pa.right pb.right

noncomputable def MS.add {n : ℕ} (a b : MS n) : MS n :=
  ⟨PreMS.add a.val b.val,
    ⟨
      PreMS.add_preserve_depth a.property.left b.property.left,
      PreMS.add_preserve_wo a.property.right b.property.right
    ⟩
  ⟩


noncomputable def PreMS.mul (f g : PreMS) : PreMS :=
  match f, g with
  | .const a, .const b => .const (a * b)
  | .nil, _ => .nil
  | _, .nil => .nil
  | .const _, _ => default
  | _, .const _ => default
  | f, .cons deg_g coef_g tl_g =>
    PreMS.add (mulMonomial f coef_g deg_g) <| PreMS.mul f tl_g.get
where mulMonomial (h m_coef : PreMS) (m_deg : ℝ) : PreMS := -- m should be either .const or lazy list of one element
  match h with
  | .const _ => default
  | .nil => .nil
  | .cons deg coef tl =>
    .cons (deg + m_deg) (PreMS.mul coef m_coef) <| mulMonomial tl.get m_coef m_deg

lemma PreMS.mul_preserve_depth_aux_aux1 {n : ℕ} {c : ℝ} (g : PreMS)
    (hf : (PreMS.const c).hasDepth n) (hg : g.hasDepth n) : ((PreMS.const c).mul g).hasDepth n := by
  cases n with
  | succ m => simp [hasDepth] at hf
  | zero => cases g <;> simp_all [mul, hasDepth]

lemma PreMS.mul_preserve_depth_aux_aux2 {n : ℕ} (g : PreMS)
    (hf : PreMS.nil.hasDepth n) (hg : g.hasDepth n) : (PreMS.nil.mul g).hasDepth n := by
  cases n with
  | succ m => simpa [mul]
  | zero => cases g <;> simp_all [mul, hasDepth]

-- lemma PreMS.mul_wf_aux_aux3 {n : ℕ} (h : PreMS) (c m_deg : ℝ)
--     (hh : h.hasDepth (n + 1)) (hm : (PreMS.const c).hasDepth n) : (PreMS.mul.mulMonomial h (PreMS.const c) m_deg).hasDepth (n + 1) := by
--   induction h using PreMS.rec generalizing n with
--   | cons _ coef tl coef_ih tl_ih =>
--     have tl_ih : ∀ {n : ℕ}, tl.get.hasDepth (n + 1) → (const c).hasDepth n → (mul.mulMonomial tl.get (const c) m_deg).hasDepth (n + 1) := tl_ih
--     simp [mul.mulMonomial, mul, hasDepth]
--     constructor
--     · cases coef <;> simp_all [mul, hasDepth]
--     · apply tl_ih
--       · simp [hasDepth] at hh
--         exact hh.right
--       · cases n <;> simp_all [hasDepth]
--   | const _ => simp [hasDepth] at hh
--   | nil => simp [mul.mulMonomial, hasDepth]
--   | mk _ ih => apply ih

-- lemma PreMS.mul_wf_aux_aux4 {n : ℕ} (h : PreMS) (m_deg : ℝ)
--     (hh : h.hasDepth (n + 1)) (hm : PreMS.nil.hasDepth n) : (PreMS.mul.mulMonomial h PreMS.nil m_deg).hasDepth (n + 1) := by
--   induction h using PreMS.rec generalizing n with
--   | cons _ coef tl coef_ih tl_ih =>
--     have tl_ih : ∀ {n : ℕ}, tl.get.hasDepth (n + 1) → nil.hasDepth n → (mul.mulMonomial tl.get nil m_deg).hasDepth (n + 1) := tl_ih
--     simp [mul.mulMonomial, mul, hasDepth]
--     constructor
--     · cases coef <;> simp_all [mul, hasDepth]
--     · apply tl_ih
--       · simp [hasDepth] at hh
--         exact hh.right
--       · simp [hasDepth]
--   | const _ => simp [hasDepth] at hh
--   | nil => simp [mul.mulMonomial, hasDepth]
--   | mk _ ih => apply ih


theorem PreMS.mul_preserve_depth_aux {n : ℕ} (f coef_g : PreMS) (deg_g : ℝ) (tl_g : Thunk PreMS)
    (pf : f.hasDepth n) (pg : (PreMS.cons deg_g coef_g tl_g).hasDepth n) :
    (f.mul (PreMS.cons deg_g coef_g tl_g)).hasDepth n ∧
    (PreMS.mul.mulMonomial f coef_g deg_g).hasDepth n := by
  cases n with
  | zero => simp [hasDepth] at pg
  | succ m =>
    simp [hasDepth] at pg
    induction f using PreMS.rec' generalizing m coef_g deg_g tl_g with
    | cons deg_f coef_f tl_f coef_f_ih tl_f_ih =>
      have aux : (mul.mulMonomial (cons deg_f coef_f tl_f) coef_g deg_g).hasDepth (m + 1) := by
        simp [mul.mulMonomial, hasDepth]
        simp [hasDepth] at pf
        constructor
        · cases coef_g with
          | cons coef_g_deg coef_g_coef coef_g_tl =>
            cases m with
            | zero => simp [hasDepth] at pg
            | succ k =>
              simp [hasDepth] at pg
              exact (coef_f_ih coef_g_coef coef_g_deg coef_g_tl _ pf.left pg.left).left
          | const => cases coef_f <;> simp_all [mul, hasDepth, default]
          | nil => cases coef_f <;> simp_all [mul, hasDepth, default]
        · exact (tl_f_ih coef_g deg_g tl_g _ pf.right pg).right
      constructor
      · simp [mul, hasDepth]
        apply PreMS.add_preserve_depth
        · exact aux
        · generalize tl_g.get = h at *
          induction h using PreMS.rec' with
          | const => simp [hasDepth] at pg
          | cons tl_g_deg tl_g_coef tl_g_tl tl_g_coef_ih tl_g_tl_ih =>
            simp [mul]
            apply PreMS.add_preserve_depth
            · simp [mul.mulMonomial, hasDepth]
              simp [hasDepth] at pf
              constructor
              · cases tl_g_coef with
                | cons coef_g_deg coef_g_coef coef_g_tl =>
                  cases m with
                  | zero => simp [hasDepth] at pg
                  | succ k =>
                    simp [hasDepth] at pg
                    exact (coef_f_ih coef_g_coef coef_g_deg coef_g_tl _ pf.left pg.right.left).left
                | const => cases coef_f <;> simp_all [mul, hasDepth, default]
                | nil => cases coef_f <;> simp_all [mul, hasDepth, default]
              · simp [hasDepth] at pg
                exact (tl_f_ih tl_g_coef tl_g_deg tl_g_tl _ pf.right pg.right).right
            · apply tl_g_tl_ih
              simp [hasDepth] at pg
              exact ⟨pg.left, pg.right.right⟩
          | nil => simp [mul, hasDepth]
      · exact aux
    | const c =>
      constructor
      · apply PreMS.mul_preserve_depth_aux_aux1 _ pf
        simpa [hasDepth]
      · simp [mul.mulMonomial, default, hasDepth]
    | nil =>
      constructor
      · apply PreMS.mul_preserve_depth_aux_aux2 _ pf
        simpa [hasDepth]
      · simp [mul.mulMonomial, default, hasDepth]

theorem PreMS.mul_preserve_depth {n : ℕ} {f g : PreMS} (pf : f.hasDepth n) (pg : g.hasDepth n) :
    (f.mul g).hasDepth n :=
  match g with
  | cons g_deg g_coef g_tl => (PreMS.mul_preserve_depth_aux f g_coef g_deg g_tl pf pg).left
  | const _ => by cases f <;> simp_all [mul, hasDepth, default]
  | nil => by cases f <;> simp [mul, hasDepth, default]

lemma PreMS.mul_preserve_wo_aux_aux1 {c : ℝ} {g : PreMS} (hg : g.wellOrdered) :
    ((PreMS.const c).mul g).wellOrdered := by
  cases g <;> simp [mul, wellOrdered]

lemma PreMS.mul_preserve_wo_aux_aux2 {g : PreMS}
    (hg : g.wellOrdered) : (PreMS.nil.mul g).wellOrdered := by
  cases g <;> simp [mul, wellOrdered]


theorem PreMS.mul_preserve_wo_aux (f coef_g : PreMS) (deg_g : ℝ) (tl_g : Thunk PreMS)
    (pf : f.wellOrdered) (pg : (PreMS.cons deg_g coef_g tl_g).wellOrdered) :
    (f.mul (PreMS.cons deg_g coef_g tl_g)).wellOrdered ∧
    (PreMS.mul.mulMonomial f coef_g deg_g).wellOrdered := by
  sorry

theorem PreMS.mul_preserve_wo {f g : PreMS} (pf : f.wellOrdered) (pg : g.wellOrdered) :
    (f.mul g).wellOrdered :=
  match g with
  | cons g_deg g_coef g_tl => (PreMS.mul_preserve_wo_aux f g_coef g_deg g_tl pf pg).left
  | const _ => by cases f <;> simp_all [mul, wellOrdered, default]
  | nil => by cases f <;> simp [mul, wellOrdered, default]

noncomputable def MS.mul {n : ℕ} (a b : MS n) : MS n :=
  ⟨PreMS.mul a.val b.val, ⟨
    PreMS.mul_preserve_depth a.property.left b.property.left,
    PreMS.mul_preserve_wo a.property.right b.property.right
  ⟩⟩

/-
(x + 1) * y^2 + (x^2 + 3) * y
  *
(x + 2) * y + (x - 2) * y^0
  =
mulMonomial
  (x + 1) * y^2 + (x^2 + 3) * y
  (x + 2) 1
+ (x + 1) * y^2 + (x^2 + 3) * y
  * (x - 2) * y^0
  =
  .cons y^3 ((x + 1) * (x + 2)) <|


+ (x + 1) * y^2 + (x^2 + 3) * y
  * (x - 2) * y^0


-/

end TendstoTactic
