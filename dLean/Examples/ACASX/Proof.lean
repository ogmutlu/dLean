import dLean.Examples.ACASX.Model
import dLean.Tactic.OdeDeriv

open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace ACASX

/-- Twice the signed nominal height relative to the target-speed line.
The time argument has been rescaled by `alo`; `gap` is the signed velocity shortfall. -/
noncomputable def lowerRelative (gap t : ℝ) : ℝ :=
  if t < max 0 gap then t ^ 2 - 2 * gap * t else -(max 0 gap) ^ 2

/-- The nominal comparison underlying the archive's "Safe lower bound" lemma.
`u = alo*T`, `z = w*a*T`, and `q = alo*tn`. The two compliance assumptions
are the evolution domain at the start and end of the actual flight segment. -/
theorem lowerRelative_comp (gap u z q : ℝ) (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hstart : gap ≤ 0 ∨ u ≤ z) (hfinish : gap - z ≤ 0 ∨ u ≤ z) :
    lowerRelative gap (u + q) ≤ z * u - 2 * gap * u + lowerRelative (gap - z) q := by
  by_cases hfast : u ≤ z
  · by_cases hg : gap ≤ 0
    · simp only [lowerRelative, max_eq_left hg,
        max_eq_left (show gap - z ≤ 0 by linarith),
        ite_eq_right (not_lt_of_ge (add_nonneg hu hq)), ite_eq_right (not_lt_of_ge hq)]
      nlinarith [mul_nonneg hu (show 0 ≤ z - 2 * gap by linarith)]
    · by_cases hgz : gap - z ≤ 0
      · simp only [lowerRelative, max_eq_right (le_of_not_ge hg), max_eq_left hgz]
        split_ifs with hold
        all_goals nlinarith [mul_nonneg (sub_nonneg.mpr hfast) hu, sq_nonneg (gap - u)]
      · simp only [lowerRelative, max_eq_right (le_of_not_ge hg),
          max_eq_right (le_of_not_ge hgz)]
        split_ifs with hold hnew
        all_goals
          nlinarith [mul_nonneg (sub_nonneg.mpr hfast) hu,
            mul_nonneg (sub_nonneg.mpr hfast) hq,
            mul_nonneg (sub_nonneg.mpr hfast) (show 0 ≤ 2 * gap - z by linarith)]
  · simp only [lowerRelative, max_eq_left (hstart.resolve_right hfast),
      max_eq_left (hfinish.resolve_right hfast),
      ite_eq_right (not_lt_of_ge (add_nonneg hu hq)), ite_eq_right (not_lt_of_ge hq)]
    nlinarith [mul_nonneg hu (show 0 ≤ z - 2 * gap by
      have := hstart.resolve_right hfast
      have := hfinish.resolve_right hfast
      linarith)]

theorem A_time_nonneg (alo t hn v w vlo : ℝ) (ha : 0 < alo)
    (hA : A alo t hn v w vlo) : 0 ≤ t := by
  rcases hA with ⟨ht, _, _⟩ | ⟨ht, _⟩
  · exact ht
  · exact (div_nonneg (le_max_left 0 _) ha.le).trans ht

theorem A_exists (alo t v w vlo : ℝ) (ht : 0 ≤ t) : ∃ hn, A alo t hn v w vlo := by
  by_cases h : t < maxI v w vlo / alo
  · exact ⟨w * alo / 2 * t ^ 2 + v * t, Or.inl ⟨ht, h, rfl⟩⟩
  · exact ⟨vlo * t - w * maxI v w vlo ^ 2 / (2 * alo), Or.inr ⟨le_of_not_gt h, rfl⟩⟩

theorem A_scaled (alo t hn v w vlo : ℝ) (ha : 0 < alo) (hw : Sense w)
    (hA : A alo t hn v w vlo) :
    2 * alo * (w * hn) = 2 * (w * vlo) * (alo * t) +
      lowerRelative (w * (vlo - v)) (alo * t) := by
  rcases hA with ⟨ht, hs, rfl⟩ | ⟨hs, rfl⟩
  · rw [lowerRelative, ite_eq_left (show alo * t < max 0 (w * (vlo - v)) by
      simpa [maxI, mul_comm] using (lt_div_iff₀ ha).mp hs)]
    rcases hw with rfl | rfl <;> ring
  · rw [lowerRelative, ite_eq_right (show ¬alo * t < max 0 (w * (vlo - v)) by
      have := (div_le_iff₀ ha).mp hs
      simpa [maxI, mul_comm] using not_lt_of_ge this)]
    rcases hw with rfl | rfl <;> simp only [maxI] <;> field_simp <;> ring

/-- At time `T + tn`, the original nominal height is below the actual displacement
at `T` plus the new nominal height. This is the archive's shifted-time argument. -/
theorem nominal_dominates (alo T tn oldHeight newHeight v w vlo a : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hT : 0 ≤ T) (htn : 0 ≤ tn)
    (hstart : advisoryLo alo v w vlo a) (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hold : A alo (T + tn) oldHeight v w vlo)
    (hnew : A alo tn newHeight (v + a * T) w vlo) :
    w * oldHeight ≤ w * (a / 2 * T ^ 2 + v * T + newHeight) := by
  have hcomp := lowerRelative_comp (w * (vlo - v)) (alo * T) (w * a * T) (alo * tn)
    (mul_nonneg ha.le hT) (mul_nonneg ha.le htn)
    (by rcases hstart with h | h
        · left; nlinarith
        · right; exact mul_le_mul_of_nonneg_right h hT)
    (by rcases hfinish with h | h
        · left; nlinarith
        · right; exact mul_le_mul_of_nonneg_right h hT)
  rw [show alo * T + alo * tn = alo * (T + tn) by ring,
    show w * (vlo - v) - w * a * T = w * (vlo - (v + a * T)) by ring] at hcomp
  nlinarith [A_scaled alo (T + tn) oldHeight v w vlo ha hw hold,
    A_scaled alo tn newHeight (v + a * T) w vlo ha hw hnew]

theorem lower_kinematic_preserved (rp hp rv alo r h v w vlo a T : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hT : 0 ≤ T)
    (hstart : advisoryLo alo v w vlo a) (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hsafe : Limpl rp hp rv alo r h v w vlo) :
    Limpl rp hp rv alo (r - rv * T) (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vlo := by
  intro tn rn hn ⟨hrn, hA⟩
  obtain ⟨oldHeight, hold⟩ := A_exists alo (T + tn) v w vlo
    (add_nonneg hT (A_time_nonneg alo tn hn (v + a * T) w vlo ha hA))
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [nominal_dominates alo T tn oldHeight hn v w vlo a ha hw hT
      (A_time_nonneg alo tn hn (v + a * T) w vlo ha hA) hstart hfinish hold hA]

/-- Scalar uniqueness on a closed interval, including zero-duration intervals. -/
theorem trajectory_eq (T : ℝ) (f g df : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (df t) (Set.Icc 0 T) t)
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt g (df t) (Set.Icc 0 T) t)
    (h0 : f 0 = g 0) : Set.EqOn f g (Set.Icc 0 T) := by
  intro t ht
  have heq := SemanticODE.preservedByDerivative_eq t ht.1 (fun τ => f τ - g τ) (fun _ => 0)
    (fun τ hτ => by
      have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
      convert! ((hf τ (hsub hτ)).mono hsub).sub ((hg τ (hsub hτ)).mono hsub) using 1; simp)
    (fun _ _ => rfl)
  linarith

/-- Exact polynomial solution of the archive ODE with fixed acceleration. -/
theorem motion_solution (rv a r h v T : ℝ) (D : ℝ × ℝ × ℝ → Prop)
    (path : ℝ → ℝ × ℝ × ℝ)
    (hevo : IsEvolution path (Evolvable.denotation (motion rv a)) D (r, h, v) T) :
    ∀ t ∈ Set.Icc 0 T,
      path t = (r - rv * t, h - (a / 2 * t ^ 2 + v * t), v + a * t) := by
  have hv : Set.EqOn (fun t => (path t).2.2) (fun t => v + a * t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => a)
    · exact fun t ht => (hevo.2.2 t ht).snd.snd
    · intro t _
      convert! ((hasDerivAt_const t v).add ((hasDerivAt_id t).const_mul a)).hasDerivWithinAt
        using 1; ring
    · simp [hevo.1]
  have hr : Set.EqOn (fun t => (path t).1) (fun t => r - rv * t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => -rv)
    · exact fun t ht => (hevo.2.2 t ht).fst
    · intro t _
      convert! ((hasDerivAt_const t r).sub ((hasDerivAt_id t).const_mul rv)).hasDerivWithinAt
        using 1; ring
    · simp [hevo.1]
  have hh : Set.EqOn (fun t => (path t).2.1)
      (fun t => h - (a / 2 * t ^ 2 + v * t)) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun t => -(v + a * t))
    · intro t ht
      have hv_t : (path t).2.2 = v + a * t := hv ht
      rw [← hv_t]
      exact (hevo.2.2 t ht).snd.fst
    · intro t _
      convert! ((hasDerivAt_const t h).sub
        ((((hasDerivAt_id t).pow 2).const_mul (a / 2)).add
          ((hasDerivAt_id t).const_mul v))).hasDerivWithinAt using 1; simp; ring
    · simp [hevo.1]
  exact fun t ht => Prod.ext (hr ht) (Prod.ext (hh ht) (hv ht))

def lowerStep (_rp _hp rv alo w vlo a r h v : ℝ) :=
  evolve (motion rv a) (lowerDomain alo w vlo a) (r, h, v)

@[spec] theorem lowerStep_spec (rp hp rv alo w vlo a r h v : ℝ) :
    ⦃0 < alo ∧ Sense w ∧ Limpl rp hp rv alo r h v w vlo⦄
    lowerStep rp hp rv alo w vlo a r h v
    ⦃fun (r, h, v) => Limpl rp hp rv alo r h v w vlo⦄ := by
  constructor
  intro ⟨ha, hw, hsafe⟩
  unfold lowerStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (motion rv a)) (lowerDomain alo w vlo a)
    (r, h, v) (Q := fun (r, h, v) => Limpl rp hp rv alo r h v w vlo)).le_wp
  intro T hT path hevo
  rw [motion_solution rv a r h v T _ path hevo T ⟨hT, le_rfl⟩]
  apply lower_kinematic_preserved rp hp rv alo r h v w vlo a T ha hw hT
  · simpa only [hevo.1, lowerDomain] using hevo.2.1 0 ⟨le_rfl, hT⟩
  · have hdom := hevo.2.1 T ⟨hT, le_rfl⟩
    rw [motion_solution rv a r h v T _ path hevo T ⟨hT, le_rfl⟩] at hdom
    exact hdom
  · exact hsafe

@[spec] theorem sense_spec : ⦃True⦄ sense ⦃Sense⦄ := by
  constructor
  intro _
  rw [SetM.wp_iff_run]
  simp [sense, chooseS, SetM.run, Sense]

@[spec] theorem choice_spec {α : Type} (p q : SetM α) (Q : α → Prop) :
    ⦃wp p Q estack⟨⟩ ∧ wp q Q estack⟨⟩⦄ p <|> q ⦃Q⦄ := by
  constructor
  intro h
  exact SetM.wp_orElse p q h.1 h.2

/-- Proof-only annotation of the original immediate-response loop.
The erased program is definitionally equal to `immediate`; see `immediate_eq`. -/
def immediate' (rp hp rv alo r h v w vlo : ℝ) : SetM (ℝ × ℝ × ℝ × ℝ × ℝ)
    requires 0 < alo ∧ Sense w ∧ Limpl rp hp rv alo r h v w vlo
    ensures (r, h, v, w, vlo) => Sense w ∧ Limpl rp hp rv alo r h v w vlo
    := do
  let mut (r, h, v, w, vlo) := (r, h, v, w, vlo)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ Sense w ∧ Limpl rp hp rv alo r h v w vlo do
    let bool ← choose Bool
    if bool then
      w ← sense
      vlo ← choose ℝ
      ensure (Limpl rp hp rv alo r h v w vlo)
    let a ← choose ℝ
    (r, h, v) ← lowerStep rp hp rv alo w vlo a r h v
  return (r, h, v, w, vlo)

theorem A_zero (alo v w vlo : ℝ) (ha : 0 < alo) : A alo 0 0 v w vlo := by
  by_cases hm : maxI v w vlo = 0
  · right
    simp [hm]
  · left
    exact ⟨le_rfl, div_pos (lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hm)) ha, by ring⟩

theorem lower_implies_noNMAC (rp hp rv alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hsafe : Limpl rp hp rv alo r h v w vlo) :
    NoNMAC rp hp r h := by
  rcases hsafe 0 0 0 ⟨by ring, A_zero alo v w vlo ha⟩ with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

theorem immediate_eq (rp hp rv alo r h v w vlo : ℝ) :
    immediate rp hp rv alo r h v w vlo = immediate' rp hp rv alo r h v w vlo := rfl

/-- STTT Theorem 1; preserve the stronger region postcondition of `acasx.kyx`. -/
theorem immediate_safe :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → Sense w → Limpl rp hp rv alo r h v w vlo →
        ∀ res ∈ SetM.run (immediate rp hp rv alo r h v w vlo),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2
          NoNMAC rp hp r_res h_res ∧ Limpl rp hp rv alo r_res h_res v_res w_res vlo_res := by
  intro rp hp rv alo r h v w vlo hb hw hsafe res hrun
  rw [immediate_eq] at hrun
  have hinv := (immediate'.spec rp hp rv alo r h v w vlo).le_wp
    ⟨hb.2.2.2, hw, hsafe⟩ res hrun
  exact ⟨lower_implies_noNMAC rp hp rv alo _ _ _ _ _ hb.2.2.2 hinv.1 hinv.2, hinv.2⟩

/-- Twice the signed nominal height in time coordinates scaled by `alo`.
The velocity arguments are already signed by `w`. -/
noncomputable def nominal (v target t : ℝ) : ℝ :=
  if t < max 0 (target - v) then t ^ 2 + 2 * v * t
  else 2 * target * t - max 0 (target - v) ^ 2

theorem nominal_antitone (v target s t : ℝ) (hF : target < 0)
    (hs : 0 ≤ s) (hst : s ≤ t) : nominal v target t ≤ nominal v target s := by
  by_cases hgap : 0 ≤ target - v
  · simp only [nominal, max_eq_right hgap]
    split_ifs with ht hs'
    · nlinarith [mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ -2 * v - s - t by linarith)]
    · linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF.le
        (show 0 ≤ t - (target - v) by linarith), sq_nonneg (s - (target - v))]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF.le (sub_nonneg.mpr hst)]
  · simp only [nominal, max_eq_left (le_of_not_ge hgap),
      ite_eq_right (not_lt_of_ge (hs.trans hst)), ite_eq_right (not_lt_of_ge hs)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hF.le (sub_nonneg.mpr hst)]

theorem nominal_of_le (v target t : ℝ) (ht : t ≤ max 0 (target - v)) :
    nominal v target t = t ^ 2 + 2 * v * t := by
  unfold nominal
  split_ifs with h
  · rfl
  · have heq : t = max 0 (target - v) := le_antisymm ht (le_of_not_gt h)
    rw [heq]
    rcases le_total 0 (target - v) with hg | hg
    · rw [max_eq_right hg]
      ring
    · rw [max_eq_left hg]
      ring

theorem vertex_le_switch (v target : ℝ) (hF : 0 ≤ target) :
    -(min 0 v) ≤ max 0 (target - v) := by
  rcases le_total 0 v with hv | hv
  · rw [min_eq_left hv]
    simp
  · rw [min_eq_right hv]
    exact (show -v ≤ target - v by linarith).trans (le_max_right 0 _)

theorem nominal_at_vertex (v target : ℝ) (hF : 0 ≤ target) :
    nominal v target (-(min 0 v)) = -(min 0 v) ^ 2 := by
  rw [nominal_of_le v target _ (vertex_le_switch v target hF)]
  rcases le_total 0 v with hv | hv
  · rw [min_eq_left hv]
    ring
  · rw [min_eq_right hv]
    ring

theorem nominal_global_min (v target t : ℝ) (hF : 0 ≤ target) (ht : 0 ≤ t) :
    -(min 0 v) ^ 2 ≤ nominal v target t := by
  by_cases hv : 0 ≤ v
  · rw [min_eq_left hv]
    by_cases hg : 0 ≤ target - v
    · simp only [nominal, max_eq_right hg]
      split_ifs with h
      · nlinarith [mul_nonneg hv ht, sq_nonneg t]
      · nlinarith [mul_nonneg hF (show 0 ≤ t - (target - v) by linarith),
          mul_nonneg hg (add_nonneg hF hv)]
    · simp only [nominal, max_eq_left (le_of_not_ge hg), ite_eq_right (not_lt_of_ge ht)]
      nlinarith [mul_nonneg hF ht]
  · rw [min_eq_right (le_of_not_ge hv)]
    simp only [nominal, max_eq_right (show 0 ≤ target - v by linarith)]
    split_ifs with h
    · nlinarith [sq_nonneg (t + v)]
    · nlinarith [mul_nonneg hF (show 0 ≤ t - (target - v) by linarith), sq_nonneg target]

theorem nominal_right_min (v target l t : ℝ) (hF : 0 ≤ target)
    (hl : 0 ≤ l) (hvertex : -(min 0 v) ≤ l)
    (hlswitch : l ≤ max 0 (target - v)) (hlt : l ≤ t) :
    nominal v target l ≤ nominal v target t := by
  have hslope : 0 ≤ v + l := by
    rcases le_total 0 v with hv | hv
    · linarith
    · rw [min_eq_right hv] at hvertex
      linarith
  have hjoin := nominal_of_le v target (max 0 (target - v)) le_rfl
  simp only [nominal, lt_self_iff_false, ite_false] at hjoin
  rw [nominal_of_le v target l hlswitch]
  unfold nominal
  split_ifs with h
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlt)
      (show 0 ≤ t + l + 2 * v by linarith)]
  · nlinarith [mul_nonneg hF (show 0 ≤ t - max 0 (target - v) by linarith),
      mul_nonneg (sub_nonneg.mpr hlswitch)
        (show 0 ≤ max 0 (target - v) + l + 2 * v by linarith)]

theorem nominal_left_min (v target t u : ℝ) (hF : 0 ≤ target)
    (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ -(min 0 v)) :
    nominal v target u ≤ nominal v target t := by
  have hswitch := vertex_le_switch v target hF
  rw [nominal_of_le v target u (hu.trans hswitch),
    nominal_of_le v target t (htu.trans (hu.trans hswitch))]
  rcases le_total 0 v with hv | hv
  · rw [min_eq_left hv] at hu
    have hzero : t = 0 ∧ u = 0 := by constructor <;> linarith
    simp [hzero.1, hzero.2]
  · rw [min_eq_right hv] at hu
    nlinarith [mul_nonneg (sub_nonneg.mpr htu)
      (show 0 ≤ -2 * v - t - u by linarith)]

theorem nominal_linear_min (v target l t : ℝ) (hF : 0 ≤ target)
    (hl : max 0 (target - v) ≤ l) (hlt : l ≤ t) :
    nominal v target l ≤ nominal v target t := by
  simp only [nominal, ite_eq_right (not_lt_of_ge hl),
    ite_eq_right (not_lt_of_ge (hl.trans hlt))]
  nlinarith [mul_nonneg hF (sub_nonneg.mpr hlt)]

/-- The six archive cases, in acceleration-scaled time coordinates. -/
def explicitWindow (v target l u height : ℝ) : Prop :=
  let c := -(min 0 v)
  let M := max 0 (target - v)
  (0 ≤ target →
    ((0 ≤ u ∧ u < c) → height < u ^ 2 + 2 * v * u) ∧
    ((c ≤ u ∧ l ≤ c) → height < -(min 0 v) ^ 2) ∧
    ((c < l ∧ l ≤ M) → height < l ^ 2 + 2 * v * l) ∧
    (M < l → height < 2 * target * l - M ^ 2)) ∧
  (target < 0 →
    ((0 ≤ u ∧ u < M) → height < u ^ 2 + 2 * v * u) ∧
    (M ≤ u → height < 2 * target * u - M ^ 2))

/-- Archive Lemma 1: cases 1/5 use the right horizontal boundary, case 2 the
parabola vertex, and cases 3/4 the left boundary. Case 6 uses the final line.
The backward direction evaluates the implicit condition at those same points. -/
theorem window_equivalent (v target l u height : ℝ) (hlu : l ≤ u) :
    explicitWindow v target l u height ↔
      ∀ t, 0 ≤ t → l ≤ t → t ≤ u → height < nominal v target t := by
  constructor
  · intro hex t ht hlt htu
    rcases le_or_gt 0 target with hF | hF
    · obtain ⟨h1, h2, h3, h4⟩ := hex.1 hF
      by_cases hu : u < -(min 0 v)
      · have hval := h1 ⟨ht.trans htu, hu⟩
        rw [← nominal_of_le v target u
          (hu.le.trans (vertex_le_switch v target hF))] at hval
        exact hval.trans_le (nominal_left_min v target t u hF ht htu hu.le)
      · by_cases hl : l ≤ -(min 0 v)
        · exact (h2 ⟨le_of_not_gt hu, hl⟩).trans_le (nominal_global_min v target t hF ht)
        · by_cases hM : l ≤ max 0 (target - v)
          · have hval := h3 ⟨lt_of_not_ge hl, hM⟩
            rw [← nominal_of_le v target l hM] at hval
            exact hval.trans_le (nominal_right_min v target l t hF
              ((neg_nonneg.mpr (min_le_left 0 v)).trans (le_of_not_ge hl))
              (le_of_not_ge hl) hM hlt)
          · have hval := h4 (lt_of_not_ge hM)
            have heq : nominal v target l =
                2 * target * l - max 0 (target - v) ^ 2 := by
              simp [nominal, not_lt_of_ge (le_of_not_ge hM)]
            rw [← heq] at hval
            exact hval.trans_le (nominal_linear_min v target l t hF
              (le_of_not_ge hM) hlt)
    · obtain ⟨h5, h6⟩ := hex.2 hF
      have hval : height < nominal v target u := by
        by_cases hu : u < max 0 (target - v)
        · simpa [nominal, hu] using h5 ⟨ht.trans htu, hu⟩
        · simpa [nominal, hu] using h6 (le_of_not_gt hu)
      exact hval.trans_le (nominal_antitone v target t u hF ht htu)
  · intro himp
    constructor
    · intro hF
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hu
        have hx := himp u hu.1 hlu le_rfl
        rwa [nominal_of_le v target u
          (hu.2.le.trans (vertex_le_switch v target hF))] at hx
      · intro hc
        have hx := himp (-(min 0 v)) (neg_nonneg.mpr (min_le_left 0 v)) hc.2 hc.1
        rwa [nominal_at_vertex v target hF] at hx
      · intro hl
        have hx := himp l
          ((neg_nonneg.mpr (min_le_left 0 v)).trans hl.1.le) le_rfl hlu
        rwa [nominal_of_le v target l hl.2] at hx
      · intro hl
        have hx := himp l ((le_max_left 0 _).trans hl.le) le_rfl hlu
        simpa [nominal, not_lt_of_ge hl.le] using hx
    · intro hF
      constructor
      · intro hu
        simpa [nominal, hu.2] using himp u hu.1 hlu le_rfl
      · intro hu
        simpa [nominal, not_lt_of_ge hu] using
          himp u ((le_max_left 0 _).trans hu) hlu le_rfl

theorem A_nominal (alo t hn v w vlo : ℝ) (ha : 0 < alo) (hw : Sense w)
    (hA : A alo t hn v w vlo) :
    2 * alo * (w * hn) = nominal (w * v) (w * vlo) (alo * t) := by
  have hs := A_scaled alo t hn v w vlo ha hw hA
  rw [show w * (vlo - v) = w * vlo - w * v by ring] at hs
  rw [hs]
  unfold nominal lowerRelative
  split_ifs <;> ring

/-- For positive closing speed the collision puck gives a closed time interval.
Only the time coordinate and the height inequality are rescaled. -/
theorem implicit_window (rp hp rv alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hrv : 0 < rv) :
    Limpl rp hp rv alo r h v w vlo ↔
      ∀ t, 0 ≤ t → alo * (r - rp) / rv ≤ t → t ≤ alo * (r + rp) / rv →
        2 * alo * (w * h + hp) < nominal (w * v) (w * vlo) t := by
  have ha0 := ne_of_gt ha
  constructor
  · intro hsafe t ht hl hu
    obtain ⟨hn, hA⟩ := A_exists alo (t / alo) v w vlo (div_nonneg ht ha.le)
    have hs := A_nominal alo (t / alo) hn v w vlo ha hw hA
    rw [mul_div_cancel₀ _ ha0] at hs
    have hinside : |r - rv * (t / alo)| ≤ rp := by
      rw [abs_le]
      have hl' := (div_le_iff₀ hrv).mp hl
      have hu' := (le_div_iff₀ hrv).mp hu
      have heq : alo * (rv * (t / alo)) = rv * t := by field_simp
      constructor <;> nlinarith
    have hsep := (hsafe (t / alo) (rv * (t / alo)) hn ⟨rfl, hA⟩).resolve_left
      (not_lt_of_ge hinside)
    nlinarith
  · intro hsafe t rn hn ⟨hrn, hA⟩
    rw [hrn]
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      have hs := hsafe (alo * t) (mul_nonneg ha.le (A_time_nonneg _ _ _ _ _ _ ha hA))
        (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
      have hn := A_nominal alo t hn v w vlo ha hw hA
      nlinarith
    · exact Or.inl (lt_of_not_ge hinside)

theorem positive_scale_lt (k x y X Y : ℝ) (hk : 0 < k)
    (heq : k * (y - x) = Y - X) : (x < y ↔ X < Y) := by
  calc
    (x < y) ↔ 0 < y - x := sub_pos.symm
    _ ↔ 0 < k * (y - x) := (mul_pos_iff_of_pos_left hk).symm
    _ ↔ X < Y := by rw [heq, sub_pos]

/-- Algebraic translation of all six archive conditions. Every multiplier
used to clear a denominator is positive; strict case boundaries are preserved. -/
theorem explicit_window (rp hp rv alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hrv : 0 < rv) :
    Lexpl rp hp rv alo r h v w vlo ↔
      explicitWindow (w * v) (w * vlo) (alo * (r - rp) / rv)
        (alo * (r + rp) / rv) (2 * alo * (w * h + hp)) := by
  let k := rv / alo
  have hk : 0 < k := div_pos hrv ha
  have ha0 := ne_of_gt ha
  have hr0 := ne_of_gt hrv
  have htime (z : ℝ) : alo * z / rv = z / k := by dsimp [k]; field_simp
  have hshift (z : ℝ) : rv * z / alo = k * z := by dsimp [k]; ring
  have hquad (z : ℝ) :
      (2 * alo * (w * h + hp) < (z / k) ^ 2 + 2 * (w * v) * (z / k)) ↔
      w * rv ^ 2 * h < alo / 2 * z ^ 2 + w * rv * v * z - rv ^ 2 * hp := by
    apply positive_scale_lt (rv ^ 2 / (2 * alo)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hline (z : ℝ) :
      (2 * alo * (w * h + hp) <
        2 * (w * vlo) * (z / k) - maxI v w vlo ^ 2) ↔
      w * rv * h < w * vlo * z - rv * maxI v w vlo ^ 2 / (2 * alo) - rv * hp := by
    apply positive_scale_lt (rv / (2 * alo)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hvertex :
      (2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) ↔
      w * h < -(min 0 (w * v)) ^ 2 / (2 * alo) - hp := by
    apply positive_scale_lt (1 / (2 * alo)) _ _ _ _ (by positivity)
    field_simp
    ring
  have hM : max 0 (w * vlo - w * v) = maxI v w vlo := by
    unfold maxI
    congr 1
    ring
  have h0 : (0 ≤ (r + rp) / k) ↔ -rp ≤ r := by
    rw [le_div_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have hu (z : ℝ) : ((r + rp) / k ≤ z) ↔ r ≤ -rp + k * z := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hul (z : ℝ) : ((r + rp) / k < z) ↔ r < -rp + k * z := by
    rw [div_lt_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hl (z : ℝ) : ((r - rp) / k ≤ z) ↔ r ≤ rp + k * z := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hll (z : ℝ) : ((r - rp) / k < z) ↔ r < rp + k * z := by
    rw [div_lt_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hur (z : ℝ) : (z ≤ (r + rp) / k) ↔ -rp + k * z ≤ r := by
    rw [← not_lt, hul, not_lt]
  have hlr (z : ℝ) : (z < (r - rp) / k) ↔ rp + k * z < r := by
    rw [← not_le, hl, not_le]
  unfold Lexpl explicitWindow
  dsimp only
  rw [htime, htime, hM]
  simp only [hquad, hline, hvertex, h0, hul, hl,
    hur, hlr, hshift, hr0, false_or, false_and, mul_neg, ← sub_eq_add_neg]

/-- With no horizontal exit, a negative target eventually violates every
finite altitude bound. A nonnegative target attains its minimum at the vertex. -/
theorem nominal_all_time (v target height : ℝ) :
    (∀ t, 0 ≤ t → height < nominal v target t) ↔
      0 ≤ target ∧ height < -(min 0 v) ^ 2 := by
  constructor
  · intro hs
    have hF : 0 ≤ target := by
      by_contra hneg
      have hneg : target < 0 := lt_of_not_ge hneg
      let t := max (max 0 (target - v)) (height / (2 * target))
      have ht : 0 ≤ t := (le_max_left 0 _).trans (le_max_left _ _)
      have hM : max 0 (target - v) ≤ t := le_max_left _ _
      have hval := hs t ht
      simp only [nominal, ite_eq_right (not_lt_of_ge hM)] at hval
      have hbound := (div_le_iff_of_neg (show 2 * target < 0 by linarith)).mp
        (le_max_right (max 0 (target - v)) (height / (2 * target)))
      nlinarith [sq_nonneg (max 0 (target - v))]
    have hval := hs (-(min 0 v)) (neg_nonneg.mpr (min_le_left 0 v))
    rw [nominal_at_vertex v target hF] at hval
    exact ⟨hF, hval⟩
  · rintro ⟨hF, hmin⟩ t ht
    exact hmin.trans_le (nominal_global_min v target t hF ht)

theorem implicit_stationary (rp hp alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) :
    Limpl rp hp 0 alo r h v w vlo ↔
      rp < |r| ∨ (0 ≤ w * vlo ∧ 2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) := by
  by_cases hsep : rp < |r|
  · simp only [hsep, true_or, iff_true]
    intro t rn hn ⟨hrn, _⟩
    left
    simpa [hrn] using hsep
  · have hinside : |r| ≤ rp := le_of_not_gt hsep
    rw [or_iff_right hsep, ← nominal_all_time]
    constructor
    · intro hsafe t ht
      obtain ⟨hn, hA⟩ := A_exists alo (t / alo) v w vlo (div_nonneg ht ha.le)
      have hs := A_nominal alo (t / alo) hn v w vlo ha hw hA
      rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hs
      have hval := (hsafe (t / alo) 0 hn ⟨by ring, hA⟩).resolve_left (by simpa using hsep)
      nlinarith
    · intro hs t rn hn ⟨hrn, hA⟩
      right
      have hval := hs (alo * t) (mul_nonneg ha.le (A_time_nonneg _ _ _ _ _ _ ha hA))
      have hn := A_nominal alo t hn v w vlo ha hw hA
      nlinarith

/-- Preserve the archive's explicit `rv = 0` disjuncts rather than dividing
by the closing speed in the degenerate case. -/
theorem explicit_stationary (rp hp alo r h v w vlo : ℝ) (ha : 0 < alo) :
    Lexpl rp hp 0 alo r h v w vlo ↔
      rp < |r| ∨ (0 ≤ w * vlo ∧ 2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) := by
  have hm : (w * h < -(min 0 (w * v)) ^ 2 / (2 * alo) - hp) ↔
      2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity : 0 < 2 * alo)]
    constructor <;> intro hx <;> nlinarith
  simp only [Lexpl, zero_mul, mul_zero, zero_div, sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    true_or, true_and]
  rw [hm]
  have himpossible₁ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  have himpossible₂ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [himpossible₁, himpossible₂, false_implies, true_and]
  by_cases hleft : r < -rp
  · have hsep : rp < |r| := (neg_le_abs r).trans_lt' (by linarith)
    simp [not_le.mpr hleft, hsep]
  · by_cases hright : rp < r
    · have hsep : rp < |r| := hright.trans_le (le_abs_self r)
      simp [hright, not_le.mpr hright, hsep]
    · have hinside : |r| ≤ rp := abs_le.mpr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      by_cases hF : 0 ≤ w * vlo
      · simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, not_lt_of_ge hF]
      · have hneg : ¬0 < w * vlo * (r + rp) := not_lt_of_ge
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hF) (by linarith))
        simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, lt_of_not_ge hF, hneg]

/-- STTT Lemma 1 / repository `acasx.kyx`. -/
theorem immediate_regions_equivalent :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → Sense w →
        (Lexpl rp hp rv alo r h v w vlo ↔ Limpl rp hp rv alo r h v w vlo) := by
  intro rp hp rv alo r h v w vlo hb hw
  by_cases hr : rv = 0
  · subst rv
    exact (explicit_stationary rp hp alo r h v w vlo hb.2.2.2).trans
      (implicit_stationary rp hp alo r h v w vlo hb.2.2.2 hw).symm
  · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
    rw [explicit_window rp hp rv alo r h v w vlo hb.2.2.2 hr,
      implicit_window rp hp rv alo r h v w vlo hb.2.2.2 hw hr]
    exact window_equivalent _ _ _ _ _ (by
      apply div_le_div_of_nonneg_right _ hr.le
      exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) hb.2.2.2.le)

/-- Signed height gained over the initial velocity line by the capped upper
trajectory. Its final slope uses `max (w*vup) (w*v)` as in the newer archive. -/
noncomputable def upperGain (gap t : ℝ) : ℝ :=
  if t < max 0 gap then t ^ 2 else 2 * max 0 gap * t - (max 0 gap) ^ 2

/-- The archive's upper-bound comparison at shifted time `T + tn`.
The hypotheses are upper compliance at the two endpoints of the actual phase. -/
theorem upperGain_comp (gap u z q : ℝ) (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hstart : z ≤ 0 ∨ (0 ≤ gap ∧ z ≤ u))
    (hfinish : z ≤ 0 ∨ (0 ≤ gap - z ∧ z ≤ u)) :
    z * u + 2 * z * q + upperGain (gap - z) q ≤ upperGain gap (u + q) := by
  have hzu : z ≤ u := hstart.elim (fun hz => hz.trans hu) And.right
  by_cases hg : 0 ≤ gap
  · have hgz : 0 ≤ gap - z := hfinish.elim (fun hz => by linarith) And.left
    simp only [upperGain, max_eq_right hg, max_eq_right hgz]
    split_ifs with hnew hold
    · nlinarith [mul_nonneg (sub_nonneg.mpr hzu) (show 0 ≤ u + 2 * q by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ gap + q by linarith)
        (show 0 ≤ gap - q - z by linarith),
        mul_nonneg (show 0 ≤ 2 * gap - z by linarith)
          (show 0 ≤ u + q - gap by linarith)]
    · linarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr hzu) (show 0 ≤ 2 * gap - z by linarith)]
  · have hz : z ≤ 0 := hstart.elim id (fun h => False.elim (hg h.1))
    by_cases hgz : 0 ≤ gap - z
    · simp only [upperGain, max_eq_left (le_of_not_ge hg), max_eq_right hgz,
        ite_eq_right (not_lt_of_ge (add_nonneg hu hq))]
      split_ifs with hnew
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hu,
          mul_nonpos_of_nonpos_of_nonneg (show 2 * z + q ≤ 0 by linarith) hq]
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hu,
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hg) hq, sq_nonneg (gap - z)]
    · simp only [upperGain, max_eq_left (le_of_not_ge hg),
        max_eq_left (le_of_not_ge hgz), ite_eq_right (not_lt_of_ge (add_nonneg hu hq)),
        ite_eq_right (not_lt_of_ge hq)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hu,
        mul_nonpos_of_nonpos_of_nonneg hz hq]

theorem Aup_time_nonneg (aup t hn v w vup : ℝ) (ha : 0 < aup)
    (hA : Aup aup t hn v w vup) : 0 ≤ t := by
  rcases hA with ⟨ht, _, _⟩ | ⟨ht, _⟩
  · exact ht
  · exact (div_nonneg (le_max_left 0 _) ha.le).trans ht

theorem Aup_exists (aup t v w vup : ℝ) (ht : 0 ≤ t) :
    ∃ hn, Aup aup t hn v w vup := by
  by_cases h : t < maxI v w vup / aup
  · exact ⟨w * aup / 2 * t ^ 2 + v * t, Or.inl ⟨ht, h, rfl⟩⟩
  · exact ⟨w * max (w * vup) (w * v) * t - w * maxI v w vup ^ 2 / (2 * aup),
      Or.inr ⟨le_of_not_gt h, rfl⟩⟩

theorem Aup_scaled (aup t hn v w vup : ℝ) (ha : 0 < aup) (hw : Sense w)
    (hA : Aup aup t hn v w vup) :
    2 * aup * (w * hn) = 2 * (w * v) * (aup * t) +
      upperGain (w * (vup - v)) (aup * t) := by
  have hmax : max (w * vup) (w * v) = w * v + max 0 (w * (vup - v)) := by
    rw [mul_sub]
    rcases le_total (w * v) (w * vup) with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rcases hA with ⟨ht, hs, rfl⟩ | ⟨hs, rfl⟩
  · rw [upperGain, ite_eq_left (show aup * t < max 0 (w * (vup - v)) by
      simpa [maxI, mul_comm] using (lt_div_iff₀ ha).mp hs)]
    rcases hw with rfl | rfl <;> ring
  · rw [upperGain, ite_eq_right (show ¬aup * t < max 0 (w * (vup - v)) by
      have := (div_le_iff₀ ha).mp hs
      simpa [maxI, mul_comm] using not_lt_of_ge this), hmax]
    rcases hw with rfl | rfl <;> simp only [maxI] <;> field_simp <;> ring

theorem upper_nominal_dominates (aup T tn oldHeight newHeight v w vup a : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hT : 0 ≤ T) (htn : 0 ≤ tn)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hold : Aup aup (T + tn) oldHeight v w vup)
    (hnew : Aup aup tn newHeight (v + a * T) w vup) :
    w * (a / 2 * T ^ 2 + v * T + newHeight) ≤ w * oldHeight := by
  have hcomp := upperGain_comp (w * (vup - v)) (aup * T) (w * a * T) (aup * tn)
    (mul_nonneg ha.le hT) (mul_nonneg ha.le htn)
    (by rcases hstart with ⟨hv, ha⟩ | ha
        · right
          exact ⟨by nlinarith, mul_le_mul_of_nonneg_right ha hT⟩
        · left
          exact mul_nonpos_of_nonpos_of_nonneg ha hT)
    (by rcases hfinish with ⟨hv, ha⟩ | ha
        · right
          exact ⟨by nlinarith, mul_le_mul_of_nonneg_right ha hT⟩
        · left
          exact mul_nonpos_of_nonpos_of_nonneg ha hT)
  rw [show aup * T + aup * tn = aup * (T + tn) by ring,
    show w * (vup - v) - w * a * T = w * (vup - (v + a * T)) by ring] at hcomp
  nlinarith [Aup_scaled aup (T + tn) oldHeight v w vup ha hw hold,
    Aup_scaled aup tn newHeight (v + a * T) w vup ha hw hnew]

theorem upper_kinematic_preserved (rp hp rv aup r h v w vup a T : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hT : 0 ≤ T)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hsafe : Uimpl rp hp rv aup r h v w vup) :
    Uimpl rp hp rv aup (r - rv * T) (h - (a / 2 * T ^ 2 + v * T))
      (v + a * T) w vup := by
  intro tn rn hn ⟨hrn, hA⟩
  obtain ⟨oldHeight, hold⟩ := Aup_exists aup (T + tn) v w vup
    (add_nonneg hT (Aup_time_nonneg aup tn hn (v + a * T) w vup ha hA))
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [upper_nominal_dominates aup T tn oldHeight hn v w vup a ha hw hT
      (Aup_time_nonneg aup tn hn (v + a * T) w vup ha hA) hstart hfinish hold hA]

def twoSidedStep (_rp _hp rv alo aup w vlo vup a r h v : ℝ) :=
  evolve (motion rv a) (twoSidedDomain alo aup w vlo vup a) (r, h, v)

@[spec] theorem twoSidedStep_spec (rp hp rv alo aup w vlo vup a r h v : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ Sense w ∧ Cimpl rp hp rv alo aup r h v w vlo vup⦄
    twoSidedStep rp hp rv alo aup w vlo vup a r h v
    ⦃fun (r, h, v) => Cimpl rp hp rv alo aup r h v w vlo vup⦄ := by
  constructor
  intro ⟨ha, haup, hw, hsafe⟩
  unfold twoSidedStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (motion rv a))
    (twoSidedDomain alo aup w vlo vup a) (r, h, v)
    (Q := fun (r, h, v) => Cimpl rp hp rv alo aup r h v w vlo vup)).le_wp
  intro T hT path hevo
  have hstart := hevo.2.1 0 ⟨le_rfl, hT⟩
  rw [hevo.1] at hstart
  have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
  rw [motion_solution rv a r h v T _ path hevo T ⟨hT, le_rfl⟩] at hfinish ⊢
  rcases hsafe with hsafe | hsafe
  · exact Or.inl (lower_kinematic_preserved rp hp rv alo r h v w vlo a T ha hw hT
      hstart.1 hfinish.1 hsafe)
  · exact Or.inr (upper_kinematic_preserved rp hp rv aup r h v w vup a T haup hw hT
      hstart.2 hfinish.2 hsafe)

/-- The newer archive reissues both targets. This annotated loop erases to the
original program by `rfl`, including the retain-advisory alternative. -/
def twoSided' (rp hp rv alo aup r h v w vlo vup : ℝ) : SetM (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
    requires 0 < alo ∧ 0 < aup ∧ Sense w ∧ Cimpl rp hp rv alo aup r h v w vlo vup
    ensures (r, h, v, w, vlo, vup) => Sense w ∧ Cimpl rp hp rv alo aup r h v w vlo vup
    := do
  let mut (r, h, v, w, vlo, vup) := (r, h, v, w, vlo, vup)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ Sense w ∧
        Cimpl rp hp rv alo aup r h v w vlo vup do
    let bool ← choose Bool
    if bool then
      w ← sense
      vlo ← choose ℝ
      vup ← choose ℝ
      ensure (Cimpl rp hp rv alo aup r h v w vlo vup)
    let a ← choose ℝ
    (r, h, v) ← twoSidedStep rp hp rv alo aup w vlo vup a r h v
  return (r, h, v, w, vlo, vup)

theorem Aup_zero (aup v w vup : ℝ) (ha : 0 < aup) : Aup aup 0 0 v w vup := by
  by_cases hm : maxI v w vup = 0
  · right
    simp [hm]
  · left
    exact ⟨le_rfl, div_pos (lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hm)) ha, by ring⟩

theorem upper_implies_noNMAC (rp hp rv aup r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hsafe : Uimpl rp hp rv aup r h v w vup) :
    NoNMAC rp hp r h := by
  rcases hsafe 0 0 0 ⟨by ring, Aup_zero aup v w vup ha⟩ with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

theorem twoSided_eq (rp hp rv alo aup r h v w vlo vup : ℝ) :
    twoSided rp hp rv alo aup r h v w vlo vup =
      twoSided' rp hp rv alo aup r h v w vlo vup := rfl

/-- STTT Theorem 3 as supplied in repository `acasxtwosided.kyx`.
Both targets can change; `alo ≤ aup` is required. The archive postcondition is NoNMAC. -/
theorem two_sided_safe :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
      Cimpl rp hp rv alo aup r h v w vlo vup →
        ∀ res ∈ SetM.run (twoSided rp hp rv alo aup r h v w vlo vup),
          let r_res := res.1
          let h_res := res.2.1
          NoNMAC rp hp r_res h_res := by
  intro rp hp rv alo aup r h v w vlo vup hb haup hw hsafe res hrun
  have ha := hb.2.2.2.trans_le haup
  rw [twoSided_eq] at hrun
  have hinv := (twoSided'.spec rp hp rv alo aup r h v w vlo vup).le_wp
    ⟨hb.2.2.2, ha, hw, hsafe⟩ res hrun
  rcases hinv.2 with hlo | hup
  · exact lower_implies_noNMAC rp hp rv alo _ _ _ _ _ hb.2.2.2 hinv.1 hlo
  · exact upper_implies_noNMAC rp hp rv aup _ _ _ _ _ ha hinv.1 hup

/-- Project the physical coordinates to the already solved three-coordinate ODE;
the persistent issue clock evolves at unit rate. -/
theorem clocked_solution (rv a r h v clock T : ℝ) (D : ℝ × ℝ × ℝ × ℝ → Prop)
    (path : ℝ → ℝ × ℝ × ℝ × ℝ)
    (hevo : IsEvolution path (Evolvable.denotation (clockedMotion rv a)) D (r, h, v, clock) T) :
    ∀ t ∈ Set.Icc 0 T,
      path t = (r - rv * t, h - (a / 2 * t ^ 2 + v * t), v + a * t, clock + t) := by
  let project := fun s : ℝ × ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2.1)
  have hmotion : IsEvolution (fun t => project (path t))
      (Evolvable.denotation (motion rv a)) (fun _ => True) (r, h, v) T := by
    refine ⟨?_, fun _ _ => trivial, ?_⟩
    · simp [project, hevo.1]
    · intro t ht
      convert! (hevo.2.2 t ht).fst.prodMk
        ((hevo.2.2 t ht).snd.fst.prodMk (hevo.2.2 t ht).snd.snd.fst) using 1
  have hclock : Set.EqOn (fun t => (path t).2.2.2) (fun t => clock + t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => 1)
    · exact fun t ht => (hevo.2.2 t ht).snd.snd.snd
    · intro t _
      convert! ((hasDerivAt_const t clock).add (hasDerivAt_id t)).hasDerivWithinAt using 1
      simp
    · simp [hevo.1]
  intro t ht
  have hm := motion_solution rv a r h v T _ _ hmotion t ht
  have hc := hclock ht
  dsimp only [project] at hm
  have hr : (path t).1 = r - rv * t := congrArg (fun s => s.1) hm
  have hh : (path t).2.1 = h - (a / 2 * t ^ 2 + v * t) :=
    congrArg (fun s => s.2.1) hm
  have hv : (path t).2.2.1 = v + a * t := congrArg (fun s => s.2.2) hm
  exact Prod.ext hr (Prod.ext hh (Prod.ext hv hc))

/-- The same shifted-time lower comparison, restricted to the remaining horizon.
No initial clock lower bound or `alo ≤ aup` assumption is needed. -/
theorem lower_bounded_preserved (rp hp rv alo tl clock r h v w vlo a T : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hT : 0 ≤ T)
    (hstart : advisoryLo alo v w vlo a) (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hsafe : LimplBounded rp hp rv alo tl clock r h v w vlo) :
    LimplBounded rp hp rv alo tl (clock + T) (r - rv * T)
      (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vlo := by
  intro tn rn hn ⟨horizon, hrn, hA⟩
  have htn := A_time_nonneg alo tn hn (v + a * T) w vlo ha hA
  obtain ⟨oldHeight, hold⟩ := A_exists alo (T + tn) v w vlo (add_nonneg hT htn)
  have hor : T + tn ≤ tl - clock ∨ tl < 0 := horizon.imp (by intro hx; linarith) id
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨hor, rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [nominal_dominates alo T tn oldHeight hn v w vlo a ha hw hT
      htn hstart hfinish hold hA]

theorem upper_bounded_preserved (rp hp rv aup tl clock r h v w vup a T : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hT : 0 ≤ T)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hsafe : UimplBounded rp hp rv aup tl clock r h v w vup) :
    UimplBounded rp hp rv aup tl (clock + T) (r - rv * T)
      (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vup := by
  intro tn rn hn ⟨horizon, hrn, hA⟩
  have htn := Aup_time_nonneg aup tn hn (v + a * T) w vup ha hA
  obtain ⟨oldHeight, hold⟩ := Aup_exists aup (T + tn) v w vup (add_nonneg hT htn)
  have hor : T + tn ≤ tl - clock ∨ tl < 0 := horizon.imp (by intro hx; linarith) id
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨hor, rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [upper_nominal_dominates aup T tn oldHeight hn v w vup a ha hw hT
      htn hstart hfinish hold hA]

def boundedStep (_rp _hp rv alo aup tl w vlo vup a r h v clock : ℝ) :=
  evolve (clockedMotion rv a) (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)

@[spec] theorem boundedStep_spec (rp hp rv alo aup tl w vlo vup a r h v clock : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ Sense w ∧ CimplBounded rp hp rv alo aup tl clock r h v w vlo vup⦄
    boundedStep rp hp rv alo aup tl w vlo vup a r h v clock
    ⦃fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplBounded rp hp rv alo aup tl clock r h v w vlo vup⦄ := by
  constructor
  intro ⟨ha, haup, hw, hsafe⟩
  unfold boundedStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (clockedMotion rv a))
    (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)
    (Q := fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplBounded rp hp rv alo aup tl clock r h v w vlo vup)).le_wp
  intro T hT path hevo
  have hstart := hevo.2.1 0 ⟨le_rfl, hT⟩
  rw [hevo.1] at hstart
  have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
  rw [clocked_solution rv a r h v clock T _ path hevo T ⟨hT, le_rfl⟩] at hfinish ⊢
  refine ⟨hfinish.1, ?_⟩
  rcases hsafe with hsafe | hsafe
  · exact Or.inl (lower_bounded_preserved rp hp rv alo tl clock r h v w vlo a T
      ha hw hT hstart.2.1 hfinish.2.1 hsafe)
  · exact Or.inr (upper_bounded_preserved rp hp rv aup tl clock r h v w vup a T
      haup hw hT hstart.2.2 hfinish.2.2 hsafe)

theorem lower_bounded_noNMAC (rp hp rv alo tl clock r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : LimplBounded rp hp rv alo tl clock r h v w vlo) : NoNMAC rp hp r h := by
  have hval := hsafe 0 0 0 ⟨ht.imp (by intro hx; linarith) id, by ring, A_zero alo v w vlo ha⟩
  rcases hval with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

theorem upper_bounded_noNMAC (rp hp rv aup tl clock r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : UimplBounded rp hp rv aup tl clock r h v w vup) : NoNMAC rp hp r h := by
  have hval := hsafe 0 0 0 ⟨ht.imp (by intro hx; linarith) id, by ring, Aup_zero aup v w vup ha⟩
  rcases hval with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

theorem lowerRelative_antitone_gap (g₀ g₁ t : ℝ) (ht : 0 ≤ t) (hg : g₁ ≤ g₀) :
    lowerRelative g₀ t ≤ lowerRelative g₁ t := by
  by_cases hg₀ : g₀ ≤ 0
  · simp [lowerRelative, max_eq_left hg₀, max_eq_left (hg.trans hg₀), not_lt_of_ge ht]
  · by_cases hg₁ : g₁ ≤ 0
    · simp only [lowerRelative, max_eq_right (le_of_not_ge hg₀), max_eq_left hg₁,
        ite_eq_right (not_lt_of_ge ht)]
      split_ifs with h
      · nlinarith [mul_nonneg ht (show 0 ≤ 2 * g₀ - t by linarith)]
      · nlinarith [sq_nonneg g₀]
    · simp only [lowerRelative, max_eq_right (le_of_not_ge hg₀),
        max_eq_right (le_of_not_ge hg₁)]
      split_ifs with h₀ h₁
      · nlinarith [mul_nonneg (sub_nonneg.mpr hg) ht]
      · nlinarith [mul_nonneg (show 0 ≤ t - g₁ by linarith)
          (show 0 ≤ t + g₁ by linarith),
          mul_nonneg ht (show 0 ≤ g₀ - t by linarith)]
      · linarith
      · nlinarith [mul_nonneg (sub_nonneg.mpr hg) (show 0 ≤ g₀ + g₁ by linarith)]

/-- The supplement's escape propagation: lowering signed relative altitude and
increasing signed initial velocity preserves a lower escape region. -/
theorem lower_region_mono (rp hp rv alo r h₀ h₁ v₀ v₁ w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hh : w * h₁ ≤ w * h₀) (hv : w * v₀ ≤ w * v₁)
    (hsafe : Limpl rp hp rv alo r h₀ v₀ w vlo) :
    Limpl rp hp rv alo r h₁ v₁ w vlo := by
  intro t rn hn ⟨hrn, hA⟩
  have ht := A_time_nonneg alo t hn v₁ w vlo ha hA
  obtain ⟨oldHeight, hold⟩ := A_exists alo t v₀ w vlo ht
  rcases hsafe t rn oldHeight ⟨hrn, hold⟩ with hsep | hsep
  · exact Or.inl hsep
  · right
    have hc := lowerRelative_antitone_gap (w * (vlo - v₀)) (w * (vlo - v₁))
      (alo * t) (mul_nonneg ha.le ht) (by nlinarith)
    nlinarith [A_scaled alo t oldHeight v₀ w vlo ha hw hold,
      A_scaled alo t hn v₁ w vlo ha hw hA]

theorem lowerEndpoint_A (alo τ hn vn v w vlo : ℝ)
    (he : lowerEndpoint alo τ hn vn v w vlo) : A alo τ hn v w vlo := by
  rcases he with ⟨ht, hs, hh, _⟩ | ⟨hs, hh, _⟩
  · exact Or.inl ⟨ht, hs, hh⟩
  · exact Or.inr ⟨hs, hh⟩

theorem lowerEndpoint_velocity (alo τ hn vn v w vlo : ℝ) (ha : 0 < alo)
    (hw : Sense w) (ht : 0 ≤ τ) (he : lowerEndpoint alo τ hn vn v w vlo) :
    w * vn = min (w * vlo) (w * v + alo * τ) := by
  have hw2 : w * w = 1 := by rcases hw with rfl | rfl <;> norm_num
  rcases he with ⟨_, hs, _, hv⟩ | ⟨hs, _, hv⟩
  · have hbound := (lt_div_iff₀ ha).mp hs
    by_cases hg : 0 ≤ w * (vlo - v)
    · rw [maxI, max_eq_right hg] at hbound
      rw [min_eq_right (by nlinarith)]
      rw [hv]
      nlinarith [hw2]
    · rw [maxI, max_eq_left (le_of_not_ge hg)] at hbound
      nlinarith
  · have hbound := (div_le_iff₀ ha).mp hs
    have hM : w * (vlo - v) ≤ maxI v w vlo := le_max_right _ _
    rw [min_eq_left (by nlinarith), hv]

theorem lowerEndpoint_velocity_compare (alo T q oldH oldV newH newV v w vlo a : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hold : lowerEndpoint alo (T + q) oldH oldV v w vlo)
    (hnew : lowerEndpoint alo q newH newV (v + a * T) w vlo) : w * oldV ≤ w * newV := by
  rw [lowerEndpoint_velocity alo (T + q) oldH oldV v w vlo ha hw (add_nonneg hT hq) hold,
    lowerEndpoint_velocity alo q newH newV (v + a * T) w vlo ha hw hq hnew]
  rcases hfinish with hf | hf
  · rw [min_eq_left (by nlinarith : w * vlo ≤ w * (v + a * T) + alo * q)]
    exact min_le_left _ _
  · apply min_le_min_left
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) hT]

theorem upper_speed (v w vup : ℝ) (hw : Sense w) :
    v + w * maxI v w vup = w * max (w * vup) (w * v) := by
  have hm : max (w * vup) (w * v) = w * v + maxI v w vup := by
    unfold maxI
    rw [mul_sub]
    rcases le_total (w * v) (w * vup) with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rw [hm]
  rcases hw with rfl | rfl <;> ring

theorem upperEndpoint_Aup (aup τ hn vn v w vup : ℝ) (_hw : Sense w)
    (he : upperEndpoint aup τ hn vn v w vup) : Aup aup τ hn v w vup := by
  rcases he with ⟨ht, hs, hh, _⟩ | ⟨hs, hh, _⟩
  · exact Or.inl ⟨ht, hs, hh⟩
  · exact Or.inr ⟨hs, hh⟩

theorem upperEndpoint_velocity (aup τ hn vn v w vup : ℝ) (ha : 0 < aup)
    (hw : Sense w) (_ht : 0 ≤ τ) (he : upperEndpoint aup τ hn vn v w vup) :
    w * vn = min (w * v + aup * τ) (max (w * vup) (w * v)) := by
  have hw2 : w * w = 1 := by rcases hw with rfl | rfl <;> norm_num
  have hm : max (w * vup) (w * v) = w * v + maxI v w vup := by
    have heq := congrArg (fun x => w * x) (upper_speed v w vup hw)
    simpa only [mul_add, ← mul_assoc, hw2, one_mul] using heq.symm
  rw [hm]
  rcases he with ⟨_, hs, _, hv⟩ | ⟨hs, _, hv⟩
  · have hbound := (lt_div_iff₀ ha).mp hs
    rw [min_eq_left (by linarith), hv]
    rcases hw with rfl | rfl <;> ring
  · have hbound := (div_le_iff₀ ha).mp hs
    rw [min_eq_right (by linarith), hv, hm]
    rcases hw with rfl | rfl <;> ring

theorem upperEndpoint_velocity_compare (aup T q oldH oldV newH newV v w vup a : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hold : upperEndpoint aup (T + q) oldH oldV v w vup)
    (hnew : upperEndpoint aup q newH newV (v + a * T) w vup) : w * newV ≤ w * oldV := by
  rw [upperEndpoint_velocity aup (T + q) oldH oldV v w vup ha hw (add_nonneg hT hq) hold,
    upperEndpoint_velocity aup q newH newV (v + a * T) w vup ha hw hq hnew]
  by_cases hz : w * a ≤ 0
  · apply min_le_min
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hT]
    · apply max_le_max_left
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hT]
  · obtain ⟨hv₀, ha₀⟩ := hstart.resolve_right hz
    obtain ⟨hv₁, _⟩ := hfinish.resolve_right hz
    rw [max_eq_left hv₀, max_eq_left hv₁]
    apply min_le_min_right
    nlinarith [mul_nonneg (sub_nonneg.mpr ha₀) hT]

theorem lowerEndpoint_exists (alo τ v w vlo : ℝ) (ht : 0 ≤ τ) :
    ∃ hn vn, lowerEndpoint alo τ hn vn v w vlo := by
  by_cases hs : τ < maxI v w vlo / alo
  · exact ⟨_, _, Or.inl ⟨ht, hs, rfl, rfl⟩⟩
  · exact ⟨_, _, Or.inr ⟨le_of_not_gt hs, rfl, rfl⟩⟩

theorem upperEndpoint_exists (aup τ v w vup : ℝ) (ht : 0 ≤ τ) :
    ∃ hn vn, upperEndpoint aup τ hn vn v w vup := by
  by_cases hs : τ < maxI v w vup / aup
  · exact ⟨_, _, Or.inl ⟨ht, hs, rfl, rfl⟩⟩
  · exact ⟨_, _, Or.inr ⟨le_of_not_gt hs, rfl, rfl⟩⟩

/-- Preserve the escape condition at the fixed advisory horizon using the
nominal endpoint height and velocity comparisons, separately for each sense. -/
theorem safeable_kinematic_preserved
    (rp hp rv alo aup tl clock vloEx vupEx r h v w vlo vup a T : ℝ)
    (ha : 0 < alo) (haup : 0 < aup) (hw : Sense w) (hT : 0 ≤ T)
    (horizon : clock + T ≤ tl)
    (hstart : advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a)
    (hfinish : advisoryLo alo (v + a * T) w vlo a ∧ advisoryUp aup (v + a * T) w vup a)
    (hsafe : CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx) :
    CimplSafeable rp hp rv alo aup tl (clock + T) (r - rv * T)
      (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vlo vloEx vup vupEx := by
  have hq : 0 ≤ tl - (clock + T) := sub_nonneg.mpr horizon
  have hs : 0 ≤ tl - clock := by linarith
  have htime : T + (tl - (clock + T)) = tl - clock := by ring
  rcases hsafe with ⟨hbounded, hescape⟩ | ⟨hbounded, hescape⟩
  · left
    refine ⟨lower_bounded_preserved rp hp rv alo tl clock r h v w vlo a T
      ha hw hT hstart.1 hfinish.1 hbounded, ?_⟩
    intro newH newV hnew
    obtain ⟨oldH, oldV, hold⟩ := lowerEndpoint_exists alo (tl - clock) v w vlo hs
    have hold' : lowerEndpoint alo (T + (tl - (clock + T))) oldH oldV v w vlo := by
      rwa [htime]
    have hh := nominal_dominates alo T (tl - (clock + T)) oldH newH v w vlo a
      ha hw hT hq hstart.1 hfinish.1 (lowerEndpoint_A _ _ _ _ _ _ _ hold')
      (lowerEndpoint_A _ _ _ _ _ _ _ hnew)
    have hv := lowerEndpoint_velocity_compare alo T (tl - (clock + T))
      oldH oldV newH newV v w vlo a ha hw hT hq hfinish.1 hold' hnew
    rw [show r - rv * T - rv * (tl - (clock + T)) = r - rv * (tl - clock) by ring]
    exact lower_region_mono rp hp rv alo _ (h - oldH)
      (h - (a / 2 * T ^ 2 + v * T) - newH) oldV newV w vloEx ha hw
      (by nlinarith) hv (hescape oldH oldV hold)
  · right
    refine ⟨upper_bounded_preserved rp hp rv aup tl clock r h v w vup a T
      haup hw hT hstart.2 hfinish.2 hbounded, ?_⟩
    intro newH newV hnew
    obtain ⟨oldH, oldV, hold⟩ := upperEndpoint_exists aup (tl - clock) v w vup hs
    have hold' : upperEndpoint aup (T + (tl - (clock + T))) oldH oldV v w vup := by
      rwa [htime]
    have hh := upper_nominal_dominates aup T (tl - (clock + T)) oldH newH v w vup a
      haup hw hT hq hstart.2 hfinish.2 (upperEndpoint_Aup _ _ _ _ _ _ _ hw hold')
      (upperEndpoint_Aup _ _ _ _ _ _ _ hw hnew)
    have hv := upperEndpoint_velocity_compare aup T (tl - (clock + T))
      oldH oldV newH newV v w vup a haup hw hT hq hstart.2 hfinish.2 hold' hnew
    have hwneg : Sense (-w) := by rcases hw with rfl | rfl <;> norm_num [Sense]
    rw [show r - rv * T - rv * (tl - (clock + T)) = r - rv * (tl - clock) by ring]
    exact lower_region_mono rp hp rv alo _ (h - oldH)
      (h - (a / 2 * T ^ 2 + v * T) - newH) oldV newV (-w) vupEx ha hwneg
      (by nlinarith) (by nlinarith) (hescape oldH oldV hold)

def safeableStep (_rp _hp rv alo aup tl _vloEx _vupEx w vlo vup a r h v clock : ℝ) :=
  evolve (clockedMotion rv a) (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)

@[spec] theorem safeableStep_spec
    (rp hp rv alo aup tl vloEx vupEx w vlo vup a r h v clock : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ 0 ≤ tl ∧ Sense w ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx⦄
    safeableStep rp hp rv alo aup tl vloEx vupEx w vlo vup a r h v clock
    ⦃fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx⦄ := by
  constructor
  intro ⟨ha, haup, htl, hw, hsafe⟩
  unfold safeableStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (clockedMotion rv a))
    (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)
    (Q := fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx)).le_wp
  intro T hT path hevo
  have hstart := hevo.2.1 0 ⟨le_rfl, hT⟩
  rw [hevo.1] at hstart
  have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
  rw [clocked_solution rv a r h v clock T _ path hevo T ⟨hT, le_rfl⟩] at hfinish ⊢
  exact ⟨hfinish.1, safeable_kinematic_preserved rp hp rv alo aup tl clock vloEx vupEx
    r h v w vlo vup a T ha haup hw hT (hfinish.1.resolve_right (not_lt_of_ge htl))
    hstart.2 hfinish.2 hsafe⟩

/-- Collision exclusion along the worst permitted delay acceleration, including
its endpoint. That endpoint is also the origin of the resolution trajectory. -/
def delayPrefix (rp hp rv ad D r h v w : ℝ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ D →
    rp < |r - rv * t| ∨ w * (h - (-(w * ad) / 2 * t ^ 2 + v * t)) < -hp

/-- The selected delayed kyx uses the velocity after the delay in `A`.
Split its quantified graph into the delay prefix and that shifted lower region. -/
theorem delayed_decomposition (rp hp rv alo ad r h v w vlo d : ℝ) (ha : 0 < alo) :
    Dimpl rp hp rv alo ad r h v w vlo d ↔
      delayPrefix rp hp rv ad (max 0 d) r h v w ∧
      Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo := by
  constructor
  · intro hs
    have hres : Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo := by
      intro t rn hn ⟨hrn, hA⟩
      have hval := hs (max 0 d + t) (rv * (max 0 d + t))
        (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d + hn)
        (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d)
        (v - w * ad * max 0 d)
        ⟨rfl, Or.inr ⟨⟨rfl, by ring⟩, by convert hA using 1 <;> ring⟩⟩
      rw [hrn]
      convert hval using 1 <;> ring_nf
    refine ⟨?_, hres⟩
    intro t ht htd
    by_cases hs' : t < max 0 d
    · exact hs t (rv * t) (-(w * ad) / 2 * t ^ 2 + v * t) 0 0
        ⟨rfl, Or.inl ⟨ht, hs', rfl⟩⟩
    · have heq : t = max 0 d := le_antisymm htd (le_of_not_gt hs')
      subst t
      have hval := hres 0 0 0 ⟨by ring, A_zero alo _ w vlo ha⟩
      simpa only [mul_zero, sub_zero, zero_add] using hval
  · rintro ⟨hpre, hres⟩ t rn hn hd vd ⟨hrn, hdelay | ⟨⟨hhd, hvd⟩, hA⟩⟩
    · rcases hdelay with ⟨ht, htd, rfl⟩
      simpa only [hrn] using hpre t ht htd.le
    · have hvel : vd = v - w * ad * max 0 d := by linarith
      rw [hvel] at hA
      have hval := hres (t - max 0 d) (rv * (t - max 0 d)) (hn - hd) ⟨rfl, hA⟩
      rw [hhd] at hval
      rw [hrn]
      convert hval using 1 <;> ring_nf

theorem delayed_nonpos (rp hp rv alo ad r h v w vlo d : ℝ) (ha : 0 < alo) (hd : d ≤ 0) :
    Dimpl rp hp rv alo ad r h v w vlo d ↔ Limpl rp hp rv alo r h v w vlo := by
  rw [delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha, max_eq_left hd]
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero]
  constructor
  · exact And.right
  · intro hs
    refine ⟨?_, hs⟩
    intro t ht hu
    have heq : t = 0 := le_antisymm hu ht
    subst t
    simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] using
      hs 0 0 0 ⟨by ring, A_zero alo v w vlo ha⟩

theorem delay_height_compare (ad T q v w a : ℝ) (hw : Sense w)
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hacc : -ad ≤ w * a) :
    w * (-(w * ad) / 2 * (T + q) ^ 2 + v * (T + q)) ≤
      w * (a / 2 * T ^ 2 + v * T + (-(w * ad) / 2 * q ^ 2 + (v + a * T) * q)) := by
  have hprod := mul_nonneg (mul_nonneg (show 0 ≤ w * a + ad by linarith) hT)
    (show 0 ≤ T + 2 * q by linarith)
  rcases hw with rfl | rfl <;> norm_num at hprod ⊢ <;> nlinarith

theorem delay_actual_bounds (ad T v w a : ℝ) (hw : Sense w)
    (hT : 0 ≤ T) (hacc : -ad ≤ w * a) :
    w * (-(w * ad) / 2 * T ^ 2 + v * T) ≤ w * (a / 2 * T ^ 2 + v * T) ∧
      w * (v - w * ad * T) ≤ w * (v + a * T) := by
  have hh := delay_height_compare ad T 0 v w a hw hT le_rfl hacc
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
  refine ⟨hh, ?_⟩
  have hprod := mul_nonneg (show 0 ≤ w * a + ad by linarith) hT
  rcases hw with rfl | rfl <;> norm_num at hprod ⊢ <;> nlinarith

/-- While delay remains, the acceleration test bounds both future delay heights
and the resolution's starting velocity. Propagate the shifted lower region. -/
theorem delayed_before_preserved (rp hp rv alo ad r h v w vlo d a T : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hT : 0 ≤ T) (hTd : T ≤ d)
    (hacc : -ad ≤ w * a) (hsafe : Dimpl rp hp rv alo ad r h v w vlo d) :
    Dimpl rp hp rv alo ad (r - rv * T) (h - (a / 2 * T ^ 2 + v * T))
      (v + a * T) w vlo (d - T) := by
  rw [delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha,
    max_eq_right (show 0 ≤ d - T by linarith)]
  have hs := (delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha).mp hsafe
  rw [max_eq_right (hT.trans hTd)] at hs
  constructor
  · intro t ht htd
    have hval := hs.1 (T + t) (add_nonneg hT ht) (by linarith)
    rcases hval with hsep | hsep
    · left
      simpa only [show r - rv * T - rv * t = r - rv * (T + t) by ring] using hsep
    · right
      nlinarith [delay_height_compare ad T t v w a hw hT ht hacc]
  · have hh := delay_height_compare ad T (d - T) v w a hw hT
      (sub_nonneg.mpr hTd) hacc
    rw [show T + (d - T) = d by ring] at hh
    have hv : w * (v - w * ad * d) ≤ w * (v + a * T - w * ad * (d - T)) := by
      have hp := mul_nonneg (show 0 ≤ w * a + ad by linarith) hT
      rcases hw with rfl | rfl <;> norm_num at hp ⊢ <;> nlinarith
    rw [show r - rv * T - rv * (d - T) = r - rv * d by ring]
    exact lower_region_mono rp hp rv alo _ _ _ _ _ w vlo ha hw
      (by nlinarith) hv hs.2

/-- Once delay expires, first compare the actual state at expiry with the delay
endpoint, then apply immediate preservation over the remaining actual motion. -/
theorem delayed_after_preserved (rp hp rv alo ad r h v w vlo d a T : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hTd : max 0 d ≤ T)
    (hacc : -ad ≤ w * a)
    (hstart : advisoryLo alo (v + a * max 0 d) w vlo a)
    (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hsafe : Dimpl rp hp rv alo ad r h v w vlo d) :
    Dimpl rp hp rv alo ad (r - rv * T) (h - (a / 2 * T ^ 2 + v * T))
      (v + a * T) w vlo (d - T) := by
  rw [delayed_nonpos _ _ _ _ _ _ _ _ _ _ _ ha
    (show d - T ≤ 0 by linarith [le_max_right 0 d])]
  have hs := ((delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha).mp hsafe).2
  obtain ⟨hh, hv⟩ := delay_actual_bounds ad (max 0 d) v w a hw (le_max_left 0 d) hacc
  have hm := lower_region_mono rp hp rv alo (r - rv * max 0 d)
    (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
    (h - (a / 2 * max 0 d ^ 2 + v * max 0 d))
    (v - w * ad * max 0 d) (v + a * max 0 d) w vlo ha hw (by nlinarith) hv hs
  have hc := lower_kinematic_preserved rp hp rv alo (r - rv * max 0 d)
    (h - (a / 2 * max 0 d ^ 2 + v * max 0 d)) (v + a * max 0 d) w vlo a
    (T - max 0 d) ha hw (sub_nonneg.mpr hTd) hstart
    (by convert hfinish using 1; ring) hm
  convert hc using 1 <;> ring_nf

theorem delayed_solution (rv a r h v d T : ℝ) (D : ℝ × ℝ × ℝ × ℝ × ℝ → Prop)
    (path : ℝ → ℝ × ℝ × ℝ × ℝ × ℝ)
    (hevo : IsEvolution path (Evolvable.denotation (delayedMotion rv a)) D (r, h, v, d, 0) T) :
    ∀ t ∈ Set.Icc 0 T,
      path t = (r - rv * t, h - (a / 2 * t ^ 2 + v * t), v + a * t, d - t, t) := by
  let project := fun s : ℝ × ℝ × ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2.1, s.2.2.2.2)
  have hmotion : IsEvolution (fun t => project (path t))
      (Evolvable.denotation (clockedMotion rv a)) (fun _ => True) (r, h, v, 0) T := by
    refine ⟨?_, fun _ _ => trivial, ?_⟩
    · simp [project, hevo.1]
    · intro t ht
      convert! (hevo.2.2 t ht).fst.prodMk
        ((hevo.2.2 t ht).snd.fst.prodMk
          ((hevo.2.2 t ht).snd.snd.fst.prodMk (hevo.2.2 t ht).snd.snd.snd.snd)) using 1
  have hdelay : Set.EqOn (fun t => (path t).2.2.2.1) (fun t => d - t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => -1)
    · exact fun t ht => (hevo.2.2 t ht).snd.snd.snd.fst
    · intro t _
      convert! ((hasDerivAt_const t d).sub (hasDerivAt_id t)).hasDerivWithinAt using 1
      norm_num
    · simp [hevo.1]
  intro t ht
  have hm := clocked_solution rv a r h v 0 T _ _ hmotion t ht
  have hd := hdelay ht
  dsimp only [project] at hm
  have hr : (path t).1 = r - rv * t := congrArg (fun s => s.1) hm
  have hh : (path t).2.1 = h - (a / 2 * t ^ 2 + v * t) := congrArg (fun s => s.2.1) hm
  have hv : (path t).2.2.1 = v + a * t := congrArg (fun s => s.2.2.1) hm
  have hc : (path t).2.2.2.2 = t := by simpa using congrArg (fun s => s.2.2.2) hm
  exact Prod.ext hr (Prod.ext hh (Prod.ext hv (Prod.ext hd hc)))

def delayedStep (_rp _hp rv alo _ad ε w vlo a r h v d : ℝ) :=
  evolve (delayedMotion rv a) (delayedDomain alo ε w vlo a) (r, h, v, d, 0)

@[spec] theorem delayedStep_spec (rp hp rv alo ad ε w vlo a r h v d : ℝ) :
    ⦃0 < alo ∧ Sense w ∧ -ad ≤ w * a ∧ Dimpl rp hp rv alo ad r h v w vlo d⦄
    delayedStep rp hp rv alo ad ε w vlo a r h v d
    ⦃fun (r, h, v, d, _) => Dimpl rp hp rv alo ad r h v w vlo d⦄ := by
  constructor
  intro ⟨ha, hw, hacc, hsafe⟩
  unfold delayedStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (delayedMotion rv a))
    (delayedDomain alo ε w vlo a) (r, h, v, d, 0)
    (Q := fun (r, h, v, d, _) => Dimpl rp hp rv alo ad r h v w vlo d)).le_wp
  intro T hT path hevo
  rw [delayed_solution rv a r h v d T _ path hevo T ⟨hT, le_rfl⟩]
  by_cases hTd : T < max 0 d
  · have hd : 0 ≤ d := by
      by_contra hn
      rw [max_eq_left (le_of_not_ge hn)] at hTd
      linarith
    exact delayed_before_preserved rp hp rv alo ad r h v w vlo d a T ha hw hT
      (by rw [max_eq_right hd] at hTd; exact hTd.le) hacc hsafe
  · have hDT : max 0 d ≤ T := le_of_not_gt hTd
    have hstart := hevo.2.1 (max 0 d) ⟨le_max_left 0 d, hDT⟩
    have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
    rw [delayed_solution rv a r h v d T _ path hevo (max 0 d)
      ⟨le_max_left 0 d, hDT⟩] at hstart
    rw [delayed_solution rv a r h v d T _ path hevo T ⟨hT, le_rfl⟩] at hfinish
    exact delayed_after_preserved rp hp rv alo ad r h v w vlo d a T ha hw hDT hacc
      (hstart.2 (by linarith [le_max_right 0 d]))
      (hfinish.2 (by linarith [le_max_right 0 d])) hsafe

def delayChoice (δ ε : ℝ) : SetM ℝ := chooseS {δ, δ + ε}

@[spec] theorem delayChoice_spec (δ ε : ℝ) :
    ⦃True⦄ delayChoice δ ε ⦃fun _ => True⦄ := by
  constructor
  intro _
  rw [SetM.wp_iff_run]
  simp

/-- Intrinsic annotation of the selected delayed kyx controller. The two delay
choices remain exactly `δ` and `δ+ε`; the wrapper equality is proved by `rfl`. -/
def delayed' (rp hp rv alo ad δ ε r h v w vlo d : ℝ) : SetM (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
    requires 0 < alo ∧ Sense w ∧ Dimpl rp hp rv alo ad r h v w vlo d
    ensures (r, h, v, w, vlo, d) => Sense w ∧ Dimpl rp hp rv alo ad r h v w vlo d
    := do
  let mut (r, h, v, w, vlo, d) := (r, h, v, w, vlo, d)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ Sense w ∧ Dimpl rp hp rv alo ad r h v w vlo d do
    let bool ← choose Bool
    if bool then
      vlo ← choose ℝ
      w ← sense
      d ← delayChoice δ ε
      ensure (Dimpl rp hp rv alo ad r h v w vlo d)
    let a ← choose ℝ
    unless (-ad ≤ w * a) do abort
    (r, h, v, d, _) ← delayedStep rp hp rv alo ad ε w vlo a r h v d
  return (r, h, v, w, vlo, d)

theorem delayed_noNMAC (rp hp rv alo ad r h v w vlo d : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hsafe : Dimpl rp hp rv alo ad r h v w vlo d) :
    NoNMAC rp hp r h := by
  have hval := ((delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha).mp hsafe).1 0
    le_rfl (le_max_left 0 d)
  rcases hval with hsep | hsep
  · left
    simpa using hsep
  · right
    rcases hw with rfl | rfl <;>
      norm_num at hsep ⊢ <;> linarith [le_abs_self h, neg_le_abs h]

theorem delayed_eq (rp hp rv alo ad δ ε r h v w vlo d : ℝ) :
    delayed rp hp rv alo ad δ ε r h v w vlo d =
      delayed' rp hp rv alo ad δ ε r h v w vlo d := rfl

/-- STTT Theorem 2; the bundled delayed kyx also preserves its implicit region. -/
theorem delayed_safe :
    ∀ rp hp rv alo ad δ ε r h v w vlo d,
      Bounds rp hp rv alo → (0 ≤ ad ∧ 0 ≤ δ ∧ 0 ≤ ε) → Sense w →
      Dimpl rp hp rv alo ad r h v w vlo d →
        ∀ res ∈ SetM.run (delayed rp hp rv alo ad δ ε r h v w vlo d),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2.1
          let d_res := res.2.2.2.2.2
          NoNMAC rp hp r_res h_res ∧
            Dimpl rp hp rv alo ad r_res h_res v_res w_res vlo_res d_res := by
  intro rp hp rv alo ad δ ε r h v w vlo d hb _had hw hsafe res hrun
  rw [delayed_eq] at hrun
  have hinv := (delayed'.spec rp hp rv alo ad δ ε r h v w vlo d).le_wp
    ⟨hb.2.2.2, hw, hsafe⟩ res hrun
  exact ⟨delayed_noNMAC rp hp rv alo ad _ _ _ _ _ _ hb.2.2.2 hinv.1 hinv.2, hinv.2⟩

noncomputable def delayPoly (ad V t : ℝ) : ℝ := -ad * t ^ 2 + 2 * V * t

/-- The signed delay parabola is concave, so its minimum on a closed collision
interval occurs at an endpoint. This also covers zero delay and `ad = 0`. -/
theorem delayPoly_min (ad V l u t : ℝ) (had : 0 ≤ ad) (hlt : l ≤ t) (htu : t ≤ u) :
    delayPoly ad V l ≤ delayPoly ad V t ∨ delayPoly ad V u ≤ delayPoly ad V t := by
  by_cases hs : 0 ≤ 2 * V - ad * (t + l)
  · left
    unfold delayPoly
    nlinarith [mul_nonneg (sub_nonneg.mpr hlt) hs]
  · right
    have hsl : 0 ≤ ad * (u + t) - 2 * V := by
      nlinarith [mul_nonneg had (show 0 ≤ u - l by linarith)]
    unfold delayPoly
    nlinarith [mul_nonneg (sub_nonneg.mpr htu) hsl]

def delayWindow (ad V D l u H : ℝ) : Prop :=
  ((l ≤ 0 ∧ 0 ≤ u) → H < 0) ∧
  ((0 < l ∧ l ≤ D) → H < delayPoly ad V l) ∧
  ((0 ≤ u ∧ u < D) → H < delayPoly ad V u) ∧
  ((l ≤ D ∧ D ≤ u) → H < delayPoly ad V D)

theorem delay_window_equivalent (ad V D l u H : ℝ) (had : 0 ≤ ad) (hD : 0 ≤ D)
    (hlu : l ≤ u) : delayWindow ad V D l u H ↔
      ∀ t, 0 ≤ t → t ≤ D → l ≤ t → t ≤ u → H < delayPoly ad V t := by
  constructor
  · rintro ⟨hzero, hleft, hright, hend⟩ t ht htd hlt htu
    have hL : H < delayPoly ad V (max 0 l) := by
      by_cases hl : l ≤ 0
      · simpa [max_eq_left hl, delayPoly] using hzero ⟨hl, ht.trans htu⟩
      · rw [max_eq_right (le_of_not_ge hl)]
        exact hleft ⟨lt_of_not_ge hl, hlt.trans htd⟩
    have hU : H < delayPoly ad V (min D u) := by
      by_cases hu : u < D
      · rw [min_eq_right hu.le]
        exact hright ⟨ht.trans htu, hu⟩
      · rw [min_eq_left (le_of_not_gt hu)]
        exact hend ⟨hlt.trans htd, le_of_not_gt hu⟩
    rcases delayPoly_min ad V (max 0 l) (min D u) t had (max_le ht hlt)
      (le_min htd htu) with h | h
    · exact hL.trans_le h
    · exact hU.trans_le h
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      simpa [delayPoly] using hs 0 le_rfl hD h.1 h.2
    · intro h
      exact hs l h.1.le h.2 le_rfl hlu
    · intro h
      exact hs u h.1 h.2.le hlu le_rfl
    · intro h
      exact hs D hD le_rfl h.1 h.2

theorem delay_height_iff (ad t h v w hp : ℝ) (hw : Sense w) :
    w * (h - (-(w * ad) / 2 * t ^ 2 + v * t)) < -hp ↔
      2 * (w * h + hp) < delayPoly ad (w * v) t := by
  unfold delayPoly
  rcases hw with rfl | rfl <;> constructor <;> intro hx <;> nlinarith

theorem delay_prefix_window (rp hp rv ad D r h v w : ℝ) (hw : Sense w) (hrv : 0 < rv) :
    delayPrefix rp hp rv ad D r h v w ↔
      ∀ t, 0 ≤ t → t ≤ D → (r - rp) / rv ≤ t → t ≤ (r + rp) / rv →
        2 * (w * h + hp) < delayPoly ad (w * v) t := by
  constructor
  · intro hs t ht htd hl hu
    have hinside : |r - rv * t| ≤ rp := by
      rw [abs_le]
      rw [div_le_iff₀ hrv] at hl
      rw [le_div_iff₀ hrv] at hu
      constructor <;> nlinarith
    exact (delay_height_iff ad t h v w hp hw).mp
      ((hs t ht htd).resolve_left (not_lt_of_ge hinside))
  · intro hs t ht htd
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      apply (delay_height_iff ad t h v w hp hw).mpr
      exact hs t ht htd (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
    · exact Or.inl (lt_of_not_ge hinside)

def delayExplicit (ad V D l u H : ℝ) : Prop :=
  ((l ≤ 0 ∧ 0 ≤ u) → H < 0) ∧
  ((0 < l ∧ l ≤ D) → H < delayPoly ad V l) ∧
  ((0 ≤ u ∧ u < D) → H < delayPoly ad V u)

theorem explicit_delay_window (rp hp rv alo ad r h v w vlo d : ℝ)
    (hb : Bounds rp hp rv alo) (hw : Sense w) (hrv : 0 < rv) :
    Dexpl rp hp rv alo ad r h v w vlo d ↔
      delayExplicit ad (w * v) (max 0 d) ((r - rp) / rv) ((r + rp) / rv)
        (2 * (w * h + hp)) ∧
      Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo := by
  have hquad (z : ℝ) :
      (2 * (w * h + hp) < delayPoly ad (w * v) (z / rv)) ↔
      w * rv ^ 2 * h < -ad / 2 * z ^ 2 + w * rv * v * z - rv ^ 2 * hp := by
    apply positive_scale_lt (rv ^ 2 / 2) _ _ _ _ (by positivity)
    unfold delayPoly
    field_simp
    ring
  have hzero : (2 * (w * h + hp) < 0) ↔ w * h < -hp := by
    constructor <;> intro hx <;> linarith
  have hc₀ : ((r - rp) / rv ≤ 0 ∧ 0 ≤ (r + rp) / rv) ↔ (-rp ≤ r ∧ r ≤ rp) := by
    rw [div_le_iff₀ hrv, le_div_iff₀ hrv]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  have hc₁ : (0 < (r - rp) / rv ∧ (r - rp) / rv ≤ max 0 d) ↔
      (rp < r ∧ r ≤ rv * max 0 d + rp) := by
    rw [lt_div_iff₀ hrv, div_le_iff₀ hrv]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  have hc₂ : (0 ≤ (r + rp) / rv ∧ (r + rp) / rv < max 0 d) ↔
      (-rp ≤ r ∧ r < rv * max 0 d - rp) := by
    rw [le_div_iff₀ hrv, div_lt_iff₀ hrv]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  unfold Dexpl delayExplicit
  dsimp only
  rw [immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw]
  simp only [hquad, hzero, hc₀, hc₁, hc₂, and_assoc]

theorem delayed_regions_pos (rp hp rv alo ad r h v w vlo d : ℝ)
    (hb : Bounds rp hp rv alo) (had : 0 ≤ ad) (hw : Sense w) (hrv : 0 < rv) :
    Dexpl rp hp rv alo ad r h v w vlo d ↔ Dimpl rp hp rv alo ad r h v w vlo d := by
  have hterminal :
      Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo →
      ((r - rp) / rv ≤ max 0 d ∧ max 0 d ≤ (r + rp) / rv) →
        2 * (w * h + hp) < delayPoly ad (w * v) (max 0 d) := by
    intro hs ⟨hl, hu⟩
    have hval := hs 0 0 0 ⟨by ring, A_zero alo _ w vlo hb.2.2.2⟩
    have hinside : |r - rv * max 0 d| ≤ rp := by
      rw [abs_le]
      rw [div_le_iff₀ hrv] at hl
      rw [le_div_iff₀ hrv] at hu
      constructor <;> nlinarith
    simp only [sub_zero] at hval
    exact (delay_height_iff ad (max 0 d) h v w hp hw).mp
      (hval.resolve_left (not_lt_of_ge hinside))
  rw [explicit_delay_window _ _ _ _ _ _ _ _ _ _ _ hb hw hrv,
    delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ hb.2.2.2,
    delay_prefix_window _ _ _ _ _ _ _ _ _ hw hrv]
  have heq := delay_window_equivalent ad (w * v) (max 0 d)
    ((r - rp) / rv) ((r + rp) / rv) (2 * (w * h + hp)) had (le_max_left 0 d)
    (div_le_div_of_nonneg_right (by linarith [hb.1]) hrv.le)
  constructor
  · rintro ⟨hex, hs⟩
    exact ⟨heq.mp ⟨hex.1, hex.2.1, hex.2.2, hterminal hs⟩, hs⟩
  · rintro ⟨hpre, hs⟩
    have hwin := heq.mpr hpre
    exact ⟨⟨hwin.1, hwin.2.1, hwin.2.2.1⟩, hs⟩

theorem delayed_regions_zero (rp hp alo ad r h v w vlo d : ℝ)
    (hb : Bounds rp hp 0 alo) (had : 0 ≤ ad) (hw : Sense w) :
    Dexpl rp hp 0 alo ad r h v w vlo d ↔ Dimpl rp hp 0 alo ad r h v w vlo d := by
  rw [Dexpl]
  rw [immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw,
    delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ hb.2.2.2]
  have hbad₁ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  have hbad₂ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [zero_mul, mul_zero, zero_add, sub_zero, zero_sub, hbad₁, hbad₂,
    false_implies, true_and]
  constructor
  · rintro ⟨hinit, hs⟩
    refine ⟨?_, hs⟩
    intro t ht htd
    by_cases hsep : rp < |r|
    · exact Or.inl (by simpa using hsep)
    · right
      have hinside := abs_le.mp (le_of_not_gt hsep)
      have hzero : 2 * (w * h + hp) < delayPoly ad (w * v) 0 := by
        have hx := hinit hinside
        simp only [delayPoly, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
        linarith
      have hend : 2 * (w * h + hp) < delayPoly ad (w * v) (max 0 d) := by
        have hx := hs 0 0 0 ⟨by ring, A_zero alo _ w vlo hb.2.2.2⟩
        simp only [sub_zero] at hx
        exact (delay_height_iff ad (max 0 d) h v w hp hw).mp (hx.resolve_left hsep)
      apply (delay_height_iff ad t h v w hp hw).mpr
      exact (delayPoly_min ad (w * v) 0 (max 0 d) t had ht htd).elim
        (fun hx => hzero.trans_le hx) (fun hx => hend.trans_le hx)
  · rintro ⟨hpre, hs⟩
    refine ⟨?_, hs⟩
    intro hinside
    have hx := hpre 0 le_rfl (le_max_left 0 d)
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] at hx
    exact hx.resolve_left (not_lt_of_ge (abs_le.mpr hinside))

/-- STTT Lemma 2, Fig. 5; the explicit predicate is transcribed from the journal. -/
theorem delayed_regions_equivalent :
    ∀ rp hp rv alo ad r h v w vlo d,
      Bounds rp hp rv alo → 0 ≤ ad → Sense w →
        (Dexpl rp hp rv alo ad r h v w vlo d ↔ Dimpl rp hp rv alo ad r h v w vlo d) := by
  intro rp hp rv alo ad r h v w vlo d hb had hw
  by_cases hr : rv = 0
  · subst rv
    exact delayed_regions_zero rp hp alo ad r h v w vlo d hb had hw
  · exact delayed_regions_pos rp hp rv alo ad r h v w vlo d hb had hw
      (lt_of_le_of_ne hb.2.2.1 (Ne.symm hr))

-- Match the real normed-space instance used when elaborating the challenge.
-- The derivative-tactic imports also supply an inner-product-space instance.
attribute [local instance 2000] NormedField.toNormedSpace

def horizontalDot (rx ry rv : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ :=
  fun (x, y, s, _n) => x * rx + y * ry + s * rv

def horizontalEnergy : ℝ × ℝ × ℝ × ℝ → ℝ :=
  fun (x, y, s, n) => x ^ 2 + y ^ 2 - s ^ 2 - n ^ 2

/-- Preserve the projected horizontal velocity relation before the energy identity. -/
theorem horizontal_dot_preserved (rx ry rv : ℝ) (hvel : rv ^ 2 = rx ^ 2 + ry ^ 2) :
    (fun st => horizontalDot rx ry rv st = 0)
    [[evolve (horizontalMotion rx ry rv) (fun _ => True)]]
    (fun st => horizontalDot rx ry rv st = 0) := by
  apply dIeq (horizontalDot rx ry rv) (fun _ => 0)
  · ode_deriv [horizontalDot, horizontalMotion]
    linarith
  · exact fun _ h => h
  · exact fun _ _ => rfl

/-- The dot relation makes the derivative of the coordinate energy vanish. -/
theorem horizontal_energy_preserved (rx ry rv : ℝ) (hvel : rv ^ 2 = rx ^ 2 + ry ^ 2) :
    (fun st => horizontalDot rx ry rv st = 0 ∧ horizontalEnergy st = 0)
    [[evolve (horizontalMotion rx ry rv) (fun _ => True)]]
    (fun st => horizontalEnergy st = 0) := by
  apply dC (cut := fun st => horizontalDot rx ry rv st = 0)
  · exact fun st h => horizontal_dot_preserved rx ry rv hvel st h.1
  · apply dIeq horizontalEnergy (fun st => 2 * horizontalDot rx ry rv st)
    · ode_deriv [horizontalEnergy, horizontalDot, horizontalMotion]
      linarith
    · exact fun _ h => h.2
    · intro st h
      simp [h.2]

/-- STTT Proposition 1, Eq. (11); no extra nonzero-speed assumption. -/
theorem horizontal_reduction :
    ∀ rp rx ry rv x y s n,
      HorizontalCoordinates rx ry rv x y s n →
        ∀ res ∈ SetM.run (evolve (horizontalMotion rx ry rv) (fun _ => True) (x, y, s, n)),
          let x_res := res.1
          let y_res := res.2.1
          let s_res := res.2.2.1
          let n_res := res.2.2.2
          (rp ^ 2 < x_res ^ 2 + y_res ^ 2 ↔ rp ^ 2 - n_res ^ 2 < s_res ^ 2) := by
  intro rp rx ry rv x y s n hcoord ⟨xr, yr, sr, nr⟩ hrun
  have henergy := horizontal_energy_preserved rx ry rv hcoord.2.2.2 (x, y, s, n)
    (by constructor <;> dsimp [horizontalDot, horizontalEnergy] <;>
          linarith [hcoord.1, hcoord.2.2.1])
    (xr, yr, sr, nr) hrun
  change (rp ^ 2 < xr ^ 2 + yr ^ 2 ↔ rp ^ 2 - nr ^ 2 < sr ^ 2)
  dsimp [horizontalEnergy] at henergy
  constructor <;> intro h <;> linarith

/-- A convex capped nominal trajectory is bounded by one of the endpoints. -/
theorem upper_nominal_endpoints (v F s z t : ℝ)
    (hF : v ≤ F) (_hs : 0 ≤ s) (hsz : s ≤ z) (hzt : z ≤ t) :
    nominal v F z ≤ max (nominal v F s) (nominal v F t) := by
  have hM : max 0 (F - v) = F - v := max_eq_right (sub_nonneg.mpr hF)
  simp only [nominal, hM]
  split_ifs with hz hs' ht
  all_goals try linarith
  · by_cases h : z + v ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z - s by linarith)
        (show z + s + 2 * v ≤ 0 by linarith)]
    · apply le_max_of_le_right
      nlinarith [mul_nonneg (show 0 ≤ t - z by linarith)
        (show 0 ≤ t + z + 2 * v by linarith)]
  · by_cases h : z + v ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z - s by linarith)
        (show z + s + 2 * v ≤ 0 by linarith)]
    · apply le_max_of_le_right
      have hFp : 0 ≤ F := by linarith
      nlinarith [mul_nonneg (show 0 ≤ F - v - z by linarith)
          (show 0 ≤ F - v + z + 2 * v by linarith),
        mul_nonneg hFp (show 0 ≤ t - (F - v) by linarith)]
  · by_cases h : F ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonneg (show 0 ≤ F - v - s by linarith)
          (show 0 ≤ -2 * v - s - (F - v) by linarith),
        mul_nonpos_of_nonpos_of_nonneg h (show 0 ≤ z - (F - v) by linarith)]
    · apply le_max_of_le_right
      nlinarith [mul_nonneg (le_of_not_ge h) (show 0 ≤ t - z by linarith)]
  · by_cases h : F ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonpos_of_nonpos_of_nonneg h (show 0 ≤ z - s by linarith)]
    · apply le_max_of_le_right
      nlinarith [mul_nonneg (le_of_not_ge h) (show 0 ≤ t - z by linarith)]

theorem nominal_antitone_nonpos (v target s t : ℝ) (hF : target ≤ 0)
    (hs : 0 ≤ s) (hst : s ≤ t) : nominal v target t ≤ nominal v target s := by
  by_cases hgap : 0 ≤ target - v
  · simp only [nominal, max_eq_right hgap]
    split_ifs with ht hs'
    · nlinarith [mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ -2 * v - s - t by linarith)]
    · linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF
        (show 0 ≤ t - (target - v) by linarith), sq_nonneg (s - (target - v))]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF (sub_nonneg.mpr hst)]
  · simp only [nominal, max_eq_left (le_of_not_ge hgap),
      ite_eq_right (not_lt_of_ge (hs.trans hst)), ite_eq_right (not_lt_of_ge hs)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hF (sub_nonneg.mpr hst)]

/-- Upper-bound cases in acceleration-scaled time coordinates. -/
def upperWindow (v F l u height : ℝ) : Prop :=
  let M := max 0 (F - v)
  (0 < F →
    ((l ≤ 0 ∧ 0 ≤ u) → 0 < height) ∧
    ((0 < l ∧ l ≤ M) → l ^ 2 + 2 * v * l < height) ∧
    ((0 ≤ u ∧ u < M) → u ^ 2 + 2 * v * u < height) ∧
    (M ≤ u → 2 * F * u - M ^ 2 < height)) ∧
  (F ≤ 0 →
    ((l ≤ 0 ∧ 0 ≤ u) → 0 < height) ∧
    ((0 < l ∧ l ≤ M) → l ^ 2 + 2 * v * l < height) ∧
    (M < l → 2 * F * l - M ^ 2 < height))

theorem upper_window_equivalent (v F l u height : ℝ) (hF : v ≤ F) (hlu : l ≤ u) :
    upperWindow v F l u height ↔
      ∀ t, 0 ≤ t → l ≤ t → t ≤ u → nominal v F t < height := by
  have hM : 0 ≤ max 0 (F - v) := le_max_left 0 _
  have hzero : nominal v F 0 = 0 := by
    by_cases hm : max 0 (F - v) = 0
    · simp [nominal, hm]
    · simp [nominal, lt_of_le_of_ne hM (Ne.symm hm)]
  constructor
  · intro hex t ht hlt htu
    rcases lt_or_ge 0 F with hpos | hneg
    · obtain ⟨h10, h11, h12, h13⟩ := hex.1 hpos
      have hright : nominal v F u < height := by
        by_cases hu : u < max 0 (F - v)
        · have hx := h12 ⟨ht.trans htu, hu⟩
          rw [nominal_of_le v F u hu.le]
          exact hx
        · have hx := h13 (le_of_not_gt hu)
          simpa [nominal, not_lt_of_ge (le_of_not_gt hu)] using hx
      by_cases hl : l ≤ 0
      · have hleft : nominal v F 0 < height := by simpa [hzero] using h10 ⟨hl, ht.trans htu⟩
        exact (upper_nominal_endpoints v F 0 t u hF le_rfl ht htu).trans_lt (max_lt hleft hright)
      · have hl0 : 0 < l := lt_of_not_ge hl
        by_cases hlM : l ≤ max 0 (F - v)
        · have hleft : nominal v F l < height := by
            rw [nominal_of_le v F l hlM]
            exact h11 ⟨hl0, hlM⟩
          exact (upper_nominal_endpoints v F l t u hF hl0.le hlt htu).trans_lt
            (max_lt hleft hright)
        · have hleft : nominal v F l < height := by
            have hle : nominal v F l ≤ nominal v F u := by
              simp only [nominal, ite_eq_right (not_lt_of_ge (le_of_not_ge hlM)),
                ite_eq_right (not_lt_of_ge ((le_of_not_ge hlM).trans hlu))]
              nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hlu)]
            exact hle.trans_lt hright
          exact (upper_nominal_endpoints v F l t u hF hl0.le hlt htu).trans_lt
            (max_lt hleft hright)
    · obtain ⟨h10, h11, h14⟩ := hex.2 hneg
      by_cases hl : l ≤ 0
      · have hleft : nominal v F 0 < height := by simpa [hzero] using h10 ⟨hl, ht.trans htu⟩
        exact (nominal_antitone_nonpos v F 0 t hneg le_rfl ht).trans_lt hleft
      · have hl0 : 0 < l := lt_of_not_ge hl
        have hleft : nominal v F l < height := by
          by_cases hlM : l ≤ max 0 (F - v)
          · rw [nominal_of_le v F l hlM]
            exact h11 ⟨hl0, hlM⟩
          · simpa [nominal, not_lt_of_ge (le_of_not_ge hlM)] using h14 (lt_of_not_ge hlM)
        exact (nominal_antitone_nonpos v F l t hneg hl0.le hlt).trans_lt hleft
  · intro himp
    constructor
    · intro hpos
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨hl, hu⟩
        simpa [hzero] using himp 0 le_rfl hl hu
      · rintro ⟨hl, hM'⟩
        have h := himp l hl.le le_rfl hlu
        rwa [nominal_of_le v F l hM'] at h
      · rintro ⟨hu, hM'⟩
        have h := himp u hu hlu le_rfl
        rwa [nominal_of_le v F u hM'.le] at h
      · intro hu
        have h := himp u (hM.trans hu) hlu le_rfl
        simpa [nominal, not_lt_of_ge hu] using h
    · intro hneg
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨hl, hu⟩
        simpa [hzero] using himp 0 le_rfl hl hu
      · rintro ⟨hl, hM'⟩
        have h := himp l hl.le le_rfl hlu
        rwa [nominal_of_le v F l hM'] at h
      · intro hl
        have h := himp l (hM.trans hl.le) le_rfl hlu
        simpa [nominal, not_lt_of_ge hl.le] using h

set_option maxHeartbeats 4000000 in
-- Normalizing all scaled inequalities in the piecewise formula is expensive.
/-- Algebraic translation of the upper explicit cases for positive closing speed. -/
theorem upper_explicit_window (rp hp rv aup r h v w vup : ℝ)
    (ha : 0 < aup) (hrv : 0 < rv) :
    Uexpl rp hp rv aup r h v w vup ↔
      upperWindow (w * v) (max (w * vup) (w * v)) (aup * (r - rp) / rv)
        (aup * (r + rp) / rv) (2 * aup * (w * h - hp)) := by
  let k := rv / aup
  have hk : 0 < k := div_pos hrv ha
  have ha0 := ne_of_gt ha
  have hr0 := ne_of_gt hrv
  have htime (z : ℝ) : aup * z / rv = z / k := by dsimp [k]; field_simp
  have hshift (z : ℝ) : rv * z / aup = k * z := by dsimp [k]; ring
  have hquad (z : ℝ) :
      ((z / k) ^ 2 + 2 * (w * v) * (z / k) < 2 * aup * (w * h - hp)) ↔
      aup / 2 * z ^ 2 + w * rv * v * z + rv ^ 2 * hp < w * rv ^ 2 * h := by
    apply positive_scale_lt (rv ^ 2 / (2 * aup)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hline (z : ℝ) :
      (2 * max (w * vup) (w * v) * (z / k) - maxI v w vup ^ 2 <
        2 * aup * (w * h - hp)) ↔
      max (w * vup) (w * v) * z - rv * maxI v w vup ^ 2 / (2 * aup) + rv * hp <
        w * rv * h := by
    apply positive_scale_lt (rv / (2 * aup)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hM : max 0 (max (w * vup) (w * v) - w * v) = maxI v w vup := by
    unfold maxI
    rw [mul_sub]
    rcases le_total (w * vup) (w * v) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]
      simp
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  have hzero : (0 < 2 * aup * (w * h - hp)) ↔ hp < w * h := by
    rw [mul_pos_iff_of_pos_left (by positivity : 0 < 2 * aup), sub_pos]
  have h0u : (0 ≤ (r + rp) / k) ↔ -rp ≤ r := by
    rw [le_div_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have h0l : ((r - rp) / k ≤ 0) ↔ r ≤ rp := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have hposl : (0 < (r - rp) / k) ↔ rp < r := by
    rw [lt_div_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have hl (z : ℝ) : ((r - rp) / k ≤ z) ↔ r ≤ rp + k * z := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hu (z : ℝ) : ((r + rp) / k < z) ↔ r < -rp + k * z := by
    rw [div_lt_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hur (z : ℝ) : (z ≤ (r + rp) / k) ↔ -rp + k * z ≤ r := by
    rw [← not_lt, hu, not_lt]
  have hlr (z : ℝ) : (z < (r - rp) / k) ↔ rp + k * z < r := by
    rw [← not_le, hl, not_le]
  unfold Uexpl upperWindow
  dsimp only
  rw [htime, htime, hM]
  simp only [hquad, hline, hzero, h0u, h0l, hposl, hl, hu,
    hur, hlr, hshift, hr0, false_or, false_and, and_comm]


theorem upper_nominal_eq (aup t hn v w vup : ℝ) (ha : 0 < aup) (hw : Sense w)
    (hA : Aup aup t hn v w vup) :
    2 * aup * (w * hn) = nominal (w * v) (max (w * vup) (w * v)) (aup * t) := by
  have hM : max 0 (max (w * vup) (w * v) - w * v) = max 0 (w * (vup - v)) := by
    rw [mul_sub]
    rcases le_total (w * vup) (w * v) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]
      simp
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  have hF : max (w * vup) (w * v) = w * v + max 0 (w * (vup - v)) := by
    rw [mul_sub]
    rcases le_total (w * v) (w * vup) with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rw [Aup_scaled aup t hn v w vup ha hw hA]
  unfold nominal upperGain
  rw [hM, hF]
  split_ifs <;> ring

theorem upper_implicit_window (rp hp rv aup r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hrv : 0 < rv) :
    Uimpl rp hp rv aup r h v w vup ↔
      ∀ t, 0 ≤ t → aup * (r - rp) / rv ≤ t → t ≤ aup * (r + rp) / rv →
        nominal (w * v) (max (w * vup) (w * v)) t < 2 * aup * (w * h - hp) := by
  have ha0 := ne_of_gt ha
  constructor
  · intro hsafe t ht hl hu
    obtain ⟨hn, hA⟩ := Aup_exists aup (t / aup) v w vup (div_nonneg ht ha.le)
    have hs := upper_nominal_eq aup (t / aup) hn v w vup ha hw hA
    rw [mul_div_cancel₀ _ ha0] at hs
    have hinside : |r - rv * (t / aup)| ≤ rp := by
      rw [abs_le]
      have hl' := (div_le_iff₀ hrv).mp hl
      have hu' := (le_div_iff₀ hrv).mp hu
      have heq : aup * (rv * (t / aup)) = rv * t := by field_simp
      constructor <;> nlinarith
    have hsep := (hsafe (t / aup) (rv * (t / aup)) hn ⟨rfl, hA⟩).resolve_left
      (not_lt_of_ge hinside)
    nlinarith
  · intro hsafe t rn hn ⟨hrn, hA⟩
    rw [hrn]
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      have hs := hsafe (aup * t) (mul_nonneg ha.le (Aup_time_nonneg _ _ _ _ _ _ ha hA))
        (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
      have hn := upper_nominal_eq aup t hn v w vup ha hw hA
      nlinarith
    · exact Or.inl (lt_of_not_ge hinside)

theorem upper_nominal_all_time (v F height : ℝ) :
    (∀ t, 0 ≤ t → nominal v F t < height) ↔ F ≤ 0 ∧ 0 < height := by
  have hM : 0 ≤ max 0 (F - v) := le_max_left 0 _
  have hzero : nominal v F 0 = 0 := by
    by_cases hm : max 0 (F - v) = 0
    · simp [nominal, hm]
    · simp [nominal, lt_of_le_of_ne hM (Ne.symm hm)]
  constructor
  · intro hs
    have hheight : 0 < height := by simpa [hzero] using hs 0 le_rfl
    have hF : F ≤ 0 := by
      by_contra h
      have hp : 0 < F := lt_of_not_ge h
      let M := max 0 (F - v)
      let t := max M ((height + M ^ 2) / (2 * F))
      have ht : 0 ≤ t := hM.trans (le_max_left _ _)
      have htM : M ≤ t := le_max_left _ _
      have htM' : max 0 (F - v) ≤ t := htM
      have hv : 2 * F * t - M ^ 2 < height := by
        simpa only [nominal, ite_eq_right (not_lt_of_ge htM')] using hs t ht
      have hb := (div_le_iff₀ (show 0 < 2 * F by positivity)).mp
        (le_max_right M ((height + M ^ 2) / (2 * F)))
      dsimp only [M] at hb
      nlinarith
    exact ⟨hF, hheight⟩
  · rintro ⟨hF, hheight⟩ t ht
    have h := nominal_antitone_nonpos v F 0 t (by linarith) le_rfl ht
    rw [hzero] at h
    exact h.trans_lt hheight

theorem upper_implicit_stationary (rp hp aup r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) :
    Uimpl rp hp 0 aup r h v w vup ↔
      rp < |r| ∨ (max (w * vup) (w * v) ≤ 0 ∧ hp < w * h) := by
  by_cases hsep : rp < |r|
  · simp only [hsep, true_or, iff_true]
    intro t rn hn ⟨hrn, _⟩
    left
    simpa [hrn] using hsep
  · have hzero : (0 < 2 * aup * (w * h - hp)) ↔ hp < w * h := by
      rw [mul_pos_iff_of_pos_left (by positivity : 0 < 2 * aup), sub_pos]
    rw [or_iff_right hsep, ← hzero]
    rw [← upper_nominal_all_time]
    constructor
    · intro hsafe t ht
      obtain ⟨hn, hA⟩ := Aup_exists aup (t / aup) v w vup (div_nonneg ht ha.le)
      have hs := upper_nominal_eq aup (t / aup) hn v w vup ha hw hA
      rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hs
      have hval := (hsafe (t / aup) 0 hn ⟨by ring, hA⟩).resolve_left (by simpa using hsep)
      nlinarith
    · intro hs t rn hn ⟨hrn, hA⟩
      right
      have hval := hs (aup * t) (mul_nonneg ha.le (Aup_time_nonneg _ _ _ _ _ _ ha hA))
      have hn := upper_nominal_eq aup t hn v w vup ha hw hA
      nlinarith

theorem upper_explicit_stationary (rp hp aup r h v w vup : ℝ) :
    Uexpl rp hp 0 aup r h v w vup ↔
      rp < |r| ∨ (max (w * vup) (w * v) ≤ 0 ∧ hp < w * h) := by
  simp only [Uexpl, zero_mul, mul_zero, zero_div, sub_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), true_or, true_and]
  have himpossible₁ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  have himpossible₂ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [himpossible₁, himpossible₂, false_implies, true_and, implies_true]
  by_cases hleft : r < -rp
  · have hsep : rp < |r| := (neg_le_abs r).trans_lt' (by linarith)
    simp [not_le.mpr hleft, hsep]
  · by_cases hright : rp < r
    · have hsep : rp < |r| := hright.trans_le (le_abs_self r)
      simp [hright, not_le.mpr hright, hsep]
    · have hinside : |r| ≤ rp := abs_le.mpr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      by_cases hF : 0 < max (w * vup) (w * v)
      · have hprod : ¬ max (w * vup) (w * v) * (r + rp) < 0 :=
          not_lt_of_ge (mul_nonneg hF.le (by linarith))
        simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, not_le_of_gt hF, hprod]
      · simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, le_of_not_gt hF]

/-- STTT17 Lemma 3: the explicit and implicit two-sided safe regions agree. -/
theorem two_sided_regions_equivalent :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
        (Cexpl rp hp rv alo aup r h v w vlo vup ↔
          Cimpl rp hp rv alo aup r h v w vlo vup) := by
  intro rp hp rv alo aup r h v w vlo vup hb ha hw
  have haup : 0 < aup := hb.2.2.2.trans_le ha
  have hupper : Uexpl rp hp rv aup r h v w vup ↔ Uimpl rp hp rv aup r h v w vup := by
    by_cases hr : rv = 0
    · subst rv
      exact (upper_explicit_stationary rp hp aup r h v w vup).trans
        (upper_implicit_stationary rp hp aup r h v w vup haup hw).symm
    · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
      rw [upper_explicit_window rp hp rv aup r h v w vup haup hr,
        upper_implicit_window rp hp rv aup r h v w vup haup hw hr]
      exact upper_window_equivalent _ _ _ _ _ (le_max_right _ _) (by
        apply div_le_div_of_nonneg_right _ hr.le
        exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) haup.le)
  exact or_congr (immediate_regions_equivalent rp hp rv alo r h v w vlo hb hw) hupper


/-- An admissible remaining-time region excludes a collision at its current state. -/
theorem bounded_region_noNMAC (rp hp rv alo aup tl clock r h v w vlo vup : ℝ)
    (ha : 0 < alo) (haup : 0 < aup) (hw : Sense w) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : CimplBounded rp hp rv alo aup tl clock r h v w vlo vup) :
    NoNMAC rp hp r h := by
  rcases hsafe with hlo | hup
  · exact lower_bounded_noNMAC rp hp rv alo tl clock r h v w vlo ha hw ht hlo
  · exact upper_bounded_noNMAC rp hp rv aup tl clock r h v w vup haup hw ht hup

/-- Paper Eq. (8), with the remaining-time region invariant on both nested loops. -/
def bounded' (rp hp rv alo aup tl r h v w vlo vup clock : ℝ) :
    SetM (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
    requires 0 < alo ∧ 0 < aup ∧ Sense w ∧ (clock ≤ tl ∨ tl < 0) ∧
      CimplBounded rp hp rv alo aup tl clock r h v w vlo vup
    ensures (r, h, v, w, vlo, vup, clock) => Sense w ∧ (clock ≤ tl ∨ tl < 0) ∧
      CimplBounded rp hp rv alo aup tl clock r h v w vlo vup
    := do
  let mut (r, h, v, w, vlo, vup, clock) := (r, h, v, w, vlo, vup, clock)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ Sense w ∧ (clock ≤ tl ∨ tl < 0) ∧
        CimplBounded rp hp rv alo aup tl clock r h v w vlo vup do
    vlo ← choose ℝ
    vup ← choose ℝ
    w ← sense
    ensure (CimplBounded rp hp rv alo aup tl 0 r h v w vlo vup)
    clock := 0
    let m ← choose Nat
    for _ in [:m]
        invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ Sense w ∧ (clock ≤ tl ∨ tl < 0) ∧
          CimplBounded rp hp rv alo aup tl clock r h v w vlo vup do
      let a ← choose ℝ
      (r, h, v, clock) ← boundedStep rp hp rv alo aup tl w vlo vup a r h v clock
  return (r, h, v, w, vlo, vup, clock)

theorem bounded_eq (rp hp rv alo aup tl r h v w vlo vup clock : ℝ) :
    bounded rp hp rv alo aup tl r h v w vlo vup clock =
      bounded' rp hp rv alo aup tl r h v w vlo vup clock := rfl

/-- STTT17 Theorem 4, with weaker precondition (`0 < aup` instead of `alo ≤ aup`) and
stronger postcondition (+ Sense, + CimplBounded), following `bounded_implicit.kyx`.
The paper's initial assumptions are recovered at `t=0` with `alo ≤ aup`. -/
theorem bounded_safe :
    ∀ rp hp rv alo aup tl r h v w vlo vup t,
      Bounds rp hp rv alo ∧ 0 < aup → Sense w → (t ≤ tl ∨ tl < 0) →
      CimplBounded rp hp rv alo aup tl t r h v w vlo vup →
        ∀ res ∈ SetM.run (bounded rp hp rv alo aup tl r h v w vlo vup t),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2.1
          let vup_res := res.2.2.2.2.2.1
          let t_res := res.2.2.2.2.2.2
          NoNMAC rp hp r_res h_res ∧ Sense w_res ∧ (t_res ≤ tl ∨ tl < 0) ∧
            CimplBounded rp hp rv alo aup tl t_res r_res h_res v_res w_res vlo_res vup_res := by
  intro rp hp rv alo aup tl r h v w vlo vup t hb hw ht hsafe res hrun
  have ha := hb.1.2.2.2
  have haup := hb.2
  rw [bounded_eq] at hrun
  have hinv := (bounded'.spec rp hp rv alo aup tl r h v w vlo vup t).le_wp
    ⟨ha, haup, hw, ht, hsafe⟩ res hrun
  exact ⟨bounded_region_noNMAC rp hp rv alo aup tl _ _ _ _ _ _ _
    ha haup hinv.1 hinv.2.1 hinv.2.2, hinv⟩

/-- The bounded component of either safeable branch implies present safety. -/
theorem safeable_region_noNMAC (rp hp rv alo aup tl clock vloEx vupEx r h v w vlo vup : ℝ)
    (ha : 0 < alo) (haup : 0 < aup) (hw : Sense w) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx) :
    NoNMAC rp hp r h := by
  apply bounded_region_noNMAC rp hp rv alo aup tl clock r h v w vlo vup ha haup hw ht
  exact hsafe.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- Paper Eq. (9), preserving the nominal safeable region on both nested loops. -/
def safeable' (rp hp rv alo aup tl vloEx vupEx r h v w vlo vup clock : ℝ) :
    SetM (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
    requires 0 < alo ∧ 0 < aup ∧ 0 ≤ tl ∧ Sense w ∧ (clock ≤ tl ∨ tl < 0) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx
    ensures (r, h, v, w, vlo, vup, clock) => Sense w ∧ (clock ≤ tl ∨ tl < 0) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx
    := do
  let mut (r, h, v, w, vlo, vup, clock) := (r, h, v, w, vlo, vup, clock)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ 0 ≤ tl ∧ Sense w ∧
        (clock ≤ tl ∨ tl < 0) ∧
        CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx do
    vlo ← choose ℝ
    vup ← choose ℝ
    w ← sense
    ensure (CimplSafeable rp hp rv alo aup tl 0 r h v w vlo vloEx vup vupEx)
    clock := 0
    let m ← choose Nat
    for _ in [:m]
        invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ 0 ≤ tl ∧ Sense w ∧
          (clock ≤ tl ∨ tl < 0) ∧
          CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx do
      let a ← choose ℝ
      (r, h, v, clock) ← safeableStep rp hp rv alo aup tl vloEx vupEx w vlo vup a r h v clock
  return (r, h, v, w, vlo, vup, clock)

theorem safeable_eq (rp hp rv alo aup tl vloEx vupEx r h v w vlo vup clock : ℝ) :
    safeable rp hp rv alo aup tl vloEx vupEx r h v w vlo vup clock =
      safeable' rp hp rv alo aup tl vloEx vupEx r h v w vlo vup clock := rfl

/-- STTT17 Theorem 5, with the stronger postcondition (+ Sense, clock bound, CimplSafeable).
As above, `t=0` recovers the paper's initial full horizon. The postcondition preserves
the nominal safeable region; it does not assert nonblocking or existence of a next advisory. -/
theorem safeable_safe :
    ∀ rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → Sense w → (t ≤ tl ∨ tl < 0) →
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx →
        ∀ res ∈ SetM.run (safeable rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2.1
          let vup_res := res.2.2.2.2.2.1
          let t_res := res.2.2.2.2.2.2
          NoNMAC rp hp r_res h_res ∧ Sense w_res ∧ (t_res ≤ tl ∨ tl < 0) ∧
            CimplSafeable rp hp rv alo aup tl t_res r_res h_res v_res
              w_res vlo_res vloEx vup_res vupEx := by
  intro rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t hb haup htl hw ht hsafe res hrun
  have ha := hb.2.2.2
  have haup := ha.trans_le haup
  rw [safeable_eq] at hrun
  have hinv := (safeable'.spec rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t).le_wp
    ⟨ha, haup, htl, hw, ht, hsafe⟩ res hrun
  exact ⟨safeable_region_noNMAC rp hp rv alo aup tl _ vloEx vupEx _ _ _ _ _ _
    ha haup hinv.1 hinv.2.1 hinv.2.2, hinv⟩

end ACASX
