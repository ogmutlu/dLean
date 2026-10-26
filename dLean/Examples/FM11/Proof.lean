import dLean.Examples.FM11.Model
import dLean.Tactic.OdeDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# FM11 local and global lane control

Proofs of all four safety statements in `Challenge.lean`, following the
stopping-distance invariant and transitivity arguments in FM11 Appendix A.
Program composition uses intrinsic contracts and inline loop invariants.
The shared model is imported from `Model.lean`; `Challenge.lean` is not imported.
Comparator checks the independent proofs under the same names in namespace `FM11`.
-/

open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true
namespace FM11

theorem behind_refl (b B : ℝ) (x v : Car → ℝ) (i : Car) : Behind b B x v i i := by
  simp [Behind]

/-- The algebraic transitivity used in FM11 Appendix A.2, Lemma 2. -/
theorem behind_trans (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (i j k : Car)
    (hij : Behind b B x v i j) (hjk : Behind b B x v j k) :
    Behind b B x v i k := by
  by_cases heq : i = j
  · simpa [heq] using hjk
  · by_cases heq' : j = k
    · simpa [← heq'] using hij
    · have hstop := div_le_div_of_nonneg_left (sq_nonneg (v j))
        (show 0 < 2 * b by positivity) (show 2 * b ≤ 2 * B by linarith)
      rcases hij.2 heq with ⟨hxij, hsij, hvi, hvj⟩
      grind

/-- A trajectory cannot cross zero if its derivative points strictly inward there. -/
theorem no_cross (T : ℝ) (hT : 0 ≤ T) (f f' : ℝ → ℝ)
    (hd : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (f' t) (Set.Icc 0 T) t)
    (h0 : f 0 < 0) (hin : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t → f' t < 0) : f T < 0 := by
  have hc : ContinuousOn f (Set.Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hc
  by_contra hbad
  have hft : 0 ≤ f t := (not_lt.mp hbad).trans (hm ⟨hT, le_rfl⟩)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
  have hcone : (0 : ℝ) - t ∈ posTangentConeAt (Set.Icc 0 T) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) T).segment_subset ht ⟨le_rfl, hT⟩)
  have hsign := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
    (hd t ht).hasFDerivWithinAt hcone
  have hmul : -t * f' t ≤ 0 := by simpa using hsign
  nlinarith [hin t ht hft]

@[simp] def stoppingMargin (b B : ℝ) (f l : Car) : St × ℝ → ℝ
  | ((x, v, _), _) => 2 * b * B * (x l - x f) + b * v l ^ 2 - B * v f ^ 2

@[simp] def responseMargin (A b B ε : ℝ) (f l : Car) : St × ℝ → ℝ
  | ((x, v, a), t) => stoppingMargin b B f l ((x, v, a), t) -
      B * (A + b) * (A * (ε - t) ^ 2 + 2 * (ε - t) * v f)

theorem stoppingMargin_hasPrime (C : Finset Car) (b B : ℝ) (f l : Car)
    (hf : f ∈ C) (hl : l ∈ C) (D : St × ℝ → Prop) :
    HasPrime (Evolvable.denotation (motion C, time)) D
      (stoppingMargin b B f l)
      (fun ((_, v, a), _) => 2 * b * v l * (B + a l) - 2 * B * v f * (b + a f)) := by
  ode_deriv [stoppingMargin, motion, time]

theorem responseMargin_hasPrime (C : Finset Car) (A b B ε : ℝ) (f l : Car)
    (hf : f ∈ C) (hl : l ∈ C) (D : St × ℝ → Prop) :
    HasPrime (Evolvable.denotation (motion C, time)) D
      (responseMargin A b B ε f l)
      (fun ((_, v, a), t) => 2 * b * v l * (B + a l) +
        2 * B * (A - a f) * (v f + (A + b) * (ε - t))) := by
  ode_deriv [responseMargin, stoppingMargin, motion, time]

/-- Accelerations are constant during each continuous phase. -/
theorem acceleration_preserved (C : Finset Car) (ε value : ℝ) (i : Car) (hi : i ∈ C) :
    (fun ((_, _, a), _) => a i = value)
    [[evolve (motion C, time) (domain ε C)]]
    (fun ((_, _, a), _) => a i = value) := by
  have hinvariant := dIeq (ode := (motion C, time)) (domain := domain ε C)
    (pre := fun ((_, _, a), _) => a i = value)
    (fun ((_, _, a), _) => a i - value) (fun _ => 0)
    (by ode_deriv [motion, time]) (fun _ h => sub_eq_zero.mpr h) (fun _ _ => rfl)
  simpa only [sub_eq_zero] using hinvariant

/-- Braking cannot decrease the stopping-distance margin (Appendix A.1). -/
theorem braking_margin_preserved (C : Finset Car) (ε b B : ℝ)
    (hb : 0 < b) (hB : 0 < B) (f l : Car) (hf : f ∈ C) (hl : l ∈ C) :
    (fun st => 0 < stoppingMargin b B f l st)
    [[evolve (motion C, time)
      (fun st => let ((_, _, a), _) := st; domain ε C st ∧ -B ≤ a l ∧ a f ≤ -b)]]
    (fun st => 0 < stoppingMargin b B f l st) := by
  apply dIgt (stoppingMargin b B f l)
    (fun ((_, v, a), _) => 2 * b * v l * (B + a l) - 2 * B * v f * (b + a f))
  · exact stoppingMargin_hasPrime C b B f l hf hl _
  · exact fun _ h => h
  · intro ((x, v, a), t) h
    have hlead : 0 ≤ 2 * b * v l * (B + a l) :=
      mul_nonneg (mul_nonneg (by positivity) (h.1.1 l hl)) (by linarith [h.2.1])
    have hfollow : 2 * B * v f * (b + a f) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (h.1.1 f hf))
        (by linarith [h.2.2])
    exact sub_nonneg.mpr (hfollow.trans hlead)

/-- The response-time reserve makes every permitted acceleration safe until ε. -/
theorem response_margin_preserved (C : Finset Car) (A b B ε : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (hf : f ∈ C) (hl : l ∈ C) :
    (fun st => 0 < responseMargin A b B ε f l st)
    [[evolve (motion C, time)
      (fun st => let ((_, _, a), _) := st; domain ε C st ∧ -B ≤ a l ∧ a f ≤ A)]]
    (fun st => 0 < responseMargin A b B ε f l st) := by
  apply dIgt (responseMargin A b B ε f l)
    (fun ((_, v, a), t) => 2 * b * v l * (B + a l) +
      2 * B * (A - a f) * (v f + (A + b) * (ε - t)))
  · exact responseMargin_hasPrime C A b B ε f l hf hl _
  · exact fun _ h => h
  · intro ((x, v, a), t) h
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (h.1.1 l hl)) (by linarith [h.2.1]))
      (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h.2.2))
        (add_nonneg (h.1.1 f hf)
          (mul_nonneg (by positivity) (sub_nonneg.mpr h.1.2))))

/-- Positive stopping margin rules out crossing, including at the evolution endpoint. -/
theorem order_preserved (C : Finset Car) (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (f l : Car) (hf : f ∈ C) (hl : l ∈ C) (D : St × ℝ → Prop)
    (hD : ∀ st, D st → let ((_, v, _), _) := st;
      0 ≤ v f ∧ 0 ≤ v l ∧ 0 < stoppingMargin b B f l st) :
    (fun ((x, _, _), _) => x f < x l)
    [[evolve (motion C, time) D]] (fun ((x, _, _), _) => x f < x l) := by
  intro initial hinit
  unfold evolve
  apply Triple.iff.mp (evolveSemantic_spec
    (Q := fun ((x, _, _), _) => x f < x l)
    (Evolvable.denotation (motion C, time)) D initial)
  intro duration hduration path hevo
  have hp : HasPrime (Evolvable.denotation (motion C, time)) D
      (fun ((x, _, _), _) => x f - x l) (fun ((_, v, _), _) => v f - v l) := by
    ode_deriv [motion, time]
  apply sub_neg.mp
  apply no_cross duration hduration _ _ (hp path _ hevo.2.2 hevo.2.1)
  · simpa only [hevo.1, sub_neg] using hinit
  · intro t ht hgap
    rcases hD (path t) (hevo.2.1 t ht) with ⟨hvf, hvl, hmargin⟩
    rcases hstate : path t with ⟨⟨xt, vt, a_t⟩, tt⟩
    simp only [hstate] at hvf hvl hmargin hgap ⊢
    by_contra hbad
    have hsq : vt l ^ 2 ≤ vt f ^ 2 := by
      nlinarith
    change 0 < 2 * b * B * (xt l - xt f) + b * vt l ^ 2 - B * vt f ^ 2 at hmargin
    have hdist := mul_nonneg
      (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hb.le)
        (hb.le.trans hbB)) hgap
    nlinarith [mul_nonneg (sub_nonneg.mpr hbB) (sq_nonneg (vt f)),
      mul_nonneg hb.le (sub_nonneg.mpr hsq)]

theorem stoppingMargin_pos_iff (b B : ℝ) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (st : St × ℝ) :
    0 < stoppingMargin b B f l st ↔
      (let ((x, v, _), _) := st
       x f + v f ^ 2 / (2 * b) < x l + v l ^ 2 / (2 * B)) := by
  rcases st with ⟨⟨x, v, a⟩, t⟩
  have heq : stoppingMargin b B f l ((x, v, a), t) = 2 * b * B *
      (x l + v l ^ 2 / (2 * B) - (x f + v f ^ 2 / (2 * b))) := by
    dsimp [stoppingMargin]
    field_simp
    ring
  rw [heq, mul_pos_iff_of_pos_left (show 0 < 2 * b * B by positivity), sub_pos]

/-- Contract for the leader's nondeterministic acceleration assignment. -/
def l_ctrl' (A B : ℝ) (l : Car) (a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => -B ≤ a_res l ∧ a_res l ≤ A ∧
      ∀ i, i ≠ l → a_res i = a i
    := do
  let al ← choose ℝ
  unless (-B ≤ al ∧ al ≤ A) do abort
  return Function.update a l al

@[spec] theorem choice_spec {α : Type} (p q : SetM α) (Q : α → Prop) :
    ⦃wp p Q estack⟨⟩ ∧ wp q Q estack⟨⟩⦄ p <|> q ⦃Q⦄ := by
  exact ⟨fun h => SetM.wp_orElse p q h.1 h.2⟩

@[reducible] def FollowerChoice (A b B ε : ℝ) (f l : Car)
    (x v : Car → ℝ) (af : ℝ) : Prop :=
  (-B ≤ af ∧ af ≤ -b) ∨
  (Safe_ε A b B ε x v f l ∧ -B ≤ af ∧ af ≤ A) ∨
  (v f = 0 ∧ af = 0)

/-- The three follower choices, with their exact acceleration and frame contract. -/
def f_ctrl' (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => FollowerChoice A b B ε f l x v (a_res f) ∧
      ∀ i, i ≠ f → a_res i = a i
    :=
  (do
    let af ← choose ℝ
    unless (-B ≤ af ∧ af ≤ -b) do abort
    return Function.update a f af)
    <|>
  (do
    unless Safe_ε A b B ε x v f l do abort
    let af ← choose ℝ
    unless (-B ≤ af ∧ af ≤ A) do abort
    return Function.update a f af)
    <|>
  (do
    unless v f = 0 do abort
    return Function.update a f 0)
where finally
  | spec =>
    constructor
    · vcgen
      simp_all
    · vcgen
      constructor
      all_goals vcgen
      all_goals simp_all

theorem acceleration_pair_preserved (C : Finset Car) (ε : ℝ) (f l : Car)
    (hf : f ∈ C) (hl : l ∈ C) (P : ℝ → ℝ → Prop) :
    (fun ((_, _, a), _) => P (a f) (a l))
    [[evolve (motion C, time) (domain ε C)]]
    (fun ((_, _, a), _) => P (a f) (a l)) := by
  rintro ⟨⟨xi, vi, ai⟩, ti⟩ hpre ⟨⟨xf, vf, af⟩, tf⟩ hrun
  have hfrozen := acceleration_preserved C ε (ai f) f hf ((xi, vi, ai), ti) rfl
    ((xf, vf, af), tf) hrun
  have hlfrozen := acceleration_preserved C ε (ai l) l hl ((xi, vi, ai), ti) rfl
    ((xf, vf, af), tf) hrun
  simpa only [hfrozen, hlfrozen] using hpre

theorem behind_of_margin (b B : ℝ) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (st : St × ℝ)
    (horder : let ((x, _, _), _) := st; x f < x l)
    (hmargin : 0 < stoppingMargin b B f l st)
    (hvf : let ((_, v, _), _) := st; 0 ≤ v f)
    (hvl : let ((_, v, _), _) := st; 0 ≤ v l) :
    let ((x, v, _), _) := st; Behind b B x v f l := by
  exact ⟨horder.le, fun _ => ⟨horder,
    (stoppingMargin_pos_iff b B hb hB f l st).mp hmargin, hvf, hvl⟩⟩

/-- A positive stopping margin and the velocity domain establish local safety. -/
theorem behind_preserved_of_margin (C : Finset Car) (b B : ℝ) (hb : 0 < b)
    (hbB : b ≤ B) (f l : Car) (hf : f ∈ C) (hl : l ∈ C)
    (D pre : St × ℝ → Prop)
    (hvel : ∀ st, D st → let ((_, v, _), _) := st; 0 ≤ v f ∧ 0 ≤ v l)
    (hinit : ∀ st, pre st → let ((x, _, _), _) := st; x f < x l)
    (hmargin : pre [[evolve (motion C, time) D]]
      (fun st => 0 < stoppingMargin b B f l st)) :
    pre [[evolve (motion C, time) D]]
      (fun ((x, v, _), _) => Behind b B x v f l) := by
  apply dC (cut := fun st => 0 < stoppingMargin b B f l st)
  · exact hmargin
  · apply dC (cut := fun ((x, _, _), _) => x f < x l)
    · intro initial hpre
      exact order_preserved C b B hb hbB f l hf hl _
        (fun st h => ⟨(hvel st h.1).1, (hvel st h.1).2, h.2⟩)
        initial (hinit initial hpre)
    · apply dW
      intro st h
      exact behind_of_margin b B hb (hb.trans_le hbB) f l st h.2 h.1.2
        (hvel st h.1.1).1 (hvel st h.1.1).2

@[simp] def BrakingPre (b B : ℝ) (f l : Car) (st : St × ℝ) : Prop :=
  let ((x, _, a), _) := st
  0 < stoppingMargin b B f l st ∧ x f < x l ∧ -B ≤ a l ∧ a f ≤ -b

theorem braking_phase_safe (C : Finset Car) (ε b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (f l : Car) (hf : f ∈ C) (hl : l ∈ C) :
    BrakingPre b B f l [[evolve (motion C, time) (domain ε C)]]
      (fun ((x, v, _), _) => Behind b B x v f l) := by
  apply dC (cut := fun ((_, _, a), _) => -B ≤ a l ∧ a f ≤ -b)
  · intro initial hpre
    exact acceleration_pair_preserved C ε f l hf hl
      (fun af al => -B ≤ al ∧ af ≤ -b) initial hpre.2.2
  · apply behind_preserved_of_margin C b B hb hbB f l hf hl _ _
    · exact fun st h => ⟨h.1.1 f hf, h.1.1 l hl⟩
    · exact fun _ h => h.2.1
    · intro initial hpre
      exact braking_margin_preserved C ε b B hb (hb.trans_le hbB) f l hf hl
        initial hpre.1

theorem responseMargin_le_stoppingMargin (C : Finset Car) (A b B ε : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hB : 0 < B) (f l : Car) (hf : f ∈ C)
    (st : St × ℝ) (h : domain ε C st) :
    responseMargin A b B ε f l st ≤ stoppingMargin b B f l st := by
  rcases st with ⟨⟨x, v, a⟩, t⟩
  have hremaining : 0 ≤ ε - t := sub_nonneg.mpr h.2
  have hvf : 0 ≤ v f := h.1 f hf
  have hreserve : 0 ≤ B * (A + b) * (A * (ε - t) ^ 2 + 2 * (ε - t) * v f) := by
    positivity
  exact sub_le_self _ hreserve

@[simp] def ResponsePre (A b B ε : ℝ) (f l : Car) (st : St × ℝ) : Prop :=
  let ((x, _, a), _) := st
  0 < responseMargin A b B ε f l st ∧ x f < x l ∧ -B ≤ a l ∧ a f ≤ A

theorem response_phase_safe (C : Finset Car) (A b B ε : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (f l : Car) (hf : f ∈ C) (hl : l ∈ C) :
    ResponsePre A b B ε f l [[evolve (motion C, time) (domain ε C)]]
      (fun ((x, v, _), _) => Behind b B x v f l) := by
  apply dC (cut := fun ((_, _, a), _) => -B ≤ a l ∧ a f ≤ A)
  · intro initial hpre
    exact acceleration_pair_preserved C ε f l hf hl
      (fun af al => -B ≤ al ∧ af ≤ A) initial hpre.2.2
  · apply behind_preserved_of_margin C b B hb hbB f l hf hl _ _
    · exact fun st h => ⟨h.1.1 f hf, h.1.1 l hl⟩
    · exact fun _ h => h.2.1
    · intro initial hpre final hrun
      have hresponse := response_margin_preserved C A b B ε hA hb (hb.trans_le hbB)
        f l hf hl initial hpre.1 final hrun
      have hdomain := SemanticODE.evolveSemantic_domain_at_end
        (Evolvable.denotation (motion C, time)) _ hrun
      exact hresponse.trans_le
        (responseMargin_le_stoppingMargin C A b B ε hA hb (hb.trans_le hbB) f l hf
          final hdomain.1)

theorem responseMargin_initial_pos_iff (A b B ε : ℝ) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (x v a : Car → ℝ) :
    0 < responseMargin A b B ε f l ((x, v, a), 0) ↔ Safe_ε A b B ε x v f l := by
  have heq : responseMargin A b B ε f l ((x, v, a), 0) = 2 * b * B *
      ((x l + v l ^ 2 / (2 * B)) -
        (x f + v f ^ 2 / (2 * b) + (A / b + 1) * (A / 2 * ε ^ 2 + ε * v f))) := by
    dsimp [responseMargin, stoppingMargin]
    field_simp
    ring
  rw [heq, mul_pos_iff_of_pos_left (show 0 < 2 * b * B by positivity), sub_pos]

@[spec] theorem dyn_local_spec (C : Finset Car) (A b B ε : ℝ) (f l : Car)
    (hf : f ∈ C) (hl : l ∈ C) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ Behind b B x v f l ∧
      -B ≤ a l ∧ FollowerChoice A b B ε f l x v (a f)⦄
    dyn ε C x v a
    ⦃fun (x_res, v_res, _) => Behind b B x_res v_res f l⦄ := by
  constructor
  intro h
  unfold dyn
  vcgen (errorOnMissingSpec := false)
  simp only [SetM.wp_pure, binderNameHint]
  by_cases heq : f = l
  · intro final _
    simp [heq]
  · rcases h with ⟨⟨hA, hb, hbB, hε⟩, hbehind, hal, hchoice⟩
    have hmargin := (stoppingMargin_pos_iff b B hb (hb.trans_le hbB) f l
      ((x, v, a), 0)).mpr (hbehind.2 heq).2.1
    rcases hchoice with hbrake | hsafe | hstop
    · exact braking_phase_safe C ε b B hb hbB f l hf hl ((x, v, a), 0)
        ⟨hmargin, (hbehind.2 heq).1, hal, hbrake.2⟩
    · exact response_phase_safe C A b B ε hA hb hbB f l hf hl ((x, v, a), 0)
        ⟨(responseMargin_initial_pos_iff A b B ε hb (hb.trans_le hbB) f l x v a).mpr
          hsafe.1, (hbehind.2 heq).1, hal, hsafe.2.2⟩
    · exact response_phase_safe C 0 b B ε (by norm_num) hb hbB f l hf hl
        ((x, v, a), 0)
        ⟨by simpa [responseMargin, hstop.1] using hmargin,
          (hbehind.2 heq).1, hal, by simp [hstop.2]⟩

def dyn_llc (_A _b _B ε : ℝ) (f l : Car) (x v a : Car → ℝ) :=
  dyn ε {f, l} x v a

@[spec] theorem dyn_llc_spec (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ Behind b B x v f l ∧
      -B ≤ a l ∧ FollowerChoice A b B ε f l x v (a f)⦄
    dyn_llc A b B ε f l x v a
    ⦃fun (x_res, v_res, _) => Behind b B x_res v_res f l⦄ := by
  exact dyn_local_spec {f, l} A b B ε f l (by simp) (by simp) x v a

def llc' (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM ((Car → ℝ) × (Car → ℝ))
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ Behind b B x v f l
    ensures (x_res, v_res) => Behind b B x_res v_res f l
    := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ Behind b B x v f l do
    a ← l_ctrl' A B l a
    a ← f_ctrl' A b B ε f l x v a
    (x, v, a) ← dyn_llc A b B ε f l x v a
  return (x, v)

theorem llc_eq (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) :
    llc A b B ε f l x v a = llc' A b B ε f l x v a := rfl

/-- FM11 Proposition 1, using the local invariant from Appendix A.1. -/
theorem llc_safe :
    ∀ A b B ε f l x v a,
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → Behind b B x v f l →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          let x_res := res.1
          let v_res := res.2
          Behind b B x_res v_res f l := by
  intro A b B ε f l x v a hp hbehind res hrun
  rw [llc_eq] at hrun
  exact (llc'.spec A b B ε f l x v a).le_wp ⟨hp, hbehind⟩ res hrun

theorem laneSafe_pairwise (C : Finset Car) (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (hsafe : LaneSafe C b B x v) :
    ∀ i ∈ C, ∀ l ∈ C, x i ≤ x l → Behind b B x v i l := by
  classical
  intro i
  induction i using
      (measure (fun i : Car => (C.filter (fun k => x i < x k)).card)).wf.induction with
  | h i ih =>
    intro hi l hl hil
    by_cases heq : i = l
    · simpa [heq] using behind_refl b B x v l
    · have hil' : x i < x l := lt_of_le_of_ne hil (hsafe.2.1 i hi l hl heq)
      obtain ⟨j, hj, hmin⟩ := (C.filter (fun k => x i < x k)).exists_min_image x
        ⟨l, Finset.mem_filter.mpr ⟨hl, hil'⟩⟩
      simp only [Finset.mem_filter] at hj hmin
      have hleader : L C x i j := by
        apply And.intro hi
        apply And.intro hj.1
        apply And.intro hj.2
        intro k hk hneq
        by_cases hki : x k < x i
        · exact Or.inl hki
        · have hik : x i < x k := lt_of_le_of_ne (le_of_not_gt hki)
            (hsafe.2.1 i hi k hk hneq.1.symm)
          exact Or.inr (lt_of_le_of_ne (hmin k ⟨hk, hik⟩)
            (hsafe.2.1 j hj.1 k hk hneq.2.symm))
      have hsub : C.filter (fun k => x j < x k) ⊆ C.filter (fun k => x i < x k) := by
        intro k hk
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hk).1, hj.2.trans (Finset.mem_filter.mp hk).2⟩
      have hrank : (C.filter (fun k => x j < x k)).card <
          (C.filter (fun k => x i < x k)).card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
          ⟨j, Finset.mem_filter.mpr hj, by simp⟩)
      exact behind_trans b B hb hbB x v i j l (hsafe.2.2 i hi j hj.1 hleader)
        (ih j hrank hj.1 l hl (hmin l ⟨hl, hil'⟩))

def leaders' (C : Finset Car) (x : Car → ℝ) (i : Car) : SetM Car
    requires i ∈ C
    ensures k => k ∈ C ∧ x i ≤ x k
    := do
  let mut k := i
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => k ∈ C ∧ x i ≤ x k do
    let l ← chooseS {l | L C x k l}
    k := l
  return k
where finally
  | spec => all_goals simp_all [SetM.run]; all_goals grind

theorem laneSafe_star (C : Finset Car) (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (hsafe : LaneSafe C b B x v) :
    ∀ i ∈ C, BehindLStar C b B x v i := by
  intro i hi k hk
  have hpath := (leaders'.spec C x i).le_wp hi k hk
  exact laneSafe_pairwise C b B hb hbB x v hsafe i hi k hpath.1 hpath.2

theorem safe_ahead (C : Finset Car) (A b B ε : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (hsafe : LaneSafe C b B x v) (f k l : Car)
    (hk : L C x f k) (hl : l ∈ C) (hfl : x f < x l)
    (hguard : Safe_ε A b B ε x v f k) : Safe_ε A b B ε x v f l := by
  have hkl : x k ≤ x l := by grind
  have hbehind := laneSafe_pairwise C b B hb hbB x v hsafe k hk.2.1 l hl hkl
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (v k))
    (show 0 < 2 * b by positivity) (show 2 * b ≤ 2 * B by linarith)
  by_cases heq : k = l
  · simpa [heq] using hguard
  · have hstop := (hbehind.2 heq).2.1
    dsimp [Safe_ε] at *
    linarith

@[reducible] def CarChoice (A b B ε : ℝ) (C : Finset Car) (i : Car)
    (x v : Car → ℝ) (ai : ℝ) : Prop :=
  (-B ≤ ai ∧ ai ≤ -b) ∨
  (∃ l ∈ C, L C x i l ∧ Safe_ε A b B ε x v i l ∧ -B ≤ ai ∧ ai ≤ A) ∨
  (v i = 0 ∧ ai = 0)

def ctrl_i' (A b B ε : ℝ) (C : Finset Car) (i : Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => CarChoice A b B ε C i x v (a_res i)
    :=
  (do
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ -b) do abort
    return Function.update a i ai)
    <|>
  (do
    let l ← chooseS {l | L C x i l}
    unless Safe_ε A b B ε x v i l do abort
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ A) do abort
    return Function.update a i ai)
    <|>
  (do
    unless v i = 0 do abort
    return Function.update a i 0)
where finally
  | spec =>
    constructor
    · vcgen
      simp_all
    · vcgen
      constructor
      all_goals vcgen
      all_goals simp_all [SetM.run]
      all_goals grind

theorem ctrl_i_eq (A b B ε : ℝ) (C : Finset Car) (i : Car) (x v a : Car → ℝ) :
    ctrl_i A b B ε C i x v a = ctrl_i' A b B ε C i x v a := rfl

theorem carChoice_bounds (A b B ε : ℝ) (C : Finset Car) (i : Car)
    (x v : Car → ℝ) (ai : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (hchoice : CarChoice A b B ε C i x v ai) : -B ≤ ai ∧ ai ≤ A := by
  grind

theorem carChoice_follower (A b B ε : ℝ) (C : Finset Car) (f l : Car)
    (x v : Car → ℝ) (af : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (hsafe : LaneSafe C b B x v) (hl : l ∈ C) (hfl : x f < x l)
    (hchoice : CarChoice A b B ε C f x v af) : FollowerChoice A b B ε f l x v af := by
  rcases hchoice with hbrake | ⟨k, hk, hleader, hguard, hbounds⟩ | hstop
  · exact Or.inl hbrake
  · exact Or.inr (Or.inl
      ⟨safe_ahead C A b B ε hb hbB x v hsafe f k l hleader hl hfl hguard, hbounds⟩)
  · exact Or.inr (Or.inr hstop)

def ctrl_n' (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => ∀ i ∈ C, CarChoice A b B ε C i x v (a_res i)
    := do
  let mut a_res := a
  for i in C.toList
      invariant pref _suff => ∀ j ∈ pref, CarChoice A b B ε C j x v (a_res j) do
    let ai ← ctrl_i' A b B ε C i x v a
    a_res := Function.update a_res i (ai i)
  return a_res
where finally
  | spec => all_goals simp_all

theorem dyn_nonnegative (C : Finset Car) (ε : ℝ) (x v a : Car → ℝ) :
    ⦃True⦄ dyn ε C x v a ⦃fun (_, v_res, _) => ∀ i ∈ C, 0 ≤ v_res i⦄ := by
  constructor
  intro _
  unfold dyn
  vcgen (errorOnMissingSpec := false)
  simp only [SetM.wp_pure, binderNameHint]
  apply dW (pre := fun _ => True)
  · intro st h
    exact h.1
  · trivial

theorem dyn_laneSafe (active C : Finset Car) (hsub : C ⊆ active)
    (A b B ε : ℝ) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v ∧
      (∀ i ∈ C, CarChoice A b B ε C i x v (a i))⦄
    dyn ε active x v a
    ⦃fun (x_res, v_res, _) => LaneSafe C b B x_res v_res⦄ := by
  apply Triple.iff.mpr
  rintro ⟨hp, hsafe, hchoice⟩ ⟨xr, vr, ar⟩ hrun
  rcases hp with ⟨hA, hb, hbB, hε⟩
  have hpairs : ∀ i ∈ C, ∀ j ∈ C, x i < x j → Behind b B xr vr i j := by
    intro i hi j hj hij
    exact (dyn_local_spec active A b B ε i j (hsub hi) (hsub hj) x v a).le_wp
      ⟨⟨hA, hb, hbB, hε⟩, laneSafe_pairwise C b B hb hbB x v hsafe i hi j hj hij.le,
        (carChoice_bounds A b B ε C j x v (a j) hA hb hbB (hchoice j hj)).1,
        carChoice_follower A b B ε C i j x v (a i) hb hbB hsafe hj hij
          (hchoice i hi)⟩ (xr, vr, ar) hrun
  have hordered : ∀ i ∈ C, ∀ j ∈ C, i ≠ j →
      Behind b B xr vr i j ∨ Behind b B xr vr j i := by
    intro i hi j hj hneq
    rcases lt_or_gt_of_ne (hsafe.2.1 i hi j hj hneq) with hij | hji
    · exact Or.inl (hpairs i hi j hj hij)
    · exact Or.inr (hpairs j hj i hi hji)
  apply And.intro (fun i hi =>
    (dyn_nonnegative active ε x v a).le_wp trivial (xr, vr, ar) hrun i (hsub hi))
  apply And.intro
  · intro i hi j hj hneq
    rcases hordered i hi j hj hneq with hij | hji
    · exact ne_of_lt (hij.2 hneq).1
    · exact ne_of_gt (hji.2 hneq.symm).1
  · intro i hi j hj hleader
    have hneq : i ≠ j := by grind
    rcases hordered i hi j hj hneq with hij | hji
    · exact hij
    · have hji' := (hji.2 hneq.symm).1
      grind

def dyn_glc (_A _b _B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) := dyn ε C x v a

@[spec] theorem dyn_glc_spec (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v ∧
      (∀ i ∈ C, CarChoice A b B ε C i x v (a i))⦄
    dyn_glc A b B ε C x v a
    ⦃fun (x_res, v_res, _) => LaneSafe C b B x_res v_res⦄ :=
  dyn_laneSafe C C (fun _ hi => hi) A b B ε x v a

def glc' (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) :
    SetM ((Car → ℝ) × (Car → ℝ))
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v
    ensures (x_res, v_res) => LaneSafe C b B x_res v_res
    := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v do
    a ← ctrl_n' A b B ε C x v a
    (x, v, a) ← dyn_glc A b B ε C x v a
  return (x, v)

theorem glc_eq (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) :
    glc A b B ε C x v a = glc' A b B ε C x v a := rfl

/-- FM11 Proposition 2: local safety lifts through the finite leader chain. -/
theorem glc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (glc A b B ε C x v a),
        let x_res := res.1
        let v_res := res.2
        LaneSafe C b B x_res v_res ∧
        (∀ i ∈ C, BehindLStar C b B x_res v_res i) := by
  intro A b B ε x v a C hp hsafe ⟨xr, vr⟩ hrun
  rw [glc_eq] at hrun
  have hfinal := (glc'.spec A b B ε C x v a).le_wp ⟨hp, hsafe⟩ (xr, vr) hrun
  exact ⟨hfinal, laneSafe_star C b B hp.2.1 hp.2.2.1 xr vr hfinal⟩

theorem laneSafe_subset (C D : Finset Car) (hsub : D ⊆ C) (b B : ℝ)
    (hb : 0 < b) (hbB : b ≤ B) (x v : Car → ℝ) (hsafe : LaneSafe C b B x v) :
    LaneSafe D b B x v := by
  apply And.intro (fun i hi => hsafe.1 i (hsub hi))
  apply And.intro
  · exact fun i hi j hj hneq => hsafe.2.1 i (hsub hi) j (hsub hj) hneq
  · intro i hi j hj hleader
    exact laneSafe_pairwise C b B hb hbB x v hsafe i (hsub hi) j (hsub hj)
      hleader.2.2.1.le

theorem laneSafe_insert (C : Finset Car) (n : Car) (b B : ℝ)
    (hb : 0 < b) (hbB : b ≤ B) (x v : Car → ℝ) (hsafe : LaneSafe C b B x v)
    (hv : 0 ≤ v n) (hx : ∀ j ∈ C, x n ≠ x j)
    (hfollow : FBehind (insert n C) b B x v n)
    (hlead : BehindL (insert n C) b B x v n) : LaneSafe (insert n C) b B x v := by
  have hpairs := laneSafe_pairwise C b B hb hbB x v hsafe
  apply And.intro
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hv
    · exact hsafe.1 i hi
  apply And.intro
  · intro i hi j hj hneq
    simp only [Finset.mem_insert] at hi hj
    grind
  · intro i hi j hj hleader
    by_cases hin : i = n
    · subst i
      exact hlead j hj hleader
    by_cases hjn : j = n
    · subst j
      exact hfollow i hi hleader
    exact hpairs i (Finset.mem_of_mem_insert_of_ne hi hin)
      j (Finset.mem_of_mem_insert_of_ne hj hjn) hleader.2.2.1.le

def delete' (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) : SetM (Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ LaneSafe C b B x v
    ensures D => LaneSafe D b B x v
    := do
  let n ← chooseS {n | n ∈ C}
  return C.erase n
where finally
  | spec =>
    apply laneSafe_subset C _ (Finset.erase_subset _ _) b B
    all_goals tauto

def new' (C : Finset Car) : SetM (Car × Finset Car)
    requires True
    ensures (n, D) => n ∉ C ∧ D = insert n C
    := do
  let n ← chooseS {n | n ∉ C}
  return (n, insert n C)
where finally
  | spec => exact ‹_ ∈ SetM.run _›

def create' (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) : SetM (Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ LaneSafe C b B x v
    ensures D => LaneSafe D b B x v
    := do
  let (n, C_new) ← new' C
  unless (0 ≤ v n ∧ ∀ j ∈ C, x n ≠ x j) do abort
  unless FBehind C_new b B x v n do abort
  unless BehindL C_new b B x v n do abort
  return C_new
where finally
  | spec =>
    simp only at *
    rcases ‹_ ∉ C ∧ _ = insert _ C› with ⟨_, rfl⟩
    apply laneSafe_insert
    all_goals tauto

def lhc' (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) :
    SetM (Finset Car × (Car → ℝ) × (Car → ℝ))
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v
    ensures (C_res, x_res, v_res) => LaneSafe C_res b B x_res v_res
    := do
  let mut (x, v, a) := (x, v, a)
  let mut C := C
  let i ← choose ℕ
  for _ in [:i]
      invariant _pref _suff =>
        (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v do
    let j ← choose ℕ
    for _ in [:j]
        invariant _pref _suff =>
          (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v do
      C ← delete' C b B x v
    let j' ← choose ℕ
    for _ in [:j']
        invariant _pref _suff =>
          (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe C b B x v do
      C ← create' C b B x v
    a ← ctrl_n' A b B ε C x v a
    (x, v, a) ← dyn_glc A b B ε C x v a
  return (C, x, v)

theorem lhc_eq (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) :
    lhc A b B ε C x v a = lhc' A b B ε C x v a := rfl

/-- FM11 Proposition 3, including the current population after creation and deletion. -/
theorem lhc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε C x v a),
        let C_res := res.1
        let x_res := res.2.1
        let v_res := res.2.2
        LaneSafe C_res b B x_res v_res ∧
        (∀ i ∈ C_res, BehindLStar C_res b B x_res v_res i) := by
  intro A b B ε x v a C hp hsafe ⟨Cr, xr, vr⟩ hrun
  rw [lhc_eq] at hrun
  have hfinal := (lhc'.spec A b B ε C x v a).le_wp ⟨hp, hsafe⟩ (Cr, xr, vr) hrun
  exact ⟨hfinal, laneSafe_star Cr b B hp.2.1 hp.2.2.1 xr vr hfinal⟩

def delete_l' (lanes : Finset Lane) (C : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (C l) b B x v
    ensures D => ∀ l ∈ lanes, LaneSafe (D l) b B x v
    := do
  let mut C := C
  for l in lanes.toList
      invariant _pref _suff =>
        (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (C l) b B x v do
    let j ← choose ℕ
    for _ in [:j]
        invariant _pref _suff =>
          (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (C l) b B x v do
      let cars ← delete' (C l) b B x v
      C := Function.update C l cars
  return C
where finally
  | spec =>
    all_goals simp_all
    have hl : l ∈ lanes := Finset.mem_toList.mp (by rw [‹lanes.toList = _›]; simp)
    grind

def create_l' (lanes : Finset Lane) (C : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (C l) b B x v
    ensures D => ∀ l ∈ lanes, LaneSafe (D l) b B x v
    := do
  let mut C := C
  for l in lanes.toList
      invariant _pref _suff =>
        (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (C l) b B x v do
    let j ← choose ℕ
    for _ in [:j]
        invariant _pref _suff =>
          (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (C l) b B x v do
      let cars ← create' (C l) b B x v
      C := Function.update C l cars
  return C
where finally
  | spec =>
    all_goals simp_all
    have hl : l ∈ lanes := Finset.mem_toList.mp (by rw [‹lanes.toList = _›]; simp)
    grind

theorem ctrl_i_choice (A b B ε : ℝ) (C : Finset Car) (i : Car)
    (x v a : Car → ℝ) (ai : ℝ)
    (hrun : Function.update a i ai ∈ SetM.run (ctrl_i A b B ε C i x v a)) :
    CarChoice A b B ε C i x v ai := by
  rw [ctrl_i_eq] at hrun
  simpa using (ctrl_i'.spec A b B ε C i x v a).le_wp trivial _ hrun

def ctrl_n_l' (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => ∀ i ∈ lanes.biUnion C, ∀ l ∈ lanes,
      i ∈ C l → CarChoice A b B ε (C l) i x v (a_res i)
    := do
  let mut a_res := a
  for i in (lanes.biUnion C).toList
      invariant pref _suff => ∀ i ∈ pref, ∀ l ∈ lanes,
        i ∈ C l → CarChoice A b B ε (C l) i x v (a_res i) do
    let ai ← choose ℝ
    for l in lanes.toList
        invariant pref _suff => ∀ l ∈ pref,
          i ∈ C l → CarChoice A b B ε (C l) i x v ai do
      if i ∈ C l then
        let a_new := Function.update a i ai
        ensure (a_new ∈ SetM.run (ctrl_i A b B ε (C l) i x v a))
    a_res := Function.update a_res i ai
  return a_res
where finally
  | spec =>
    all_goals simp_all
    all_goals try
      have hchoice := ctrl_i_choice A b B ε (C l) i x v a ai
        ‹Function.update a i ai ∈ SetM.run (ctrl_i A b B ε (C l) i x v a)›
    all_goals grind [Function.update_apply]

def dyn_ghc (_A _b _B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) := dyn ε (lanes.biUnion C) x v a

@[spec] theorem dyn_ghc_spec (A b B ε : ℝ) (lanes : Finset Lane)
    (C : Lane → Finset Car) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧
      (∀ l ∈ lanes, LaneSafe (C l) b B x v) ∧
      (∀ i ∈ lanes.biUnion C, ∀ l ∈ lanes,
        i ∈ C l → CarChoice A b B ε (C l) i x v (a i))⦄
    dyn_ghc A b B ε lanes C x v a
    ⦃fun (x_res, v_res, _) => ∀ l ∈ lanes, LaneSafe (C l) b B x_res v_res⦄ := by
  apply Triple.iff.mpr
  rintro ⟨hp, hsafe, hchoice⟩ ⟨xr, vr, ar⟩ hrun l hl
  have hsub : C l ⊆ lanes.biUnion C := fun _ hi => Finset.mem_biUnion.mpr ⟨l, hl, hi⟩
  exact (dyn_laneSafe _ (C l) hsub A b B ε x v a).le_wp
    ⟨hp, hsafe l hl, fun i hi => hchoice i (hsub hi) l hl hi⟩ (xr, vr, ar) hrun

def ghc' (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM ((Lane → Finset Car) × (Car → ℝ) × (Car → ℝ))
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧
      ∀ l ∈ lanes, LaneSafe (C l) b B x v
    ensures (C_res, x_res, v_res) => ∀ l ∈ lanes, LaneSafe (C_res l) b B x_res v_res
    := do
  let mut (x, v, a) := (x, v, a)
  let mut C := C
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧
        ∀ l ∈ lanes, LaneSafe (C l) b B x v do
    C ← delete_l' lanes C b B x v
    C ← create_l' lanes C b B x v
    a ← ctrl_n_l' A b B ε lanes C x v a
    (x, v, a) ← dyn_ghc A b B ε lanes C x v a
  return (C, x, v)

theorem ghc_eq (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) : ghc A b B ε lanes C x v a = ghc' A b B ε lanes C x v a := rfl

/-- FM11 Theorem 1: lane-wise safety under population changes and shared dynamics. -/
theorem ghc_safe :
    ∀ A b B ε x v a (lanes : Finset Lane) (C : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (C l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes C x v a),
          let C_res := res.1
          let x_res := res.2.1
          let v_res := res.2.2
          ∀ l ∈ lanes, LaneSafe (C_res l) b B x_res v_res ∧
          (∀ i ∈ C_res l, BehindLStar (C_res l) b B x_res v_res i) := by
  intro A b B ε x v a lanes C hp hsafe ⟨Cr, xr, vr⟩ hrun
  rw [ghc_eq] at hrun
  have hfinal := (ghc'.spec A b B ε lanes C x v a).le_wp ⟨hp, hsafe⟩ (Cr, xr, vr) hrun
  dsimp only
  intro l hl
  exact ⟨hfinal l hl, laneSafe_star (Cr l) b B hp.2.1 hp.2.2.1 xr vr (hfinal l hl)⟩

end FM11
