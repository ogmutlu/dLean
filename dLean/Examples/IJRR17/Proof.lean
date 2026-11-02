import dLean.Examples.IJRR17.Model
import dLean.Tactic.OdeDeriv

/-!
# IJRR17: safety and liveness following `robix.kyx`

Independent proofs of journal Theorems 1--9, 11, and 12. Theorem 10 is audited
separately in `Theorem10.lean`: its exact statement has a checked counterexample,
and a version with explicit initial obstacle-velocity bounds is proved there.
The shared model and challenge statements are unchanged, and no admitted
challenge theorem is imported.

The safety proofs use the archive's stopping-distance, friendly-margin,
orientation, remaining-reaction-time, waypoint, and intersection invariants.
Signed differential margins combine its exact-speed and displacement cuts.
Intrinsic contracts and `vcgen` compose the controllers and loops. The diamond
claims use explicit trajectories and successful finite runs: obstacle braking,
waypoint acceleration and coasting, and waiting before crossing an intersection.
-/

open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace IJRR17

@[spec] theorem choice_spec {α : Type} (p q : SetM α) (Q : α → Prop) :
    ⦃wp p Q estack⟨⟩ ∧ wp q Q estack⟨⟩⦄ p <|> q ⦃Q⦄ :=
  ⟨fun h => SetM.wp_orElse p q h.1 h.2⟩

@[reducible]
def StaticInv (b : ℝ) (p d o : Vec2) (s : ℝ) : Prop :=
  0 ≤ s ∧ UnitDirection d ∧ stopDist b s < infNorm (p - o)

@[reducible]
def StaticReady (A b ε : ℝ) (p d o : Vec2) (s a : ℝ) : Prop :=
  (a = -b ∧ StaticInv b p d o s) ∨
  (s = 0 ∧ a = 0 ∧ StaticInv b p d o s) ∨
  (a = A ∧ 0 ≤ s ∧ UnitDirection d ∧ Safe A b 0 ε p o s)

theorem static_initial (b : ℝ) (p d o : Vec2) (s : ℝ) :
    Initial p d o s → StaticInv b p d o s := by
  rintro ⟨rfl, hsep, hd⟩
  apply And.intro le_rfl (And.intro hd ?_)
  simp only [stopDist, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
  by_contra h
  have hmax := le_of_not_gt h
  have hzero := (max_le_iff.mp hmax)
  dsimp [infNorm] at hzero
  have hx := abs_nonpos_iff.mp hzero.1
  have hy := abs_nonpos_iff.mp hzero.2
  simp [distanceSq, hx, hy] at hsep

theorem static_separated (b : ℝ) (hb : 0 < b) (p d o : Vec2) (s : ℝ) :
    StaticInv b p d o s → 0 < distanceSq p o := by
  rintro ⟨hs, hd, hclear⟩
  have hnorm : 0 < infNorm (p - o) :=
    lt_of_le_of_lt (div_nonneg (sq_nonneg s) (by positivity)) hclear
  by_contra h
  have hx : p 0 - o 0 = 0 := by
    dsimp [distanceSq] at h
    nlinarith [sq_nonneg (p 1 - o 1), sq_nonneg (p 0 - o 0)]
  have hy : p 1 - o 1 = 0 := by
    dsimp [distanceSq] at h
    nlinarith [sq_nonneg (p 0 - o 0), sq_nonneg (p 1 - o 1)]
  simp [infNorm, hx, hy] at hnorm

noncomputable def staticControl (A b Ω ε : ℝ) (p _d o : Vec2) (s sMeasured ω r : ℝ) :=
  ctrl_r b Ω (pure A) (fun p o s _ => Safe A b 0 ε p o s) p o s sMeasured ω r

noncomputable def staticDyn (_A _b ε a r : ℝ) (v p d o : Vec2) (s ω : ℝ) :=
  dyn ε a r v p d o s ω

@[spec] theorem ctrl_r_static_spec (A b Ω ε : ℝ) (p d o : Vec2) (s sMeasured ω r : ℝ) :
    ⦃sMeasured = s ∧ StaticInv b p d o s⦄
      staticControl A b Ω ε p d o s sMeasured ω r
    ⦃fun (a, _ω, _r, o) => StaticReady A b ε p d o s a⦄ := by
  unfold staticControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

noncomputable def directionEnergy : (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ → ℝ :=
  fun ((_p, d, _o, _s, _ω), _t) => d 0 ^ 2 + d 1 ^ 2 - 1

noncomputable def signedBrake (b σ : ℝ) (i : Fin 2) :
    (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ → ℝ :=
  fun ((p, _d, o, s, _ω), _t) => σ * (p i - o i) - stopDist b s

noncomputable def signedResponse (A b ε σ : ℝ) (i : Fin 2) :
    (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ → ℝ :=
  fun ((p, d, o, s, ω), t) => signedBrake b σ i ((p, d, o, s, ω), t) -
    (A / b + 1) * (A / 2 * (ε - t) ^ 2 + (ε - t) * s)

theorem directionEnergy_hasPrime (a r : ℝ) (D) :
    HasPrime (Evolvable.denotation (motion a r 0, time)) D directionEnergy (fun _ => 0) := by
  ode_deriv [directionEnergy, motion, time, perp]

theorem signedBrake_hasPrime (a b r σ : ℝ) (i : Fin 2) (D) :
    HasPrime (Evolvable.denotation (motion a r 0, time)) D (signedBrake b σ i)
      (fun ((_p, d, _o, s, _ω), _t) => s * (σ * d i - a / b)) := by
  ode_deriv [signedBrake, stopDist, motion, time]

theorem signedResponse_hasPrime (A b ε r σ : ℝ) (i : Fin 2) (D) :
    HasPrime (Evolvable.denotation (motion A r 0, time)) D (signedResponse A b ε σ i)
      (fun ((_p, d, _o, s, _ω), _t) => s * (σ * d i + 1)) := by
  ode_deriv [signedResponse, signedBrake, stopDist, motion, time]

theorem unit_preserved (a r ε : ℝ) :
    (fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d)
    [[evolve (motion a r 0, time) (domain ε)]]
    (fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d) := by
  simpa only [directionEnergy, sub_eq_zero, UnitDirection] using
    (dIeq (ode := (motion a r 0, time)) (domain := domain ε)
      (pre := fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d)
      directionEnergy (fun _ => 0) (directionEnergy_hasPrime a r _)
      (fun _ h => sub_eq_zero.mpr h) (fun _ _ => rfl))

theorem signed_direction_nonneg (σ : ℝ) (i : Fin 2) (d : Vec2)
    (hσ : σ = 1 ∨ σ = -1) (hd : UnitDirection d) : 0 ≤ σ * d i + 1 := by
  fin_cases i <;> rcases hσ with rfl | rfl <;>
    dsimp [UnitDirection] at hd ⊢ <;> nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

theorem response_signed (b ε a r σ : ℝ) (i : Fin 2) (hb : 0 < b)
    (ha : a = -b ∨ 0 ≤ a) (hσ : σ = 1 ∨ σ = -1) :
    (fun ((p, d, o, s, _ω), t) =>
      t = 0 ∧ UnitDirection d ∧ stoppingMargin a b 0 ε s < σ * (p i - o i))
    [[evolve (motion a r 0, time) (domain ε)]]
    (fun ((p, d, o, s, _ω), _t) =>
      0 ≤ s ∧ UnitDirection d ∧ stopDist b s < σ * (p i - o i)) := by
  apply dC (cut := fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d)
  · exact fun st h => unit_preserved a r ε st h.2.1
  · rintro ⟨⟨p₀, d₀, o₀, s₀, ω₀⟩, t₀⟩ ⟨rfl, hunit, hmargin⟩
      ⟨⟨p, d, o, s, ω⟩, t⟩ hrun
    have hstart : 0 < signedResponse a b ε σ i ((p₀, d₀, o₀, s₀, ω₀), 0) := by
      dsimp [signedResponse, signedBrake, stoppingMargin, stopDist] at hmargin ⊢
      simp only [zero_mul, zero_div, add_zero, sub_zero] at hmargin ⊢
      linarith
    have hend := dIgt (ode := (motion a r 0, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
      (pre := fun st => 0 < signedResponse a b ε σ i st)
      (signedResponse a b ε σ i) (fun ((_p, d, _o, s, _ω), _t) => s * (σ * d i + 1))
      (signedResponse_hasPrime a b ε r σ i _)
      (fun _ h => h)
      (fun st h => mul_nonneg h.1.2 (signed_direction_nonneg σ i st.1.2.1 hσ h.2))
      ((p₀, d₀, o₀, s₀, ω₀), 0) hstart ((p, d, o, s, ω), t) hrun
    have hdom : domain ε ((p, d, o, s, ω), t) ∧ UnitDirection d :=
      dW (ode := (motion a r 0, time))
        (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
        (pre := fun _ => True) (fun _ h => h)
        ((p₀, d₀, o₀, s₀, ω₀), 0) trivial ((p, d, o, s, ω), t) hrun
    have hreserve : 0 ≤ (a / b + 1) * (a / 2 * (ε - t) ^ 2 + (ε - t) * s) :=
      ha.elim (fun heq => by simp [heq, hb.ne'])
        (fun ha => mul_nonneg (add_nonneg (div_nonneg ha hb.le) (by norm_num))
          (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
            (mul_nonneg (sub_nonneg.mpr hdom.1.1) hdom.1.2)))
    exact ⟨hdom.1.2, hdom.2, by dsimp [signedResponse, signedBrake] at hend; linarith⟩

theorem signed_witness (c : ℝ) (q : Vec2) (h : c < infNorm q) :
    ∃ i : Fin 2, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ c < σ * q i := by
  simpa only [Fin.exists_fin_two, or_and_right, exists_or, exists_eq_left,
    one_mul, neg_one_mul, ← lt_max_iff, infNorm, abs_eq_max_neg] using h

theorem signed_le_infNorm (q : Vec2) (i : Fin 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    σ * q i ≤ infNorm q := by
  have hi : |q i| ≤ infNorm q := by fin_cases i <;> simp [infNorm]
  rcases hσ with rfl | rfl
  · simpa using (le_abs_self (q i)).trans hi
  · simpa using (neg_le_abs (q i)).trans hi

theorem response_clearance (b ε a r : ℝ) (hb : 0 < b) (ha : a = -b ∨ 0 ≤ a)
    (p d o : Vec2) (s ω : ℝ) (hd : UnitDirection d)
    (hsafe : Safe a b 0 ε p o s) :
    ∀ res ∈ SetM.run (evolve (motion a r 0, time) (domain ε) ((p, d, o, s, ω), 0)),
      let ((pr, dr, or_, sr, _ω), _t) := res
      StaticInv b pr dr or_ sr := by
  obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stoppingMargin a b 0 ε s) (p - o) hsafe
  rintro ⟨⟨pr, dr, or_, sr, ωr⟩, t⟩ hrun
  have h := response_signed b ε a r σ i hb ha hσ ((p, d, o, s, ω), 0)
    ⟨rfl, hd, by simpa using hmargin⟩ ((pr, dr, or_, sr, ωr), t) hrun
  exact ⟨h.1, h.2.1, h.2.2.trans_le (by simpa using signed_le_infNorm (pr - or_) i σ hσ)⟩

@[spec] theorem dyn_static_spec (A b ε a r : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (v p d o : Vec2) (s ω : ℝ) :
    ⦃v = 0 ∧ StaticReady A b ε p d o s a⦄ staticDyn A b ε a r v p d o s ω
    ⦃fun (p, d, o, s, _ω) => StaticInv b p d o s⦄ := by
  unfold staticDyn dyn
  vcgen (errorOnMissingSpec := false)
  rename_i hpre
  simp only [SetM.wp_pure, binderNameHint]
  rcases hpre with ⟨rfl, hready⟩
  rcases hready with ⟨rfl, hs, hd, hclear⟩ | ⟨rfl, rfl, hs, hd, hclear⟩ |
    ⟨rfl, hs, hd, hsafe⟩
  · exact response_clearance b ε (-b) r hb (.inl rfl) p d o s ω hd
      (by simpa [Safe, stoppingMargin, hb.ne'] using hclear)
  · exact response_clearance b ε 0 r hb (.inr le_rfl) p d o 0 ω hd
      (by simpa [Safe, stoppingMargin, stopDist] using hclear)
  · exact response_clearance b ε a r hb (.inr hA) p d o s ω hd hsafe

noncomputable def dwss' (A b Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (p d o : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires StaticInv b p d o s
    ensures (p, d, o, s, _ω, _r, _v) => StaticInv b p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, (0 : Vec2))
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => StaticInv b p d o s do
    let (pMeasured, sMeasured) ← pure (p, s)
    v ← pure 0
    let (a, ω_new, r_new, o_new) ← staticControl A b Ω ε pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← pure a
    (p, d, o, s, ω) ← staticDyn A b ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

theorem dwss_eq (A b Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (p d o : Vec2) (s ω r : ℝ) :
    dwss A b Ω ε p d o s ω r = dwss' A b Ω ε hA hb p d o s ω r := by
  rfl

/-- Journal Theorem 1 / archive "Theorem 1: Static safety". -/
theorem dwss_safe :
    ∀ A b Ω ε p d o s ω r,
      Bounds A b 0 ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwss A b Ω ε p d o s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          0 < distanceSq p_res o_res := by
  intro A b Ω ε p d o s ω r hbounds hinit res hrun
  rw [dwss_eq A b Ω ε hbounds.1 hbounds.2.1] at hrun
  exact static_separated b hbounds.2.1 _ _ _ _
    ((dwss'.spec A b Ω ε hbounds.1 hbounds.2.1 p d o s ω r).le_wp
      (static_initial b p d o s hinit) res hrun)

/-! ## Passive safety: the archive's conditional stopping-distance invariant -/

@[reducible]
def PassiveInv (b V : ℝ) (p d o : Vec2) (s : ℝ) : Prop :=
  0 ≤ s ∧ UnitDirection d ∧
    (0 < s → stopDist b s + V * s / b < infNorm (p - o))

noncomputable def passiveResponse (A b V ε σ : ℝ) (i : Fin 2) :
    (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ → ℝ :=
  fun ((p, _d, o, s, _ω), t) => σ * (p i - o i) - stopDist b s - V * s / b -
    (A / b + 1) * (A / 2 * (ε - t) ^ 2 + (ε - t) * (s + V))

theorem passiveResponse_hasPrime (A b V ε a r σ : ℝ) (hb : b ≠ 0)
    (v : Vec2) (i : Fin 2) (D) :
    HasPrime (Evolvable.denotation (motion a r v, time)) D (passiveResponse A b V ε σ i)
      (fun ((_p, d, _o, s, _ω), t) =>
        s * (σ * d i + 1) + (V - σ * v i) +
          (A - a) / b * (s + V + (A + b) * (ε - t))) := by
  ode_deriv [passiveResponse, stopDist, motion, time]
  field_simp
  ring

theorem motion_unit_preserved (a r ε : ℝ) (v : Vec2) :
    (fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d) := by
  have hderiv : HasPrime (Evolvable.denotation (motion a r v, time)) (domain ε)
      directionEnergy (fun _ => 0) := by
    ode_deriv [directionEnergy, motion, time, perp]
  simpa only [directionEnergy, sub_eq_zero, UnitDirection] using
    (dIeq (ode := (motion a r v, time)) (domain := domain ε)
      (pre := fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d)
      directionEnergy (fun _ => 0) hderiv
      (fun _ h => sub_eq_zero.mpr h) (fun _ _ => rfl))

theorem velocity_component_bound (V σ : ℝ) (v : Vec2) (i : Fin 2)
    (hV : 0 ≤ V) (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2)
    (hσ : σ = 1 ∨ σ = -1) : 0 ≤ V - σ * v i := by
  fin_cases i <;> rcases hσ with rfl | rfl <;>
    dsimp at * <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem passive_response_signed (M b V ε a r σ : ℝ) (v : Vec2) (i : Fin 2)
    (hb : 0 < b) (hV : 0 ≤ V) (hM : M = -b ∨ 0 ≤ M) (ha : a ≤ M)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hσ : σ = 1 ∨ σ = -1) :
    (fun ((p, d, o, s, _ω), t) =>
      t = 0 ∧ UnitDirection d ∧ stoppingMargin M b V ε s < σ * (p i - o i))
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((p, d, o, s, _ω), _t) =>
      0 ≤ s ∧ UnitDirection d ∧ stopDist b s + V * s / b < σ * (p i - o i)) := by
  apply dC (cut := fun ((_p, d, _o, _s, _ω), _t) => UnitDirection d)
  · exact fun st h => motion_unit_preserved a r ε v st h.2.1
  · rintro ⟨⟨p₀, d₀, o₀, s₀, ω₀⟩, t₀⟩ ⟨rfl, hunit, hmargin⟩
      ⟨⟨p, d, o, s, ω⟩, t⟩ hrun
    have hstart : 0 < passiveResponse M b V ε σ i ((p₀, d₀, o₀, s₀, ω₀), 0) := by
      dsimp [passiveResponse, stoppingMargin] at hmargin ⊢
      simp only [sub_zero] at hmargin ⊢
      linarith
    have hMb : 0 ≤ M + b := hM.elim (fun h => by simp [h]) (fun h => by linarith)
    have hend := dIgt (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
      (pre := fun st => 0 < passiveResponse M b V ε σ i st)
      (passiveResponse M b V ε σ i)
      (fun ((_p, d, _o, s, _ω), t) => s * (σ * d i + 1) + (V - σ * v i) +
        (M - a) / b * (s + V + (M + b) * (ε - t)))
      (passiveResponse_hasPrime M b V ε a r σ hb.ne' v i _)
      (fun _ h => h)
      (fun st h => add_nonneg
        (add_nonneg (mul_nonneg h.1.2 (signed_direction_nonneg σ i st.1.2.1 hσ h.2))
          (velocity_component_bound V σ v i hV hv hσ))
        (mul_nonneg (div_nonneg (sub_nonneg.mpr ha) hb.le)
          (add_nonneg (add_nonneg h.1.2 hV)
            (mul_nonneg hMb (sub_nonneg.mpr h.1.1)))))
      ((p₀, d₀, o₀, s₀, ω₀), 0) hstart ((p, d, o, s, ω), t) hrun
    have hdom : domain ε ((p, d, o, s, ω), t) ∧ UnitDirection d :=
      dW (ode := (motion a r v, time))
        (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
        (pre := fun _ => True) (fun _ h => h)
        ((p₀, d₀, o₀, s₀, ω₀), 0) trivial ((p, d, o, s, ω), t) hrun
    have hreserve : 0 ≤ (M / b + 1) * (M / 2 * (ε - t) ^ 2 + (ε - t) * (s + V)) :=
      hM.elim (fun heq => by simp [heq, hb.ne'])
        (fun hM => mul_nonneg (add_nonneg (div_nonneg hM hb.le) (by norm_num))
          (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
            (mul_nonneg (sub_nonneg.mpr hdom.1.1) (add_nonneg hdom.1.2 hV))))
    exact ⟨hdom.1.2, hdom.2, by dsimp [passiveResponse] at hend; linarith⟩

theorem passive_response_clearance (M b V ε a r : ℝ) (hb : 0 < b) (hV : 0 ≤ V)
    (hM : M = -b ∨ 0 ≤ M) (ha : a ≤ M) (v p d o : Vec2) (s ω : ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hd : UnitDirection d)
    (hsafe : Safe M b V ε p o s) :
    ∀ res ∈ SetM.run (evolve (motion a r v, time) (domain ε) ((p, d, o, s, ω), 0)),
      let ((pr, dr, or_, sr, _ω), _t) := res
      PassiveInv b V pr dr or_ sr := by
  obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stoppingMargin M b V ε s) (p - o) hsafe
  rintro ⟨⟨pr, dr, or_, sr, ωr⟩, t⟩ hrun
  have h := passive_response_signed M b V ε a r σ v i hb hV hM ha hv hσ
    ((p, d, o, s, ω), 0) ⟨rfl, hd, by simpa using hmargin⟩
    ((pr, dr, or_, sr, ωr), t) hrun
  exact ⟨h.1, h.2.1, fun _ => h.2.2.trans_le
    (by simpa using signed_le_infNorm (pr - or_) i σ hσ)⟩

theorem stopped_passive (b V ε a r : ℝ) (v : Vec2) (ha : a ≤ 0) :
    (fun ((_p, d, _o, s, _ω), _t) => s = 0 ∧ UnitDirection d)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((p, d, o, s, _ω), _t) => PassiveInv b V p d o s) := by
  have hderiv : HasPrime (Evolvable.denotation (motion a r v, time)) (domain ε)
      (fun ((_p, _d, _o, s, _ω), _t) => s) (fun _ => a) := by
    ode_deriv [motion, time]
  rintro ⟨⟨p₀, d₀, o₀, s₀, ω₀⟩, t₀⟩ ⟨hs₀, hd₀⟩ ⟨⟨p, d, o, s, ω⟩, t⟩ hrun
  have hs := dIle (ode := (motion a r v, time)) (domain := domain ε)
    (pre := fun ((_p, _d, _o, s, _ω), _t) => s = 0)
    (fun ((_p, _d, _o, s, _ω), _t) => s) (fun _ => a) hderiv
    (fun _ h => h.le) (fun _ _ => ha)
    ((p₀, d₀, o₀, s₀, ω₀), t₀) hs₀ ((p, d, o, s, ω), t) hrun
  have hdom := dW (ode := (motion a r v, time)) (domain := domain ε)
    (pre := fun _ => True) (fun _ h => h)
    ((p₀, d₀, o₀, s₀, ω₀), t₀) trivial ((p, d, o, s, ω), t) hrun
  have hd := motion_unit_preserved a r ε v
    ((p₀, d₀, o₀, s₀, ω₀), t₀) hd₀ ((p, d, o, s, ω), t) hrun
  exact ⟨hdom.2, hd, fun hpos => False.elim (not_lt_of_ge hs hpos)⟩

@[reducible]
def PassiveReady (A b V ε : ℝ) (p d o : Vec2) (s a : ℝ) : Prop :=
  (a ≤ -b ∧ PassiveInv b V p d o s) ∨
  (s = 0 ∧ a = 0 ∧ UnitDirection d) ∨
  (0 ≤ a ∧ a ≤ A ∧ UnitDirection d ∧ Safe A b V ε p o s)

noncomputable def passiveControl (A b V Ω ε : ℝ) (p _d o : Vec2)
    (s sMeasured ω r : ℝ) :=
  ctrl_r b Ω (pure A) (fun p o s _ => Safe A b V ε p o s) p o s sMeasured ω r

noncomputable def passiveDyn (_A _b _V ε a r : ℝ) (v p d o : Vec2) (s ω : ℝ) :=
  dyn ε a r v p d o s ω

@[spec] theorem ctrl_o_spec (V : ℝ) :
    ⦃True⦄ ctrl_o V ⦃fun v => v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2⦄ := by
  unfold ctrl_o
  vcgen
  simp_all

@[spec] theorem passiveControl_spec (A b V Ω ε : ℝ) (hA : 0 ≤ A)
    (p d o : Vec2) (s sMeasured ω r : ℝ) :
    ⦃sMeasured = s ∧ PassiveInv b V p d o s⦄
      passiveControl A b V Ω ε p d o s sMeasured ω r
    ⦃fun (a, _ω, _r, o) => PassiveReady A b V ε p d o s a⦄ := by
  unfold passiveControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

@[spec] theorem passiveDyn_spec (A b V ε a r : ℝ) (hA : 0 ≤ A)
    (hb : 0 < b) (hV : 0 ≤ V) (v p d o : Vec2) (s ω : ℝ) :
    ⦃v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 ∧ PassiveReady A b V ε p d o s a⦄
      passiveDyn A b V ε a r v p d o s ω
    ⦃fun (p, d, o, s, _ω) => PassiveInv b V p d o s⦄ := by
  unfold passiveDyn dyn
  vcgen (errorOnMissingSpec := false)
  rename_i hpre
  simp only [SetM.wp_pure, binderNameHint]
  rcases hpre with ⟨hv, hready⟩
  rcases hready with ⟨ha, hs, hd, hclear⟩ | ⟨rfl, rfl, hd⟩ | ⟨ha, haA, hd, hsafe⟩
  · by_cases hpos : 0 < s
    · exact passive_response_clearance (-b) b V ε a r hb hV (.inl rfl) ha v p d o s ω hv hd
        (by simpa [Safe, stoppingMargin, hb.ne'] using hclear hpos)
    · exact stopped_passive b V ε a r v (by linarith)
        ((p, d, o, s, ω), 0) ⟨le_antisymm (le_of_not_gt hpos) hs, hd⟩
  · exact stopped_passive b V ε 0 r v le_rfl ((p, d, o, 0, ω), 0) ⟨rfl, hd⟩
  · exact passive_response_clearance A b V ε a r hb hV (.inr hA) haA v p d o s ω hv hd hsafe

theorem passive_initial (b V : ℝ) (p d o : Vec2) (s : ℝ) :
    Initial p d o s → PassiveInv b V p d o s := by
  rintro ⟨rfl, _hsep, hd⟩
  exact ⟨le_rfl, hd, fun h => False.elim (lt_irrefl 0 h)⟩

theorem passive_separated (b V : ℝ) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o : Vec2) (s : ℝ) : PassiveInv b V p d o s → PassiveSafe p o s := by
  rintro ⟨hs, hd, hclear⟩ hpos
  apply static_separated b hb p d o s
  exact ⟨hs, hd, lt_of_le_of_lt
    (le_add_of_nonneg_right (div_nonneg (mul_nonneg hV hs) hb.le)) (hclear hpos)⟩

noncomputable def dwps' (A b V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires PassiveInv b V p d o s
    ensures (p, d, o, s, _ω, _r, _v) => PassiveInv b V p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PassiveInv b V p d o s do
    let (pMeasured, sMeasured) ← pure (p, s)
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new) ← passiveControl A b V Ω ε pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← pure a
    (p, d, o, s, ω) ← passiveDyn A b V ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

theorem dwps_eq (A b V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) :
    dwps A b V Ω ε p d o v s ω r = dwps' A b V Ω ε hA hb hV p d o v s ω r := by
  rfl

/-- Journal Theorem 2 / archive "Theorem 2: Passive safety". -/
theorem dwps_safe :
    ∀ A b V Ω ε p d o v s ω r,
      Bounds A b V ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwps A b V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := by
  intro A b V Ω ε p d o v s ω r hbounds hinit res hrun
  rw [dwps_eq A b V Ω ε hbounds.1 hbounds.2.1 hbounds.2.2.1] at hrun
  exact passive_separated b V hbounds.2.1 hbounds.2.2.1 _ _ _ _
    ((dwps'.spec A b V Ω ε hbounds.1 hbounds.2.1 hbounds.2.2.1 p d o v s ω r).le_wp
      (passive_initial b V p d o s hinit) res hrun)

theorem location_safe (A b V ε Δp : ℝ) (p pm o : Vec2) (s : ℝ)
    (hΔ : 0 ≤ Δp) (hloc : distanceSq pm p ≤ Δp ^ 2)
    (hguard : stoppingMargin A b V ε s + Δp < infNorm (pm - o)) :
    Safe A b V ε p o s := by
  obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stoppingMargin A b V ε s + Δp) (pm - o) hguard
  have herr := velocity_component_bound Δp σ (pm - p) i hΔ
    (by simpa [distanceSq] using hloc) hσ
  have hle := signed_le_infNorm (p - o) i σ hσ
  dsimp at herr hmargin hle
  dsimp [Safe]
  nlinarith

theorem stoppingMargin_speed_mono (A b V ε s sm : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hV : 0 ≤ V) (hε : 0 ≤ ε) (hs : 0 ≤ s) (hsm : s ≤ sm) :
    stoppingMargin A b V ε s ≤ stoppingMargin A b V ε sm := by
  unfold stoppingMargin stopDist
  gcongr

noncomputable def locationControl (A b V Ω ε Δp : ℝ) (_p pm _d o : Vec2)
    (s sm ω r : ℝ) :=
  ctrl_r b Ω (pure A)
    (fun p o s _ => stoppingMargin A b V ε s + Δp < infNorm (p - o)) pm o s sm ω r

@[spec] theorem locate_spec (Δp : ℝ) (p : Vec2) (s : ℝ) :
    ⦃True⦄ locate Δp p s ⦃fun (pm, sm) => distanceSq pm p ≤ Δp ^ 2 ∧ sm = s⦄ := by
  unfold locate
  vcgen
  simp_all

@[spec] theorem locationControl_spec (A b V Ω ε Δp : ℝ) (hA : 0 ≤ A) (hΔ : 0 ≤ Δp)
    (p pm d o : Vec2) (s sm ω r : ℝ) :
    ⦃distanceSq pm p ≤ Δp ^ 2 ∧ sm = s ∧ PassiveInv b V p d o s⦄
      locationControl A b V Ω ε Δp p pm d o s sm ω r
    ⦃fun (a, _ω, _r, o) => PassiveReady A b V ε p d o s a⦄ := by
  unfold locationControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    · simp_all
    · rename_i _ _ _ hpre hω hguard
      exact Or.inr (Or.inr ⟨hA, le_rfl, hpre.2.2.2.1,
        location_safe A b V ε Δp p pm o s hΔ hpre.1
          (by simpa [hpre.2.1] using hguard.2)⟩)

noncomputable def dwpslu' (A b V Ω ε Δp : ℝ) (hΔ : 0 ≤ Δp) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires PassiveInv b V p d o s
    ensures (p, d, o, s, _ω, _r, _v) => PassiveInv b V p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PassiveInv b V p d o s do
    let (pMeasured, sMeasured) ← locate Δp p s
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new) ← locationControl A b V Ω ε Δp p pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← pure a
    (p, d, o, s, ω) ← passiveDyn A b V ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

theorem dwpslu_eq (A b V Ω ε Δp : ℝ) (hΔ : 0 ≤ Δp) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) :
    dwpslu A b V Ω ε Δp p d o v s ω r = dwpslu' A b V Ω ε Δp hΔ hA hb hV p d o v s ω r := by
  rfl

theorem dwpslu_safe :
    ∀ A b V Ω ε Δp p d o v s ω r,
      Bounds A b V ε → 0 ≤ Δp → Initial p d o s →
        ∀ res ∈ SetM.run (dwpslu A b V Ω ε Δp p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := by
  intro A b V Ω ε Δp p d o v s ω r hbounds hΔ hinit res hrun
  rw [dwpslu_eq A b V Ω ε Δp hΔ hbounds.1 hbounds.2.1 hbounds.2.2.1] at hrun
  exact passive_separated b V hbounds.2.1 hbounds.2.2.1 _ _ _ _
    ((dwpslu'.spec A b V Ω ε Δp hΔ hbounds.1 hbounds.2.1 hbounds.2.2.1 p d o v s ω r).le_wp
      (passive_initial b V p d o s hinit) res hrun)

@[spec] theorem sense_spec (Δs : ℝ) (p : Vec2) (s : ℝ) :
    ⦃True⦄ sense Δs p s ⦃fun (pm, sm) => pm = p ∧ s ≤ sm⦄ := by
  unfold sense
  vcgen
  grind

noncomputable def velocityControl (A b V Ω ε : ℝ) (p _d o : Vec2)
    (s sm ω r : ℝ) :=
  ctrl_r b Ω (pure A) (fun p o s _ => Safe A b V ε p o s) p o s sm ω r

@[spec] theorem velocityControl_spec (A b V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hV : 0 ≤ V) (hε : 0 ≤ ε) (p d o : Vec2) (s sm ω r : ℝ) :
    ⦃s ≤ sm ∧ PassiveInv b V p d o s⦄
      velocityControl A b V Ω ε p d o s sm ω r
    ⦃fun (a, _ω, _r, o) => PassiveReady A b V ε p d o s a⦄ := by
  unfold velocityControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    · simp_all
    · rename_i _ _ _ hpre hω hguard
      exact Or.inr (Or.inr ⟨hA, le_rfl, hpre.2.2.1,
        (stoppingMargin_speed_mono A b V ε s sm hA hb hV hε hpre.2.1 hpre.1).trans_lt hguard.2⟩)

noncomputable def dwpsvu' (A b V Ω ε Δs : ℝ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires PassiveInv b V p d o s
    ensures (p, d, o, s, _ω, _r, _v) => PassiveInv b V p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PassiveInv b V p d o s do
    let (pMeasured, sMeasured) ← sense Δs p s
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new) ← velocityControl A b V Ω ε pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← pure a
    (p, d, o, s, ω) ← passiveDyn A b V ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

theorem dwpsvu_eq (A b V Ω ε Δs : ℝ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) :
    dwpsvu A b V Ω ε Δs p d o v s ω r = dwpsvu' A b V Ω ε Δs hε hA hb hV p d o v s ω r := by
  rfl

theorem dwpsvu_safe :
    ∀ A b V Ω ε Δs p d o v s ω r,
      Bounds A b V ε → 0 ≤ Δs → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsvu A b V Ω ε Δs p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := by
  intro A b V Ω ε Δs p d o v s ω r hbounds _hΔ hinit res hrun
  rw [dwpsvu_eq A b V Ω ε Δs hbounds.2.2.2.le hbounds.1 hbounds.2.1 hbounds.2.2.1] at hrun
  exact passive_separated b V hbounds.2.1 hbounds.2.2.1 _ _ _ _
    ((dwpsvu'.spec A b V Ω ε Δs hbounds.2.2.2.le hbounds.1 hbounds.2.1 hbounds.2.2.1
      p d o v s ω r).le_wp (passive_initial b V p d o s hinit) res hrun)

@[reducible]
def PerturbReady (A b V ε Δa : ℝ) (p d o : Vec2) (s a : ℝ) : Prop :=
  (a = -b ∧ PassiveInv (b * Δa) V p d o s) ∨
  (s = 0 ∧ a = 0 ∧ UnitDirection d) ∨
  (a = A ∧ UnitDirection d ∧ Safe A (b * Δa) V ε p o s)

noncomputable def perturbControl (A b V Ω ε Δa : ℝ) (p _d o : Vec2)
    (s sm ω r : ℝ) :=
  ctrl_r b Ω (pure A) (fun p o s _ => Safe A (b * Δa) V ε p o s) p o s sm ω r

noncomputable def perturbAct (_A _b _V _ε Δa : ℝ) (_p _d _o : Vec2) (_s a : ℝ) :=
  act Δa a

@[spec] theorem perturbControl_spec (A b V Ω ε Δa : ℝ) (p d o : Vec2) (s sm ω r : ℝ) :
    ⦃sm = s ∧ PassiveInv (b * Δa) V p d o s⦄
      perturbControl A b V Ω ε Δa p d o s sm ω r
    ⦃fun (a, _ω, _r, o) => PerturbReady A b V ε Δa p d o s a⦄ := by
  unfold perturbControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

@[spec] theorem perturbAct_spec (A b V ε Δa : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hΔ : 0 < Δa) (p d o : Vec2) (s a : ℝ) :
    ⦃PerturbReady A b V ε Δa p d o s a⦄ perturbAct A b V ε Δa p d o s a
    ⦃fun actual => PassiveReady A (b * Δa) V ε p d o s actual⦄ := by
  unfold perturbAct act
  vcgen
  rename_i hpre hδ
  rcases hpre with ⟨rfl, hinv⟩ | ⟨rfl, rfl, hd⟩ | ⟨rfl, hd, hsafe⟩
  · exact Or.inl ⟨by nlinarith [hδ.1], hinv⟩
  · exact Or.inr (Or.inl ⟨rfl, mul_zero _, hd⟩)
  · exact Or.inr (Or.inr ⟨mul_nonneg (by linarith [hδ.1]) hA,
      by nlinarith [hδ.2], hd, hsafe⟩)

noncomputable def dwpsap' (A b V Ω ε Δa : ℝ) (hΔ : 0 < Δa) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires PassiveInv (b * Δa) V p d o s
    ensures (p, d, o, s, _ω, _r, _v) => PassiveInv (b * Δa) V p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PassiveInv (b * Δa) V p d o s do
    let (pMeasured, sMeasured) ← pure (p, s)
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new) ← perturbControl A b V Ω ε Δa pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← perturbAct A b V ε Δa p d o s a
    (p, d, o, s, ω) ← passiveDyn A (b * Δa) V ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)
where finally
  | spec => all_goals positivity

theorem dwpsap_eq (A b V Ω ε Δa : ℝ) (hΔ : 0 < Δa) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) :
    dwpsap A b V Ω ε Δa p d o v s ω r = dwpsap' A b V Ω ε Δa hΔ hA hb hV p d o v s ω r := by
  rfl

theorem dwpsap_safe :
    ∀ A b V Ω ε Δa p d o v s ω r,
      Bounds A b V ε → 0 < Δa → Δa ≤ 1 → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsap A b V Ω ε Δa p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := by
  intro A b V Ω ε Δa p d o v s ω r hbounds hΔ _hΔle hinit res hrun
  rw [dwpsap_eq A b V Ω ε Δa hΔ hbounds.1 hbounds.2.1 hbounds.2.2.1] at hrun
  exact passive_separated (b * Δa) V (mul_pos hbounds.2.1 hΔ) hbounds.2.2.1 _ _ _ _
    ((dwpsap'.spec A b V Ω ε Δa hΔ hbounds.1 hbounds.2.1 hbounds.2.2.1
      p d o v s ω r).le_wp (passive_initial (b * Δa) V p d o s hinit) res hrun)

noncomputable def terminalSpeed (a ε : ℝ) :
    (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ → ℝ :=
  fun ((_p, _d, _o, s, _ω), t) => s + a * (ε - t)

theorem terminalSpeed_preserved (a r ε : ℝ) (v : Vec2) :
    (fun st => 0 ≤ terminalSpeed a ε st)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun st => 0 ≤ terminalSpeed a ε st) := by
  apply dIge (terminalSpeed a ε) (fun _ => 0)
  · ode_deriv [terminalSpeed, motion, time]
  · exact fun _ h => h
  · exact fun _ _ => le_rfl

theorem actual_response_signed (b V ε a r σ : ℝ) (v : Vec2) (i : Fin 2)
    (hb : 0 < b) (hV : 0 ≤ V) (ha : -b ≤ a)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hσ : σ = 1 ∨ σ = -1) :
    (fun ((p, d, o, s, _ω), t) => t = 0 ∧ UnitDirection d ∧
      0 ≤ s + a * ε ∧ stoppingMargin a b V ε s < σ * (p i - o i))
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((p, d, o, s, _ω), _t) =>
      0 ≤ s ∧ UnitDirection d ∧ stopDist b s + V * s / b < σ * (p i - o i)) := by
  apply dC (cut := fun st => UnitDirection st.1.2.1 ∧ 0 ≤ terminalSpeed a ε st)
  · intro st h res hrun
    exact ⟨motion_unit_preserved a r ε v st h.2.1 res hrun,
      terminalSpeed_preserved a r ε v st
        (by rcases st with ⟨⟨p, d, o, s, ω⟩, t⟩; simpa [terminalSpeed, h.1] using h.2.2.1)
        res hrun⟩
  · rintro ⟨⟨p₀, d₀, o₀, s₀, ω₀⟩, t₀⟩ ⟨rfl, hunit, hbudget, hmargin⟩
      ⟨⟨p, d, o, s, ω⟩, t⟩ hrun
    have hstart : 0 < passiveResponse a b V ε σ i ((p₀, d₀, o₀, s₀, ω₀), 0) := by
      dsimp [passiveResponse, stoppingMargin] at hmargin ⊢
      simp only [sub_zero] at hmargin ⊢
      linarith
    have hprime : HasPrime (Evolvable.denotation (motion a r v, time))
        (fun st => domain ε st ∧ UnitDirection st.1.2.1 ∧ 0 ≤ terminalSpeed a ε st)
        (passiveResponse a b V ε σ i)
        (fun ((_p, d, _o, s, _ω), _t) => s * (σ * d i + 1) + (V - σ * v i)) := by
      simpa using passiveResponse_hasPrime a b V ε a r σ hb.ne' v i _
    have hend := dIgt (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1 ∧ 0 ≤ terminalSpeed a ε st)
      (pre := fun st => 0 < passiveResponse a b V ε σ i st)
      (passiveResponse a b V ε σ i)
      (fun ((_p, d, _o, s, _ω), _t) => s * (σ * d i + 1) + (V - σ * v i)) hprime
      (fun _ h => h)
      (fun st h => add_nonneg
        (mul_nonneg h.1.2 (signed_direction_nonneg σ i st.1.2.1 hσ h.2.1))
        (velocity_component_bound V σ v i hV hv hσ))
      ((p₀, d₀, o₀, s₀, ω₀), 0) hstart ((p, d, o, s, ω), t) hrun
    have hdom := dW (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1 ∧ 0 ≤ terminalSpeed a ε st)
      (pre := fun _ => True) (fun _ h => h)
      ((p₀, d₀, o₀, s₀, ω₀), 0) trivial ((p, d, o, s, ω), t) hrun
    have hcoeff : 0 ≤ a / b + 1 := by
      have hdiv : -1 ≤ a / b := (le_div_iff₀ hb).mpr (by linarith)
      linarith
    have hinner : 0 ≤ a / 2 * (ε - t) ^ 2 + (ε - t) * (s + V) := by
      have hbudget' := hdom.2.2
      dsimp [terminalSpeed] at hbudget'
      have hh : 0 ≤ ε - t := sub_nonneg.mpr hdom.1.1
      nlinarith [mul_nonneg hh (add_nonneg hbudget' hdom.1.2), mul_nonneg hh hV]
    have hreserve := mul_nonneg hcoeff hinner
    exact ⟨hdom.1.2, hdom.2.1, by dsimp [passiveResponse] at hend; linarith⟩

theorem braking_margin_mono (b₁ b₂ V s : ℝ) (hb₁ : 0 < b₁) (hbb : b₁ ≤ b₂)
    (hV : 0 ≤ V) (hs : 0 ≤ s) :
    stopDist b₂ s + V * s / b₂ ≤ stopDist b₁ s + V * s / b₁ := by
  unfold stopDist
  gcongr

theorem actual_clearance (b V ε a r : ℝ) (hb : 0 < b) (hV : 0 ≤ V) (hε : 0 < ε)
    (ha : -b ≤ a) (v p d o : Vec2) (s ω : ℝ) (hs : 0 ≤ s)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hd : UnitDirection d)
    (hsafe : actualMargin b V ε s a < infNorm (p - o)) :
    ∀ res ∈ SetM.run (evolve (motion a r v, time) (domain ε) ((p, d, o, s, ω), 0)),
      let ((pr, dr, or_, sr, _ω), _t) := res
      PassiveInv b V pr dr or_ sr := by
  by_cases hbudget : 0 ≤ s + a * ε
  · rw [actualMargin, ite_eq_left hbudget] at hsafe
    obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stoppingMargin a b V ε s) (p - o) hsafe
    rintro ⟨⟨pr, dr, or_, sr, ωr⟩, t⟩ hrun
    have h := actual_response_signed b V ε a r σ v i hb hV ha hv hσ
      ((p, d, o, s, ω), 0) ⟨rfl, hd, hbudget, by simpa using hmargin⟩
      ((pr, dr, or_, sr, ωr), t) hrun
    exact ⟨h.1, h.2.1, fun _ => h.2.2.trans_le
      (by simpa using signed_le_infNorm (pr - or_) i σ hσ)⟩
  · have ha0 : a < 0 := by nlinarith
    have hsafe' : Safe a (-a) V ε p o s := by
      simp [actualMargin, hbudget] at hsafe
      simp only [neg_div] at hsafe
      simp [Safe, stoppingMargin, stopDist, div_neg, ha0.ne, mul_neg]
      linarith
    rintro ⟨⟨pr, dr, or_, sr, ωr⟩, t⟩ hrun
    have h := passive_response_clearance a (-a) V ε a r (by linarith) hV
      (.inl (by ring)) le_rfl v p d o s ω hv hd hsafe' ((pr, dr, or_, sr, ωr), t) hrun
    exact ⟨h.1, h.2.1, fun hpos =>
      (braking_margin_mono (-a) b V sr (by linarith) (by linarith) hV h.1).trans_lt (h.2.2 hpos)⟩

@[reducible]
def ActualReady (b V ε : ℝ) (p d o : Vec2) (s a : ℝ) : Prop :=
  (a = -b ∧ PassiveInv b V p d o s) ∨
  (s = 0 ∧ a = 0 ∧ UnitDirection d) ∨
  (-b ≤ a ∧ 0 ≤ s ∧ UnitDirection d ∧ actualMargin b V ε s a < infNorm (p - o))

@[spec] theorem driveActual_spec (A b : ℝ) :
    ⦃True⦄ driveActual A b ⦃fun a => -b ≤ a ∧ a ≤ A⦄ := by
  unfold driveActual
  vcgen
  simp_all

noncomputable def actualControl (A b V Ω ε : ℝ) (p _d o : Vec2) (s sm ω r : ℝ) :=
  ctrl_r b Ω (driveActual A b) (fun p o s a => actualMargin b V ε s a < infNorm (p - o))
    p o s sm ω r

noncomputable def actualDyn (_b _V ε a r : ℝ) (v p d o : Vec2) (s ω : ℝ) :=
  dyn ε a r v p d o s ω

@[spec] theorem actualControl_spec (A b V Ω ε : ℝ) (p d o : Vec2) (s sm ω r : ℝ) :
    ⦃sm = s ∧ PassiveInv b V p d o s⦄ actualControl A b V Ω ε p d o s sm ω r
    ⦃fun (a, _ω, _r, o) => ActualReady b V ε p d o s a⦄ := by
  unfold actualControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

@[spec] theorem actualDyn_spec (b V ε a r : ℝ) (hb : 0 < b) (hV : 0 ≤ V) (hε : 0 < ε)
    (v p d o : Vec2) (s ω : ℝ) :
    ⦃v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 ∧ ActualReady b V ε p d o s a⦄
      actualDyn b V ε a r v p d o s ω
    ⦃fun (p, d, o, s, _ω) => PassiveInv b V p d o s⦄ := by
  unfold actualDyn dyn
  vcgen (errorOnMissingSpec := false)
  rename_i hpre
  simp only [SetM.wp_pure, binderNameHint]
  rcases hpre with ⟨hv, hready⟩
  rcases hready with ⟨rfl, hs, hd, hclear⟩ | ⟨rfl, rfl, hd⟩ | ⟨ha, hs, hd, hsafe⟩
  · by_cases hpos : 0 < s
    · exact passive_response_clearance (-b) b V ε (-b) r hb hV (.inl rfl) le_rfl v p d o s ω hv hd
        (by simpa [Safe, stoppingMargin, hb.ne'] using hclear hpos)
    · exact stopped_passive b V ε (-b) r v (by linarith)
        ((p, d, o, s, ω), 0) ⟨le_antisymm (le_of_not_gt hpos) hs, hd⟩
  · exact stopped_passive b V ε 0 r v le_rfl ((p, d, o, 0, ω), 0) ⟨rfl, hd⟩
  · exact actual_clearance b V ε a r hb hV hε ha v p d o s ω hs hv hd hsafe

noncomputable def dwpsa' (A b V Ω ε : ℝ) (hε : 0 < ε) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires PassiveInv b V p d o s
    ensures (p, d, o, s, _ω, _r, _v) => PassiveInv b V p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PassiveInv b V p d o s do
    let (pMeasured, sMeasured) ← pure (p, s)
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new) ← actualControl A b V Ω ε pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← pure a
    (p, d, o, s, ω) ← actualDyn b V ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

theorem dwpsa_eq (A b V Ω ε : ℝ) (hε : 0 < ε) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) :
    dwpsa A b V Ω ε p d o v s ω r = dwpsa' A b V Ω ε hε hb hV p d o v s ω r := by
  rfl

theorem dwpsa_safe :
    ∀ A b V Ω ε p d o v s ω r,
      Bounds A b V ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsa A b V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := by
  intro A b V Ω ε p d o v s ω r hbounds hinit res hrun
  rw [dwpsa_eq A b V Ω ε hbounds.2.2.2 hbounds.2.1 hbounds.2.2.1] at hrun
  exact passive_separated b V hbounds.2.1 hbounds.2.2.1 _ _ _ _
    ((dwpsa'.spec A b V Ω ε hbounds.2.2.2 hbounds.2.1 hbounds.2.2.1 p d o v s ω r).le_wp
      (passive_initial b V p d o s hinit) res hrun)

theorem passiveResponse_preserved (M b V ε a r σ : ℝ) (v : Vec2) (i : Fin 2)
    (hb : 0 < b) (hV : 0 ≤ V) (hM : M = -b ∨ 0 ≤ M) (ha : a ≤ M)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hσ : σ = 1 ∨ σ = -1) :
    (fun st => UnitDirection st.1.2.1 ∧ 0 < passiveResponse M b V ε σ i st)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun st => UnitDirection st.1.2.1 ∧ 0 < passiveResponse M b V ε σ i st) := by
  apply dC (cut := fun st => UnitDirection st.1.2.1)
  · exact fun st h => motion_unit_preserved a r ε v st h.1
  · intro st h res hrun
    have hdom := dW (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
      (pre := fun _ => True) (fun _ h => h) st trivial res hrun
    apply And.intro hdom.2
    apply dIgt (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
      (pre := fun st => 0 < passiveResponse M b V ε σ i st)
      (passiveResponse M b V ε σ i)
      (fun ((_p, d, _o, s, _ω), t) => s * (σ * d i + 1) + (V - σ * v i) +
        (M - a) / b * (s + V + (M + b) * (ε - t)))
      (passiveResponse_hasPrime M b V ε a r σ hb.ne' v i _)
      (fun _ h => h) ?_ st h.2 res hrun
    intro st h
    have hMb : 0 ≤ M + b := hM.elim (fun h => by simp [h]) (fun h => by linarith)
    exact add_nonneg
      (add_nonneg (mul_nonneg h.1.2 (signed_direction_nonneg σ i st.1.2.1 hσ h.2))
        (velocity_component_bound V σ v i hV hv hσ))
      (mul_nonneg (div_nonneg (sub_nonneg.mpr ha) hb.le)
        (add_nonneg (add_nonneg h.1.2 hV) (mul_nonneg hMb (sub_nonneg.mpr h.1.1))))

@[reducible]
def ReactionInv (A b V ε a : ℝ) (p d o : Vec2) (s ω t : ℝ) : Prop :=
  0 ≤ s ∧ UnitDirection d ∧ t ≤ ε ∧
    ((a = -b ∧ (0 < s → stopDist b s + V * s / b < infNorm (p - o))) ∨
     (a = 0 ∧ s = 0) ∨
     (a = A ∧ ∃ i : Fin 2, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
       0 < passiveResponse A b V ε σ i ((p, d, o, s, ω), t)))

theorem reaction_passive (A b V ε a : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o : Vec2) (s ω t : ℝ) :
    ReactionInv A b V ε a p d o s ω t → PassiveInv b V p d o s := by
  rintro ⟨hs, hd, ht, h⟩
  apply And.intro hs (And.intro hd ?_)
  rcases h with ⟨_, hclear⟩ | ⟨_, rfl⟩ | ⟨_, i, σ, hσ, hmargin⟩
  · exact hclear
  · simp
  · intro _
    have hreserve : 0 ≤ (A / b + 1) * (A / 2 * (ε - t) ^ 2 + (ε - t) * (s + V)) :=
      mul_nonneg (add_nonneg (div_nonneg hA hb.le) (by norm_num))
        (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
          (mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hs hV)))
    have hle := signed_le_infNorm (p - o) i σ hσ
    dsimp [passiveResponse] at hmargin
    dsimp at hle
    linarith

noncomputable def asyncControl (A b V Ω ε : ℝ) (p _d o : Vec2) (s ω r : ℝ) :=
  ctrl_r b Ω (pure A) (fun p o s _ => Safe A b V ε p o s) p o s s ω r

@[spec] theorem asyncControl_spec (A b V Ω ε : ℝ) (hε : 0 ≤ ε)
    (p d o : Vec2) (s ω r : ℝ) :
    ⦃PassiveInv b V p d o s⦄ asyncControl A b V Ω ε p d o s ω r
    ⦃fun (a, ω, _r, o) => ReactionInv A b V ε a p d o s ω 0⦄ := by
  unfold asyncControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    · simp_all
    · rename_i _ _ _ hpre hω hguard
      obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stoppingMargin A b V ε s) (p - o) hguard.2
      have hpositive : 0 < passiveResponse A b V ε σ i ((p, d, o, s, ω), 0) := by
        dsimp [passiveResponse, stoppingMargin] at hmargin ⊢
        simp only [sub_zero] at hmargin ⊢
        linarith
      exact ⟨hpre.1, hpre.2.1, hε, Or.inr (Or.inr ⟨rfl, i, σ, hσ, hpositive⟩)⟩

theorem speed_upper (a r ε smax : ℝ) (v : Vec2) (ha : a ≤ 0) :
    (fun ((_p, _d, _o, s, _ω), _t) => s ≤ smax)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((_p, _d, _o, s, _ω), _t) => s ≤ smax) := by
  have hderiv : HasPrime (Evolvable.denotation (motion a r v, time)) (domain ε)
      (fun ((_p, _d, _o, s, _ω), _t) => s - smax) (fun _ => a) := by
    ode_deriv [motion, time]
  simpa only [sub_nonpos] using
    (dIle (ode := (motion a r v, time)) (domain := domain ε)
      (pre := fun ((_p, _d, _o, s, _ω), _t) => s ≤ smax)
      (fun ((_p, _d, _o, s, _ω), _t) => s - smax) (fun _ => a) hderiv
      (fun _ h => sub_nonpos.mpr h) (fun _ _ => ha))

theorem reaction_preserved (A b V ε a r : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (v : Vec2) (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) :
    (fun ((p, d, o, s, ω), t) => ReactionInv A b V ε a p d o s ω t)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((p, d, o, s, ω), t) => ReactionInv A b V ε a p d o s ω t) := by
  rintro ⟨⟨p₀, d₀, o₀, s₀, ω₀⟩, t₀⟩ ⟨hs₀, hd₀, ht₀, hready⟩
    ⟨⟨p, d, o, s, ω⟩, t⟩ hrun
  have hdom := dW (ode := (motion a r v, time)) (domain := domain ε)
    (pre := fun _ => True) (fun _ h => h)
    ((p₀, d₀, o₀, s₀, ω₀), t₀) trivial ((p, d, o, s, ω), t) hrun
  have hd := motion_unit_preserved a r ε v
    ((p₀, d₀, o₀, s₀, ω₀), t₀) hd₀ ((p, d, o, s, ω), t) hrun
  apply And.intro hdom.2 (And.intro hd (And.intro hdom.1 ?_))
  rcases hready with ⟨rfl, hclear⟩ | ⟨rfl, rfl⟩ | ⟨rfl, i, σ, hσ, hmargin⟩
  · have hclear' : 0 < s → stopDist b s + V * s / b < infNorm (p - o) := by
      by_cases hpos : 0 < s₀
      · obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stopDist b s₀ + V * s₀ / b)
          (p₀ - o₀) (hclear hpos)
        have hstart : 0 < passiveResponse (-b) b V ε σ i ((p₀, d₀, o₀, s₀, ω₀), t₀) := by
          dsimp [passiveResponse]
          simp [hb.ne']
          dsimp at hmargin
          linarith
        have h := passiveResponse_preserved (-b) b V ε (-b) r σ v i hb hV
          (.inl rfl) le_rfl hv hσ ((p₀, d₀, o₀, s₀, ω₀), t₀) ⟨hd₀, hstart⟩
          ((p, d, o, s, ω), t) hrun
        intro _
        have hle := signed_le_infNorm (p - o) i σ hσ
        dsimp [passiveResponse] at h
        simp [hb.ne'] at h
        dsimp at hle
        linarith [h.2]
      · have h := speed_upper (-b) r ε 0 v (by linarith)
          ((p₀, d₀, o₀, s₀, ω₀), t₀) (le_of_not_gt hpos) ((p, d, o, s, ω), t) hrun
        exact fun hpos => False.elim (not_lt_of_ge h hpos)
    exact Or.inl ⟨rfl, hclear'⟩
  · have h := speed_upper 0 r ε 0 v le_rfl
      ((p₀, d₀, o₀, 0, ω₀), t₀) le_rfl ((p, d, o, s, ω), t) hrun
    exact Or.inr (Or.inl ⟨rfl, le_antisymm h hdom.2⟩)
  · exact Or.inr (Or.inr ⟨rfl, i, σ, hσ,
      (passiveResponse_preserved a b V ε a r σ v i hb hV (.inr hA) le_rfl hv hσ
        ((p₀, d₀, o₀, s₀, ω₀), t₀) ⟨hd₀, hmargin⟩ ((p, d, o, s, ω), t) hrun).2⟩)

noncomputable def reactionDyn (_A _b _V ε a r : ℝ) (v p d o : Vec2) (s ω t : ℝ) :=
  evolve (motion a r v, time) (domain ε) ((p, d, o, s, ω), t)

@[spec] theorem reactionDyn_spec (A b V ε a r : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (v p d o : Vec2) (s ω t : ℝ) :
    ⦃v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 ∧ ReactionInv A b V ε a p d o s ω t⦄
      reactionDyn A b V ε a r v p d o s ω t
    ⦃fun ((p, d, o, s, ω), t) => ReactionInv A b V ε a p d o s ω t⦄ := by
  constructor
  rintro ⟨hv, hinv⟩
  exact reaction_preserved A b V ε a r hA hb hV v hv ((p, d, o, s, ω), t) hinv

noncomputable def dwpsns' (A b V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (hε : 0 ≤ ε) (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires PassiveInv b V p d o s
    ensures (p, d, o, s, _ω, _r, _v) => PassiveInv b V p d o s
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PassiveInv b V p d o s do
    let (a, ω_new, r_new, o_new) ← asyncControl A b V Ω ε p d o s ω r
    ω := ω_new
    r := r_new
    o := o_new
    let mut t : ℝ := 0
    let m ← choose ℕ
    for _ in [:m]
        invariant _pref _suff => ReactionInv A b V ε a p d o s ω t do
      v ← ctrl_o V
      let (res, t_new) ← reactionDyn A b V ε a r v p d o s ω t
      (p, d, o, s, ω) := res
      t := t_new
  return (p, d, o, s, ω, r, v)
where finally
  | spec =>
    all_goals apply reaction_passive A b V ε _ hA hb hV
    all_goals assumption

theorem dwpsns_eq (A b V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (hε : 0 ≤ ε) (p d o v : Vec2) (s ω r : ℝ) :
    dwpsns A b V Ω ε p d o v s ω r = dwpsns' A b V Ω ε hA hb hV hε p d o v s ω r := by
  rfl

/-- Journal Theorem 9 / archive "Passive safety for asynchronous controllers". -/
theorem dwpsns_safe :
    ∀ A b V Ω ε p d o v s ω r,
      Bounds A b V ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsns A b V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := by
  intro A b V Ω ε p d o v s ω r hbounds hinit res hrun
  rw [dwpsns_eq A b V Ω ε hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.le] at hrun
  exact passive_separated b V hbounds.2.1 hbounds.2.2.1 _ _ _ _
    ((dwpsns'.spec A b V Ω ε hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.le
      p d o v s ω r).le_wp (passive_initial b V p d o s hinit) res hrun)

def orientationProjection : (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ) × ℝ →
    (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ :=
  fun ((p, d, o, s, ω, _β), t) => ((p, d, o, s, ω), t)

theorem orientation_projection (a r ε : ℝ) (v p d o : Vec2) (s ω β t : ℝ) :
    ∀ res ∈ SetM.run (evolve (orientationMotion a r v, time) (orientationDomain ε)
      ((p, d, o, s, ω, β), t)),
      orientationProjection res ∈ SetM.run (evolve (motion a r v, time) (domain ε)
        ((p, d, o, s, ω), t)) := by
  exact (evolveSemantic_spec (Evolvable.denotation (orientationMotion a r v, time))
    (orientationDomain ε) ((p, d, o, s, ω, β), t)).le_wp (by
    intro T hT path hevol
    apply SemanticODE.mem_evolveSemantic _ (domain ε) ((p, d, o, s, ω), t) T
      (fun τ => orientationProjection (path τ)) hT
    apply And.intro (congrArg orientationProjection hevol.1)
    apply And.intro (fun τ hτ => hevol.2.1 τ hτ)
    constructor
    · intro τ hτ
      have h := hevol.2.2.1 τ hτ
      exact h.fst.prodMk (h.snd.fst.prodMk (h.snd.snd.fst.prodMk
        (h.snd.snd.snd.fst.prodMk h.snd.snd.snd.snd.fst)))
    · exact hevol.2.2.2
  )

noncomputable def curveError (r : ℝ) : (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ) × ℝ → ℝ :=
  fun ((_p, _d, _o, s, ω, _β), _t) => r * ω - s

theorem orientation_curve (a r ε : ℝ) (v : Vec2) (hr : r ≠ 0) :
    (fun st => curveError r st = 0)
    [[evolve (orientationMotion a r v, time) (orientationDomain ε)]]
    (fun st => curveError r st = 0) := by
  apply dIeq (curveError r) (fun _ => 0)
  · ode_deriv [curveError, orientationMotion, time]
    field_simp
    ring
  · exact fun _ h => h
  · exact fun _ _ => rfl

noncomputable def angularResponse (M b ε γ r σ : ℝ) :
    (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ) × ℝ → ℝ :=
  fun ((_p, _d, _o, s, _ω, β), t) => γ * |r| - σ * r * β - stopDist b s -
    (M / b + 1) * (M / 2 * (ε - t) ^ 2 + (ε - t) * s)

theorem angularResponse_hasPrime (M b ε γ r σ : ℝ) (v : Vec2) (D) :
    HasPrime (Evolvable.denotation (orientationMotion M r v, time)) D
      (angularResponse M b ε γ r σ)
      (fun ((_p, _d, _o, s, ω, _β), _t) => s - σ * r * ω) := by
  ode_deriv [angularResponse, stopDist, orientationMotion, time]

theorem angular_response (M b ε γ r σ : ℝ) (v : Vec2) (hb : 0 < b)
    (hr : r ≠ 0) (hM : M = -b ∨ 0 ≤ M) (hσ : σ = 1 ∨ σ = -1) :
    (fun st => curveError r st = 0 ∧ 0 < angularResponse M b ε γ r σ st)
    [[evolve (orientationMotion M r v, time) (orientationDomain ε)]]
    (fun ((_p, _d, _o, s, _ω, β), _t) => σ * r * β + stopDist b s < γ * |r|) := by
  apply dC (cut := fun st => curveError r st = 0)
  · exact fun st h => orientation_curve M r ε v hr st h.1
  · intro st h res hrun
    have hend := dIgt (ode := (orientationMotion M r v, time))
      (domain := fun st => orientationDomain ε st ∧ curveError r st = 0)
      (pre := fun st => 0 < angularResponse M b ε γ r σ st)
      (angularResponse M b ε γ r σ)
      (fun ((_p, _d, _o, s, ω, _β), _t) => s - σ * r * ω)
      (angularResponse_hasPrime M b ε γ r σ v _)
      (fun _ h => h) ?_ st h.2 res hrun
    · rcases res with ⟨⟨p, d, o, s, ω, β⟩, t⟩
      have hdom := dW (ode := (orientationMotion M r v, time))
        (domain := fun st => orientationDomain ε st ∧ curveError r st = 0)
        (pre := fun _ => True) (fun _ h => h) st trivial ((p, d, o, s, ω, β), t) hrun
      have hreserve : 0 ≤ (M / b + 1) * (M / 2 * (ε - t) ^ 2 + (ε - t) * s) :=
        hM.elim (fun heq => by simp [heq, hb.ne'])
          (fun hM => mul_nonneg (add_nonneg (div_nonneg hM hb.le) (by norm_num))
            (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
              (mul_nonneg (sub_nonneg.mpr hdom.1.1) hdom.1.2)))
      dsimp [angularResponse] at hend ⊢
      linarith
    · rintro ⟨⟨p, d, o, s, ω, β⟩, t⟩ ⟨hdom, hcurve⟩
      dsimp [curveError] at hcurve
      rcases hσ with rfl | rfl <;> dsimp <;> nlinarith [hdom.2]

@[reducible]
def TurnSafe (b γ r s β : ℝ) : Prop :=
  ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → σ * r * β + stopDist b s < γ * |r|

@[reducible]
def OrientationInv (b V γ : ℝ) (p d o : Vec2) (s r β visible : ℝ) : Prop :=
  0 ≤ s ∧ UnitDirection d ∧ r ≠ 0 ∧
    (0 < s → stopDist b s + V * s / b < infNorm (p - o) ∨
      (¬0 < visible ∧ TurnSafe b γ r s β))

@[reducible]
def OrientationReady (A b V ε γ : ℝ) (p d o : Vec2) (s a r β visible : ℝ) : Prop :=
  (a = -b ∧ OrientationInv b V γ p d o s r β visible) ∨
  (s = 0 ∧ a = 0 ∧ UnitDirection d ∧ r ≠ 0) ∨
  (a = A ∧ 0 ≤ s ∧ UnitDirection d ∧ r ≠ 0 ∧ β = 0 ∧
    (0 < visible → Safe A b V ε p o s) ∧ stoppingMargin A b 0 ε s < γ * |r|)

noncomputable def orientControl (A b V ε γ : ℝ) (p _d o : Vec2) (s ω r β visible : ℝ) :=
  orientationControl A b V ε γ p o s ω r β visible

@[spec] theorem orientControl_spec (A b V ε γ : ℝ) (p d o : Vec2) (s ω r β visible : ℝ) :
    ⦃OrientationInv b V γ p d o s r β visible⦄
      orientControl A b V ε γ p d o s ω r β visible
    ⦃fun (a, _ω, r, o, β, visible) => OrientationReady A b V ε γ p d o s a r β visible⦄ := by
  unfold orientControl orientationControl
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

theorem orientation_step (A b V ε γ a r visible : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (v p d o : Vec2) (s ω β : ℝ) (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2)
    (hcurve : ω * r = s) (hready : OrientationReady A b V ε γ p d o s a r β visible) :
    ∀ res ∈ SetM.run (evolve (orientationMotion a r v, time) (orientationDomain ε)
      ((p, d, o, s, ω, β), 0)),
      let ((pr, dr, or_, sr, _ω, βr), _t) := res
      OrientationInv b V γ pr dr or_ sr r βr visible := by
  rintro ⟨⟨pr, dr, or_, sr, ωr, βr⟩, t⟩ hrun
  have hproj := orientation_projection a r ε v p d o s ω β 0
    ((pr, dr, or_, sr, ωr, βr), t) hrun
  have hdom := dW (ode := (motion a r v, time)) (domain := domain ε)
    (pre := fun _ => True) (fun _ h => h)
    ((p, d, o, s, ω), 0) trivial ((pr, dr, or_, sr, ωr), t) hproj
  have hcurve' : curveError r ((p, d, o, s, ω, β), 0) = 0 := by
    dsimp [curveError]
    nlinarith [hcurve]
  rcases hready with ⟨rfl, hs, hd, hr, hinv⟩ | ⟨rfl, rfl, hd, hr⟩ |
    ⟨rfl, hs, hd, hr, rfl, hvis, hturn⟩
  · have hdr := motion_unit_preserved (-b) r ε v
      ((p, d, o, s, ω), 0) hd ((pr, dr, or_, sr, ωr), t) hproj
    apply And.intro hdom.2 (And.intro hdr (And.intro hr ?_))
    intro hpos
    have hstartpos : 0 < s := by
      have hspeed := speed_upper (-b) r ε s v (by linarith)
        ((p, d, o, s, ω), 0) le_rfl ((pr, dr, or_, sr, ωr), t) hproj
      linarith
    rcases hinv hstartpos with hclear | ⟨hvis, hturn⟩
    · exact Or.inl ((passive_response_clearance (-b) b V ε (-b) r hb hV (.inl rfl)
        le_rfl v p d o s ω hv hd
        (by simpa [Safe, stoppingMargin, hb.ne'] using hclear)
        ((pr, dr, or_, sr, ωr), t) hproj).2.2 hpos)
    · have hturnres : TurnSafe b γ r sr βr := by
        intro σ hσ
        have hpositive : 0 < angularResponse (-b) b ε γ r σ ((p, d, o, s, ω, β), 0) := by
          dsimp [angularResponse]
          simp only [neg_div, div_self hb.ne', neg_add_cancel, zero_mul, sub_zero]
          linarith [hturn σ hσ]
        exact angular_response (-b) b ε γ r σ v hb hr (.inl rfl) hσ
          ((p, d, o, s, ω, β), 0) ⟨hcurve', hpositive⟩ ((pr, dr, or_, sr, ωr, βr), t) hrun
      exact Or.inr ⟨hvis, hturnres⟩
  · have hzero := speed_upper 0 r ε 0 v le_rfl
      ((p, d, o, 0, ω), 0) le_rfl ((pr, dr, or_, sr, ωr), t) hproj
    have hdr := motion_unit_preserved 0 r ε v
      ((p, d, o, 0, ω), 0) hd ((pr, dr, or_, sr, ωr), t) hproj
    exact ⟨hdom.2, hdr, hr, fun hpos => False.elim (not_lt_of_ge hzero hpos)⟩
  · have hdr := motion_unit_preserved a r ε v
      ((p, d, o, s, ω), 0) hd ((pr, dr, or_, sr, ωr), t) hproj
    apply And.intro hdom.2 (And.intro hdr (And.intro hr ?_))
    intro hpos
    by_cases hvisible : 0 < visible
    · exact Or.inl ((passive_response_clearance a b V ε a r hb hV (.inr hA)
        le_rfl v p d o s ω hv hd (hvis hvisible)
        ((pr, dr, or_, sr, ωr), t) hproj).2.2 hpos)
    · have hturnres : TurnSafe b γ r sr βr := by
        intro σ hσ
        have hpositive : 0 < angularResponse a b ε γ r σ ((p, d, o, s, ω, 0), 0) := by
          dsimp [angularResponse, stoppingMargin] at hturn ⊢
          simp only [mul_zero, sub_zero, zero_mul, zero_div, add_zero] at hturn ⊢
          linarith
        exact angular_response a b ε γ r σ v hb hr (.inr hA) hσ
          ((p, d, o, s, ω, 0), 0) ⟨hcurve', hpositive⟩ ((pr, dr, or_, sr, ωr, βr), t) hrun
      exact Or.inr ⟨hvisible, hturnres⟩

noncomputable def orientStep (_A _b _V ε _γ a r _visible : ℝ)
    (v p d o : Vec2) (s ω β : ℝ) :=
  evolve (orientationMotion a r v, time) (orientationDomain ε) ((p, d, o, s, ω, β), 0)

@[spec] theorem orientStep_spec (A b V ε γ a r visible : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V) (v p d o : Vec2) (s ω β : ℝ) :
    ⦃v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 ∧ ω * r = s ∧
      OrientationReady A b V ε γ p d o s a r β visible⦄
      orientStep A b V ε γ a r visible v p d o s ω β
    ⦃fun ((p, d, o, s, _ω, β), _t) => OrientationInv b V γ p d o s r β visible⦄ := by
  constructor
  rintro ⟨hv, hcurve, hready⟩
  exact orientation_step A b V ε γ a r visible hA hb hV v p d o s ω β hv hcurve hready

noncomputable def dwpos' (A b V ε γ : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r β visible : ℝ) :
    SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2 × ℝ × ℝ)
    requires OrientationInv b V γ p d o s r β visible
    ensures (p, d, o, s, _ω, r, _v, β, visible) => OrientationInv b V γ p d o s r β visible
    := do
  let mut (p, d, o, s, ω, r, v, β, visible) := (p, d, o, s, ω, r, v, β, visible)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => OrientationInv b V γ p d o s r β visible do
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new, β_new, visible_new) ←
      orientControl A b V ε γ p d o s ω r β visible
    ω := ω_new
    r := r_new
    o := o_new
    β := β_new
    visible := visible_new
    ω ← choose ℝ
    ensure (ω * r = s)
    let (res, _t) ← orientStep A b V ε γ a r visible v p d o s ω β
    (p, d, o, s, ω, β) := res
  return (p, d, o, s, ω, r, v, β, visible)

theorem dwpos_eq (A b V ε γ : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r β visible : ℝ) :
    dwpos A b V ε γ p d o v s ω r β visible =
      dwpos' A b V ε γ hA hb hV p d o v s ω r β visible := by rfl

theorem orientation_safe (b V γ : ℝ) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o : Vec2) (s r β visible : ℝ) :
    OrientationInv b V γ p d o s r β visible →
      0 < s → 0 < distanceSq p o ∨ (¬0 < visible ∧ |β| < γ) := by
  rintro ⟨hs, hd, hr, hinv⟩ hpos
  rcases hinv hpos with hclear | ⟨hvis, hturn⟩
  · exact Or.inl (passive_separated b V hb hV p d o s ⟨hs, hd, fun _ => hclear⟩ hpos)
  · have hstop : 0 ≤ stopDist b s := div_nonneg (sq_nonneg s) (by positivity)
    have hp := hturn 1 (.inl rfl)
    have hn := hturn (-1) (.inr rfl)
    have hab : |r * β| < γ * |r| := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    rw [abs_mul] at hab
    have hβ : |β| < γ := by
      have hrpos := abs_pos.mpr hr
      nlinarith
    exact Or.inr ⟨hvis, hβ⟩

/-- Journal Theorem 4 / archive "Theorem 4: Passive orientation safety". -/
theorem dwpos_safe :
    ∀ A b V ε γ p d o v s ω r β visible,
      Bounds A b V ε → 0 < γ →
      (Initial p d o s ∧ β = 0 ∧ r ≠ 0) →
        ∀ res ∈ SetM.run (dwpos A b V ε γ p d o v s ω r β visible),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          let β_res := res.2.2.2.2.2.2.2.1
          let visible_res := res.2.2.2.2.2.2.2.2
          0 < s_res → 0 < distanceSq p_res o_res ∨
            (¬0 < visible_res ∧ |β_res| < γ) := by
  intro A b V ε γ p d o v s ω r β visible hbounds _hγ hinit res hrun
  rw [dwpos_eq A b V ε γ hbounds.1 hbounds.2.1 hbounds.2.2.1] at hrun
  apply orientation_safe b V γ hbounds.2.1 hbounds.2.2.1 _ _ _ _ _ _ _
  apply (dwpos'.spec A b V ε γ hbounds.1 hbounds.2.1 hbounds.2.2.1
    p d o v s ω r β visible).le_wp ?_ res hrun
  rcases hinit with ⟨⟨rfl, _, hd⟩, _, hr⟩
  exact ⟨le_rfl, hd, hr, by simp⟩

theorem passiveResponse_offset_preserved (M b V ε a r σ C : ℝ) (v : Vec2) (i : Fin 2)
    (hb : 0 < b) (hV : 0 ≤ V) (hM : M = -b ∨ 0 ≤ M) (ha : a ≤ M)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hσ : σ = 1 ∨ σ = -1) :
    (fun st => UnitDirection st.1.2.1 ∧ C < passiveResponse M b V ε σ i st)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun st => UnitDirection st.1.2.1 ∧ C < passiveResponse M b V ε σ i st) := by
  apply dC (cut := fun st => UnitDirection st.1.2.1)
  · exact fun st h => motion_unit_preserved a r ε v st h.1
  · intro st h res hrun
    have hdom := dW (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
      (pre := fun _ => True) (fun _ h => h) st trivial res hrun
    apply And.intro hdom.2
    apply sub_pos.mp
    apply dIgt (ode := (motion a r v, time))
      (domain := fun st => domain ε st ∧ UnitDirection st.1.2.1)
      (pre := fun st => C < passiveResponse M b V ε σ i st)
      (fun st => passiveResponse M b V ε σ i st - C)
      (fun ((_p, d, _o, s, _ω), t) => s * (σ * d i + 1) + (V - σ * v i) +
        (M - a) / b * (s + V + (M + b) * (ε - t)))
      (fun path I ho hD t ht =>
        (passiveResponse_hasPrime M b V ε a r σ hb.ne' v i
          (fun st => domain ε st ∧ UnitDirection st.1.2.1) path I ho hD t ht).sub_const C)
      (fun _ h => sub_pos.mpr h) ?_ st h.2 res hrun
    intro st h
    have hMb : 0 ≤ M + b := hM.elim (fun h => by simp [h]) (fun h => by linarith)
    exact add_nonneg
      (add_nonneg (mul_nonneg h.1.2 (signed_direction_nonneg σ i st.1.2.1 hσ h.2))
        (velocity_component_bound V σ v i hV hv hσ))
      (mul_nonneg (div_nonneg (sub_nonneg.mpr ha) hb.le)
        (add_nonneg (add_nonneg h.1.2 hV) (mul_nonneg hMb (sub_nonneg.mpr h.1.1))))

@[reducible]
def FriendlyInv (b V C : ℝ) (p d o : Vec2) (s : ℝ) : Prop :=
  0 ≤ s ∧ UnitDirection d ∧
    (0 < s → stopDist b s + V * s / b + C < infNorm (p - o))

theorem friendly_clearance (M b V ε a r C : ℝ) (hb : 0 < b) (hV : 0 ≤ V)
    (hM : M = -b ∨ 0 ≤ M) (ha : a ≤ M) (v p d o : Vec2) (s ω : ℝ)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hd : UnitDirection d)
    (hsafe : stoppingMargin M b V ε s + C < infNorm (p - o)) :
    ∀ res ∈ SetM.run (evolve (motion a r v, time) (domain ε) ((p, d, o, s, ω), 0)),
      let ((pr, dr, or_, sr, _ω), _t) := res
      FriendlyInv b V C pr dr or_ sr := by
  obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness (stoppingMargin M b V ε s + C) (p - o) hsafe
  have hstart : C < passiveResponse M b V ε σ i ((p, d, o, s, ω), 0) := by
    dsimp [passiveResponse, stoppingMargin] at hmargin ⊢
    simp only [sub_zero] at hmargin ⊢
    linarith
  rintro ⟨⟨pr, dr, or_, sr, ωr⟩, t⟩ hrun
  have h := passiveResponse_offset_preserved M b V ε a r σ C v i hb hV hM ha hv hσ
    ((p, d, o, s, ω), 0) ⟨hd, hstart⟩ ((pr, dr, or_, sr, ωr), t) hrun
  have hdom := dW (ode := (motion a r v, time)) (domain := domain ε)
    (pre := fun _ => True) (fun _ h => h)
    ((p, d, o, s, ω), 0) trivial ((pr, dr, or_, sr, ωr), t) hrun
  have hreserve : 0 ≤ (M / b + 1) * (M / 2 * (ε - t) ^ 2 + (ε - t) * (sr + V)) :=
    hM.elim (fun heq => by simp [heq, hb.ne'])
      (fun hM => mul_nonneg (add_nonneg (div_nonneg hM hb.le) (by norm_num))
        (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
          (mul_nonneg (sub_nonneg.mpr hdom.1) (add_nonneg hdom.2 hV))))
  have hle := signed_le_infNorm (pr - or_) i σ hσ
  exact ⟨hdom.2, h.1, fun _ => by dsimp [passiveResponse] at h; dsimp at hle; linarith [h.2]⟩

theorem stopped_friendly (b V C ε a r : ℝ) (v : Vec2) (ha : a ≤ 0) :
    (fun ((_p, d, _o, s, _ω), _t) => s = 0 ∧ UnitDirection d)
    [[evolve (motion a r v, time) (domain ε)]]
    (fun ((p, d, o, s, _ω), _t) => FriendlyInv b V C p d o s) := by
  intro st h res hrun
  have hspeed := speed_upper a r ε 0 v ha st h.1.le res hrun
  have hdom := dW (ode := (motion a r v, time)) (domain := domain ε)
    (pre := fun _ => True) (fun _ h => h) st trivial res hrun
  exact ⟨hdom.2, motion_unit_preserved a r ε v st h.2 res hrun,
    fun hpos => False.elim (not_lt_of_ge hspeed hpos)⟩

@[reducible]
def FriendlyReady (A b V ε C : ℝ) (p d o : Vec2) (s a : ℝ) : Prop :=
  (a = -b ∧ FriendlyInv b V C p d o s) ∨
  (s = 0 ∧ a = 0 ∧ UnitDirection d) ∨
  (a = A ∧ UnitDirection d ∧ stoppingMargin A b V ε s + C < infNorm (p - o))

noncomputable def friendlyControl (A b V Ω ε C : ℝ) (p _d o : Vec2) (s sm ω r : ℝ) :=
  ctrl_r b Ω (pure A) (fun p o s _ => stoppingMargin A b V ε s + C < infNorm (p - o)) p o s sm ω r

noncomputable def friendlyDyn (_A _b _V ε _C a r : ℝ) (v p d o : Vec2) (s ω : ℝ) :=
  dyn ε a r v p d o s ω

@[spec] theorem friendlyControl_spec (A b V Ω ε C : ℝ) (p d o : Vec2) (s sm ω r : ℝ) :
    ⦃sm = s ∧ FriendlyInv b V C p d o s⦄ friendlyControl A b V Ω ε C p d o s sm ω r
    ⦃fun (a, _ω, _r, o) => FriendlyReady A b V ε C p d o s a⦄ := by
  unfold friendlyControl ctrl_r
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

@[spec] theorem friendlyDyn_spec (A b V ε C a r : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (v p d o : Vec2) (s ω : ℝ) :
    ⦃v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 ∧ FriendlyReady A b V ε C p d o s a⦄
      friendlyDyn A b V ε C a r v p d o s ω
    ⦃fun (p, d, o, s, _ω) => FriendlyInv b V C p d o s⦄ := by
  unfold friendlyDyn dyn
  vcgen (errorOnMissingSpec := false)
  rename_i hpre
  simp only [SetM.wp_pure, binderNameHint]
  rcases hpre with ⟨hv, hready⟩
  rcases hready with ⟨rfl, hs, hd, hclear⟩ | ⟨rfl, rfl, hd⟩ | ⟨rfl, hd, hsafe⟩
  · by_cases hpos : 0 < s
    · exact friendly_clearance (-b) b V ε (-b) r C hb hV (.inl rfl) le_rfl v p d o s ω hv hd
        (by simpa [stoppingMargin, hb.ne'] using hclear hpos)
    · exact stopped_friendly b V C ε (-b) r v (by linarith)
        ((p, d, o, s, ω), 0) ⟨le_antisymm (le_of_not_gt hpos) hs, hd⟩
  · exact stopped_friendly b V C ε 0 r v le_rfl ((p, d, o, 0, ω), 0) ⟨rfl, hd⟩
  · exact friendly_clearance a b V ε a r C hb hV (.inr hA) le_rfl v p d o s ω hv hd hsafe

noncomputable def dwpfs' (A b bo τ V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ × Vec2)
    requires FriendlyInv b V (friendlyMargin bo τ V) p d o s ∧ v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2
    ensures (p, d, o, s, _ω, _r, v) =>
      FriendlyInv b V (friendlyMargin bo τ V) p d o s ∧ v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        FriendlyInv b V (friendlyMargin bo τ V) p d o s ∧ v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 do
    let (pMeasured, sMeasured) ← pure (p, s)
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new) ←
      friendlyControl A b V Ω ε (friendlyMargin bo τ V) pMeasured d o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← pure a
    (p, d, o, s, ω) ← friendlyDyn A b V ε (friendlyMargin bo τ V) aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

theorem dwpfs_eq (A b bo τ V Ω ε : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V)
    (p d o v : Vec2) (s ω r : ℝ) :
    dwpfs A b bo τ V Ω ε p d o v s ω r = dwpfs' A b bo τ V Ω ε hA hb hV p d o v s ω r := by
  rfl

/-! Successful finite runs are needed for the archive's diamond modalities.
These membership lemmas complement the demonic `vcgen` safety contracts. -/

theorem run_bind {α β : Type} (p : SetM α) (f : α → SetM β) (x : α) (y : β)
    (hx : x ∈ SetM.run p) (hy : y ∈ SetM.run (f x)) : y ∈ SetM.run (p >>= f) := by
  change y ∈ ⋃ z ∈ SetM.run p, SetM.run (f z)
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hy⟩⟩

noncomputable def repeatStep {σ : Type} (step : σ → SetM σ) : ℕ → σ → SetM σ
  | 0, x => pure x
  | n + 1, x => do
      let y ← step x
      repeatStep step n y

theorem forIn_list_repeat {α σ : Type} (step : σ → SetM σ) (xs : List α) (x : σ) :
    forIn xs x (fun _ st => do let next ← step st; pure (ForInStep.yield next)) =
      repeatStep step xs.length x := by
  induction xs generalizing x with
  | nil => simp [repeatStep]
  | cons a xs ih =>
    simp only [List.forIn_cons, bind_assoc, pure_bind]
    simp only [ih, List.length_cons, repeatStep]

theorem forIn_range_repeat {σ : Type} (step : σ → SetM σ) (n : ℕ) (x : σ) :
    forIn [:n] x (fun _ st => do let next ← step st; pure (ForInStep.yield next)) =
      repeatStep step n x := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_repeat]
  simp [Std.Legacy.Range.size]

noncomputable def finiteLoop {σ : Type} (step : σ → SetM σ) (x : σ) : SetM σ := do
  let n ← choose ℕ
  repeatStep step n x

def Reach {σ : Type} (step : σ → SetM σ) (x y : σ) : Prop :=
  ∃ n, y ∈ SetM.run (repeatStep step n x)

theorem reach_refl {σ : Type} (step : σ → SetM σ) (x : σ) : Reach step x x :=
  ⟨0, Set.mem_singleton x⟩

theorem reach_prepend {σ : Type} (step : σ → SetM σ) (x y z : σ)
    (hxy : y ∈ SetM.run (step x)) (hyz : Reach step y z) : Reach step x z := by
  obtain ⟨n, hn⟩ := hyz
  exact ⟨n + 1, run_bind _ _ y z hxy hn⟩

theorem reach_run {σ : Type} (step : σ → SetM σ) (x y : σ)
    (h : Reach step x y) : y ∈ SetM.run (finiteLoop step x) := by
  obtain ⟨n, hn⟩ := h
  exact run_bind _ _ n y (Set.mem_univ n) hn

noncomputable def obstacleStep (bo V ε : ℝ) (do_ : Vec2) (st : Vec2 × ℝ) : SetM (Vec2 × ℝ) := do
  let ao ← choose ℝ
  ensure (-bo ≤ ao ∧ st.2 + ao * ε ≤ V)
  let (res, _t) ← evolve (obstacleMotion do_ ao, time) (obstacleDomain ε) (st, 0)
  return res

theorem obstacle_eq_loop (bo V ε : ℝ) (do_ o : Vec2) (so : ℝ) :
    obstacle bo V ε do_ o so = finiteLoop (obstacleStep bo V ε do_) (o, so) := by
  unfold obstacle finiteLoop
  simp only [← forIn_range_repeat]
  simp only [obstacleStep, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]

theorem obstacle_brake_evolution (bo ε so T : ℝ) (do_ o : Vec2)
    (hbo : 0 < bo) (hT : 0 ≤ T) (hTε : T ≤ ε) (hstop : 0 ≤ so - bo * T) :
    ((o + (so * T - bo / 2 * T ^ 2) • do_, so - bo * T), T) ∈
      SetM.run (evolve (obstacleMotion do_ (-bo), time) (obstacleDomain ε) ((o, so), 0)) := by
  apply SemanticODE.mem_evolveSemantic _ (obstacleDomain ε) ((o, so), 0) T
    (fun t => ((o + (so * t - bo / 2 * t ^ 2) • do_, so - bo * t), t)) hT
  constructor
  · simp
  · constructor
    · intro t ht
      exact ⟨by nlinarith [ht.2], ht.2.trans hTε⟩
    · constructor
      · intro t ht
        have hq : HasDerivAt (fun τ : ℝ => so * τ - bo / 2 * τ ^ 2) (so - bo * t) t := by
          convert ((hasDerivAt_id t).const_mul so).sub
            (((hasDerivAt_id t).pow 2).const_mul (bo / 2)) using 1
          · rfl
          · dsimp
            ring
        have hx := (hasDerivAt_const t o).add (hq.smul_const do_)
        have hs := (hasDerivAt_const t so).sub ((hasDerivAt_id t).const_mul bo)
        simpa [obstacleMotion] using (hx.prodMk hs).hasDerivWithinAt (s := Set.Icc 0 T)
      · intro t ht
        exact (hasDerivAt_id t).hasDerivWithinAt

theorem obstacle_brake_step (bo V ε so T : ℝ) (do_ o : Vec2)
    (hbo : 0 < bo) (hε : 0 ≤ ε) (hV : so ≤ V)
    (hT : 0 ≤ T) (hTε : T ≤ ε) (hstop : 0 ≤ so - bo * T) :
    (o + (so * T - bo / 2 * T ^ 2) • do_, so - bo * T) ∈
      SetM.run (obstacleStep bo V ε do_ (o, so)) := by
  unfold obstacleStep
  apply run_bind _ _ (-bo) _ (Set.mem_univ _)
  apply run_bind _ _ () _ (show () ∈ SetM.run (ensure (-bo ≤ -bo ∧ so + -bo * ε ≤ V)) from
    ⟨le_rfl, by nlinarith⟩)
  apply run_bind _ _ ((o + (so * T - bo / 2 * T ^ 2) • do_, so - bo * T), T) _
    (obstacle_brake_evolution bo ε so T do_ o hbo hT hTε hstop)
  exact Set.mem_singleton _

theorem obstacle_brake_reach (bo V ε : ℝ) (do_ : Vec2) (hbo : 0 < bo) (hε : 0 < ε)
    (n : ℕ) : ∀ (o : Vec2) (so : ℝ), 0 ≤ so → so ≤ V → so ≤ (n : ℝ) * bo * ε →
      Reach (obstacleStep bo V ε do_) (o, so) (o + stopDist bo so • do_, 0) := by
  induction n with
  | zero =>
    intro o so hs hV hn
    have hzero : so = 0 := by norm_num at hn; linarith
    simpa [hzero, stopDist] using reach_refl (obstacleStep bo V ε do_) (o, so)
  | succ n ih =>
    intro o so hs hV hn
    by_cases hshort : so ≤ bo * ε
    · have hTε : so / bo ≤ ε := (div_le_iff₀ hbo).mpr (by nlinarith)
      have hstop : so - bo * (so / bo) = 0 := by field_simp; ring
      have hdist : so * (so / bo) - bo / 2 * (so / bo) ^ 2 = stopDist bo so := by
        unfold stopDist
        field_simp
        ring
      have hstep := obstacle_brake_step bo V ε so (so / bo) do_ o hbo hε.le hV
        (div_nonneg hs hbo.le) hTε hstop.ge
      rw [hdist, hstop] at hstep
      exact reach_prepend _ _ _ _ hstep (reach_refl _ _)
    · have hsnext : 0 ≤ so - bo * ε := by linarith
      have hVnext : so - bo * ε ≤ V := by nlinarith
      have hnnext : so - bo * ε ≤ (n : ℝ) * bo * ε := by
        push_cast at hn
        nlinarith
      have hstep := obstacle_brake_step bo V ε so ε do_ o hbo hε.le hV hε.le le_rfl hsnext
      have hrec := ih (o + (so * ε - bo / 2 * ε ^ 2) • do_) (so - bo * ε) hsnext hVnext hnnext
      have hdist : so * ε - bo / 2 * ε ^ 2 + stopDist bo (so - bo * ε) = stopDist bo so := by
        unfold stopDist
        field_simp
        ring
      rw [add_assoc, ← add_smul, hdist] at hrec
      exact reach_prepend _ _ _ _ hstep hrec

theorem obstacle_stop_run (bo V ε : ℝ) (do_ o : Vec2) (so : ℝ)
    (hbo : 0 < bo) (hε : 0 < ε) (hs : 0 ≤ so) (hV : so ≤ V) :
    (o + stopDist bo so • do_, 0) ∈ SetM.run (obstacle bo V ε do_ o so) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (so / (bo * ε))
  have hcap : so ≤ (n : ℝ) * bo * ε := by
    have h := (div_lt_iff₀ (mul_pos hbo hε)).mp hn
    nlinarith
  rw [obstacle_eq_loop]
  exact reach_run _ _ _ (obstacle_brake_reach bo V ε do_ hbo hε n o so hs hV hcap)

theorem clearance_sq (C : ℝ) (p o : Vec2) (hC : 0 ≤ C)
    (hgap : C < infNorm (p - o)) : C ^ 2 < distanceSq p o := by
  obtain ⟨i, σ, hσ, hmargin⟩ := signed_witness C (p - o) hgap
  fin_cases i <;> rcases hσ with rfl | rfl <;>
    dsimp [distanceSq] at * <;>
    nlinarith [sq_nonneg (p 0 - o 0), sq_nonneg (p 1 - o 1)]

theorem stopped_obstacle_separated (K : ℝ) (p o do_ : Vec2) (hd : UnitDirection do_)
    (hgap : K ^ 2 < distanceSq p o) : 0 < distanceSq p (o + K • do_) := by
  by_contra h
  have hx : p 0 - (o + K • do_) 0 = 0 := by
    dsimp [distanceSq] at h ⊢
    nlinarith [sq_nonneg (p 1 - (o + K • do_) 1)]
  have hy : p 1 - (o + K • do_) 1 = 0 := by
    dsimp [distanceSq] at h ⊢
    nlinarith [sq_nonneg (p 0 - (o + K • do_) 0)]
  have hdist : distanceSq p o = K ^ 2 := by
    calc
      distanceSq p o = K ^ 2 * (do_ 0 ^ 2 + do_ 1 ^ 2) := by
        dsimp [distanceSq] at hx hy ⊢
        rw [show p 0 = o 0 + K * do_ 0 by linarith,
          show p 1 = o 1 + K * do_ 1 by linarith]
        ring
      _ = K ^ 2 := by rw [hd, mul_one]
  linarith

theorem obstacle_friendly_stop (bo τ V ε : ℝ) (p o v do_ : Vec2) (so : ℝ)
    (hbo : 0 < bo) (hτ : 0 ≤ τ) (hV : 0 ≤ V) (hε : 0 < ε)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2) (hs : 0 ≤ so)
    (hsq : so ^ 2 = v 0 ^ 2 + v 1 ^ 2) (hcons : so • do_ = v)
    (hgap : friendlyMargin bo τ V ^ 2 < distanceSq p o) :
    ∃ res ∈ SetM.run (obstacle bo V ε do_ o so), 0 < distanceSq p res.1 ∧ res.2 = 0 := by
  have hsoV : so ≤ V := by nlinarith
  apply Exists.intro (o + stopDist bo so • do_, 0)
  apply And.intro (obstacle_stop_run bo V ε do_ o so hbo hε hs hsoV)
  apply And.intro ?_ rfl
  by_cases hzero : so = 0
  · simp [hzero, stopDist]
    nlinarith [sq_nonneg (friendlyMargin bo τ V)]
  · have hc₀ := congrArg (fun u : Vec2 => u 0) hcons
    have hc₁ := congrArg (fun u : Vec2 => u 1) hcons
    have hmul : so ^ 2 * (do_ 0 ^ 2 + do_ 1 ^ 2 - 1) = 0 := by
      dsimp at hc₀ hc₁
      nlinarith [congrArg (fun x : ℝ => x ^ 2) hc₀, congrArg (fun x : ℝ => x ^ 2) hc₁]
    have hd : UnitDirection do_ := sub_eq_zero.mp
      ((mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hzero))
    have hK : 0 ≤ stopDist bo so := div_nonneg (sq_nonneg so) (by positivity)
    have hmono : stopDist bo so ≤ stopDist bo V := by unfold stopDist; gcongr
    have hC : stopDist bo so ≤ friendlyMargin bo τ V := by
      dsimp [friendlyMargin, stopDist] at hmono ⊢
      linarith [mul_nonneg hτ hV]
    exact stopped_obstacle_separated (stopDist bo so) p o do_ hd (by nlinarith)

/-- Journal Theorem 3: the coarse safety invariant and the refined obstacle diamond. -/
theorem dwpfs_safe :
    ∀ A b bo τ V Ω ε p d o v s ω r,
      Bounds A b V ε → 0 ≤ τ → 0 < bo → FriendlyInitial bo τ V p d o v s →
        ∀ res ∈ SetM.run (dwpfs A b bo τ V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          let v_res := res.2.2.2.2.2.2
          PassiveFriendlySafe bo τ V ε p_res o_res v_res s_res := by
  intro A b bo τ V Ω ε p d o v s ω r hbounds hτ hbo hinit res hrun
  rw [dwpfs_eq A b bo τ V Ω ε hbounds.1 hbounds.2.1 hbounds.2.2.1] at hrun
  have hinv := (dwpfs'.spec A b bo τ V Ω ε hbounds.1 hbounds.2.1 hbounds.2.2.1
    p d o v s ω r).le_wp (show FriendlyInv b V (friendlyMargin bo τ V) p d o s ∧
      v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 from by
        rcases hinit with ⟨rfl, _, hv, hd⟩
        exact ⟨⟨le_rfl, hd, by simp⟩, hv⟩) res hrun
  constructor
  · intro hpos
    apply clearance_sq (friendlyMargin bo τ V) _ _
      (add_nonneg (div_nonneg (sq_nonneg V) (by positivity)) (mul_nonneg hτ hbounds.2.2.1))
    have hclear := hinv.1.2.2 hpos
    have hstop : 0 ≤ stopDist b res.2.2.2.1 :=
      div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hbounds.2.1.le)
    have hmove := div_nonneg (mul_nonneg hbounds.2.2.1 hinv.1.1) hbounds.2.1.le
    linarith
  · rintro so do_ ⟨hs, hsq, hcons, hgap⟩
    exact obstacle_friendly_stop bo τ V ε _ _ _ do_ so hbo hτ hbounds.2.2.1 hbounds.2.2.2
      hinv.2 hs hsq hcons hgap

noncomputable def lineSpeedError (a s₀ : ℝ) : (ℝ × ℝ) × ℝ → ℝ :=
  fun ((_p, s), t) => s - s₀ - a * t

noncomputable def linePositionError (a p₀ s₀ : ℝ) : (ℝ × ℝ) × ℝ → ℝ :=
  fun ((p, _s), t) => p - p₀ - s₀ * t - a / 2 * t ^ 2

theorem line_exact (a ε p₀ s₀ : ℝ) :
    ∀ res ∈ SetM.run (evolve (lineMotion a, time) (lineDomain ε) ((p₀, s₀), 0)),
      let ((p, s), t) := res
      0 ≤ t ∧ t ≤ ε ∧ 0 ≤ s ∧ s = s₀ + a * t ∧ p = p₀ + s₀ * t + a / 2 * t ^ 2 := by
  have hsprime : HasPrime (Evolvable.denotation (lineMotion a, time)) (lineDomain ε)
      (lineSpeedError a s₀) (fun _ => 0) := by
    ode_deriv [lineSpeedError, lineMotion, time]
  have hspeed := dIeq (ode := (lineMotion a, time)) (domain := lineDomain ε)
    (pre := fun st => lineSpeedError a s₀ st = 0)
    (lineSpeedError a s₀) (fun _ => 0) hsprime (fun _ h => h) (fun _ _ => rfl)
  have hposition :
      (fun st => lineSpeedError a s₀ st = 0 ∧ linePositionError a p₀ s₀ st = 0)
      [[evolve (lineMotion a, time) (lineDomain ε)]]
      (fun st => linePositionError a p₀ s₀ st = 0) := by
    apply dC (cut := fun st => lineSpeedError a s₀ st = 0)
    · exact fun st h => hspeed st h.1
    · apply dIeq (linePositionError a p₀ s₀) (lineSpeedError a s₀)
      · ode_deriv [linePositionError, lineSpeedError, lineMotion, time]
        grind
      · exact fun _ h => h.2
      · exact fun _ h => h.2
  have htprime : HasPrime (Evolvable.denotation (lineMotion a, time)) (lineDomain ε)
      (fun st => st.2) (fun _ => 1) := by ode_deriv [lineMotion, time]
  rintro ⟨⟨p, s⟩, t⟩ hrun
  have hs := hspeed ((p₀, s₀), 0) (by simp [lineSpeedError]) ((p, s), t) hrun
  have hp := hposition ((p₀, s₀), 0) (by simp [lineSpeedError, linePositionError]) ((p, s), t) hrun
  have ht := dIge (ode := (lineMotion a, time)) (domain := lineDomain ε)
    (pre := fun st => 0 ≤ st.2) (fun st => st.2) (fun _ => 1) htprime
    (fun _ h => h) (fun _ _ => by norm_num) ((p₀, s₀), 0) le_rfl ((p, s), t) hrun
  have hdom := dW (ode := (lineMotion a, time)) (domain := lineDomain ε)
    (pre := fun _ => True) (fun _ h => h) ((p₀, s₀), 0) trivial ((p, s), t) hrun
  exact ⟨ht, hdom.1, hdom.2, by dsimp [lineSpeedError] at hs; linarith,
    by dsimp [linePositionError] at hp; linarith⟩

@[reducible]
def WaypointInv (b g Δg Vg p s : ℝ) : Prop :=
  0 ≤ s ∧ s ≤ Vg ∧ p + stopDist b s < g + Δg

@[reducible]
def WaypointReady (A b ε g Δg Vg p s a : ℝ) : Prop :=
  (a = -b ∧ WaypointInv b g Δg Vg p s) ∨
  (s = 0 ∧ a = 0 ∧ WaypointInv b g Δg Vg p s) ∨
  (a = A ∧ 0 ≤ s ∧ p + stoppingMargin A b 0 ε s < g + Δg ∧ s + A * ε ≤ Vg) ∨
  (p ≤ g - Δg ∧ 0 ≤ s ∧ s ≤ Vg ∧ a ≤ (Vg - s) / ε)

noncomputable def waypointCtrl (A b ε g Δg Vg p s : ℝ) :=
  waypointControl A b ε g Δg Vg p s

@[spec] theorem waypointCtrl_spec (A b ε g Δg Vg p s : ℝ) :
    ⦃WaypointInv b g Δg Vg p s⦄ waypointCtrl A b ε g Δg Vg p s
    ⦃fun a => WaypointReady A b ε g Δg Vg p s a⦄ := by
  unfold waypointCtrl waypointControl
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    · vcgen
      simp_all
    · vcgen
      constructor
      all_goals vcgen
      all_goals simp_all

theorem waypoint_phase (A b ε g Δg Vg p s a : ℝ)
    (hbounds : WaypointBounds A b ε Δg Vg)
    (hready : WaypointReady A b ε g Δg Vg p s a) :
    ∀ res ∈ SetM.run (evolve (lineMotion a, time) (lineDomain ε) ((p, s), 0)),
      WaypointInv b g Δg Vg res.1.1 res.1.2 := by
  rcases hbounds with ⟨hA, hb, hε, hVg, hΔg⟩
  have hV : 0 ≤ Vg := by nlinarith
  have hstopV : 0 ≤ stopDist b Vg := div_nonneg (sq_nonneg _) (by positivity)
  have hΔ : 0 < Δg := by nlinarith
  rintro ⟨⟨pr, sr⟩, t⟩ hrun
  obtain ⟨ht, htε, hsr, hs, hp⟩ := line_exact a ε p s ((pr, sr), t) hrun
  rcases hready with ⟨rfl, hs₀, hsV, hclear⟩ | ⟨rfl, rfl, hs₀, hsV, hclear⟩ |
    ⟨rfl, hs₀, hclear, hsV⟩ | ⟨hpg, hs₀, hsV, haV⟩
  · have hbarrier : pr + stopDist b sr = p + stopDist b s := by
      rw [hp, hs]
      unfold stopDist
      field_simp
      ring
    exact ⟨hsr, by nlinarith, by linarith⟩
  · simp only [zero_mul, add_zero] at hs hp
    simpa [WaypointInv, hs, hp] using And.intro hsr (And.intro hsV hclear)
  · have hreserve : 0 ≤ (a / b + 1) * (a / 2 * (ε - t) ^ 2 + (ε - t) * sr) :=
      mul_nonneg (add_nonneg (div_nonneg hA.le hb.le) (by norm_num))
        (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
          (mul_nonneg (sub_nonneg.mpr htε) hsr))
    have hbarrier : pr + stopDist b sr +
        (a / b + 1) * (a / 2 * (ε - t) ^ 2 + (ε - t) * sr) =
        p + stoppingMargin a b 0 ε s := by
      rw [hp, hs]
      unfold stoppingMargin stopDist
      field_simp
      ring
    exact ⟨hsr, by nlinarith, by linarith⟩
  · have hterminal : s + a * ε ≤ Vg := by
      have h := (le_div_iff₀ hε).mp haV
      linarith
    have hsrV : sr ≤ Vg := by
      by_cases ha : 0 ≤ a
      · nlinarith
      · nlinarith
    have hpr : pr ≤ p + Vg * ε := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hsV),
        mul_nonneg ht (sub_nonneg.mpr hsrV), mul_nonneg hV (sub_nonneg.mpr htε)]
    have hstop : stopDist b sr ≤ stopDist b Vg := by unfold stopDist; gcongr
    exact ⟨hsr, hsrV, by linarith⟩

noncomputable def waypointDyn (_A _b ε _g _Δg _Vg p s a : ℝ) :=
  evolve (lineMotion a, time) (lineDomain ε) ((p, s), 0)

@[spec] theorem waypointDyn_spec (A b ε g Δg Vg p s a : ℝ)
    (hbounds : WaypointBounds A b ε Δg Vg) :
    ⦃WaypointReady A b ε g Δg Vg p s a⦄ waypointDyn A b ε g Δg Vg p s a
    ⦃fun ((p, s), _t) => WaypointInv b g Δg Vg p s⦄ :=
  ⟨waypoint_phase A b ε g Δg Vg p s a hbounds⟩

noncomputable def dwwp' (A b ε g Δg Vg p s : ℝ) (hbounds : WaypointBounds A b ε Δg Vg) :
    SetM (ℝ × ℝ)
    requires WaypointInv b g Δg Vg p s
    ensures (p, s) => WaypointInv b g Δg Vg p s
    := do
  let mut (p, s) := (p, s)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => WaypointInv b g Δg Vg p s do
    let a ← waypointCtrl A b ε g Δg Vg p s
    let (res, _t) ← waypointDyn A b ε g Δg Vg p s a
    (p, s) := res
  return (p, s)

theorem dwwp_eq (A b ε g Δg Vg p s : ℝ) (hbounds : WaypointBounds A b ε Δg Vg) :
    dwwp A b ε g Δg Vg p s = dwwp' A b ε g Δg Vg p s hbounds := by rfl

theorem line_evolution (a ε p s T : ℝ) (hs : 0 ≤ s) (hT : 0 ≤ T) (hTε : T ≤ ε)
    (hsT : 0 ≤ s + a * T) :
    ((p + s * T + a / 2 * T ^ 2, s + a * T), T) ∈
      SetM.run (evolve (lineMotion a, time) (lineDomain ε) ((p, s), 0)) := by
  apply SemanticODE.mem_evolveSemantic _ (lineDomain ε) ((p, s), 0) T
    (fun t => ((p + s * t + a / 2 * t ^ 2, s + a * t), t)) hT
  constructor
  · simp
  · constructor
    · intro t ht
      apply And.intro (ht.2.trans hTε)
      by_cases ha : 0 ≤ a
      · nlinarith [mul_nonneg ha ht.1]
      · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (sub_nonneg.mpr ht.2)]
    · constructor
      · intro t ht
        have hp : HasDerivAt (fun τ : ℝ => p + s * τ + a / 2 * τ ^ 2) (s + a * t) t := by
          convert ((hasDerivAt_const t p).add ((hasDerivAt_id t).const_mul s)).add
            (((hasDerivAt_id t).pow 2).const_mul (a / 2)) using 1
          · rfl
          · dsimp
            ring
        have hs := (hasDerivAt_const t s).add ((hasDerivAt_id t).const_mul a)
        simpa [lineMotion] using (hp.prodMk hs).hasDerivWithinAt (s := Set.Icc 0 T)
      · intro t ht
        exact (hasDerivAt_id t).hasDerivWithinAt

noncomputable def waypointStep (A b ε g Δg Vg : ℝ) (st : ℝ × ℝ) : SetM (ℝ × ℝ) := do
  let a ← waypointControl A b ε g Δg Vg st.1 st.2
  let (res, _t) ← evolve (lineMotion a, time) (lineDomain ε) (st, 0)
  return res

theorem dwwp_eq_loop (A b ε g Δg Vg p s : ℝ) :
    dwwp A b ε g Δg Vg p s = finiteLoop (waypointStep A b ε g Δg Vg) (p, s) := by
  unfold dwwp finiteLoop
  simp only [← forIn_range_repeat]
  simp only [waypointStep, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]

theorem waypoint_arbitrary_control (A b ε g Δg Vg p s a : ℝ)
    (hp : p ≤ g - Δg) (hs : s ≤ Vg) (ha : -b ≤ a)
    (haV : a ≤ (Vg - s) / ε) (haA : a ≤ A) :
    a ∈ SetM.run (waypointControl A b ε g Δg Vg p s) := by
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply run_bind _ _ () _ (show () ∈ SetM.run (ensure (p ≤ g - Δg ∧ s ≤ Vg)) from ⟨hp, hs⟩)
  apply run_bind _ _ a _ (Set.mem_univ _)
  apply run_bind _ _ () _ (show () ∈ SetM.run (ensure (-b ≤ a ∧ a ≤ (Vg - s) / ε ∧ a ≤ A)) from
    ⟨ha, haV, haA⟩)
  exact Set.mem_singleton _

theorem waypoint_step_run (A b ε g Δg Vg p s a T : ℝ)
    (hctrl : a ∈ SetM.run (waypointControl A b ε g Δg Vg p s))
    (hs : 0 ≤ s) (hT : 0 ≤ T) (hTε : T ≤ ε) (hsT : 0 ≤ s + a * T) :
    (p + s * T + a / 2 * T ^ 2, s + a * T) ∈
      SetM.run (waypointStep A b ε g Δg Vg (p, s)) := by
  unfold waypointStep
  apply run_bind _ _ a _ hctrl
  apply run_bind _ _ ((p + s * T + a / 2 * T ^ 2, s + a * T), T) _
    (line_evolution a ε p s T hs hT hTε hsT)
  exact Set.mem_singleton _

theorem waypoint_coast_reach (A b ε g Δg Vg s : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hε : 0 < ε) (hs : 0 < s) (hsV : s ≤ Vg) (n : ℕ) :
    ∀ p : ℝ, g - Δg < p + (n : ℝ) * (s * ε) →
      ∃ pr, Reach (waypointStep A b ε g Δg Vg) (p, s) (pr, s) ∧ g - Δg < pr := by
  induction n with
  | zero =>
    intro p hp
    exact ⟨p, reach_refl _ _, by simpa using hp⟩
  | succ n ih =>
    intro p hp
    by_cases hdone : g - Δg < p
    · exact ⟨p, reach_refl _ _, hdone⟩
    · have hctrl := waypoint_arbitrary_control A b ε g Δg Vg p s 0
        (le_of_not_gt hdone) hsV (by linarith) (div_nonneg (sub_nonneg.mpr hsV) hε.le) hA
      have hstep := waypoint_step_run A b ε g Δg Vg p s 0 ε hctrl hs.le hε.le le_rfl (by linarith)
      simp only [zero_div, zero_mul, add_zero] at hstep
      obtain ⟨pr, hreach, hpr⟩ := ih (p + s * ε) (by push_cast at hp; linarith)
      exact ⟨pr, reach_prepend _ _ _ _ hstep hreach, hpr⟩

/-- Journal Theorem 11: universal waypoint bound and a successful run into the goal region. -/
theorem dwwp_live :
    ∀ A b ε g Δg Vg p s,
      WaypointBounds A b ε Δg Vg → (s = 0 ∧ p < g - Δg) →
        (∀ res ∈ SetM.run (dwwp A b ε g Δg Vg p s),
          let p_res := res.1
          p_res < g + Δg) ∧
        (∃ res ∈ SetM.run (dwwp A b ε g Δg Vg p s),
          let p_res := res.1
          g - Δg < p_res) := by
  intro A b ε g Δg Vg p s hbounds hinit
  rcases hinit with ⟨rfl, hp⟩
  have hA := hbounds.1
  have hb := hbounds.2.1
  have hε := hbounds.2.2.1
  have hVg := hbounds.2.2.2.1
  have hΔg := hbounds.2.2.2.2
  have hV : 0 ≤ Vg := by nlinarith
  have hstopV : 0 ≤ stopDist b Vg := div_nonneg (sq_nonneg _) (by positivity)
  have hΔ : 0 < Δg := by nlinarith
  constructor
  · intro res hrun
    rw [dwwp_eq A b ε g Δg Vg p 0 hbounds] at hrun
    have hinit : WaypointInv b g Δg Vg p 0 := by
      exact ⟨le_rfl, hV, by simpa [stopDist] using (show p < g + Δg by linarith)⟩
    have hinv := (dwwp'.spec A b ε g Δg Vg p 0 hbounds).le_wp hinit res hrun
    have hstop : 0 ≤ stopDist b res.2 := div_nonneg (sq_nonneg _) (by positivity)
    linarith [hinv.2.2]
  · have hctrl := waypoint_arbitrary_control A b ε g Δg Vg p 0 A hp.le hV
      (by linarith) ((le_div_iff₀ hε).mpr (by nlinarith)) le_rfl
    have hstep := waypoint_step_run A b ε g Δg Vg p 0 A ε hctrl le_rfl hε.le le_rfl
      (by positivity)
    simp only [zero_mul, add_zero, zero_add] at hstep
    have hu : 0 < A * ε := mul_pos hA hε
    have huV : A * ε ≤ Vg := by nlinarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((g - Δg - (p + A / 2 * ε ^ 2)) / (A * ε * ε))
    have hprogress : g - Δg < p + A / 2 * ε ^ 2 + (n : ℝ) * (A * ε * ε) := by
      have h := (div_lt_iff₀ (mul_pos hu hε)).mp hn
      linarith
    obtain ⟨pr, hreach, hpr⟩ := waypoint_coast_reach A b ε g Δg Vg (A * ε) hA.le hb hε hu huV
      n (p + A / 2 * ε ^ 2) hprogress
    apply Exists.intro (pr, A * ε)
    apply And.intro ?_ hpr
    rw [dwwp_eq_loop]
    exact reach_run _ _ _ (reach_prepend _ _ _ _ hstep hreach)

def intersectionProjection (robot : Bool) : (ℝ × ℝ × ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  fun ((p, s, o, v), t) => if robot then ((p, s), t) else ((o, v), t)

theorem intersection_projection (robot : Bool) (a ao ε Vmin p s o v : ℝ) (hVmin : 0 ≤ Vmin) :
    ∀ res ∈ SetM.run (evolve (intersectionMotion a ao, time) (intersectionDomain ε Vmin)
      ((p, s, o, v), 0)),
      intersectionProjection robot res ∈ SetM.run
        (evolve (lineMotion (if robot then a else ao), time) (lineDomain ε)
          (intersectionProjection robot ((p, s, o, v), 0))) := by
  exact (evolveSemantic_spec (Evolvable.denotation (intersectionMotion a ao, time))
    (intersectionDomain ε Vmin) ((p, s, o, v), 0)).le_wp (by
    intro T hT path hevol
    apply SemanticODE.mem_evolveSemantic _ (lineDomain ε)
      (intersectionProjection robot ((p, s, o, v), 0)) T
      (fun t => intersectionProjection robot (path t)) hT
    constructor
    · exact congrArg (intersectionProjection robot) hevol.1
    · constructor
      · intro t ht
        have h := hevol.2.1 t ht
        cases robot
        · exact ⟨h.1, hVmin.trans h.2.2⟩
        · exact ⟨h.1, h.2.1⟩
      · constructor
        · intro t ht
          have h := hevol.2.2.1 t ht
          cases robot
          · exact h.snd.snd.fst.prodMk h.snd.snd.snd
          · exact h.fst.prodMk h.snd.fst
        · cases robot <;> exact hevol.2.2.2)

@[reducible]
def Early (A p s o v : ℝ) : Prop := o + v * (-p / s) + A / 2 * (-p / s) ^ 2 < 0

@[reducible]
def Late (Vmin p s o : ℝ) : Prop := 0 < o + Vmin * (-p) / s

@[reducible]
def IntersectionInv (A b Vmin p s o v : ℝ) : Prop :=
  0 ≤ s ∧ Vmin ≤ v ∧
    (AfterX p o ∨ p + stopDist b s < 0 ∨ (0 < s ∧ (Early A p s o v ∨ Late Vmin p s o)))

theorem crossing_early (A p s o v a ao t pr sr or_ vr : ℝ)
    (hA : 0 ≤ A) (hs : 0 < s) (hv : 0 ≤ v) (ha : 0 ≤ a) (hao : ao ≤ A)
    (ht : 0 ≤ t) (hpr : pr ≤ 0)
    (hp : pr = p + s * t + a / 2 * t ^ 2) (hsp : sr = s + a * t)
    (ho : or_ = o + v * t + ao / 2 * t ^ 2) (hvr : vr = v + ao * t)
    (hearly : Early A p s o v) : Early A pr sr or_ vr := by
  have hsr : 0 < sr := by nlinarith [mul_nonneg ha ht]
  let T₀ := -p / s
  let T₁ := -pr / sr
  have hT₀eq : T₀ * s = -p := by dsimp [T₀]; field_simp
  have hT₁eq : T₁ * sr = -pr := by dsimp [T₁]; field_simp
  have hT₁ : 0 ≤ T₁ := div_nonneg (neg_nonneg.mpr hpr) hsr.le
  have htT₀ : t ≤ T₀ := by nlinarith [mul_nonneg ha (sq_nonneg t)]
  have hsum : t + T₁ ≤ T₀ := by
    have hprod := mul_nonneg (mul_nonneg ha ht) (show 0 ≤ T₀ - t / 2 by linarith)
    nlinarith
  have hT₀ : 0 ≤ T₀ := ht.trans htT₀
  have hfirst : or_ + vr * T₁ + A / 2 * T₁ ^ 2 ≤
      o + v * (t + T₁) + A / 2 * (t + T₁) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hao) (sq_nonneg t),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hao) ht) hT₁]
  have hsecond : o + v * (t + T₁) + A / 2 * (t + T₁) ^ 2 ≤
      o + v * T₀ + A / 2 * T₀ ^ 2 := by
    nlinarith [mul_nonneg hv (sub_nonneg.mpr hsum),
      mul_nonneg hA (mul_nonneg (sub_nonneg.mpr hsum) (by linarith : 0 ≤ T₀ + (t + T₁)))]
  exact hfirst.trans_lt (hsecond.trans_lt hearly)

theorem crossing_late (Vmin Smax p s o v a ao t pr sr or_ vr : ℝ)
    (hV : 0 < Vmin) (hS : 0 < Smax) (hs : 0 < s) (hv : Vmin ≤ v) (hvrV : Vmin ≤ vr)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hpr : pr ≤ 0) (hsrS : sr ≤ Smax)
    (hp : pr = p + s * t + a / 2 * t ^ 2) (hsp : sr = s + a * t)
    (ho : or_ = o + v * t + ao / 2 * t ^ 2) (hvr : vr = v + ao * t)
    (hlate : 0 < o + Vmin * (-p) / Smax) : Late Vmin pr sr or_ := by
  have hsr : 0 < sr := by nlinarith [mul_nonneg ha ht]
  let T₀ := -p / Smax
  let T₁ := -pr / sr
  have hT₀eq : T₀ * Smax = -p := by dsimp [T₀]; field_simp
  have hT₁eq : T₁ * sr = -pr := by dsimp [T₁]; field_simp
  have hT₁ : 0 ≤ T₁ := div_nonneg (neg_nonneg.mpr hpr) hsr.le
  have hsum : T₀ ≤ t + T₁ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsrS) ht,
      mul_nonneg (sub_nonneg.mpr hsrS) hT₁, mul_nonneg ha (sq_nonneg t)]
  have hoLower : o + Vmin * t ≤ or_ := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hv), mul_nonneg ht (sub_nonneg.mpr hvrV)]
  change 0 < or_ + Vmin * (-pr) / sr
  rw [mul_div_assoc]
  have hlate' : 0 < o + Vmin * T₀ := by
    dsimp [T₀]
    convert hlate using 1
    ring
  change 0 < or_ + Vmin * T₁
  nlinarith

theorem intersection_fallback (A b Vmin ε p s o v : ℝ)
    (hinv : IntersectionInv A b Vmin p s o v)
    (hafter : ¬AfterX p o) (hfast : ¬PassFaster A Vmin ε p s o v)
    (hcoast : ¬PassCoast Vmin p s o) : p + stopDist b s < 0 := by
  rcases hinv.2.2 with h | h | ⟨hs, h | h⟩
  · exact False.elim (hafter h)
  · exact h
  · exact False.elim (hfast ⟨hs, Or.inl h⟩)
  · exact False.elim (hcoast ⟨hs, h⟩)

@[reducible]
def IntersectionReady (A b Vmin ε p s o v a : ℝ) : Prop :=
  AfterX p o ∨
  (PassFaster A Vmin ε p s o v ∧ 0 ≤ a ∧ a ≤ A) ∨
  (PassCoast Vmin p s o ∧ a = 0) ∨
  (a = -b ∧ p + stopDist b s < 0) ∨
  (a = 0 ∧ s = 0 ∧ p < 0) ∨
  (a = A ∧ p + stoppingMargin A b 0 ε s < 0)

noncomputable def intersectionCtrl (A b Vmin ε p s o v : ℝ) :=
  intersectionControl A b Vmin ε p s o v

@[spec] theorem intersectionCtrl_spec (A b Vmin ε p s o v : ℝ) :
    ⦃IntersectionInv A b Vmin p s o v⦄ intersectionCtrl A b Vmin ε p s o v
    ⦃fun a => IntersectionReady A b Vmin ε p s o v a⦄ := by
  unfold intersectionCtrl intersectionControl
  vcgen
  case vc1 => simp_all
  case vc2 => simp_all
  case vc3 => simp_all
  case vc4 =>
    have hstop := intersection_fallback A b Vmin ε p s o v (by assumption)
      (by assumption) (by assumption) (by assumption)
    constructor
    · vcgen
      simp_all
    · vcgen
      constructor
      all_goals vcgen
      all_goals simp_all [stopDist]

theorem intersection_phase (A b Vmin ε p s o v a ao : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hV : 0 < Vmin) (hε : 0 < ε)
    (hs₀ : 0 ≤ s) (hv₀ : Vmin ≤ v) (hao : ao ≤ A)
    (hready : IntersectionReady A b Vmin ε p s o v a) :
    ∀ res ∈ SetM.run (evolve (intersectionMotion a ao, time) (intersectionDomain ε Vmin)
      ((p, s, o, v), 0)),
      IntersectionInv A b Vmin res.1.1 res.1.2.1 res.1.2.2.1 res.1.2.2.2 := by
  rintro ⟨⟨pr, sr, or_, vr⟩, t⟩ hrun
  have hr := intersection_projection true a ao ε Vmin p s o v hV.le
    ((pr, sr, or_, vr), t) hrun
  have ho := intersection_projection false a ao ε Vmin p s o v hV.le
    ((pr, sr, or_, vr), t) hrun
  obtain ⟨ht, htε, hsr, hsp, hp⟩ := line_exact a ε p s ((pr, sr), t) hr
  obtain ⟨_, _, _, hvr, hop⟩ := line_exact ao ε o v ((or_, vr), t) ho
  have hdom := dW (ode := (intersectionMotion a ao, time)) (domain := intersectionDomain ε Vmin)
    (pre := fun _ => True) (fun _ h => h) ((p, s, o, v), 0) trivial ((pr, sr, or_, vr), t) hrun
  have hvrV : Vmin ≤ vr := hdom.2.2
  have hpp : p ≤ pr := by nlinarith [mul_nonneg ht hs₀, mul_nonneg ht hsr]
  have hoo : o ≤ or_ := by
    nlinarith [mul_nonneg ht (hV.le.trans hv₀), mul_nonneg ht (hV.le.trans hvrV)]
  apply And.intro hsr (And.intro hvrV ?_)
  by_cases hafter : AfterX pr or_
  · exact Or.inl hafter
  · have hpr : pr ≤ 0 := le_of_not_gt (fun h => hafter (Or.inl h))
    have hor : or_ ≤ 0 := le_of_not_gt (fun h => hafter (Or.inr h))
    rcases hready with h | ⟨⟨hspos, hearly | hlate⟩, ha, haA⟩ |
      ⟨⟨hspos, hlate⟩, rfl⟩ | ⟨rfl, hstop⟩ | ⟨rfl, rfl, hpneg⟩ | ⟨rfl, hmargin⟩
    · rcases h with h | h <;> linarith
    · exact Or.inr (Or.inr ⟨by nlinarith [mul_nonneg ha ht],
        Or.inl (crossing_early A p s o v a ao t pr sr or_ vr hA.le hspos (hV.le.trans hv₀)
          ha hao ht hpr hp hsp hop hvr hearly)⟩)
    · have hsrS : sr ≤ s + A * ε := by
        nlinarith [mul_nonneg ha (sub_nonneg.mpr htε), mul_nonneg (sub_nonneg.mpr haA) hε.le]
      exact Or.inr (Or.inr ⟨by nlinarith [mul_nonneg ha ht],
        Or.inr (crossing_late Vmin (s + A * ε) p s o v a ao t pr sr or_ vr hV
          (by nlinarith) hspos hv₀ hvrV ha ht hpr hsrS hp hsp hop hvr hlate)⟩)
    · have hsrS : sr ≤ s := by simpa using hsp.le
      exact Or.inr (Or.inr ⟨by simpa [hsp] using hspos,
        Or.inr (crossing_late Vmin s p s o v 0 ao t pr sr or_ vr hV hspos hspos hv₀ hvrV
          le_rfl ht hpr hsrS hp hsp hop hvr hlate)⟩)
    · have hbarrier : pr + stopDist b sr = p + stopDist b s := by
        rw [hp, hsp]
        unfold stopDist
        field_simp
        ring
      exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inl (by simpa [stopDist, hp, hsp] using hpneg))
    · have hreserve : 0 ≤ (a / b + 1) * (a / 2 * (ε - t) ^ 2 + (ε - t) * sr) :=
        mul_nonneg (add_nonneg (div_nonneg hA.le hb.le) (by norm_num))
          (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
            (mul_nonneg (sub_nonneg.mpr htε) hsr))
      have hbarrier : pr + stopDist b sr +
          (a / b + 1) * (a / 2 * (ε - t) ^ 2 + (ε - t) * sr) =
          p + stoppingMargin a b 0 ε s := by
        rw [hp, hsp]
        unfold stoppingMargin stopDist
        field_simp
        ring
      exact Or.inr (Or.inl (by linarith))

noncomputable def intersectionDyn (_A _b Vmin ε p s o v a ao : ℝ) :=
  evolve (intersectionMotion a ao, time) (intersectionDomain ε Vmin) ((p, s, o, v), 0)

@[spec] theorem intersectionDyn_spec (A b Vmin ε p s o v a ao : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hV : 0 < Vmin) (hε : 0 < ε) :
    ⦃0 ≤ s ∧ Vmin ≤ v ∧ ao ≤ A ∧ IntersectionReady A b Vmin ε p s o v a⦄
      intersectionDyn A b Vmin ε p s o v a ao
    ⦃fun ((p, s, o, v), _t) => IntersectionInv A b Vmin p s o v⦄ := by
  constructor
  rintro ⟨hs, hv, hao, hready⟩
  exact intersection_phase A b Vmin ε p s o v a ao hA hb hV hε hs hv hao hready

noncomputable def dwcx' (A b Vmin ε p s o v : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hV : 0 < Vmin) (hε : 0 < ε) : SetM (ℝ × ℝ × ℝ × ℝ)
    requires IntersectionInv A b Vmin p s o v
    ensures (p, s, o, v) => IntersectionInv A b Vmin p s o v
    := do
  let mut (p, s, o, v) := (p, s, o, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => IntersectionInv A b Vmin p s o v do
    let ao ← driveActual A b
    let a ← intersectionCtrl A b Vmin ε p s o v
    let (res, _t) ← intersectionDyn A b Vmin ε p s o v a ao
    (p, s, o, v) := res
  return (p, s, o, v)

theorem dwcx_eq (A b Vmin ε p s o v : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hV : 0 < Vmin) (hε : 0 < ε) :
    dwcx A b Vmin ε p s o v = dwcx' A b Vmin ε p s o v hA hb hV hε := by rfl

theorem intersection_safe (A b Vmin p s o v : ℝ) (hb : 0 < b)
    (hinv : IntersectionInv A b Vmin p s o v) : p = 0 → o ≠ 0 := by
  intro hp ho
  have h : stopDist b s < 0 := by
    simpa [hp, ho, AfterX, Early, Late] using hinv.2.2
  exact not_lt_of_ge (div_nonneg (sq_nonneg s) (show 0 ≤ 2 * b by positivity)) h

theorem intersection_evolution (a ε Vmin p s o v T : ℝ) (hs : 0 ≤ s)
    (hv : Vmin ≤ v) (hT : 0 ≤ T) (hTε : T ≤ ε) (hsT : 0 ≤ s + a * T) :
    ((p + s * T + a / 2 * T ^ 2, s + a * T, o + v * T, v), T) ∈
      SetM.run (evolve (intersectionMotion a 0, time) (intersectionDomain ε Vmin)
        ((p, s, o, v), 0)) := by
  apply SemanticODE.mem_evolveSemantic _ (intersectionDomain ε Vmin) ((p, s, o, v), 0) T
    (fun t => ((p + s * t + a / 2 * t ^ 2, s + a * t, o + v * t, v), t)) hT
  constructor
  · simp
  · constructor
    · intro t ht
      apply And.intro (ht.2.trans hTε)
      apply And.intro ?_ hv
      by_cases ha : 0 ≤ a
      · nlinarith [mul_nonneg ha ht.1]
      · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (sub_nonneg.mpr ht.2)]
    · constructor
      · intro t ht
        have hp : HasDerivAt (fun τ : ℝ => p + s * τ + a / 2 * τ ^ 2) (s + a * t) t := by
          convert ((hasDerivAt_const t p).add ((hasDerivAt_id t).const_mul s)).add
            (((hasDerivAt_id t).pow 2).const_mul (a / 2)) using 1
          · rfl
          · dsimp
            ring
        have hs := (hasDerivAt_const t s).add ((hasDerivAt_id t).const_mul a)
        have ho := (hasDerivAt_const t o).add ((hasDerivAt_id t).const_mul v)
        simpa [intersectionMotion] using
          (hp.prodMk (hs.prodMk (ho.prodMk (hasDerivAt_const t v)))).hasDerivWithinAt
            (s := Set.Icc 0 T)
      · intro t ht
        exact (hasDerivAt_id t).hasDerivWithinAt

theorem driveActual_mem (A b a : ℝ) (ha : -b ≤ a) (hA : a ≤ A) :
    a ∈ SetM.run (driveActual A b) := by
  unfold driveActual
  apply run_bind _ _ a _ (Set.mem_univ _)
  apply run_bind _ _ () _ (show () ∈ SetM.run (ensure (-b ≤ a ∧ a ≤ A)) from ⟨ha, hA⟩)
  exact Set.mem_singleton _

theorem intersection_after_control (A b Vmin ε p s o v a : ℝ)
    (hafter : AfterX p o) (ha : -b ≤ a) (hA : a ≤ A) :
    a ∈ SetM.run (intersectionControl A b Vmin ε p s o v) := by
  rw [intersectionControl, ite_eq_left hafter]
  exact driveActual_mem A b a ha hA

theorem intersection_stopped_control (A b Vmin ε p o v : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) :
    0 ∈ SetM.run (intersectionControl A b Vmin ε p 0 o v) := by
  by_cases hafter : AfterX p o
  · exact intersection_after_control A b Vmin ε p 0 o v 0 hafter (by linarith) hA
  · rw [intersectionControl, ite_eq_right hafter,
      ite_eq_right (show ¬PassFaster A Vmin ε p 0 o v by simp [PassFaster]),
      ite_eq_right (show ¬PassCoast Vmin p 0 o by simp [PassCoast])]
    apply Or.inr
    apply Or.inl
    apply run_bind _ _ () _ (show () ∈ SetM.run (ensure ((0 : ℝ) = 0)) from rfl)
    exact Set.mem_singleton _

noncomputable def intersectionStep (A b Vmin ε : ℝ) (st : ℝ × ℝ × ℝ × ℝ) :
    SetM (ℝ × ℝ × ℝ × ℝ) := do
  let ao ← driveActual A b
  let a ← intersectionControl A b Vmin ε st.1 st.2.1 st.2.2.1 st.2.2.2
  let (res, _t) ← evolve (intersectionMotion a ao, time) (intersectionDomain ε Vmin) (st, 0)
  return res

theorem dwcx_eq_loop (A b Vmin ε p s o v : ℝ) :
    dwcx A b Vmin ε p s o v = finiteLoop (intersectionStep A b Vmin ε) (p, s, o, v) := by
  unfold dwcx finiteLoop
  simp only [← forIn_range_repeat]
  simp only [intersectionStep, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]

theorem intersection_step_run (A b Vmin ε p s o v a T : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hctrl : a ∈ SetM.run (intersectionControl A b Vmin ε p s o v))
    (hs : 0 ≤ s) (hv : Vmin ≤ v) (hT : 0 ≤ T) (hTε : T ≤ ε) (hsT : 0 ≤ s + a * T) :
    (p + s * T + a / 2 * T ^ 2, s + a * T, o + v * T, v) ∈
      SetM.run (intersectionStep A b Vmin ε (p, s, o, v)) := by
  unfold intersectionStep
  apply run_bind _ _ 0 _ (driveActual_mem A b 0 (by linarith) hA)
  apply run_bind _ _ a _ hctrl
  apply run_bind _ _ ((p + s * T + a / 2 * T ^ 2, s + a * T, o + v * T, v), T) _
    (intersection_evolution a ε Vmin p s o v T hs hv hT hTε hsT)
  exact Set.mem_singleton _

theorem repeatStep_add {σ : Type} (step : σ → SetM σ) (n m : ℕ) (x : σ) :
    repeatStep step (n + m) x = (do let y ← repeatStep step n x; repeatStep step m y) := by
  induction n generalizing x with
  | zero => simp [repeatStep]
  | succ n ih => simp [repeatStep, Nat.succ_add, ih, bind_assoc]

theorem reach_trans {σ : Type} (step : σ → SetM σ) (x y z : σ)
    (hxy : Reach step x y) (hyz : Reach step y z) : Reach step x z := by
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  apply Exists.intro (n + m)
  rw [repeatStep_add]
  exact run_bind _ _ y z hn hm

theorem intersection_wait_reach (A b Vmin ε p v : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (_hV : 0 < Vmin) (hε : 0 < ε) (hv : Vmin ≤ v) (n : ℕ) :
    ∀ o : ℝ, 0 < o + (n : ℝ) * (v * ε) →
      ∃ or_, Reach (intersectionStep A b Vmin ε) (p, 0, o, v) (p, 0, or_, v) ∧ 0 < or_ := by
  induction n with
  | zero =>
    intro o ho
    exact ⟨o, reach_refl _ _, by simpa using ho⟩
  | succ n ih =>
    intro o ho
    by_cases hdone : 0 < o
    · exact ⟨o, reach_refl _ _, hdone⟩
    · have hctrl := intersection_stopped_control A b Vmin ε p o v hA hb
      have hstep := intersection_step_run A b Vmin ε p 0 o v 0 ε hA hb hctrl le_rfl hv hε.le
        le_rfl (by norm_num)
      simp only [zero_mul, zero_div, add_zero] at hstep
      obtain ⟨or_, hreach, hor⟩ := ih (o + v * ε) (by push_cast at ho; linarith)
      exact ⟨or_, reach_prepend _ _ _ _ hstep hreach, hor⟩

theorem intersection_coast_reach (A b Vmin ε s v : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hV : 0 < Vmin) (hε : 0 < ε) (hs : 0 < s)
    (hv : Vmin ≤ v) (n : ℕ) :
    ∀ p o : ℝ, 0 < o → 0 < p + (n : ℝ) * (s * ε) →
      ∃ pr or_, Reach (intersectionStep A b Vmin ε) (p, s, o, v) (pr, s, or_, v) ∧ 0 < pr := by
  induction n with
  | zero =>
    intro p o ho hp
    exact ⟨p, o, reach_refl _ _, by simpa using hp⟩
  | succ n ih =>
    intro p o ho hp
    by_cases hdone : 0 < p
    · exact ⟨p, o, reach_refl _ _, hdone⟩
    · have hctrl := intersection_after_control A b Vmin ε p s o v 0 (Or.inr ho) (by linarith) hA
      have hstep := intersection_step_run A b Vmin ε p s o v 0 ε hA hb hctrl hs.le hv hε.le
        le_rfl (by linarith)
      simp only [zero_mul, zero_div, add_zero] at hstep
      obtain ⟨pr, or_, hreach, hpr⟩ := ih (p + s * ε) (o + v * ε) (by nlinarith)
        (by push_cast at hp; linarith)
      exact ⟨pr, or_, reach_prepend _ _ _ _ hstep hreach, hpr⟩

/-- Journal Theorem 12: collision exclusion and a successful intersection crossing. -/
theorem dwcx_live :
    ∀ A b Vmin ε p s o v,
      (0 < A ∧ 0 < b ∧ 0 < ε ∧ 0 < Vmin) → (s = 0 ∧ Vmin ≤ v ∧ p < 0) →
        (∀ res ∈ SetM.run (dwcx A b Vmin ε p s o v),
          let p_res := res.1
          let o_res := res.2.2.1
          p_res = 0 → o_res ≠ 0) ∧
        (∃ res ∈ SetM.run (dwcx A b Vmin ε p s o v),
          let p_res := res.1
          0 < p_res) := by
  intro A b Vmin ε p s o v hbounds hinit
  rcases hbounds with ⟨hA, hb, hε, hV⟩
  rcases hinit with ⟨rfl, hv, hp⟩
  constructor
  · intro res hrun
    rw [dwcx_eq A b Vmin ε p 0 o v hA hb hV hε] at hrun
    apply intersection_safe A b Vmin _ _ _ _ hb
    apply (dwcx'.spec A b Vmin ε p 0 o v hA hb hV hε).le_wp ?_ res hrun
    exact ⟨le_rfl, hv, Or.inr (Or.inl (by simpa [stopDist] using hp))⟩
  · have hvpos : 0 < v := hV.trans_le hv
    have hve : 0 < v * ε := mul_pos hvpos hε
    obtain ⟨nw, hnw⟩ := exists_nat_gt (-o / (v * ε))
    have howait : 0 < o + (nw : ℝ) * (v * ε) := by
      have h := (div_lt_iff₀ hve).mp hnw
      linarith
    obtain ⟨owait, hwait, howait⟩ :=
      intersection_wait_reach A b Vmin ε p v hA.le hb.le hV hε hv nw o howait
    have hctrl := intersection_after_control A b Vmin ε p 0 owait v A (Or.inr howait)
      (by linarith) le_rfl
    have hu : 0 < A * ε := mul_pos hA hε
    have hstep := intersection_step_run A b Vmin ε p 0 owait v A ε hA.le hb.le hctrl le_rfl hv
      hε.le le_rfl (by simpa using hu.le)
    simp only [zero_mul, zero_add, add_zero] at hstep
    obtain ⟨nc, hnc⟩ := exists_nat_gt (-(p + A / 2 * ε ^ 2) / (A * ε * ε))
    have hprogress : 0 < p + A / 2 * ε ^ 2 + (nc : ℝ) * (A * ε * ε) := by
      have h := (div_lt_iff₀ (mul_pos hu hε)).mp hnc
      linarith
    obtain ⟨pr, or_, hcoast, hpr⟩ := intersection_coast_reach A b Vmin ε (A * ε) v
      hA.le hb.le hV hε hu hv nc (p + A / 2 * ε ^ 2) (owait + v * ε) (by linarith) hprogress
    apply Exists.intro (pr, A * ε, or_, v)
    apply And.intro ?_ hpr
    rw [dwcx_eq_loop]
    exact reach_run _ _ _ (reach_trans _ _ _ _ hwait (reach_prepend _ _ _ _ hstep hcoast))

end IJRR17
