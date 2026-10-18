import dLean.Core.ODE
import dLean.Tactic.AutoDiff

/-!
# Braking in a real vector space

Example from (https://lfcps.org/course/lfcps20/projects/akabra_cslamber.pdf)

Consider a vehicle with position vector `x` in an arbitrary dimensional real
inner product space and scalar speed `v`. The origin represents a point the
vehicle must avoid, and `B` is its constant positive braking strength. Each
loop iteration chooses an arbitrary unit direction `d` and evolves according to
`x' = v * d` and `v' = -B` while speed remains nonnegative. The direction stays
fixed during each continuous phase but may change between phases.

This module proves `vector_braking_safe`: if the initial speed is positive and
the stopping distance `v^2 / (2*B)` is strictly less than the initial distance
to the origin, every returned position remains different from the origin after
any finite number of loop iterations.

The invariant uses a unit vector `u` and a positive slack `eps` to bound the
margin `v^2 - 2*B*inner(u, x) + eps` by zero. Since `eps > 0`, this bound
forces the projection `inner(u, x)` to remain positive and therefore excludes
`x = 0`.
-/

open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
open scoped RealInnerProductSpace

@[simp] def brake (d : V) (B : ℝ) : V × ℝ → V × ℝ
  | (_x, v) => (v • d, -B)

@[simp] def domain : V × ℝ → Prop
  | (_x, v) => 0 ≤ v

@[simp] def margin (u : V) (eps B : ℝ) : V × ℝ → ℝ
  | (x, v) => v ^ 2 - 2 * B * ⟪u, x⟫ + eps

@[simp] def invariant (B : ℝ) : V × ℝ → Prop
  | (x, v) => (0 < B ∧ 0 ≤ v) ∧
    ∃ u : V, ‖u‖ = 1 ∧
      ∃ eps : ℝ, 0 < eps ∧ margin u eps B (x, v) ≤ 0

-- @[simp] def margin' (u d : V) (B : ℝ) : V × ℝ → ℝ
--   | (_x, v) => -2 * B * v * (1 + ⟪u, d⟫)

theorem margin_preserved
    (u d : V) (eps B : ℝ) (hB : 0 < B) (hu : ‖u‖ = 1) (hd : ‖d‖ = 1) :
    (fun (x, v) => margin u eps B (x, v) ≤ 0)
    [[evolve (brake d B) domain]]
    (fun (x, v) => margin u eps B (x, v) ≤ 0) := by
  apply dIle (margin u eps B)
  · autodiff
  · simp_all
  · intro (x, v) _
    have : 0 ≤ 1 + ⟪u, d⟫ := by
      linarith [neg_one_le_real_inner_of_norm_eq_one hu hd] --Cauchy Schwartz
    have : -2 * B * v ≤ 0 := by simp_all
    simp
    nlinarith

theorem evolution_preserves
    (d : V) (B : ℝ) (hB : 0 < B) (hd : ‖d‖ = 1) :
    invariant B [[evolve (brake d B) domain]] invariant B := by
  intro _ hinv
  rcases hinv with ⟨⟨_, _⟩, n, _, eps, _, _⟩
  apply dC (cut := fun st => margin n eps B st ≤ 0)
  · solve_by_elim
  · apply dW
    grind [= margin, = domain, = invariant]
  · grind [margin_preserved]

theorem initial_invariant
    (B v : ℝ) (x : V) (hpre : 0 < B ∧ 0 < v ∧ v ^ 2 / (2 * B) < ‖x‖) :
    invariant B (x, v) := by
  simp_all
  rcases hpre with ⟨hB, hv, hstop⟩
  ring_nf
  simp only [le_of_lt, hv]
  have hxnorm : 0 < ‖x‖ := by
    apply lt_trans _ hstop
    exact div_pos (pow_pos hv 2) (mul_pos (by norm_num) hB)
  have hmargin : 0 < B * ‖x‖ * 2 - v ^ 2 := by
    have h := (div_lt_iff₀ (mul_pos (by norm_num) hB)).mp hstop
    nlinarith
  let u : V := ‖x‖⁻¹ • x
  have hn_norm : ‖u‖ = 1 := by
    simp [u, norm_smul, hxnorm.ne']
  have hn_inner : ⟪u, x⟫ = ‖x‖ := by
    simp only [u, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    field_simp [hxnorm.ne']
  simp_all only [norm_pos_iff, ne_eq, sub_pos, true_and]
  refine ⟨u, hn_norm, ?_⟩
  refine ⟨B * ‖x‖ * 2 - v ^ 2, sub_pos.mpr hmargin, ?_⟩
  rw [hn_inner]
  linarith

@[spec] theorem brakingStep_spec (B : ℝ) (d : V) (st : V × ℝ) :
    ⦃(0 < B ∧ ‖d‖ = 1) ∧ invariant B st⦄
    evolve (brake d B) domain st
    ⦃invariant B⦄ := by
  constructor
  intro h
  exact evolution_preserves d B h.1.1 h.1.2 st h.2

def prog (B v : ℝ) (x : V) := do
  let mut (x, v) := (x, v)
  let n ← choose ℕ
  for _ in [:n] do
    let d ← choose {d : V // ‖d‖ = 1}
    (x, v) ← evolve (brake (d : V) B) domain (x, v)
  return x

def prog' (B v : ℝ) (x : V)
    requires 0 < B ∧ 0 < v ∧ v ^ 2 / (2 * B) < ‖x‖
    ensures x_res => x_res ≠ 0
    := do
  let mut (x, v) := (x, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => invariant B (x, v) do
    let d ← choose {d : V // ‖d‖ = 1}
    (x, v) ← evolve (brake (d : V) B) domain (x, v)
  return x
where finally
  | spec =>
    case vc1 =>
      exact initial_invariant B v x (by assumption)
    case vc2 =>
      rcases ‹invariant B (x, v)› with ⟨⟨_, _⟩, u, _, eps, heps, hmargin⟩
      intro hx
      have hx' : x = 0 := hx
      subst x
      simp only [margin, inner_zero_right, mul_zero, sub_zero] at hmargin
      nlinarith [sq_nonneg v]

theorem prog_eq_prog' (B v : ℝ) (x : V) : prog B v x = prog' B v x := rfl

theorem vector_braking_safe :
    ∀ B v (x : V),
      0 < B ∧ 0 < v ∧ v ^ 2 / (2 * B) < ‖x‖ →
        ∀ x_res ∈ SetM.run (prog B v x), x_res ≠ 0 := by
  intro B v x hpre x' hrun
  rw [prog_eq_prog'] at hrun
  exact (prog'.spec B v x).le_wp hpre x' hrun
