import dLean.Core.ODE
import dLean.Tactic.AutoDiff

/-!
# Aerodynamic Bouncing Ball

This module proves `aerodynamic_quantum_safe`, an example from the
[LFCPS book](https://doi.org/10.1007/978-3-319-63588-0). A ball released from
rest between the ground and height `H` remains in that interval after any
finite number of bounces. The model splits upward and downward motion to account
for the direction vertical velocity `v` and reverses velocity at the ground
with elastic damping factor `c` between zero and one. `g` is the gravitaitonal
constant and `r` is the air resistance. The loop invariant combines
nonnegative height with the energy bound `v^2 + 2*g*x <= 2*g*H`.
-/

open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

@[simp] def up (g r : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (_x, v) => (v, -g - r * v ^ 2)

@[simp] def upDomain : ℝ × ℝ → Prop
  | (x, v) => 0 ≤ x ∧ 0 ≤ v

@[simp] def down (g r : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (_x, v) => (v, -g + r * v ^ 2)

@[simp] def downDomain : ℝ × ℝ → Prop
  | (x, v) => 0 ≤ x ∧ v ≤ 0

@[simp] def energyGap (g H : ℝ) : ℝ × ℝ → ℝ
  | (x, v) => v ^ 2 + 2 * g * x - 2 * g * H

-- @[simp] def upEnergyGap' (g r : ℝ) : ℝ × ℝ → ℝ
--   | (_x, v) => 2 * v * (-g - r * v ^ 2) + 2 * g * v

-- @[simp] def downEnergyGap' (g r : ℝ) : ℝ × ℝ → ℝ
--   | (_x, v) => 2 * v * (-g + r * v ^ 2) + 2 * g * v

@[simp] def invariant (g H : ℝ) : ℝ × ℝ → Prop
  | (x, v) => energyGap g H (x, v) ≤ 0 ∧ 0 ≤ x

theorem upward_preserves (g H r : ℝ) (hr : 0 ≤ r) :
    invariant g H [[evolve (up g r) upDomain]] invariant g H := by
  apply dC (cut := fun (x, v) => energyGap g H (x, v) ≤ 0)
  · apply dIle (energyGap g H)
    · autodiff
    · simp_all
    · intro (x, v) _
      simp
      ring_nf
      have : 0 ≤ v ^ 3 := by simp_all
      nlinarith
  · apply dW
    simp_all

theorem downward_preserves (g H r : ℝ) (hr : 0 ≤ r) :
    invariant g H [[evolve (down g r) downDomain]] invariant g H := by
  apply dC (cut := fun (x, v) => energyGap g H (x, v) ≤ 0)
  · apply dIle (energyGap g H)
    · autodiff
    · simp_all
    · intro (x, v) _
      simp
      ring_nf
      have : v ^ 3 ≤ 0 := by
        simp_all [Odd.pow_nonpos (n := 3) (by decide)]
      nlinarith
  · apply dW
    simp_all

theorem continuous_preserves (hr : 0 ≤ r) :
    invariant g H
    [[evolve (up g r) upDomain ∪ evolve (down g r) downDomain]]
    invariant g H := by
  apply Ensures.nondet_choice
  · apply upward_preserves
    simp_all
  · apply downward_preserves
    simp_all

theorem bounce_preserves {g H c x v : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hinv : invariant g H (x, v)) : invariant g H (x, -c * v) := by
  simp_all
  have : c ^ 2 ≤ 1 := by simp_all [pow_le_one₀]
  nlinarith

@[spec] theorem continuous_spec (g r : ℝ) (st : ℝ × ℝ) :
    ⦃0 ≤ r⦄
    (evolve (up g r) upDomain ∪ evolve (down g r) downDomain) st
    ⦃fun st' => ∀ H, invariant g H st → invariant g H st'⦄ := by
  refine ⟨?_⟩
  intro h st' hst' H hH
  exact continuous_preserves h st hH st' hst'

def prog (g c r x v : ℝ) := do
  let mut (x, v) := (x, v)
  let n ← choose ℕ
  for _ in [:n] do
    if x = 0 then
      v := -c * v
    (x, v) ← (evolve (up g r) upDomain ∪
              evolve (down g r) downDomain) (x, v)
  return x

def prog' (g c r x₀ v₀ : ℝ) : SetM ℝ
    given (H : ℝ)
    requires (x₀ ≤ H ∧ v₀ = 0 ∧ 0 ≤ x₀) ∧ (0 < g ∧ c ≤ 1 ∧ 0 ≤ c ∧ 0 ≤ r)
    ensures x_res => 0 ≤ x_res ∧ x_res ≤ H
    := do
  let mut (x, v) := (x₀, v₀)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => invariant g x₀ (x, v) do
    if x = 0 then
      v := -c * v
    (x, v) ← (evolve (up g r) upDomain ∪
              evolve (down g r) downDomain) (x, v)
  return x
where finally
  | spec =>
    case vc1 => simp_all
    case vc2 =>
      simp_all
      nlinarith
    case vc4 =>
      rename_i hinv hx hall
      exact hall x₀ (bounce_preserves (c := c) (by simp_all) (by simp_all) hinv)

theorem prog_eq_prog' (g c r x v : ℝ) : prog g c r x v = prog' g c r x v := rfl

theorem aerodynamic_quantum_safe :
    ∀ g H c r x v, (x ≤ H ∧ v = 0 ∧ 0 ≤ x) ∧ (0 < g ∧ c ≤ 1 ∧ 0 ≤ c ∧ 0 ≤ r) →
      ∀ x_res ∈ SetM.run (prog g c r x v), 0 ≤ x_res ∧ x_res ≤ H := by
  intro g H c r x v hpre res hrun
  rw [prog_eq_prog'] at hrun
  exact (prog'.spec g c r x v H).le_wp hpre res hrun
