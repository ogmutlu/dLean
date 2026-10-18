import dLean.Core.QODE
import dLean.Tactic.QodeDeriv
open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

abbrev Car := Nat
abbrev CarState := ℝ × ℝ × ℝ

@[simp] def x (f : Car → CarState) (car : Car) : ℝ := (f car).1
@[simp] def v (f : Car → CarState) (car : Car) : ℝ := (f car).2.1
@[simp] def a (f : Car → CarState) (car : Car) : ℝ := (f car).2.2

@[simp] def motion (active : Finset Car) :
    Set Car × ((Car → CarState) → (Car → CarState)) :=
  (active, fun f => fun car =>
              (v f car, a f car, 0))

@[simp] def domain (_ : Car → CarState) : Prop := True

@[reducible] def Ordered (f : Car → CarState) (i j : Car) : Prop :=
  x f i < x f j ∧ v f i ≤ v f j ∧ a f i ≤ a f j

@[simp] def invariant (active : Finset Car) (f : Car → CarState) : Prop :=
  ∀ i ∈ active, ∀ j ∈ active,
    i ≠ j → Ordered f i j ∨ Ordered f j i

@[simp] def aGap (i j : Car) (f : Car → CarState) : ℝ :=
  a f i - a f j

@[simp] def vGap (i j : Car) (f : Car → CarState) : ℝ :=
  v f i - v f j

@[simp] def xGap (i j : Car) (f : Car → CarState) : ℝ :=
  x f i - x f j

@[simp] def vGap' (i j : Car) (f : Car → CarState) : ℝ :=
  a f i - a f j

@[simp] def xGap' (i j : Car) (f : Car → CarState) : ℝ :=
  v f i - v f j

theorem ordered_preserved (active : Finset Car) (i j : Car)
    (hi : i ∈ active) (hj : j ∈ active) :
    (fun f => Ordered f i j)
    [[evolve (motion active) domain]]
    (fun f => Ordered f i j) := by
  apply dC (cut := fun f => aGap i j f ≤ 0)
  · apply dIle (aGap i j) (fun _ => 0)
    · qode_deriv [aGap, a, motion]
    · grind only [aGap]
    · simp
  · apply dC (cut := fun f => vGap i j f ≤ 0)
    · apply dIle (vGap i j) (vGap' i j)
      · qode_deriv [vGap, vGap', v, a, motion]
      · grind only [vGap]
      · grind only [aGap, vGap']
    · apply dC (cut := fun f => xGap i j f < 0)
      · apply dIlt (xGap i j) (xGap' i j)
        · qode_deriv [xGap, xGap', x, v, a, motion]
        · grind only [xGap]
        · grind only [vGap, xGap']
      · apply dW
        grind only [aGap, xGap, vGap]

theorem motion_preserves_invariant (active : Finset Car) :
    invariant active
    [[evolve (motion active) domain]]
    invariant active := by
  rw [Ensures.iff_run]
  intro f hInvariant f' hEvolution i hi j hj hij
  rcases hInvariant i hi j hj hij with hForward | hBackward
  · exact Or.inl (ordered_preserved active i j hi hj
      f hForward f' hEvolution)
  · exact Or.inr (ordered_preserved active j i hj hi
      f hBackward f' hEvolution)

@[spec] theorem motionStep_spec (active : Finset Car) (f : Car → CarState) :
    ⦃invariant active f⦄
    evolve (motion active) domain f
    ⦃invariant active⦄ := by
  exact ⟨motion_preserves_invariant active f⟩

def prog (active : Finset Car) (f : Car → CarState)
    requires invariant active f
    ensures res => ∀ i ∈ res.1, ∀ j ∈ res.1, i ≠ j → res.2 i ≠ res.2 j
    := do
  let mut active := active
  let mut f := f
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => invariant active f do
    let i ← chooseS {i | i ∉ active}
    active := insert i active
    unless (∀ j ∈ active, i ≠ j →
        Ordered f i j ∨ Ordered f j i) do abort
    f ← evolve (motion active) domain f
  return (active, fun car => x f car)
where finally
  | spec => all_goals grind [invariant, x]

theorem dccs_collision_free :
    ∀ active f, invariant active f →
      ∀ res ∈ SetM.run (prog active f),
        let (active', x_res) := res
        ∀ i ∈ active', ∀ j ∈ active', i ≠ j → x_res i ≠ x_res j := by
  intro active f hinv res hrun
  exact (prog.spec active f).le_wp hinv res hrun
