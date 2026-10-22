import dLean.Tactic.AutoDiff

/-! Shared-time ODE/QODE derivative tests, including active-set boundaries. -/

open dLean

namespace dLean.Tests.CombinedDynamics

abbrev Cars := (Nat → ℝ) × (Nat → ℝ) × (Nat → ℝ)

@[simp] def motion (active : Finset Nat) : Set Nat × (Cars → Cars) :=
  (active, fun (_x, v, a) => (v, a, 0))

@[simp] def clock : ℝ → ℝ := fun _ => 1

example (active : Finset Nat) :
    HasPrime (Evolvable.denotation (motion active, clock)) (fun _ => True)
      (fun st : Cars × ℝ => st.2) (fun _ => 1) := by
  ode_deriv

-- The clock must evolve even when there are no active cars.
example : HasPrime (Evolvable.denotation (motion ∅, clock)) (fun _ => True)
    (fun st : Cars × ℝ => st.2) (fun _ => 1) := by
  ode_deriv

example (active : Finset Nat) (i : Nat) (hi : i ∈ active) :
    HasPrime (Evolvable.denotation (motion active, clock)) (fun _ => True)
      (fun st : Cars × ℝ => st.1.1 i) (fun st => st.1.2.1 i) := by
  ode_deriv

example (active : Finset Nat) (i : Nat) (hi : i ∈ active) :
    HasPrime (Evolvable.denotation (motion active, clock)) (fun _ => True)
      (fun ((x, v, _a), t) => x i + t * v i)
      (fun ((_x, v, a), t) => 2 * v i + t * a i) := by
  ode_deriv

-- Concrete active-set membership is discharged without an explicit hypothesis.
example (f l : Nat) :
    HasPrime (Evolvable.denotation (motion {f, l}, clock)) (fun _ => True)
      (fun st : Cars × ℝ => st.1.1 f) (fun st => st.1.2.1 f) := by
  ode_deriv

-- An inactive field has no derivative constraint, even if the supplied RHS is zero.
example : True := by
  fail_if_success
    have : HasPrime (Evolvable.denotation (motion ∅, clock)) (fun _ => True)
        (fun st : Cars × ℝ => st.1.1 0) (fun _ => 0) := by ode_deriv
  trivial

example (active : Finset Nat) (i : Nat) (hi : i ∈ active) : ∃ derivative,
    HasPrime (Evolvable.denotation (motion active, clock)) (fun _ => True)
      (fun ((x, v, _a), t) => x i + t * v i) derivative ∧
    ∀ x v a t, derivative ((x, v, a), t) = 2 * v i + t * a i := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x v a t
    ring

example : ∃ derivative,
    HasPrime (Evolvable.denotation (motion ∅, clock)) (fun _ => True)
      (fun st : Cars × ℝ => st.2) derivative ∧
    ∀ st, derivative st = 1 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro st
    rfl

-- The same synthesis path also supports a QODE without a scalar component.
example (active : Finset Nat) (i : Nat) (hi : i ∈ active) : ∃ derivative,
    HasPrime (Evolvable.denotation (motion active)) (fun _ => True)
      (fun (x, v, _a) => x i * v i) derivative ∧
    ∀ x v a, derivative (x, v, a) = v i ^ 2 + x i * a i := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x v a
    ring

-- Nested products must preserve all three simultaneous components.
example (active : Finset Nat) (i : Nat) (hi : i ∈ active) : ∃ derivative,
    HasPrime (Evolvable.denotation (motion active, (clock, clock))) (fun _ => True)
      (fun ((x, _v, _a), (t, u)) => x i + t * u) derivative ∧
    ∀ x v a t u, derivative ((x, v, a), (t, u)) = v i + u + t := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x v a t u
    ring

-- A literal QODE is itself a pair; distinguish it from a product of systems by its instance.
example : ∃ derivative,
    HasPrime (Evolvable.denotation
      (((Set.univ : Set Nat), fun x : Nat → ℝ => x), clock)) (fun _ => True)
      (fun (x, t) => x 0 + t) derivative ∧
    ∀ x t, derivative (x, t) = x 0 + 1 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x t
    rfl

-- Pure ODE products remain supported by both proof and synthesis.
example : HasPrime (Evolvable.denotation (clock, clock)) (fun _ => True)
    (fun (t, u) => t * u) (fun (t, u) => u + t) := by
  ode_deriv

example : ∃ derivative,
    HasPrime (Evolvable.denotation (clock, clock)) (fun _ => True)
      (fun (t, u) => t * u) derivative ∧
    ∀ t u, derivative (t, u) = u + t := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro t u
    ring

-- The scalar component can also come first.
example (active : Finset Nat) (i : Nat) (hi : i ∈ active) : ∃ derivative,
    HasPrime (Evolvable.denotation (clock, motion active)) (fun _ => True)
      (fun (t, (x, _v, _a)) => t + x i) derivative ∧
    ∀ t x v a, derivative (t, (x, v, a)) = 1 + v i := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro t x v a
    rfl

-- Each QODE component keeps its own active-set requirements.
example (left right : Finset Nat) (i j : Nat) (hi : i ∈ left) (hj : j ∈ right) :
    HasPrime (Evolvable.denotation (motion left, motion right)) (fun _ => True)
      (fun ((x, _v, _a), (y, _w, _b)) => x i - y j)
      (fun ((_x, v, _a), (_y, w, _b)) => v i - w j) := by
  ode_deriv

example : True := by
  fail_if_success
    have : HasPrime (Evolvable.denotation (motion {0}, motion ∅)) (fun _ => True)
        (fun st : Cars × Cars => st.2.1 0) (fun st => st.2.2.1 0) := by ode_deriv
  trivial

example : True := by
  fail_if_success
    have : ∃ derivative,
        HasPrime (Evolvable.denotation (motion ∅, clock)) (fun _ => True)
          (fun st : Cars × ℝ => st.1.1 0) derivative := by
      refine ⟨?_, ?_⟩
      rotate_left
      autodiff
  trivial

example : True := by
  fail_if_success
    have : HasPrime (Evolvable.denotation (motion {0}, clock)) (fun _ => True)
        (fun st : Cars × ℝ => st.1.1 0) (fun _ => 0) := by autodiff
  trivial

-- A moving index is not a fixed QODE coordinate and must not be differentiated as one.
def continuum : Set ℝ × ((ℝ → ℝ) → ℝ → ℝ) := (Set.univ, fun x => x)

example : True := by
  fail_if_success
    have : ∃ derivative,
        HasPrime (Evolvable.denotation (continuum, clock)) (fun _ => True)
          (fun (x, t) => x t) derivative := by
      refine ⟨?_, ?_⟩
      rotate_left
      autodiff
  trivial

end dLean.Tests.CombinedDynamics
