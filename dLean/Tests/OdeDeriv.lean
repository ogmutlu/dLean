import dLean.Tactic.OdeDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Regression tests for supplied derivatives. Run with `lake build dLean.Tests`. -/

open dLean
open scoped RealInnerProductSpace

namespace dLean.Tests.OdeDeriv

def growth (x : ℝ) : ℝ := x

example : HasPrime (Evolvable.denotation growth) (fun _ => True)
    (fun x => x ^ 3 - 2 * x + 7) (fun x => 3 * x ^ 3 - 2 * x) := by
  ode_deriv

example : HasPrime (Evolvable.denotation growth) (fun _ => True)
    (fun x => Real.sin x + Real.cos x)
    (fun x => Real.cos x * x - Real.sin x * x) := by
  ode_deriv

-- A wrong derivative must not be accepted, including through `autodiff`'s fallback.
example : True := by
  fail_if_success
    have : HasPrime (Evolvable.denotation growth) (fun _ => True)
        (fun x => x ^ 2) (fun _ => 0) := by ode_deriv
  trivial

def motion : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | (_x, v, a) => (v, a, 0)

example : HasPrime (Evolvable.denotation motion) (fun _ => True)
    (fun (x, v, a) => x * v + a ^ 2) (fun (x, v, a) => v ^ 2 + x * a) := by
  ode_deriv

def nonnegative (x : ℝ) : Prop := 0 ≤ x

-- Anonymous conjunctions in the domain must still expose named predicates.
example : HasPrime (Evolvable.denotation growth)
    (fun x => nonnegative x ∧ x = 0) (fun x => x ^ 2) (fun _ => 0) := by
  ode_deriv

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

def rotation (x : Vec2) : Vec2 := !₂[-x 1, x 0]

example : HasPrime (Evolvable.denotation rotation) (fun _ => True)
    (fun x => ‖x‖ ^ 2) (fun _ => 0) := by
  ode_deriv

example : HasPrime (Evolvable.denotation rotation) (fun _ => True)
    (fun x => x 0) (fun x => -x 1) := by
  ode_deriv

def expand (x : Vec3) : Vec3 := 2 • x

example : HasPrime (Evolvable.denotation expand) (fun _ => True)
    (fun x => ‖x‖ ^ 2) (fun x => 4 * ‖x‖ ^ 2) := by
  ode_deriv

example {I : Type} [Fintype I] :
    HasPrime (Evolvable.denotation (fun x : EuclideanSpace ℝ I => 2 • x))
      (fun _ => True) (fun x => ‖x‖ ^ 2) (fun x => 4 * ‖x‖ ^ 2) := by
  ode_deriv

example {I : Type} [Fintype I] {f : ℝ → PiLp 2 (fun _ : I => ℝ)}
    {v : PiLp 2 (fun _ : I => ℝ)}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt f v s t) (i : I) :
    HasDerivWithinAt (fun t => f t i) (v i) s t :=
  dLean.OdeDeriv.hasDerivWithinAt_piLp_apply i h

example {I : Type} [Fintype I] {f : ℝ → I → ℝ} {v : I → ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f v s t) :
    HasDerivWithinAt (fun t => WithLp.toLp 2 (f t)) (WithLp.toLp 2 v) s t :=
  dLean.OdeDeriv.hasDerivWithinAt_toLp h

end dLean.Tests.OdeDeriv
