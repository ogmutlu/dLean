import dLean.Tactic.AutoDiff
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Regression tests for synthesized derivatives. The first goal assigns the derivative;
the second checks it against an independently written formula.
-/

open dLean
open scoped RealInnerProductSpace

namespace dLean.Tests.AutoDiff

def growth (x : ℝ) : ℝ := x

example : ∃ derivative,
    HasPrime (Evolvable.denotation growth) (fun _ => True)
      (fun x => x ^ 3 - 2 * x + 7) derivative ∧
    ∀ x, derivative x = 3 * x ^ 3 - 2 * x := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    ring

example : ∃ derivative,
    HasPrime (Evolvable.denotation growth) (fun _ => True)
      (fun x => Real.sin x + Real.cos x) derivative ∧
    ∀ x, derivative x = Real.cos x * x - Real.sin x * x := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    ring

example : ∃ derivative,
    HasPrime (Evolvable.denotation growth) (fun _ => True)
      (fun x => x ^ 0 + x ^ 1) derivative ∧
    ∀ x, derivative x = x := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    ring

def cube (x : ℝ) : ℝ := x * x * x

example : ∃ derivative,
    HasPrime (Evolvable.denotation growth) (fun _ => True) cube derivative ∧
    ∀ x, derivative x = 3 * x ^ 3 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff [cube]
  · intro x
    ring

def motion : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | (_x, v, a) => (v, a, 0)

-- Recursively flattened product states, beyond the old two-field special case.
example : ∃ derivative,
    HasPrime (Evolvable.denotation motion) (fun _ => True)
      (fun (x, v, a) => x * v + a ^ 2) derivative ∧
    ∀ x v a, derivative (x, v, a) = v ^ 2 + x * a := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x v a
    ring

def grouped : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ
  | ((x, y), z) => ((y, z), x)

example : ∃ derivative,
    HasPrime (Evolvable.denotation grouped) (fun _ => True)
      (fun ((x, y), z) => x * y + z ^ 2) derivative ∧
    ∀ x y z, derivative ((x, y), z) = y ^ 2 + x * z + 2 * z * x := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x y z
    ring

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

def rotation (x : Vec2) : Vec2 := !₂[-x 1, x 0]

example : ∃ derivative,
    HasPrime (Evolvable.denotation rotation) (fun _ => True)
      (fun x => ‖x‖ ^ 2) derivative ∧
    ∀ x, derivative x = 0 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring

-- Differentiating the constructed vector exercises toLp, vecCons, and vecEmpty.
example : ∃ derivative,
    HasPrime (Evolvable.denotation rotation) (fun _ => True)
      (fun x => ‖rotation x‖ ^ 2) derivative ∧
    ∀ x, derivative x = 0 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    simp [PiLp.inner_apply, Fin.sum_univ_two, rotation]
    ring

-- Coordinates and vector literals must work beyond two dimensions.
def shifted (x : Vec3) : Vec3 := !₂[x 1, x 2, x 0]

example : ∃ derivative,
    HasPrime (Evolvable.denotation shifted) (fun _ => True)
      (fun x => x 0 * x 1) derivative ∧
    ∀ x, derivative x = x 1 ^ 2 + x 0 * x 2 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    simp
    ring

def oscillator : Vec3 × Vec3 → Vec3 × Vec3
  | (x, v) => (v, -x)

example : ∃ derivative,
    HasPrime (Evolvable.denotation oscillator) (fun _ => True)
      (fun (x, v) => ⟪x, v⟫) derivative ∧
    ∀ x v, derivative (x, v) = ⟪v, v⟫ - ⟪x, x⟫ := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x v
    simp [inner_neg_right]
    ring

def functionGrowth (x : Fin 3 → ℝ) : Fin 3 → ℝ := x

-- toLp also wraps arbitrary function-valued states, not just vector literals.
example : ∃ derivative,
    HasPrime (Evolvable.denotation functionGrowth) (fun _ => True)
      (fun x => ‖WithLp.toLp 2 x‖ ^ 2) derivative ∧
    ∀ x, derivative x = 2 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · autodiff
  · intro x
    simp

-- Supplying a derivative still takes the certificate-only path.
example : HasPrime (Evolvable.denotation growth) (fun _ => True)
    (fun x => x ^ 2) (fun x => 2 * x ^ 2) := by
  autodiff

example : True := by
  fail_if_success
    have : HasPrime (Evolvable.denotation growth) (fun _ => True)
        (fun x => x ^ 2) (fun _ => 0) := by autodiff
  trivial

end dLean.Tests.AutoDiff
