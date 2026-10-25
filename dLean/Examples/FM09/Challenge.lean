import dLean.Core.ODE
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# FM09 — throughout-safety version of the FTRM challenge

This file states:
1. The verification-plan properties AC1–AC7 (Section 4.3). Each safety lemma is
   stated on the *bare* ODE of its phase, with no filtering test after it.
   Since an ODE can stop at any time (`evolve_prefix_closed`), such a lemma
   covers every intermediate point of the phase.
2. The gluing of Fig. 11: a loop invariant for completed iterations plus safety
   of every *prefix* of one more iteration.
3. The combined theorem `ftrm_safe_throughout`: every phase prefix
   after any number of completed iterations is `p`-separated.
-/

open dLean
open scoped RealInnerProductSpace

namespace FM09

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-- Safe planar separation of two aircrafts, with coordinates x and y -/
@[reducible]
def Separated (p : ℝ) (x y : Vec2) : Prop :=
  p ^ 2 ≤ ‖x - y‖ ^ 2

/-- The perpendicular of a vector, a counterclockwise quarter-turn. -/
@[simp] def perp (v : Vec2) : Vec2 :=
  !₂[-v 1, v 0]

/-- Flight of first aircraft -/
@[simp] def F (ω : ℝ) := fun ((_x : Vec2), d) => (d, ω • perp d)

/-- Flight of second aircraft -/
@[simp] def G (ρ : ℝ) := fun ((_y : Vec2), e) => (e, ρ • perp e)

/-- Joint flight dynamics, Section 4.1.
Position vectors x, y
Angular speeds ω, ρ
Linear velocity vectors d, e
-/
@[simp] def flight (ω ρ : ℝ) := fun (x, d, y, e) =>
  let (x', d') := F ω (x, d)
  let (y', e') := G ρ (y, e)
  (x', d', y', e')

---------- Non-flyable tangential roundabout maneuver, Figure 5 -------------

/-- Free flight by choosing arbitrary angular velocities -/
def free (p : ℝ) (x d y e : Vec2) := do
  let mut (x, d, y, e) := (x, d, y, e)
  let n ← choose ℕ
  for _ in [:n] do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← evolve (flight ω ρ)
                   (fun (x, (_: Vec2), y, (_: Vec2)) => Separated p x y) -- domain
                   (x, d, y, e)
  return (x, d, y, e)

/-- Agree on arbitrary roundabout center c and angular velocity ω -/
def agree := do
  let ω ← choose ℝ
  let c ← choose Vec2
  return (ω, c)

/-- Entry procedure with instant turns -/
@[simp] def entry_n (ω : ℝ) (c : Vec2) (x y : Vec2) :=
  let d := ω • perp (x - c)
  let e := ω • perp (y - c)
  (d, e) -- direction vectors tangential to roundabout center c

def ntrm (p : ℝ) (x d y e : Vec2) := do
  let mut (x, d, y, e) := (x, d, y, e)
  let n ← choose ℕ
  for _ in [:n] do
    (x, d, y, e) ← free p x d y e
    let (ω, c) ← agree
    (d, e) := entry_n ω c x y
    (x, d, y, e) ← evolve (flight ω ω) (fun _ => True) (x, d, y, e)
  return (x, y)

/-- Initially separated aircraft remain separated after any finite NTRM run. -/
theorem ntrm_safe :
    ∀ (p : ℝ) (x d y e : Vec2), Separated p x y →
      ∀ res ∈ SetM.run (ntrm p x d y e),
        let (x_res, y_res) := res
        Separated p x_res y_res := sorry

----- Fully-flyable tangential roundabout maneuver, Figure 14 ---------

/-- Far separation, equation (8) -/
noncomputable def far (p r : ℝ) : ℝ :=
  √2 * (p + (2 / 3) * Real.pi * r)

/-- Entry configuration condition `C` -/
@[reducible]
def C (r : ℝ) (x d y e c : Vec2) : Prop :=
  ‖x - c‖ = √(3 * r ^ 2) ∧ ∃ lx ≥ (0: ℝ), x + lx • d = c ∧
  ‖y - c‖ = √(3 * r ^ 2) ∧ ∃ ly ≥ (0: ℝ), y + ly • e = c

@[reducible]
def exitReady (x₀ d₀ y₀ e₀ : Vec2) := fun (x, d, y, e) =>
  ∃ lx mx : ℝ, 0 ≤ lx ∧ 0 < mx ∧ x + lx • d = x₀ + mx • d₀ ∧
  ∃ ly my : ℝ, 0 ≤ ly ∧ 0 < my ∧ y + ly • e = y₀ + my • e₀

/-- Tangential roundabout configuration `R`, equation (2). -/
@[reducible]
def R (ω : ℝ) (c : Vec2) (x d y e : Vec2) : Prop :=
  d = ω • perp (x - c) ∧ e = ω • perp (y - c)

def entryEvol (ω : ℝ) := evolve (flight (-ω) (-ω)) (fun _ => True)

def circEvol (ω : ℝ) (x₀ d₀ y₀ e₀ : Vec2) :=
  evolve
    (flight ω ω)
    (fun (x, d, y, e) => ¬exitReady x₀ d₀ y₀ e₀ (x, d, y, e) ∨
      (x, d, y, e) ∈ frontier {st | exitReady x₀ d₀ y₀ e₀ st})

def exitEvol := evolve (flight 0 0) (fun _ => True)

/-- Free flight with far separation -/
def free_f (p r : ℝ) (x d y e : Vec2) := free (far p r) x d y e

def agree_f (p : ℝ) (x d y e : Vec2) := do
  let c ← choose Vec2
  let r ← chooseS {r : ℝ | r ≥ 0}
  ensure (C r x d y e c)
  unless Separated (far p r) x y do abort
  let ω ← choose ℝ
  unless (r * ω) ^ 2 = ‖d‖ ^ 2 do abort
  return (ω, c, r)

def entry_f (ω r : ℝ) (c x d y e : Vec2) := do
  let (x, d, y, e) ← entryEvol ω (x, d, y, e)
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  return (x, d, y, e)

def circ_f (ω : ℝ) (x₀ d₀ y₀ e₀ x d y e : Vec2) := do
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  ensure (exitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  return (x, d, y, e)

def exit_f (x d y e : Vec2) := do
  let (x, d, y, e) ← exitEvol (x, d, y, e)
  --the test below from the paper would make the proof trivial
  --unless (far p r) ^ 2 ≤ ‖x - y‖ ^ 2 do abort
  return (x, d, y, e)

def ftrm (p r : ℝ) (x d y e : Vec2) := do
  let mut (x, d, y, e) := (x, d, y, e)
  let mut r := r
  let n ← choose ℕ
  for _ in [:n] do
    (x, d, y, e) ← free_f p r x d y e
    let (ω, c, r_new) ← agree_f p x d y e
    r := r_new
    let (x₀, d₀, y₀, e₀) := (x, d, y, e)
    (x, d, y, e) ← entry_f ω r c x d y e
    (x, d, y, e) ← circ_f ω x₀ d₀ y₀ e₀ x d y e
    (x, d, y, e) ← exit_f x d y e
  return (x, y)

theorem ftrm_safe :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ r > 0 ∧ Separated (far p r) x y →
        ∀ res ∈ SetM.run (ftrm p r x d y e),
          let (x_res, y_res) := res
          Separated p x_res y_res := sorry

/-! ## AC1–AC7 -/

/-- AC1 (free phase): free flight preserves far separation (its domain) and
the linear speeds. Prefix-closed, hence throughout. -/
theorem AC1_free :
    ∀ (p r : ℝ) (x d y e : Vec2), Separated (far p r) x y →
      ∀ res ∈ SetM.run (free_f p r x d y e),
        let (x', d', y', e') := res
        Separated (far p r) x' y' ∧ ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := sorry

/-- AC1 (roundabout circle, Fig. 5): the common circular flight preserves the
tangential configuration `R` and separation, for any domain. -/
theorem AC1_circ :
    ∀ (p ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ res ∈ SetM.run (evolve (flight ω ω) domain (x, d, y, e)),
          let (x', d', y', e') := res
          R ω c x' d' y' e' ∧ Separated p x' y' := sorry

/-- AC2: linear speeds are invariant under any flight, for any domain. -/
theorem AC2 :
    ∀ (ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      ∀ res ∈ SetM.run (evolve (flight ω ρ) domain (x, d, y, e)),
        let (_, d', _, e') := res
        ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := sorry

/-- AC3 (flyable entry, eq. (3)): when the entry reaches the roundabout radius,
both aircraft are in the tangential configuration `R`. The anchor points are
not hypotheses here; they exist by the entry configuration `CEntry`. -/
theorem AC3 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∀ res ∈ SetM.run (entryEvol ω (x, d, y, e)),
          let (x', d', y', e') := res
          ‖x' - c‖ ^ 2 = r ^ 2 → R ω c x' d' y' e' := sorry

/-- AC4 (bounded entry reachability, eq. (5)): there is an entry evolution
reaching both roundabout circles within `T = πr / (3‖d‖)`.
Unrestricted entry can also take extra turns; their duration is not bounded here. -/
theorem AC4 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ (duration : ℝ) (trajectory : ℝ → Vec2 × Vec2 × Vec2 × Vec2),
          0 ≤ duration ∧ duration ≤ Real.pi * r / (3 * ‖d‖) ∧
          IsEvolution trajectory (Evolvable.denotation (flight (-ω) (-ω)))
            (fun _ => True) (x, d, y, e) duration ∧
          let (xr, _, yr, _) := trajectory duration
          ‖xr - c‖ ^ 2 = r ^ 2 ∧ ‖yr - c‖ ^ 2 = r ^ 2 := sorry

/-- AC4, liveness corollary: the actual `entry_f`, including its radius test,
has a successful run reaching both roundabout circles. -/
theorem AC4_live :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ res ∈ SetM.run (entry_f ω r c x d y e),
          let (x', _, y', _) := res
          ‖x' - c‖ ^ 2 = r ^ 2 ∧ ‖y' - c‖ ^ 2 = r ^ 2 := sorry

/-- AC5 (eqs. (6), (16)): bounded-speed curved flight with arbitrary
time-varying angular speeds preserves `p`-separation for duration `≤ T`. -/
theorem AC5 :
    ∀ (p b T : ℝ) (x d y e : Vec2) (ω ρ : ℝ → ℝ),
      0 ≤ p ∧ 0 ≤ b ∧ 0 ≤ T ∧ ‖d‖ ^ 2 ≤ ‖e‖ ^ 2 ∧ ‖e‖ ^ 2 ≤ b ^ 2 ∧
      Separated (Real.sqrt 2 * (p + 2 * b * T)) x y →
        ∀ (duration : ℝ) (trajectory : ℝ → Vec2 × Vec2 × Vec2 × Vec2),
          0 ≤ duration → duration ≤ T →
          IsEvolution trajectory
            (Evolvable.denotation
              (fun (t : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2) => flight (ω t) (ρ t) st))
            (fun _ => True) (x, d, y, e) duration →
          let (x', _, y', _) := trajectory duration
          Separated p x' y' := sorry

/-- Entry separation under the far margin (eq. (8)): the bare unrestricted
entry ODE keeps `p`-separation at every time, including extra turns. -/
theorem AC5_entry :
    ∀ (p r ω : ℝ) (c x d y e : Vec2),
      0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ ∧
      Separated (far p r) x y →
        ∀ res ∈ SetM.run (entryEvol ω (x, d, y, e)),
          let (x', _, y', _) := res
          Separated p x' y' := sorry

/-- AC6 (successful negotiation): every outcome of `agree_f` meets the entry
requirements, far separation for the new radius, and speed compatibility. -/
theorem AC6 :
    ∀ (p : ℝ) (x d y e : Vec2),
      ∀ res ∈ SetM.run (agree_f p x d y e),
        let (ω, c, r) := res
        0 ≤ r ∧ C r x d y e c ∧ Separated (far p r) x y ∧
          (r * ω) ^ 2 = ‖d‖ ^ 2 := sorry

/-- AC6, feasibility (eq. (9)): choosing the simultaneous intersection of the
flight paths as center is accepted by `agree_f` (non-vacuity). -/
theorem AC6_feasible :
    ∀ (p l : ℝ) (x d y e : Vec2),
      0 < l ∧ x + l • d = y + l • e ∧ ‖d‖ = ‖e‖ ∧ 0 < ‖d‖ ∧
      Separated (far p (l * ‖d‖ / Real.sqrt 3)) x y →
        ∃ ω : ℝ, (ω, x + l • d, l * ‖d‖ / Real.sqrt 3) ∈ SetM.run (agree_f p x d y e) :=
  sorry

/-- AC7, safety (eq. (10)): straight exits from a tangential configuration
keep separation. Stated on the bare exit ODE, i.e. without the `?S(f)` guard. -/
theorem AC7 :
    ∀ (p ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ res ∈ SetM.run (exitEvol (x, d, y, e)),
          let (x', _, y', _) := res
          Separated p x' y' := sorry

/-- AC7, liveness (eq. (11)): with different exit directions the aircraft
become arbitrarily far apart, so the exit guard `?S(f)` can be passed. -/
theorem AC7_live :
    ∀ (ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ d ≠ e →
        ∀ a : ℝ, ∃ res ∈ SetM.run (exitEvol (x, d, y, e)),
          let (x', _, y', _) := res
          a ^ 2 < ‖x' - y'‖ ^ 2 := sorry

/-! ## Gluing for the maneuver (Fig. 11) -/

/-- Completed iterations preserve separation and equal speeds. Negotiation
establishes the stronger far separation needed before each new entry. -/
@[reducible]
def Inv (p : ℝ) := fun (x, (d : Vec2), y, (e : Vec2), (r : ℝ)) =>
  0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y

/-- One iteration of `ftrm`, retaining velocities and the agreed radius. -/
def ftrmBody (p : ℝ) := fun (x, d, y, e, r) => do
  let (x, d, y, e) ← free_f p r x d y e
  let (ω, c, r) ← agree_f p x d y e
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← entry_f ω r c x d y e
  let (x, d, y, e) ← circ_f ω x₀ d₀ y₀ e₀ x d y e
  let (x, d, y, e) ← exit_f x d y e
  return (x, d, y, e, r)

/-- FTRM stopped inside phase `k`, before that phase's trailing test.
The entry evolution has domain `True`, exactly as in `entry_f`. -/
def ftrmPrefix (p : ℝ) (k : Fin 5) := fun (x, d, y, e, r) => do
  let (x, d, y, e) ← free_f p r x d y e
  if k = 0 then return (x, y)
  let (ω, c, r) ← agree_f p x d y e
  if k = 1 then return (x, y)
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← evolve (flight (-ω) (-ω)) (fun _ => True) (x, d, y, e)
  if k = 2 then return (x, y)
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  if k = 3 then return (x, y)
  ensure (exitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← exitEvol (x, d, y, e)
  return (x, y)

/-- A complete iteration preserves separation and equal speeds. -/
theorem ftrmBody_inv :
    ∀ (p : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2 × ℝ), Inv p st →
      ∀ res ∈ SetM.run (ftrmBody p st), Inv p res := sorry

/-- Every phase prefix of the iteration is safe, including unrestricted
entry before its radius test and exit without a final separation test. -/
theorem ftrmPrefix_safe :
    ∀ (p : ℝ) (k : Fin 5) (st : Vec2 × Vec2 × Vec2 × Vec2 × ℝ), Inv p st →
      ∀ res ∈ SetM.run (ftrmPrefix p k st),
        let (xr, yr) := res
        Separated p xr yr := sorry

/-- Throughout safety for the FTRM: after any number of its
completed iterations, every prefix of every additional phase is separated.
Entry may take arbitrarily many turns and exit has no final separation guard. -/
theorem ftrm_safe_throughout :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ st ∈ SetM.run (loop (ftrmBody p) (x, d, y, e, r)),
          ∀ k : Fin 5, ∀ res ∈ SetM.run (ftrmPrefix p k st),
            let (xr, yr) := res
            Separated p xr yr := sorry

end FM09
