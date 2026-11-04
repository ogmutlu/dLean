import dLean.Core.ODE
import Mathlib.Analysis.InnerProductSpace.PiL2

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

/-!
## Non-flyable tangential roundabout maneuver
-/

/-- Free flight by choosing arbitrary angular velocities -/
def free (p : ℝ) (x d y e : Vec2) := do
  let mut (x, d, y, e) := (x, d, y, e)
  let n ← choose ℕ
  for _ in [:n] do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← evolve (flight ω ρ)
                   (fun (x, (_: Vec2), y, (_: Vec2)) => Separated p x y)
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

/-!
## NTRM for any finite number of aircraft
This generalizes the paper's 5 aircraft scenario.
-/

/-- Every pair of distinct aircraft respects the protected separation. -/
@[reducible] def SeparatedMany {n : ℕ} (p : ℝ) (x : Fin n → Vec2) : Prop :=
  ∀ i j, i ≠ j → Separated p (x i) (x j)

/-- All velocities are tangential to the same roundabout. -/
@[reducible] def RMany {n : ℕ} (ω : ℝ) (c : Vec2) (x d : Fin n → Vec2) : Prop :=
  ∀ i, d i = ω • perp (x i - c)

/-- Simultaneous planar flight, with independent angular velocities. -/
def flight_many {n : ℕ} (ω : Fin n → ℝ) :
    (Fin n → Vec2) × (Fin n → Vec2) → (Fin n → Vec2) × (Fin n → Vec2) :=
  fun (_, d) => (d, fun i => ω i • perp (d i))

/-- Arbitrarily many free-flight segments, restricted by mutual separation. -/
def free_many {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let mut (x, d) := (x, d)
  let iterations ← choose ℕ
  for _ in [:iterations] do
    let ω ← choose (Fin n → ℝ)
    (x, d) ← evolve (flight_many ω)
      (fun ((x : Fin n → Vec2), (_ : Fin n → Vec2)) => SeparatedMany p x) (x, d)
  return (x, d)

/-- Instantaneous tangential entry for all aircraft around the shared center. -/
def entry_n_many {n : ℕ} (ω : ℝ) (c : Vec2) (x : Fin n → Vec2) : Fin n → Vec2 :=
  fun i => ω • perp (x i - c)

def ntrm_many {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let mut (x, d) := (x, d)
  let iterations ← choose ℕ
  for _ in [:iterations] do
    (x, d) ← free_many p x d
    let (ω, c) ← agree
    d := entry_n_many ω c x
    (x, d) ← evolve (flight_many (fun _ => ω)) (fun _ => True) (x, d)
  return x

/-!
## Fully-flyable tangential roundabout maneuver
-/

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
  return (x, d, y, e, r)

def ftrmPrefix (p r : ℝ) (k : Fin 5) (x d y e : Vec2) := do
  --free
  let (x, d, y, e) ← free_f p r x d y e
  if k = 0 then return (x, y)
  --agree
  let (ω, c, r) ← agree_f p x d y e
  if k = 1 then return (x, y)
  --entry
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← entryEvol ω (x, d, y, e)
  if k = 2 then return (x, y)
  --circ
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  if k = 3 then return (x, y)
  --exit
  ensure (exitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← exitEvol (x, d, y, e)
  return (x, y)

/-!
## Theorem 1: replacing the flyable entry procedure

The time bound may depend on the negotiated geometry and the initial state.
`entry r ω c x d y e` chooses independent, time-varying turn-rate controls.
`modifiedEntryEvol` runs their flight dynamics together with a clock, initially zero,
in the domain `t ≤ T`. The entry contract applies before the completion test `t = T`,
so it covers every intermediate state of every permitted evolution.
-/

abbrev EntryProcedure :=
  ℝ → ℝ → Vec2 → Vec2 → Vec2 → Vec2 → Vec2 →
    SetM ((ℝ → ℝ) × (ℝ → ℝ))

abbrev EntryTimeBound := ℝ → ℝ → Vec2 → Vec2 → Vec2 → Vec2 → Vec2 → ℝ

/-- Independent entry turn rates, synchronized with the clock equation `t' = 1`. -/
def entryDynamics (turnX turnY : ℝ → ℝ) :=
  ((fun (t : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2) => flight (turnX t) (turnY t) st),
    (fun (_t : ℝ) => (1 : ℝ)))

def entryDomain (T : ℝ) : (Vec2 × Vec2 × Vec2 × Vec2) × ℝ → Prop :=
  fun (_, t) => t ≤ T

/-- Clocked entry evolution, including all stopping times up to the entry deadline.
Its domain contains no separation or tangency constraint. -/
def modifiedEntryEvol (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) := do
  let (turnX, turnY) ← entry r ω c x d y e
  evolve (entryDynamics turnX turnY) (entryDomain (bound r ω c x d y e))
    ((x, d, y, e), (0 : ℝ))

/-- Theorem 1's modified-entry premise, checked on states admitted by negotiation:
safe distance throughout `[0,T]`, and tangency at `T`. Flight dynamics and clock motion
are supplied by `evolve`, and speed preservation follows from those dynamics. As with
the paper's boxed premise, this contract does not assert existence of a complete run. -/
def ModifiedEntryContract (entry : EntryProcedure) (bound : EntryTimeBound) (p : ℝ) : Prop :=
  ∀ (r ω : ℝ) (c x d y e : Vec2),
    0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y →
    let T := bound r ω c x d y e
    0 ≤ T ∧ ∀ res ∈ SetM.run (modifiedEntryEvol entry bound r ω c x d y e),
      let st := res.1
      let t := res.2
      Separated p st.1 st.2.2.1 ∧
      (t = T → R ω c st.1 st.2.1 st.2.2.1 st.2.2.2)

def modifiedEntryComplete (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) := do
  let T := bound r ω c x d y e
  let (st, t) ← modifiedEntryEvol entry bound r ω c x d y e
  ensure (t = T)
  return st

def modifiedEntryPrefix (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) := do
  let (st, _t) ← modifiedEntryEvol entry bound r ω c x d y e
  return st

/-- Theorem 1: the original FTRM cycle with only its entry procedure replaced. -/
def ftrmModified (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (x d y e : Vec2) := do
  let mut (x, d, y, e) := (x, d, y, e)
  let mut r := r
  let n ← choose ℕ
  for _ in [:n] do
    (x, d, y, e) ← free_f p r x d y e
    let (ω, c, r_new) ← agree_f p x d y e
    r := r_new
    let (x₀, d₀, y₀, e₀) := (x, d, y, e)
    (x, d, y, e) ← modifiedEntryComplete entry bound r ω c x d y e
    (x, d, y, e) ← circ_f ω x₀ d₀ y₀ e₀ x d y e
    (x, d, y, e) ← exit_f x d y e
  return (x, d, y, e, r)

/-- Observation of every phase of the modified cycle, including entry times before `T`
and circular-flight times before the exit-ready test. -/
def ftrmModifiedPrefix (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (k : Fin 5) (x d y e : Vec2) := do
  let (x, d, y, e) ← free_f p r x d y e
  if k = 0 then return (x, y)
  let (ω, c, r) ← agree_f p x d y e
  if k = 1 then return (x, y)
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  if k = 2 then
    let (x, _, y, _) ← modifiedEntryPrefix entry bound r ω c x d y e
    return (x, y)
  let (x, d, y, e) ← modifiedEntryComplete entry bound r ω c x d y e
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  if k = 3 then return (x, y)
  ensure (exitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← exitEvol (x, d, y, e)
  return (x, y)

end FM09
