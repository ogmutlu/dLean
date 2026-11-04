import dLean.Core.QODE
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# IJRR 2017: ground-robot obstacle avoidance and navigation

Sources: Mitsch, Ghorbal, Vogelbacher, and Platzer, *Formal verification of obstacle
avoidance and navigation of ground robots*, IJRR 36(12), 1312--1340 (2017), and the
authors' `keymaera/IJRR17/keYmaeraX/robix.kyx` archive at revision
`b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`.

This replaces the earlier RSS 2013 transcription. The scope is all main journal
Theorems 1--12 and archive Corollaries 1.1--1.3 and 2. The archive supplies
Theorems 1--9 and 11--12; Model 12 / Theorem 10
is transcribed directly from journal Section 7.4, since it is absent from the
KeYmaera X archive. Supplementary Theorems 13--15 are outside this scope.

The archive supplies the exact program choices and initial assumptions where the
printed article differs. See `keymaera/IJRR17/README.md` for the correspondence and
discrepancies, including refined-obstacle control, orientation control, and waypoint
bounds. No semantic equivalence with a KeYmaera encoding is proved by this file.

`p d o v` are planar vectors: robot position/direction and obstacle position/velocity.
`s` is robot speed, `ω` angular velocity, and `r` a signed curve radius. A continuous
phase keeps `r`, acceleration, and obstacle velocity fixed. Direction is preserved
at control steps. Norms are Euclidean; `infNorm` is the maximum absolute coordinate.
There are no trailing collision tests. Every physical phase permits arbitrary
stopping times. Finite repetitions include zero iterations.
-/

open dLean

namespace IJRR17

noncomputable section

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

@[simp] def perp (d : Vec2) : Vec2 := !₂[-d 1, d 0]

def infNorm (p : Vec2) : ℝ := max |p 0| |p 1|

/-- Squared Euclidean separation, matching the polynomial archive postconditions. -/
def distanceSq (p o : Vec2) : ℝ := (p 0 - o 0) ^ 2 + (p 1 - o 1) ^ 2

@[reducible]
def UnitDirection (d : Vec2) : Prop := d 0 ^ 2 + d 1 ^ 2 = 1

/-- Bounds shared by archive Theorems 1--9. `Ω` only bounds steering choices. -/
@[reducible]
def Bounds (A b V ε : ℝ) : Prop := 0 ≤ A ∧ 0 < b ∧ 0 ≤ V ∧ 0 < ε

/-- Initial state of archive Theorems 1, 2, and 5--9 (no extra radius assumption). -/
@[reducible]
def Initial (p d o : Vec2) (s : ℝ) : Prop :=
  s = 0 ∧ 0 < distanceSq p o ∧ UnitDirection d

/-- Journal (5): a signed nonzero radius, without a curve-center variable. -/
@[reducible]
def Curve (s ω r : ℝ) : Prop := r ≠ 0 ∧ r * ω = s

def stopDist (b s : ℝ) : ℝ := s ^ 2 / (2 * b)

/-- Journal (23), also the archive's stopDist + accelComp. Setting `V = 0`
gives static safety (7). `A` is replaced by the chosen acceleration in (43). -/
def stoppingMargin (A b V ε s : ℝ) : ℝ :=
  stopDist b s + V * s / b + (A / b + 1) * (A / 2 * ε ^ 2 + ε * (s + V))

@[reducible]
def Safe (A b V ε : ℝ) (p o : Vec2) (s : ℝ) : Prop :=
  stoppingMargin A b V ε s < infNorm (p - o)

/-- The shared collision-exclusion target, journal (26), archive Theorems 2, 5--9. -/
@[reducible]
def PassiveSafe (p o : Vec2) (s : ℝ) : Prop := 0 < s → 0 < distanceSq p o

/-- Joint motion (24), with fixed radius `r`; the clock is composed separately. -/
def motion (a r : ℝ) (v : Vec2) :=
  fun ((_p : Vec2), d, (_o : Vec2), (s : ℝ), (ω : ℝ)) =>
    (s • d, ω • perp d, v, a, a / r)

@[simp] def time : ℝ → ℝ := fun _ => 1

def domain (ε : ℝ) : (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ → Prop :=
  fun ((_p, _d, _o, s, _ω), t) => t ≤ ε ∧ 0 ≤ s

def dyn (ε a r : ℝ) (v p d o : Vec2) (s ω : ℝ) := do
  let (res, _t) ← evolve (motion a r v, time) (domain ε) ((p, d, o, s, ω), 0)
  return res

/-- Obstacle control (22). Squared speed bound as in the archive. -/
def ctrl_o (V : ℝ) : SetM Vec2 := do
  let v ← choose Vec2
  ensure (v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2)
  return v

/-- Journal Model 1 / archive robot controller. The actual speed controls the
stopped branch and curve consistency. Only the safety guard uses sensed speed.
Returns acceleration, angular velocity, radius, and reselected obstacle position. -/
def ctrl_r (b Ω : ℝ) (drive : SetM ℝ) (safe : Vec2 → Vec2 → ℝ → ℝ → Prop)
    (pMeasured o : Vec2) (s sMeasured ω r : ℝ) : SetM (ℝ × ℝ × ℝ × Vec2) :=
  (pure (-b, ω, r, o))
    <|>
  (do
    ensure (s = 0)
    return (0, 0, r, o))
    <|>
  (do
    let a ← drive
    let ω ← choose ℝ
    ensure (-Ω ≤ ω ∧ ω ≤ Ω)
    let r ← choose ℝ
    let o ← choose Vec2
    ensure (Curve s ω r ∧ safe pMeasured o sMeasured a)
    return (a, ω, r, o))

/-- Shared loop for Models 2--4 and 7--10. Control retains the physical direction.
`sense` precedes obstacle/robot control; `act` follows it. Returns
`(p, d, o, s, ω, r, v)`, retaining the current radius and obstacle velocity. -/
def dynamicWindow (b Ω ε : ℝ) (obstacleControl : SetM Vec2) (drive : SetM ℝ)
    (safe : Vec2 → Vec2 → ℝ → ℝ → Prop)
    (sense : Vec2 → ℝ → SetM (Vec2 × ℝ)) (act : ℝ → SetM ℝ)
    (p d o v : Vec2) (s ω r : ℝ) := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n] do
    let (pMeasured, sMeasured) ← sense p s
    v ← obstacleControl
    let (a, ω_new, r_new, o_new) ← ctrl_r b Ω drive safe pMeasured o s sMeasured ω r
    ω := ω_new
    r := r_new
    o := o_new
    let aActual ← act a
    (p, d, o, s, ω) ← dyn ε aActual r v p d o s ω
  return (p, d, o, s, ω, r, v)

/-- Model 2 / archive Theorem 1: stationary obstacles. -/
def dwss (A b Ω ε : ℝ) (p d o : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (pure 0) (pure A) (fun p o s _ => Safe A b 0 ε p o s)
    (fun p s => pure (p, s)) (fun a => pure a) p d o 0 s ω r

/-! ### Corollaries 1.2 and 1.3: margins for imperfect trajectories -/

/-- Archive "Corollary 1.2: Static safety with margin for imperfect trajectories":
the squared direction length is within `Δd` of one. -/
@[reducible]
def ApproxDirection (Δd : ℝ) (d : Vec2) : Prop :=
  1 - Δd ≤ d 0 ^ 2 + d 1 ^ 2 ∧ d 0 ^ 2 + d 1 ^ 2 ≤ 1 + Δd

@[reducible]
def ImperfectInitial (Δd : ℝ) (p d o : Vec2) (s : ℝ) : Prop :=
  s = 0 ∧ 0 < distanceSq p o ∧ ApproxDirection Δd d

/-- Corollary 1.2's margin scales both stopping and reaction distance by `1 + Δd`. -/
@[reducible]
def ImperfectSafe (A b ε Δd : ℝ) (p o : Vec2) (s : ℝ) : Prop :=
  (1 + Δd) * stoppingMargin A b 0 ε s < infNorm (p - o)

/-- Archive "Corollary 1.2: Static safety with margin for imperfect trajectories". -/
def dwss_imperfect (A b Ω ε Δd : ℝ) (p d o : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (pure 0) (pure A) (fun p o s _ => ImperfectSafe A b ε Δd p o s)
    (fun p s => pure (p, s)) (fun a => pure a) p d o 0 s ω r

/-- Archive "Corollary 1.3: Static safety with margin for imperfect trajectories
(no division)": the polynomial clearance guard, before division by `2*b`. -/
@[reducible]
def ImperfectSafeNoDiv (A b ε Δd : ℝ) (p o : Vec2) (s : ℝ) : Prop :=
  (1 + Δd) * s ^ 2 + (1 + Δd) * (A + b) * (A * ε ^ 2 + 2 * ε * s) <
    2 * b * infNorm (p - o)

/-- Archive "Corollary 1.3: Static safety with margin for imperfect trajectories
(no division)". As in the other models, acceleration and the reset clock are local;
their source initial values `a = t = 0` do not affect this projected safety program.
The source's initial `ω = 0` and `r = 1` are retained in its challenge theorem. -/
def dwss_imperfect_no_div (A b Ω ε Δd : ℝ) (p d o : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (pure 0) (pure A) (fun p o s _ => ImperfectSafeNoDiv A b ε Δd p o s)
    (fun p s => pure (p, s)) (fun a => pure a) p d o 0 s ω r

/-- Model 3 / archive Theorem 2: passive safety with maximum acceleration. -/
def dwps (A b V Ω ε : ℝ) (p d o v : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (ctrl_o V) (pure A) (fun p o s _ => Safe A b V ε p o s)
    (fun p s => pure (p, s)) (fun a => pure a) p d o v s ω r

/-! ### Corollary 1.1: instantaneous velocity control -/

/-- Archive "Corollary 1.1: Velocity-controlled passive safety": no braking
distance is needed because the controller can set the speed to zero instantly. -/
@[reducible]
def VelocitySafe (V ε : ℝ) (p o : Vec2) (s : ℝ) : Prop :=
  ε * (s + V) < infNorm (p - o)

/-- Corollary 1.1's stop-or-select-velocity controller. -/
def velocityRobotControl (V Ω ε : ℝ) (p o : Vec2) (_s _ω r : ℝ) :=
  (pure (0, 0, r, o)) <|> (do
    let s ← choose ℝ
    ensure (0 ≤ s)
    let ω ← choose ℝ
    ensure (-Ω ≤ ω ∧ ω ≤ Ω)
    let r ← choose ℝ
    let o ← choose Vec2
    ensure (Curve s ω r ∧ VelocitySafe V ε p o s)
    return (s, ω, r, o))

/-- Archive "Corollary 1.1: Velocity-controlled passive safety". Using `motion 0`
keeps the selected speed and angular velocity fixed during each physical phase. -/
def dwps_velocity (V Ω ε : ℝ) (p d o v : Vec2) (s ω r : ℝ) := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n] do
    v ← ctrl_o V
    let (s_new, ω_new, r_new, o_new) ← velocityRobotControl V Ω ε p o s ω r
    s := s_new
    ω := ω_new
    r := r_new
    o := o_new
    (p, d, o, s, ω) ← dyn ε 0 r v p d o s ω
  return (p, d, o, s, ω, r, v)

/-! ## Models 4--5: passive-friendly safety -/

def friendlyMargin (bo τ V : ℝ) : ℝ := V ^ 2 / (2 * bo) + τ * V

def dwpfs (A b bo τ V Ω ε : ℝ) (p d o v : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (ctrl_o V) (pure A)
    (fun p o s _ => stoppingMargin A b V ε s + friendlyMargin bo τ V < infNorm (p - o))
    (fun p s => pure (p, s)) (fun a => pure a) p d o v s ω r

/-- Archive Theorem 3's refined obstacle: fixed direction, acceleration at least
`-bo`, and positive physical step bound `ε` (not the possibly zero allowance `τ`). -/
def obstacleMotion (do_ : Vec2) (ao : ℝ) : Vec2 × ℝ → Vec2 × ℝ :=
  fun (_o, so) => (so • do_, ao)

def obstacleDomain (ε : ℝ) : (Vec2 × ℝ) × ℝ → Prop :=
  fun ((_o, so), t) => 0 ≤ so ∧ t ≤ ε

def obstacle (bo V ε : ℝ) (do_ o : Vec2) (so : ℝ) := do
  let mut (o, so) := (o, so)
  let n ← choose ℕ
  for _ in [:n] do
    let ao ← choose ℝ
    ensure (-bo ≤ ao ∧ so + ao * ε ≤ V)
    let (res, _t) ← evolve (obstacleMotion do_ ao, time) (obstacleDomain ε) ((o, so), 0)
    (o, so) := res
  return (o, so)

/-- Archive Theorem 3's initial state, including stoppedness and bounded coarse
obstacle velocity. These are stronger than the printed formula (36). -/
@[reducible]
def FriendlyInitial (bo τ V : ℝ) (p d o v : Vec2) (s : ℝ) : Prop :=
  s = 0 ∧ friendlyMargin bo τ V < infNorm (p - o) ∧
    v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 ∧ UnitDirection d

/-- Exact polynomial/vector form of the archived safety-and-diamond target.
The robot is fixed in the separate obstacle-stopping program. The diamond is
conditional on clearance and velocity/direction consistency, not robot stoppedness. -/
@[reducible]
def PassiveFriendlySafe (bo τ V ε : ℝ) (p o v : Vec2) (s : ℝ) : Prop :=
  (0 < s → friendlyMargin bo τ V ^ 2 < distanceSq p o) ∧
  (∀ (so : ℝ) (do_ : Vec2),
    (0 ≤ so ∧ so ^ 2 = v 0 ^ 2 + v 1 ^ 2 ∧ so • do_ = v ∧
      friendlyMargin bo τ V ^ 2 < distanceSq p o) →
      ∃ res ∈ SetM.run (obstacle bo V ε do_ o so), 0 < distanceSq p res.1 ∧ res.2 = 0)

/-! ## Model 6: passive orientation safety -/

def orientationMotion (a r : ℝ) (v : Vec2) :=
  fun ((_p : Vec2), d, (_o : Vec2), (s : ℝ), (ω : ℝ), (_β : ℝ)) =>
    (s • d, ω • perp d, v, a, a / r, ω)

def orientationDomain (ε : ℝ) : (Vec2 × Vec2 × Vec2 × ℝ × ℝ × ℝ) × ℝ → Prop :=
  fun ((_p, _d, _o, s, _ω, _β), t) => t ≤ ε ∧ 0 ≤ s

/-- Archive Theorem 4's controller. It resets angular progress on a new curve,
and reestablishes `r * ω = s` before every evolution, without a steering bound. -/
def orientationControl (A b V ε γ : ℝ) (p o : Vec2) (s ω r β visible : ℝ) :=
  (pure (-b, ω, r, o, β, visible))
    <|>
  (do
    ensure (s = 0)
    return (0, 0, r, o, β, visible))
    <|>
  (do
    let r ← choose ℝ
    ensure (r ≠ 0)
    let o ← choose Vec2
    let visible ← choose ℝ
    ensure (0 < visible → Safe A b V ε p o s)
    ensure (stoppingMargin A b 0 ε s < γ * |r|)
    return (A, ω, r, o, 0, visible))

def dwpos (A b V ε γ : ℝ) (p d o v : Vec2) (s ω r β visible : ℝ) := do
  let mut (p, d, o, s, ω, r, v, β, visible) := (p, d, o, s, ω, r, v, β, visible)
  let n ← choose ℕ
  for _ in [:n] do
    v ← ctrl_o V
    let (a, ω_new, r_new, o_new, β_new, visible_new) ←
      orientationControl A b V ε γ p o s ω r β visible
    ω := ω_new
    r := r_new
    o := o_new
    β := β_new
    visible := visible_new
    ω ← choose ℝ
    ensure (ω * r = s)
    let (res, _t) ← evolve (orientationMotion a r v, time) (orientationDomain ε)
      ((p, d, o, s, ω, β), 0)
    (p, d, o, s, ω, β) := res
  return (p, d, o, s, ω, r, v, β, visible)

/-! ### Corollary 2: velocity-controlled passive orientation safety -/

/-- Archive "Corollary 2: Velocity-controlled passive orientation safety".
The archive does not test `0 ≤ s` here; the subsequent evolution domain does. -/
def velocityOrientationControl (V ε γ : ℝ) (p o : Vec2) (_s ω r β visible : ℝ) :=
  (pure (0, 0, r, o, β, visible)) <|> (do
    let s ← choose ℝ
    let r ← choose ℝ
    ensure (r ≠ 0)
    let o ← choose Vec2
    let visible ← choose ℝ
    ensure (0 < visible → VelocitySafe V ε p o s)
    ensure (ε * s < γ * |r|)
    return (s, ω, r, o, 0, visible))

/-- Archive "Corollary 2: Velocity-controlled passive orientation safety".
Every iteration resets the clock and reestablishes `ω*r = s` before evolution. -/
def dwpos_velocity (V ε γ : ℝ) (p d o v : Vec2) (s ω r β visible : ℝ) := do
  let mut (p, d, o, s, ω, r, v, β, visible) := (p, d, o, s, ω, r, v, β, visible)
  let n ← choose ℕ
  for _ in [:n] do
    v ← ctrl_o V
    let (s_new, ω_new, r_new, o_new, β_new, visible_new) ←
      velocityOrientationControl V ε γ p o s ω r β visible
    s := s_new
    ω := ω_new
    r := r_new
    o := o_new
    β := β_new
    visible := visible_new
    ω ← choose ℝ
    ensure (ω * r = s)
    let (res, _t) ← evolve (orientationMotion 0 r v, time) (orientationDomain ε)
      ((p, d, o, s, ω, β), 0)
    (p, d, o, s, ω, β) := res
  return (p, d, o, s, ω, r, v, β, visible)

/-! ## Models 7--10: actual acceleration and uncertainty -/

def driveActual (A b : ℝ) : SetM ℝ := do
  let a ← choose ℝ
  ensure (-b ≤ a ∧ a ≤ A)
  return a

/-- Archive Theorem 5's piecewise stopping margin, journal (42)--(44). -/
def actualMargin (b V ε s a : ℝ) : ℝ :=
  if 0 ≤ s + a * ε then stoppingMargin a b V ε s
  else -(s ^ 2) / (2 * a) - V * s / a

def dwpsa (A b V Ω ε : ℝ) (p d o v : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (ctrl_o V) (driveActual A b)
    (fun p o s a => actualMargin b V ε s a < infNorm (p - o))
    (fun p s => pure (p, s)) (fun a => pure a) p d o v s ω r

def locate (Δp : ℝ) (p : Vec2) (s : ℝ) : SetM (Vec2 × ℝ) := do
  let measured ← choose Vec2
  ensure (distanceSq measured p ≤ Δp ^ 2)
  return (measured, s)

def dwpslu (A b V Ω ε Δp : ℝ) (p d o v : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (ctrl_o V) (pure A)
    (fun p o s _ => stoppingMargin A b V ε s + Δp < infNorm (p - o))
    (locate Δp) (fun a => pure a) p d o v s ω r

def act (Δa a : ℝ) : SetM ℝ := do
  let δa ← choose ℝ
  ensure (Δa ≤ δa ∧ δa ≤ 1)
  return δa * a

def dwpsap (A b V Ω ε Δa : ℝ) (p d o v : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (ctrl_o V) (pure A)
    (fun p o s _ => Safe A (b * Δa) V ε p o s)
    (fun p s => pure (p, s)) (act Δa) p d o v s ω r

/-- Returns the maximum speed consistent with the measured nonnegative speed. -/
def sense (Δs : ℝ) (p : Vec2) (s : ℝ) : SetM (Vec2 × ℝ) := do
  let measured ← choose ℝ
  ensure (0 ≤ measured ∧ s - Δs ≤ measured ∧ measured ≤ s + Δs)
  return (p, measured + Δs)

def dwpsvu (A b V Ω ε Δs : ℝ) (p d o v : Vec2) (s ω r : ℝ) :=
  dynamicWindow b Ω ε (ctrl_o V) (pure A) (fun p o s _ => Safe A b V ε p o s)
    (sense Δs) (fun a => pure a) p d o v s ω r

/-! ## Model 11: asynchronous obstacle control -/

/-- The clock is reset only at the outer robot-control step. Each inner obstacle
step continues that same clock, preserving the total reaction bound `ε`. -/
def dwpsns (A b V Ω ε : ℝ) (p d o v : Vec2) (s ω r : ℝ) := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n] do
    let (a, ω_new, r_new, o_new) ←
      ctrl_r b Ω (pure A) (fun p o s _ => Safe A b V ε p o s) p o s s ω r
    ω := ω_new
    r := r_new
    o := o_new
    let mut t : ℝ := 0
    let m ← choose ℕ
    for _ in [:m] do
      v ← ctrl_o V
      let (res, t_new) ← evolve (motion a r v, time) (domain ε) ((p, d, o, s, ω), t)
      (p, d, o, s, ω) := res
      t := t_new
  return (p, d, o, s, ω, r, v)

/-! ## Model 12: countably many explicitly tracked obstacles -/

/-- Natural-number labels and an arbitrary active set represent finite as well
as countably infinite obstacle populations. No finite enumeration is assumed. -/
abbrev Obstacle := ℕ

/-- Equation (56): any finite number of active obstacles may update velocity.
An obstacle's position is never reselected. Unselected velocities retain their
previous values, including when the chosen number of updates is zero. -/
def ctrl_o_nobs (O : Set Obstacle) (V : Obstacle → ℝ) (v : Obstacle → Vec2) := do
  let mut v := v
  let n ← choose ℕ
  for _ in [:n] do
    let i ← chooseS O
    let vi ← choose Vec2
    ensure (‖vi‖ ≤ V i)
    v := Function.update v i vi
  return v

/-- Equation (57): the actual-acceleration clearance for every tracked obstacle. -/
@[reducible]
def SafeNobs (b ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p : Vec2) (o : Obstacle → Vec2) (s a : ℝ) : Prop :=
  ∀ i ∈ O, actualMargin b (V i) ε s a < infNorm (p - o i)

/-- Equation (55), specializing the parametric robot controller to tracked
positions: unlike the summary-obstacle models, there is no `o := *` assignment. -/
def ctrl_r_nobs (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p : Vec2) (o : Obstacle → Vec2) (s ω r : ℝ) : SetM (ℝ × ℝ × ℝ) :=
  (pure (-b, ω, r))
    <|>
  (do
    ensure (s = 0)
    return (0, 0, r))
    <|>
  (do
    let a ← driveActual A b
    let ω ← choose ℝ
    ensure (-Ω ≤ ω ∧ ω ≤ Ω)
    let r ← choose ℝ
    ensure (Curve s ω r ∧ SafeNobs b ε O V p o s a)
    return (a, ω, r))

/-- Robot part of printed (58). Its negative angular sign is retained literally;
earlier journal models and the KeYmaera X archive use a positive sign instead. -/
def robotMotionNobs (a r : ℝ) : Vec2 × Vec2 × ℝ × ℝ → Vec2 × Vec2 × ℝ × ℝ :=
  fun (_p, d, s, ω) => (s • d, (-ω) • perp d, a, a / r)

/-- Obstacle part of (58): coordinatewise evolution of every active position.
This QODE needs no norm on the infinite collection of obstacle positions. -/
def obstaclesMotionNobs (O : Set Obstacle) (v : Obstacle → Vec2) :
    Set Obstacle × ((Obstacle → Vec2) → (Obstacle → Vec2)) :=
  (O, fun _o => v)

def nobsDomain (ε : ℝ) :
    ((Vec2 × Vec2 × ℝ × ℝ) × (Obstacle → Vec2)) × ℝ → Prop :=
  fun (((_p, _d, s, _ω), _o), t) => 0 ≤ s ∧ t ≤ ε

/-- One shared physical duration for the robot ODE, all active obstacle QODE
coordinates, and clock. Inactive coordinates are not constrained by the QODE. -/
def dyn_nobs (ε a r : ℝ) (O : Set Obstacle) (v : Obstacle → Vec2)
    (p d : Vec2) (o : Obstacle → Vec2) (s ω : ℝ) := do
  let (((p, d, s, ω), o), _t) ← evolve
    ((robotMotionNobs a r, obstaclesMotionNobs O v), time) (nobsDomain ε)
    (((p, d, s, ω), o), 0)
  return (p, d, o, s, ω)

/-- Model 12, equation (55). Returns `(p, d, o, s, ω, r, v)`, with total
position/velocity functions and the current radius. The printed initial state
(59) imposes no obstacle-velocity bound; no such bound is silently added here. -/
def dwnobs (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o v : Obstacle → Vec2) (s ω r : ℝ) := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n] do
    v ← ctrl_o_nobs O V v
    let (a, ω_new, r_new) ← ctrl_r_nobs A b Ω ε O V p o s ω r
    ω := ω_new
    r := r_new
    (p, d, o, s, ω) ← dyn_nobs ε a r O v p d o s ω
  return (p, d, o, s, ω, r, v)

/-! ## Models 13--14: waypoint and intersection liveness -/

def lineMotion (a : ℝ) : ℝ × ℝ → ℝ × ℝ := fun (_p, s) => (s, a)

def lineDomain (ε : ℝ) : (ℝ × ℝ) × ℝ → Prop :=
  fun ((_p, s), t) => t ≤ ε ∧ 0 ≤ s

/-- Archive Theorem 11's four control branches. The last branch uses independent
bounds `a ≤ (Vg-s)/ε` and `a ≤ A`, as in the executable archive. -/
def waypointControl (A b ε g Δg Vg p s : ℝ) : SetM ℝ :=
  (pure (-b))
    <|>
  (do
    ensure (s = 0)
    return 0)
    <|>
  (do
    ensure (p + stoppingMargin A b 0 ε s < g + Δg ∧ s + A * ε ≤ Vg)
    return A)
    <|>
  (do
    ensure (p ≤ g - Δg ∧ s ≤ Vg)
    let a ← choose ℝ
    ensure (-b ≤ a ∧ a ≤ (Vg - s) / ε ∧ a ≤ A)
    return a)

def dwwp (A b ε g Δg Vg p s : ℝ) := do
  let mut (p, s) := (p, s)
  let n ← choose ℕ
  for _ in [:n] do
    let a ← waypointControl A b ε g Δg Vg p s
    let (res, _t) ← evolve (lineMotion a, time) (lineDomain ε) ((p, s), 0)
    (p, s) := res
  return (p, s)

/-- Archive Theorem 11's parameter conditions, stronger than printed (69). -/
@[reducible]
def WaypointBounds (A b ε Δg Vg : ℝ) : Prop :=
  0 < A ∧ 0 < b ∧ 0 < ε ∧ 2 * A * ε ≤ Vg ∧ Vg * ε + stopDist b Vg < Δg

/-- Intersections are at zero on both one-dimensional paths, as in the archive. -/
@[reducible]
def AfterX (p o : ℝ) : Prop := 0 < p ∨ 0 < o

@[reducible]
def PassFaster (A Vmin ε p s o v : ℝ) : Prop :=
  0 < s ∧ (o + v * (-p / s) + A / 2 * (-p / s) ^ 2 < 0 ∨
    0 < o + Vmin * (-p) / (s + A * ε))

@[reducible]
def PassCoast (Vmin p s o : ℝ) : Prop := 0 < s ∧ 0 < o + Vmin * (-p) / s

/-- Ordered controller branches of archive Theorem 12, not nondeterministic tests
that would also permit the fallback when an earlier condition holds. -/
def intersectionControl (A b Vmin ε p s o v : ℝ) : SetM ℝ := do
  if AfterX p o then
    driveActual A b
  else if PassFaster A Vmin ε p s o v then
    let a ← choose ℝ
    ensure (0 ≤ a ∧ a ≤ A)
    return a
  else if PassCoast Vmin p s o then
    return 0
  else
    (pure (-b)) <|>
      (do ensure (s = 0); return 0) <|>
      (do ensure (p + stoppingMargin A b 0 ε s < 0); return A)

def intersectionMotion (a ao : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_p, s, _o, v) => (s, a, v, ao)

def intersectionDomain (ε Vmin : ℝ) : (ℝ × ℝ × ℝ × ℝ) × ℝ → Prop :=
  fun ((_p, s, _o, v), t) => t ≤ ε ∧ 0 ≤ s ∧ Vmin ≤ v

def dwcx (A b Vmin ε p s o v : ℝ) := do
  let mut (p, s, o, v) := (p, s, o, v)
  let n ← choose ℕ
  for _ in [:n] do
    let ao ← driveActual A b
    let a ← intersectionControl A b Vmin ε p s o v
    let (res, _t) ← evolve (intersectionMotion a ao, time) (intersectionDomain ε Vmin)
      ((p, s, o, v), 0)
    (p, s, o, v) := res
  return (p, s, o, v)

end

end IJRR17
