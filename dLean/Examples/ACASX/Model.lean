import dLean.Core.ODE

/-!
# ACAS X: STTT 2017

Shared, unannotated models for the five main safety theorems of Jeannin et al.,
*A Formally Verified Hybrid System for Safe Advisories in the Next-Generation
Airborne Collision Avoidance System*, STTT 19(6), 717--741 (2017).

The pinned repository `acasx.kyx` and `acasxtwosided.kyx` take precedence for
Theorem 1, Lemma 1, and Theorem 3. The journal's KeYmaera X 4.3 supplement supplies
Theorems 2, 4, and 5. Sources and differences are recorded in
`keymaera/ACASX/README.md`. In particular, the selected two-sided model reassigns
both targets, and the bounded/safeable models retain a persistent clock.

`r` is signed horizontal separation, `h` relative altitude, `v` relative vertical
velocity (ownship minus the constant intruder velocity), and `rv` nonnegative
horizontal closing speed. `w = ±1` gives advisory sense; `vlo` and `vup` are
vertical targets. All accelerations and targets are symbolic real parameters.
An acceleration choice is constant during one continuous phase. All loops allow
any finite number of iterations, including zero. Every evolution permits any
stopping time in its domain; there are no trailing collision-exclusion tests.

The model is independent of the admitted challenge statements. The scope is the
five main safety claims, horizontal reduction, and the immediate/delayed
one-sided region equivalences. This is a transcription, not a proved equivalence
between dLean semantics and the original dL programs.
-/

open dLean

namespace ACASX

noncomputable section

@[reducible]
def Sense (w : ℝ) : Prop := w = -1 ∨ w = 1

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

/-- The journal supplement only assumes positive upper acceleration for Theorems 3/4. -/
@[reducible]
def TwoSidedBounds (rp hp rv alo aup : ℝ) : Prop := Bounds rp hp rv alo ∧ 0 < aup

@[reducible]
def NoNMAC (rp hp r h : ℝ) : Prop := rp < |r| ∨ hp < |h|

def maxI (v w target : ℝ) : ℝ := max 0 (w * (target - v))

/-- Fig. 3 / `acasx.kyx`: graph of the lower nominal trajectory. -/
@[reducible]
def A (alo t hn v w vlo : ℝ) : Prop :=
  (0 ≤ t ∧ t < maxI v w vlo / alo ∧ hn = w * alo / 2 * t ^ 2 + v * t) ∨
  (maxI v w vlo / alo ≤ t ∧ hn = vlo * t - w * maxI v w vlo ^ 2 / (2 * alo))

/-- Fig. 8 / `acasxtwosided.kyx`: overcompliance changes the final slope.
For `Sense w`, its `w * max (w*vup) (w*v)` equals the supplement's `v + w*maxI`. -/
@[reducible]
def Aup (aup t hn v w vup : ℝ) : Prop :=
  (0 ≤ t ∧ t < maxI v w vup / aup ∧ hn = w * aup / 2 * t ^ 2 + v * t) ∨
  (maxI v w vup / aup ≤ t ∧
    hn = w * max (w * vup) (w * v) * t - w * maxI v w vup ^ 2 / (2 * aup))

@[reducible]
def Limpl (rp hp rv alo r h v w vlo : ℝ) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ A alo t hn v w vlo →
    rp < |r - rn| ∨ w * (h - hn) < -hp

@[reducible]
def Uimpl (rp hp rv aup r h v w vup : ℝ) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ Aup aup t hn v w vup →
    rp < |r - rn| ∨ hp < w * (h - hn)

@[reducible]
def Cimpl (rp hp rv alo aup r h v w vlo vup : ℝ) : Prop :=
  Limpl rp hp rv alo r h v w vlo ∨ Uimpl rp hp rv aup r h v w vup

/-- Fig. 3 / Lemma 1 in `acasx.kyx`: the six explicit cases. -/
@[reducible]
def Lexpl (rp hp rv alo r h v w vlo : ℝ) : Prop :=
  let m := min 0 (w * v)
  let M := maxI v w vlo
  (0 ≤ w * vlo →
    ((-rp ≤ r ∧ r < -rp - rv * m / alo) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    ((-rp - rv * m / alo ≤ r ∧ r ≤ rp - rv * m / alo) →
      w * h < -(m ^ 2) / (2 * alo) - hp) ∧
    ((rp - rv * m / alo < r ∧ r ≤ rp + rv * M / alo) →
      w * rv ^ 2 * h < alo / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
    (rp + rv * M / alo < r →
      rv = 0 ∨ w * rv * h < w * vlo * (r - rp) - rv * M ^ 2 / (2 * alo) - rv * hp)) ∧
  (w * vlo < 0 →
    ((-rp ≤ r ∧ r < -rp + rv * M / alo) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    (-rp + rv * M / alo ≤ r →
      (rv = 0 ∧ rp < r) ∨
        w * rv * h < w * vlo * (r + rp) - rv * M ^ 2 / (2 * alo) - rv * hp))

/-- Fig. 5 and the bundled `safe_delay_implicit.kyx`: delay followed by resolution.
The resolution starts with `vd`, as in the actual kyx formula (the printed Fig. 5 uses `v`). -/
@[reducible]
def Dimpl (rp hp rv alo ad r h v w vlo d : ℝ) : Prop :=
  ∀ t rn hn hd vd : ℝ,
    rn = rv * t ∧
      ((0 ≤ t ∧ t < max 0 d ∧ hn = -(w * ad) / 2 * t ^ 2 + v * t) ∨
        ((hd = -(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d ∧
          vd - v = -w * ad * max 0 d) ∧
          A alo (t - max 0 d) (hn - hd) vd w vlo)) →
      rp < |r - rn| ∨ w * (h - hn) < -hp

/-- Journal Fig. 5; no standalone delayed-explicit kyx was found in the supplement. -/
@[reducible]
def Dexpl (rp hp rv alo ad r h v w vlo d : ℝ) : Prop :=
  let rd := rv * max 0 d
  let vd := v - w * ad * max 0 d
  let hd := -(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d
  ((-rp ≤ r ∧ r ≤ rp) → w * h < -hp) ∧
  ((rp < r ∧ r ≤ rd + rp) →
    w * rv ^ 2 * h < -ad / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
  ((-rp ≤ r ∧ r < rd - rp) →
    w * rv ^ 2 * h < -ad / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
  Lexpl rp hp rv alo (r - rd) (h - hd) vd w vlo

/-- `tl` is the horizon, `t` time since issue; a negative horizon means unbounded time. -/
@[reducible]
def LimplBounded (rp hp rv alo tl t r h v w vlo : ℝ) : Prop :=
  ∀ tn rn hn : ℝ, (tn ≤ tl - t ∨ tl < 0) ∧ rn = rv * tn ∧ A alo tn hn v w vlo →
    rp < |r - rn| ∨ w * (h - hn) < -hp

@[reducible]
def UimplBounded (rp hp rv aup tl t r h v w vup : ℝ) : Prop :=
  ∀ tn rn hn : ℝ, (tn ≤ tl - t ∨ tl < 0) ∧ rn = rv * tn ∧ Aup aup tn hn v w vup →
    rp < |r - rn| ∨ hp < w * (h - hn)

@[reducible]
def CimplBounded (rp hp rv alo aup tl t r h v w vlo vup : ℝ) : Prop :=
  LimplBounded rp hp rv alo tl t r h v w vlo ∨
    UimplBounded rp hp rv aup tl t r h v w vup

/-- Nominal lower state at the end of the remaining advisory period. -/
@[reducible]
def lowerEndpoint (alo τ hn vn v w vlo : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vlo / alo ∧
    hn = w * alo / 2 * τ ^ 2 + v * τ ∧ vn = w * alo * τ + v) ∨
  (maxI v w vlo / alo ≤ τ ∧
    hn = vlo * τ - w * maxI v w vlo ^ 2 / (2 * alo) ∧ vn = vlo)

@[reducible]
def upperEndpoint (aup τ hn vn v w vup : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vup / aup ∧
    hn = w * aup / 2 * τ ^ 2 + v * τ ∧ vn = w * aup * τ + v) ∨
  (maxI v w vup / aup ≤ τ ∧
    hn = (v + w * maxI v w vup) * τ - w * maxI v w vup ^ 2 / (2 * aup) ∧
    vn = v + w * maxI v w vup)

/-- Fig. 12, using the generated formulas in `AcasXSafeable.scala`.
Escape targets `vloEx`, `vupEx` are fixed parameters, not reassigned by the controller. -/
@[reducible]
def CimplSafeable (rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx : ℝ) : Prop :=
  (LimplBounded rp hp rv alo tl t r h v w vlo ∧
    ∀ hn vn : ℝ, lowerEndpoint alo (tl - t) hn vn v w vlo →
      Limpl rp hp rv alo (r - rv * (tl - t)) (h - hn) vn w vloEx) ∨
  (UimplBounded rp hp rv aup tl t r h v w vup ∧
    ∀ hn vn : ℝ, upperEndpoint aup (tl - t) hn vn v w vup →
      Limpl rp hp rv alo (r - rv * (tl - t)) (h - hn) vn (-w) vupEx)

@[reducible]
def advisoryLo (alo v w vlo a : ℝ) : Prop := w * vlo ≤ w * v ∨ alo ≤ w * a

@[reducible]
def advisoryUp (aup v w vup a : ℝ) : Prop :=
  (w * v ≤ w * vup ∧ w * a ≤ aup) ∨ w * a ≤ 0

/-- A single acceleration is held fixed for this phase. -/
def motion (rv a : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun (_r, _h, v) => (-rv, -v, a)

def lowerDomain (alo w vlo a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a

def twoSidedDomain (alo aup w vlo vup a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

def sense : SetM ℝ := pure (-1) <|> pure 1

/-- Journal Theorem 1, repository `acasx.kyx`. Returns `(r,h,v,w,vlo)`. -/
def immediate (rp hp rv alo r h v w vlo : ℝ) := do
  let mut (r, h, v, w, vlo) := (r, h, v, w, vlo)
  let n ← choose ℕ
  for _ in [:n] do
    (w, vlo) ← (pure (w, vlo)) <|> (do
      let w ← sense
      let vlo ← choose ℝ
      ensure (Limpl rp hp rv alo r h v w vlo)
      return (w, vlo))
    let a ← choose ℝ
    (r, h, v) ← evolve (motion rv a) (lowerDomain alo w vlo a) (r, h, v)
  return (r, h, v, w, vlo)

def delayedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _d, _t) => (-rv, -v, a, -1, 1)

def delayedDomain (alo ε w vlo a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, d, t) => t ≤ ε ∧ (d ≤ 0 → advisoryLo alo v w vlo a)

/-- Journal Theorem 2 / bundled `safe_delay_implicit.kyx`.
Choosing `δ + ε` represents COC; advisory display labels have no operational use.
Returns `(r,h,v,w,vlo,d)`; only the local system clock is discarded. -/
def delayed (rp hp rv alo ad δ ε r h v w vlo d : ℝ) := do
  let mut (r, h, v, w, vlo, d) := (r, h, v, w, vlo, d)
  let n ← choose ℕ
  for _ in [:n] do
    (w, vlo, d) ← (pure (w, vlo, d)) <|> (do
      let vlo ← choose ℝ
      let w ← sense
      let d ← pure δ <|> pure (δ + ε)
      ensure (Dimpl rp hp rv alo ad r h v w vlo d)
      return (w, vlo, d))
    let a ← choose ℝ
    ensure (-ad ≤ w * a)
    let (r_new, h_new, v_new, d_new, _t) ←
      evolve (delayedMotion rv a) (delayedDomain alo ε w vlo a) (r, h, v, d, 0)
    (r, h, v, d) := (r_new, h_new, v_new, d_new)
  return (r, h, v, w, vlo, d)

/-- Journal Theorem 3, repository `acasxtwosided.kyx`: reassign both targets.
Returns `(r,h,v,w,vlo,vup)`. The older supplement only reassigns `vlo`. -/
def twoSided (rp hp rv alo aup r h v w vlo vup : ℝ) := do
  let mut (r, h, v, w, vlo, vup) := (r, h, v, w, vlo, vup)
  let n ← choose ℕ
  for _ in [:n] do
    (w, vlo, vup) ← (pure (w, vlo, vup)) <|> (do
      let w ← sense
      let vlo ← choose ℝ
      let vup ← choose ℝ
      ensure (Cimpl rp hp rv alo aup r h v w vlo vup)
      return (w, vlo, vup))
    let a ← choose ℝ
    (r, h, v) ← evolve (motion rv a) (twoSidedDomain alo aup w vlo vup a) (r, h, v)
  return (r, h, v, w, vlo, vup)

def clockedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _t) => (-rv, -v, a, 1)

def clockedDomain (alo aup tl w vlo vup a : ℝ) : ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, t) => (t ≤ tl ∨ tl < 0) ∧
    advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

/-- Common *artifact* loop for Theorems 4/5. `safe` is the exact issue guard.
Retaining an advisory also retains its clock. Issuing a new advisory resets it.
Returns `(r,h,v,w,vlo,vup,t)`, including the time since the latest issue. -/
def clocked (rv alo aup tl : ℝ) (safe : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (r h v w vlo vup t : ℝ) := do
  let mut (r, h, v, w, vlo, vup, t) := (r, h, v, w, vlo, vup, t)
  let n ← choose ℕ
  for _ in [:n] do
    (w, vlo, vup, t) ← (pure (w, vlo, vup, t)) <|> (do
      let vlo ← choose ℝ
      let vup ← choose ℝ
      let w ← sense
      ensure (safe r h v w vlo vup 0)
      return (w, vlo, vup, 0))
    let a ← choose ℝ
    (r, h, v, t) ← evolve (clockedMotion rv a)
      (clockedDomain alo aup tl w vlo vup a) (r, h, v, t)
  return (r, h, v, w, vlo, vup, t)

/-- Journal Theorem 4 / `bounded_implicit.kyx`. -/
def bounded (rp hp rv alo aup tl r h v w vlo vup t : ℝ) :=
  clocked rv alo aup tl
    (fun r h v w vlo vup t => CimplBounded rp hp rv alo aup tl t r h v w vlo vup)
    r h v w vlo vup t

/-- Journal Theorem 5 / `AcasXSafeable.scala`, generated `model`.
Escape target parameters remain fixed across reissued advisories. -/
def safeable (rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t : ℝ) :=
  clocked rv alo aup tl
    (fun r h v w vlo vup t =>
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx)
    r h v w vlo vup t

/-- Journal Proposition 1, Eq. (11): both horizontal descriptions evolve together. -/
def horizontalMotion (rx ry rv : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun _ => (rx, ry, -rv, 0)

@[reducible]
def HorizontalCoordinates (rx ry rv x y s n : ℝ) : Prop :=
  x * rx + y * ry = -s * rv ∧ x * ry - y * rx = n * rv ∧
    x ^ 2 + y ^ 2 = n ^ 2 + s ^ 2 ∧ rv ^ 2 = rx ^ 2 + ry ^ 2

end

end ACASX
