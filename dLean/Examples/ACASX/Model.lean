import dLean.Core.ODE

open dLean

namespace ACASX

@[reducible]
def Sense (w : ℝ) : Prop := w = -1 ∨ w = 1

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

@[reducible]
def NoNMAC (rp hp r h : ℝ) : Prop := rp < |r| ∨ hp < |h|

@[reducible]
def maxI (v w target : ℝ) : ℝ := max 0 (w * (target - v))

/-- Fig. 3 : A -/
@[reducible]
def A (alo t hn v w vlo : ℝ) : Prop :=
  (0 ≤ t ∧ t < maxI v w vlo / alo ∧ hn = w * alo / 2 * t ^ 2 + v * t) ∨
  (maxI v w vlo / alo ≤ t ∧ hn = vlo * t - w * maxI v w vlo ^ 2 / (2 * alo))

/-- Fig. 8 : A_up -/
@[reducible]
def Aup (aup t hn v w vup : ℝ) : Prop :=
  (0 ≤ t ∧ t < maxI v w vup / aup ∧ hn = w * aup / 2 * t ^ 2 + v * t) ∨
  (maxI v w vup / aup ≤ t ∧
    hn = w * max (w * vup) (w * v) * t - w * maxI v w vup ^ 2 / (2 * aup))

/-- Fig. 3 : L⁻¹_impl -/
@[reducible]
def Limpl (rp hp rv alo r h v w vlo : ℝ) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ A alo t hn v w vlo →
    rp < |r - rn| ∨ w * (h - hn) < -hp

/-- Fig. 8 : U⁻¹_impl -/
@[reducible]
def Uimpl (rp hp rv aup r h v w vup : ℝ) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ Aup aup t hn v w vup →
    rp < |r - rn| ∨ hp < w * (h - hn)

/-- Fig. 8 : C⁻¹_impl -/
@[reducible]
def Cimpl (rp hp rv alo aup r h v w vlo vup : ℝ) : Prop :=
  Limpl rp hp rv alo r h v w vlo ∨ Uimpl rp hp rv aup r h v w vup

/-- Fig. 3 : L⁻¹_expl -/
@[reducible]
def Lexpl (rp hp rv alo r h v w vlo : ℝ) : Prop :=
  let m := min 0 (w * v)
  let M := maxI v w vlo
  (0 ≤ w * vlo →
    -- case1 -> bound1
    ((-rp ≤ r ∧ r < -rp - rv * m / alo) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    -- case2 -> bound2
    ((-rp - rv * m / alo ≤ r ∧ r ≤ rp - rv * m / alo) →
      w * h < -(m ^ 2) / (2 * alo) - hp) ∧
    -- case3 -> bound3
    ((rp - rv * m / alo < r ∧ r ≤ rp + rv * M / alo) →
      w * rv ^ 2 * h < alo / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
    -- case4 -> bound4
    (rp + rv * M / alo < r →
      rv = 0 ∨ w * rv * h < w * vlo * (r - rp) - rv * M ^ 2 / (2 * alo) - rv * hp)
  ) ∧
  (w * vlo < 0 →
    -- case5 -> bound5
    ((-rp ≤ r ∧ r < -rp + rv * M / alo) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    -- case6 -> bound6
    (-rp + rv * M / alo ≤ r →
      (rv = 0 ∧ rp < r) ∨
        w * rv * h < w * vlo * (r + rp) - rv * M ^ 2 / (2 * alo) - rv * hp)
  )

/-- Fig. 8 : U⁻¹_expl -/
@[reducible]
def Uexpl (rp hp rv aup r h v w vup : ℝ) : Prop :=
  let M := maxI v w vup
  let V := max (w * vup) (w * v)
  (0 < V →
    -- case10 -> bound10
    ((-rp ≤ r ∧ r ≤ rp) → hp < w * h) ∧
    -- case11 -> bound11
    ((rp < r ∧ r ≤ rp + rv * M / aup) →
      aup / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case12 -> bound12
    ((-rp ≤ r ∧ r < -rp + rv * M / aup) →
      aup / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case13 -> bound13
    (-rp + rv * M / aup ≤ r →
      (rv = 0 ∧ rp < r) ∨ V * (r + rp) - rv * M ^ 2 / (2 * aup) + rv * hp < w * rv * h)
  ) ∧
  (V ≤ 0 →
    -- case10 -> bound10
    ((-rp ≤ r ∧ r ≤ rp) → hp < w * h) ∧
    -- case11 -> bound11
    ((rp < r ∧ r ≤ rp + rv * M / aup) →
      aup / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case14 -> bound14
    (rp + rv * M / aup < r →
      rv = 0 ∨ V * (r - rp) - rv * M ^ 2 / (2 * aup) + rv * hp < w * rv * h)
  )

/-- Fig. 8 : C⁻¹_expl -/
@[reducible]
def Cexpl (rp hp rv alo aup r h v w vlo vup : ℝ) : Prop :=
  Lexpl rp hp rv alo r h v w vlo ∨ Uexpl rp hp rv aup r h v w vup

/-- Fig. 5 : Dᵈ_impl, follows `safe_delay_implicit.kyx`.
the paper (fixed version: `vd` instead of `v` inside `A`) -/
@[reducible]
def Dimpl (rp hp rv alo ad r h v w vlo d : ℝ) : Prop :=
  ∀ t rn hn hd vd : ℝ,
    rn = rv * t ∧
      ((0 ≤ t ∧ t < max 0 d ∧ hn = -(w * ad) / 2 * t ^ 2 + v * t) ∨
        ((hd = -(w * ad) / 2 * (max 0 d) ^ 2 + v * max 0 d ∧ vd - v = -w * ad * max 0 d) ∧
          A alo (t - max 0 d) (hn - hd) vd w vlo)
      ) →
      rp < |r - rn| ∨ w * (h - hn) < -hp

/-- Fig. 5 : Dᵈ_expl -/
@[reducible]
def Dexpl (rp hp rv alo ad r h v w vlo d : ℝ) : Prop :=
  let rd := rv * max 0 d
  let vd := v - w * ad * max 0 d
  let hd := -(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d
  -- case7 -> bound7
  ((-rp ≤ r ∧ r ≤ rp) → w * h < -hp) ∧
  -- case8 -> bound8
  ((rp < r ∧ r ≤ rd + rp) →
    w * rv ^ 2 * h < -ad / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
  -- case9 -> bound9
  ((-rp ≤ r ∧ r < rd - rp) →
    w * rv ^ 2 * h < -ad / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
  Lexpl rp hp rv alo (r - rd) (h - hd) vd w vlo

/-- Fig. 10 : Lε_impl (equivalent to paper for `t=0`), follows `bounded_implicit.kyx`
(fixed typo from paper: `hp` to `-hp`) -/
@[reducible]
def LimplBounded (rp hp rv alo tl t r h v w vlo : ℝ) : Prop :=
  ∀ tn rn hn : ℝ, (tn ≤ tl - t ∨ tl < 0) ∧ rn = rv * tn ∧ A alo tn hn v w vlo →
    rp < |r - rn| ∨ w * (h - hn) < -hp

/-- Fig. 10 : Uε_impl (equivalent to paper for `t=0`) -/
@[reducible]
def UimplBounded (rp hp rv aup tl t r h v w vup : ℝ) : Prop :=
  ∀ tn rn hn : ℝ, (tn ≤ tl - t ∨ tl < 0) ∧ rn = rv * tn ∧ Aup aup tn hn v w vup →
    rp < |r - rn| ∨ hp < w * (h - hn)

/-- Fig. 10 : Cε_impl (equivalent to paper for `t=0`) -/
@[reducible]
def CimplBounded (rp hp rv alo aup tl t r h v w vlo vup : ℝ) : Prop :=
  LimplBounded rp hp rv alo tl t r h v w vlo ∨
    UimplBounded rp hp rv aup tl t r h v w vup

/-- Fig. 12 : lower endpoint, follows `condImplSafeableLo` in `AcasXSafeable.scala`
(fixed typo from paper: `vlo * τ` to `v * τ` in the first disjunct). -/
@[reducible]
def lowerEndpoint (alo τ hn vn v w vlo : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vlo / alo ∧
    hn = w * alo / 2 * τ ^ 2 + v * τ ∧ vn = w * alo * τ + v) ∨
  (maxI v w vlo / alo ≤ τ ∧
    hn = vlo * τ - w * maxI v w vlo ^ 2 / (2 * alo) ∧ vn = vlo)

/-- Fig. 12 : upper endpoint, follows `condImplSafeableUp` in `AcasXSafeable.scala`
(fixed typo from paper: `vup * τ` to `v * τ` in the first disjunct). -/
@[reducible]
def upperEndpoint (aup τ hn vn v w vup : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vup / aup ∧
    hn = w * aup / 2 * τ ^ 2 + v * τ ∧ vn = w * aup * τ + v) ∨
  (maxI v w vup / aup ≤ τ ∧
    hn = w * max (w * vup) (w * v) * τ - w * maxI v w vup ^ 2 / (2 * aup) ∧
    vn = w * max (w * vup) (w * v))

/-- Fig. 12 : Csafeable(ε)_impl (equivalent to paper for `t=0`) -/
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
def advisoryUp (aup v w vup a : ℝ) : Prop := (w * v ≤ w * vup ∧ w * a ≤ aup) ∨ w * a ≤ 0

/-- From Eq. (1) -/
def motion (rv a : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun (_r, _h, v) => (-rv, -v, a)

/-- From Eq. (1) -/
def lowerDomain (alo w vlo a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a

/-- From Eq. (5) -/
def twoSidedDomain (alo aup w vlo vup a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

def sense : SetM ℝ := chooseS {-1, 1}

/-- From Theorem 1, and `acasx.kyx`. -/
def immediate (rp hp rv alo r h v w vlo : ℝ) := do
  let mut (r, h, v, w, vlo) := (r, h, v, w, vlo)
  let n ← choose ℕ
  for _ in [:n] do
    let bool ← choose Bool
    if bool then
      w ← sense
      vlo ← choose ℝ
      ensure (Limpl rp hp rv alo r h v w vlo)
      -- advisory := (w, vlo)
    let a ← choose ℝ
    (r, h, v) ← evolve (motion rv a) (lowerDomain alo w vlo a) (r, h, v)
  return (r, h, v, w, vlo)

/-- From Eq. (4) -/
def delayedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _d, _t) => (-rv, -v, a, -1, 1)

/-- From Eq. (4) -/
def delayedDomain (alo ε w vlo a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, d, t) => t ≤ ε ∧ (d ≤ 0 → advisoryLo alo v w vlo a)

/-- From Theorem 2, and `safe_delay_implicit.kyx`.
Choosing d `δ` is the `advisory := (w, vlo)` case, `δ + ε` is the `advisory := COC` case.
Advisory labels have no operational use. -/
def delayed (rp hp rv alo ad δ ε r h v w vlo d : ℝ) := do
  let mut (r, h, v, w, vlo, d) := (r, h, v, w, vlo, d)
  let n ← choose ℕ
  for _ in [:n] do
    let bool ← choose Bool
    if bool then
      vlo ← choose ℝ
      w ← sense
      d ← chooseS {δ, (δ + ε)}
      ensure (Dimpl rp hp rv alo ad r h v w vlo d)
    let a ← choose ℝ
    unless (-ad ≤ w * a) do abort
    (r, h, v, d, _) ←
      evolve (delayedMotion rv a) (delayedDomain alo ε w vlo a) (r, h, v, d, 0)
  return (r, h, v, w, vlo, d)

/-- From Theorem 3, and `acasxtwosided.kyx`. -/
def twoSided (rp hp rv alo aup r h v w vlo vup : ℝ) := do
  let mut (r, h, v, w, vlo, vup) := (r, h, v, w, vlo, vup)
  let n ← choose ℕ
  for _ in [:n] do
    let bool ← choose Bool
    if bool then
      w ← sense
      vlo ← choose ℝ
      vup ← choose ℝ
      ensure (Cimpl rp hp rv alo aup r h v w vlo vup)
      -- advisory := (w, vlo, vup)
    let a ← choose ℝ
    (r, h, v) ← evolve (motion rv a) (twoSidedDomain alo aup w vlo vup a) (r, h, v)
  return (r, h, v, w, vlo, vup)

/-- From Eq. (8) -/
def clockedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _t) => (-rv, -v, a, 1)

/-- From Eq. (8) -/
def clockedDomain (alo aup tl w vlo vup a : ℝ) : ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, t) => (t ≤ tl ∨ tl < 0) ∧
    advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

/-- Common program from Eqs. (8)/(9) (equivalent to paper when initially `t=0`) -/
def clocked (rv alo aup tl : ℝ) (safe : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (r h v w vlo vup t : ℝ) := do
  let mut (r, h, v, w, vlo, vup, t) := (r, h, v, w, vlo, vup, t)
  let n ← choose ℕ
  for _ in [:n] do
    vlo ← choose ℝ
    vup ← choose ℝ
    w ← sense
    ensure (safe r h v w vlo vup 0)
    -- advisory := (w, vlo, vup)
    t := 0
    let m ← choose Nat
    for _ in [:m] do
      let a ← choose ℝ
      (r, h, v, t) ← evolve (clockedMotion rv a)
        (clockedDomain alo aup tl w vlo vup a) (r, h, v, t)
  return (r, h, v, w, vlo, vup, t)

/-- From Theorem 4 -/
def bounded (rp hp rv alo aup tl r h v w vlo vup t : ℝ) :=
  clocked rv alo aup tl
    (fun r h v w vlo vup t => CimplBounded rp hp rv alo aup tl t r h v w vlo vup)
    r h v w vlo vup t

/-- From Theorem 5 -/
def safeable (rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t : ℝ) :=
  clocked rv alo aup tl
    (fun r h v w vlo vup t =>
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx)
    r h v w vlo vup t

/-- From Eq. (11) -/
def horizontalMotion (rx ry rv : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_x, _y, _s, _n) => (rx, ry, -rv, 0)

/-- From Eq. (11) -/
@[reducible]
def HorizontalCoordinates (rx ry rv x y s n : ℝ) : Prop :=
  x * rx + y * ry = -s * rv ∧ x * ry - y * rx = n * rv ∧
    x ^ 2 + y ^ 2 = n ^ 2 + s ^ 2 ∧ rv ^ 2 = rx ^ 2 + ry ^ 2


end ACASX
