import dLean.Core.QODE
open dLean

namespace FM11

abbrev Car := Nat
/- x, v, and a for every car. -/
abbrev St := (Car → ℝ) × (Car → ℝ) × (Car → ℝ)

/-- The relation `f << l` from Section 5.2. -/
@[reducible]
def Behind (b B : ℝ) (x v : Car → ℝ) (f l : Car) : Prop :=
  (x f ≤ x l) ∧
    (f ≠ l →
      (x f < x l ∧ x f + (v f ^ 2) / (2 * b) < x l + (v l ^ 2) / (2 * B) ∧
      v f ≥ 0 ∧ v l ≥ 0))

/-- The car `l = L(i)` is the leader of i.
Represented as a relation rather than a function.
Added `i ∈ C ∧ l ∈ C` which is implicit in the paper.
-/
@[reducible]
def L (C : Finset Car) (x : Car → ℝ) (i : Car) (l : Car) : Prop :=
  i ∈ C ∧ l ∈ C ∧ x i < x l ∧ ∀ k ∈ C,
    (k ≠ i ∧ k ≠ l) → (x k < x i ∨ x l < x k)

/-- The relation `i << L(i)` from Section 5.2.
i is safely behind its leader.
-/
@[reducible]
def BehindL (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) (i : Car) : Prop :=
  ∀ l ∈ C, L C x i l → Behind b B x v i l


/-- Not present in the paper
-/
@[reducible]
def LaneSafe (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) : Prop :=
  (∀ i ∈ C, 0 ≤ v i) ∧
  (∀ i ∈ C, ∀ j ∈ C, i ≠ j → x i ≠ x j) ∧
  (∀ i ∈ C, BehindL C b B x v i)


/-- The relation `i << L*(i)` from Section 6.2.
i is safely behind all l such that l = L^n(i) for some n.
-/
@[reducible]
def BehindLStar (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) (i : Car) : Prop :=
  ∀ k ∈
    (SetM.run do
    let mut k := i
    let n ← choose ℕ
    for _ in [:n] do
      let l ← chooseS {l | L C x k l} -- L(k)
      k := l
    return k),
  Behind b B x v i k

/-- Quantified ODE of car motion -/
@[simp] def motion (C : Finset Car) : Set Car × (St → St) :=
  (C, fun (_x, v, a) => (v, a, 0))

/-- ODE modelling time -/
@[simp] def time : ℝ → ℝ := fun _t => 1

/-- Domain constraint -/
@[simp] def domain (ε : ℝ) (C : Finset Car) : St × ℝ → Prop
  | ((_x, v, _a), t) => (∀ i ∈ C, 0 ≤ v i) ∧ t ≤ ε

/-- Evolve cars and a clock starting from 0 simultenaosly -/
def dyn (ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) := do
  let ((x, v, a), _t) ← evolve (motion C, time)
                               (domain ε C)
                               ((x, v, a), 0)
  return (x, v, a)

@[reducible]
def Safe_ε (A b B ε : ℝ) (x v : Car → ℝ) (f l : Car) : Prop :=
  x f + (v f ^ 2) / (2 * b) + (A / b + 1) * (A / 2 * ε ^ 2 + ε * v f) <
    x l + v l ^ 2 / (2 * B)

-------------------- Local lane control, Model 1 ----------------------------

/-- Update a(l) -/
def l_ctrl (A B : ℝ) (l : Car) (a : Car → ℝ) : SetM (Car → ℝ) := do
  let al ← choose ℝ
  unless (-B ≤ al ∧ al ≤ A) do abort
  return Function.update a l al

/-- Update a(f) -/
def f_ctrl (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM (Car → ℝ) :=
  (do
    let af ← choose ℝ
    unless (-B ≤ af ∧ af ≤ -b) do abort
    return Function.update a f af)
    <|>
  (do
    unless Safe_ε A b B ε x v f l do abort
    let af ← choose ℝ
    unless (-B ≤ af ∧ af ≤ A) do abort
    return Function.update a f af)
    <|>
  (do
    unless v f = 0 do abort
    return Function.update a f 0)

/-- Local lane control with 2 cars: f (follower) and l (leader) -/
def llc (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    a ← l_ctrl A B l a
    a ← f_ctrl A b B ε f l x v a
    (x, v, a) ← dyn ε {f, l} x v a
  return (x, v)

theorem llc_safe :
    ∀ A b B ε f l x v a,
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → Behind b B x v f l →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          let (x_res, v_res) := res
          Behind b B x_res v_res f l := sorry

-------------------- Global lane control, Model 2 ----------------------------

/-- Generalized f_ctrl: in the 2nd option Safe_ε should hold for L(i)
This is not equivalent to:
`let l ← chooseS {l | L C x i l} ; f_ctrl`
because that would force to select a leader for all cars and fail otherwise.
But the frontmost car cannot have a leader. That car has to choose 1st or 3rd
option.
-/
def ctrl_i (A b B ε : ℝ) (C : Finset Car) (i : Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) :=
  (do
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ -b) do abort
    return Function.update a i ai)
    <|>
  (do
    let l ← chooseS {l | L C x i l} -- leader of i
    unless Safe_ε A b B ε x v i l do abort
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ A) do abort
    return Function.update a i ai)
    <|>
  (do
    unless v i = 0 do abort
    return Function.update a i 0)

/-- Run the controller for all cars at the same time, i.e.
they all have the same initial state. Each ctrl_i can only
update a(i), so a sequantial update via a for loop is OK.
-/
def ctrl_n (A b B ε : ℝ) (C : Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) := do
  let mut a_res := a
  for i in C.toList do
    let ai ← ctrl_i A b B ε C i x v a
    a_res := Function.update a_res i (ai i)
  return a_res

-- def ctrl_n (A b B ε : ℝ) (C : Finset Car)
--     (x v a : Car → ℝ) : SetM (Car → ℝ) := do
--   chooseS {a' | (∀ i ∈ C, Function.update a i (a' i) ∈
--                   SetM.run (ctrl_i A b B ε C i x v a)) ∧
--                   ∀ i, i ∉ C → a' i = a i}

/-- Global lane control, fixed number of cars -/
def glc (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    a ← ctrl_n A b B ε C x v a
    (x, v, a) ← dyn ε C x v a
  return (x, v)

theorem glc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (glc A b B ε C x v a),
        let (x_res, v_res) := res
        LaneSafe C b B x_res v_res ∧
        (∀ i ∈ C, BehindLStar C b B x_res v_res i) := sorry

-------------------- Local highway control, Model 3 --------------------------

/-- The relation `F(n) << n` from Section 6.2.
n is safely ahead of its follower.
-/
@[reducible]
def FBehind (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) (n : Car) : Prop :=
  ∀ j ∈ C, L C x j n → Behind b B x v j n

def new (C : Finset Car) : SetM (Car × Finset Car) := do
  let n ← chooseS {n | n ∉ C}
  return (n, insert n C)

def delete (C : Finset Car) : SetM (Finset Car) := do
  let n ← chooseS {n | n ∈ C}
  return C.erase n

def create (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) := do
  let (n, C_new) ← new C
  unless (0 ≤ v n ∧ ∀ j ∈ C, x n ≠ x j) do abort -- not present in paper
  unless (FBehind C_new b B x v n) do abort -- F(n) << n
  unless (BehindL C_new b B x v n) do abort -- n << L(n)
  return C_new

/-- Local highway control, dynamic number of cars -/
def lhc (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) := do
  let mut (x, v, a) := (x, v, a)
  let mut C := C
  let i ← choose ℕ
  for _ in [:i] do -- for i many iterations
    let j ← choose ℕ
    for _ in [:j] do -- delete j many cars
      C ← delete C
    let j' ← choose ℕ
    for _ in [:j'] do -- create j' many cars
      C ← create C b B x v
    a ← ctrl_n A b B ε C x v a
    (x, v, a) ← dyn ε C x v a
  return (C, x, v)

theorem lhc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε C x v a),
        let (C_res, x_res, v_res) := res
        LaneSafe C_res b B x_res v_res ∧
        (∀ i ∈ C_res, BehindLStar C_res b B x_res v_res i) := sorry

-------------------- Global highway control, Model 4 -------------------------
-- GHC is not explicitly modelled in the paper unlike the previous ones.

/-- We will represent current situation of cars by `Lane → Finset Car` -/
abbrev Lane := Nat

/-- ∀l : L delete_l∗ -/
def delete_l (lanes : Finset Lane) (C : Lane → Finset Car) :
    SetM (Lane → Finset Car) := do
  let mut C := C
  for l in lanes.toList do
    let j ← choose ℕ
    for _ in [:j] do -- delete j many cars from lane l
      let cars ← delete (C l)
      C := Function.update C l cars
  return C

/-- ∀l : L new_l∗ -/
def create_l (lanes : Finset Lane) (C : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car) := do
  let mut C := C
  for l in lanes.toList do
    let j ← choose ℕ
    for _ in [:j] do -- delete j many cars in lane l
      let cars ← create (C l) b B x v
      C := Function.update C l cars
  return C

/-- ∀l : L ctrl_n_l
Global control. A car occupying multiple lanes must choose one acceleration
allowed by each of its lane controllers, all reading the same initial state.
-/
def ctrl_n_l (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) := do
  let mut a_res := a
  for i in (lanes.biUnion C).toList do -- set of all cars
    let ai ← choose ℝ -- we select the a(i) early in case i is on multiple lanes
    for l in lanes.toList do
      if i ∈ C l then -- lanes containing the car i
        let a_new := Function.update a i ai
        -- assert that ai conforms with lane i
        ensure (a_new ∈ SetM.run (ctrl_i A b B ε (C l) i x v a))
    a_res := Function.update a_res i ai
  return a_res

/-- Global highway control, dynamic number of cars, multiple lanes -/
def ghc (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) := do
  let mut (x, v, a) := (x, v, a)
  let mut C := C
  let n ← choose ℕ
  for _ in [:n] do
    C ← delete_l lanes C
    C ← create_l lanes C b B x v
    a ← ctrl_n_l A b B ε lanes C x v a
    (x, v, a) ← dyn ε (lanes.biUnion C) x v a
  return (C, x, v)

theorem ghc_safe :
    ∀ A b B ε x v a (lanes : Finset Lane) (C : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (C l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes C x v a),
          let (C_res, x_res, v_res) := res
          ∀ l ∈ lanes, LaneSafe (C_res l) b B x_res v_res ∧
          (∀ i ∈ C_res l, BehindLStar (C_res l) b B x_res v_res i) := sorry

end FM11
