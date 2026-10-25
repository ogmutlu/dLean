import dLean.Examples.FM09.Challenge
import dLean.Tactic.OdeDeriv

/-!
# FM09 throughout safety

Proofs for `Challenge.lean`, following the phase verification plan AC1–AC7.
The AC1 phase contracts also yield the complete NTRM safety theorem.
-/

open dLean
open Std.WP
open scoped RealInnerProductSpace
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace FM09.Proofs

@[simp] theorem perp_sub (u v : Vec2) : perp (u - v) = perp u - perp v := by
  ext i
  fin_cases i
  · simp [perp, PiLp.toLp_apply]
    ring
  · simp [perp, PiLp.toLp_apply]

theorem inner_perp_self (v : Vec2) : ⟪v, perp v⟫ = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, perp]
  ring

theorem evolve_prefix_closed {α σ : Type} [Evolvable α σ]
    (ode : α) (domain : σ → Prop) (st : σ) (T : ℝ) (trajectory : ℝ → σ)
    (_hT : 0 ≤ T) (hevol : IsEvolution trajectory (Evolvable.denotation ode) domain st T) :
    ∀ t ∈ Set.Icc 0 T, trajectory t ∈ SetM.run (evolve ode domain st) := by
  intro t ht
  apply SemanticODE.mem_evolveSemantic _ domain st t trajectory ht.1
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
  exact ⟨hevol.1, fun τ hτ => hevol.2.1 τ (hsub hτ),
    Evolvable.rest_closed ode trajectory hsub hevol.2.2⟩

noncomputable def speedGap (s : ℝ) : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (_, d, _, _) =>
  ‖d‖ ^ 2 - s ^ 2

noncomputable def otherSpeedGap (s : ℝ) : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (_, _, _, e) =>
  ‖e‖ ^ 2 - s ^ 2

theorem speedGap_hasPrime (s ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ρ)) domain (speedGap s) (fun _ => 0) := by
  ode_deriv [speedGap, flight, F, G, perp]

theorem otherSpeedGap_hasPrime (s ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ρ)) domain (otherSpeedGap s) (fun _ => 0) := by
  ode_deriv [otherSpeedGap, flight, F, G, perp]

theorem AC2 :
    ∀ (ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      ∀ res ∈ SetM.run (evolve (flight ω ρ) domain (x, d, y, e)),
        let (_, d', _, e') := res
        ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := by
  intro ω ρ domain x d y e ⟨xr, dr, yr, er⟩ hrun
  have hd := dIeq (ode := flight ω ρ) (domain := domain)
    (pre := fun st => speedGap ‖d‖ st = 0)
    (speedGap ‖d‖) (fun _ => 0) (speedGap_hasPrime ‖d‖ ω ρ domain)
    (fun _ h => h) (fun _ _ => rfl) (x, d, y, e) (by simp [speedGap])
    (xr, dr, yr, er) hrun
  have he := dIeq (ode := flight ω ρ) (domain := domain)
    (pre := fun st => otherSpeedGap ‖e‖ st = 0)
    (otherSpeedGap ‖e‖) (fun _ => 0) (otherSpeedGap_hasPrime ‖e‖ ω ρ domain)
    (fun _ h => h) (fun _ _ => rfl) (x, d, y, e) (by simp [otherSpeedGap])
    (xr, dr, yr, er) hrun
  exact ⟨(sq_eq_sq₀ (norm_nonneg dr) (norm_nonneg d)).mp (sub_eq_zero.mp hd),
    (sq_eq_sq₀ (norm_nonneg er) (norm_nonneg e)).mp (sub_eq_zero.mp he)⟩

noncomputable def roundaboutEnergy (ω : ℝ) (c : Vec2) := fun (x, d, y, e) =>
  ‖d - ω • perp (x - c)‖ ^ 2 + ‖e - ω • perp (y - c)‖ ^ 2

theorem roundaboutEnergy_zero_iff (ω : ℝ) (c : Vec2) (st : Vec2 × Vec2 × Vec2 × Vec2) :
    roundaboutEnergy ω c st = 0 ↔ (let (x, d, y, e) := st; R ω c x d y e) := by
  rcases st with ⟨x, d, y, e⟩
  rw [roundaboutEnergy, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp [R, sub_eq_zero]

theorem roundaboutEnergy_hasPrime (ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ω)) domain
      (roundaboutEnergy ω c) (fun _ => 0) := by
  ode_deriv [roundaboutEnergy, flight, F, G, perp]

theorem R_preserved (ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    (fun (x, d, y, e) => R ω c x d y e)
      [[evolve (flight ω ω) domain]] (fun (x, d, y, e) => R ω c x d y e) := by
  intro initial hpre final hrun
  apply (roundaboutEnergy_zero_iff ω c final).mp
  exact dIeq (ode := flight ω ω) (domain := domain)
    (pre := fun st => roundaboutEnergy ω c st = 0)
    (roundaboutEnergy ω c) (fun _ => 0) (roundaboutEnergy_hasPrime ω c domain)
    (fun _ h => h) (fun _ _ => rfl)
    initial ((roundaboutEnergy_zero_iff ω c initial).mpr hpre) final hrun

noncomputable def separationGap (p : ℝ) : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (x, _, y, _) =>
  ‖x - y‖ ^ 2 - p ^ 2

theorem separationGap_hasPrime (p ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ω))
      (fun (x, d, y, e) => domain (x, d, y, e) ∧ R ω c x d y e) (separationGap p) (fun _ => 0) := by
  ode_deriv [separationGap, R, flight, F, G, perp]

theorem AC1_circ :
    ∀ (p ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ res ∈ SetM.run (evolve (flight ω ω) domain (x, d, y, e)),
          let (x', d', y', e') := res
          R ω c x' d' y' e' ∧ Separated p x' y' := by
  intro p ω c domain x d y e hpre ⟨xr, dr, yr, er⟩ hrun
  apply And.intro (R_preserved ω c domain (x, d, y, e) hpre.1 _ hrun)
  have hsafe :
      (fun (x, d, y, e) => R ω c x d y e ∧ Separated p x y)
      [[evolve (flight ω ω) domain]] (fun st => 0 ≤ separationGap p st) := by
    apply dC (cut := fun (x, d, y, e) => R ω c x d y e)
    · intro initial h
      exact R_preserved ω c domain initial h.1
    · apply dIge (separationGap p) (fun _ => 0)
      · exact separationGap_hasPrime p ω c domain
      · rintro ⟨x, d, y, e⟩ h
        exact sub_nonneg.mpr h.2
      · exact fun _ _ => le_rfl
  exact sub_nonneg.mp (hsafe (x, d, y, e) hpre (xr, dr, yr, er) hrun)

def freeStep (p ω ρ : ℝ) (x d y e : Vec2) :=
  evolve (flight ω ρ) (fun (x, _, y, _) => Separated p x y) (x, d, y, e)

@[spec] theorem freeStep_spec (p ω ρ : ℝ) (x d y e : Vec2) :
    ⦃Separated p x y⦄ freeStep p ω ρ x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  intro hpre
  apply SetM.wp_and
  · exact dW (ode := flight ω ρ)
      (pre := fun (x, (_ : Vec2), y, (_ : Vec2)) => Separated p x y)
      (fun _ hdom => hdom) (x, d, y, e) hpre
  · exact AC2 ω ρ _ x d y e

def free' (p : ℝ) (x d₀ y e₀ : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires Separated p x y
    ensures (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d₀‖ ∧ ‖er‖ = ‖e₀‖
    := do
  let mut (x, d, y, e) := (x, d₀, y, e₀)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => Separated p x y ∧ ‖d‖ = ‖d₀‖ ∧ ‖e‖ = ‖e₀‖ do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← freeStep p ω ρ x d y e
  return (x, d, y, e)

theorem AC1_free :
    ∀ (p r : ℝ) (x d y e : Vec2), Separated (far p r) x y →
      ∀ res ∈ SetM.run (free_f p r x d y e),
        let (x', d', y', e') := res
        Separated (far p r) x' y' ∧ ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := by
  intro p r x d y e hpre res hrun
  exact (free'.spec (far p r) x d y e).le_wp hpre res hrun

/-- The unrestricted circular phase of the NTRM controller. -/
def circStep (_p ω : ℝ) (_c x d y e : Vec2) :=
  evolve (flight ω ω) (fun _ => True) (x, d, y, e)

@[spec] theorem circStep_spec (p ω : ℝ) (c x d y e : Vec2) :
    ⦃R ω c x d y e ∧ Separated p x y⦄ circStep p ω c x d y e
    ⦃fun (xr, _, yr, _) => Separated p xr yr⦄ := by
  constructor
  intro hpre res hrun
  exact (AC1_circ p ω c _ x d y e hpre res hrun).2

@[spec] theorem agree_spec : ⦃True⦄ agree ⦃fun _ => True⦄ := by
  constructor
  intro _ _ _
  trivial

/-- Figure 5: compose the AC1 phase contracts with instantaneous entry. -/
def ntrm' (p : ℝ) (x d y e : Vec2) : SetM (Vec2 × Vec2)
    requires Separated p x y
    ensures (xr, yr) => Separated p xr yr
    := do
  let mut (x, d, y, e) := (x, d, y, e)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => Separated p x y do
    (x, d, y, e) ← free' p x d y e
    let (ω, c) ← agree
    (d, e) := entry_n ω c x y
    (x, d, y, e) ← circStep p ω c x d y e
  return (x, y)
where finally
  | spec => all_goals simp_all [entry_n]

theorem ntrm_safe :
    ∀ (p : ℝ) (x d y e : Vec2), Separated p x y →
      ∀ res ∈ SetM.run (ntrm p x d y e),
        let (xr, yr) := res
        Separated p xr yr := by
  intro p x d y e hpre res hrun
  exact (ntrm'.spec p x d y e).le_wp hpre res hrun

def agree_f' (p : ℝ) (x d y e : Vec2) : SetM (ℝ × Vec2 × ℝ)
    requires True
    ensures (ω, c, r) => 0 ≤ r ∧ C r x d y e c ∧ Separated (far p r) x y ∧
      (r * ω) ^ 2 = ‖d‖ ^ 2
    := do
  let c ← choose Vec2
  let r ← chooseS {r : ℝ | r ≥ 0}
  ensure (C r x d y e c)
  unless Separated (far p r) x y do abort
  let ω ← choose ℝ
  unless (r * ω) ^ 2 = ‖d‖ ^ 2 do abort
  return (ω, c, r)
where finally
  | spec => all_goals grind [SetM.run]

theorem AC6 :
    ∀ (p : ℝ) (x d y e : Vec2),
      ∀ res ∈ SetM.run (agree_f p x d y e),
        let (ω, c, r) := res
        0 ≤ r ∧ C r x d y e c ∧ Separated (far p r) x y ∧
          (r * ω) ^ 2 = ‖d‖ ^ 2 := by
  intro p x d y e res hrun
  exact (agree_f'.spec p x d y e).le_wp trivial res hrun

@[simp] theorem norm_perp (v : Vec2) : ‖perp v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, perp, add_comm]

theorem R_relative (ω : ℝ) (c x d y e : Vec2) (h : R ω c x d y e) :
    d - e = ω • perp (x - y) := by
  calc
    d - e = ω • (perp (x - c) - perp (y - c)) := by rw [h.1, h.2, smul_sub]
    _ = ω • perp (x - y) := by
      rw [← perp_sub]
      congr 2
      abel

noncomputable def exitInner : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (x, d, y, e) => ⟪x - y, d - e⟫

theorem exitInner_hasPrime (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight 0 0)) domain exitInner
      (fun (_, d, _, e) => ‖d - e‖ ^ 2) := by
  ode_deriv [exitInner, flight, F, G]

theorem exitGap_hasPrime (p : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight 0 0)) domain (separationGap p)
      (fun st => 2 * exitInner st) := by
  ode_deriv [exitInner, separationGap, flight, F, G]

theorem AC7 :
    ∀ (p ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ res ∈ SetM.run (exitEvol (x, d, y, e)),
          let (x', _, y', _) := res
          Separated p x' y' := by
  intro p ω c x d y e hpre ⟨xr, dr, yr, er⟩ hrun
  have horth : exitInner (x, d, y, e) = 0 := by
    dsimp [exitInner]
    rw [R_relative ω c x d y e hpre.1, real_inner_smul_right, inner_perp_self, mul_zero]
  have hsafe : (fun st => 0 ≤ exitInner st ∧ 0 ≤ separationGap p st)
      [[evolve (flight 0 0) (fun _ => True)]] (fun st => 0 ≤ separationGap p st) := by
    apply dC (cut := fun st => 0 ≤ exitInner st)
    · apply dIge exitInner (fun (_, d, _, e) => ‖d - e‖ ^ 2)
      · exact exitInner_hasPrime _
      · exact fun _ h => h.1
      · exact fun _ _ => sq_nonneg _
    · apply dIge (separationGap p) (fun st => 2 * exitInner st)
      · exact exitGap_hasPrime p _
      · exact fun _ h => h.2
      · intro st h
        exact mul_nonneg (by norm_num) h.2
  exact sub_nonneg.mp (hsafe (x, d, y, e)
    ⟨horth.ge, sub_nonneg.mpr hpre.2⟩ (xr, dr, yr, er) hrun)

def straightTrajectory (x d y e : Vec2) (t : ℝ) := (x + t • d, d, y + t • e, e)

theorem straightTrajectory_evolution (x d y e : Vec2) (T : ℝ) :
    IsEvolution (straightTrajectory x d y e) (Evolvable.denotation (flight 0 0))
      (fun _ => True) (x, d, y, e) T := by
  apply And.intro (by simp [straightTrajectory])
  apply And.intro (fun _ _ => trivial)
  intro t ht
  simp only [straightTrajectory, flight, F, G, zero_smul]
  change HasDerivWithinAt (fun t => (x + t • d, d, y + t • e, e))
    (d, 0, e, 0) (Set.Icc 0 T) t
  have hx := ((hasDerivAt_id t).smul_const d).const_add x
  have hy := ((hasDerivAt_id t).smul_const e).const_add y
  simpa using (hx.prodMk ((hasDerivAt_const t d).prodMk
    (hy.prodMk (hasDerivAt_const t e)))).hasDerivWithinAt

theorem AC7_live :
    ∀ (ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ d ≠ e →
        ∀ a : ℝ, ∃ res ∈ SetM.run (exitEvol (x, d, y, e)),
          let (x', _, y', _) := res
          a ^ 2 < ‖x' - y'‖ ^ 2 := by
  intro ω c x d y e hpre a
  have hv : 0 < ‖d - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpre.2)
  let T := (|a| + ‖x - y‖ + 1) / ‖d - e‖
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have htime : T * ‖d - e‖ = |a| + ‖x - y‖ + 1 := by
    dsimp [T]
    exact div_mul_cancel₀ _ hv.ne'
  have hdiff : (x + T • d) - (y + T • e) = x - y + T • (d - e) := by
    simp only [smul_sub]
    abel
  have htriangle := norm_sub_le (x - y + T • (d - e)) (x - y)
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT,
    htime] at htriangle
  apply Exists.intro (straightTrajectory x d y e T)
  apply And.intro
  · exact SemanticODE.mem_evolveSemantic _ _ _ T _ hT
      (straightTrajectory_evolution x d y e T)
  · change a ^ 2 < ‖(x + T • d) - (y + T • e)‖ ^ 2
    rw [hdiff]
    nlinarith [sq_abs a, norm_nonneg (x - y + T • (d - e)), abs_nonneg a]

theorem constant_of_zero_derivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f 0 (Set.Icc 0 T) t) : f T = f 0 := by
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hf
    (C := 0) (fun _ _ => by simp) T ⟨hT, le_rfl⟩
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound

noncomputable def rotate (κ t : ℝ) (v : Vec2) : Vec2 :=
  Real.cos (κ * t) • v + Real.sin (κ * t) • perp v

theorem hasDerivAt_rotate (κ t : ℝ) (v : Vec2) :
    HasDerivAt (fun τ => rotate κ τ v) (κ • perp (rotate κ t v)) t := by
  have hc := (((hasDerivAt_id t).const_mul κ).cos).smul_const v
  have hs := (((hasDerivAt_id t).const_mul κ).sin).smul_const (perp v)
  apply (hc.add hs).congr_deriv
  ext i
  fin_cases i <;> simp [rotate, perp] <;> ring

theorem velocity_solution (κ T : ℝ) (v : ℝ → Vec2) (hT : 0 ≤ T)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (κ • perp (v t)) (Set.Icc 0 T) t) :
    v T = rotate κ T (v 0) := by
  let z := fun t => v t - rotate κ t (v 0)
  have hz : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt z (κ • perp (z t)) (Set.Icc 0 T) t := by
    intro t ht
    simpa only [z, perp_sub, smul_sub] using
      (OdeDeriv.hasDerivWithinAt_sub_apply (hv t ht)
        (hasDerivAt_rotate κ t (v 0)).hasDerivWithinAt)
  have henergy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun t => ‖z t‖ ^ 2) 0 (Set.Icc 0 T) t := by
    intro t ht
    simpa only [real_inner_smul_right, inner_perp_self, mul_zero] using (hz t ht).norm_sq
  have heq := constant_of_zero_derivative (fun t => ‖z t‖ ^ 2) T hT henergy
  simpa [z, rotate, sub_eq_zero] using heq

noncomputable def displacement (κ t : ℝ) (v : Vec2) : Vec2 :=
  (Real.sin (κ * t) / κ) • v + ((1 - Real.cos (κ * t)) / κ) • perp v

theorem hasDerivAt_displacement (κ t : ℝ) (v : Vec2) (hκ : κ ≠ 0) :
    HasDerivAt (fun τ => displacement κ τ v) (rotate κ t v) t := by
  have hs := ((((hasDerivAt_id t).const_mul κ).sin).div_const κ).smul_const v
  have hc := (((((hasDerivAt_id t).const_mul κ).cos).const_sub 1).div_const κ).smul_const
    (perp v)
  apply (hs.add hc).congr_deriv
  simp [rotate, hκ]

theorem position_solution (κ T : ℝ) (x v : ℝ → Vec2) (hκ : κ ≠ 0) (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (v t) (Set.Icc 0 T) t)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (κ • perp (v t)) (Set.Icc 0 T) t) :
    x T = x 0 + displacement κ T (v 0) := by
  have hvel : ∀ t ∈ Set.Icc 0 T, v t = rotate κ t (v 0) := by
    intro t ht
    exact velocity_solution κ t v ht.1 (fun τ hτ =>
      (hv τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2))
  have hz : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun t => x t - (x 0 + displacement κ t (v 0))) 0
        (Set.Icc 0 T) t := by
    intro t ht
    simpa only [hvel t ht, sub_self] using
      OdeDeriv.hasDerivWithinAt_sub_apply (hx t ht)
        ((hasDerivAt_displacement κ t (v 0) hκ).const_add (x 0)).hasDerivWithinAt
  have heq := constant_of_zero_derivative _ T hT hz
  simpa [displacement, sub_eq_zero] using heq

@[simp] def positionX : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (x, _, _, _) => x
@[simp] def velocityD : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (_, d, _, _) => d
@[simp] def positionY : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (_, _, y, _) => y
@[simp] def velocityE : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (_, _, _, e) => e

theorem flight_components (ω ρ : ℝ) {path : ℝ → Vec2 × Vec2 × Vec2 × Vec2}
    {interval : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt path (flight ω ρ (path t)) interval t) :
    HasDerivWithinAt (fun τ => positionX (path τ)) (velocityD (path t)) interval t ∧
    HasDerivWithinAt (fun τ => velocityD (path τ)) (ω • perp (velocityD (path t))) interval t ∧
    HasDerivWithinAt (fun τ => positionY (path τ)) (velocityE (path t)) interval t ∧
    HasDerivWithinAt (fun τ => velocityE (path τ)) (ρ • perp (velocityE (path t))) interval t := by
  have hx := OdeDeriv.hasDerivWithinAt_fst h
  have hdye := OdeDeriv.hasDerivWithinAt_snd h
  have hd := OdeDeriv.hasDerivWithinAt_fst hdye
  have hye := OdeDeriv.hasDerivWithinAt_snd hdye
  have hy := OdeDeriv.hasDerivWithinAt_fst hye
  have he := OdeDeriv.hasDerivWithinAt_snd hye
  exact ⟨hx, hd, hy, he⟩

noncomputable def circularTrajectory (κ : ℝ) (x d y e : Vec2) (t : ℝ) :=
  (x + displacement κ t d, rotate κ t d, y + displacement κ t e, rotate κ t e)

theorem flight_solution (κ T : ℝ) (path : ℝ → Vec2 × Vec2 × Vec2 × Vec2) (x d y e : Vec2)
    (hκ : κ ≠ 0) (hT : 0 ≤ T) (hinit : path 0 = (x, d, y, e))
    (hODE : Evolvable.denotation (flight κ κ) path (Set.Icc 0 T)) :
    path T = circularTrajectory κ x d y e T := by
  have hc := fun t ht => flight_components κ κ (hODE t ht)
  have hx := position_solution κ T (fun t => positionX (path t))
    (fun t => velocityD (path t)) hκ hT (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1)
  have hd := velocity_solution κ T (fun t => velocityD (path t)) hT
    (fun t ht => (hc t ht).2.1)
  have hy := position_solution κ T (fun t => positionY (path t))
    (fun t => velocityE (path t)) hκ hT (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2)
  have he := velocity_solution κ T (fun t => velocityE (path t)) hT
    (fun t ht => (hc t ht).2.2.2)
  simp only [hinit, positionX, velocityD, positionY, velocityE] at hx hd hy he
  exact Prod.ext hx (Prod.ext hd (Prod.ext hy he))

theorem circularTrajectory_evolution (κ : ℝ) (x d y e : Vec2) (T : ℝ)
    (hκ : κ ≠ 0) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop)
    (hdom : ∀ t ∈ Set.Icc 0 T, domain (circularTrajectory κ x d y e t)) :
    IsEvolution (circularTrajectory κ x d y e) (Evolvable.denotation (flight κ κ))
      domain (x, d, y, e) T := by
  apply And.intro (by simp [circularTrajectory, displacement, rotate])
  apply And.intro hdom
  intro t ht
  have hx := (hasDerivAt_displacement κ t d hκ).const_add x
  have hd := hasDerivAt_rotate κ t d
  have hy := (hasDerivAt_displacement κ t e hκ).const_add y
  have he := hasDerivAt_rotate κ t e
  exact (hx.prodMk (hd.prodMk (hy.prodMk he))).hasDerivWithinAt

theorem heading_inner (x d c : Vec2) (h : ∃ l ≥ (0 : ℝ), x + l • d = c) :
    ⟪x - c, perp d⟫ = 0 ∧ ⟪x - c, d⟫ = -‖x - c‖ * ‖d‖ := by
  obtain ⟨l, hl, hh⟩ := h
  have hpos : x - c = -(l • d) := by rw [← hh]; abel
  apply And.intro
  · rw [hpos, inner_neg_left, real_inner_smul_left, inner_perp_self]
    ring
  · rw [hpos, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl]
    ring

theorem sqrt_radius (r : ℝ) (hr : 0 ≤ r) : Real.sqrt (3 * r ^ 2) = Real.sqrt 3 * r := by
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

theorem speed_radius (r ω : ℝ) (d : Vec2) (hr : 0 ≤ r)
    (h : (r * ω) ^ 2 = ‖d‖ ^ 2) : ‖d‖ = r * |ω| := by
  apply (sq_eq_sq₀ (norm_nonneg d) (mul_nonneg hr (abs_nonneg ω))).mp
  rw [mul_pow, sq_abs, ← mul_pow]
  exact h.symm

theorem motion_norm_sq (κ t : ℝ) (x d c : Vec2) :
    ‖x + displacement κ t d - c‖ ^ 2 = ‖x - c‖ ^ 2 +
      2 * (Real.sin (κ * t) / κ) * ⟪x - c, d⟫ +
      2 * ((1 - Real.cos (κ * t)) / κ) * ⟪x - c, perp d⟫ +
      2 * ((1 - Real.cos (κ * t)) / κ ^ 2) * ‖d‖ ^ 2 := by
  have hpos : x + displacement κ t d - c = (x - c) + displacement κ t d := by abel
  rw [hpos, norm_add_sq_real]
  simp only [displacement, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, norm_perp, inner_add_right, real_inner_smul_right, real_inner_smul_left,
    inner_perp_self]
  have htrig := congrArg (fun s : ℝ => s / κ ^ 2 * ‖d‖ ^ 2)
    (Real.sin_sq_add_cos_sq (κ * t))
  ring_nf at htrig ⊢
  nlinarith

theorem cos_abs_mul (ω t : ℝ) : Real.cos (ω * t) = Real.cos (|ω| * t) := by
  by_cases h : 0 ≤ ω
  · simp only [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), neg_mul, Real.cos_neg]

theorem sin_div_abs (ω t : ℝ) :
    Real.sin (ω * t) / ω = Real.sin (|ω| * t) / |ω| := by
  by_cases h : 0 ≤ ω
  · simp only [abs_of_nonneg h]
  · simp only [abs_of_neg (lt_of_not_ge h), neg_mul, Real.sin_neg, neg_div_neg_eq]

theorem entry_motion_norm_sq (r ω t : ℝ) (x d c : Vec2) (hω : ω ≠ 0)
    (hposition : ‖x - c‖ = Real.sqrt 3 * r)
    (hheading : ∃ l ≥ (0 : ℝ), x + l • d = c) (hspeed : ‖d‖ = r * |ω|) :
    ‖x + displacement (-ω) t d - c‖ ^ 2 =
      r ^ 2 * (5 - 2 * Real.cos (|ω| * t) - 2 * Real.sqrt 3 * Real.sin (|ω| * t)) := by
  obtain ⟨horth, hinner⟩ := heading_inner x d c hheading
  rw [motion_norm_sq, horth, hinner, hposition]
  simp only [mul_zero, add_zero, neg_mul, Real.cos_neg, Real.sin_neg, neg_div_neg_eq,
    neg_sq, cos_abs_mul ω t, sin_div_abs ω t]
  rw [← sq_abs ω, hspeed, mul_pow (Real.sqrt 3) r, Real.sq_sqrt (by norm_num)]
  field_simp [abs_ne_zero.mpr hω]
  ring

theorem inner_perp_flip (u v : Vec2) : ⟪u, perp v⟫ = -⟪v, perp u⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, perp]
  ring

/-- The conserved anchor geometry of (14)–(15), with the fixed anchor eliminated.
Under the speed equation, this is `ω² * (4*r² - ‖h-c‖²)` for
`h = x - ω⁻¹ • perp d`. -/
noncomputable def entryCircleInvariant (r ω : ℝ) (c : Vec2) := fun (x, d) =>
  ‖d - ω • perp (x - c)‖ ^ 2 -
    2 * ω ^ 2 * (‖x - c‖ ^ 2 - r ^ 2)

theorem entryCircleInvariant_hasPrime (r ω : ℝ) (c : Vec2) :
    HasPrime (Evolvable.denotation (F (-ω))) (fun _ => True)
      (entryCircleInvariant r ω c) (fun _ => 0) := by
  ode_deriv [entryCircleInvariant, F, perp]

theorem entryCircleInvariant_initial (r ω : ℝ) (x d c : Vec2)
    (hposition : ‖x - c‖ = Real.sqrt 3 * r)
    (hheading : ∃ l ≥ (0 : ℝ), x + l • d = c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2) :
    entryCircleInvariant r ω c (x, d) = 0 := by
  have horth : ⟪d, perp (x - c)⟫ = 0 := by
    rw [inner_perp_flip, (heading_inner x d c hheading).1, neg_zero]
  rw [entryCircleInvariant, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, norm_perp, real_inner_smul_right, horth, mul_zero, sub_zero]
  rw [hposition, mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [hspeed]

theorem entry_tangent_of_radius (r ω T : ℝ) (c : Vec2) (x d : ℝ → Vec2) (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (d t) (Set.Icc 0 T) t)
    (hd : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt d ((-ω) • perp (d t)) (Set.Icc 0 T) t)
    (hinit : entryCircleInvariant r ω c (x 0, d 0) = 0)
    (hradius : ‖x T - c‖ ^ 2 = r ^ 2) : d T = ω • perp (x T - c) := by
  have hprime := entryCircleInvariant_hasPrime r ω c (fun t => (x t, d t))
    (Set.Icc 0 T) (fun t ht => (hx t ht).prodMk (hd t ht)) (fun _ _ => trivial)
  have heq := constant_of_zero_derivative
    (fun t => entryCircleInvariant r ω c (x t, d t)) T hT hprime
  rw [hinit] at heq
  simpa only [entryCircleInvariant, hradius, sub_self, mul_zero, sub_zero,
    sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] using heq

theorem AC4 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ (duration : ℝ) (trajectory : ℝ → Vec2 × Vec2 × Vec2 × Vec2),
          0 ≤ duration ∧ duration ≤ Real.pi * r / (3 * ‖d‖) ∧
          IsEvolution trajectory (Evolvable.denotation (flight (-ω) (-ω)))
            (fun _ => True) (x, d, y, e) duration ∧
          let (xr, _, yr, _) := trajectory duration
          ‖xr - c‖ ^ 2 = r ^ 2 ∧ ‖yr - c‖ ^ 2 = r ^ 2 := by
  intro r ω c x d y e ⟨hr, hd, hentry, hspeed, he⟩
  obtain ⟨hx, lx, hlx, hxc, hy, ly, hly, hyc⟩ := hentry
  have hω : ω ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, zero_pow (by decide)] at hspeed
    nlinarith [sq_pos_of_pos hd]
  have hs := speed_radius r ω d hr.le hspeed
  have hes : ‖e‖ = r * |ω| := he.trans hs
  have hxp := hx.trans (sqrt_radius r hr.le)
  have hyp := hy.trans (sqrt_radius r hr.le)
  let T := Real.pi / (3 * |ω|)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hperiod : |ω| * T = Real.pi / 3 := by dsimp [T]; field_simp
  apply Exists.intro T
  apply Exists.intro (circularTrajectory (-ω) x d y e)
  apply And.intro hT
  apply And.intro
  · rw [hs]
    dsimp [T]
    apply le_of_eq
    field_simp
  apply And.intro
    (circularTrajectory_evolution (-ω) x d y e T (neg_ne_zero.mpr hω)
      (fun _ => True) (fun _ _ => trivial))
  change ‖x + displacement (-ω) T d - c‖ ^ 2 = r ^ 2 ∧
    ‖y + displacement (-ω) T e - c‖ ^ 2 = r ^ 2
  rw [entry_motion_norm_sq r ω T x d c hω hxp ⟨lx, hlx, hxc⟩ hs,
    entry_motion_norm_sq r ω T y e c hω hyp ⟨ly, hly, hyc⟩ hes, hperiod,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hroot : 5 - 2 * (1 / 2 : ℝ) - 2 * Real.sqrt 3 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  simp only [hroot, mul_one, and_self]

theorem entry_evolution_tangent (r ω T : ℝ) (c x d y e : Vec2)
    (path : ℝ → Vec2 × Vec2 × Vec2 × Vec2)
    (hr : 0 < r) (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (he : ‖e‖ = ‖d‖) (hT : 0 ≤ T)
    (hevo : IsEvolution path (Evolvable.denotation (flight (-ω) (-ω)))
      (fun _ => True) (x, d, y, e) T)
    (hradius : ‖positionX (path T) - c‖ ^ 2 = r ^ 2) :
    let (xr, dr, yr, er) := path T
    R ω c xr dr yr er := by
  obtain ⟨hx, lx, hlx, hxc, hy, ly, hly, hyc⟩ := hentry
  have hxp := hx.trans (sqrt_radius r hr.le)
  have hyp := hy.trans (sqrt_radius r hr.le)
  have hdpos : 0 < ‖d‖ := by
    by_contra! h
    have hzero : d = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg d))
    have hxc' : x = c := by simpa only [hzero, smul_zero, add_zero] using hxc
    have hpositive : 0 < ‖x - c‖ := by rw [hxp]; positivity
    simp only [hxc', sub_self, norm_zero, lt_self_iff_false] at hpositive
  have hω : ω ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, zero_pow (by decide)] at hspeed
    nlinarith [sq_pos_of_pos hdpos]
  have hs := speed_radius r ω d hr.le hspeed
  have hes : ‖e‖ = r * |ω| := he.trans hs
  have hsol := flight_solution (-ω) T path x d y e (neg_ne_zero.mpr hω) hT hevo.1 hevo.2.2
  have hnorms : ‖positionY (path T) - c‖ ^ 2 = ‖positionX (path T) - c‖ ^ 2 := by
    rw [hsol]
    change ‖y + displacement (-ω) T e - c‖ ^ 2 = ‖x + displacement (-ω) T d - c‖ ^ 2
    rw [entry_motion_norm_sq r ω T y e c hω hyp ⟨ly, hly, hyc⟩ hes,
      entry_motion_norm_sq r ω T x d c hω hxp ⟨lx, hlx, hxc⟩ hs]
  have hc := fun t ht => flight_components (-ω) (-ω) (hevo.2.2 t ht)
  have hinitX : entryCircleInvariant r ω c (positionX (path 0), velocityD (path 0)) = 0 := by
    simpa only [hevo.1, positionX, velocityD] using
      entryCircleInvariant_initial r ω x d c hxp ⟨lx, hlx, hxc⟩ hspeed
  have hinitY : entryCircleInvariant r ω c (positionY (path 0), velocityE (path 0)) = 0 := by
    simpa only [hevo.1, positionY, velocityE] using
      entryCircleInvariant_initial r ω y e c hyp ⟨ly, hly, hyc⟩ (by rw [he]; exact hspeed)
  have hX := entry_tangent_of_radius r ω T c (fun t => positionX (path t))
    (fun t => velocityD (path t)) hT (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1) hinitX hradius
  have hY := entry_tangent_of_radius r ω T c (fun t => positionY (path t))
    (fun t => velocityE (path t)) hT (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2) hinitY (hnorms.trans hradius)
  exact ⟨hX, hY⟩

theorem AC3 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∀ res ∈ SetM.run (entryEvol ω (x, d, y, e)),
          let (x', d', y', e') := res
          ‖x' - c‖ ^ 2 = r ^ 2 → R ω c x' d' y' e' := by
  intro r ω c x d y e ⟨hr, hentry, hspeed, he⟩ res hrun
  apply (evolveSemantic_spec (Evolvable.denotation (flight (-ω) (-ω)))
    (fun _ => True) (x, d, y, e)
    (Q := fun (xr, dr, yr, er) => ‖xr - c‖ ^ 2 = r ^ 2 → R ω c xr dr yr er)).le_wp
    ?_ res hrun
  intro T hT path hevo hradius
  exact entry_evolution_tangent r ω T c x d y e path hr hentry hspeed he hT hevo hradius

theorem bind_mem {α β : Type} {p : SetM α} {q : α → SetM β} {a : α} {b : β}
    (ha : a ∈ SetM.run p) (hb : b ∈ SetM.run (q a)) : b ∈ SetM.run (p >>= q) := by
  change b ∈ ⋃ a ∈ SetM.run p, SetM.run (q a)
  exact Set.mem_iUnion_of_mem a (Set.mem_iUnion_of_mem ha hb)

theorem AC4_live :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ res ∈ SetM.run (entry_f ω r c x d y e),
          let (x', _, y', _) := res
          ‖x' - c‖ ^ 2 = r ^ 2 ∧ ‖y' - c‖ ^ 2 = r ^ 2 := by
  intro r ω c x d y e hpre
  obtain ⟨T, path, hT, _, hevo, hradii⟩ := AC4 r ω c x d y e hpre
  have hrun : path T ∈ SetM.run (entryEvol ω (x, d, y, e)) :=
    SemanticODE.mem_evolveSemantic _ _ _ T path hT hevo
  rcases hfinal : path T with ⟨xr, dr, yr, er⟩
  simp only [hfinal] at hradii hrun
  apply Exists.intro (xr, dr, yr, er)
  apply And.intro
  · unfold entry_f
    apply bind_mem hrun
    simp only [hradii.1, ite_true]
    rfl
  · exact hradii

theorem AC6_feasible :
    ∀ (p l : ℝ) (x d y e : Vec2),
      0 < l ∧ x + l • d = y + l • e ∧ ‖d‖ = ‖e‖ ∧ 0 < ‖d‖ ∧
      Separated (far p (l * ‖d‖ / Real.sqrt 3)) x y →
        ∃ ω : ℝ, (ω, x + l • d, l * ‖d‖ / Real.sqrt 3) ∈ SetM.run (agree_f p x d y e) := by
  intro p l x d y e ⟨hl, hinter, hde, hd, hsep⟩
  let c := x + l • d
  let r := l * ‖d‖ / Real.sqrt 3
  let ω := Real.sqrt 3 / l
  have hroot : 0 < Real.sqrt 3 := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrad : Real.sqrt 3 * r = l * ‖d‖ := by dsimp [r]; field_simp
  have hx : ‖x - c‖ = l * ‖d‖ := by
    have hvec : x - c = -(l • d) := by dsimp [c]; abel
    rw [hvec, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  have hy : ‖y - c‖ = l * ‖d‖ := by
    have hvec : y - c = -(l • e) := by dsimp [c]; rw [hinter]; abel
    rw [hvec, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hl, ← hde]
  have hentry : C r x d y e c :=
    ⟨by rw [hx, sqrt_radius r hr, hrad], l, hl.le, rfl,
      by rw [hy, sqrt_radius r hr, hrad], l, hl.le, hinter.symm⟩
  have hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2 := by
    have hmul : r * ω = ‖d‖ := by dsimp [r, ω]; field_simp
    rw [hmul]
  apply Exists.intro ω
  unfold agree_f
  apply bind_mem (a := c)
  · trivial
  apply bind_mem (a := r)
  · exact hr
  apply bind_mem (a := ())
  · exact hentry
  simp only [show Separated (far p r) x y from hsep, ite_true]
  apply bind_mem (a := ω)
  · trivial
  simp only [hspeed, ite_true]
  rfl

theorem speed_constant_variable (ω : ℝ → ℝ) (v : ℝ → Vec2) (T : ℝ) (hT : 0 ≤ T)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (ω t • perp (v t)) (Set.Icc 0 T) t) : ‖v T‖ = ‖v 0‖ := by
  have hprime : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun t => ‖v t‖ ^ 2) 0 (Set.Icc 0 T) t := by
    intro t ht
    simpa only [real_inner_smul_right, inner_perp_self, mul_zero] using (hv t ht).norm_sq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (constant_of_zero_derivative _ T hT hprime)

/-- Equation (7): each coordinate moves by at most `b*T`, even with varying turn rates. -/
theorem coordinate_displacement (ω : ℝ → ℝ) (x v : ℝ → Vec2) (T b : ℝ) (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (v t) (Set.Icc 0 T) t)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (ω t • perp (v t)) (Set.Icc 0 T) t)
    (hbound : ‖v 0‖ ≤ b) : ∀ i : Fin 2, |x T i - x 0 i| ≤ b * T := by
  have hspeed : ∀ t ∈ Set.Icc 0 T, ‖v t‖ = ‖v 0‖ := by
    intro t ht
    exact speed_constant_variable ω v t ht.1 (fun τ hτ =>
      (hv τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2))
  intro i
  have hderiv := fun t ht => OdeDeriv.hasDerivWithinAt_piLp_apply i (hx t ht)
  have hcoord : ∀ t ∈ Set.Ico 0 T, ‖v t i‖ ≤ b := by
    intro t ht
    exact (PiLp.norm_apply_le (v t) i).trans ((hspeed t ⟨ht.1, ht.2.le⟩).le.trans hbound)
  simpa only [Real.norm_eq_abs, sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hcoord T ⟨hT, le_rfl⟩

theorem far_coordinate (q : ℝ) (u : Vec2) (hq : 0 ≤ q)
    (h : (Real.sqrt 2 * q) ^ 2 ≤ ‖u‖ ^ 2) : ∃ i : Fin 2, q ≤ |u i| := by
  by_contra! hnot
  have h0 := (sq_lt_sq₀ (abs_nonneg (u 0)) hq).mpr (hnot 0)
  have h1 := (sq_lt_sq₀ (abs_nonneg (u 1)) hq).mpr (hnot 1)
  rw [sq_abs] at h0 h1
  have hnorm : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hnorm] at h
  nlinarith

/-- Appendix A.5: separation in one coordinate survives the two displacement bounds. -/
theorem separated_of_coordinate_bounds (p b T : ℝ) (x y xr yr : Vec2)
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hsep : Separated (Real.sqrt 2 * (p + 2 * b * T)) x y)
    (hx : ∀ i : Fin 2, |xr i - x i| ≤ b * T)
    (hy : ∀ i : Fin 2, |yr i - y i| ≤ b * T) : Separated p xr yr := by
  obtain ⟨i, hi⟩ := far_coordinate (p + 2 * b * T) (x - y) (by positivity) hsep
  change p + 2 * b * T ≤ |x i - y i| at hi
  have htriangle : |x i - y i| ≤ |xr i - yr i| + |xr i - x i| + |yr i - y i| := by
    have heq : x i - y i = (xr i - yr i) + (-(xr i - x i)) + (yr i - y i) := by ring
    rw [heq]
    have hab := abs_add_le (xr i - yr i) (-(xr i - x i))
    have habc := abs_add_le ((xr i - yr i) + (-(xr i - x i))) (yr i - y i)
    simp only [abs_neg] at hab habc ⊢
    linarith
  have hcoord : p ≤ |xr i - yr i| := by linarith [hx i, hy i]
  have hnorm : |xr i - yr i| ≤ ‖xr - yr‖ := PiLp.norm_apply_le (xr - yr) i
  exact (sq_le_sq₀ hp (norm_nonneg _)).mpr (hcoord.trans hnorm)

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
          Separated p x' y' := by
  intro p b T x d y e ω ρ ⟨hp, hb, hT, hde, he, hsep⟩ duration path h0 hduration hevo
  have hc := fun t ht => flight_components (ω t) (ρ t) (hevo.2.2 t ht)
  have hdbound : ‖d‖ ≤ b := (sq_le_sq₀ (norm_nonneg d) hb).mp (hde.trans he)
  have hebound : ‖e‖ ≤ b := (sq_le_sq₀ (norm_nonneg e) hb).mp he
  have hx := coordinate_displacement ω (fun t => positionX (path t))
    (fun t => velocityD (path t)) duration b h0 (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1) (by simpa only [hevo.1, velocityD] using hdbound)
  have hy := coordinate_displacement ρ (fun t => positionY (path t))
    (fun t => velocityE (path t)) duration b h0 (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2) (by simpa only [hevo.1, velocityE] using hebound)
  rcases hfinal : path duration with ⟨xr, dr, yr, er⟩
  simp only [hevo.1, hfinal, positionX, positionY] at hx hy
  apply separated_of_coordinate_bounds p b T x y xr yr hp hb hT hsep
  · exact fun i => (hx i).trans (mul_le_mul_of_nonneg_left hduration hb)
  · exact fun i => (hy i).trans (mul_le_mul_of_nonneg_left hduration hb)

theorem separated_mono (p q : ℝ) (x y : Vec2) (hp : 0 ≤ p) (hpq : p ≤ q)
    (h : Separated q x y) : Separated p x y :=
  ((sq_le_sq₀ hp (hp.trans hpq)).mpr hpq).trans h

theorem stationary_flight (ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x y : Vec2) :
    ∀ res ∈ SetM.run (evolve (flight ω ρ) domain (x, 0, y, 0)),
      res = (x, 0, y, 0) := by
  apply (evolveSemantic_spec (Evolvable.denotation (flight ω ρ)) domain (x, 0, y, 0)
    (Q := fun res => res = (x, 0, y, 0))).le_wp
  intro T hT path hevo
  have hc := fun t ht => flight_components ω ρ (hevo.2.2 t ht)
  have hx := coordinate_displacement (fun _ => ω) (fun t => positionX (path t))
    (fun t => velocityD (path t)) T 0 hT (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1) (by simp [hevo.1, velocityD])
  have hy := coordinate_displacement (fun _ => ρ) (fun t => positionY (path t))
    (fun t => velocityE (path t)) T 0 hT (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2) (by simp [hevo.1, velocityE])
  have hd := speed_constant_variable (fun _ => ω) (fun t => velocityD (path t))
    T hT (fun t ht => (hc t ht).2.1)
  have he := speed_constant_variable (fun _ => ρ) (fun t => velocityE (path t))
    T hT (fun t ht => (hc t ht).2.2.2)
  rcases hfinal : path T with ⟨xr, dr, yr, er⟩
  simp only [hevo.1, hfinal, positionX, velocityD, positionY, velocityE, norm_zero,
    norm_eq_zero, zero_mul, abs_nonpos_iff, sub_eq_zero] at hx hy hd he
  exact Prod.ext (by ext i; exact hx i) (Prod.ext hd (Prod.ext (by ext i; exact hy i) he))

theorem far_ge (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) : p ≤ far p r := by
  have hroot : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hoffset : 0 ≤ (2 / 3 : ℝ) * Real.pi * r := by positivity
  unfold far
  nlinarith [mul_nonneg (sub_nonneg.mpr hroot) (add_nonneg hp hoffset)]

theorem separated_of_far (p r : ℝ) (x y : Vec2) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (h : Separated (far p r) x y) : Separated p x y :=
  separated_mono p (far p r) x y hp (far_ge p r hp hr) h

def freeSafeStep (p r ω ρ : ℝ) (x d y e : Vec2) := freeStep (far p r) ω ρ x d y e

@[spec] theorem freeSafeStep_spec (p r ω ρ : ℝ) (x d y e : Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ Separated p x y⦄ freeSafeStep p r ω ρ x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  rintro ⟨hp, hr, _⟩
  apply SetM.wp_and
  · exact dW (ode := flight ω ρ) (pre := fun _ => True)
      (fun (xr, _, yr, _) hdom => separated_of_far p r xr yr hp hr hdom)
      (x, d, y, e) trivial
  · exact AC2 ω ρ _ x d y e

/-- Free flight preserves ordinary separation even when no positive-duration
flight is possible. Its zero-iteration branch simply retains the safe state. -/
def free_safe (p r : ℝ) (x d₀ y e₀ : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires 0 ≤ p ∧ 0 ≤ r ∧ Separated p x y
    ensures (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d₀‖ ∧ ‖er‖ = ‖e₀‖
    := do
  let mut (x, d, y, e) := (x, d₀, y, e₀)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        0 ≤ p ∧ 0 ≤ r ∧ Separated p x y ∧ ‖d‖ = ‖d₀‖ ∧ ‖e‖ = ‖e₀‖ do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← freeSafeStep p r ω ρ x d y e
  return (x, d, y, e)

def safeCirc (_p ω : ℝ) (_c x₀ d₀ y₀ e₀ x d y e : Vec2) :=
  circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)

@[spec] theorem safeCirc_spec (p ω : ℝ) (c x₀ d₀ y₀ e₀ x d y e : Vec2) :
    ⦃R ω c x d y e ∧ Separated p x y⦄
    safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
    ⦃fun (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  intro hpre res hrun
  obtain ⟨hR, hsep⟩ := AC1_circ p ω c _ x d y e hpre res hrun
  exact ⟨hR, hsep, AC2 ω ω _ x d y e res hrun⟩

def safeExit (_p _ω : ℝ) (_c x d y e : Vec2) := exitEvol (x, d, y, e)

@[spec] theorem safeExit_spec (p ω : ℝ) (c x d y e : Vec2) :
    ⦃R ω c x d y e ∧ Separated p x y⦄ safeExit p ω c x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  intro hpre res hrun
  exact ⟨AC7 p ω c x d y e hpre res hrun, AC2 0 0 (fun _ => True) x d y e res hrun⟩

def circ_f' (p ω : ℝ) (c x₀ d₀ y₀ e₀ x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires R ω c x d y e ∧ Separated p x y
    ensures (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let (x, d, y, e) ← safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
  ensure (exitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  return (x, d, y, e)

def exit_f' (p ω : ℝ) (c x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires R ω c x d y e ∧ Separated p x y
    ensures (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let (x, d, y, e) ← safeExit p ω c x d y e
  return (x, d, y, e)

theorem ftrm_eq_loop (p r : ℝ) (x d y e : Vec2) :
    ftrm p r x d y e = (do
      let (x, _, y, _, _) ← loop (ftrmBody p) (x, d, y, e, r)
      return (x, y)) := by
  simp [ftrm, loop, ftrmBody]

/-! ## Unrestricted entry: safety for arbitrarily many entry turns -/

/-- Equal entry radii and speeds imply a common time to the negotiated center. -/
theorem entry_common_heading (r ω : ℝ) (c x d y e : Vec2) (hr : 0 < r)
    (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (hde : ‖e‖ = ‖d‖) :
    ∃ l : ℝ, 0 ≤ l ∧ x + l • d = c ∧ y + l • e = c ∧ (l * ω) ^ 2 = 3 := by
  obtain ⟨hx, l, hl, hxc, hy, m, hm, hyc⟩ := hentry
  have hxp : ‖x - c‖ = Real.sqrt 3 * r := hx.trans (sqrt_radius r hr.le)
  have hyp : ‖y - c‖ = Real.sqrt 3 * r := hy.trans (sqrt_radius r hr.le)
  have hposx : x - c = -(l • d) := by rw [← hxc]; abel
  have hposy : y - c = -(m • e) := by rw [← hyc]; abel
  have hlnorm : l * ‖d‖ = Real.sqrt 3 * r := by
    simpa only [hposx, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl] using hxp
  have hmnorm : m * ‖d‖ = Real.sqrt 3 * r := by
    simpa only [hposy, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm, hde] using hyp
  have hd : ‖d‖ ≠ 0 := by
    intro hz
    have hroot : 0 < Real.sqrt (3 : ℝ) := by positivity
    rw [hz, mul_zero] at hlnorm
    nlinarith
  have hlm : l = m := mul_right_cancel₀ hd (hlnorm.trans hmnorm.symm)
  apply Exists.intro l
  apply And.intro hl
  apply And.intro hxc
  apply And.intro (by simpa only [hlm] using hyc)
  apply mul_right_cancel₀ (pow_ne_zero 2 hr.ne')
  calc
    (l * ω) ^ 2 * r ^ 2 = l ^ 2 * (r * ω) ^ 2 := by ring
    _ = (l * ‖d‖) ^ 2 := by rw [hspeed, mul_pow]
    _ = (Real.sqrt 3 * r) ^ 2 := congrArg (fun a : ℝ => a ^ 2) hlnorm
    _ = 3 * r ^ 2 := by rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

noncomputable def relativeEntryInvariant (q ω : ℝ) := fun (x, d, y, e) =>
  ‖d - e - ω • perp (x - y)‖ ^ 2 -
    2 * ω ^ 2 * (‖x - y‖ ^ 2 - q)

theorem relativeEntryInvariant_hasPrime (q ω : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight (-ω) (-ω))) domain
      (relativeEntryInvariant q ω) (fun _ => 0) := by
  ode_deriv [relativeEntryInvariant, flight, F, G, perp]

theorem relativeEntryInvariant_initial (l ω : ℝ) (x d y e : Vec2)
    (hpos : x - y = -(l • (d - e))) (hsq : (l * ω) ^ 2 = 3) :
    relativeEntryInvariant (‖x - y‖ ^ 2 / 3) ω (x, d, y, e) = 0 := by
  have horth : ⟪d - e, perp (x - y)⟫ = 0 := by
    rw [inner_perp_flip, hpos, inner_neg_left, real_inner_smul_left, inner_perp_self]
    ring
  have hspeed : ω ^ 2 * ‖x - y‖ ^ 2 = 3 * ‖d - e‖ ^ 2 := by
    rw [hpos, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc
      _ = (l * ω) ^ 2 * ‖d - e‖ ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [relativeEntryInvariant, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_perp,
    real_inner_smul_right, horth, mul_zero, sub_zero]
  nlinarith

/-- Relative anchor geometry bounds distance throughout every complete entry circle.
The duration is arbitrary; no first-hit domain or final radius test is used. -/
theorem unrestricted_entry_distance (r ω : ℝ) (c x d y e : Vec2) (hr : 0 < r)
    (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (hde : ‖e‖ = ‖d‖) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    ∀ res ∈ SetM.run (evolve (flight (-ω) (-ω)) domain (x, d, y, e)),
      let (xr, _, yr, _) := res
      ‖x - y‖ ^ 2 ≤ 3 * ‖xr - yr‖ ^ 2 := by
  obtain ⟨l, _, hxc, hyc, hsq⟩ := entry_common_heading r ω c x d y e hr hentry hspeed hde
  have hpos : x - y = -(l • (d - e)) := by
    calc
      _ = (x + l • d) - (y + l • e) - l • (d - e) := by rw [smul_sub]; abel
      _ = _ := by rw [hxc, hyc, sub_self, zero_sub]
  have hω : ω ≠ 0 := by
    intro hz
    norm_num [hz] at hsq
  intro ⟨xr, dr, yr, er⟩ hrun
  have hinv := dIeq (ode := flight (-ω) (-ω)) (domain := domain)
    (pre := fun st => relativeEntryInvariant (‖x - y‖ ^ 2 / 3) ω st = 0)
    (relativeEntryInvariant (‖x - y‖ ^ 2 / 3) ω) (fun _ => 0)
    (relativeEntryInvariant_hasPrime _ ω domain) (fun _ h => h) (fun _ _ => rfl)
    (x, d, y, e) (relativeEntryInvariant_initial l ω x d y e hpos hsq) (xr, dr, yr, er) hrun
  change ‖dr - er - ω • perp (xr - yr)‖ ^ 2 -
    2 * ω ^ 2 * (‖xr - yr‖ ^ 2 - ‖x - y‖ ^ 2 / 3) = 0 at hinv
  have hprod : 0 ≤ 2 * ω ^ 2 * (‖xr - yr‖ ^ 2 - ‖x - y‖ ^ 2 / 3) := by
    rw [← sub_eq_zero.mp hinv]
    exact sq_nonneg _
  have hfactor : 0 < 2 * ω ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hω)
  have hgap := nonneg_of_mul_nonneg_right hprod hfactor
  nlinarith

/-- The paper's negotiated far margin exceeds the loss allowed by the relative
entry-circle invariant. The entry radii also bound the initial distance above. -/
theorem negotiated_entry_margin (p r : ℝ) (c x d y e : Vec2) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hentry : C r x d y e c) (hsep : Separated (far p r) x y) :
    3 * p ^ 2 ≤ ‖x - y‖ ^ 2 := by
  obtain ⟨hx, _, _, _, hy, _, _, _⟩ := hentry
  have hupper : ‖x - y‖ ≤ 2 * Real.sqrt 3 * r := by
    calc
      _ = ‖(x - c) - (y - c)‖ := by congr 1; abel
      _ ≤ ‖x - c‖ + ‖y - c‖ := norm_sub_le _ _
      _ = _ := by rw [hx, hy, sqrt_radius r hr]; ring
  have hupperSq : ‖x - y‖ ^ 2 ≤ 12 * r ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (x - y)) (by positivity)).mpr hupper
    norm_num only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h
    exact h
  have hoffset : r ≤ (2 / 3 : ℝ) * Real.pi * r := by
    have hpi : (1 : ℝ) ≤ (2 / 3 : ℝ) * Real.pi := by nlinarith [Real.two_le_pi]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hr
  have hsmall : 0 ≤ Real.sqrt 2 * (p + r) := by positivity
  have hlarge : 0 ≤ far p r := by unfold far; positivity
  have hfar : Real.sqrt 2 * (p + r) ≤ far p r := by
    unfold far
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
  have hlower : 2 * (p + r) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have h := ((sq_le_sq₀ hsmall hlarge).mpr hfar).trans hsep
    simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using h
  have hprod : 0 ≤ p * r := mul_nonneg hp hr
  have hbound : p ≤ 2 * r := by
    by_contra! h
    have hpr : 2 * r ^ 2 ≤ p * r := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h.le) hr]
    have hsq : (2 * r) ^ 2 < p ^ 2 := (sq_lt_sq₀ (by positivity) hp).mpr h
    nlinarith
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hbound), sq_nonneg p]

/-- Unrestricted entry preserves separation at every intermediate time. -/
theorem unrestricted_entry_safe (p r ω : ℝ) (c x d y e : Vec2)
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hentry : C r x d y e c)
    (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2) (hde : ‖e‖ = ‖d‖)
    (hsep : Separated (far p r) x y) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    ∀ res ∈ SetM.run (evolve (flight (-ω) (-ω)) domain (x, d, y, e)),
      let (xr, _, yr, _) := res
      Separated p xr yr := by
  intro ⟨xr, dr, yr, er⟩ hrun
  by_cases hrpos : 0 < r
  · have hbound := unrestricted_entry_distance r ω c x d y e hrpos hentry hspeed hde
      domain (xr, dr, yr, er) hrun
    have hmargin := negotiated_entry_margin p r c x d y e hp hr hentry hsep
    change p ^ 2 ≤ ‖xr - yr‖ ^ 2
    nlinarith
  · have hz : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    have hd : d = 0 := by simpa [hz] using hspeed.symm
    have he : e = 0 := by simpa [hd] using hde
    have hrest := stationary_flight (-ω) (-ω) domain x y (xr, dr, yr, er)
      (by simpa only [hd, he] using hrun)
    have hx : xr = x := congrArg positionX hrest
    have hy : yr = y := congrArg positionY hrest
    rw [hx, hy]
    exact separated_of_far p r x y hp hr hsep

theorem AC5_entry :
    ∀ (p r ω : ℝ) (c x d y e : Vec2),
      0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ ∧
      Separated (far p r) x y →
        ∀ res ∈ SetM.run (entryEvol ω (x, d, y, e)),
          let (x', _, y', _) := res
          Separated p x' y' := by
  intro p r ω c x d y e ⟨hp, hr, hentry, hspeed, hde, hsep⟩ res hrun
  exact unrestricted_entry_safe p r ω c x d y e hp hr hentry hspeed hde hsep
    (fun _ => True) res hrun

/-- Successful unrestricted entry establishes tangency after any number of turns. -/
theorem unrestricted_entry_tangent (r ω : ℝ) (c x d y e : Vec2) (hr : 0 ≤ r)
    (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (hde : ‖e‖ = ‖d‖) :
    ∀ res ∈ SetM.run (evolve (flight (-ω) (-ω)) (fun _ => True) (x, d, y, e)),
      ‖positionX res - c‖ ^ 2 = r ^ 2 →
      let (xr, dr, yr, er) := res
      R ω c xr dr yr er := by
  intro res hrun
  by_cases hrpos : 0 < r
  · exact AC3 r ω c x d y e ⟨hrpos, hentry, hspeed, hde⟩ res hrun
  · intro _
    have hz : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    obtain ⟨hx, _, _, _, hy, _, _, _⟩ := hentry
    have hxc : x = c := sub_eq_zero.mp (norm_eq_zero.mp (by simpa [hz] using hx))
    have hyc : y = c := sub_eq_zero.mp (norm_eq_zero.mp (by simpa [hz] using hy))
    have hd : d = 0 := by simpa [hz] using hspeed.symm
    have he : e = 0 := by simpa [hd] using hde
    have hrest := stationary_flight (-ω) (-ω) (fun _ => True) x y res
      (by simpa only [hd, he] using hrun)
    rw [hrest]
    have hperp : perp (0 : Vec2) = 0 := by
      ext i
      fin_cases i <;> simp [perp, PiLp.toLp_apply]
    simp only [R, hxc, hyc, sub_self, hperp, smul_zero, and_self]

def unrestrictedEntryStep (_p _r ω : ℝ) (_c x d y e : Vec2) :=
  entryEvol ω (x, d, y, e)

@[spec] theorem unrestrictedEntryStep_spec (p r ω : ℝ) (c x d y e : Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y⦄
    unrestrictedEntryStep p r ω c x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧
      (‖xr - c‖ ^ 2 = r ^ 2 → R ω c xr dr yr er) ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  rintro ⟨hp, hr, hentry, hspeed, hde, hsep⟩ res hrun
  exact ⟨AC5_entry p r ω c x d y e ⟨hp, hr, hentry, hspeed, hde, hsep⟩ res hrun,
    unrestricted_entry_tangent r ω c x d y e hr hentry hspeed hde res hrun,
    AC2 (-ω) (-ω) (fun _ => True) x d y e res hrun⟩

/-- A contract for the unchanged `entry_f`, including every permitted extra turn. -/
def unrestrictedEntry (p r ω : ℝ) (c x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires 0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y
    ensures (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let (x, d, y, e) ← unrestrictedEntryStep p r ω c x d y e
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  return (x, d, y, e)

theorem entry_f_safe (p r ω : ℝ) (c x d y e : Vec2)
    (hpre : 0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y) :
    ∀ res ∈ SetM.run (entry_f ω r c x d y e),
      let (xr, dr, yr, er) := res
      R ω c xr dr yr er ∧ Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖ := by
  intro res hrun
  exact (unrestrictedEntry.spec p r ω c x d y e).le_wp hpre res hrun

def ftrmBody' (p : ℝ) (x d y e : Vec2) (r : ℝ) : SetM (Vec2 × Vec2 × Vec2 × Vec2 × ℝ)
    requires Inv p (x, d, y, e, r)
    ensures res => Inv p res
    := do
  let (x, d, y, e) ← free_safe p r x d y e
  let (ω, c, r) ← agree_f' p x d y e
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← unrestrictedEntry p r ω c x d y e
  let (x, d, y, e) ← circ_f' p ω c x₀ d₀ y₀ e₀ x d y e
  let (x, d, y, e) ← exit_f' p ω c x d y e
  return (x, d, y, e, r)

@[spec] theorem ftrmBody_spec (p : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2 × ℝ) :
    ⦃Inv p st⦄ ftrmBody p st ⦃Inv p⦄ := by
  rcases st with ⟨x, d, y, e, r⟩
  exact ftrmBody'.spec p x d y e r

theorem ftrmBody_inv :
    ∀ (p : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2 × ℝ), Inv p st →
      ∀ res ∈ SetM.run (ftrmBody p st), Inv p res := by
  intro p st hpre res hrun
  exact (ftrmBody_spec p st).le_wp hpre res hrun

def ftrmRuns (p : ℝ) (initial : Vec2 × Vec2 × Vec2 × Vec2 × ℝ) :
    SetM (Vec2 × Vec2 × Vec2 × Vec2 × ℝ)
    requires Inv p initial
    ensures res => Inv p res
    := do
  let mut st := initial
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => Inv p st do
    st ← ftrmBody p st
  return st

@[spec] theorem ftrmLoop_spec (p : ℝ) (initial : Vec2 × Vec2 × Vec2 × Vec2 × ℝ) :
    ⦃Inv p initial⦄ loop (ftrmBody p) initial ⦃Inv p⦄ := by
  exact ftrmRuns.spec p initial

/-- FTRM endpoint safety with unrestricted `entry_f` and the unguarded exit.
The proof uses entry geometry rather than an entry-time bound. -/
theorem ftrm_safe :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ res ∈ SetM.run (ftrm p r x d y e),
          let (xr, yr) := res
          Separated p xr yr := by
  intro p r x d y e ⟨hp, hde, hr, hsep⟩ res hrun
  have hinv : Inv p (x, d, y, e, r) :=
    ⟨hp, hr.le, hde, separated_of_far p r x y hp hr.le hsep⟩
  rw [ftrm_eq_loop] at hrun
  apply SetM.of_wp_run_mem hrun
  vcgen invariants
  | inv1 => fun _pref _suff st => Inv p st
  all_goals grind

def ftrmPrefix' (p : ℝ) (k : Fin 5) (x d y e : Vec2) (r : ℝ) : SetM (Vec2 × Vec2)
    requires Inv p (x, d, y, e, r)
    ensures (xr, yr) => Separated p xr yr
    := do
  let (x, d, y, e) ← free_safe p r x d y e
  if k = 0 then return (x, y)
  let (ω, c, r) ← agree_f' p x d y e
  if k = 1 then return (x, y)
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← unrestrictedEntryStep p r ω c x d y e
  if k = 2 then return (x, y)
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  let (x, d, y, e) ← safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
  if k = 3 then return (x, y)
  ensure (exitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← safeExit p ω c x d y e
  return (x, y)

@[spec] theorem ftrmPrefix_spec (p : ℝ) (k : Fin 5) (st : Vec2 × Vec2 × Vec2 × Vec2 × ℝ) :
    ⦃Inv p st⦄ ftrmPrefix p k st ⦃fun (x, y) => Separated p x y⦄ := by
  rcases st with ⟨x, d, y, e, r⟩
  exact ftrmPrefix'.spec p k x d y e r

theorem ftrmPrefix_safe :
    ∀ (p : ℝ) (k : Fin 5) (st : Vec2 × Vec2 × Vec2 × Vec2 × ℝ), Inv p st →
      ∀ res ∈ SetM.run (ftrmPrefix p k st),
        let (xr, yr) := res
        Separated p xr yr := by
  intro p k st hpre res hrun
  exact (ftrmPrefix_spec p k st).le_wp hpre res hrun

/-- Throughout safety for the FTRM: after any number of its
completed iterations, every prefix of every additional phase is separated.
Entry may take arbitrarily many turns and exit has no final separation guard. -/
theorem ftrm_safe_throughout :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ st ∈ SetM.run (loop (ftrmBody p) (x, d, y, e, r)),
          ∀ k : Fin 5, ∀ res ∈ SetM.run (ftrmPrefix p k st),
            let (xr, yr) := res
            Separated p xr yr := by
  intro p r x d y e ⟨hp, hde, hr, hsep⟩ st hrun k res hprefix
  have hinv : Inv p (x, d, y, e, r) :=
    ⟨hp, hr.le, hde, separated_of_far p r x y hp hr.le hsep⟩
  have hstate := (ftrmLoop_spec p (x, d, y, e, r)).le_wp hinv st hrun
  exact (ftrmPrefix_spec p k st).le_wp hstate res hprefix

end FM09.Proofs
