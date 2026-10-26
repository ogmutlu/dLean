import dLean.Examples.FM09.Model

open dLean

namespace FM09

/-- Initially separated aircraft remain separated after any finite NTRM run. -/
theorem ntrm_safe :
    ∀ (p : ℝ) (x d y e : Vec2), Separated p x y →
      ∀ res ∈ SetM.run (ntrm p x d y e),
        let x_res := res.1
        let y_res := res.2
        Separated p x_res y_res := sorry

theorem ftrm_end_safe :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ r > 0 ∧ Separated (far p r) x y →
        ∀ res ∈ SetM.run (ftrm p r x d y e),
          let x_res := res.1
          let y_res := res.2.2.1
          Separated p x_res y_res := sorry

/-- Throughout safety for the FTRM: after any number of its
completed iterations, every prefix of every additional phase is separated.
Entry may take arbitrarily many turns and exit has no final separation guard. -/
theorem ftrm_throughout_safe :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ tmp ∈ SetM.run (ftrm p r x d y e),
        let x := tmp.1
        let d := tmp.2.1
        let y := tmp.2.2.1
        let e := tmp.2.2.2.1
        let r := tmp.2.2.2.2
          ∀ k : Fin 5, ∀ res ∈ SetM.run (ftrmPrefix p r k x d y e),
          let x_res := res.1
          let y_res := res.2
          Separated p x_res y_res := sorry

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
not hypotheses here; they exist by the entry configuration `C`. -/
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

end FM09
