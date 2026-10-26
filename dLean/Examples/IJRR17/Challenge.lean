import dLean.Examples.IJRR17.Model

open dLean

namespace IJRR17

/-- Journal Theorem 1 / archive "Theorem 1: Static safety". -/
theorem dwss_safe :
    ∀ A b Ω ε p d o s ω r,
      Bounds A b 0 ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwss A b Ω ε p d o s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          0 < distanceSq p_res o_res := sorry

/-- Journal Theorem 2 / archive "Theorem 2: Passive safety". -/
theorem dwps_safe :
    ∀ A b V Ω ε p d o v s ω r,
      Bounds A b V ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwps A b V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := sorry

/-- Journal Theorem 3, with the archive's explicit initial stoppedness,
coarse obstacle-speed bound, and its fixed-direction, bounded-braking diamond. -/
theorem dwpfs_safe :
    ∀ A b bo τ V Ω ε p d o v s ω r,
      Bounds A b V ε → 0 ≤ τ → 0 < bo → FriendlyInitial bo τ V p d o v s →
        ∀ res ∈ SetM.run (dwpfs A b bo τ V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          let v_res := res.2.2.2.2.2.2
          PassiveFriendlySafe bo τ V ε p_res o_res v_res s_res := sorry

/-- Journal Theorem 4 / archive "Theorem 4: Passive orientation safety". -/
theorem dwpos_safe :
    ∀ A b V ε γ p d o v s ω r β visible,
      Bounds A b V ε → 0 < γ →
      (Initial p d o s ∧ β = 0 ∧ r ≠ 0) →
        ∀ res ∈ SetM.run (dwpos A b V ε γ p d o v s ω r β visible),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          let β_res := res.2.2.2.2.2.2.2.1
          let visible_res := res.2.2.2.2.2.2.2.2
          0 < s_res → 0 < distanceSq p_res o_res ∨
            (¬0 < visible_res ∧ |β_res| < γ) := sorry

/-- Journal Theorem 5 / archive "Passive safety with actual acceleration". -/
theorem dwpsa_safe :
    ∀ A b V Ω ε p d o v s ω r,
      Bounds A b V ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsa A b V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := sorry

/-- Journal Theorem 6 / archive "Passive safety despite location uncertainty". -/
theorem dwpslu_safe :
    ∀ A b V Ω ε Δp p d o v s ω r,
      Bounds A b V ε → 0 ≤ Δp → Initial p d o s →
        ∀ res ∈ SetM.run (dwpslu A b V Ω ε Δp p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := sorry

/-- Journal Theorem 7 / archive "Passive safety despite actuator perturbation". -/
theorem dwpsap_safe :
    ∀ A b V Ω ε Δa p d o v s ω r,
      Bounds A b V ε → 0 < Δa → Δa ≤ 1 → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsap A b V Ω ε Δa p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := sorry

/-- Journal Theorem 8 / archive "Passive safety despite velocity uncertainty". -/
theorem dwpsvu_safe :
    ∀ A b V Ω ε Δs p d o v s ω r,
      Bounds A b V ε → 0 ≤ Δs → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsvu A b V Ω ε Δs p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := sorry

/-- Journal Theorem 9 / archive "Passive safety for asynchronous controllers". -/
theorem dwpsns_safe :
    ∀ A b V Ω ε p d o v s ω r,
      Bounds A b V ε → Initial p d o s →
        ∀ res ∈ SetM.run (dwpsns A b V Ω ε p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          PassiveSafe p_res o_res s_res := sorry

/-- Journal Theorem 10, Section 7.4, equations (59)--(60). This is a direct
paper transcription, not an entry from the KeYmaera X archive. Initial obstacle
velocities are unrestricted as printed; see the source caveat in the reference notes. -/
theorem dwnobs_safe :
    ∀ A b Ω ε (O : Set Obstacle) (V : Obstacle → ℝ)
      (p d : Vec2) (o v : Obstacle → Vec2) s ω r,
      (0 ≤ A ∧ 0 < b ∧ 0 ≤ Ω ∧ 0 < ε) → (∀ i ∈ O, 0 ≤ V i) →
      (s = 0 ∧ r ≠ 0 ∧ UnitDirection d) →
        ∀ res ∈ SetM.run (dwnobs A b Ω ε O V p d o v s ω r),
          let p_res := res.1
          let o_res := res.2.2.1
          let s_res := res.2.2.2.1
          s_res ≠ 0 → ∀ i ∈ O, 0 < infNorm (p_res - o_res i) := sorry

/-- Journal Theorem 11, using the archive's parameter bounds: every successful
run stays below the far waypoint boundary, and some run enters the goal region. -/
theorem dwwp_live :
    ∀ A b ε g Δg Vg p s,
      WaypointBounds A b ε Δg Vg → (s = 0 ∧ p < g - Δg) →
        (∀ res ∈ SetM.run (dwwp A b ε g Δg Vg p s),
          let p_res := res.1
          p_res < g + Δg) ∧
        (∃ res ∈ SetM.run (dwwp A b ε g Δg Vg p s),
          let p_res := res.1
          g - Δg < p_res) := sorry

/-- Journal Theorem 12 / archive "Cross intersection": universal collision
exclusion at the intersection and existential successful crossing. -/
theorem dwcx_live :
    ∀ A b Vmin ε p s o v,
      (0 < A ∧ 0 < b ∧ 0 < ε ∧ 0 < Vmin) → (s = 0 ∧ Vmin ≤ v ∧ p < 0) →
        (∀ res ∈ SetM.run (dwcx A b Vmin ε p s o v),
          let p_res := res.1
          let o_res := res.2.2.1
          p_res = 0 → o_res ≠ 0) ∧
        (∃ res ∈ SetM.run (dwcx A b Vmin ε p s o v),
          let p_res := res.1
          0 < p_res) := sorry

end IJRR17
