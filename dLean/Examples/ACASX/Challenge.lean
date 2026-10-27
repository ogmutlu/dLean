import dLean.Examples.ACASX.Model

open dLean

namespace ACASX

/-- STTT Theorem 1; preserve the stronger region postcondition of `acasx.kyx`. -/
theorem immediate_safe :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → Sense w → Limpl rp hp rv alo r h v w vlo →
        ∀ res ∈ SetM.run (immediate rp hp rv alo r h v w vlo),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2
          NoNMAC rp hp r_res h_res ∧ Limpl rp hp rv alo r_res h_res v_res w_res vlo_res :=
  sorry

/-- STTT Lemma 1 / repository `acasx.kyx`. -/
theorem immediate_regions_equivalent :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → Sense w →
        (Lexpl rp hp rv alo r h v w vlo ↔ Limpl rp hp rv alo r h v w vlo) := sorry

/-- STTT Theorem 2; the bundled delayed kyx also preserves its implicit region. -/
theorem delayed_safe :
    ∀ rp hp rv alo ad δ ε r h v w vlo d,
      Bounds rp hp rv alo → (0 ≤ ad ∧ 0 ≤ δ ∧ 0 ≤ ε) → Sense w →
      Dimpl rp hp rv alo ad r h v w vlo d →
        ∀ res ∈ SetM.run (delayed rp hp rv alo ad δ ε r h v w vlo d),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2.1
          let d_res := res.2.2.2.2.2
          NoNMAC rp hp r_res h_res ∧
            Dimpl rp hp rv alo ad r_res h_res v_res w_res vlo_res d_res := sorry

/-- STTT Lemma 2, Fig. 5; the explicit predicate is transcribed from the journal. -/
theorem delayed_regions_equivalent :
    ∀ rp hp rv alo ad r h v w vlo d,
      Bounds rp hp rv alo → 0 ≤ ad → Sense w →
        (Dexpl rp hp rv alo ad r h v w vlo d ↔ Dimpl rp hp rv alo ad r h v w vlo d) :=
  sorry

/-- STTT Theorem 3 as supplied in repository `acasxtwosided.kyx`.
Both targets can change; `alo ≤ aup` is required. The archive postcondition is NoNMAC. -/
theorem two_sided_safe :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
      Cimpl rp hp rv alo aup r h v w vlo vup →
        ∀ res ∈ SetM.run (twoSided rp hp rv alo aup r h v w vlo vup),
          let r_res := res.1
          let h_res := res.2.1
          NoNMAC rp hp r_res h_res := sorry

/-- STTT Theorem 4 as supplied in `bounded_implicit.kyx`.
The initial clock is an arbitrary admissible elapsed time, not implicitly zero. -/
theorem bounded_safe :
    ∀ rp hp rv alo aup tl r h v w vlo vup t,
      TwoSidedBounds rp hp rv alo aup → Sense w → (t ≤ tl ∨ tl < 0) →
      CimplBounded rp hp rv alo aup tl t r h v w vlo vup →
        ∀ res ∈ SetM.run (bounded rp hp rv alo aup tl r h v w vlo vup t),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2.1
          let vup_res := res.2.2.2.2.2.1
          let t_res := res.2.2.2.2.2.2
          NoNMAC rp hp r_res h_res ∧ Sense w_res ∧ (t_res ≤ tl ∨ tl < 0) ∧
            CimplBounded rp hp rv alo aup tl t_res r_res h_res v_res w_res vlo_res vup_res :=
  sorry

/-- STTT Theorem 5 / the generated model in `AcasXSafeable.scala`.
This is safety and region preservation; it does not assert nonblocking or escape liveness. -/
theorem safeable_safe :
    ∀ rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → Sense w → (t ≤ tl ∨ tl < 0) →
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx →
        ∀ res ∈ SetM.run (safeable rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t),
          let r_res := res.1
          let h_res := res.2.1
          let v_res := res.2.2.1
          let w_res := res.2.2.2.1
          let vlo_res := res.2.2.2.2.1
          let vup_res := res.2.2.2.2.2.1
          let t_res := res.2.2.2.2.2.2
          NoNMAC rp hp r_res h_res ∧ Sense w_res ∧ (t_res ≤ tl ∨ tl < 0) ∧
            CimplSafeable rp hp rv alo aup tl t_res r_res h_res v_res
              w_res vlo_res vloEx vup_res vupEx := sorry

/-- STTT Proposition 1, Eq. (11); no extra nonzero-speed assumption. -/
theorem horizontal_reduction :
    ∀ rp rx ry rv x y s n,
      HorizontalCoordinates rx ry rv x y s n →
        ∀ res ∈ SetM.run (evolve (horizontalMotion rx ry rv) (fun _ => True) (x, y, s, n)),
          let x_res := res.1
          let y_res := res.2.1
          let s_res := res.2.2.1
          let n_res := res.2.2.2
          (rp ^ 2 < x_res ^ 2 + y_res ^ 2 ↔ rp ^ 2 - n_res ^ 2 < s_res ^ 2) := sorry

end ACASX
