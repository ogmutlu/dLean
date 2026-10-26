import dLean.Examples.FM11.Model

open dLean

namespace FM11

theorem llc_safe :
    ∀ A b B ε f l x v a,
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → Behind b B x v f l →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          let x_res := res.1
          let v_res := res.2
          Behind b B x_res v_res f l := sorry

theorem glc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (glc A b B ε C x v a),
        let x_res := res.1
        let v_res := res.2
        LaneSafe C b B x_res v_res ∧
        (∀ i ∈ C, BehindLStar C b B x_res v_res i) := sorry

theorem lhc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε C x v a),
        let C_res := res.1
        let x_res := res.2.1
        let v_res := res.2.2
        LaneSafe C_res b B x_res v_res ∧
        (∀ i ∈ C_res, BehindLStar C_res b B x_res v_res i) := sorry

theorem ghc_safe :
    ∀ A b B ε x v a (lanes : Finset Lane) (C : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (C l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes C x v a),
          let C_res := res.1
          let x_res := res.2.1
          let v_res := res.2.2
          ∀ l ∈ lanes, LaneSafe (C_res l) b B x_res v_res ∧
          (∀ i ∈ C_res l, BehindLStar (C_res l) b B x_res v_res i) := sorry

end FM11
