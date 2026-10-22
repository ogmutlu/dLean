import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import dLean.Core.QODE

/-!
# ODE Derivative Tactic

This module provides `ode_deriv`, a tactic for proving scalar `HasPrime` goals
for ordinary ODEs, quantified ODEs, and products of those systems. It derives
the result from their trajectory equations using differentiation rules and
polynomial normalization.
-/

namespace dLean

open Lean Meta Elab Tactic
open scoped RealInnerProductSpace ENNReal

namespace OdeDeriv

theorem hasDerivWithinAt_fst
    {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A × B} {f' : A × B} {interval : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => (f τ).1) f'.1 interval t := by
  simpa using h.hasFDerivWithinAt.fst.hasDerivWithinAt

theorem hasDerivWithinAt_snd
    {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A × B} {f' : A × B} {interval : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => (f τ).2) f'.2 interval t := by
  simpa using h.hasFDerivWithinAt.snd.hasDerivWithinAt

theorem hasDerivWithinAt_prodMk
    {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A} {f' : A} {g : ℝ → B} {g' : B} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => (f τ, g τ)) (f', g') interval t :=
  hf.prodMk hg

theorem hasDerivWithinAt_apply
    {I A : Type} [Finite I] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : ℝ → I → A} {f' : I → A} {interval : Set ℝ} {t : ℝ}
    (index : I) (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => f τ index) (f' index) interval t := by
  let _ := Fintype.ofFinite I
  have hCoordinate :=
    (ContinuousLinearMap.proj index).hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [Function.comp_def] using hCoordinate

-- `Fintype` supplies the PiLp normed-space instances needed to elaborate the statement.
set_option linter.unusedFintypeInType false in
theorem hasDerivWithinAt_piLp_apply
    {I : Type} [Fintype I] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : I → Type} [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace ℝ (A i)]
    {f : ℝ → PiLp p A} {f' : PiLp p A} {interval : Set ℝ} {t : ℝ}
    (index : I) (h : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => f τ index) (f' index) interval t := by
  have hCoordinate :=
    (PiLp.proj (𝕜 := ℝ) p A index).hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [Function.comp_def] using hCoordinate

set_option linter.unusedFintypeInType false in
theorem hasDerivWithinAt_toLp
    {I : Type} [Fintype I] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : I → Type} [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace ℝ (A i)]
    {f : ℝ → ∀ i, A i} {f' : ∀ i, A i} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => WithLp.toLp p (f τ)) (WithLp.toLp p f') interval t := by
  let equiv := (PiLp.continuousLinearEquiv p ℝ A).symm.toContinuousLinearMap
  have hToLp := equiv.hasFDerivAt.comp_hasDerivWithinAt t hf
  simpa [equiv, Function.comp_def] using hToLp

theorem hasDerivWithinAt_vecCons
    {n : ℕ} {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : ℝ → A} {f' : A} {g : ℝ → Fin n → A} {g' : Fin n → A}
    {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => Matrix.vecCons (f τ) (g τ))
      (Matrix.vecCons f' g') interval t :=
  HasDerivWithinAt.finCons (F' := fun _ => A) hf hg

theorem hasDerivWithinAt_toLp_vecCons
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : ℝ → A} {f' : A} {g : ℝ → Fin n → A} {g' : Fin n → A}
    {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => WithLp.toLp p (Matrix.vecCons (f τ) (g τ)))
      (WithLp.toLp p (Matrix.vecCons f' g')) interval t :=
  hasDerivWithinAt_toLp (hasDerivWithinAt_vecCons hf hg)

theorem hasDerivWithinAt_vecEmpty
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {interval : Set ℝ} {t : ℝ} :
    HasDerivWithinAt (fun _ : ℝ => (Matrix.vecEmpty : Fin 0 → A))
      Matrix.vecEmpty interval t :=
  (hasDerivWithinAt_const t interval
    (Matrix.vecEmpty : Fin 0 → A)).congr_deriv (Subsingleton.elim _ _)

theorem hasDerivWithinAt_add_apply
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f g : ℝ → G} {f' g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ + g τ) (f' + g') interval t := by
  with_reducible_and_instances exact hf.add hg

theorem hasDerivWithinAt_sub_apply
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f g : ℝ → G} {f' g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ - g τ) (f' - g') interval t := by
  with_reducible_and_instances exact hf.sub hg

theorem hasDerivWithinAt_smul_apply
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → ℝ} {g : ℝ → G} {f' : ℝ} {g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ • g τ) (f t • g' + f' • g t) interval t := by
  with_reducible_and_instances exact hf.smul hg

theorem hasDerivWithinAt_mul_apply
    {f g : ℝ → ℝ} {f' g' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => f τ * g τ) (f' * g t + f t * g') interval t := by
  with_reducible_and_instances exact hf.mul hg

theorem hasDerivWithinAt_inner_apply
    {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {f g : ℝ → G} {f' g' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t)
    (hg : HasDerivWithinAt g g' interval t) :
    HasDerivWithinAt (fun τ => ⟪f τ, g τ⟫) (⟪f t, g'⟫ + ⟪f', g t⟫) interval t := by
  exact hf.inner ℝ hg

theorem hasDerivWithinAt_norm_sq_apply
    {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {f : ℝ → G} {f' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => ‖f τ‖ ^ 2) (2 * ⟪f t, f'⟫) interval t :=
  hf.norm_sq

theorem hasDerivWithinAt_neg_apply
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → G} {f' : G} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => -f τ) (-f') interval t := by
  with_reducible_and_instances exact hf.neg

theorem hasDerivWithinAt_pow_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) (n : ℕ) :
    HasDerivWithinAt (fun τ => f τ ^ n) (n * f t ^ (n - 1) * f') interval t := by
  with_reducible_and_instances exact hf.pow n

theorem hasDerivWithinAt_sin_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => Real.sin (f τ)) (Real.cos (f t) * f') interval t := by
  with_reducible_and_instances exact hf.sin

theorem hasDerivWithinAt_cos_apply
    {f : ℝ → ℝ} {f' : ℝ} {interval : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' interval t) :
    HasDerivWithinAt (fun τ => Real.cos (f τ)) (-Real.sin (f t) * f') interval t := by
  with_reducible_and_instances exact hf.cos

end OdeDeriv

namespace IndexedDeriv

theorem deriv_fst
    {E₁ E₂ : Type} [IndexedDeriv I E₁] [IndexedDeriv I E₂]
    {active : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv active trajectory rhs interval t) :
    has_deriv active (fun τ => (trajectory τ).1) rhs.1 interval t :=
  h.1

theorem deriv_snd
    {E₁ E₂ : Type} [IndexedDeriv I E₁] [IndexedDeriv I E₂]
    {active : Set I} {trajectory : ℝ → E₁ × E₂} {rhs : E₁ × E₂}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv active trajectory rhs interval t) :
    has_deriv active (fun τ => (trajectory τ).2) rhs.2 interval t :=
  h.2

theorem hasDerivWithinAt_apply
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {active : Set I} {trajectory : ℝ → I → F} {rhs : I → F}
    {interval : Set ℝ} {t : ℝ}
    (h : has_deriv active trajectory rhs interval t)
    (i : I) (hi : i ∈ active) :
    HasDerivWithinAt (fun τ => trajectory τ i) (rhs i) interval t :=
  h i hi

end IndexedDeriv

syntax "ode_deriv_step" : tactic

macro_rules
  | `(tactic| ode_deriv_step) =>
      `(tactic|
        first
        | assumption
        | (apply OdeDeriv.hasDerivWithinAt_add_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sub_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_neg_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_norm_sq_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_pow_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_sin_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_cos_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_smul_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_mul_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_inner_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_fst <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_snd <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_toLp_vecCons <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_toLp <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_vecCons <;> ode_deriv_step)
        | apply OdeDeriv.hasDerivWithinAt_vecEmpty
        | (apply OdeDeriv.hasDerivWithinAt_piLp_apply <;> ode_deriv_step)
        | (apply OdeDeriv.hasDerivWithinAt_apply <;> ode_deriv_step)
        | (solve
            | apply IndexedDeriv.hasDerivWithinAt_apply <;>
                first
                | assumption
                | solve_by_elim [IndexedDeriv.deriv_fst, IndexedDeriv.deriv_snd]
                | simp)
        | apply hasDerivWithinAt_const)

/--
`ode_deriv` proves a scalar `HasPrime` goal for an ODE, QODE, or their product. It automatically
unfolds the observable, proposed derivative, evolution domain, and vector field.
Use `ode_deriv [definitions]` to provide additional definitions or simplification
lemmas when necessary.
-/
syntax "ode_deriv" : tactic
syntax "ode_deriv" " [" term,* "]" : tactic

private def lastArg (args : Array Expr) (offset : Nat) : MetaM Expr :=
  if offset < args.size then
    pure args[args.size - 1 - offset]!
  else
    throwError "ode_deriv: malformed HasPrime goal"

private partial def addHeadDefinition (definitions : Array Name) (e : Expr) : Array Name :=
  match e with
  | .lam _ _ body _ => addHeadDefinition definitions body
  | .letE _ _ _ body _ => addHeadDefinition definitions body
  | .mdata _ inner => addHeadDefinition definitions inner
  | _ =>
      let fn := e.getAppFn
      match fn.constName? with
      | some name =>
          if name == ``And then
            let args := e.getAppArgs
            if args.size ≥ 2 then
              let definitions := addHeadDefinition definitions args[args.size - 2]!
              addHeadDefinition definitions args[args.size - 1]!
            else
              definitions
          else if name == ``Prod.mk then
            let args := e.getAppArgs
            if args[0]!.isAppOfArity ``Set 1 then
              addHeadDefinition definitions args[args.size - 1]!
            else
              let definitions := addHeadDefinition definitions args[args.size - 2]!
              addHeadDefinition definitions args[args.size - 1]!
          else if name == ``Prod.casesOn || name.isInternalDetail then
            let args := e.getAppArgs
            if args.size > 0 then
              addHeadDefinition definitions args[args.size - 1]!
            else
              definitions
          else if name == ``True || name == ``False || name == ``Or ||
              name == ``Eq || name == ``LE.le || name == ``GE.ge ||
              name == ``LT.lt || name == ``GT.gt || name == ``HAdd.hAdd ||
              name == ``HSub.hSub || name == ``HMul.hMul ||
              name == ``HSMul.hSMul || name == ``HPow.hPow ||
              name == ``Neg.neg || name == ``Norm.norm ||
              name == ``inner || name == ``OfNat.ofNat ||
              name == ``Zero.zero || name == ``Prod.fst ||
              name == ``Prod.snd then
            definitions
          else if definitions.contains name then
            definitions
          else
            definitions.push name
      | none =>
          if fn.isLambda then
            addHeadDefinition definitions e.headBeta
          else
            definitions

private def inferredDefinitions : TacticM (Array Name) := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.getAppFn.constName? == some ``HasPrime do
    throwError "ode_deriv: expected a HasPrime goal, got{indentExpr target}"
  let args := target.getAppArgs
  let semanticOde ← lastArg args 3
  let domain ← lastArg args 2
  let f ← lastArg args 1
  let fPrime ← lastArg args 0
  let ode ←
    if semanticOde.getAppFn.constName? == some ``Evolvable.denotation then
      lastArg semanticOde.getAppArgs 0
    else
      pure semanticOde
  let definitions := addHeadDefinition #[] ode
  let definitions := addHeadDefinition definitions domain
  let definitions := addHeadDefinition definitions f
  return addHeadDefinition definitions fPrime

-- Split product systems before specializing time; indexed-coordinate quantifiers
-- inside a QODE must remain available with their active-set premises.
private partial def dynamicsAt (h t ht : Expr) : MetaM Expr := do
  let type ← whnf (← inferType h)
  if type.isAppOfArity ``And 2 then
    let left ← dynamicsAt (← mkAppM ``And.left #[h]) t ht
    let right ← dynamicsAt (← mkAppM ``And.right #[h]) t ht
    mkAppM ``And.intro #[left, right]
  else
    pure <| mkAppN h #[t, ht]

elab "ode_dynamics_at " h:ident t:ident ht:ident " as " name:ident : tactic => do
  let goal ← getMainGoal
  let (_, goal) ← goal.withContext do
    let proof ← dynamicsAt (← elabTerm h none) (← elabTerm t none) (← elabTerm ht none)
    goal.note name.getId proof
  replaceMainGoal [goal]

private partial def derivativeFacts (h : Expr) : MetaM (Array Expr) := do
  let type ← whnf (← inferType h)
  if type.isAppOfArity ``And 2 then
    return (← derivativeFacts (← mkAppM ``And.left #[h])) ++
      (← derivativeFacts (← mkAppM ``And.right #[h]))
  else
    return #[h]

elab "ode_expose_derivatives " h:ident : tactic => do
  let mut goal ← getMainGoal
  let facts ← goal.withContext do derivativeFacts (← elabTerm h none)
  for i in [:facts.size] do
    let (_, next) ← goal.withContext do goal.note (h.getId.appendAfter s!"_{i}") facts[i]!
    goal := next
  replaceMainGoal [goal]

def runOdeDeriv (definitions : Array (TSyntax `term)) : TacticM Unit := do
  let inferred ← inferredDefinitions
  let inferredSimpDefinitions ← inferred.mapM fun definition =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent definition):term)
  let suppliedSimpDefinitions ← definitions.mapM fun definition =>
    `(Lean.Parser.Tactic.simpLemma| $(definition):term)
  let simpDefinitions := inferredSimpDefinitions ++ suppliedSimpDefinitions
  evalTactic (← `(tactic|
    (intro trajectory interval hODE hDomain t ht
     ode_dynamics_at hODE t ht as hSt
     have hDom := hDomain t ht
     simp -failIfUnchanged
       [Function.comp_apply, inner_smul_right, inner_zero_left,
         real_inner_self_eq_norm_sq, $simpDefinitions,*]
       at hSt hDom ⊢
     ode_expose_derivatives hSt
     apply HasDerivWithinAt.congr_deriv <;>
       first
       | ode_deriv_step
       | (clear hODE hDomain hSt
          simp_all -failIfUnchanged
            [Function.comp_apply, inner_smul_right, inner_zero_left,
              real_inner_self_eq_norm_sq, $simpDefinitions,*] <;>
          simp -failIfUnchanged
            [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, Finset.sum_mul, Finset.mul_sum,
              Fin.sum_univ_succ, PiLp.toLp_apply, $simpDefinitions,*] <;>
          ring_nf <;>
          try simp))))

elab_rules : tactic
  | `(tactic| ode_deriv) => runOdeDeriv #[]
  | `(tactic| ode_deriv [$definitions,*]) => runOdeDeriv definitions

end dLean
