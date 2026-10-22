import dLean.Tactic.OdeDeriv
import Mathlib.Lean.Meta.Simp

/-!
# Automatic Differentiation

This module provides `autodiff`, a tactic that computes the Lie derivative of
a scalar observable along an autonomous ODE and proves the resulting
`HasPrime` goal using `ode_deriv`.
-/

namespace dLean
open Lean Meta Elab Tactic

namespace AutoDiff

private structure Coordinate where
  stateVar : Expr
  tangent : Expr

private def mkRealNat (n : Nat) : MetaM Expr := do
  let real := mkConst ``Real
  let numeral := mkNatLit n
  let instanceType := mkApp2 (mkConst ``OfNat [0]) real numeral
  let inst ← synthInstance instanceType
  pure <| mkApp3 (mkConst ``OfNat.ofNat [0]) real numeral inst

private def mkZero (e : Expr) : MetaM Expr := do
  let type ← inferType e
  let level ← mkFreshLevelMVar
  let inst ← synthInstance (mkApp (mkConst ``Zero [level]) type)
  pure <| mkApp2 (mkConst ``Zero.zero [level]) type inst

private def dependsOn (coordinates : Array Coordinate) (e : Expr) : Bool :=
  coordinates.any fun coordinate => e.containsFVar coordinate.stateVar.fvarId!

private def lastArg (args : Array Expr) (offset : Nat) : MetaM Expr :=
  if offset < args.size then
    pure args[args.size - 1 - offset]!
  else
    throwError "autodiff: malformed application"

private def add (left right : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[left, right]

private def sub (left right : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[left, right]

private def mul (left right : Expr) : MetaM Expr :=
  mkAppM ``HMul.hMul #[left, right]

private def smul (scalar vector : Expr) : MetaM Expr :=
  mkAppM ``HSMul.hSMul #[scalar, vector]

private def inner (left right : Expr) : MetaM Expr :=
  return (← simpOnlyNames [``inner_smul_right, ``inner_zero_left, ``inner_zero_right]
    (← mkAppM ``inner #[mkConst ``Real, left, right])).expr

private partial def powDerivative
    (base dbase : Expr) : Nat → MetaM Expr
  | 0 => mkRealNat 0
  | 1 => pure dbase
  | n + 2 => do
      let exponent := n + 1
      let previous ← mkAppM ``HPow.hPow #[base, mkNatLit exponent]
      add (← mul (← powDerivative base dbase exponent) base) (← mul previous dbase)

private partial def differentiate
    (coordinates : Array Coordinate) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.getAppFn.constName? == some ``Matrix.vecEmpty then
    return e
  if !dependsOn coordinates e then
    return ← mkZero e

  if let some coordinate := coordinates.find? fun coordinate =>
      coordinate.stateVar == e then
    return coordinate.tangent

  let fn := e.getAppFn
  let args := e.getAppArgs
  if let some coordinate := coordinates.find? fun coordinate => coordinate.stateVar == fn then
    if args.any (dependsOn coordinates) then
      throwError "autodiff: state-dependent indices are not supported"
    return (mkAppN coordinate.tangent args).headBeta
  if let .proj typeName 0 struct := fn then
    if typeName == ``WithLp && args.size == 1 then
      let idx := args[0]!
      let dstruct ← differentiate coordinates struct
      return mkApp (.proj ``WithLp 0 dstruct) idx
  if (fn.constName?.map (·.toString.endsWith ".Real.add")).getD false then
    let left ← lastArg args 1
    let right ← lastArg args 0
    return ← match dependsOn coordinates left, dependsOn coordinates right with
      | true, true => add (← differentiate coordinates left) (← differentiate coordinates right)
      | true, false => differentiate coordinates left
      | false, true => differentiate coordinates right
      | false, false => mkZero e
  if (fn.constName?.map (·.toString.endsWith "inner")).getD false then
    let left ← lastArg args 1
    let right ← lastArg args 0
    return ← match dependsOn coordinates left, dependsOn coordinates right with
      | true, true =>
          add
            (← inner left (← differentiate coordinates right))
            (← inner (← differentiate coordinates left) right)
      | true, false => inner (← differentiate coordinates left) right
      | false, true => inner left (← differentiate coordinates right)
      | false, false => mkZero e
  match fn.constName? with
  | some ``HAdd.hAdd =>
      let left ← lastArg args 1
      let right ← lastArg args 0
      match dependsOn coordinates left, dependsOn coordinates right with
      | true, true => add (← differentiate coordinates left) (← differentiate coordinates right)
      | true, false => differentiate coordinates left
      | false, true => differentiate coordinates right
      | false, false => mkZero e
  | some ``HSub.hSub =>
      let left ← lastArg args 1
      let right ← lastArg args 0
      match dependsOn coordinates left, dependsOn coordinates right with
      | true, true => sub (← differentiate coordinates left) (← differentiate coordinates right)
      | true, false => differentiate coordinates left
      | false, true => mkAppM ``Neg.neg #[← differentiate coordinates right]
      | false, false => mkZero e
  | some ``HMul.hMul =>
      let left ← lastArg args 1
      let right ← lastArg args 0
      match dependsOn coordinates left, dependsOn coordinates right with
      | true, true =>
          add
            (← mul (← differentiate coordinates left) right)
            (← mul left (← differentiate coordinates right))
      | true, false => mul (← differentiate coordinates left) right
      | false, true => mul left (← differentiate coordinates right)
      | false, false => mkZero e
  | some ``HSMul.hSMul =>
      let scalar ← lastArg args 1
      let vector ← lastArg args 0
      match dependsOn coordinates scalar, dependsOn coordinates vector with
      | true, true =>
          add
            (← smul scalar (← differentiate coordinates vector))
            (← smul (← differentiate coordinates scalar) vector)
      | true, false => smul (← differentiate coordinates scalar) vector
      | false, true => smul scalar (← differentiate coordinates vector)
      | false, false => mkZero e
  | some ``Neg.neg =>
      mkAppM ``Neg.neg #[← differentiate coordinates (← lastArg args 0)]
  | some ``HPow.hPow =>
      let base ← lastArg args 1
      let exponent ← whnf (← lastArg args 0)
      let .lit (.natVal n) := exponent |
        throwError "autodiff: only powers with a literal natural exponent are supported"
      if n == 2 && base.getAppFn.constName? == some ``Norm.norm then
        let normArg ← lastArg base.getAppArgs 0
        let dNormArg ← differentiate coordinates normArg
        mul (← mkRealNat 2) (← inner normArg dNormArg)
      else
        powDerivative base (← differentiate coordinates base) n
  | some ``WithLp.toLp =>
      let body ← lastArg args 0
      let dbody ← differentiate coordinates body
      pure <| mkApp (mkAppN fn args.pop) dbody
  | some ``WithLp.ofLp =>
      if args.size == 4 then
        let vec ← lastArg args 1
        let idx ← lastArg args 0
        let dvec ← differentiate coordinates vec
        pure <| mkApp (mkApp (mkAppN fn args.pop.pop) dvec) idx
      else
        let vec ← lastArg args 0
        let dvec ← differentiate coordinates vec
        pure <| mkApp (mkAppN fn args.pop) dvec
  | some ``Matrix.vecCons | some ``Fin.cons =>
      let head ← lastArg args 1
      let tail ← lastArg args 0
      let dhead ← differentiate coordinates head
      let dtail ← differentiate coordinates tail
      pure <| mkApp (mkApp (mkAppN fn args.pop.pop) dhead) dtail
  | some ``Real.sin =>
      let argument ← lastArg args 0
      mul (← mkAppM ``Real.cos #[argument]) (← differentiate coordinates argument)
  | some ``Real.cos =>
      let argument ← lastArg args 0
      let sine ← mkAppM ``Real.sin #[argument]
      mul (← mkAppM ``Neg.neg #[sine])
        (← differentiate coordinates argument)
  | _ =>
      if let some unfolded ← unfoldDefinition? e (ignoreTransparency := true) then
        differentiate coordinates (← simpOnlyNames [] unfolded).expr
      else
        throwError
          "autodiff: unsupported state-dependent expression{indentExpr e}\n\
           Supported operations are +, -, *, scalar multiplication, inner products,\n\
           squared norms, PiLp vectors, negation, natural powers, sin, and cos."

private def headDefinition? (e : Expr) : Option Name :=
  e.getAppFn.constName?.filter fun name =>
    name != ``id && name != ``Function.comp

private partial def normalizeRealOperations (e : Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let normalizedArgs ← args.mapM normalizeRealOperations
  let normalized := mkAppN fn normalizedArgs
  match fn.constName? with
  | some name =>
      if name.toString.endsWith ".Real.add" then
        add (← lastArg normalizedArgs 1) (← lastArg normalizedArgs 0)
      else if name.toString.endsWith ".Real.mul" then
        mul (← lastArg normalizedArgs 1) (← lastArg normalizedArgs 0)
      else
        pure normalized
  | none => pure normalized

private def simplifyDefinition (definition : Expr) (e : Expr) : MetaM Expr := do
  match headDefinition? definition with
  | some _ =>
      let some unfolded ← unfoldDefinition? e (ignoreTransparency := true) |
        throwError "autodiff: could not unfold{indentExpr e}"
      normalizeRealOperations (← simpOnlyNames [] unfolded).expr
  | none => normalizeRealOperations (← simpOnlyNames [] e).expr

private partial def withStateVars
    (ty : Expr)
    (k : Expr → Array Expr → (Expr → MetaM (Array Expr)) → MetaM Expr) :
    MetaM Expr := do
  let tyWhnf ← whnf ty
  if tyWhnf.isAppOfArity ``Prod 2 then
    let #[leftType, rightType] := tyWhnf.getAppArgs |
      throwError "autodiff: malformed product state type"
    withStateVars leftType fun leftTuple leftVars leftProject =>
      withStateVars rightType fun rightTuple rightVars rightProject => do
        let tuple ← mkAppM ``Prod.mk #[leftTuple, rightTuple]
        let project (st : Expr) : MetaM (Array Expr) := do
          let fst ← mkAppM ``Prod.fst #[st]
          let snd ← mkAppM ``Prod.snd #[st]
          return (← leftProject fst) ++ (← rightProject snd)
        k tuple (leftVars ++ rightVars) project
  else
    withLocalDeclD `x ty fun x =>
      k x #[x] (fun st => pure #[st])

private partial def extractCoordinates
    (shape odeExpr : Expr) : MetaM (Array Coordinate) := do
  if shape.isAppOfArity ``Prod.mk 4 then
    let shapeArgs := shape.getAppArgs
    let leftShape ← lastArg shapeArgs 1
    let rightShape ← lastArg shapeArgs 0
    let odeWhnf ← whnf odeExpr
    unless odeWhnf.isAppOfArity ``Prod.mk 4 do
      throwError "autodiff: the vector field did not reduce to a product{indentExpr odeWhnf}"
    let odeArgs := odeWhnf.getAppArgs
    let leftOde ← lastArg odeArgs 1
    let rightOde ← lastArg odeArgs 0
    return (← extractCoordinates leftShape leftOde) ++
      (← extractCoordinates rightShape rightOde)
  else
    let odeExpr ←
      if odeExpr.isAppOfArity ``Prod.fst 3 || odeExpr.isAppOfArity ``Prod.snd 3 then
        let arg ← lastArg odeExpr.getAppArgs 0
        if let some unfoldedArg ← unfoldDefinition? arg (ignoreTransparency := true) then
          pure <| mkApp (mkAppN odeExpr.getAppFn odeExpr.getAppArgs.pop) unfoldedArg
        else
          pure odeExpr
      else
        pure odeExpr
    let tangent ← normalizeRealOperations (← simpOnlyNames [] odeExpr).expr
    return #[⟨shape, tangent⟩]

private def symbolicDerivative (vectorField f : Expr) : MetaM Expr := do
  let fType ← whnf (← inferType f)
  let .forallE _ stateType resultType _ := fType |
    throwError "autodiff: expected a scalar state function, got{indentExpr fType}"
  unless ← isDefEq resultType (mkConst ``Real) do
    throwError "autodiff: expected a function returning Real, got{indentExpr resultType}"

  withStateVars stateType fun state vars project => do
    let fBody ← simplifyDefinition f (mkApp f state)
    let odeBody ← simplifyDefinition vectorField (mkApp vectorField state)
    let coordinates ← extractCoordinates state odeBody
    let body ← differentiate coordinates fBody
    let coordinateFunction ← mkLambdaFVars vars body
    withLocalDeclD `st stateType fun st => do
      let projections ← project st
      mkLambdaFVars #[st] (mkAppN coordinateFunction projections).headBeta

-- This is a candidate field for symbolic differentiation, not an assertion that
-- inactive QODE coordinates have derivatives. `ode_deriv` checks every use.
private partial def vectorFieldFromInstance (instanceExpr ode : Expr) : MetaM Expr := do
  let instanceExpr ← instantiateMVars instanceExpr
  match instanceExpr.getAppFn.constName? with
  | some ``ODE => whnf ode
  | some ``QODE => whnf (← mkAppM ``Prod.snd #[ode])
  | some ``product =>
      let args := instanceExpr.getAppArgs
      let left ← vectorFieldFromInstance (← lastArg args 1) (← mkAppM ``Prod.fst #[ode])
      let right ← vectorFieldFromInstance (← lastArg args 0) (← mkAppM ``Prod.snd #[ode])
      let instanceType ← whnf (← inferType instanceExpr)
      let stateType ← lastArg instanceType.getAppArgs 0
      withLocalDeclD `st stateType fun st => do
        let leftState ← mkAppM ``Prod.fst #[st]
        let rightState ← mkAppM ``Prod.snd #[st]
        mkLambdaFVars #[st] (← mkAppM ``Prod.mk #[mkApp left leftState, mkApp right rightState])
  | some ``timeDependentODE =>
      throwError "autodiff: time-dependent vector fields are not yet supported"
  | _ =>
      throwError "autodiff: unsupported Evolvable instance{indentExpr instanceExpr}"

private def autonomousVectorField (semanticOde : Expr) : MetaM Expr := do
  let semanticOde ← instantiateMVars semanticOde
  unless semanticOde.getAppFn.constName? == some ``Evolvable.denotation do
    throwError "autodiff: expected an ODE obtained through Evolvable.denotation"
  let args := semanticOde.getAppArgs
  vectorFieldFromInstance (← lastArg args 1) (← lastArg args 0)

/--
`autodiff` computes and assigns `?f'` in a `HasPrime ode domain f ?f'` goal,
then proves the resulting derivative equation using `ode_deriv`.

It supports autonomous ODEs, QODEs, and their products, with scalar expressions built from
addition, subtraction, multiplication, scalar multiplication, inner products,
squared norms, PiLp vectors, negation, natural powers, sine, and cosine. If the
derivative is already supplied, `autodiff` instead applies `ode_deriv` directly.
Indexed applications must use state-independent indices. Their derivative proofs
require membership in the corresponding active set.
-/
syntax "autodiff" : tactic
syntax "autodiff" " [" term,* "]" : tactic

private def runAutoDiff (definitions : Array (TSyntax `term)) : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    unless target.getAppFn.constName? == some ``HasPrime do
      throwError "autodiff: expected a HasPrime goal, got{indentExpr target}"
    let args := target.getAppArgs
    let semanticOde ← lastArg args 3
    let f ← lastArg args 1
    let fPrime ← lastArg args 0
    match fPrime with
    | .mvar fPrimeGoal =>
        let vectorField ← autonomousVectorField semanticOde
        let derivative ← symbolicDerivative vectorField f
        fPrimeGoal.assign derivative
        dLean.runOdeDeriv definitions
    | _ => dLean.runOdeDeriv definitions

elab_rules : tactic
  | `(tactic| autodiff) => runAutoDiff #[]
  | `(tactic| autodiff [$definitions,*]) => runAutoDiff definitions

end AutoDiff
end dLean
