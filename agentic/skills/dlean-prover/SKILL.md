---
name: dlean-prover
description: Model, prove, and maintain dLean hybrid programs using SetM, intrinsic vcgen contracts, differential invariants, and ODE or QODE derivative tactics. Use for dLean modelling and proof work in the library and its clients, not for general Lean theorem proving.
---

# dLean Prover

Use the active checkout's `dLean/Core` and `dLean/Tactic` as the authoritative APIs.
The current examples use `Std.WP`, intrinsic contracts, and inline loop invariants.
Inspect the relevant model and nearby proofs before choosing an invariant or a proof rule.

In the source repository, FM09 demonstrates vector dynamics and phase composition;
FM11 demonstrates quantified car dynamics, changing populations, and lane controllers.
Their `Model.lean`, `Challenge.lean`, and `Proof.lean` files are the reference idioms.
Prepared benchmark workspaces contain the task's model and dLean library, but do not
include reference `Proof.lean` files. Follow the workspace instructions and permitted edit scope.

## Modelling

### Separate the model, challenge, and proof

For examples using the shared-model layout:

- Put state types, mathematical predicates, vector fields, evolution domains, and
  unannotated hybrid programs in `Model.lean`. Keep it independent of admitted challenge theorems.
- Import that model in `Challenge.lean` and state the requested theorems there.
- Import the same model in `Proof.lean`; prove the target theorems independently under
  the same namespace and names. Do not import `Challenge.lean` to obtain model definitions.
- In a benchmark, work in `Solution.lean` as instructed. Its import of the shared model
  replaces copying or redefining the model. Preserve the supplied programs and target statements.

For example, both FM09 theorem files import `dLean.Examples.FM09.Model` and use namespace
`FM09`. `config.json` selects theorem names; the benchmark module names `Challenge` and
`Solution` differ from the repository's qualified module paths. Both benchmark harnesses
copy an optional task `Model.lean` to `dLean/Examples/NAME/Model.lean`, include it in the
trusted source fingerprint, and preserve it in the agent workspace.

### Represent state and predicates directly

Use mathematical types for physical quantities: FM09's `Vec2` is
`EuclideanSpace ℝ (Fin 2)`. Pass components such as `x d y e` as ordinary program arguments,
and bundle them into tuples at evolution boundaries. Prefer readable tuple lambdas in
vector fields and state predicates:

```lean
@[reducible]
def exitReady (x₀ d₀ y₀ e₀ : Vec2) := fun (x, d, y, e) =>
  ∃ lx mx : ℝ, 0 ≤ lx ∧ 0 < mx ∧ x + lx • d = x₀ + mx • d₀ ∧
  ∃ ly my : ℝ, 0 ≤ ly ∧ 0 < my ∧ y + ly • e = y₀ + my • e₀
```

Use named predicates for separation, tangency, stopping distance, or entry conditions.
Keep their arguments and assumptions explicit. Use `noncomputable def` for norm-based real
observables when needed. Do not add state aliases merely to hide tuple projections; reuse
an existing alias when it serves the model, such as FM11's product of car-coordinate functions.

For quantified systems, separate the active population from total coordinate functions.
FM11 uses `C : Finset Car`, `x v a : Car → ℝ`, and `Lane → Finset Car` for lane populations.
Use `Function.update` for individual coordinates and return the updated population after
creation or deletion. Continuous QODE obligations constrain active coordinates only; retain
membership hypotheses for every coordinate used in a differential proof.

### Write hybrid programs with ordinary control flow

- Use `do`, mutable locals, and `for` loops for sequential composition and iteration.
  `let n ← choose ℕ; for _ in [:n] do ...` models any finite number of repetitions,
  including zero. Iterate over `C.toList` for a finite population.
- Use `choose` for unconstrained nondeterministic choices and `chooseS` for constrained ones.
  Use `ensure P` or `unless P do abort` for tests. Keep `<|>` alternatives as program choices.
  Prefer these constructs over set comprehensions encoding an entire controller; retain
  set notation where it expresses a choice constraint or a mathematical set.
- Carry evolving discrete parameters explicitly. FM09's FTRM assigns the newly negotiated
  radius to a mutable `r` and returns that latest radius with the physical state. A shadowed
  local must not accidentally leave later phases or the returned state using the old value.
- Preserve the intended read state when translating simultaneous control into a loop.
  FM11's `ctrl_n` reads each choice from the original `x v a` and accumulates results in
  `a_res`. For a car occupying multiple lanes, choose one acceleration and check that same
  value against every applicable lane controller, as in `ctrl_n_l`.

`SetM` is demonic: safety quantifies over every successful result in `SetM.run`.
An aborted branch has no successful result; an endpoint test can therefore make an endpoint
safety theorem vacuous. An existential successful-run theorem expresses a separate liveness
or feasibility property. Do not replace one of these claims with the other.

### Make continuous phases and safety scope explicit

Define vector fields and evolution domains separately, then use `evolve ode domain`.
FM09 composes two aircraft fields into `flight ω ρ`. FM11 combines the active-car QODE
with a clock as `evolve (motion C, time) (domain ε C)`, starting the clock at zero.
A domain constrains the whole evolution; a following `ensure` constrains only accepted endpoints.

Distinguish final-state safety from safety throughout a phase. For throughout claims,
expose arbitrary stopping times or phase prefixes before trailing tests, as FM09's
`ftrmPrefix` does. State the actual current population and any updated parameters in results.
For a lane invariant, check that nonnegative speeds and distinct positions are explicit
where needed: FM11's `LaneSafe` includes both alongside leader safety. A leader implication
alone may be vacuous. Document such modelling additions separately from claims in the paper;
do not silently add guards, assumptions, or stronger domains to make a proof succeed.

### Keep Comparator target statements stable

When authoring statements selected by `config.json`, name returned components using ordinary
projection bindings in both Challenge and Proof:

```lean
∀ res ∈ SetM.run (llc A b B ε f l x v a),
  let x_res := res.1
  let v_res := res.2
  Behind b B x_res v_res f l
```

Use a named temporary such as `tmp` for a returned full state, and bind the components once
before writing the safety condition. Tuple-pattern `let (x, v) := res` can generate different
auxiliary matcher constants in the two modules because Lean reuses earlier matchers.
Identical source text and definitionally equal types are not sufficient for Comparator's
structural statement comparison. Ordinary projection bindings avoid this matcher issue.

Tuple unpacking remains appropriate inside programs, intrinsic contracts, and helper statements
not selected by the config; FM09's AC helper statements retain that style. When proving a fixed
benchmark, preserve its given statement rather than silently rewriting it for Comparator.

## Proving

### Prefer intrinsic contracts and inline invariants

Keep unannotated programs in the shared model. In the proof file, define annotated counterparts
such as `free'`, `llc'`, or `ftrm'`, using the same program behaviour and proof-only contracts:

```lean
open dLean
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true
```

Put `requires` and `ensures` on the definition, and an inline
`invariant pref suff => ...` immediately before each loop's `do`. Refer to mutable locals
directly in that invariant. Include facts needed for later iterations and phase contracts,
such as speed compatibility, parameter bounds, and the current population's safety.

For example, after registering the continuous step's `freeStep_spec`, FM09 composes it as:

```lean
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
```

The contract generates `free'.spec`, registered as a specification, using `vcgen`.
Discharge residual VCs in `where finally | spec => ...`; use the generated goal names
from the current definition rather than assuming a fixed numbering. Use `given` for
logical parameters occurring only in the contract. They are not available in the program
body; capture a runtime value separately if the inline invariant needs it.

Separate the analytic phase proof from program composition. Prove an ODE/QODE preservation
lemma, expose it as a `Std.WP.Triple` theorem tagged `@[spec]`, then let intrinsic vcgen
compose the phases and loops. If a named wrapper is needed for spec matching, keep it
definitionally equal to the model command. Do not add tests or restrict choices in the wrapper.

Generated contracts and explicitly registered specs are selected automatically at call sites.
Use `#check prog'.spec` or `#print prog'.spec` to inspect the generated theorem. To diagnose
spec selection, put `set_option trace.Elab.Tactic.Do.vcgen true in` before the definition.
Primitive rules for `choose`, `chooseS`, `abort`, `test`, and `evolveSemantic` are already
registered in the library; ordinary assignments do not need custom specs.

### Transfer contracts back to the model program

Check the annotated program against the original with an equality proved by `rfl` when they
are definitionally equal, as in FM11's `llc_eq`, `glc_eq`, and `ghc_eq`. Replacing a continuous
command by an equal wrapper may still allow `rfl`. If it fails, inspect the actual program
bodies and semantics before trying automation.

For a membership-based safety theorem, rewrite the run through that equality when needed,
then apply the contract with `(prog'.spec ...).le_wp hpre res hrun`. Direct application is
also valid when Lean sees the programs as definitionally equal. Alternatively register a
spec on the model program using the annotated counterpart's spec, as in FM09's `ftrm_spec`.
Program equality is distinct from Comparator's structural equality check on theorem types.

After introducing a result, ordinary `let` bindings in the goal may need `dsimp only` before
introducing later quantified variables. FM09's throughout theorem and FM11's GHC theorem
use this to prevent `intro` from naming a local definition instead of the next quantifier.

### Use direct vcgen when an intrinsic counterpart is unsuitable

Use the current `Std.WP` bridge rather than unfolding the set monad:

```lean
intro ... result hrun
apply SetM.of_wp_run_mem hrun
unfold prog
vcgen (errorOnMissingSpec := false) invariants
| inv1 => fun _pref _suff state => invariant parameters state
```

This is a schematic fallback, not the default for new examples. Match `state` to every mutable
local in declaration order; the first two arguments are the consumed and remaining loop elements.
Use one `vcgen` call with invariants, rather than the old `vcgen; intros; vcgen invariants` flow.
`errorOnMissingSpec := false` leaves unsupported calls as WP goals to prove; it does not discharge
them. Prefer a reusable phase spec when possible. Keep legacy `mvcgen`/`Std.Do` adapters confined
to explicitly legacy files.

Avoid globally unfolding `SetM`, its monad instances, or `SetM.run`. Normalize a remaining pure
continuation with `simp only [SetM.wp_pure, binderNameHint]` before applying a phase lemma.
Prefer `apply` over `refine`. If inference fails, first normalize the goal and check its
precondition, domain, and postcondition; use `refine` only when a remaining elaboration problem
requires explicit holes.

### Prove continuous preservation with differential rules

Evolution statements use `pre [[evolve ode domain]] post`. Choose the rule matching the argument:

- `dW`: obtain the postcondition from the evolution domain.
- `dC (cut := ...)`: prove a preserved fact, then add it to the domain for the remaining goal.
- `dIeq`, `dIle`, `dIlt`, `dIge`, `dIgt`: preserve a scalar observable's equality to zero,
  nonpositivity, negativity, nonnegativity, or positivity, respectively.
- `Ensures.nondet_choice`: prove both alternatives of a continuous nondeterministic choice.
- `Ensures.iff_run`: move between a preservation statement and explicit run membership.

Build a mathematical invariant strong enough for the phase postcondition and the next phase.
Use named observables when controlled unfolding clarifies differentiation or arithmetic.
For nonlinear geometry or reachability, use explicit trajectories and semantic derivative
arguments where the differential invariant rules do not express the needed claim.

For ordinary ODEs and simultaneous products, `autodiff` computes scalar Lie derivatives for
supported arithmetic, literal natural powers, inner products, trigonometry, and function-coordinate
applications.
Use `ode_deriv [definitions]` for explicit derivatives or additional unfolding. For quantified
ODEs of shape `Set I × (F → F)`, use `ode_deriv` and supply the relevant active-index membership
facts. Inspect current `HasPrime`, `Evolvable`, and `IndexedDeriv` instances when a derivative
cannot be obtained; inactive coordinates do not automatically have the active ODE's derivative.

Finish with `simp`, `simp_all`, or `grind [definitions]` for structural facts. State missing sign
or geometric facts with `have` before `linarith` or `nlinarith`; use `ring_nf` for polynomial
normalization. Keep these mathematical obligations separate from the loop-composition VCs.

## Verification

Rebuild changed model dependencies before checking importing files; a standalone
`lake env lean Proof.lean` can otherwise read stale imported `.olean` files. Use targeted
`lake build` commands for the affected model, challenge, and proof modules, and check
`Solution.lean` in the prepared benchmark workspace.

Preserve target names, assumptions, programs, and postconditions. Ensure the target proofs and
their dependencies use no admitted challenge theorem or forbidden axiom. Read `config.json` to
identify Comparator targets. A successful Lean build, a source-text comparison, or a check of
definitional equality alone does not establish Comparator acceptance. Report a full Comparator
pass only after it actually runs successfully; distinguish it from local structural type checks.
