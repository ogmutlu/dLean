---
name: dlean-prover
description: Prove and maintain dLean hybrid-program theorems using SetM weakest preconditions, vcgen loop invariants, differential cuts and invariants, and ODE or QODE derivative tactics. Use for proof work in the dLean library and its clients, not for general Lean theorem proving.
---

# dLean Prover

Prove or maintain the requested theorem in the style supported by the active dLean checkout. This
skill supplements general Lean skills with dLean-specific semantics, proof rules, and `vcgen`
patterns.

Before proving, inspect the relevant modules under `dLean/Core` and `dLean/Tactic`; they are the
authoritative APIs. Inspect nearby dLean examples when they are available, especially when the task
asks for the project's established proof style. Do not carry API assumptions across dLean
checkouts.

## Prefer contracts and inline invariants for new examples

Enable `experimental.vcgen` and `experimental.intrinsic`. State `requires` and `ensures` clauses
on a program definition and place `invariant pref suff => ...` before the loop's `do` keyword.
The invariant refers to mutable locals directly. Prove residual contract VCs in
`where finally | spec => ...`; the generated `prog.spec` is registered as a specification.
For `SetM`, apply `(prog.spec ...).le_wp hpre result hrun` to recover a membership-based safety
claim. See the current `Proof.lean` examples for compiled patterns.

Use `given` for logical parameters that occur only in the contract. Such parameters are not
available inside the program body; BouncingBall's inline invariant uses the original height
`x0`, while its contract quantifies over the logical upper bound `H`.

Register a `Std.WP.Triple` spec for each continuous-step wrapper, using the analytic preservation
lemma to prove it. This lets the automatically generated contract proof use `vcgen` without
`errorOnMissingSpec := false`.

The `ProofMVCGen.lean` variants preserve the original tactic workflow. They explicitly import
`dLean.Core.SemanticsLegacy` and use `dLean.Legacy.SetM.of_wp_run_mem`. Keep that adapter separate
from new `Std.WP` contract proofs.

## Read the program as demonic nondeterminism

`SetM` represents all possible results of a computation. Safety therefore means that the
postcondition holds for every member of `SetM.run`.

When a theorem is stated using membership in `SetM.run`, use the existing WP bridge rather than
unfolding the set monad:

```lean
intro ... result hrun
apply SetM.of_wp_run_mem hrun
unfold prog
vcgen (errorOnMissingSpec := false)
```

The target is now a weakest-precondition obligation. Avoid globally unfolding `SetM`, its monad
instances, or `SetM.run`: doing so loses the abstraction on which `vcgen` and the registered specs
operate.

The library already registers `[spec]` rules for:

- `choose`: prove the continuation for every chosen value;
- `chooseS`: prove it for every member of the chosen set;
- `abort`: no successful result exists;
- `test`: assume the tested proposition;
- `evolveSemantic`: prove the continuation for every permitted evolution.

These theorems are normally used implicitly by `vcgen`; their absence from the proof script is
expected. Ordinary mutable bindings and assignments do not need custom specs.

## Build the mathematical invariant before running the loop proof

Identify a predicate strong enough both to survive one iteration and to imply the final safety
claim. Define it as a named `@[simp] def` when controlled unfolding will help arithmetic and
structural simplification.

First prove focused helper theorems for the continuous commands. Keep `vcgen` for imperative
composition and use dLean's differential rules for evolution. This separates program VCs from the
mathematics of the invariant.

## State the `vcgen` loop invariant with the generated state shape

Use `Std.WP` and enable the experimental tactic, then generate the loop obligations in one call:

```lean
open Std.WP
set_option experimental.vcgen true

unfold prog
vcgen (errorOnMissingSpec := false) invariants
| inv1 => fun _pref _suff state => invariant parameters state
```

The first two invariant arguments are the consumed and remaining elements. Match `state` to all
mutable locals in declaration order; destructured bindings produce tuples.

`errorOnMissingSpec := false` leaves unsupported continuous commands as WP obligations for the
mathematical preservation helpers. This is intentional: prove those obligations rather than
unfolding the ODE semantics. The `evolveSemantic` spec is registered, but `evolve` wrappers and
nondeterministic unions need not be unfolded by the tactic.

Use the generated `vc1`, `vc2`, etc. names from the current goal. In the current examples the
initial-state VC comes first, the final postcondition second, and the loop-body VCs follow.
The tactic already introduces loop and choice parameters; do not repeat the old two-stage
`vcgen; intros; vcgen invariants` pattern.

Before applying a continuous-preservation helper, normalize pure continuations:

```lean
simp only [SetM.wp_pure, binderNameHint]
refine continuous_preserves ... _ ?_
-- establish the helper's precondition from the loop invariant and branch facts
```

Use `refine helper ... ?_` when `apply` unfolds the proposition-based WP too far. Similarly,
`refine dC (cut := cutPredicate) ?_ ?_` preserves the intended two differential-cut obligations.

## Prove evolution preservation with dLean rules

Evolution statements use `Ensures` notation:

```lean
pre [[evolve ode domain]] post
```

Use the rules according to the mathematical argument:

- `dW`: derive the postcondition directly from the evolution domain;
- `dC (cut := cutPredicate)`: establish a fact along the evolution, then add it to the domain for
  the remaining proof;
- `dIeq`, `dIle`, `dIlt`, `dIge`, `dIgt`: preserve respectively equality, nonpositive, negative,
  nonnegative, or positive scalar observables;
- `Ensures.nondet_choice`: prove both sides of `p ∪ q`;
- `Ensures.iff_run`: switch to explicit initial/final states when lifting a pointwise preservation
  theorem through a quantified invariant.

For a nondeterministic continuous command, prove each ODE once and compose them:

```lean
apply Ensures.nondet_choice
· exact left_evolution_preserves ...
· exact right_evolution_preserves ...
```

## Choose the derivative tactic that matches the ODE representation

For ordinary autonomous vector fields:

- `autodiff` computes the scalar Lie derivative and proves the `HasPrime` goal;
- `autodiff` supports `+`, `-`, multiplication, scalar multiplication, inner products, negation,
  literal natural powers, `Real.sin`, and `Real.cos`;
- if the derivative function is supplied explicitly, use `ode_deriv` or let `autodiff` delegate to
  it;
- pass extra unfolding lemmas as `ode_deriv [definitions]` when inference does not normalize an
  observable or vector field.

For quantified ODEs represented by `Set I × (F → F)`:

- use `qode_deriv` on `HasPrime` goals;
- provide the named gap, projection, and motion definitions needed for simplification, for example
  `qode_deriv [vGap', motion]`;
- the tactic obtains coordinate derivatives only for active indices, so retain and supply index
  membership facts such as `i ∈ active` and `j ∈ active`.

Both derivative tactics unfold the ODE, domain, observable, and proposed derivative automatically.
Add explicit definitions only when the current goal shows that further unfolding is required.

## Finish VCs in the local proof style

- Use `simp only [SetM.wp_pure]` when a generated VC still contains a nested pure WP before applying an
  `Ensures` helper.
- Use `simp`, `simp_all`, or `grind [definitions]` to expose tuple projections, domains, record-free
  state updates, and invariant structure.
- Name non-obvious arithmetic or geometric facts with `have` before calling `linarith` or
  `nlinarith`.
- In the final postcondition VC, unpack only the invariant information needed to show the returned
  value is safe.

## Diagnose by layer

- If `vcgen` stops at a primitive, inspect its `[spec]` theorem in `dLean/Core/Semantics.lean` and
  ensure the primitive has not been hidden behind an opaque local definition.
- If a loop invariant pattern does not elaborate, inspect the generated product state in the
  invariant goal; include every mutable local and both list arguments.
- If `apply` fails after `vcgen`, first normalize (`simp [SetM.wp_pure]`); then compare the helper theorem's
  `Ensures` precondition with the current invariant.
- If `autodiff` reports an unsupported expression or ODE, provide an explicit derivative and use
  `ode_deriv`, or prove `HasPrime` from the semantic derivative assumptions.
- If `qode_deriv` cannot find a coordinate derivative, check both that the state is built from
  supported function/product `IndexedDeriv` instances and that the coordinate is in the active set.
- If arithmetic automation stalls, simplify the named observable and derivative, normalize with
  `ring_nf`, then state the missing sign fact explicitly.

