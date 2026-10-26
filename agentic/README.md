# Proof-agent benchmark CLI

Run from the repository root with Python 3.11 or newer and uv:

```sh
uv sync --project agentic 
uv run --project agentic --locked dlean-prove help
uv run --project agentic --locked dlean-prove run --help
uv run --project agentic --locked pyright --project .
uv run --project agentic --locked ruff check agentic
uv run --project agentic --locked ruff format agentic
```

The Python entry point and the standalone `prove.sh` shell harness are both available. Python uses
the official `openai-codex` SDK for Codex; the shell harness uses `codex exec`.
Python currently supports only Codex. Claude support remains in `prove.sh`; a Python backend
using the Claude Code SDK is deferred.
Fire exposes only the four benchmark commands.
Relative problem, workspace, and output paths are resolved against the caller's working directory.
The application locates the source repository through its editable uv project installation.

The workspace's VS Code settings use the Ruff extension with the project's uv-managed executable
and configuration. Python files are formatted on save, with safe fixes and import organization on
explicit saves. Ruff targets Python 3.11 and an 80-character line length, matching the Python ruler.

## Commands

```sh
uv run --project agentic --locked dlean-prove prepare PROBLEM [OUTPUT_DIRECTORY]
uv run --project agentic --locked dlean-prove agent AGENT SANDBOX [OPTIONS]
uv run --project agentic --locked dlean-prove judge PROBLEM SOLUTION_FILE [OUTPUT_DIRECTORY] [OPTIONS]
uv run --project agentic --locked dlean-prove run PROBLEM AGENT [OPTIONS]
```

- `prepare` copies a trusted challenge snapshot, builds `Challenge`, and initializes a sanitized
  Git repository. `Solution.lean` initially matches `Challenge.lean`. The default output is
  `./NAME-sandbox`, where `NAME` is the problem directory's basename.
  If the problem includes `Model.lean`, it is copied to `dLean/Examples/NAME/Model.lean`
  and included in the source fingerprint. Challenge and Solution can both import
  `dLean.Examples.NAME.Model` without duplicating the model definitions.
- `agent` runs `codex` in a prepared workspace. It records `agent-output.jsonl` and
  `agent-stderr.log`, streams both logs to the terminal, and returns the agent's exit code.
- `judge` creates a fresh trusted project, copies in the submitted Lean file, and invokes
  Comparator. The default output is `./NAME-judge`.
- `run` builds a trusted project and creates a separate agent project. It runs the agent, copies
  its solution back to the trusted project, and invokes Comparator there. The default output is
  `benchmark-results/TIMESTAMP-NAME-AGENT` in the source repository, using a UTC timestamp.

Output directories must not already exist. Workspaces include source fingerprints, Lean toolchain
information, and the source Git commit/dirty status in `benchmark-metadata.txt`. A complete run
records the problem, agent, model, solution path, and exit codes in `result.txt`. A failed Comparator
takes precedence over the agent's exit code; otherwise the agent's exit code is returned.

The Python Codex runner writes SDK notifications as JSON lines with `method` and `params` fields
to `agent-output.jsonl`; `agent-stderr.log` contains worker diagnostics. These differ from the
native `codex exec --json` events produced by the shell harness. A completed SDK turn returns 0,
a failed turn or SDK error returns 1, and an interrupted turn returns 130. Harness timeouts retain
GNU `timeout` exit codes (124, or 137 if forced termination is needed).

## Options

| Commands | Option | Meaning |
| --- | --- | --- |
| `agent`, `run` | `--model MODEL` | Override the model; defaults to `gpt-6.1-sol`. |
| `agent`, `run` | `--timeout SECONDS` | Positive integer; defaults to 600. |
| `run` | `--output DIRECTORY` | Store the complete run in a new directory. |
| `run` | `--skip-judge` | Run the agent without invoking Comparator. |
| `judge`, `run` | `--unsafe-no-systemd` | Invoke Comparator without the documented systemd wrapper. |

Fire accepts both hyphens and underscores in option names. Put boolean flags last, or give an
explicit value such as `--skip-judge=True`, so a following positional argument is not consumed as
the flag's value. The harness validates integer limits, booleans, paths, and agent names before
starting a workflow.

## Executables and environment

The source checkout must already have its Lean dependencies installed. Workspace preparation
links the trusted `.lake/packages` cache and runs `lake build Challenge`. Agent execution requires
GNU `timeout`, which sends TERM on expiry and KILL after a further 30 seconds. The application
copies build artifacts between trusted and agent projects; the agent never receives reference
`Proof.lean` files or source repository Git history.

| Variable | Meaning |
| --- | --- |
| `CODEX_BIN` | Optional SDK runtime override; otherwise Python uses the SDK's pinned runtime. The shell harness defaults to `codex`. |
| `ELAN_BIN` | Toolchain resolver, default `elan`. |
| `COMPARATOR_ROOT` | Comparator checkout; supplies default Comparator and lean4export locations. |
| `COMPARATOR_BIN` | Explicit Comparator executable; overrides `COMPARATOR_ROOT`. |
| `COMPARATOR_LEAN4EXPORT` | Explicit lean4export executable matching the Lean toolchain. |
| `COMPARATOR_LANDRUN` | Landrun executable, default `landrun`. |

Comparator defaults to the documented `systemd-run --user` wrapper with
`RestrictAddressFamilies=~AF_UNIX`. Its PATH, Landrun path, and lean4export path are explicitly
forwarded to the service. `--unsafe-no-systemd` runs `lake env` directly with those same executable
settings. See the repository README for Comparator setup.

## Agent isolation

Codex runs in the prepared workspace with `TMPDIR=WORKSPACE/.tmp`. The prompt instructs the
agent to read `AGENTS.md`, inspect the local dLean library, edit `Solution.lean`, and check it with
`lake env lean Solution.lean`. The instruction template is copied as `AGENTS.md`;
`skills/dlean-prover` is copied to `.agents/skills/dlean-prover`.

Codex runs with approval disabled and ephemeral threads. Its permission profile grants workspace
writes and read access to minimal system paths, trusted dependencies, its runtime, the Lean
toolchain, and optional local `lean4` and `lean-proof` skills. Tool networking and live web search
are enabled. Its shell PATH contains the resolved toolchain and standard system directories.
The SDK thread does not select a broad sandbox preset; it inherits the custom permission profile.

The Python runner uses a fresh `CODEX_HOME` outside the writable workspace so user configuration,
rules, and history are not loaded. If `auth.json` exists in the original `CODEX_HOME` (or
`~/.codex`), the worker links it into that private temporary directory to reuse file-based login.
The temporary directory is not granted to agent tools and is removed after execution. Existing
API-key environment settings are inherited. Credentials stored only in an OS keyring are not
copied to the isolated home. The shell harness retains its `--ignore-user-config --ignore-rules`
flags and its normal Codex authentication lookup.

The SDK executes in a Python worker under a process-group timeout, so
timeouts terminate the worker and its app-server children. A termination handler also closes the
SDK connection and temporary home during graceful shutdown.

## Python structure

- `domain.py`: immutable domain values, option validation, and result/exit-code decisions.
- `workspace.py`: trusted snapshots, fingerprints, dependency links, and sanitized Git initialization.
- `agents.py`: Codex worker command construction, dependencies, and timeout handling.
- `codex_runner.py`: SDK thread/turn execution, isolated configuration, and Codex permissions.
- `judge.py`: Comparator executable resolution and systemd invocation.
- `process.py`: executable lookup, subprocess execution, and concurrent live log forwarding.
- `cli.py`: Fire adapters and typed workflow orchestration.

The domain module does not launch processes or inspect the filesystem. The Python package is
intended to run from this checkout using uv's editable installation.

VS Code's Pylance extension uses strict checking from the workspace settings. Missing-stub
diagnostics for Fire and the Codex runtime are suppressed only on their import lines.
