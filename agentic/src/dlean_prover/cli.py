"""Fire command adapters for the typed benchmark workflows."""

import shutil
import subprocess
import sys
from datetime import UTC, datetime

import fire  # pyright: ignore

from .agents import run_agent
from .domain import (
    Agent,
    AgentOptions,
    BenchmarkError,
    JudgeOptions,
    RunOptions,
    RunResult,
    boolean_argument,
    path_argument,
)
from .judge import run_comparator
from .process import shell_exit_code
from .workspace import (
    REPO_ROOT,
    create_agent_project,
    create_project,
    init_agent_git,
    load_problem,
    load_workspace,
    new_directory,
)


def finish(status: int) -> None:
    if status:
        raise SystemExit(status)


def prepare(problem: str, output_directory: str | None = None) -> None:
    """Create and build a sandbox with Solution.lean copied from Challenge.lean.

    Args:
        problem: Directory containing Challenge.lean and config.json.
        output_directory: New directory; defaults to ./NAME-sandbox.
    """
    task = load_problem(path_argument(problem, "problem").resolve())
    destination = path_argument(
        output_directory
        if output_directory is not None
        else f"{task.name}-sandbox",
        "output directory",
    ).resolve()
    workspace = create_project(task, destination, initialize_git=True)
    print(workspace.path)


def agent(
    agent: str,
    sandbox: str,
    model: str | None = None,
    timeout: int = 600,
) -> None:
    """Run Codex in a prepared sandbox, saving logs without judging.

    Args:
        agent: codex.
        sandbox: Workspace created by prepare.
        model: Codex model; defaults to gpt-6.1-sol.
        timeout: Positive time limit in seconds, enforced by the harness.
    """
    selected_agent = Agent.parse(agent)
    options = AgentOptions(model, timeout)
    workspace = load_workspace(path_argument(sandbox, "sandbox").resolve())
    status = run_agent(
        workspace,
        REPO_ROOT / ".lake/packages",
        selected_agent,
        options,
        workspace.path / "agent-output.jsonl",
        workspace.path / "agent-stderr.log",
    )
    print(f"\nAgent workspace: {workspace.path}\nAgent exit code: {status}")
    print(f"Solution: {workspace.solution}")
    finish(status)


def judge(
    problem: str,
    solution_file: str,
    output_directory: str | None = None,
    unsafe_no_systemd: bool = False,
) -> None:
    """Check a solution in a fresh project using Lean Comparator.

    Args:
        problem: Directory containing Challenge.lean and config.json.
        solution_file: Submitted Lean file, usually SANDBOX/Solution.lean.
        output_directory: New directory; defaults to ./NAME-judge.
        unsafe_no_systemd: Disable the documented systemd wrapper.
    """
    task = load_problem(path_argument(problem, "problem").resolve())
    solution = path_argument(solution_file, "solution file").resolve()
    if not solution.is_file():
        raise BenchmarkError(f"solution file not found: {solution}")
    options = JudgeOptions(
        not boolean_argument(unsafe_no_systemd, "unsafe-no-systemd")
    )
    destination = path_argument(
        output_directory
        if output_directory is not None
        else f"{task.name}-judge",
        "output directory",
    ).resolve()
    workspace = create_project(task, destination)
    shutil.copy2(solution, workspace.solution)
    finish(run_comparator(workspace, options))
    print(workspace.path)


def run(
    problem: str,
    agent: str,
    model: str | None = None,
    timeout: int = 600,
    output: str | None = None,
    skip_judge: bool = False,
    unsafe_no_systemd: bool = False,
) -> None:
    """Prepare trusted and agent projects,
    run an agent, then judge its solution.

    Args:
        problem: Directory containing Challenge.lean and config.json.
        agent: codex.
        model: Codex model; defaults to gpt-6.1-sol.
        timeout: Positive time limit in seconds, enforced by the harness.
        output: New run directory; defaults to
                benchmark-results/TIMESTAMP-NAME-AGENT.
        skip_judge: Run the agent without invoking Comparator.
        unsafe_no_systemd: Disable the documented systemd
                           wrapper for Comparator.
    """
    task = load_problem(path_argument(problem, "problem").resolve())
    options = RunOptions(
        Agent.parse(agent),
        AgentOptions(model, timeout),
        JudgeOptions(
            not boolean_argument(unsafe_no_systemd, "unsafe-no-systemd")
        ),
        boolean_argument(skip_judge, "skip-judge"),
    )
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    default_output = (
        REPO_ROOT
        / "benchmark-results"
        / f"{stamp}-{task.name}-{options.agent.value}"
    )
    destination = path_argument(
        output if output is not None else default_output, "output directory"
    ).resolve()
    new_directory(destination)
    trusted = create_project(task, destination / "trusted")
    workspace = create_agent_project(trusted, destination / "agent")
    init_agent_git(workspace)
    agent_status = run_agent(
        workspace,
        trusted.path / ".lake/packages",
        options.agent,
        options.agent_options,
        destination / "agent-output.jsonl",
        destination / "agent-stderr.log",
    )
    comparator_status = None
    if not options.skip_judge:
        shutil.copy2(workspace.solution, trusted.solution)
        comparator_status = run_comparator(trusted, options.judge_options)
    result = RunResult(
        task,
        options.agent,
        options.agent_options.effective_model,
        workspace,
        agent_status,
        comparator_status,
    )
    (destination / "result.txt").write_text(result.metadata())
    print(f"\nRun directory: {destination}\nAgent exit code: {agent_status}")
    print(
        "Comparator exit code:"
        f"{comparator_status if comparator_status is not None else 'skipped'}"
    )
    finish(result.exit_code)


def main() -> None:
    arguments = sys.argv[1:]
    if arguments == ["help"]:
        arguments = ["--help"]
    try:
        fire.Fire(  # pyright: ignore
            {"prepare": prepare, "agent": agent, "judge": judge, "run": run},
            command=arguments,
        )
    except BenchmarkError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1) from None
    except subprocess.CalledProcessError as error:
        print(
            f"error: command failed ({error.returncode}): {error.cmd}",
            file=sys.stderr,
        )
        raise SystemExit(shell_exit_code(error.returncode)) from None
    except OSError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1) from None
    except KeyboardInterrupt:
        raise SystemExit(130) from None


if __name__ == "__main__":
    main()
