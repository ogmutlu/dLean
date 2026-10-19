"""Run the Codex SDK in a worker covered by
the harness's process-group timeout."""

import json
import os
import signal
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from types import FrameType

from codex_cli_bin import bundled_package_dir  # pyright: ignore
from openai_codex import ApprovalMode, Codex, CodexConfig, CodexError
from openai_codex.types import TurnCompletedNotification, TurnStatus
from pydantic import BaseModel

from .agents import PROMPT, toml_table
from .domain import AgentOptions, BenchmarkError, Workspace
from .process import note, resolve_executable


def runtime_paths() -> tuple[str | None, Path]:
    override = os.environ.get("CODEX_BIN")
    if override is None:
        return None, bundled_package_dir().resolve()
    executable = resolve_executable(override)
    entry = executable.resolve()
    runtime = (
        entry.parent.parent
        if str(entry).endswith("/node_modules/@openai/codex/bin/codex.js")
        else entry
    )
    return str(executable), runtime


def sdk_configuration(
    workspace: Workspace,
    packages: Path,
    toolchain_root: Path,
    codex_home: Path,
) -> CodexConfig:
    executable, runtime = runtime_paths()
    permissions = {
        ":minimal": "read",
        str(workspace.path): "write",
        str(packages): "read",
        str(runtime): "read",
        str(toolchain_root): "read",
    }
    for name in ("lean4", "lean-proof"):
        skill = Path.home() / ".codex/skills" / name
        if skill.is_dir():
            permissions[str(skill.resolve())] = "read"
    sandbox_path = f"{toolchain_root / 'bin'}:/usr/local/bin:/usr/bin:/bin"
    shell_environment = (
        'shell_environment_policy={inherit="core",set='
        + toml_table({"PATH": sandbox_path})
        + ",ignore_default_excludes=false}"
    )
    return CodexConfig(
        codex_bin=executable,
        config_overrides=(
            'default_permissions="dlean-benchmark"',
            "permissions.dlean-benchmark.filesystem=" + toml_table(permissions),
            shell_environment,
            "permissions.dlean-benchmark.network.enabled=true",
            'web_search="live"',
        ),
        cwd=str(workspace.path),
        env={"CODEX_HOME": str(codex_home)},
        client_name="dlean_prover",
        client_title="dLean proof-agent benchmark",
    )


def link_authentication(codex_home: Path) -> None:
    source_home = Path(
        os.environ.get("CODEX_HOME", str(Path.home() / ".codex"))
    )
    authentication = (source_home / "auth.json").resolve()
    if authentication.is_file():
        (codex_home / "auth.json").symlink_to(authentication)


def run_codex(
    workspace: Workspace,
    packages: Path,
    toolchain_root: Path,
    options: AgentOptions,
) -> int:
    with TemporaryDirectory(
        prefix="dlean-codex-", dir="/tmp"
    ) as temporary_home:
        codex_home = Path(temporary_home)
        link_authentication(codex_home)
        configuration = sdk_configuration(
            workspace, packages, toolchain_root, codex_home
        )
        with Codex(configuration) as codex:
            thread = codex.thread_start(
                approval_mode=ApprovalMode.deny_all,
                cwd=str(workspace.path),
                ephemeral=True,
                model=options.effective_model,
            )
            turn = thread.turn(PROMPT)
            for event in turn.stream():
                payload = event.payload
                parameters = (
                    payload.model_dump(mode="json", by_alias=True)
                    if isinstance(payload, BaseModel)
                    else payload.params
                )
                print(
                    json.dumps(
                        {
                            "method": event.method,
                            "params": parameters,
                        }
                    ),
                    flush=True,
                )
                if isinstance(event.payload, TurnCompletedNotification):
                    completed = event.payload.turn
                    if completed.error is not None:
                        note(completed.error.message)
                    if completed.status is TurnStatus.completed:
                        return 0
                    return (
                        130 if completed.status is TurnStatus.interrupted else 1
                    )
    raise BenchmarkError("Codex SDK stream ended without a completed turn")


def terminate(_signum: int, _frame: FrameType | None) -> None:
    raise SystemExit(143)


def main() -> None:
    signal.signal(signal.SIGTERM, terminate)
    try:
        if len(sys.argv) != 5:
            raise BenchmarkError(
                "expected workspace, packages, toolchain, and model arguments"
            )
        status = run_codex(
            Workspace(Path(sys.argv[1])),
            Path(sys.argv[2]),
            Path(sys.argv[3]),
            AgentOptions(model=sys.argv[4] or None),
        )
    except (BenchmarkError, CodexError, OSError) as error:
        note(f"Codex SDK failed: {error}")
        raise SystemExit(1) from None
    except KeyboardInterrupt:
        raise SystemExit(130) from None
    raise SystemExit(status)


if __name__ == "__main__":
    main()
