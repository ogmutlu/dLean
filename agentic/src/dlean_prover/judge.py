"""Independent solution checking through Lean Comparator."""

import os
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .domain import BenchmarkError, JudgeOptions, Workspace
from .process import note, resolve_executable, shell_exit_code


@dataclass(frozen=True)
class ComparatorPaths:
    comparator: Path
    lean4export: Path
    landrun: Path


def comparator_paths() -> ComparatorPaths:
    root = os.environ.get("COMPARATOR_ROOT", "")
    comparator = os.environ.get("COMPARATOR_BIN", "")
    lean4export = os.environ.get("COMPARATOR_LEAN4EXPORT", "")
    if root:
        comparator = comparator or str(Path(root) / ".lake/build/bin/comparator")
        lean4export = lean4export or str(
            Path(root) / ".lake/packages/lean4export/.lake/build/bin/lean4export"
        )
    if not comparator:
        raise BenchmarkError("set COMPARATOR_ROOT or COMPARATOR_BIN")
    if not lean4export:
        raise BenchmarkError("set COMPARATOR_ROOT or COMPARATOR_LEAN4EXPORT")
    return ComparatorPaths(
        resolve_executable(comparator),
        resolve_executable(lean4export),
        resolve_executable(os.environ.get("COMPARATOR_LANDRUN", "landrun")),
    )


def run_comparator(workspace: Workspace, options: JudgeOptions) -> int:
    paths = comparator_paths()
    note("Judging Solution.lean with Lean Comparator")
    command = ["lake", "env", str(paths.comparator), "config.json"]
    environment = dict(os.environ)
    if options.use_systemd:
        command = [
            str(resolve_executable("systemd-run")),
            "--user", "--wait", "--pipe", "--collect", "--quiet",
            "--property=RestrictAddressFamilies=~AF_UNIX",
            f"--working-directory={workspace.path}",
            f"--setenv=PATH={os.environ.get('PATH', '')}",
            f"--setenv=COMPARATOR_LANDRUN={paths.landrun}",
            f"--setenv=COMPARATOR_LEAN4EXPORT={paths.lean4export}",
            "--", *command,
        ]
    else:
        note("WARNING: invoking Comparator without the documented systemd hardening")
        environment.update(
            COMPARATOR_LANDRUN=str(paths.landrun),
            COMPARATOR_LEAN4EXPORT=str(paths.lean4export),
        )
    process = subprocess.run(command, cwd=workspace.path, env=environment, check=False)
    return shell_exit_code(process.returncode)
