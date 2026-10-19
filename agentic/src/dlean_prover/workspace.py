"""Prepare sanitized Lean projects and record their trusted source snapshot."""

import hashlib
import os
import shutil
import subprocess
from pathlib import Path

from .domain import BenchmarkError, Problem, Workspace
from .process import capture, checked, note

AGENTIC_ROOT = Path(__file__).resolve().parents[2]
REPO_ROOT = AGENTIC_ROOT.parent
PROJECT_FILES = (
    "dLean.lean",
    "lean-toolchain",
    "lake-manifest.json",
    "config.json",
    "Challenge.lean",
    "Solution.lean",
    "lakefile.toml",
    "AGENTS.md",
    ".gitignore",
    "benchmark-metadata.txt",
)


def load_problem(path: Path) -> Problem:
    if not path.is_dir():
        raise BenchmarkError(f"problem directory not found: {path}")
    for name in ("Challenge.lean", "config.json"):
        if not (path / name).is_file():
            raise BenchmarkError(f"missing {name} in {path}")
    return Problem(path)


def load_workspace(path: Path) -> Workspace:
    required = (
        ".agents/skills/dlean-prover/SKILL.md",
        "AGENTS.md",
        "Challenge.lean",
        "Solution.lean",
        "config.json",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "dLean/Core",
        "dLean/Tactic",
        ".lake/packages",
    )
    for name in required:
        entry = path / name
        if not entry.exists() and not entry.is_symlink():
            raise BenchmarkError(
                f"not a prepared benchmark sandbox; missing {entry}"
            )
    return Workspace(path)


def new_directory(path: Path) -> None:
    if path.exists() or path.is_symlink():
        raise BenchmarkError(f"output already exists: {path}")
    path.mkdir(parents=True)


def source_fingerprint(problem: Problem) -> str:
    paths = [
        str(path.relative_to(REPO_ROOT))
        for directory in ("dLean/Core", "dLean/Tactic")
        for path in (REPO_ROOT / directory).rglob("*.lean")
        if path.is_file() and not path.is_symlink()
    ]
    paths.extend(
        [
            "dLean.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            "agentic/AGENTS.md",
            "agentic/skills/dlean-prover/SKILL.md",
            str(problem.path / "Challenge.lean"),
            str(problem.path / "config.json"),
        ]
    )
    fingerprint = hashlib.sha256()
    for name in sorted(paths, key=os.fsencode):
        digest = hashlib.sha256((REPO_ROOT / name).read_bytes()).hexdigest()
        escaped = name.replace("\\", "\\\\").replace("\n", "\\n")
        prefix = "\\" if escaped != name else ""
        fingerprint.update(os.fsencode(f"{prefix}{digest}  {escaped}\n"))
    return fingerprint.hexdigest()


def write_metadata(problem: Problem, destination: Path) -> None:
    metadata = (
        f"problem={problem.path}\n"
        f"source_fingerprint={source_fingerprint(problem)}\n"
        f"lean_toolchain={(REPO_ROOT / 'lean-toolchain').read_text().strip()}\n"
    )
    commit = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if commit.returncode == 0:
        dirty = bool(capture(["git", "status", "--porcelain"], REPO_ROOT))
        metadata += f"git_commit={commit.stdout.strip()}\ngit_dirty={str(dirty).lower()}\n"
    (destination / "benchmark-metadata.txt").write_text(metadata)


def init_agent_git(workspace: Workspace) -> None:
    if (workspace.path / ".git").exists():
        raise BenchmarkError(
            f"refusing to replace existing Git data in {workspace.path}"
        )
    checked(["git", "init", "-q"], workspace.path)
    checked(["git", "add", ".agents", "dLean", *PROJECT_FILES], workspace.path)
    checked(
        [
            "git",
            "-c",
            "user.name=dLean Benchmark",
            "-c",
            "user.email=benchmark@example.invalid",
            "commit",
            "-qm",
            "Initial sanitized benchmark",
        ],
        workspace.path,
    )


def create_project(
    problem: Problem, destination: Path, initialize_git: bool = False
) -> Workspace:
    packages = REPO_ROOT / ".lake/packages"
    if not (packages / "mathlib").is_dir():
        raise BenchmarkError(
            f"missing trusted dependency cache; run 'lake update && lake exe cache get' in {REPO_ROOT}"
        )
    instructions = AGENTIC_ROOT / "AGENTS.md"
    skill = AGENTIC_ROOT / "skills/dlean-prover"
    for required in (instructions, skill / "SKILL.md"):
        if not required.is_file():
            raise BenchmarkError(
                f"missing benchmark instructions or skill: {required}"
            )
    new_directory(destination)
    for name in ("Core", "Tactic"):
        shutil.copytree(
            REPO_ROOT / "dLean" / name,
            destination / "dLean" / name,
            symlinks=True,
        )
    for name in ("dLean.lean", "lean-toolchain", "lake-manifest.json"):
        shutil.copy2(REPO_ROOT / name, destination / name)
    shutil.copy2(problem.path / "config.json", destination / "config.json")
    for name in ("Challenge.lean", "Solution.lean"):
        shutil.copy2(problem.path / "Challenge.lean", destination / name)
    lakefile = (REPO_ROOT / "lakefile.toml").read_text()
    lakefile += '\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n'
    (destination / "lakefile.toml").write_text(lakefile)
    shutil.copy2(instructions, destination / "AGENTS.md")
    shutil.copytree(
        skill, destination / ".agents/skills/dlean-prover", symlinks=True
    )
    (destination / ".gitignore").write_text(
        "/.lake\n/.tmp\n/agent-output.jsonl\n/agent-stderr.log\n"
    )
    note("Linking the shared, trusted dependency package cache")
    (destination / ".lake").mkdir()
    (destination / ".lake/packages").symlink_to(
        packages, target_is_directory=True
    )
    write_metadata(problem, destination)
    note("Building the trusted challenge snapshot")
    checked(["lake", "build", "Challenge"], destination)
    workspace = Workspace(destination)
    if initialize_git:
        init_agent_git(workspace)
    return workspace


def create_agent_project(source: Workspace, destination: Path) -> Workspace:
    new_directory(destination)
    for name in ("dLean/Core", "dLean/Tactic", ".agents", ".lake/build"):
        shutil.copytree(source.path / name, destination / name, symlinks=True)
    for name in PROJECT_FILES:
        shutil.copy2(source.path / name, destination / name)
    (destination / ".lake/packages").mkdir()
    return Workspace(destination)
