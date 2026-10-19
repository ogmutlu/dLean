"""Domain values and validation, independent of subprocess execution."""

from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path

DEFAULT_CODEX_MODEL = "gpt-6.1-sol"


class BenchmarkError(Exception):
    """An invalid benchmark request or unavailable prerequisite."""


class Agent(StrEnum):
    CODEX = "codex"

    @classmethod
    def parse(cls, value: object) -> "Agent":
        try:
            return cls(value)
        except ValueError:
            raise BenchmarkError(
                f"unknown agent {value!r}; expected codex"
            ) from None


def path_argument(value: object, name: str) -> Path:
    if not isinstance(value, (str, Path)) or not str(value):
        raise BenchmarkError(f"{name} must be a nonempty path")
    return Path(value)


def boolean_argument(value: object, name: str) -> bool:
    if not isinstance(value, bool):
        raise BenchmarkError(f"{name} must be true or false")
    return value


def validate_agent_options(model: object, timeout: object) -> None:
    if model is not None and not isinstance(model, str):
        raise BenchmarkError("model must be a string")
    if (
        isinstance(timeout, bool)
        or not isinstance(timeout, int)
        or timeout <= 0
    ):
        raise BenchmarkError("--timeout requires a positive integer")


@dataclass(frozen=True)
class Problem:
    path: Path

    @property
    def name(self) -> str:
        return self.path.name


@dataclass(frozen=True)
class Workspace:
    path: Path

    @property
    def solution(self) -> Path:
        return self.path / "Solution.lean"


@dataclass(frozen=True)
class AgentOptions:
    model: str | None = None
    timeout: int = 600

    @property
    def effective_model(self) -> str:
        if self.model is not None and self.model != "":
            return self.model
        return DEFAULT_CODEX_MODEL

    def __post_init__(self) -> None:
        validate_agent_options(self.model, self.timeout)


@dataclass(frozen=True)
class JudgeOptions:
    use_systemd: bool = True


@dataclass(frozen=True)
class RunOptions:
    agent: Agent
    agent_options: AgentOptions
    judge_options: JudgeOptions
    skip_judge: bool = False


@dataclass(frozen=True)
class RunResult:
    problem: Problem
    agent: Agent
    model: str | None
    workspace: Workspace
    agent_exit_code: int
    comparator_exit_code: int | None

    @property
    def exit_code(self) -> int:
        if self.comparator_exit_code not in (None, 0):
            return self.comparator_exit_code
        return self.agent_exit_code

    def metadata(self) -> str:
        comparator = self.comparator_exit_code
        return (
            f"problem={self.problem.path}\n"
            f"agent={self.agent.value}\n"
            f"model={self.model or 'default'}\n"
            f"agent_exit_code={self.agent_exit_code}\n"
            "comparator_exit_code="
            f"{comparator if comparator is not None else 'skipped'}\n"
            f"solution={self.workspace.solution}\n"
        )
