"""Process execution and live logging without shell command strings."""

import os
import shutil
import signal
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import IO

from .domain import BenchmarkError


def note(message: str) -> None:
    print(f"==> {message}", file=sys.stderr, flush=True)


def resolve_executable(value: str) -> Path:
    if "/" in value:
        executable = Path(value).resolve()
        if not executable.is_file() or not os.access(executable, os.X_OK):
            raise BenchmarkError(f"not executable: {value}")
        return executable
    found = shutil.which(value)
    if found is None:
        raise BenchmarkError(f"required command not found: {value}")
    return Path(found).absolute()


def checked(command: list[str], cwd: Path, env: dict[str, str] | None = None) -> None:
    subprocess.run(command, cwd=cwd, env=env, check=True)


def capture(command: list[str], cwd: Path) -> str:
    return subprocess.run(
        command, cwd=cwd, check=True, text=True, stdout=subprocess.PIPE
    ).stdout.strip()


def shell_exit_code(returncode: int) -> int:
    return returncode if returncode >= 0 else 128 - returncode


def copy_output(source: IO[bytes], terminal: IO[bytes], log: IO[bytes]) -> None:
    while chunk := os.read(source.fileno(), 65536):
        log.write(chunk)
        log.flush()
        terminal.write(chunk)
        terminal.flush()


def logged(
    command: list[str],
    cwd: Path,
    env: dict[str, str],
    stdout_file: Path,
    stderr_file: Path,
) -> int:
    with (
        stdout_file.open("wb") as stdout_log,
        stderr_file.open("wb") as stderr_log,
        subprocess.Popen(
            command,
            cwd=cwd,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        ) as process,
    ):
        assert process.stdout is not None
        assert process.stderr is not None
        with ThreadPoolExecutor(max_workers=2) as readers:
            stdout_reader = readers.submit(
                copy_output, process.stdout, sys.stdout.buffer, stdout_log
            )
            stderr_reader = readers.submit(
                copy_output, process.stderr, sys.stderr.buffer, stderr_log
            )
            try:
                status = process.wait()
            except KeyboardInterrupt:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise
            stdout_reader.result()
            stderr_reader.result()
    return shell_exit_code(status)
