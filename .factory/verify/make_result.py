"""The script of the workflow `verify-trusted` (github-and-ci.md, sections 4.2 and 4.3).

Shipped by the AI Software Factory and run from the trusted checkout of the
default branch. Standard library only. Three commands:

    state   read tasks/<TASK>.yaml from the trusted checkout and compute the
            test state over the files it names (record formats, section 4)
    copy    copy those files from the trusted checkout over the candidate
    result  write result.json in the form factory/result/1

Every value of result.json comes from the trusted checkout, the event or the
run, except `result` and `tests`, which come from the run of the code under test.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ElementTree
from pathlib import Path

BRANCH = re.compile(r"^factory/(TASK-[0-9]{4})/(RUN-[0-9]{8}T[0-9]{6}Z-[0-9a-f]{6})$")
SAFE_PATH = re.compile(r"^(?!/)(?!.*(^|/)\.\.(/|$))[^\s].*$")


class NotExecutable(Exception):
    """The verification cannot be carried out as specified."""


def branch_parts(head_ref):
    match = BRANCH.match(head_ref or "")
    if not match:
        raise NotExecutable("the head branch is not a task branch of the factory")
    return match.group(1), match.group(2)


def _scalar(text):
    text = text.strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in "'\"":
        return text[1:-1]
    return text


def read_list(text, key):
    """The list of strings under a top-level key of a task file.

    Reads the two forms a task uses, `key: [a, b]` and `key:` followed by
    `- a` lines. Anything else is an error: this script does not guess.
    """
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if not line.startswith(key + ":"):
            continue
        rest = line[len(key) + 1:].split(" #", 1)[0].strip()
        if rest.startswith("[") and rest.endswith("]"):
            inner = rest[1:-1].strip()
            return [_scalar(item) for item in inner.split(",")] if inner else []
        if rest:
            raise NotExecutable(f"the field {key} of the task is not a list")
        items = []
        for following in lines[index + 1:]:
            if not following.strip() or following.lstrip().startswith("#"):
                continue
            if not following.startswith((" ", "-")):
                break
            entry = following.strip()
            if not entry.startswith("- "):
                raise NotExecutable(f"the field {key} of the task is not a list of strings")
            items.append(_scalar(entry[2:].split(" #", 1)[0]))
        return items
    raise NotExecutable(f"the task has no field {key}")


def test_files(trusted, task):
    """(acceptance tests, all files of the test state) that the task names, from the trusted checkout."""
    task_file = Path(trusted) / "tasks" / f"{task}.yaml"
    if not task_file.is_file():
        raise NotExecutable(f"tasks/{task}.yaml does not exist on the default branch")
    text = task_file.read_text(encoding="utf-8")
    tests = read_list(text, "acceptance_tests")
    support = read_list(text, "test_support")
    for path in tests + support:
        if not SAFE_PATH.match(path):
            raise NotExecutable(f"the task names the path {path!r}, which is not a path inside the project")
    if not tests:
        raise NotExecutable("the task names no acceptance test")
    return tests, tests + support


def test_state(trusted, paths):
    """The state identifier of the files: the algorithm of record-formats.md, section 4."""
    rows = []
    for path in paths:
        out = subprocess.run(["git", "-C", str(trusted), "ls-tree", "-z", "HEAD", "--", path],
                             capture_output=True, check=True).stdout
        entries = [e for e in out.split(b"\0") if e]
        found = [e for e in entries if e.split(b"\t", 1)[1].decode("utf-8") == path]
        if len(found) != 1:
            raise NotExecutable(f"{path} is not a file at the commit of the default branch")
        mode, kind, blob = found[0].split(b"\t", 1)[0].decode("ascii").split(" ")
        if kind != "blob":
            raise NotExecutable(f"{path} is not a file at the commit of the default branch")
        rows.append((mode, path, blob))
    if len({row[1] for row in rows}) != len(rows):
        raise NotExecutable("a test file is named more than once")
    rows.sort(key=lambda row: row[1].encode("utf-8"))
    listing = "".join(f"{mode}\t{path}\t{blob}\n" for mode, path, blob in rows)
    return "sha256:" + hashlib.sha256(listing.encode("utf-8")).hexdigest()


def command_state(args):
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    task, run_ref = branch_parts(os.environ.get("HEAD_REF"))
    tests, files = test_files(args.trusted, task)
    state = {"task": task, "run_ref": run_ref, "test_state": test_state(args.trusted, files),
             "acceptance_tests": tests, "files": files}
    (work / "state.json").write_text(json.dumps(state), encoding="utf-8")
    (work / "acceptance-tests").write_bytes(b"".join(t.encode("utf-8") + b"\0" for t in tests))
    print(f"task {task}, test state {state['test_state']}")


def command_copy(args):
    state = json.loads((Path(args.work) / "state.json").read_text(encoding="utf-8"))
    trusted, candidate = Path(args.trusted).resolve(), Path(args.candidate).resolve()
    for path in state["files"]:
        target = candidate / path
        folder = candidate
        for part in Path(path).parts[:-1]:
            folder = folder / part
            if folder.is_symlink():          # the candidate is untrusted: never write through its links
                raise NotExecutable(f"{folder.relative_to(candidate)} is a symbolic link in the task branch")
        if target.is_symlink() or target.is_file():
            target.unlink()
        elif target.exists():
            raise NotExecutable(f"{path} is not a file in the task branch")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(trusted / path, target)
    print(f"copied {len(state['files'])} approved test files over the candidate")


def read_junit(path):
    """Counts of a JUnit report, or None if there is no readable report."""
    try:
        root = ElementTree.parse(path).getroot()
    except (OSError, ElementTree.ParseError):
        return None
    suites = [root] if root.tag == "testsuite" else list(root.iter("testsuite"))
    if not suites:
        return None
    counts = {"total": 0, "failed": 0, "errors": 0, "skipped": 0}
    try:
        for suite in suites:
            counts["total"] += int(suite.get("tests", 0))
            counts["failed"] += int(suite.get("failures", 0))
            counts["errors"] += int(suite.get("errors", 0))
            counts["skipped"] += int(suite.get("skipped", 0))
    except ValueError:
        return None
    return counts


def decide(scan_outcome, tests_outcome, pytest_exit, counts):
    """`passed`, `failed` or `not executable` (github-and-ci.md, 4.2, steps 4 to 6).

    A finding of the secret scanner is `failed`. Tests count only if pytest ran
    them and wrote its report: exit code 0 with at least one test that ran and
    no failure is `passed`, exit code 1 is `failed`. Everything else, including
    a project that cannot be installed and a run that collected no test, is
    `not executable`.
    """
    if scan_outcome != "success":
        return "failed" if scan_outcome == "failure" else "not executable"
    if counts is None or pytest_exit is None or tests_outcome not in ("success", "failure"):
        return "not executable"
    ran = counts["total"] - counts["skipped"]
    if pytest_exit == 0 and counts["failed"] == 0 and counts["errors"] == 0 and ran > 0:
        return "passed"
    if pytest_exit == 1 and (counts["failed"] > 0 or counts["errors"] > 0):
        return "failed"
    return "not executable"


def command_result(args):
    work = Path(args.work)
    state = json.loads((work / "state.json").read_text(encoding="utf-8"))
    counts = read_junit(work / "junit.xml")
    try:
        pytest_exit = int((work / "pytest-exit").read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        pytest_exit = None
    result = decide(os.environ.get("SCAN_OUTCOME", ""), os.environ.get("TESTS_OUTCOME", ""), pytest_exit, counts)
    data = {
        "schema": "factory/result/1",
        "repository_id": int(os.environ["REPOSITORY_ID"]),
        "run": {"id": int(os.environ["RUN_ID"]), "attempt": int(os.environ["RUN_ATTEMPT"])},
        "task": state["task"],
        "run_ref": state["run_ref"],
        "pull_request": int(os.environ["PULL_REQUEST"]),
        "implementation_commit": os.environ["HEAD_SHA"],
        "definition_commit": os.environ["DEFINITION_SHA"],
        "test_state": state["test_state"],
        "result": result,
        "environment": {"runner": os.environ.get("RUNNER_IMAGE", "not reported"),
                        "python": ".".join(str(part) for part in sys.version_info[:3])},
        "tests": counts or {"total": 0, "failed": 0, "errors": 0, "skipped": 0},
    }
    Path(args.output).write_bytes((json.dumps(data, indent=2) + "\n").encode("utf-8"))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as handle:
            handle.write(f"result={result}\n")
    print(f"result: {result}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    state = commands.add_parser("state")
    state.add_argument("--trusted", required=True)
    state.add_argument("--work", required=True)
    state.set_defaults(run=command_state)
    copy = commands.add_parser("copy")
    copy.add_argument("--trusted", required=True)
    copy.add_argument("--candidate", required=True)
    copy.add_argument("--work", required=True)
    copy.set_defaults(run=command_copy)
    result = commands.add_parser("result")
    result.add_argument("--work", required=True)
    result.add_argument("--output", required=True)
    result.set_defaults(run=command_result)
    args = parser.parse_args(argv)
    try:
        args.run(args)
    except NotExecutable as exc:
        print(f"not executable: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
