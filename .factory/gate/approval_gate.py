# Shipped by the AI Software Factory. Protected content of the project: it changes
# only through a change to the default branch that is itself verified and approved.
#
# This file is a copy of the module factory.merge_rule of the factory, written by
# tools/make_gate_script.py. The job `approval-gate` runs it; the core runs the
# module. Do not edit it here.
#
"""The rule for a merge: one rule, one implementation.

Specifications: docs/03-architecture/spec/github-and-ci.md, section 6.2, steps 3 to 7;
record formats, section 6, "Rule for a merge"; ADR-0004; ADR-0005; ADR-0006.

This module decides whether a change may be merged. It is used in two places:

    the core            before a merge (factory.merge), with the stored bundle
                        and trusted root of the evidence
    `approval-gate`     in the project, as the copy `.factory/gate/approval_gate.py`
                        on the default branch, with the attestation asked online

Both run this very text, so both decide the same way. For that reason the
module uses the standard library and PyYAML only and imports nothing else of
the factory. `tools/make_gate_script.py` writes the copy; a test fails if the
copy differs.

What it trusts, and where it takes it from:

    list of signers, approvers     the default branch (`trusted_dir` at `trusted_ref`)
    head of the default branch     the same checkout
    head of the pull request       the caller: the event of the gate, or the pull request
    approval, rejection            a commit of the records branch signed with a human
                                   key of an approver
    approved test state            the approval of states, signed by a human, that the
                                   work order of the evidence starts from
    result of the verification     `result.json` with its attestation, verified with `gh`
    attempts of the verification   the runs of `verify-trusted`, asked through `gh`

The evidence record and the work order are signed with the recording key only.
Nothing is taken from them without a second source: the result file must carry
an attestation of `verify-trusted` of this repository, and the test state must
be the one a human approved. A stolen recording key therefore passes nothing.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml

VERIFY_WORKFLOW = "verify-trusted.yml"
VERIFY_WORKFLOW_PATH = f".github/workflows/{VERIFY_WORKFLOW}"
GH_MINIMUM = (2, 102, 0)
FRAME_PATH = ".factory/frame.yaml"
EVIDENCE_FILES = ("bundle.jsonl", "evidence.yaml", "result.json", "trusted_root.jsonl")

ROLE_HUMAN, ROLE_FACTORY = "human", "factory"
_ROLE_SUFFIX = {"@role-human": ROLE_HUMAN, "@role-factory": ROLE_FACTORY}
ROLE_OF_KIND = {"approval": ROLE_HUMAN, "rejection": ROLE_HUMAN, "decision": ROLE_HUMAN,
                "workorder": ROLE_FACTORY, "run": ROLE_FACTORY, "evidence": ROLE_FACTORY, "blocker": ROLE_FACTORY}

_COMMIT = re.compile(r"[0-9a-f]{40}")
_ID = r"\d{8}T\d{6}Z-[0-9a-f]{6}"
_PATHS = (
    ("approval", re.compile(rf"^approvals/states/(APR-{_ID})\.yaml$")),
    ("approval", re.compile(rf"^approvals/changes/[0-9a-f]{{40}}/(APR-{_ID})\.yaml$")),
    ("rejection", re.compile(rf"^rejections/changes/[0-9a-f]{{40}}/(REJ-{_ID})\.yaml$")),
    ("workorder", re.compile(rf"^workorders/(WO-{_ID})\.yaml$")),
    ("run", re.compile(rf"^runs/(RUN-{_ID})\.yaml$")),
    ("blocker", re.compile(rf"^blockers/(BLK-{_ID})\.yaml$")),
    ("decision", re.compile(rf"^decisions/(DEC-{_ID})\.yaml$")),
)
_EVIDENCE_PATH = re.compile(rf"^evidence/(EV-{_ID})/evidence\.yaml$")
_GOOD_SIGNATURE = re.compile(r'^Good "git" signature for (\S+) with \S+ key \S+\s*$', re.MULTILINE)
_KEY_TYPE = re.compile(r"^(ssh-|ecdsa-|sk-)")
_FILE_MODE = "100644"


class GitHubError(Exception):
    """GitHub, or its command line, did not do what was asked."""


class RuleError(Exception):
    """Something the rule relies on cannot be trusted: the records branch, the list of signers, the frame."""


@dataclass(frozen=True)
class Entry:
    """One record of the records branch, with the commit that added it and the signer of that commit."""
    kind: str
    id: str
    path: str
    commit: str
    signer: str
    data: dict[str, Any]


@dataclass(frozen=True)
class Attempts:
    """The attempts of all runs of `verify-trusted` named for one pull request and head."""
    state: str                                        # "none", "in progress" or "completed"
    attempts: tuple[tuple[int, int, str], ...] = ()   # (run, attempt, conclusion), completed ones
    waiting: tuple[int, ...] = ()                     # runs with an attempt that has not completed
    run_id: int = 0                                   # the latest run
    attempt: int = 0                                  # its latest attempt
    url: str = ""

    @property
    def passed(self) -> bool:
        """The rule on attempts: every completed attempt of every run succeeded."""
        return self.state == "completed" and bool(self.attempts) and all(c == "success" for _, _, c in self.attempts)


@dataclass(frozen=True)
class Decision:
    """What the rule says for one head. `reasons` is empty exactly if it passed."""
    passed: bool
    reasons: tuple[str, ...] = ()
    approval: str | None = None
    evidence: str | None = None


# ----------------------------------------------------------------------- git

def _git(folder: Path | str, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(folder), *args], env=dict(os.environ, LC_ALL="C"),
                          stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def _text(raw: bytes) -> str:
    return raw.decode("utf-8", errors="replace").strip()


def _show(folder: Path | str, commit: str, path: str) -> bytes:
    result = _git(folder, "show", f"{commit}:{path}")
    if result.returncode != 0:
        raise RuleError(f"{path} cannot be read at commit {commit}")
    return result.stdout


# ------------------------------------------------------------------- signers

def role_of(principal: str) -> str:
    """Role of a principal, from its suffix. Raises ValueError for any other principal."""
    for suffix, role in _ROLE_SUFFIX.items():
        if principal.endswith(suffix) and len(principal) > len(suffix):
            return role
    raise ValueError(f"principal {principal!r} ends with neither @role-human nor @role-factory")


def parse_signers(text: bytes) -> dict[str, str]:
    """allowed_signers -> {base64 public key: principal}. Strict: one principal per line, with a role, no pattern."""
    result: dict[str, str] = {}
    try:
        lines = text.decode("utf-8").splitlines()
    except UnicodeDecodeError:
        raise ValueError("is not valid UTF-8") from None
    for number, line in enumerate(lines, start=1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        tokens = line.split()
        at = next((i for i, t in enumerate(tokens) if i >= 1 and _KEY_TYPE.match(t)), None)
        if at is None or at + 1 >= len(tokens):
            raise ValueError(f"line {number}: no public key found")
        principal, options, key = tokens[0], tokens[1:at], tokens[at + 1]
        if any(c in principal for c in ",*?!"):
            raise ValueError(f"line {number}: exactly one principal without a pattern is allowed, not {principal!r}")
        for option in options:
            if not option.startswith("namespaces="):
                raise ValueError(f"line {number}: the option {option!r} is not allowed")
        try:
            role_of(principal)
        except ValueError as exc:
            raise ValueError(f"line {number}: {exc}") from None
        if key in result and result[key] != principal:
            raise ValueError(f"line {number}: the same key is listed for {result[key]} and {principal}")
        result[key] = principal
    if not result:
        raise ValueError("names no signer")
    return result


# ------------------------------------------------------------ records branch

def read_records(records_dir: Path | str, ref: str, signers_file: Path | str, approvers: tuple[str, ...]) -> list[Entry]:
    """Check the whole records branch and return its records, oldest first (section 6.2, step 3).

    Every commit has exactly one parent, the first one none. Every commit only
    adds files, with rename detection off, and adds exactly one record. Every
    commit carries a good signature of a key on the list of signers, and the
    role of that key is the role that writes this kind of record; a human
    signer must be an approver. Raises RuleError with the commit and the reason.
    """
    listed = _git(records_dir, "rev-list", "--topo-order", "--reverse", "--parents", ref)
    if listed.returncode != 0:
        raise RuleError(f"the records branch cannot be read: {_text(listed.stderr) or 'no such reference'}")
    entries: list[Entry] = []
    seen: dict[str, str] = {}
    for index, line in enumerate(_text(listed.stdout).splitlines()):
        commit, *parents = line.split()
        if index == 0 and parents:
            raise RuleError(f"records commit {commit}: the first commit of the branch must have no parent")
        if index > 0 and len(parents) != 1:
            raise RuleError(f"records commit {commit}: has {len(parents)} parents; every commit must have exactly one")
        try:
            entry = _check_commit(records_dir, commit, index == 0, signers_file, approvers)
        except RuleError as exc:
            raise RuleError(f"records commit {commit}: {exc}") from None
        if entry is None:
            continue
        if entry.id in seen:
            raise RuleError(f"records commit {commit}: the identifier {entry.id} was already used in commit {seen[entry.id]}")
        seen[entry.id] = commit
        entries.append(entry)
    if not listed.stdout.strip():
        raise RuleError("the records branch has no commit")
    return entries


def _check_commit(records_dir: Path | str, commit: str, first: bool, signers_file: Path | str,
                  approvers: tuple[str, ...]) -> Entry | None:
    raw = _git(records_dir, "diff-tree", "--no-renames", "-r", "--root", "--no-commit-id", "-z", commit)
    if raw.returncode != 0:
        raise RuleError(f"its changes cannot be read: {_text(raw.stderr)}")
    fields = raw.stdout.decode("utf-8", errors="surrogateescape").split("\0")
    added: list[str] = []
    for meta, path in zip(fields[0::2], fields[1::2]):
        _, new_mode, _, _, status = meta.lstrip(":").split(" ")
        if status != "A":
            raise RuleError(f"changes {path} (status {status}); a commit may only add files")
        if new_mode != _FILE_MODE:
            raise RuleError(f"adds {path} with mode {new_mode}; only regular files ({_FILE_MODE}) are allowed")
        added.append(path)
    if not added:
        raise RuleError("adds no file")

    verified = _git(records_dir, "-c", "gpg.format=ssh", "-c", f"gpg.ssh.allowedSignersFile={signers_file}",
                    "-c", "gpg.minTrustLevel=fully", "verify-commit", commit)
    output = _text(verified.stderr + b"\n" + verified.stdout)
    match = _GOOD_SIGNATURE.search(output)
    if verified.returncode != 0 or not match:
        detail = output.splitlines()[0] if output else "the commit is not signed"
        raise RuleError(f"has no good signature of a permitted signer: {detail}")
    principal = match.group(1)
    try:
        role = role_of(principal)
    except ValueError as exc:
        raise RuleError(str(exc)) from None

    if first:
        if added != ["README.md"]:
            raise RuleError("the first commit of the branch must add only README.md")
        if role != ROLE_FACTORY:
            raise RuleError(f"the first commit must be signed with the recording key, not by {principal}")
        return None

    kind, record_path = _record_of(added)
    try:
        data = yaml.safe_load(_show(records_dir, commit, record_path).decode("utf-8"))
    except (yaml.YAMLError, UnicodeDecodeError):
        raise RuleError(f"{record_path} is not valid YAML") from None
    if not isinstance(data, dict) or not isinstance(data.get("id"), str):
        raise RuleError(f"{record_path} is not a record")
    if data.get("schema") != f"factory/{kind}/1":
        raise RuleError(f"{record_path}: holds the schema {data.get('schema')}, but the path is that of kind {kind}")
    name = record_path.split("/")[1] if kind == "evidence" else Path(record_path).stem
    if name != data["id"]:
        raise RuleError(f"{record_path}: the identifier {data['id']} does not fit the path")
    if kind in ("approval", "rejection"):
        problem = _cover_problem(kind, record_path, data)
        if problem:
            raise RuleError(f"{record_path}: {problem}")

    if role != ROLE_OF_KIND[kind]:
        raise RuleError(f"{record_path}: a record of kind {kind} must be signed with a key of role "
                        f"{ROLE_OF_KIND[kind]}, but the commit is signed by {principal}")
    if role == ROLE_HUMAN:
        if data.get("by") != principal:
            raise RuleError(f"{record_path}: field 'by' is {data.get('by')}, but the commit is signed by {principal}")
        if principal not in approvers:
            raise RuleError(f"{record_path}: {principal} is not an approver in the frame of the project")
    elif data.get("by") != "factory":
        raise RuleError(f"{record_path}: field 'by' is {data.get('by')}, but the commit is signed with the recording key")
    return Entry(kind, data["id"], record_path, commit, principal, data)


def _record_of(added: list[str]) -> tuple[str, str]:
    """Kind and record file of the one record a commit adds."""
    if len(added) == 1:
        for kind, pattern in _PATHS:
            if pattern.match(added[0]):
                return kind, added[0]
        raise RuleError(f"adds {added[0]}, which is not the path of a record")
    folders = {p.rsplit("/", 1)[0] for p in added if "/" in p}
    names = tuple(sorted(p.rsplit("/", 1)[-1] for p in added))
    if len(folders) == 1 and len(added) == len(EVIDENCE_FILES) and names == EVIDENCE_FILES:
        record_path = f"{folders.pop()}/evidence.yaml"
        if _EVIDENCE_PATH.match(record_path):
            return "evidence", record_path
    raise RuleError(f"adds {len(added)} files; a commit must add exactly one record: "
                    "one file, or one evidence folder with its four files")


def _cover_problem(kind: str, record_path: str, data: dict[str, Any]) -> str | None:
    """Why what an approval or a rejection covers does not fit its path, or None."""
    covers = data.get("covers")
    if not isinstance(covers, list) or not covers or not all(isinstance(c, dict) for c in covers):
        return "has no entries in 'covers'"
    under_commit = record_path.split("/")[1] == "changes"
    is_change = covers[0].get("kind") == "change"
    if under_commit != is_change:
        return "what it covers does not fit the folder it lies in"
    if is_change:
        if len(covers) != 1:
            return "must cover exactly one change"
        if record_path.split("/")[2] != covers[0].get("commit"):
            return f"lies under the commit {record_path.split('/')[2]}, but names the commit {covers[0].get('commit')}"
    elif kind == "rejection":
        return "a rejection must cover a change"
    return None


# -------------------------------------------------- verification on GitHub

def run_name(pull_request: int, head: str) -> str:
    """The name `verify-trusted` gives its run for a pull request and its head (section 4.2)."""
    return f"verify-trusted pr-{pull_request} {head}"


def signer_identity(repo: str, default_branch: str) -> str:
    """The exact identity of the workflow that may sign a result file (section 6.1, step 3)."""
    return f"https://github.com/{repo}/{VERIFY_WORKFLOW_PATH}@refs/heads/{default_branch}"


def attempts_of(gh, pull_request: int, head: str) -> Attempts:
    """Find the runs of `verify-trusted` for a pull request and head by their run name, with every attempt.

    Neither the field `head_sha` of a run nor its field `pull_requests` is used
    (section 6.1, step 1). `gh` needs `workflow_runs(workflow)` and
    `run_attempt(run_id, attempt)`.
    """
    name = run_name(pull_request, head)
    runs = [r for r in gh.workflow_runs(VERIFY_WORKFLOW) if r.get("display_title") == name]
    if not runs:
        return Attempts("none")
    runs.sort(key=lambda r: (r.get("created_at", ""), r["id"]))
    attempts: list[tuple[int, int, str]] = []
    waiting: list[int] = []
    latest_url = ""
    for run in runs:
        for number in range(1, int(run.get("run_attempt", 1)) + 1):
            attempt = gh.run_attempt(run["id"], number)
            if attempt.get("status") != "completed":
                waiting.append(run["id"])
                continue
            attempts.append((run["id"], number, attempt.get("conclusion") or "none"))
            latest_url = attempt.get("html_url", latest_url)
    last = runs[-1]
    if waiting:
        return Attempts("in progress", tuple(attempts), tuple(sorted(set(waiting))), last["id"],
                        int(last.get("run_attempt", 1)), latest_url)
    return Attempts("completed", tuple(attempts), (), last["id"], int(last.get("run_attempt", 1)), latest_url)


def certificate_problem(attestation: dict[str, Any], identity: str, repository_id: int | str, run_uri: str) -> str | None:
    """Why the certificate of one verified attestation is not that of this verification run, or None."""
    try:
        certificate = attestation["verificationResult"]["signature"]["certificate"]
    except (KeyError, TypeError):
        return "the verified attestation has no certificate"
    expected = {
        "subjectAlternativeName": identity,
        "sourceRepositoryIdentifier": str(repository_id),
        "runInvocationURI": run_uri,
        "runnerEnvironment": "github-hosted",
    }
    for field, value in expected.items():
        if str(certificate.get(field)) != value:
            return f"its certificate has {field} = {certificate.get(field)}, expected {value}"
    return None


# ------------------------------------------------------------------ the rule

def check_merge(records_dir: Path | str, trusted_dir: Path | str, head: str, allowed_signers: Path | str, gh, *,
                pull_request: int, records_ref: str = "HEAD", trusted_ref: str = "HEAD",
                stored_attestation: bool = False) -> Decision:
    """Whether the commit `head` of the pull request may be merged (section 6.2, steps 3 to 8).

    `records_dir` is a repository that holds the records branch at `records_ref`;
    `trusted_dir` one that holds the default branch at `trusted_ref`;
    `allowed_signers` the file with the list of signers of that default branch.
    `gh` answers `repository()`, `gh_version()`, `workflow_runs()`,
    `run_attempt()` and `attestation_verify()`.

    With `stored_attestation` the result file is verified with the bundle and
    the trusted root stored in the evidence, as the core does before a merge;
    without it, the attestation is asked from GitHub, as `approval-gate` does.
    Everything else is the same.

    Passes only if no rejection exists for the commit and one approval of the
    change satisfies every condition. Never raises for a refusal: the reasons
    are returned.
    """
    if not _COMMIT.fullmatch(head or ""):
        return Decision(False, (f"{head!r} is not a commit identifier",))
    try:
        records, default_head = _trusted_records(records_dir, records_ref, trusted_dir, trusted_ref, allowed_signers)
    except RuleError as exc:
        return Decision(False, (str(exc),))

    rejections = [r for r in records if r.kind == "rejection" and r.data["covers"][0].get("commit") == head]
    if rejections:
        return Decision(False, tuple(f"the commit {head} was rejected by {r.signer} with {r.id}: {r.data.get('reason')}"
                                     for r in rejections))
    approvals = [r for r in records if r.kind == "approval" and r.path.startswith(f"approvals/changes/{head}/")]
    if not approvals:
        return Decision(False, (f"no approval of a change exists for the commit {head}",))

    try:
        version = tuple(gh.gh_version())
        if version < GH_MINIMUM:
            return Decision(False, (f"gh {'.'.join(map(str, version))} is older than "
                                    f"{'.'.join(map(str, GH_MINIMUM))}; attestations are not verified with it",))
        repository = gh.repository()
        attempts = attempts_of(gh, pull_request, head)
    except GitHubError as exc:
        return Decision(False, (f"GitHub could not be asked: {exc}",))

    by_id = {r.id: r for r in records}
    reasons: list[str] = []
    for approval in approvals:
        try:
            problems, evidence = _approval_problems(approval, by_id, records_dir, head, default_head, pull_request,
                                                    repository, attempts, gh, stored_attestation)
        except (KeyError, TypeError, IndexError, ValueError, AttributeError) as exc:
            problems, evidence = [f"a record it relies on does not have the expected form ({type(exc).__name__}: {exc})"], None
        if not problems:
            return Decision(True, (), approval.id, evidence)
        reasons += [f"{approval.id}: {problem}" for problem in problems]
    return Decision(False, tuple(reasons))


def _trusted_records(records_dir, records_ref, trusted_dir, trusted_ref, allowed_signers) -> tuple[list[Entry], str]:
    """The checked records and the head of the default branch, from the trusted checkout only."""
    resolved = _git(trusted_dir, "rev-parse", "--verify", "--quiet", f"{trusted_ref}^{{commit}}")
    if resolved.returncode != 0:
        raise RuleError(f"the default branch cannot be read at {trusted_ref}")
    default_head = _text(resolved.stdout)
    try:
        parse_signers(Path(allowed_signers).read_bytes())
    except OSError:
        raise RuleError("the list of signers of the default branch cannot be read") from None
    except ValueError as exc:
        raise RuleError(f"the list of signers of the default branch: {exc}") from None
    try:
        frame = yaml.safe_load(_show(trusted_dir, default_head, FRAME_PATH).decode("utf-8"))
    except (yaml.YAMLError, UnicodeDecodeError):
        raise RuleError(f"{FRAME_PATH} of the default branch is not valid YAML") from None
    approvers = frame.get("approvers") if isinstance(frame, dict) else None
    if not isinstance(approvers, list) or not approvers or not all(isinstance(a, str) for a in approvers):
        raise RuleError(f"{FRAME_PATH} of the default branch names no approvers")
    return read_records(records_dir, records_ref, allowed_signers, tuple(approvers)), default_head


def _approval_problems(approval: Entry, by_id: dict[str, Entry], records_dir, head: str, default_head: str,
                       pull_request: int, repository: dict[str, Any], attempts: Attempts, gh,
                       stored_attestation: bool) -> tuple[list[str], str | None]:
    """Why this approval of the change does not let the head be merged; empty if it does. Also the evidence it names."""
    cover = approval.data["covers"][0]
    evidence = by_id.get(cover.get("evidence"))
    if evidence is None or evidence.kind != "evidence":
        return [f"the evidence {cover.get('evidence')} it names is not on the records branch"], None
    stated = evidence.data
    problems: list[str] = []

    # step 5: the evidence, and the test state a human approved before the start
    if stated["result"] != "passed":
        problems.append(f"the evidence {evidence.id} has the result '{stated['result']}', not 'passed'")
    if stated["implementation_commit"] != head:
        problems.append(f"the evidence {evidence.id} is for the commit {stated['implementation_commit']}, not for the head {head}")
    if stated["task"] != cover.get("ref"):
        problems.append(f"the evidence {evidence.id} is for {stated['task']}, the approval for {cover.get('ref')}")
    order = by_id.get(stated["work_order"])
    if order is None or order.kind != "workorder":
        return problems + [f"the work order {stated['work_order']} of the evidence is not on the records branch"], evidence.id
    start = order.data["starts_from"]
    if (order.data["run"], order.data["task"], order.data["base_commit"]) != (
            stated["agent_run"], stated["task"], stated["base_commit"]):
        problems.append(f"the evidence {evidence.id} does not name run, task and base commit of its work order {order.id}")
    approved = by_id.get(start["approval"])
    if approved is None or approved.kind != "approval" or approved.data["covers"][0].get("kind") == "change":
        return problems + [f"the approval of states {start['approval']} of the work order is not on the records branch"], evidence.id
    tests = [c for c in approved.data["covers"] if c.get("kind") == "tests" and c.get("ref") == stated["task"]]
    if len(tests) != 1:
        problems.append(f"the approval of states {approved.id} does not approve the tests of {stated['task']}")
    elif not (tests[0].get("state") == stated["test_state"] == start["states"]["tests"]):
        problems.append(f"the evidence {evidence.id} has the test state {stated['test_state']}; approved before the start "
                        f"was {tests[0].get('state')} ({approved.id})")

    # step 6: the result file and its attestation
    folder = evidence.path.rsplit("/", 1)[0]
    content = _show(records_dir, evidence.commit, f"{folder}/result.json")
    try:
        result = json.loads(content.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        return problems + [f"the result file of the evidence {evidence.id} is not valid JSON"], evidence.id
    if not isinstance(result, dict) or result.get("schema") != "factory/result/1":
        return problems + [f"the result file of the evidence {evidence.id} is not a result of the verification"], evidence.id
    repo, repository_id = repository["full_name"], repository["id"]
    for name, found, expected, meaning in [
        ("result", result["result"], "passed", "what a merge needs"),
        ("result", result["result"], stated["result"], "the result of the evidence record"),
        ("implementation_commit", result["implementation_commit"], head, "the head of the pull request"),
        ("test_state", result["test_state"], stated["test_state"], "the test state of the evidence record"),
        ("definition_commit", result["definition_commit"], default_head,
         "the current head of the default branch; the default branch has moved since the verification"),
        ("definition_commit", result["definition_commit"], stated["base_commit"], "the base commit of the evidence record"),
        ("repository_id", result["repository_id"], repository_id, "the identifier of this repository"),
        ("pull_request", result["pull_request"], pull_request, "this pull request"),
        ("task", result["task"], stated["task"], "the task of the evidence record"),
        ("run_ref", result["run_ref"], stated["agent_run"], "the run of the evidence record"),
        ("run.id", str(result["run"]["id"]), str(stated["verification"]["run"]["id"]), "the verification run of the evidence record"),
    ]:
        if found != expected:
            problems.append(f"the result file names {name} = {found}, but {meaning} is {expected}")

    identity = signer_identity(repo, repository["default_branch"])
    run_uri = f"https://github.com/{repo}/actions/runs/{result['run']['id']}/attempts/{result['run']['attempt']}"
    with tempfile.TemporaryDirectory(prefix="factory-gate-") as tmp:
        file = Path(tmp) / "result.json"
        file.write_bytes(content)
        stored = {}
        if stored_attestation:
            for option, name in (("bundle", "bundle.jsonl"), ("trusted_root", "trusted_root.jsonl")):
                stored[option] = Path(tmp) / name
                stored[option].write_bytes(_show(records_dir, evidence.commit, f"{folder}/{name}"))
        try:
            attestations = gh.attestation_verify(file, repo, identity, **stored)
        except GitHubError as exc:
            attestations = None
            problems.append(f"the attestation of the result file did not verify: {exc}")
    if attestations is not None:
        mismatches = [certificate_problem(a, identity, repository_id, run_uri) for a in attestations]
        if not attestations or all(mismatches):
            problems.append("no attestation of the result file is from the verification run it names"
                            + (f": {mismatches[0]}" if mismatches else ""))

    # step 7: the rule on attempts, for every run of verify-trusted of this pull request and head
    if attempts.state == "none":
        problems.append(f"no run of verify-trusted is named for pull request {pull_request} and head {head}")
    elif attempts.state == "in progress":
        problems.append("a run of verify-trusted for this pull request and head is still in progress")
    else:
        failed = [f"run {r} attempt {a}: {c}" for r, a, c in attempts.attempts if c != "success"]
        if not attempts.passed:
            problems.append("an attempt of the verification failed; a later attempt that passed does not count "
                            f"({'; '.join(failed) or 'no completed attempt'})")
        if (attempts.run_id, attempts.attempt) != (result["run"]["id"], result["run"]["attempt"]):
            problems.append(f"the result file is of run {result['run']['id']} attempt {result['run']['attempt']}, but the latest "
                            f"attempt of the verification is run {attempts.run_id} attempt {attempts.attempt}")
    return problems, evidence.id


# -------------------------------------------------------- the gate as a job

class GhCommand:
    """What the rule asks of GitHub, through `gh`, for the job `approval-gate`.

    The repository is taken from the environment of the job, not from an
    answer of the API. The token of the job is read by `gh` from `GH_TOKEN`;
    nothing here holds or prints it.
    """

    def __init__(self, repo: str, repository_id: int, default_branch: str, executable: str = "gh") -> None:
        if not re.fullmatch(r"[\w.-]+/[\w.-]+", repo):
            raise ValueError(f"{repo!r} is not a repository of the form owner/name")
        self.repo, self.repository_id, self.default_branch, self.executable = repo, repository_id, default_branch, executable

    def _run(self, *args: str) -> str:
        try:
            result = subprocess.run([self.executable, *args], stdin=subprocess.DEVNULL, capture_output=True, timeout=300)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise GitHubError(f"gh {args[0]} could not be run: {type(exc).__name__}") from None
        if result.returncode != 0:
            raise GitHubError(f"gh {' '.join(args[:2])} failed: {_text(result.stderr)}")
        return result.stdout.decode("utf-8", errors="replace")

    def repository(self) -> dict[str, Any]:
        return {"id": self.repository_id, "full_name": self.repo, "default_branch": self.default_branch}

    def gh_version(self) -> tuple[int, ...]:
        match = re.search(r"gh version (\d+)\.(\d+)\.(\d+)", self._run("--version"))
        if not match:
            raise GitHubError("gh does not report its version")
        return tuple(int(part) for part in match.groups())

    def workflow_runs(self, workflow: str) -> list[dict[str, Any]]:
        pages = json.loads(self._run(
            "api", "--paginate", "--slurp", "--method", "GET", "-H", "Accept: application/vnd.github+json",
            f"repos/{self.repo}/actions/workflows/{workflow}/runs", "-f", "event=pull_request_target", "-F", "per_page=100"))
        return [run for page in pages for run in page.get("workflow_runs", [])]

    def run_attempt(self, run_id: int, attempt: int) -> dict[str, Any]:
        return json.loads(self._run("api", "-H", "Accept: application/vnd.github+json",
                                    f"repos/{self.repo}/actions/runs/{int(run_id)}/attempts/{int(attempt)}"))

    def attestation_verify(self, file: Path, repo: str, cert_identity: str, *, bundle: Path | None = None,
                           trusted_root: Path | None = None) -> list[dict[str, Any]]:
        args = ["attestation", "verify", str(file), "--repo", repo, "--cert-identity", cert_identity,
                "--deny-self-hosted-runners", "--format", "json"]
        if bundle is not None:
            args += ["--bundle", str(bundle)]
        if trusted_root is not None:
            args += ["--custom-trusted-root", str(trusted_root)]
        verified = json.loads(self._run(*args))
        if not isinstance(verified, list) or not verified:
            raise GitHubError("gh attestation verify returned no verified attestation")
        return verified


def main(argv: list[str] | None = None) -> int:
    """The job `approval-gate`: exit code 0 only if the head of the pull request may be merged."""
    env = os.environ
    parser = argparse.ArgumentParser(description="The rule for a merge of the AI Software Factory, as the job approval-gate.")
    parser.add_argument("--records", default="records", help="checkout of the records branch, with its whole history")
    parser.add_argument("--trusted", default="trusted", help="checkout of the default branch")
    parser.add_argument("--gh", default="gh", help="the command line of GitHub, in the pinned version")
    args = parser.parse_args(argv)
    try:
        head, number = env["HEAD_SHA"], int(env["PULL_REQUEST"])
        gh = GhCommand(env["GITHUB_REPOSITORY"], int(env["GITHUB_REPOSITORY_ID"]), env["DEFAULT_BRANCH"], args.gh)
    except (KeyError, ValueError) as exc:
        print(f"approval-gate: the job does not say what to check ({type(exc).__name__}: {exc})")
        return 1
    decision = check_merge(args.records, args.trusted, head, Path(args.trusted) / ".factory" / "allowed_signers", gh,
                           pull_request=number)
    if decision.passed:
        print(f"approval-gate: passed for pull request {number}, head {head}: "
              f"approval {decision.approval}, evidence {decision.evidence}")
        return 0
    print(f"approval-gate: refused for pull request {number}, head {head}")
    for reason in decision.reasons:
        print(f"  - {reason}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
