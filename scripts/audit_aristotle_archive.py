#!/usr/bin/env python3
"""Read-only safety audit for an immutable Aristotle result archive."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import tarfile
from pathlib import Path, PurePosixPath


class ArchiveAuditError(ValueError):
    pass


FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "new axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe declaration": re.compile(r"(?m)^\s*unsafe\b"),
    "Classical namespace": re.compile(r"\bClassical(?:\.|\b)"),
}


def safe_member_name(name: str) -> bool:
    path = PurePosixPath(name)
    return (not path.is_absolute() and ".." not in path.parts and
            not name.startswith("/") and "\x00" not in name)


def audit_archive(path: Path) -> dict:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    lean_files: list[dict] = []
    scoped_exceptions: list[dict] = []
    with tarfile.open(path, mode="r:*") as archive:
        for member in archive.getmembers():
            if not safe_member_name(member.name):
                raise ArchiveAuditError(f"unsafe archive path {member.name!r}")
            if member.issym() or member.islnk():
                raise ArchiveAuditError(f"archive link is not permitted: {member.name!r}")
            if not member.isfile() or not member.name.endswith(".lean"):
                continue
            extracted = archive.extractfile(member)
            if extracted is None:
                raise ArchiveAuditError(f"cannot read Lean member {member.name!r}")
            raw = extracted.read()
            try:
                source = raw.decode("utf-8")
            except UnicodeDecodeError as error:
                raise ArchiveAuditError(f"non-UTF-8 Lean member {member.name!r}") from error
            failures = [label for label, pattern in FORBIDDEN.items()
                        if pattern.search(source)]
            # Aristotle's generated compilation harness may open Classical
            # even when the returned edition sources do not. This is never
            # silently ignored: it is a path-scoped, reported exception. All
            # placeholders, axioms and unsafe declarations remain forbidden
            # everywhere, including the harness.
            if (failures == ["Classical namespace"] and
                    PurePosixPath(member.name).parts[-2:] == ("RequestProject", "Main.lean")):
                scoped_exceptions.append({
                    "path": member.name,
                    "construct": "Classical namespace",
                    "scope": "generated-compilation-harness-only",
                })
                failures = []
            if failures:
                raise ArchiveAuditError(
                    f"{member.name}: forbidden constructs: {', '.join(failures)}"
                )
            lean_files.append({
                "path": member.name,
                "bytes": len(raw),
                "sha256": hashlib.sha256(raw).hexdigest(),
            })
    if not lean_files:
        raise ArchiveAuditError("archive contains no Lean source")
    return {
        "archive": str(path),
        "archive_sha256": digest,
        "lean_files": sorted(lean_files, key=lambda record: record["path"]),
        "forbidden_constructs": [],
        "scoped_exceptions": scoped_exceptions,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    try:
        report = audit_archive(args.archive)
    except (ArchiveAuditError, OSError, tarfile.TarError) as error:
        raise SystemExit(f"archive audit error: {error}")
    print(json.dumps(report, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
