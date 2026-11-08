#!/usr/bin/env python3
"""Final-signature documentation gate; no third-party Python dependencies.

From the repository root (no HOL build needed for the first two commands)::

  python3 src/simp/tests/compatibility/check_task27_docs.py
  python3 -B -m unittest discover -s src/simp/tests/compatibility \
      -p test_task27_docs.py
  python3 src/simp/tests/compatibility/check_task27_docs.py \
      --execute-examples --output /tmp/task27-docs-result

The last command requires built bossLib/holTheory and their dependencies. It
builds ONLY a private process_docfiles executable using standard buildheap,
processes the selected 48 docfiles together, then starts 30 independent
processes for the extension/split examples. No SML is piped into bin/hol.
Docfiles and prelude are copied before processing; repository build sources
are hashed. A relocated configured HOLDIR is exposed read-only via bwrap
when necessary (no shared symlink repair). Commands,
environment/runtime options, hashes, logs and a single processed receipt
archive survive in --output; the private executable and scratch are removed.
Pandoc's presence is recorded; without it this validates polyscripter, NOT
.txt/HTML rendering. This is not a full documentation or clean-build gate.

Scope: current notes/README/MANIFEST and every help docfile mentioning one of
the owners below (also owner-named docfiles). Historical compatibility ledgers
are deliberately not inputs. References outside these owners are not API
claims checked by this gate. Signatures, NEVER doc declarations, supply names.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[4]
CORE_OWNERS = """
Cond_rewr Cond_rewrExt Opening OpeningExt Traverse TraverseExt Travrules
TravrulesExt congLib congExtLib simpLib simpExtLib splitLib simpMarkerLib
pureSimps pureSimpsExt boolSimps boolSimpsExt combinSimps combinSimpsExt
""".split()
SIGNATURES = {m: f"src/simp/src/{m}.sig" for m in CORE_OWNERS}
SIGNATURES.update({
    "numSimpsExt": "src/num/arith/src/numSimpsExt.sig",
    "pred_setSimpsExt": "src/pred_set/src/pred_setSimpsExt.sig",
    "listSimpsExt": "src/list/src/listSimpsExt.sig",
    "intReduceExt": "src/integer/intReduceExt.sig",
    "integer_wordLibExt": "src/integer/integer_wordLibExt.sig",
    "realSimpsExt": "src/real/realSimpsExt.sig",
    "trackedSimpDefaults": "src/boss/trackedSimpDefaults.sig",
})
CURRENT_DOCS = ("src/simp/src/notes.md", "src/simp/README",
                "src/simp/src/MANIFEST")
REMOVED_DOCS = tuple(f"help/Docfiles/simpLib.{name}.smd" for name in (
    "filter_rewrites", "legacy_traversedata_for_ss", "threaded_cong_ss"))
SELECTED_DOCS = tuple("""
Cond_rewrExt.COND_REWR_CONVS.smd
fcpLib.FCP_ss.smd
simpExtLib.ExclX.smd
simpExtLib.GEN_GLOBAL_SIMP_TAC.smd
simpExtLib.GEN_SIMP_TAC.smd
simpExtLib.Split.smd
simpExtLib.add_looper.smd
simpExtLib.add_safe_solver.smd
simpExtLib.add_split.smd
simpExtLib.add_unsafe_solver.smd
simpExtLib.clear_rules.smd
simpExtLib.del_looper.smd
simpExtLib.del_split.smd
simpExtLib.filter_rewrites.smd
simpExtLib.looper_ss.smd
simpExtLib.mk_simpset.smd
simpExtLib.mk_tactic_solver.smd
simpExtLib.prepare_rewrite_bundle.smd
simpExtLib.remove_solver.smd
simpExtLib.rewrite_source_handles.smd
simpExtLib.safe_solver_ss.smd
simpExtLib.set_cond_depth.smd
simpExtLib.set_looper.smd
simpExtLib.set_safe_solvers.smd
simpExtLib.set_subgoaler.smd
simpExtLib.set_term_ord.smd
simpExtLib.set_unsafe_solvers.smd
simpExtLib.solver_ss.smd
simpExtLib.split_ss.smd
simpExtLib.threaded_cong_ss.smd
simpExtLib.xtraversedata_for_ss.smd
simpLib..KAL.smd
simpLib.AC.smd
simpLib.ASM_SIMP_RULE.smd
simpLib.Cong.smd
simpLib.Excl.smd
simpLib.SIMP_PROVE.smd
simpLib.SSFRAG.smd
simpLib.exclude_ssfrags.smd
simpLib.force_add.smd
simpLib.mk_simpset.smd
simpLib.register_frag.smd
simpLib.remove_ssfrags.smd
simpLib.traversedata_for_ss.smd
simpLib.type_ssfrag.smd
splitLib.SPLIT_TAC.smd
splitLib.enable_split_attribute.smd
splitLib.exclude_split.smd
""".split())
INDEPENDENT_DOCS = tuple(n for n in SELECTED_DOCS
                         if n.startswith("simpExtLib.")) + (
                             "splitLib.SPLIT_TAC.smd",)
# This explicit build input is saved verbatim with each executable run.
PRELUDE = """(* Task27 private processor: standard HOL interactive bindings. *)
(* polyscripter.sml loads tools-poly/prelude.ML and prelude2.ML itself. *)
val _ = load "listTheory";
"""
# Fail closed if these precise current claims disappear/change. This is not
# an NLP proof: changed wording requires review and a corresponding test.
SENTINELS = {
    "src/simp/README": (
        "There is no transparent promotion of arbitrary ordinary simpsets "
        "or replay in getters.",),
    "src/simp/src/notes.md": (
        "there is no eligibility scan or extension dispatch.",
        "These replacements are not transparent compatibility wrappers.",
        "There is no goal-time promotion/strategy dispatch in ordinary "
        "tactics.",
        "ssfrags_of` is inspection, **not** reconstruction:",),
    "src/simp/src/MANIFEST": (
        "No arbitrary ordinary set import or ssfrags_of reconstruction.",),
    "help/Docfiles/simpExtLib.GEN_SIMP_TAC.smd": (
        "there is no ordinary-set promotion.",),
}
IDENT = r"[A-Za-z_][A-Za-z_0-9']*"
SYMBOL = r"[!%&$#+\-/:<=>?@\\~`^*]+"
NAME = rf"(?:{IDENT}|{SYMBOL})"
QUALIFIED = re.compile(
    rf"\b({'|'.join(sorted(SIGNATURES, key=len, reverse=True))})\."
    rf"(\.KAL|{IDENT}|{SYMBOL})")
NON_API = {
    "splitLib.persistent.rules.v1": "private persistence stream",
    "simpLib.ssfragDB": "private typed registry slot",
    "simpExtLib.ssfragDB": "private typed registry slot",
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_sml_comments(text):
    """Nested SML comments/strings, with line numbers and offsets preserved."""
    result, pos, depth, string = [], 0, 0, False
    while pos < len(text):
        pair, char = text[pos:pos + 2], text[pos]
        if not string and pair == "(*":
            depth += 1
        elif depth and pair == "*)":
            depth -= 1
        elif depth:
            result.append("\n" if char == "\n" else " ")
            pos += 1
            continue
        elif string and char == "\\":
            result.extend("\n" if c == "\n" else " " for c in pair)
            pos += len(pair)
            continue
        else:
            if char == '"':
                string = not string
                result.append(" ")
            else:
                result.append(" " if string and char != "\n" else char)
            pos += 1
            continue
        result.extend("  ")  # comment delimiter
        pos += 2
    if depth or string:
        raise ValueError("unclosed SML comment/string")
    return "".join(result)


def signature_symbols(text, include_symbols=None):
    """Read declaration names/types/constructors, not identifiers in comments.

    Handles the final signatures' flat specifications, type parameters,
    datatype alternatives and includes. Unknown includes fail rather than
    silently validating an incomplete API. This is not a general SML parser.
    """
    text = strip_sml_comments(text)
    params = r"(?:\([^)]*\)\s*|'[A-Za-z_0-9]+\s+)?"
    declaration = re.compile(
        rf"\b(val|type|eqtype|datatype|exception|include)\s+"
        rf"{params}(?:op\s+)?({NAME})")
    matches = list(declaration.finditer(text))
    symbols = set()
    for i, match in enumerate(matches):
        kind, name = match.groups()
        if kind == "include":
            if include_symbols is None or name not in include_symbols:
                raise ValueError(f"unresolved signature include: {name}")
            symbols.update(include_symbols[name])
            continue
        symbols.add(name)
        if kind == "datatype":
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            body = text[match.end():end]
            if not re.match(r"\s*=\s*datatype\b", body):
                symbols.update(re.findall(rf"(?:=|\|)\s*({NAME})", body))
    return symbols


def mask_non_api(text, path):
    """Only explicit historical table coordinates and exact private names."""
    excluded = []
    lines = text.splitlines(keepends=True)
    in_old_table = False
    for index, line in enumerate(lines):
        if path == "src/simp/src/notes.md":
            # Only the OLD column of this exact migration table is historical.
            # Final-column references still have to exist in their signatures.
            if line == ("| Earlier branch use | "
                        "Final module/type/construction |\n"):
                in_old_table = True
            elif not line.startswith("| "):
                in_old_table = False
            elif in_old_table:
                old, sep, rest = line[1:].partition("|")
                if sep:
                    excluded.append({"line": index + 1,
                                     "reason": "earlier branch table column",
                                     "text": old.strip()})
                    line = "|" + " " * len(old) + sep + rest
        for name, reason in NON_API.items():
            if name in line:
                # Do not hide a longer unknown reference sharing this prefix.
                pattern = re.escape(name) + r"(?![A-Za-z_0-9'.])"
                if re.search(pattern, line):
                    excluded.append({"line": index + 1, "reason": reason,
                                     "text": name})
                    line = re.sub(pattern, lambda m: " " * len(m.group()),
                                  line)
        lines[index] = line
    return "".join(lines), excluded


def scan_references(text, symbols, path):
    text, excluded = mask_non_api(text, path)
    valid, unknown = [], []
    for match in QUALIFIED.finditer(text):
        owner, name = match.groups()
        name = name.rstrip("`")  # Markdown's closing inline-code delimiter
        # Module.sml/.sig and globbed filenames are not member accesses.
        if name in {"sml", "sig", "smd"} or name == "*":
            continue
        # Alias-encoded link target for the ++ operator.
        if name == ".KAL":
            name = "++"
        entry = {"line": text.count("\n", 0, match.start()) + 1,
                 "reference": f"{owner}.{name}"}
        (valid if name in symbols[owner] else unknown).append(entry)
    return valid, unknown, excluded


def docfile_title_errors(path, text, symbols):
    """Validate filename/title/heading against signature, not declarations."""
    owner, _, member = Path(path).stem.partition(".")
    if owner not in symbols:
        return []  # external owner, explicitly outside this signature gate
    explicit = re.search(r"^title:\s*['\"]?([^\n'\"]+)", text, re.M)
    title = explicit.group(1).strip() if explicit else f"{owner}.{member}"
    errors = []
    if not title.startswith(owner + "."):
        return [f"title {title!r} disagrees with filename owner {owner}"]
    actual = title[len(owner) + 1:]
    if actual not in symbols[owner]:
        errors.append(f"unknown docfile title: {title}")
    # .KAL is the canonical help filename encoding for ++, not an API.
    expected = "++" if member == ".KAL" else member
    if actual != expected:
        errors.append(f"title {title!r} disagrees with filename {member}")
    heading = re.search(r"^## `([^`]+)`", text, re.M)
    if not heading or heading.group(1) not in {actual, title}:
        errors.append(f"heading disagrees with title {title}")
    return errors


def check_docs(root=ROOT):
    root = Path(root)
    abbrev = signature_symbols((root / "src/1/Abbrev.sig").read_text())
    symbols = {m: signature_symbols((root / p).read_text(), {"Abbrev": abbrev})
               for m, p in SIGNATURES.items()}
    docs = set(CURRENT_DOCS)
    for path in (root / "help/Docfiles").glob("*.smd"):
        if path.name.split(".")[0] in symbols or QUALIFIED.search(
                path.read_text()):
            docs.add(path.relative_to(root).as_posix())
    errors, unknown, excluded, count = [], [], [], 0
    for path in sorted(docs):
        text = (root / path).read_text()
        valid, missing, non_api = scan_references(text, symbols, path)
        count += len(valid)
        unknown.extend(dict(path=path, **m) for m in missing)
        excluded.extend(dict(path=path, **m) for m in non_api)
        if path.endswith(".smd"):
            errors.extend(f"{path}: {e}" for e in
                          docfile_title_errors(path, text, symbols))
    for path in REMOVED_DOCS:
        if (root / path).exists():
            errors.append(f"removed docfile still exists: {path}")
    for path, claims in SENTINELS.items():
        text = " ".join((root / path).read_text().split())
        for claim in claims:
            if claim not in text:
                errors.append(f"{path}: missing reviewed sentinel: {claim}")
    return {
        "scope": "current docs + relevant help; not historical ledgers",
        "signature_sha256": {p: sha256(root / p) for p in
                             sorted(set(SIGNATURES.values()) |
                                    {"src/1/Abbrev.sig"})},
        "doc_sha256": {p: sha256(root / p) for p in sorted(docs)},
        "signature_symbols": {m: sorted(s) for m, s in symbols.items()},
        "signature_references": count,
        "unknown_references": unknown,
        "non_api": excluded,
        "errors": errors,
    }


def processed_errors(text):
    # >>+ intentionally allows runtime exceptions; static failures must never
    # be accepted merely because process_docfiles itself returned success.
    return bool(re.search(r"Static Errors|error:|Exception- Fail|\bFail \"",
                          text))


def execute_examples(root, output, timeout=300):
    """Private processor; one combined run and fresh independent processes."""
    root, output = Path(root).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "prelude.sml").write_text(PRELUDE)
    result = {"selected_docs": list(SELECTED_DOCS),
              "independent_docs": list(INDEPENDENT_DOCS),
              "environment": {"HOL_CONFIG": "", "LC_ALL": "C.UTF-8"},
              "runtime_options": [], "timeout_seconds_per_process": timeout,
              "pandoc": shutil.which("pandoc"), "runs": []}
    env = dict(os.environ, **result["environment"])

    def run(args, cwd, logname):
        command = [str(a) for a in args]
        alias = Path(result["configured_holdir"])
        if alias != root:
            # Existing heaps/object links may name a configured path absent
            # on this host. Expose it privately, never repair shared symlinks.
            mask = alias.parent
            while not mask.is_dir() or mask.is_symlink():
                mask = mask.parent
            if mask == Path("/") or root == mask:
                raise RuntimeError("unsafe configured alias parent")
            # Use the configured canonical root consistently with sigobj.
            def canonical(path):
                try:
                    return str(alias / Path(path).relative_to(root))
                except ValueError:
                    return path
            command = [canonical(arg) for arg in command]
            env["HOLDIR"] = str(alias)
            result["environment"]["HOLDIR"] = str(alias)
            command = [
                "bwrap", "--die-with-parent", "--unshare-pid", "--unshare-net",
                "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
                # Poly/ML's FileSys.tmpName may use /tmp, not TMPDIR; SAT
                # proof replay during bossLib loading needs writable temp.
                "--tmpfs", "/tmp", "--tmpfs", str(mask), "--ro-bind", str(root), str(alias),
                "--ro-bind", str(root), str(root),
                "--bind", str(scratch), str(scratch),
                "--chdir", canonical(str(cwd)), "--", *command]
        with (output / logname).open("w") as log:
            proc = subprocess.run(command, cwd=cwd, env=env,
                                  stdin=subprocess.DEVNULL, stdout=log,
                                  stderr=subprocess.STDOUT,
                                  timeout=timeout, check=False)
        return {"command": command, "cwd": str(cwd),
                "exit": proc.returncode, "log": logname}

    try:
        with tempfile.TemporaryDirectory(prefix="task27-docs-") as temporary:
            scratch = Path(temporary)
            prelude = scratch / "prelude.sml"
            shutil.copy2(output / "prelude.sml", prelude)
            exe = scratch / "process_docfiles"
            config = (root / "sigobj/Systeml.sml").read_text()
            configured = re.search(r'^val HOLDIR = "([^"]+)"', config, re.M)
            if not configured:
                raise RuntimeError("cannot find configured Systeml.HOLDIR")
            result["configured_holdir"] = configured.group(1)
            # polyscripter uses ../../tools-poly/prelude{,2}.ML at startup.
            # Supply only that path, not a copied build tree or changed input.
            work = scratch / 'src/boss'
            work.mkdir(parents=True)
            (scratch / 'tools-poly').symlink_to(
                Path(result['configured_holdir']) / 'tools-poly')
            env.update(HOLDIR=str(root), HOME=str(scratch),
                       TMPDIR=str(scratch), TERM="dumb")
            result["environment"].update({k: env[k] for k in
                                          ("HOLDIR", "HOME", "TMPDIR",
                                           "TERM", "PATH")})
            inputs = ["bin/hol", "bin/hol.state0", "tools-poly/prelude.ML",
                      "tools-poly/prelude2.ML",
                      "Manual/Tools/polyscripter.sml",
                      "help/src-sml/Flash.sig", "help/src-sml/Flash.sml",
                      "help/src-sml/process_docfiles.sml"]
            result["build_input_sha256"] = {
                p: sha256(root / p) for p in inputs}
            result["prelude_sha256"] = sha256(prelude)
            result["doc_sha256"] = {
                f"help/Docfiles/{n}": sha256(root / "help/Docfiles" / n)
                for n in SELECTED_DOCS}
            build = [root / "bin/hol", "buildheap", "-b",
                     root / "bin/hol.state0", "bossLib", "holTheory", "Arbrat",
                     prelude, root / "Manual/Tools/polyscripter.sml",
                     root / "help/src-sml/Flash.sig",
                     root / "help/src-sml/Flash.sml",
                     root / "help/src-sml/process_docfiles.sml",
                     "-o", exe, "--exe", "main"]
            # Poly's exporter/linker also writes beside its current working
            # directory; keep all compiler artifacts in disposable scratch.
            result["build"] = run(build, work, "build.log")
            if result["build"]["exit"] or not exe.exists():
                raise RuntimeError("private processor build failed")
            # Copies: pandoc may write .txt beside its source .smd files.
            source = scratch / "input"
            source.mkdir()
            for name in SELECTED_DOCS:
                shutil.copy2(root / "help/Docfiles" / name, source / name)
            processed = scratch / "processed"
            combined = run([exe, source, processed], work,
                           "combined.log")
            combined["processed_count"] = len(list(processed.glob("*.smd")))
            combined["completion"] = "...polyscripter pass done" in (
                output / "combined.log").read_text()
            combined["static_errors"] = any(processed_errors(p.read_text())
                                             for p in processed.glob("*.smd"))
            result["combined"] = combined
            archive = output / "processed-receipts.tar.gz"
            with tarfile.open(archive, "w:gz") as tf:
                for path in sorted(processed.glob("*.smd")):
                    tf.add(path, arcname="processed/" + path.name)
            individual = scratch / "individual"
            individual.mkdir()
            dest = scratch / "individual-processed"
            for name in INDEPENDENT_DOCS:
                for path in individual.iterdir():
                    path.unlink()
                if dest.exists():
                    shutil.rmtree(dest)
                shutil.copy2(source / name, individual / name)
                receipt = run([exe, individual, dest], work,
                              f"individual-{name}.log")
                path = dest / name
                receipt.update(doc=name, processed=path.exists(),
                               completion="...polyscripter pass done" in (
                                   output / receipt["log"]).read_text(),
                               sha256=sha256(path) if path.exists() else None,
                               static_errors=(not path.exists() or
                                              processed_errors(
                                                  path.read_text())))
                result["runs"].append(receipt)
            result["ok"] = (
                combined["exit"] == 0 and combined["completion"] and
                combined["processed_count"] == len(SELECTED_DOCS) and
                not combined["static_errors"] and
                all(r["exit"] == 0 and r["processed"] and r["completion"] and
                    not r["static_errors"] for r in result["runs"]))
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        result.update(ok=False, error=str(error))
    finally:
        # Keep commands rerunnable after removing the private tree.
        if "temporary" in locals():
            result = json.loads(json.dumps(result).replace(
                temporary, "<scratch>"))
        (output / "execution.json").write_text(
            json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--execute-examples", action="store_true")
    parser.add_argument("--output", type=Path,
                        help="new evidence directory (required for execution)")
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    if args.execute_examples and args.output is None:
        parser.error("--execute-examples requires --output (a new directory)")
    report = check_docs(args.root)
    ok = not report["errors"] and not report["unknown_references"]
    if ok and args.execute_examples:
        execution = execute_examples(args.root, args.output, args.timeout)
        ok = execution["ok"]
        report["execution"] = {
            "ok": ok, "receipt": str(args.output / "execution.json")}
        if "error" in execution:
            report["execution"]["error"] = execution["error"]
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / "scan.json").write_text(
            json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
