#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository_root"

if [ -d "$HOME/.elan/bin" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi

command -v lake >/dev/null 2>&1 || {
  echo "error: lake is required" >&2
  exit 1
}
command -v python3 >/dev/null 2>&1 || {
  echo "error: python3 is required" >&2
  exit 1
}
command -v elan >/dev/null 2>&1 || {
  echo "error: elan is required to locate the pinned Lean toolchain" >&2
  exit 1
}

toolchain_entry=$(tr -d "[:space:]" < lean-toolchain)
toolchain_lean=$(elan which lean)
toolchain_root=$(dirname -- "$(dirname -- "$toolchain_lean")")
export LAKE_HOME="$toolchain_root"
export LEAN_SYSROOT="$toolchain_root"
export LEAN="$toolchain_root/bin/lean"
export PATH="$toolchain_root/bin:$HOME/.elan/bin:$PATH"

if [ ! -d "TTC" ] || [ -L "TTC" ]; then
  echo "error: required TTC proof directory is missing or not a regular directory" >&2
  exit 1
fi

for required_file in \
  lakefile.toml lean-toolchain comparator.json \
  formalization.yaml Challenge.lean Solution.lean README.md LICENSE; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

check_tmpdir=$(mktemp -d)
cleanup_check_tmpdir() {
  rm -rf -- "$check_tmpdir"
}
trap cleanup_check_tmpdir EXIT

# In the managed exec namespace Lean may see a host PID in /proc/<pid>/exe.
# Redirect those reads to the current process so Lean can locate its sysroot.
cat >"$check_tmpdir/lean-proc-self.c" <<\C
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>

static int is_proc_pid_exe(const char *path) {
  if (path == NULL || strncmp(path, "/proc/", 6) != 0) return 0;
  const char *p = path + 6;
  if (*p < 48 || *p > 57) return 0;
  while (*p >= 48 && *p <= 57) ++p;
  return strcmp(p, "/exe") == 0;
}

ssize_t readlink(const char *path, char *buffer, size_t size) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (real_readlink == NULL) real_readlink = dlsym(RTLD_NEXT, "readlink");
  if (is_proc_pid_exe(path)) path = "/proc/self/exe";
  return real_readlink(path, buffer, size);
}

ssize_t readlinkat(int dirfd, const char *path, char *buffer, size_t size) {
  static ssize_t (*real_readlinkat)(int, const char *, char *, size_t);
  if (real_readlinkat == NULL) real_readlinkat = dlsym(RTLD_NEXT, "readlinkat");
  if (dirfd == AT_FDCWD && is_proc_pid_exe(path)) path = "/proc/self/exe";
  return real_readlinkat(dirfd, path, buffer, size);
}
C
command -v cc >/dev/null 2>&1 || {
  echo "error: cc is required to prepare the local Lean process shim" >&2
  exit 1
}
cc -shared -fPIC -o "$check_tmpdir/lean-proc-self.so" \
  "$check_tmpdir/lean-proc-self.c" -ldl
export LD_PRELOAD="$check_tmpdir/lean-proc-self.so${LD_PRELOAD:+:$LD_PRELOAD}"

expected_version=${toolchain_entry#*:}
expected_lean_version=${expected_version#v}
lake_version=$(lake --version)
case "$lake_version" in
  *"$expected_version"*|*"Lean version $expected_lean_version"*) ;;
  *)
    echo "error: lake does not match lean-toolchain $toolchain_entry: $lake_version" >&2
    exit 1
    ;;
esac
if [ ! -x "$toolchain_root/bin/lean" ]; then
  echo "error: pinned toolchain Lean binary is missing: $toolchain_root/bin/lean" >&2
  exit 1
fi

python3 - <<\PY
import json
import pathlib
import re

config = json.loads(pathlib.Path("comparator.json").read_text(encoding="utf-8"))
module_files = ["Challenge.lean", "Solution.lean"]
module_files += [str(p) for p in sorted(pathlib.Path("TTC").rglob("*.lean"))]
for name in module_files:
    lines = pathlib.Path(name).read_text(encoding="utf-8").splitlines()
    first = next(
        (line.strip() for line in lines
         if line.strip() and not line.strip().startswith("--")),
        "",
    )
    if first != "module" and not first.startswith("import ") \
            and not first.startswith("public import "):
        raise SystemExit(f"error: {name} must begin with a module or import header")
expected_definitions = [
    "TTC.HousingMarket",
    "TTC.ttcAllocation",
    "TTC.ttcIter",
    "TTC.Core",
    "TTC.StrictCore",
]
expected_theorems = [
    "TTC.Palomar.ttcTerminates",
    "TTC.Palomar.ttcInCore",
    "TTC.Palomar.ttcUniqueStrictCore"
]
if config.get("challenge_module") != "Challenge":
    raise SystemExit("error: comparator challenge_module must be Challenge")
if config.get("solution_module") != "Solution":
    raise SystemExit("error: comparator solution_module must be Solution")
actual_definitions = config.get("definition_names")
if actual_definitions != expected_definitions:
    raise SystemExit(f"error: unexpected definition_names: {actual_definitions}")
actual_theorems = config.get("theorem_names")
if actual_theorems != expected_theorems:
    raise SystemExit(f"error: unexpected theorem_names: {actual_theorems}")
if set(config.get("permitted_axioms", [])) != {
    "propext", "Classical.choice", "Quot.sound"
}:
    raise SystemExit("error: permitted_axioms must be propext, Classical.choice, and Quot.sound")

challenge = pathlib.Path("Challenge.lean").read_text(encoding="utf-8")
challenge_imports = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", challenge, re.M)
for imports in challenge_imports:
    for imported in imports.split():
        if not (imported == "Lean" or imported.startswith("Lean.")
                or imported == "Mathlib" or imported.startswith("Mathlib.")):
            raise SystemExit(f"error: Challenge imports a project or unsupported module: {imported}")
challenge_sorry_count = len(re.findall(r"\bsorry\b", challenge))
if challenge_sorry_count != 3:
    raise SystemExit(f"error: Challenge.lean must contain exactly 3 sorry tokens (the 3 theorem placeholders; definitions have real bodies), found {challenge_sorry_count}")
if re.search(r"\b(admit|axiom|unsafe)\b", challenge):
    raise SystemExit("error: Challenge.lean contains admit, axiom, or unsafe")

solution = pathlib.Path("Solution.lean").read_text(encoding="utf-8")
solution_forbidden = re.findall(r"\b(sorry|admit|axiom|unsafe)\b", solution)
if solution_forbidden:
    raise SystemExit(f"error: forbidden token(s) {sorted(set(solution_forbidden))} found in Solution.lean")

for path in sorted(pathlib.Path("TTC").rglob("*.lean")):
    forbidden = re.findall(r"\b(sorry|admit|axiom|unsafe)\b", path.read_text(encoding="utf-8"))
    if forbidden:
        raise SystemExit(f"error: forbidden token(s) {sorted(set(forbidden))} found in {path}")
print("Module headers, two Challenge placeholders, and proof-source token checks passed.")
PY

lake build
lake build Challenge Solution

if ! lake env lean --src-deps Challenge.lean >"$check_tmpdir/challenge-src-deps.txt" 2>&1; then
  cat "$check_tmpdir/challenge-src-deps.txt" >&2
  exit 1
fi
python3 - "$check_tmpdir/challenge-src-deps.txt" <<\PY
import pathlib
import re
import sys

paths = [line.strip() for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines() if line.strip()]
if not paths:
    raise SystemExit("error: lake reported no Challenge source dependencies")
bad = []
for raw in paths:
    path = pathlib.Path(raw).resolve().as_posix()
    if not (re.search(r"/src/lean/", path) or re.search(r"/.lake/packages/", path)
            or path.startswith(str(pathlib.Path.cwd().resolve()) + "/")):
        bad.append(raw)
if bad:
    raise SystemExit("error: Challenge imports source files outside the project/Lean/Mathlib allowlist:\n" + "\n".join(bad))
print(f"Challenge import-source allowlist passed ({len(paths)} source files).")
PY

python3 - "$check_tmpdir" <<\PY
import json
import pathlib
import sys

config = json.loads(pathlib.Path("comparator.json").read_text(encoding="utf-8"))
temp = pathlib.Path(sys.argv[1])
names = config["definition_names"] + config["theorem_names"]

# For the declaration-kind check, elaborate the module directly (append checks
# to the module source) rather than importing it: def bodies are not exposed
# across module imports in Lean 4 (they appear as axiomInfo), so the check
# must run in the module's own environment where they are defnInfo.
# Challenge defines the comparator definitions directly; Solution uses the
# library's copies (verified via Challenge), so Solution only checks theorems.
for module in ("Challenge", "Solution"):
    checks = temp / f"{module}Check.lean"
    src = pathlib.Path(f"{module}.lean").read_text(encoding="utf-8")
    lines = [src.rstrip(), ""]
    lines.extend(f"#check @{name}" for name in names)
    lines.extend(["", "open Lean", "", "run_cmd do", "  let env ← getEnv"])
    # Definition-kind check only for Challenge (where they are defined).
    def_names = config["definition_names"] if module == "Challenge" else []
    for name in def_names:
        lines.extend([
            f"  match env.find? `{name} with",
            "  | some (.defnInfo _) => pure ()",
            f"  | some _ => throwError \"comparator definition is not a def: {name}\"",
            f"  | none => throwError \"missing comparator definition: {name}\"",
        ])
    for name in config["theorem_names"]:
        lines.extend([
            f"  match env.find? `{name} with",
            "  | some (.thmInfo _) => pure ()",
            f"  | some _ => throwError \"comparator theorem is not a theorem: {name}\"",
            f"  | none => throwError \"missing comparator theorem: {name}\"",
        ])
    checks.write_text("\n".join(lines) + "\n", encoding="utf-8")

axioms = temp / "AxiomCheck.lean"
axiom_lines = ["import Solution", ""]
axiom_lines.extend(f"#print axioms {name}" for name in config["theorem_names"])
axioms.write_text("\n".join(axiom_lines) + "\n", encoding="utf-8")

all_axioms = temp / "AllAxiomsCheck.lean"
all_axioms.write_text("""import Solution

open Lean
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "TTC." then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "disallowed axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"All {checked} TTC declarations use only permitted axioms."
""", encoding="utf-8")
PY

lake env lean "$check_tmpdir/ChallengeCheck.lean"
lake env lean "$check_tmpdir/SolutionCheck.lean"
lake env lean "$check_tmpdir/AllAxiomsCheck.lean"

if ! lake env lean "$check_tmpdir/AxiomCheck.lean" >"$check_tmpdir/axioms.out" 2>&1; then
  cat "$check_tmpdir/axioms.out" >&2
  exit 1
fi
cat "$check_tmpdir/axioms.out"

python3 - "$check_tmpdir/axioms.out" <<\PY
import json
import pathlib
import re
import sys

config = json.loads(pathlib.Path("comparator.json").read_text(encoding="utf-8"))
output = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
allowed = set(config["permitted_axioms"])
for theorem in config["theorem_names"]:
    reports = [
        line for line in output.splitlines()
        if theorem in line and ("does not depend on any axioms" in line or "depends on axioms:" in line)
    ]
    if len(reports) != 1:
        raise SystemExit(f"error: missing or duplicate #print axioms report for {theorem}")
    report = reports[0]
    match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", report)
    axioms = set() if match is None else {name.strip() for name in match.group(1).split(",") if name.strip()}
    extra = axioms - allowed
    if extra:
        raise SystemExit(f"error: {theorem} uses disallowed axioms: {sorted(extra)}")
    actual = ", ".join(sorted(axioms)) or "none"
    print(f"Actual axioms of {theorem}: {actual}")
    print(f"Axiom audit passed for {theorem}.")
PY

comparator_status=0
lake comparator --config=comparator.json --inadvisably-no-sandbox 2>&1 | tee "$check_tmpdir/comparator.out" || comparator_status=$?
if [ "$comparator_status" -ne 0 ]; then
  echo "error: lake comparator exited with status $comparator_status" >&2
  exit "$comparator_status"
fi

git diff --check
echo "Local Palomar declaration, build, axiom, sorry, comparator, and whitespace checks passed."
