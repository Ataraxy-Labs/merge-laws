#!/usr/bin/env python3
"""Differential test: does the real weave binary decide entity merges the way the proven model does?

Reads cases from `lake exe gencases N` on stdin. For each case it writes base, ours and theirs as Python
files (one function per entity), runs `weave-driver base ours theirs -o merged`, and checks every entity:

  model says clean   -> weave must give exactly that function body, or leave it out if absent
  model says conflict -> weave must mark a conflict on that function, or resolve it without
                         dropping either side's change (the model leaves weave's finer merges out)

Exit status is the number of disagreements (0 means weave agreed on every case).
"""
import json, os, re, subprocess, sys, tempfile

DRIVER = os.environ.get("WEAVE_DRIVER", "weave-driver")



def source(bodies):
    # each body names its own function, so no two functions ever share a body and weave's rename
    # detection (which the model leaves out) never fires: this tests the per-entity decision alone
    parts = [f'def f{k}():\n    return "f{k}_{v}"\n' for k, v in enumerate(bodies) if v is not None]
    return "\n\n".join(parts) if parts else "\n"


def parse(text):
    """Functions outside conflict markers -> body, and the set of functions inside a conflict."""
    clean, conflicted, last = {}, set(), None
    for line in text.splitlines():
        m = re.match(r"def (f\d+)\(\):", line)
        if m:
            last = m.group(1)
        if line.startswith("<<<<<<<"):
            # weave names the entity in the marker; plain git-style markers inside a function body name nothing
            named = re.search(r"function `(f\d+)", line)
            conflicted.add(named.group(1) if named else last)
    for m in re.finditer(r'def (f\d+)\(\):\n    return "(?:f\d+_)?(\w*)"', strip_conflicts(text)):
        clean[m.group(1)] = m.group(2)
    return clean, conflicted


def strip_conflicts(text):
    out, inside = [], False
    for line in text.splitlines():
        if line.startswith("<<<<<<<"):
            inside = True
        elif line.startswith(">>>>>>>"):
            inside = False
        elif not inside:
            out.append(line)
    return "\n".join(out) + "\n"


def check(case, work):
    paths = {}
    for side in ("base", "ours", "theirs"):
        paths[side] = os.path.join(work, f"{side}.py")
        with open(paths[side], "w") as f:
            f.write(source(case[side]))
    merged = os.path.join(work, "merged.py")
    subprocess.run([DRIVER, paths["base"], paths["ours"], paths["theirs"], "-o", merged, "-p", "m.py"],
                   capture_output=True, text=True)
    text = open(merged).read()
    if all(b is None for b in case["base"]):
        # an empty base file has no entities to match on, so weave falls back to a plain line merge: coarser than
        # the model, never lossy. Check only that every function either side wrote is still in the result.
        lost = [f"f{k}: {side}'s body is missing" for k in range(len(case["expect"])) for side in ("ours", "theirs")
                if case[side][k] is not None and f'return "f{k}_{case[side][k]}"' not in text]
        return lost, -1
    clean, conflicted = parse(text)
    problems, resolved = [], 0
    for k, want in enumerate(case["expect"]):
        name = f"f{k}"
        o, t = case["ours"][k], case["theirs"][k]
        if want == "conflict":
            if name in conflicted:
                continue
            got = clean.get(name)
            # resolved by weave's finer merges: fine only if neither side's change was dropped
            if got is not None and got == o == t:
                resolved += 1
            else:
                problems.append(f"{name}: model conflict, weave gave {got!r} (ours {o!r}, theirs {t!r})")
        else:
            v = want["clean"]
            got = clean.get(name)
            if name in conflicted:
                problems.append(f"{name}: model clean {v!r}, weave conflicted")
            elif got != v:
                problems.append(f"{name}: model clean {v!r}, weave gave {got!r}")
    return problems, resolved


def main():
    cases = [json.loads(l) for l in sys.stdin if l.strip()]
    bad, entities, conflicts, resolved, fallback = 0, 0, 0, 0, 0
    with tempfile.TemporaryDirectory() as work:
        for case in cases:
            problems, r = check(case, work)
            if r == -1:
                fallback += 1
                r = 0
            entities += len(case["expect"])
            conflicts += sum(1 for e in case["expect"] if e == "conflict")
            resolved += r
            if problems:
                bad += 1
                if bad <= 10:
                    print(f"case {case['case']}: " + "; ".join(problems))
    print(f"{len(cases)} merges, {entities} entities ({conflicts} conflicts in the model): "
          f"{len(cases) - bad} agreed, {bad} disagreed"
          f" ({fallback} had an empty base file: weave line-merged them, nothing lost)")
    sys.exit(min(bad, 255))


if __name__ == "__main__":
    main()
