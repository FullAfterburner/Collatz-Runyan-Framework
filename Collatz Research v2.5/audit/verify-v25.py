#!/usr/bin/env python3
"""Compile exact staged source bytes, then inspect axioms of imported compiled declarations."""
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import traceback

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "full-audit-v25"
OUT.mkdir(exist_ok=True)
CONFIG = json.loads(Path(__file__).with_name("audit-config.json").read_text())
PROJECTS = CONFIG["projects"]
NEW = "Collatz Research v2.5"
OLD = "Collatz Research v2.4"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9']*)\b", re.M)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$", re.M)
AXIOM = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
records = []
checks = []

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def run(args, cwd, logfile):
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
    (OUT / logfile).write_text(p.stdout, encoding="utf-8")
    print(f"{logfile}: exit {p.returncode}", flush=True)
    if p.returncode or re.search(r"\berror:", p.stdout) or "sorryAx" in p.stdout:
        print(p.stdout, flush=True)
        raise RuntimeError(f"Lean or setup failure: {logfile}")
    return p.stdout

def manifest(project):
    return dict(
        (line.split(maxsplit=1)[1].strip(), line.split(maxsplit=1)[0].lower())
        for line in (ROOT / project / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines()
        if line.strip())

def ordered(project, files):
    # Local import edges derived from source; external Mathlib imports are supplied by Lake.
    names = {Path(f).with_suffix("").as_posix().replace("/", "."): f for f in files}
    imports = {}
    for f in files:
        txt = (ROOT / project / f).read_text(encoding="utf-8-sig")
        imports[f] = [names[i] for i in re.findall(r"^import\s+([A-Za-z_][A-Za-z_0-9.]*)", txt, re.M)
                      if i in names]
        if project == NEW:
            actual = re.findall(r"^import\s+([A-Za-z_][A-Za-z_0-9.]*)", txt, re.M)
            require(all(i == "Mathlib" or i in names for i in actual), f"Unexpected import: {f}: {actual}")
    done = []
    while len(done) < len(files):
        ready = [f for f in files if f not in done and set(imports[f]) <= set(done)]
        require(bool(ready), f"Dependency cycle in {project}: {imports}")
        done.extend(ready)
    return done, imports

def audit_project(project, files, env_project, scratch, leanpath):
    source_root = scratch / "sources"
    build_root = scratch / "oleans"
    source_root.mkdir(parents=True)
    build_root.mkdir(parents=True)
    order, edges = ordered(project, files)
    (OUT / (project+"-dependencies.json")).write_text(json.dumps({"order":order,"imports":edges},indent=2)+"\n")
    for file in order:
        source = source_root / file
        source.parent.mkdir(parents=True, exist_ok=True)
        raw = (ROOT / project / file).read_bytes()
        source.write_bytes(raw)
        module = Path(file).with_suffix("").as_posix().replace("/", ".")
        output = build_root / Path(file).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        txt = raw.decode("utf-8-sig")
        ns = NAMESPACE.findall(txt)
        simple = DECL.findall(txt)
        require(len(ns) == 1 and len(simple) == files[file] and len(set(simple)) == len(simple),
                f"Unexpected declaration inventory: {project}/{file}")
        names = [ns[0]+"."+n for n in simple]
        if project == NEW:
            require(names == CONFIG["new_names"][file], f"New declaration names differ: {file}")
        # Lake supplies Mathlib paths; prepend only freshly generated local artifacts.
        command = ["lake", "env", "env", "LEAN_PATH="+str(build_root)+os.pathsep+leanpath,
                   "lean", "--root="+str(source_root)]
        tag = project+"-"+Path(file).stem
        run(command+["-o",str(output),str(source)], env_project, tag+"-compile.txt")
        require(output.is_file() and source.read_bytes()==raw, f"Missing artifact or changed source: {file}")
        driver = source_root / "AuditDriver.lean"
        driver.write_text("import "+module+"\n"+"\n".join("#print axioms "+n for n in names)+"\n",
                          encoding="utf-8")
        log = run(command+[str(driver)],env_project,tag+"-axioms.txt")
        entries = AXIOM.findall(log)
        require(collections.Counter(n for n,_ in entries)==collections.Counter(names),
                f"Unexpected axiom output names/count: {project}/{file}")
        dependencies = {n:sorted(a.strip() for a in ax.split(",") if a.strip()) for n,ax in entries}
        unexpected = {a for ax in dependencies.values() for a in ax}-ALLOWED
        require(not unexpected,f"Unapproved axioms {unexpected}: {file}")
        records.append({"project":project,"file":file,"source_sha256":digest(raw),
                        "compiled_sha256":digest(output.read_bytes()),"declarations":dependencies})
        print(f"PASS {project}/{file}: {len(names)} declarations",flush=True)

def main():
    require(sum(len(v) for v in PROJECTS.values())==43,"Config module total")
    require(sum(sum(v.values()) for v in PROJECTS.values())==418,"Config declaration total")
    source_commit = CONFIG["baseline_source_commit"]
    inventory_commit = CONFIG["baseline_inventory_commit"]
    baseline_path = OLD + "/audit/declaration-inventory.json"
    baseline = json.loads(git("show",inventory_commit+":"+baseline_path))
    require(len(baseline["entries"])==305,"Published inventory count")
    require((ROOT / baseline_path).read_bytes()==git("show",inventory_commit+":"+baseline_path),
            "Published baseline inventory modified")
    for project, files in PROJECTS.items():
        if project != "Lean Proofs":
            require({p.name for p in (ROOT/project).glob("*.lean")}==set(files),f"Source file set differs: {project}")
        for file in files:
            raw=(ROOT/project/file).read_bytes()
            if project==NEW:
                require(digest(raw)==CONFIG["new_sha256"][file],f"Authoritative SHA mismatch: {file}")
            else:
                require(raw==git("show",source_commit+":"+project+"/"+file),f"Baseline source changed: {project}/{file}")
            checks.append({"project":project,"file":file,"sha256":digest(raw)})
    for project in [OLD,NEW]:
        m=manifest(project)
        require(set(m)==set(PROJECTS[project]),f"Manifest source set mismatch: {project}")
        for f,h in m.items():
            require(digest((ROOT/project/f).read_bytes())==h,f"Manifest SHA mismatch: {project}/{f}")
    for project in ["Lean Proofs","Collatz Research v2.3"]:
        for f in ["lean-toolchain","lakefile.toml","lake-manifest.json"]:
            require((ROOT/project/f).read_bytes()==git("show",source_commit+":"+project+"/"+f),
                    f"Baseline environment changed: {project}/{f}")
    (OUT/"source-checks.json").write_text(json.dumps(checks,indent=2)+"\n")
    print("PASS 43 source identities and both versioned manifests",flush=True)
    environments={}
    for project in ["Lean Proofs","Collatz Research v2.3"]:
        cwd=ROOT/project
        run(["lake","exe","cache","get"],cwd,project+"-setup.txt")
        run(["lake","env","lean","--version"],cwd,project+"-lean-version.txt")
        leanpath=run(["lake","env","printenv","LEAN_PATH"],cwd,project+"-lean-path.txt").strip()
        require(bool(leanpath),"Empty Lake LEAN_PATH")
        # Resolve relative entries against the environment project.
        environments[project]=os.pathsep.join(str((cwd/p).resolve()) for p in leanpath.split(os.pathsep) if p)
    with tempfile.TemporaryDirectory(prefix="collatz-v25-") as temp:
        for idx,(project,files) in enumerate(PROJECTS.items()):
            env_project=project if project in environments else "Collatz Research v2.3"
            audit_project(project,files,ROOT/env_project,Path(temp)/str(idx),environments[env_project])
    combined={}
    old={}
    for record in records:
        for n,ax in record["declarations"].items():
            require(n not in combined,f"Duplicate declaration: {n}")
            combined[n]=ax
            if record["project"]!=NEW:
                old[n]=ax
    published={e["name"]:sorted(e["axioms"]) for e in baseline["entries"]}
    require(old==published,"Fresh v2.4 axiom inventory differs from published baseline")
    require(len(records)==43 and len(combined)==418,"Final module/declaration count")

if __name__ == "__main__":
    status="failed"
    failure=""
    try:
        main()
        status="passed"
    except Exception:
        failure=traceback.format_exc()
        print(failure,flush=True)
    finally:
        total=sum(len(r["declarations"]) for r in records)
        result={"status":status,"source_commit":git("rev-parse","HEAD").decode().strip(),
                "modules":len(records),"declarations":total,"allowed_axioms":sorted(ALLOWED),
                "records":records,"failure":failure}
        (OUT/"declaration-inventory.json").write_text(json.dumps(result,indent=2)+"\n")
        summary=f"{status.upper()}: {total}/418 declarations, {len(records)}/43 modules\n"
        (OUT/"summary.txt").write_text(summary+failure)
        print(summary,flush=True)
    if status!="passed":
        raise SystemExit(1)
