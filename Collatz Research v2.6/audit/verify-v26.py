#!/usr/bin/env python3
"""Audit exact v2.5/v2.6 source bytes and fresh compiled declarations."""
import hashlib, json, os, re, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/"full-audit-v26"
OUT.mkdir(exist_ok=True)
ENV=ROOT/"Collatz Research v2.3"
NEW=ROOT/"Collatz Research v2.6"
OLD=ROOT/"Collatz Research v2.5"
ALLOWED={"propext","Classical.choice","Quot.sound"}
DECL=re.compile(r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9']*)\b",re.M)
NS=re.compile(r"^namespace\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$",re.M)
AX=re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def run(args, log):
    p=subprocess.run(args,cwd=ENV,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding="utf-8",errors="replace")
    (OUT/log).write_text(p.stdout,encoding="utf-8")
    require(p.returncode==0 and not re.search(r"\berror:",p.stdout) and "sorryAx" not in p.stdout,log+": "+p.stdout)
    print(log+": PASS",flush=True)
    return p.stdout
def manifest(p):
    return {line.split()[1]:line.split()[0].lower() for line in (p/"SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines() if line.strip()}
def main():
    inv=json.loads((NEW/"audit/source-inventory.json").read_text())
    old=json.loads((OLD/"audit/audit-config.json").read_text())["projects"][OLD.name]
    expected={**old,**{e["file"]:e["declarations"] for e in inv}}
    require(len(old)==7 and sum(old.values())==113 and len(inv)==19 and sum(e["declarations"] for e in inv)==142,"Inventory totals")
    sources={}
    for project, files in [(OLD,old),(NEW,{e["file"]:e["declarations"] for e in inv})]:
        hashes=manifest(project)
        require(set(hashes)==set(files)=={p.name for p in project.glob("*.lean")},"Manifest/source mismatch "+project.name)
        for f in files:
            raw=(project/f).read_bytes()
            h=hashlib.sha256(raw).hexdigest()
            require(h==hashes[f],"SHA mismatch "+f)
            if project==NEW:
                require(h==next(e["sha256"] for e in inv if e["file"]==f),"Inventory SHA mismatch "+f)
            sources[f]=raw
    run(["lake","exe","cache","get"],"setup.txt")
    run(["lake","env","lean","--version"],"lean-version.txt")
    lp=run(["lake","env","printenv","LEAN_PATH"],"lean-path.txt").strip()
    require(bool(lp),"Empty LEAN_PATH")
    lp=os.pathsep.join(str((ENV/p).resolve()) for p in lp.split(os.pathsep) if p)
    deps={f:{i+".lean" for i in re.findall(r"^import\s+([A-Za-z_][A-Za-z_0-9.]*)",b.decode("utf-8-sig"),re.M) if i+".lean" in sources} for f,b in sources.items()}
    done=set(); records=[]; all_names=set()
    with tempfile.TemporaryDirectory(prefix="collatz-v26-") as tmp:
        src=Path(tmp)/"src"; build=Path(tmp)/"build";src.mkdir();build.mkdir()
        for f,b in sources.items(): (src/f).write_bytes(b)
        cmd=["lake","env","env","LEAN_PATH="+str(build)+os.pathsep+lp,"lean","--root="+str(src)]
        while len(done)<len(sources):
            ready=sorted(f for f in sources if f not in done and deps[f]<=done)
            require(bool(ready),"Dependency cycle")
            for f in ready:
                name=Path(f).stem; t=sources[f].decode("utf-8-sig")
                ns=NS.findall(t); simple=DECL.findall(t)
                require(len(ns)==1 and len(simple)==expected[f] and len(set(simple))==len(simple),"Declaration inventory "+f)
                names=[ns[0]+"."+n for n in simple]
                require(not (set(names)&all_names),"Duplicate declarations "+f)
                output=build/(name+".olean")
                run(cmd+["-o",str(output),str(src/f)],name+"-compile.txt")
                require(output.is_file() and (src/f).read_bytes()==sources[f],"Missing artifact or source changed "+f)
                driver=src/"AuditDriver.lean"
                driver.write_text("import "+name+"\n"+"\n".join("#print axioms "+n for n in names)+"\n",encoding="utf-8")
                log=run(cmd+[str(driver)],name+"-axioms.txt")
                entries=AX.findall(log)
                require(len(entries)==len(names) and {n for n,_ in entries}==set(names),"Axiom audit names "+f)
                axioms={n:sorted(a.strip() for a in v.split(",") if a.strip()) for n,v in entries}
                require(all(set(a)<=ALLOWED for a in axioms.values()),"Unexpected axioms "+f)
                records.append({"file":f,"source_sha256":hashlib.sha256(sources[f]).hexdigest(),"declarations":axioms})
                all_names.update(names);done.add(f)
    require(len(records)==26 and len(all_names)==255,"Combined module/declaration totals")
    commit=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
    (OUT/"declaration-inventory.json").write_text(json.dumps({"status":"passed","commit":commit,"modules":26,"declarations":255,"new_modules":19,"new_declarations":142,"records":records},indent=2)+"\n",encoding="utf-8")
    (OUT/"summary.txt").write_text("PASS: 26/26 combined modules; 255/255 declarations (19 new modules, 142 new declarations).\n",encoding="utf-8")
if __name__=="__main__": main()
