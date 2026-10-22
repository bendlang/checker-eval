#!/usr/bin/env python3
# python3 run.py MODE [PARALLEL]
#
# Gives each of the 20 tasks in tasks/ to one Claude Code agent (Opus 5.5) and grades it.
# MODE "checker": the agent may run `bend`, so it can check its proofs and fix them.
# MODE "blind":   the agent can run nothing; it must write the proofs in one reply.
# Pass: `bend task.bend --verdict` prints ALL PROOFS CHECK, the task text is unchanged at
# the top, nothing in it is redefined, and nothing is unsafe. Writes results/MODE.json.
import json, os, re, subprocess, sys, concurrent.futures as cf, time

MODE = sys.argv[1]
PAR  = int(sys.argv[2]) if len(sys.argv) > 2 else 10
HERE = os.path.dirname(os.path.abspath(__file__))
assert MODE in ("checker", "blind")

RULES = ("Below is task.bend, a Bend 2 file. Bend is a proof language. Complete the file so that "
         "`bend task.bend --verdict` prints ALL PROOFS CHECK: prove every law whose proof is missing. "
         "Append your definitions after the existing text: do not change, remove or redefine anything "
         "already in the file, and do not use unsafe definitions. ")
DO = {
  "checker": "The file is in your current directory. You may run only `bend`. Stop when the verdict passes.",
  "blind":   "You cannot run anything: reply with ONLY the text to append, in one ```bend code block.",
}
TOOLS = {
  "checker": ["--allowedTools", "Bash(bend:*)", "Read", "Edit", "Write",
              "--disallowedTools", "Glob", "Grep", "WebFetch", "WebSearch", "Task"],
  "blind":   ["--disallowedTools", "Bash", "Read", "Edit", "Write", "Glob", "Grep", "WebFetch", "WebSearch", "Task"],
}

def names(text):
  return re.findall(r"^(?:def|law|type)\s+([A-Za-z_][\w.]*)", text, re.M)

def cheat(task, out):
  if not out.startswith(task): return "edited the task"
  rest = out[len(task):]
  if re.search(r"^def\s+[\w.]+\?", rest, re.M) or "unsafe" in rest: return "unsafe"
  laws = set(re.findall(r"^law\s+(\w+)", task, re.M))
  for n in names(rest):
    if n in names(task) and n not in laws: return "redefined " + n
  return None

def one(f):
  d = os.path.join(HERE, "work", MODE, f[:-5])
  os.makedirs(d, exist_ok=True)
  task = open(os.path.join(HERE, "tasks", f)).read()
  file = os.path.join(d, "task.bend")
  open(file, "w").write(task)
  t0 = time.time()
  cmd = ["claude", "-p", "--model", "claude-opus-5-5", "--effort", "high", "--max-turns", "60",
         "--output-format", "stream-json", "--verbose", *TOOLS[MODE]]
  try:
    log = subprocess.run(cmd, input=RULES + DO[MODE] + "\n\ntask.bend:\n\n" + task,
                         capture_output=True, text=True, cwd=d, timeout=1500).stdout
  except subprocess.TimeoutExpired as e:
    log = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
  open(os.path.join(d, "log.jsonl"), "w").write(log)
  result = [json.loads(l) for l in log.splitlines() if l.startswith("{") and '"type":"result"' in l]
  if MODE == "blind":
    reply = result[-1].get("result", "") if result else ""
    code = re.findall(r"```(?:bend)?\n(.*?)```", reply, re.S)
    open(file, "w").write(task + "\n" + (code[-1] if code else ""))
  why = cheat(task, open(file).read())
  v = subprocess.run(["bend", "task.bend", "--verdict"], cwd=d, capture_output=True, text=True, timeout=300)
  rec = {"task": f, "pass": why is None and "ALL PROOFS CHECK" in v.stdout + v.stderr, "why": why,
         "secs": round(time.time() - t0), "cost_api_usd": result[-1].get("total_cost_usd") if result else None}
  print(json.dumps(rec), flush=True)
  return rec

with cf.ThreadPoolExecutor(PAR) as ex:
  recs = list(ex.map(one, sorted(os.listdir(os.path.join(HERE, "tasks")))))
json.dump(recs, open(os.path.join(HERE, "results", MODE + ".json"), "w"), indent=1)
print(MODE, "PASS", sum(r["pass"] for r in recs), "/", len(recs))
