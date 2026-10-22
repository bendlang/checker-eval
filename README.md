# Bend checker eval: 20/20 vs 0/20

Can an AI write proven code? This repo measures it on 20 Bend tasks, run two ways:

- **checker**: the agent may run `bend`, Bend's proof checker, so it sees its errors and fixes them.
- **blind**: the agent can run nothing and must write the proofs in one reply.

Same model (Claude Opus 5.5), same tasks, same rules. Only access to the checker changes.

## Our result (Oct 10, 2026)

| mode    | passed | API-priced cost | slowest task |
|---------|--------|-----------------|--------------|
| checker | 20/20  | $18.24          | 636s         |
| blind   | 0/20   | $12.92          | 905s         |

Per-task records are in `results/`. Running the eval overwrites them, so `git diff` shows how your run differs.

## The tasks

Each file in `tasks/` is a small program spec: some functions and the laws they must satisfy, with the proofs missing. They come in five levels, from `cake` to `hell`. They are the evals in [bendlang/bend](https://github.com/bendlang/bend/tree/main/evals), with the solutions cut off. Every reference solution there passes `bend <file> --verdict`.

A task passes only if `bend task.bend --verdict` prints `ALL PROOFS CHECK`, the task text is unchanged, nothing in it is redefined, and no unsafe definition is used. `--verdict` rechecks everything with Bend's small proven kernel.

## Run it

You need Python 3, [Claude Code](https://docs.anthropic.com/en/docs/claude-code) logged in, and Bend:

```sh
curl -fsSL https://bend-lang.com/install.sh | sh
python3 run.py checker   # 10-20 minutes, 10 tasks at a time
python3 run.py blind
```

Each agent works in `work/<mode>/<task>/`, where you can read its file and full log (`log.jsonl`).
