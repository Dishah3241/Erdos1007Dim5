# Erdős 1007, dimension five: fifteen edges, attained by K6 and K1,3,3

A Lean certification of a result already solved in the human literature.

| | |
|---|---|
| Stage | 1 — statement freeze |
| Palomar entry | not yet submitted |
| `formal_proof` PR | not yet opened |
| Mathlib PR | not yet opened |
| Writeup | not yet published |

Built with the workspace at [`~/Code/Math`](../..). `AGENTS.md` holds the working rules;
`../../docs/PLAYBOOK.md` holds the pipeline.

## Gates

```sh
lake build && lake exe axioms && lake exe fidelity && lake exe module-system \
  && lake exe standalone-mathlib && lake exe proof-links && lake exe style \
  && lake exe documentation && lake exe layering && lake exe palomar-compatibility \
  && scripts/check-palomar-challenge.sh && scripts/lint-env.sh \
  && leanblueprint checkdecls && scripts/audit-probes.sh
```
