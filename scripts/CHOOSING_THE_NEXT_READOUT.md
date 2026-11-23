# Choose the next readout without eliminating an unmodeled candidate

Run `python3 scripts/plan_candidate_readouts.py --demo stream` for a next measurement, or use `--demo network` for ternary contacts. The two menus compute predictions from different typed engines. To follow an observed outcome append `--outcome yes` (stream) or `--outcome bright` (network), in the order of the successive recommended tests. These commands are advisory and never modify a candidate, baseline or history. A successful CLI exit means the planner returned a result; **even an outside-library observation is not a passing physics check**. Invalid input or an exhausted planning budget exits with code 2.

The planner minimizes worst-case total acquisition cost with a fresh preparation for each test, using only the listed controls and their declared positive costs. It can accept independent hypotheses directly:

```json
{"schema":"idt-measurement-design/1","models":["left","right","not_yet_modeled"],
 "tests":[{"id":"look","cost":1,"outcomes":["bright","dark"],
           "allows":{"left":["bright"],"right":["dark"]}}]}
```

Pass that JSON with `--spec FILE`; `--full` includes the decision graph. A missing or null prediction means **every declared outcome remains possible**. No prior or uniform distribution over an unobserved parameter is inferred. An outcome that no submitted model allows is reported explicitly, not assigned to a favored model. If planning exceeds its budget, no partial plan is labeled optimal.

The target is to separate every model pair for which some offered test has disjoint predicted outcomes. When this is impossible for a pair, both survive any observation they both permit. Overlap is not transitive: an unmodeled response can overlap a strictly bright model and a strictly dark model without making the latter two indistinguishable. The method neither enforces a winner nor treats a prediction as a measurement. It assumes each fresh preparation can realize any allowed outcome; additional constraints tying a nuisance parameter across queries require a different design.

| Preset and acquisition contract | Best fixed cost | Best worst-case adaptive cost |
| --- | ---: | ---: |
| Signed three-port stream, fresh preparation per read | 8 | 8 |
| Ternary network, fresh preparation per read | 19 | 15 |
| Same network, one deterministic trajectory with nondisturbing probes | 10 | 10 |

The first two rows are reproduced by the [predictor menus](probe_active_readout_panels.py). Costs count declared dispatch/read operations, not laboratory seconds or actual CPU speed. For the last row, the [one-run planner](probe_shared_prefix_readout_cost.py) charges shared advance only once: six contacts and four readings suffice. Some branches finish early, but adaptivity does not improve the worst case on this contract. It is a separate finite probe, not a feature silently enabled in the fresh-preparation CLI. If a probe disturbs its input, sharing the trajectory is not free: a three-port echo returns to its origin with probability 1 when unobserved and 65/81 after a specified intervening binary projective measurement. Do not use a cheap non-disturbance assumption to reject a real candidate.
