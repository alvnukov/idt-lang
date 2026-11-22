# Autonomous programs and finite memory

These two probes separate supplied operational resources from consequences of
those resources. They provide exact finite controls and analytical arguments,
not new Lean proofs or changes to claim statuses. Neither derives a physical
runtime law, preparation, Born readout, tensor composition, or quantum mechanics.

## A fixed law still needs a program–data interaction

[The autonomous-program probe](probe_autonomous_mixer_program.py) contrasts two
different input contracts.

An independently prepared **additive pilot** under fixed linear propagation,
fixed elapsed evolution and fixed output has `y_p(x) = A x + b_p`. Its odd
response, `(y_p(x) - y_p(-x))/2`, is always `A x`, regardless of the pilot.
It cannot select a different linear transformation of unknown data. Uniform
errors on both signs obey `||U_p - U_q|| <= epsilon_p + epsilon_q`. The sharp
common errors are `1` for identity/swap and `1/sqrt(2)` for identity/native
mixer. Testing only one input can conceal this: the exact counterfeit passes
that input, has squared vacuum output `1/2`, and has squared error `2` on its
negative. These are amplitude-frame comparisons, not normalized click tables.

A **joint configuration control** is different. Orthogonal clock/tape states
and unknown data start as a product. One fixed reversible rule advances the
clock, rotates a binary tape, and conditionally applies the same native mixer
to the scanned neighboring pair. No list of target matrices is installed in
the update law. The prepared tape selects collisions; zeros idle. The probe
checks 64 tapes at three starting clock positions: 192 six-tick cases.

- `110000` gives `T12 T01`; `010100` gives `T01 T12`.
- Both return their clock and tape after six ticks and act on arbitrary data.
- Twelve ticks repeat the word; they do not halt it.
- A four-bit tape can return while the three-position scanner does not.
- An extra enabled collision is not identity padding.

The positive construction supplies an interaction between program and data;
additive pilots do not produce that interaction. Exact deterministic programs
for unitaries inequivalent up to phase must be orthogonal under the stated
isometry/returned-program contract. Superposing enable bits generally entangles
the data with the program; the checked control has reduced data purity `3/4`.

Program preparation, growing storage, synchronization, readout timing and a
possible halting latch remain resources. Tape rotation is local in tape
geometry, and clock/data translation covariance is checked. Neither establishes
a fully local homogeneous one-dimensional cellular automaton: the spatial
conditional collision and its registration still need an implementation.
Scanner ticks count abstract updates, not a derived physical execution time.

## A depth trace tests a specified memory cap

[The Markov-spectrum probe](probe_native_markov_spectrum.py) supplies the centered
ray `(1,-1,0)/(1+i)`, the word `D = T12 T01`, and the calibrated squared-amplitude
return readout. Its exact sequence is

`p_t = (4 + 3 cos(t omega))/7`, with `cos(omega) = 1/8`.

The first three returns are `1, 5/8, 5/32`. The comparison class is one fixed
homogeneous real stochastic model `q_t = mu P^t r`: at most `d` complete states,
one preparation `mu`, one row-stochastic transition `P`, and one response
`r` in `[0,1]^d`, unchanged with requested depth. A visible three-port carrier
does not establish a three-state bound on the complete classical apparatus.
Uncounted clocks, intermediate measurements, selection, or depth-dependent
preparations/transitions/responses change this contract.

Put `Delta_d^2 = min_{1 <= j <= d} |1 - exp(i j omega)|^2`. The analytical
resolvent argument gives the exact-rational finite-window certificate

`max_{0 <= t < L} |p_t - q_t| >= 3/14 - (4d(d+1)/Delta_d^2 + 8/7)/L`.

The sufficient lengths below make this bound at least `1/10`.

| Complete-state cap `d` | Depth values `L` | Largest depth `L-1` |
|---:|---:|---:|
| 1 | 50 | 49 |
| 2 | 130 | 129 |
| 3 | 250 | 249 |
| 4 | 2,855 | 2,854 |
| 8 | 10,250 | 10,249 |
| 16 | 2,785,886 | 2,785,885 |
| 32 | 10,815,761 | 10,815,760 |
| 64 | 42,607,512 | 42,607,511 |

These are conservative design certificates, not minimum necessary depths or
runtime estimates. The code computes their rational bounds, not millions of
experimental trials. In particular, a separate two-state inequality already
excludes uniform error at most `1/10` on the first **three** depths; its interval
gap is `31/1600`. Exact agreement for a `d`-state model is impossible on the
first `d+2` depths, but the supplied general quantitative bound there is tiny.
The distinct all-time analytical optimum is error `3/7`, attained by the
constant response `4/7`; it is not inferred merely from the finite table.

**Depth is not a repeated shot.** Depth `t` means `t` applications of `D` within
a preparation/readout protocol. Repeating shots at the same depth estimates
one return probability; it does not extend the depth window. No shot budget,
confidence interval, independence of shots, or experimental rate is supplied.

The boundary controls are constructive. Any requested prefix `0,...,M` is
fitted exactly by an `M+1`-state absorbing clock with the supplied table stored
in its response; it then stays at the last value. Two states with a different
reset transition at each depth also fit the trace. Thus no single finite trace
excludes every finite-memory model. A prepared autonomous program or clock is
part of the memory to be counted, not a free exemption from the state cap.

## Reproduction

```bash
python3 -B -m scripts.probe_autonomous_mixer_program
python3 -B -m scripts.probe_native_markov_spectrum --json
python3 -B -m unittest tests.test_autonomous_program_and_memory
python3 -B -O -m unittest tests.test_autonomous_program_and_memory
```

The independent tests compare a rational cosine recurrence with native returns,
recompute each design-length certificate, and exercise the pilot, program,
clock and depth-dependent-reset boundaries. They do not validate a physical
memory cap or promote these conditional controls to a universal theory claim.
