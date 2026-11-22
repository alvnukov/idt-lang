# Test an actual device pair, not just a desired frequency

Supply a finite signal machine with one named rail at each state, and a
finite clock with a Boolean contact at each state. Read both outputs before
each shared step, then advance each device by its own successor. Each
machine starts at its declared state; take its reachable recurrent cycle.
The question is whether **every independent relative phase of those two
cycles** produces the calibrated square shares of a supplied neutral
integer current. A transient is reported, not asserted to obey a long-run
rate. This is not a test of all possible preparations, all clocks, an
individual photon hit, or independent trials.

For example, construct the two finite tables directly from the
[physical petal model](INTERNAL_DETECTOR_CLOCKS.md):

```sh
python3 -B -m scripts.compile_petal_clock_hypothesis --current 1 2 -1 -2 --clock matched
python3 -B -m scripts.compile_petal_clock_hypothesis --current 1 2 -1 -2 --clock ring --period 10
```

The compiler follows actual local transitions from a prepared state until
it returns to a state already seen. It registers the signal's held hub label
and the other device's actual contact, not a sequence drawn from target
weights. The matched preparation gives 2,8,2,8 counts for all phases; the
10-step ring can miss both short rails. The additional `--emit` option
produces a batch of tables for the normal screen, without certifying that
the input hardware describes a physical apparatus. The [explicit
controls](../data/periodic_contact_controls.json) retain these proposals
separately from the earlier, unassessed source descriptions.

**Why this is cheap.** If cycle lengths are m and n and g=gcd(m,n), indices
i,j occur together exactly once in a joint orbit when j−i agrees with the
initial offset modulo g. Count rail labels and clock contacts by residue
and combine those counts as a circular correlation. Sparse residues use a
direct sum; dense ones can use a single exactly packed integer product per
rail with enough space between coefficients to avoid a carry. No floating
point transform, random phase mixture or loop over lcm(m,n) is necessary.
One test exercises a joint cycle of **262,128,000 steps** without materializing
it, and separate exhaustive small-machine replays check the result against
literal joint stepping.

A counterexample names both actual states, the offset, observed integer
counts and required rational values over the joint cycle. A bounded or
expired search never certifies unchecked offsets. All successful prefix
rows are identical to the common target; they are stored as one count
vector and its multiplicity. A clock with no contacts on its reachable
cycle is undefined, not an observation of zero probability. Every signal
state must have a rail; models with missing signals at real triggers need
another contract and cannot be encoded by dropping trials.

The full API accepts up to 16,384 states in either table. CLI batch input
and immutable-history submissions have their own 128 KiB size boundary;
the larger computation API is not a promise to archive arbitrarily large
input files. The separate cache reader accepts receipts up to 512 KiB and
can replay them under matching source/runtime provenance. This is an
integrity check in a trusted cache directory, not independent attestation.
