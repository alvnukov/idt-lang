# What can an observer at the detector actually count?

The [one-marker detector](SINGLE_EVENT_ORIGINS.md) makes a definite circuit
through every live channel. Following every microscopic hop of a prepared
walker gives square shares. An observer at the hub does **not** see every
microscopic hop. These finite probes distinguish the observation protocols;
none establishes a physical trigger or an independent single-event law.

## A clock and a register at one junction

On a passage from port i to j, exchange names i and j in a single register
held at the hub. Between passages the register is untouched. A known first
departure suffices to align it with the travelling cursor; no subsequent
message from a distant vertex is required. The register update is reversible
even on a *wrong* initial name, and consequently does not repair that name.
We assume stable port identities and a passive record of local readouts.

On unary lengths (2,1,3), counting all hops, hub returns and changes of rail
gives **(16,4,36), (2,1,3), and (1,1,1)** respectively. This ambiguity is
present even on precisely the same prepared orbit.

Give the observer an independent pulse moving on a simple even ring of h
edges at the same hop rate as the signal. Read the register whenever this
pulse returns to its local contact. On the active signal orbit rail i has a
single contiguous block of length t_i = 4 v_i², and T is their sum. Over one
joint period the clock sees exactly one residue class modulo gcd(T,h).
It gives the intended fractions for every starting phase **if and only if**
this gcd divides every t_i. Necessity follows already from integrality of
the required counts. Sufficiency uses the *contiguous blocks*, not just
their sizes. No averaging over unknowable phases is allowed.

The [local-clock probe](probe_internal_detector_clocks.py) finds that h=10
works for every neutral integer triangle. With four occupied channels,
(1,2,−1,−2), the very same clock instead reads **(0,2,0,2)** or **(1,1,1,1)**
in its four contacts. The intended proportions are 1:4:1:4. Adding an empty
fourth port to a triangle does not cause this failure.

**Conditional arithmetic classification.** Write a neutral triangle as
k(a,b,−a−b) with a,b coprime. Then T = 8 k²(a²+ab+b²), while the gcd of
the individual block lengths is 4 k². The quadratic factor is odd. Its odd
prime divisors are 3 or 1 modulo 3: except at 3, a root of x²+x+1 modulo p
is a nontrivial cube root of unity, and conversely every prime 1 modulo 3
has such a root. Neither a nor b can vanish modulo a divisor of the factor
without the other doing so. Thus a ring works on **every** triangle exactly
when 8 and 3 do not divide h and every odd prime divisor of h is 2 modulo 3.
Among physical even periods from 4 to 32 these are 4, 10, 20 and 22.

With four or more rails the only universal simple even ring in this family
has h=4. For each odd prime p, choose x,y modulo p with x²+y²=−1: the sets
of squares and of −1 minus a square both have size (p+1)/2 and intersect.
The invertible change (x,y,1)=(a+b,a+c,b+c) then makes the sum of squares
of (a,b,c,−a−b−c) zero modulo p, without all four entries being zero modulo
p. A multiple of eight fails even for (1,−1,0,0). Zeros extend these
countercontrols to more ports. The script constructs witnesses rather than
sampling opinions about primes. This calculation is not a Lean proof or a
restriction on clocks other than the specified ring and timing rule.

## A clock made from a second copy of the same process

[The matched clock](probe_matched_vernier_petals.py) takes another copy of
the unary apparatus with its own active marker. Insert just two relay
vertices in **one wire carrying lane 1** on a distinguished reference petal.
The moving mark passes that particular wire once per complete tour: on a
petal of n edges, cycling its n bit positions through n laps presents the
mark to each logical edge once. Both traversal directions work. There is
one marked departure from the distinguished petal per reference tour; use
that local port as the only trigger. Both walkers still traverse an actual
reciprocal edge at every step. There is no remote stop signal.

The duplicate has period T+2, *without a device measuring T or storing a
rate*. Since gcd(T,T+2)=2 and every t_i is a multiple of four, one observer
at the common hub sees the square proportions whatever the two starting
phases or number of occupied rails. For the four-channel example the two
periods are 40 and 42. **All 20 triggers** in 840 elementary hops give
**(2,8,2,8)**. Undetuned identical copies instead always sample the same
channel. A mismatched two-rail copy, a trapped marker that never triggers,
or an unsuitable relative hop speed does not have this guarantee.

This removes phase selection, **not** the need to prepare two matched unary
structures at the same speed. It neither copies an unknown quantum state
nor guarantees a click for a freely chosen external trigger. Self-timed
rates, arbitrary laboratory cadence, independent trials and absorption of
one quantum of energy are different requirements.

## What if the stimuli have a fixed external cadence?

The [externally driven comparison](probe_trigger_carry_slip.py) answers once
at **every** stimulus, even during startup. Normally the main apparatus
moves h hops between stimuli. A reference advances only on stimuli; once per
reference tour M it commands the main apparatus to hold for one background
step. Two equal-delay trees distribute the clock-enable signals to the
actual vertices. This is additional hardware, not action by the bare hub at
a distance. Its reversibility is not assumed.

Each group of M fixed intervals advances the signal by Mh−1 steps. If every
prime factor of T divides M, this increment is coprime to T for *every*
positive h; an active matched clone supplies M=T. Each recurrent starting
phase is visited, even for h=T. For T=56 the full 3,136 replies give
896:224:2,016. This guarantee does **not** apply to a short run: at h=56
there can be 2,912 intervening stimuli between two replies on the rare
rail. Variable intervals can defeat it altogether. This device trades
the matched passive clock's input-dependent reporting period for driven
control and memory, not for independent trials.

Not all jitter is equivalent. In the [repeated-calendar probe](probe_calendar_carry_alias.py),
if P gaps sum to H and g=gcd(P,M), the phase advance after a full common
calendar block is (M/g)H−P/g. Full phase coverage at each fixed calendar
and reference residue requires this advance to be coprime to T. A failure
need not bias every coarse channel count. With T=M=8 and two equally sized
rails, alternating gaps 1,2 yield 32:32 for every phase, whereas seven gaps
of length one followed by one gap of length two can give 3:5, 4:4 or 5:3.
Neither calendar uses detector outputs or knows the starting phase.

## Alternative starting directly from raw occurrences

[Two circulating occurrence lists](probe_coprime_signed_encounters.py) use
the raw input twice, with one idle cell added to the second ring. Lengths
L and L+1 force every ordered raw pair to meet over time with no list of
pairs or precomputed squared weights. Opposite signs on the same rail
incur debt; matching signs repay debt before generating a click. An entire
first tour is counted as preparation. After this, the net clicks on a rail
are its signed occurrence sum squared. Null encounters, repayments and
silence count against the clock, rather than disappearing from the sample.

On the triangle the result is 0:8 or 6:2, but only **8 of 72** ticks click.
On a joint fixture it is **256 of 65,792**. An outstanding serial request
can take the next click; a fixed-time stimulus cannot count on one. A dark
channel can click during unprimed startup. A changed input can invalidate
the old debt. Duplication, synchronized strides, sign/rail comparison,
priming and bounded-for-fixed-input memory are still supplied.

Run the five probes with
`python3 -B -m scripts.replay_primitive_probe_campaign --bundle local_observer_clocks`.
Their [candidate inventory](../data/primitive_observer_clock_inventory.json)
retains each route separately, including the assumptions that can change
the outcome.
