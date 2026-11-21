# What selects the mixer and the square?

**Conditional result:** in the smallest signed-integer architecture with
transparent two-step exchange, a nonzero nonnegative stock that adds over
raw channels and has one common gain selects both the mixer (up to
orientation) and the square count. The stock need not be integer, faithful
on every input, sign-symmetric, identical on different channels, or
polynomial. No metric or probability table enters this argument.

This is an argument plus [exact finite probes](probe_separable_event_stock.py),
not a new Lean theorem, an empirical determination of the microscopic
architecture, or a derivation of measurement. See the [whole-event
experiment](ROUTED_EVENT_CANDIDATE.md) for the separate sampling step.

The [stronger port-only result](PORT_STOCK_ORIGIN.md) derives the weight
up to an integral change of basis without assuming internal separability.
The finite-difference route below independently tests *named raw channels*.

### Inputs that matter

Two addressable ports each carry d signed integers. Giving every token the
same substitution, respecting cancellation and concatenation, makes the net
update an integer matrix M. Require M² = r²S, where S swaps ports, and
M(z,z) = r(z,z), for a positive integer scale r. Commutation with S gives
M = [A,B; B,A], with A+B = rI and (A−B)² = −r²I. Hence
2A²−2rA+r²I = 0; reducing modulo two gives even r, and taking the
determinant of ((A−B)/r)² gives even d. The first possible positive pair
is r=d=2. Choosing that minimum is a research preference. The
[raw-table check](probe_raw_gate_reconstruction.py) treats this separately
from reconstruction of a turn on the contrasts between ports.

At this minimum A=I+J, B=I−J, J²=−I. Such a real two-dimensional J has
characteristic polynomial t²+1, so write J=[a,b;c,−a], with bc=−1−a².
Allow four unrelated functions on signed integers and let F(q)=Σⱼ fⱼ(qⱼ).
Assume fⱼ(0)=0, fⱼ≥0, F is nonzero somewhere, and F(Mq)=hF(q) with
one positive gain h for all integer inputs. **Separability is a substantive
premise:** adding probabilities of exclusive outcomes does not imply that
each raw contribution depends only on its own count. Counting only by
output *port* does not require separability of its two internal channels.

### Exclude a sheared turn without giving the channels a metric

Symmetrize F over port exchange and simultaneous sign reversal. Its
one-port contribution is E(x,y)=u(x)+v(y), with u,v even, nonnegative
and zero at zero. Equal-port and opposite-port inputs give E(2z)=hE(z)
and E(2Jz)=hE(z). Thus E(Jz)=E(z).

There is a short argument for faithful integer stocks. If a≠0 then any
nonzero axis input splits under J into **two** nonzero axes. Repeat this
on each summand of its unchanged separable stock. A finite starting count
would dominate 2ᵏ positive integers at every depth k. Impossible.

For possibly dark, real-valued stocks more care is needed. Suppose a≠0;
take L=|abc|=|a|(1+a²). Take a rectangular difference of E(z)=E(Jz) along
the two input axes. The left side vanishes. On the right is a mixed
difference of u(X) plus one of v(Y), with (X,Y)=Jz ranging independently
over the integer lattice. Each difference is therefore constant. Choosing
input increments L/a,L/b gives constant second difference of u at step L;
choosing L/c,−L/a does the same for v. Evenness and their values at zero
give u(Ln)=n²u(L), v(Ln)=n²v(L). Invariance on each axis now says
u(L)=a²u(L)+c²v(L), v(L)=b²u(L)+a²v(L). Hence u(L)=v(L)=0.
Both second differences vanish everywhere. A two-sided affine sequence
that stays nonnegative is constant. Thus u,v are periodic with period L.

They cannot both be zero, since the symmetrization sums nonnegative stocks.
Their finite range and doubling law force h=1. Write L=2ˢm with m odd;
doubling s times shows both functions have period m. Both 1+a and 1−a
are units modulo m: any common odd prime factor with a(1+a²) would have
to divide 2. On the first raw axis the original symmetrized gain law gives
u(n) ≥ u((1+a)n)+u((1−a)n). Summing over a period forces u to be zero,
since both multipliers permute the residues. The other axis gives the same
contradiction for v. This last test uses individual ports, not just paired
and antipaired preparations.

### Identify the stock without assuming a sign or orientation

Now a=0, bc=−1: there are just two integral turns. Their raw matrices
H and Hᵀ have entries ±1. Apply the gain to both signs of one input
axis. At a given magnitude n put sⱼ=fⱼ(n)+fⱼ(−n). Then h sⱼ = Σᵢ sᵢ.
A nonzero stock gives h=4, and the sign sums agree at every magnitude.
The odd parts satisfy Mᵀd=4d. Squaring gives 4Sd=16d, impossible unless
d=0. All four functions are therefore the same even f. Two distinct
columns agree in two rows and disagree in two rows. Hence
f(x+y)+f(x−y)=2f(x)+2f(y). Taking y=1 gives **f(n)=κn²** with one
undetermined positive scale κ. This selects a weight, not the physical
choice of a single result with probability proportional to it.

### How to catch a false positive

- The inverse computation treats the positive and negative responses of
  each rail independently. For each orientation 296 equations on 80 unknown
  values (signed magnitudes up to 10) have rank 79 modulo 101; the explicit
  integer null vector bounds the rational rank above. Only the square
  survives on this interval. A decoder altered beyond it passes the
  **entire** finite inverse check. Independent four-rail points test direct
  conservation; not all are outside the calibration family.
- A shear of the two internal coordinates preserves a positive stock with
  a within-port cross term exactly. A globally nonseparable square of the
  total square stock scales by 16; a signed sum scales by 2 for every
  root. A four-cycle counting ordinary marks loses transparency. These
  are genuine competitors if the respective assumptions are dropped.
- A mod-five detector for J=[7,5;−10,−7] can accept doubling and all equal-
  and opposite-port controls while failing a single-port exposure. Testing
  only the highly symmetric preparations is inadequate.

Existing Lean results address [transparent reconstruction](../Proofs/QMClosure/TransparentSwapRoot.lean),
[a conserved common port readout](../Proofs/QMClosure/PositiveMixerQuadraticReadout.lean),
and [quadratic selection on Gaussian integers](../Proofs/QMClosure/GaussianIntegerQuadraticSelection.lean).
Here the question is different: which *raw integral table and four
initially unspecified channel responses* can coexist at minimal size?
