# Stationary tripler readout selection

## Checked conditional theorem

On the literal initial carrier P4, let `E` be its canonical complex evaluation,
`N(p)=Complex.normSq(E(p))` and `c=2*a*b`. The contract has five supplied
premises for a real response `W`

1. `W(1)=1`.
2. `W(a*p)+W(b*p)=W(p)` for every preparation.
3. `W(c*p)>=W(p)` for every preparation.
4. With `B(n,m)=n*a+m*b`, natural `n<=n'`, `m<=m'` and every `p` imply
   `W(B(n,m)*p)<=W(B(n',m')*p)`.
5. `W(3*p)=W(3)*W(p)` for every preparation.

`InitialStationaryTriplerSelection.selected` gives `W(p)=N(p)` on every
actual preparation. `norm_model` and `exists_unique_response` establish
an inhabited, unique response model under this contract. [Lean source](../Proofs/QMClosure/InitialStationaryTriplerSelection.lean)

The fixed multiplier is the coherent term `3*p=p+p+p`, acting on every
input. Stationary numerical gain is a supplied readout hypothesis.
Physical implementation of the coherent multiplier requires an independent
bridge. Physical copying and independent repetitions retain their own contracts.

## Gain calibration and selection

`InitialStationaryTriplerCountCalibration.tripler_gain` obtains `W(3)=9`.
Its `natural_gain` gives `W(j*p)=j^2*W(p)` for every natural count `j` and
every preparation. Exact doubling, `c` invariance and positive dyadic
scaling are part of the count-calibration route. [Lean source](../Proofs/QMClosure/InitialStationaryTriplerCountCalibration.lean)

`InitialCountHomogeneousReadoutSelection.evaluation_extensional` obtains
equal responses from equal `E` coordinates. The count-homogeneous geometry
then selects the norm-square response. [Lean source](../Proofs/QMClosure/InitialCountHomogeneousReadoutSelection.lean)

The proof extends the response mathematically through rational coordinates
and a continuous complex-coordinate construction. This extension is a
proof device. Physical availability of limit preparations and a completed
state space require independent bridges. Continuity of this mathematical
extension, radial factorization and gain nine are obtained in the argument.

The final package also proves global response multiplicativity,
same-preparation square response, paired echo and null insertion after
selection.

## Process and origin boundary

The preceding dyadic detector countercontrol in section 219 has a faithful
literal coefficient action, exact serial composition, a continuous response
and all native branch-word gains. Its response still fails numerical
self-squaring and norm selection. Exact process composition leaves the
additional detector-gain bridge visible. [Section 219](219-dyadic-detector-process-boundary.md)

Under the four base laws, both square and stationary-tripler contracts
select the same numerical model. Their operational premises concern
different process promises. The tripler result concerns one fixed coherent
multiplier with a universal input-domain law.

The literal P4 carrier and its geometry remain supplied. Physical origins
of the additive preparation interface, column conservation, full prepared
count order, oriented `c` comparison and stationary tripler response remain
open. Born actualization, Hilbert reconstruction, full QM, GR and
physical-scale origins remain open.
