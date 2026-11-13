# Classical finite phase and joint-readout boundary

Two conditional kernels describe a classical representation of the finite phase
algebra and a positivity obstruction for a proposed additional transformation.
Their ledger entries carry `conditionalKernelTheorem` and
`parentAccepted` after independent review and the shared dependency audit.
The local ambient base consists of all
nonnegative rational distributions of total one on four classical points. The
joint ambient base contains all such distributions on sixteen ordered pairs.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Exact finite-carrier identities

Write a local point as `(q,p)` in `Bool × Bool`. The three phases permute these
points by flipping `q`, both bits, or `p`. Each destructive map is the average
of identity and its corresponding phase. Their common map sends any local
distribution to its total weight divided equally among the four points.
[ClassicalFinitePhaseRepresentation.lean](../Proofs/QMClosure/ClassicalFinitePhaseRepresentation.lean)

`destructive`, `local_projector_total` and `local_phase_package` establish the
complete destructive multiplication table, projector totality, commuting phase
involutions and the three-phase product identity. The two-wire permutation `G`
satisfies the three stated CNOT conjugation identities. Its required cross
commutations instantiate `actual_cnot_defects_equal` through the existing
operator-level transfer theorem.
[ClassicalFinitePhaseRepresentation.lean](../Proofs/QMClosure/ClassicalFinitePhaseRepresentation.lean)

These operator equalities quantify over every rational distribution on the
specified carriers. The normalized-state theorems likewise cover every ambient
state satisfying their hypotheses. Exact coordinate proofs on the finite point
sets establish these identities for arbitrary distribution values. Sample-only
tests would have a narrower scope. The permutation actions and their inverses
preserve the full normalized bases.
[ClassicalFinitePhaseRepresentation.lean](../Proofs/QMClosure/ClassicalFinitePhaseRepresentation.lean)

## Six selected preparations inside the simplex

The three character coordinates use the signs of `p`, `q xor p` and `q`. For
each coordinate and each sign, `preparation` assigns weight `1/2` to the two
points with that sign and zero to the other points. The six preparations have
the corresponding signed-axis coordinates, and every opposite pair has the
same uniform midpoint.
[ClassicalFinitePhaseRepresentation.lean](../Proofs/QMClosure/ClassicalFinitePhaseRepresentation.lean)

`preparation_two_point_mixture` expresses each selected preparation as an equal
mixture of two distinct normalized point masses. The ambient simplex therefore
contains states beyond the selected family. In particular,
`point_mass_violates_unit_quadratic_bound` gives the normalized point mass at
`(false,false)` with all three character coordinates equal to one. Their square
sum is three, exceeding the chosen unit quadratic bound.
[ClassicalFinitePhaseRepresentation.lean](../Proofs/QMClosure/ClassicalFinitePhaseRepresentation.lean)

The construction supplies a classical realization of the specified finite
algebra. The selected preparations remain mixed in its full ambient base.
Restricted composite-state selection, all-reference pure-marginal atomicity and
additional geometric selectors require their own contracts and artifacts.
[ClassicalFinitePhaseRepresentation.lean](../Proofs/QMClosure/ClassicalFinitePhaseRepresentation.lean)

## A proposed coordinate transformation

The positive permutation `W` exchanges `q` and `p`. It sends the three character
coordinates `(x,y,z)` to `(z,y,x)` on every rational distribution. A separately
defined proposed linear transformation `H` acts as

```text
(x,y,z) ↦ (z,-y,x).
```

`H_total`, `H_coordinates` and `H_involutive` prove total-weight preservation,
the coordinate action and `H²=I` throughout the local linear carrier.
`H_preparation` permutes the six selected preparation labels.
`H_preserves_chosen_mixtures` extends this to every nonnegative total-one
rational mixture of those six preparations.
[ClassicalPhaseJointReadoutBoundary.lean](../Proofs/QMClosure/ClassicalPhaseJointReadoutBoundary.lean)

The same source establishes `H_point_mass_negative`. The normalized point mass
at `(false,false)` acquires coefficient `-1/2` at `(true,true)` under `H`.
`H_not_positive_on_full_simplex` records the resulting ambient positivity
failure. Operational acceptance of `H` as a reversible classical gate would
require positivity on the actual state base. Its involution law and
selected-mixture preservation leave that requirement unsatisfied.
[ClassicalPhaseJointReadoutBoundary.lean](../Proofs/QMClosure/ClassicalPhaseJointReadoutBoundary.lean)

## A generated preparation and event witness

The preparation named `bell` is obtained by applying `G` to the product of the
selected x-plus and z-plus preparations. `bell_generated` and `bell_normalized`
verify its generation and normalization. `bell_diagonal` identifies its full
distribution as weight `1/4` on each equal pair `(a,a)` and zero elsewhere.
This is a correlated classical preparation. A Bell-nonlocality conclusion
would require a separate measurement scenario and inequality statement.
[ClassicalPhaseJointReadoutBoundary.lean](../Proofs/QMClosure/ClassicalPhaseJointReadoutBoundary.lean)

The selected effect applies the first-wire permutation `K=Jy W`, then `G`,
then the product event `p_A=false` and `q_B=false`.
`selected_effect_valid` places its value between zero and one on every
normalized ambient joint state. Its support identity is derived from this
actual permutation-and-event protocol.
[ClassicalPhaseJointReadoutBoundary.lean](../Proofs/QMClosure/ClassicalPhaseJointReadoutBoundary.lean)

For the specified first-wire extension of `H`,
`H_extension_selected_effect` gives value `-1/2` on the transformed generated
preparation. Thus the obstruction also has a joint witness using a generated
positive preparation and a generated valid effect. The local point-mass
obstruction and this joint witness each retain their explicit carrier and
readout scope.
[ClassicalPhaseJointReadoutBoundary.lean](../Proofs/QMClosure/ClassicalPhaseJointReadoutBoundary.lean)

## Geometric continuation

The next analytic route adds an actual nonidentity order-three transformation
fixing a designated pointer pair and an actual two-sided axis exchange. Its
target is a closed-ball preparation closure under a derived metric. The
rank, covariance, subgroup-density and closure steps await Lean formalization.
Composite geometry, independent operational origins and completed QM
reconstruction remain open. Sections 225–230 retain their historical scope.
[Finite-gate ball-closure route](232-finite-gate-ball-closure-route.md)
