## 174. Context-Bundle Nontriviality Research Note

Status: research note, not a theorem, not a verifier claim.

This note records the current best candidate for a lower foundation beneath the
existing finite-QM and weak-gravity fronts. It is deliberately written before
any verifier or manifest upgrade, because the primitive base must be clarified
before the theory can honestly claim progress toward full QM or a gravity
bridge.

### 174.1. Diagnosis

The current carrier-neutral core is:

```text
T0 = (H, E, M, I)

H = possible histories / event bundles
E = event algebra
M = admissible readout contexts
I = admissible inheritance acts
```

This is useful, but it may still be too close to a hidden global ontology. The
risk is `E subset 2^H`: it reads as if there is a global event algebra first,
with readout contexts selecting parts of it afterward.

Bell/contextuality points in the opposite direction. The theory should not
assume a global table of facts and then restrict it to contexts. It should start
from local contexts and ask whether their local sections can be glued.

The suspected correction is:

```text
not:    global histories -> global event algebra -> contexts
but:    contexts -> local sections -> admissible gluing / obstruction
```

### 174.2. Proposed Lower Grammar

Candidate lower core:

```text
C  = admissible context cover / context category
O  = local outcome-event presheaf over C
I  = admissible inheritance transitions between contexts
R  = facticization / readout witness relation
D  = stable distinguishability relation
Omega = obstruction / holonomy class of failed global gluing
```

`Omega` should not be introduced as a primitive unless the derivation fails. The
preferred route is to derive it from `C, O, I, R, D`.

The current objects should be reinterpreted as:

```text
H = derived inheritance traces, not global realized histories
E = derived local event algebras inside contexts, not a primitive global algebra
M = context cover/category C
I = inheritance transition family, with path and cycle structure
W = QM scaffold/import, not primitive
Gamma_I = positivity/distinguishability assumption or obligation, not primitive proof
```

### 174.3. Candidate Principles

#### Local Facticity

A fact is not a global object. A fact is a stable local section witnessed by an
admissible readout context.

```text
fact := stable local section + admissible readout witness
```

#### No Primitive Global Section

The theory may not assume that all local context sections glue into one global
fact table.

```text
global section = derived if it exists, never primitive
```

#### Overlap Discipline

Local sections may be compared only through declared overlaps, restrictions, or
inheritance transitions. Compatibility must be explicit.

#### Obstruction Physicality

If locally compatible sections admit no global section, the obstruction is a
candidate physical invariant.

```text
failed global gluing -> obstruction candidate
```

This is the natural language for Bell/contextuality.

#### Inheritance Holonomy

Cycles of admissible inheritance can be exact/gauge or non-exact/physical.
Only non-exact holonomy can source observable phase or curvature structure.

```text
exact cycle -> gauge / relabeling
non-exact cycle -> physical invariant candidate
```

#### Finite Witness Discipline

A stable distinction is physical only if some finite admissible readout can
witness it.

This retains the existing FDC direction:

```text
stable inherited distinguishability -> finite admissible readout witness
```

#### Minimal Carrier

A carrier is not primitive. A carrier is an economical representation of stable
context/inheritance/readout structure.

```text
carrier := representation selected by constraints
```

Complex Hilbert space must therefore be selected, not inserted.

#### Scale Projection

The same obstruction can project differently under different coarse-grainings:

```text
QM scale       -> phase/contextuality/Bell projection
gravity scale  -> clock/source/curvature projection
```

This is a hypothesis, not a theorem. It must eventually produce a suppression
or decoupling statement explaining why ordinary finite QM gates do not expose
the gravity-facing response.

### 174.4. Projection 1: Bell

Bell is the cleanest first test.

In this language:

```text
Bell violation
  -> no global noncontextual fact table
  -> no global section over the measurement cover
```

This supports `Local Facticity` and `No Primitive Global Section`. It does not
by itself prove Hilbert space.

Expected theorem route:

```text
finite context cover
+ local outcome sections
+ empirical compatibility on overlaps
+ Bell/KS obstruction
=> no global fact table
```

Failure mode:

```text
If Bell can be represented only by importing Hilbert amplitudes,
then this lower grammar has not explained Bell.
```

### 174.5. Projection 2: Hilbert Pressure

Hilbert space should be treated as a carrier candidate for representing:

```text
local contexts
incompatible readouts
transition phase / holonomy
composition
finite distinguishability
bounded correlations
```

Context-bundle nontriviality alone is too weak. It can produce contextuality and
obstruction, but it does not automatically select complex Hilbert space.

The likely required additions are:

```text
finite witness discipline
local tomography / product-context separation
no hidden joint-only invariants
bounded correlation screen
reversible filtering or purification-like constraint
minimal carrier rule
```

Expected theorem pressure:

```text
CBN
+ finite witnesses
+ composition constraints
+ bounded correlations
+ no joint-only residuals
=> complex-Hilbert-like carrier pressure
```

This is still weaker than:

```text
=> complex Hilbert space derived
```

The hard wall remains:

```text
why complex Hilbert exactly, not a broader GPT/Jordan carrier?
```

### 174.6. Projection 3: Gravity

Gravity should not enter as a primitive metric or as GR. The route should be:

```text
inheritance transitions
-> stable clock chains
-> source response
-> non-exact holonomy / obstruction
-> curvature-like readout
-> effective metric / GR limit
```

This matches the existing no-fit holonomy discipline:

```text
exact cycle -> gauge only
non-exact cycle -> needs curvature, topology, independent action cost,
                   or pre-fixed source-coupled response
```

Gravity is therefore a projection candidate:

```text
context/inheritance obstruction
  coarse-grained through clock/source readouts
  -> curvature / geometry
```

Failure mode:

```text
If the route needs metric geometry, G_N, Planck units, or known GR equations as
primitive inputs, then it is not below GR.
```

### 174.7. Why QM May Not Show Gravity Directly

The current scale-hidden hypothesis is:

```text
ordinary finite QM gates freeze clock/source response
```

They can expose:

```text
phase
contextuality
Bell obstruction
finite carrier constraints
```

while not exposing:

```text
gravity-facing clock/source curvature
```

Required future result:

```text
scale separation / suppression theorem
```

Without such a theorem, the Hilbert-Bell-gravity link remains a strong
research route, not a derivation.

### 174.8. Required Mini-Theorems

#### T1. Bell Obstruction

```text
CBN + finite empirical cover + Bell/KS compatibility data
=> no global fact table
```

Most likely tractable.

#### T2. Local Tomography Separator

```text
CBN + product-context exhaustion + product readout separation
=> local tomography
=> reject hidden joint-only carriers
```

Already partially covered by the context-product local tomography route.

#### T3. Complex-Hilbert Pressure

```text
CBN
+ finite witness discipline
+ local tomography
+ reversible filtering / purification-like condition
+ bounded correlations
+ no hidden joint-only residuals
=> complex-Hilbert-like carrier pressure
```

This is the main QM foundation wall.

#### T4. Clock/Source Curvature Projection

```text
CBN
+ stable clock chains
+ source response
+ non-exact inheritance holonomy
+ admissible coarse-graining
=> curvature-like readout
```

This is the main gravity bridge wall.

#### T5. Scale Separation

```text
clock/source curvature terms vanish or become negligible in ordinary finite
QM readout gates under declared scale/coarse-graining conditions
```

This is required before the Hilbert-Bell-gravity link can become more than a
structural analogy.

### 174.9. What Must Not Be Claimed

This note does not claim:

```text
full QM derived
complex Hilbert derived
Born rule derived
GR derived
hbar_I or G_I derived
gravity explains Bell
Bell proves gravity
```

It claims only that the current primitive base should be reconsidered around
local contexts, local sections, inheritance transitions, facticization
witnesses, stable distinguishability, and derived gluing obstructions.

### 174.10. Research Decision

The promising base is:

```text
context first, global history later if derivable
local fact first, global fact table only if gluing succeeds
obstruction first, carrier/geometry as projections
```

The next research pass should not start by editing the verifier. It should
attempt T1-T5 as paper-level proof sketches and identify which assumptions are
genuinely primitive, which are bridge assumptions, and which are imported from
QM/GR.

### 174.11. First Proof-Pressure Analysis

#### T1 looks structurally strong

Let `C` be the measurement/context cover and `O` the local outcome presheaf. A
global fact table is exactly a global section of `O`. A Bell/KS obstruction is
then a proof that the observed local sections cannot be glued into such a global
section.

This route does not need Hilbert space if the empirical tables are treated as
the input object:

```text
empirical local tables
+ compatibility/no-signalling on overlaps
+ Bell/KS violation
=> no global section
```

This is the cleanest current support for replacing global event algebra with
context-indexed local events.

Detailed proof sketch:

```text
Let X be the finite set of measurement labels.
Let C be a finite cover of X by jointly admissible contexts.
For each context c in C, let O(c) be the set of local outcome sections on c.
For c' subset c, let rho(c,c') : O(c) -> O(c') be restriction.
```

An empirical model is:

```text
e_c : O(c) -> Prob
```

with overlap compatibility:

```text
for all c,d in C:
  marginal(e_c, c cap d) = marginal(e_d, c cap d)
```

An individual global fact table would be:

```text
s in O(X)
```

such that:

```text
rho(X,c)(s) in support(e_c)
```

for every context `c`.

A hidden-variable/global-table model is a distribution:

```text
mu : O(X) -> Prob
```

whose marginals reproduce all local tables:

```text
marginal(mu, c) = e_c
```

Therefore:

```text
Bell/KS obstruction
  = no such global section or global distribution exists
```

IDT translation:

```text
admissible_context        -> c in C
local_section             -> s_c in O(c)
facticization_witness     -> e_c or observed readout support
stable_distinguishability -> separation inside declared local contexts
global fact table         -> global section of O
Bell obstruction          -> failure of global gluing
```

This is not a Hilbert derivation. It is a lower-level theorem candidate:

```text
empirical contextuality is already expressible in the context/local-section
grammar, before choosing a quantum carrier.
```

Boundary:

```text
T1 imports empirical tables, not Hilbert amplitudes.
T1 proves no-global-table for those tables.
T1 does not explain why nature realizes exactly the quantum tables.
T1 does not derive Tsirelson bounds or Born probabilities.
```

#### T2 is already partially supported

The existing context-product local tomography route says:

```text
product-context closure
+ stable invariant witness completeness
+ product readout separation
=> local tomography
```

In the new grammar this becomes:

```text
if composite local sections are exhausted by product-context witnesses,
then hidden joint-only sections are not admissible stable facts
```

This gives a real separator against real-Hilbert-like hidden joint invariants,
but it remains conditional.

#### T3 is the Hilbert wall

Context-bundle nontriviality yields contextual obstruction, but many carriers
can represent obstruction. To get complex-Hilbert pressure, additional
constraints must narrow the carrier class.

The likely narrowing stack is:

```text
finite local witnesses
+ product-context tomography
+ no hidden joint-only invariants
+ reversible filtering / purification-like recovery
+ bounded correlations
+ minimal faithful carrier
```

The missing theorem is not:

```text
contextuality => Hilbert
```

but:

```text
contextuality
+ finite composition/recovery/correlation constraints
=> complex-Hilbert-like carrier is the minimal faithful representation
```

This is the main QM route.

#### T4 is the gravity wall

The gravity projection needs more than analogy. It needs a construction that
turns inheritance obstruction into clock/source curvature.

A plausible shape is:

```text
context category C
-> clock-chain functor K
-> source-response cochain S
-> non-exact cycle/curvature obstruction dS != 0
-> coarse-grained geometry readout
```

The hard part is proving that `S` is not imported from GR or fitted from `G_N`.
It must come from admissible inheritance, stable clock chains, and source
response already fixed before comparison.

#### T5 is required for the scale claim

The scale-hidden claim needs an actual theorem of the form:

```text
under ordinary finite QM gate conditions,
clock/source curvature terms are frozen, negligible, or projected out
```

Without this, the Hilbert-Bell-gravity connection remains structural but not
predictive.

### 174.12. Primitive Verdict

Keep as primitive candidates:

```text
admissible_context
local_section
inheritance_transition
facticization_witness
stable_distinguishability
```

Treat as derived or bookkeeping:

```text
history = inheritance path
event algebra = local algebra inside a context
global event algebra = derived only if global gluing succeeds
holonomy/obstruction = derived from inheritance cycles
carrier = representation selected by constraints
spacetime geometry = clock/source readout projection
```

Treat as forbidden primitives:

```text
complex amplitudes
Hilbert space
Born rule
metric spacetime
GR field equations
hbar_I
G_I
```

The base is promising only if the first group can generate the second group
without importing the third.

### 174.13. T2/T3 Carrier Pressure Pass

The carrier-selection route should be viewed as a sequence of filters, not as a
single jump from contextuality to Hilbert space.

The current pressure stack is:

```text
CBN
-> no primitive global fact table
-> finite facticization witnesses
-> product-context separation
-> local tomography
-> no hidden joint-only stable invariants
-> recoverable filtering / purification-like dilation
-> bounded correlations
-> non-complex and unconstrained GPT exclusions
-> minimal faithful carrier pressure
```

Each arrow has a different status.

#### T2: local tomography is a separator, not carrier selection

The existing context-product theorem fits the new base:

```text
product contexts exhaust composite stable facts
+ product readouts separate stable facts
=> composite operational state is determined by local joint statistics
```

In `CBN` language:

```text
every admissible composite section must be witnessed by product-context local
sections, unless a hidden joint-only invariant is explicitly allowed
```

Therefore T2 can reject real-Hilbert-like composite carriers under its
assumptions, because those carriers contain a stable joint invariant that local
product sections cannot witness.

But T2 does not select complex Hilbert. It only removes a class of carriers that
violate product-context witness exhaustion.

#### T3: Hilbert pressure needs a reconstruction stack

`CBN` supplies the missing lower language:

```text
local contexts
local sections
failed global gluing
inheritance cycles
finite witnesses
```

But many theories can implement that language. The Hilbert route requires
additional constraints that are not yet primitive consequences:

```text
local tomography / local distinguishability
continuous reversible inheritance between pure stable sections
purification or reversible dilation of mixed/readout-lost states
state-effect duality or equivalent positivity rule
bounded correlations
minimal faithful representation
```

The strongest current candidate theorem is therefore:

```text
CBN
+ FDC
+ local tomography
+ reversible purification/filtering
+ bounded correlations
+ minimal faithful carrier
=> complex-Hilbert-like carrier pressure
```

This is intentionally weaker than:

```text
=> complex Hilbert derived
```

The proof burden is to show that the added constraints are themselves forced by
fundamental unknownness/facticization, rather than imported from successful QM
practice.

#### Why continuous reversible inheritance matters

Without a continuity/reversibility requirement, contextual theories can collapse
toward classical finite/simplex behavior or branch into broader GPT behavior.
Continuous reversible motion between pure stable sections is the known type of
condition that starts excluding classical discreteness and pushes toward
smooth carrier geometry.

In IDT terms this should not be imported as unitary dynamics. It should be
reframed as:

```text
admissible reversible inheritance paths exist between pure local sections
without changing facticization class
```

This becomes an obligation:

```text
reversible_inheritance_path_obligation
```

not a primitive unitary group.

#### Why purification/recoverable filtering matters

If every apparent loss of local information can be represented as discarding a
larger reversible inheritance context, then mixed/local states are not
fundamental ignorance blobs. They are restrictions of a larger stable section.

This bridges CBN to carrier structure:

```text
local section restriction
recoverable extension
state/process correspondence pressure
```

But purification is powerful. If inserted as an axiom without derivation, it is
a bridge assumption, not a primitive.

#### Why bounded correlations matter

Bell obstruction only rejects global fact tables. It still permits
superquantum no-signalling boxes unless more structure is added.

The bounded-correlation screen is therefore not optional:

```text
no global table
+ no-signalling
!= quantum
```

IDT needs an internal reason why admissible context bundles reject PR-box-like
correlations. Possible sources:

```text
finite witness stability
recoverable filtering
minimal carrier geometry
composition consistency
```

This is a real open problem, not a bookkeeping gap.

#### T3 failure modes

The Hilbert route fails if any of these happen:

```text
1. continuous reversible inheritance is simply unitary dynamics renamed;
2. purification is imported as a QM axiom rather than derived from restriction/recovery;
3. bounded correlations are enforced by inserting Tsirelson bounds by hand;
4. minimal carrier is declared before the admissible carrier class is defined;
5. nonfinite GPT residuals remain unconstrained.
```

Current verdict:

```text
T2 is a real conditional separator.
T3 is plausible but not closed.
The missing bridge is deriving the reconstruction stack from CBN/FDC.
```

### 174.14. External Alignment

This research direction aligns with three external facts, without importing
their full frameworks as IDT primitives:

1. Bell's theorem motivates rejecting local pre-existing fact tables for the
   observed correlation data.
2. The sheaf-theoretic treatment of contextuality identifies non-locality and
   contextuality with obstructions to global sections over measurement covers.
3. Operational reconstructions of QM show that Hilbert structure can be treated
   as something to derive from principles rather than assume at the start.
4. Reconstruction routes repeatedly use continuity/reversibility, local
   distinguishability/tomography, and purification-like principles as the
   pressure stack that narrows general operational theories toward QM.

Relevant references:

```text
Bell 1964, On the Einstein Podolsky Rosen paradox
Abramsky-Brandenburger 2011, The Sheaf-Theoretic Structure of Non-Locality and Contextuality
Hardy 2001, Quantum Theory From Five Reasonable Axioms
Masanes-Mueller 2011, A derivation of quantum theory from physical requirements
Chiribella-D'Ariano-Perinotti 2010, Probabilistic theories with purification
Chiribella-D'Ariano-Perinotti 2011, Informational derivation of Quantum Theory
```

IDT should borrow the lesson, not the conclusion:

```text
global fact tables are optional derived objects,
not primitives.
```

### 174.15. T4 Gravity Projection Pass

The gravity route is weaker than the Bell route and less mature than the
Hilbert-pressure route. The current weak-field gates are useful consistency
scaffolds, but they do not derive `G_I`, metric geometry, or GR.

The CBN-compatible construction should be:

```text
context category C
-> admissible inheritance transitions I
-> stable clock-chain functor K : C -> ClockRatios
-> source-response cochain S on inheritance/context cells
-> non-exact cycle obstruction dS != 0
-> coarse-grained curvature-like readout
-> effective weak-field clock geometry
```

In current IDT language:

```text
stable clock chain      -> primitive tick / clock universality front
source-response cochain -> source-response charge and packet fronts
non-exact obstruction   -> non-exact holonomy source gate
weak-field readout      -> clock-rate / Poisson / PPN validation scaffold
```

#### What is real today

The existing gravity front already has useful guardrails:

```text
lambda is bookkeeping, not physical time
only clock-rate ratios are admissible readouts
primitive tick cannot use hbar, G_N, Planck units, or known quantum frequencies
known weak-field formulas are executable no-refit gates
G_N remains a calibration, not a primitive derivation
PPN gamma/no-slip remains a target, not a primitive derivation
```

This is not empty. It prevents hidden fitting and keeps the gravity route honest.

#### What T4 would need

T4 must prove a statement of this shape:

```text
CBN
+ admissible clock chains
+ source-response cochain fixed before comparison
+ non-exact inheritance holonomy
+ coarse-graining stability
=> curvature-like clock/source readout
```

The key missing object is:

```text
source-response cochain S
```

It must be derived from inheritance/facticization structure, not from the
Newtonian source law, Einstein equations, measured `G_N`, or post-fit galaxy
residuals.

#### The likely mathematical shape

The promising abstraction is cohomological:

```text
exact clock/source response       -> gauge / no physical curvature
closed but non-exact response     -> topology-like holonomy
non-closed response dS != 0       -> curvature/source readout
```

This mirrors the holonomy discipline already used in the phase sector:

```text
exact phase = gauge
non-exact holonomy = possible physical invariant
```

The research question is whether the same obstruction logic can be made
clock/source-valued rather than phase-valued.

#### Why this is not yet gravity

Even if `dS != 0` is derived, three bridges remain:

```text
1. show the coarse-grained readout has metric form;
2. show the weak static limit gives a Poisson-like source law;
3. show no-slip / PPN gamma -> 1 under isotropic source conditions.
```

If any of these bridges require GR equations as input, T4 fails as a below-GR
derivation.

#### T4 failure modes

The gravity route fails if:

```text
1. clock universality is assumed instead of derived from admissible clocks;
2. source charge is normalized by G_N rather than inherited response;
3. non-exact holonomy is chosen after seeing a desired weak-field result;
4. metric geometry is inserted before clock/source readout;
5. no-slip is imported from GR rather than derived from isotropic source packet;
6. scale separation is asserted without a suppression theorem.
```

Current verdict:

```text
T4 is a plausible structural route, not a proof.
The next hard object is source_response_cochain_from_inheritance.
Without it, gravity remains a calibrated readout scaffold.
```

### 174.16. Global Synthesis After T1-T4

The current global picture is:

```text
T1 Bell/no-global-table                  -> structurally strong
T2 local tomography separator            -> conditional separator exists
T3 complex-Hilbert pressure              -> plausible, not closed
T4 clock/source curvature projection     -> plausible, weaker, not closed
T5 scale separation                      -> required, not started
```

This means the base is not a dead end, but it is also not yet a derivation of
QM or gravity.

The common invariant across the routes is:

```text
obstruction to globally trivial context/inheritance structure
```

Different projections read this obstruction differently:

```text
Bell projection:
  obstruction to global fact table

Hilbert projection:
  obstruction represented as phase/context carrier structure

Gravity projection:
  obstruction represented as clock/source curvature after coarse-graining
```

The theory should therefore focus on obstruction calculus, not on Hilbert or
metric geometry directly.

### 174.17. Five Missing Objects

The global proof graph now appears to depend on five missing objects:

#### 1. Distinguishability geometry from CBN/FDC

Current gap:

```text
PSD/distinguishability geometry is still an obligation.
```

Needed:

```text
stable local distinguishability
-> positive separation geometry
-> admissible probability/readout measure
```

Risk:

```text
positivity is imported from Hilbert/PSD kernels.
```

#### 2. Reversible inheritance path theorem

Current gap:

```text
reversible dynamics / Wigner-style inheritance remains open.
```

Needed:

```text
pure stable local sections
+ same facticization class
=> admissible continuous reversible inheritance path
```

Risk:

```text
unitary dynamics is renamed as inheritance.
```

#### 3. Quadratic/Born readout theorem

Current gap:

```text
Born rule remains open/blocked at the quadratic actualization obligation.
```

Needed:

```text
selected carrier
+ additive alternatives
+ facticized readout
+ noncontextual probability over operationally identical readouts
=> quadratic readout
```

Risk:

```text
Born probabilities are smuggled in through normalized amplitudes.
```

#### 4. Source-response cochain from inheritance

Current gap:

```text
gravity route has calibrated weak-field scaffolds but not a derived source
cochain.
```

Needed:

```text
inheritance activity
+ stable clock chains
+ admissible source response
=> source-response cochain S fixed before comparison
```

Risk:

```text
S is normalized by G_N, Newtonian gravity, GR equations, or fitted residuals.
```

#### 5. Scale separation / suppression theorem

Current gap:

```text
Hilbert-Bell and gravity projections are structurally linked, but their
separation by scale is not derived.
```

Needed:

```text
ordinary finite QM gate conditions
=> clock/source curvature response is frozen, negligible, or projected out
```

Risk:

```text
scale suppression is asserted as explanation rather than proved.
```

### 174.18. Revised Primitive Base Candidate

The base should now be tested as:

```text
P1 admissible_context
P2 local_section
P3 inheritance_transition
P4 facticization_witness
P5 stable_distinguishability
```

Everything else is either derived or an obligation:

```text
history                     -> inheritance path
event algebra               -> local context algebra
global event algebra         -> global section if gluing succeeds
obstruction/holonomy         -> derived cycle/gluing invariant
carrier                     -> minimal faithful representation
probability measure          -> readout theorem
spacetime geometry           -> clock/source projection
action scale                 -> independent work/tick/cycle standard
```

The strongest research claim allowed now is:

```text
IDT should be rebuilt around local contextual facticity and derived obstruction
calculus.
```

Not:

```text
IDT has derived QM or gravity.
```

### 174.19. Loopholes As Primitive-Design Signals

The open edges in Bell, Hilbert reconstruction, and GR should not be treated as
embarrassing exceptions. They are useful design signals for the primitive
layer.

Bell gives the cleanest warning:

```text
do not primitive a global fact table
```

Its mathematical core is a conditional obstruction theorem. Under locality,
measurement-setting independence, compatible overlaps/no-signalling, and
ordinary probabilistic marginals, some empirical tables have no global hidden
fact table. The experimental program makes this warning extremely strong, but
it does not eliminate every metaphysical escape route such as superdeterminism,
retrocausality, many-world bookkeeping, or alternative readings of local
causality.

For IDT this is not a weakness. It means the base language must expose the
assumptions:

```text
context_choice_independence
overlap_compatibility
no_primitive_global_section
global_section_obstruction
```

Hilbert reconstruction gives the second warning:

```text
do not primitive the carrier
```

Hilbert space is an extraordinarily successful carrier, but standard
reconstruction routes depend on visible assumptions: composition, local
tomography, purification or reversible filtering, continuity, symmetry,
self-duality, or probability-readout rules. If those assumptions are inserted
as primitives, the derivation becomes circular.

For IDT the carrier must remain a selected representation:

```text
local contextual facticity
+ stable distinguishability
+ admissible inheritance transitions
+ composition constraints
+ bounded correlation constraints
=> minimal faithful carrier
```

Until this route is proved, complex Hilbert space is a target and scaffold, not
a primitive.

GR gives the third warning:

```text
do not primitive spacetime metric geometry
```

GR is strongly tested in its domain, but its open edges are exactly where a
deeper theory should be visible: singularities, quantum gravity, black-hole
interiors, early cosmology, source interpretation, and dark-sector ambiguity.

For IDT the metric should be an effective projection:

```text
inheritance transitions
+ stable clock chains
+ source-response cochain
+ non-exact cycle/holonomy obstruction
+ coarse-graining stability
=> metric-like clock/source geometry
```

The shared base principle is therefore:

```text
No Primitive Global Structure:
  no primitive global fact table;
  no primitive Hilbert carrier;
  no primitive metric spacetime.

All three may appear only as successful gluing, representation, or projection
results with explicit assumptions and failure modes.
```

This principle is stronger than the current `T0 = (H, E, M, I)` grammar. It
suggests that `H`, `E`, Hilbert carriers, and metric spacetime must be moved
downstream of the context/inheritance layer, not used as first objects.

### 174.20. Next Research Order

The correct order is:

```text
1. Formalize CBN grammar and global-section obstruction.
2. Prove T1 without Hilbert imports.
3. Re-express T2 local tomography in the CBN grammar.
4. Attack distinguishability geometry from stable local sections.
5. Attack reversible inheritance path theorem.
6. Only then revisit Hilbert carrier selection.
7. In parallel, define source_response_cochain_from_inheritance.
8. Only then revisit gravity projection and scale separation.
```

This order avoids building a large formal system on a primitive base that still
assumes what Bell is telling us not to assume.

Status:

`context_bundle_nontriviality_research_note_added`

### 174.21. v7 Recovery Problem

The v7 base candidate is not complete until it explains why the old executable
v6 core was useful.

Current v7 candidate:

```text
B0 = (C, O, I, R, D)

C = admissible context cover/category
O = local outcome-event presheaf over C
I = inheritance transitions between contexts
R = facticization/readout witness relation
D = stable distinguishability relation
```

Current v6 executable scaffold:

```text
T0 = (H, E, M, I)

H = history/event-bundle domain
E = event algebra
M = readout-context family
I = inheritance-act family
```

The necessary migration theorem is not:

```text
B0 declares T0 obsolete.
```

The necessary theorem is:

```text
Under finite gluing, witness coverage, and inheritance coherence,
B0 recovers T0 as a readout-facing interface.
```

Candidate recovery map:

```text
M_B0 := objects/contexts of C
E_B0(c) := local outcome-event algebra generated by O(c)
H_B0 := admissible inheritance traces modulo operational equivalence
I_B0 := admissible transition family induced by I
```

Only local event algebras are immediate. A global event algebra exists only
under a gluing condition:

```text
global E exists
<=> compatible local sections glue without obstruction.
```

If gluing fails, the failure is not a defect. It is the Bell/contextuality
signal:

```text
failed gluing => obstruction/holonomy class => physical negative control
```

Therefore the v7 migration must split old `E` into two roles:

```text
local_E_family       = admissible and primitive-facing
global_E_if_glued    = derived interface, not primitive
```

This is the first hard correction to the old base.

### 174.22. Minimal Theorem Stack For v7

The v7 base needs a small theorem stack before it can carry the QM program.

T0-recovery theorem:

```text
B0 + finite context cover + local event closure + inheritance coherence
=> v6-style readout interface (H_readout, E_local, M, I_readout)
```

This should be the first migration theorem because it protects prior executable
work without preserving the global-ontology mistake.

Bell obstruction theorem:

```text
B0 + compatible local empirical sections + no global section
=> no primitive global fact table
```

This is the cleanest likely formal theorem. It imports empirical/contextual
tables but does not import Hilbert amplitudes.

Local tomography separator:

```text
B0 + product-context closure + stable invariant witness completeness
+ product readout separation
=> local tomography
```

This recovers the real-Hilbert separator route in the new grammar.

Distinguishability geometry theorem:

```text
B0 + stable distinguishability + finite witness coverage
=> positive separation geometry or explicit obstruction
```

This is where the route may hit a real wall. Without a non-Hilbert derivation
of positivity/geometry, Hilbert selection cannot be honest.

Probability readout theorem:

```text
B0 + selected carrier + additivity/coarse-graining + operational equivalence
=> admissible probability readout
```

This is the Born-rule wall in cleaner form.

Source-response projection theorem:

```text
B0 + stable clock chains + source-response cochain + coarse-graining
=> metric-like clock/source readout or explicit obstruction
```

This is the gravity-facing wall.

### 174.23. Where The Wall Is Most Likely

The strongest candidate route is:

```text
contextual local facticity
=> obstruction calculus
=> Bell/global-section boundary
=> product-composition screens
=> local tomography separator
```

This route is structurally solid and should be formalizable.

The likely wall is later:

```text
stable distinguishability
=> positive geometry
=> complex Hilbert carrier
=> quadratic/Born readout
```

The missing ingredient is not another physical constant. It is a principle
that forces the admissible representation of distinguishability to be positive,
composable, reversible enough, and correlation-bounded without naming Hilbert
space.

Candidate names for the missing principle:

```text
stable_distinguishability_geometry
recoverable_context_transformations
finite_reversible_facticity
minimal_positive_composite_carrier
```

But these names must not become axioms by stealth. Each one must be tested as a
theorem obligation or rejected as a bridge assumption.

### 174.24. Base Verdict After v7 Boundary

The v7 base is stronger than the old base because it removes three dangerous
primitive assumptions:

```text
global history ontology
global event algebra
carrier/metric geometry as first objects
```

It is not yet sufficient for full QM.

The honest status is:

```text
v7 base candidate is directionally better and logically cleaner;
Bell/global-section obstruction is likely provable;
local tomography separator is likely recoverable;
Hilbert/Born/metric projection still require new theorem obligations.
```

Therefore the next research move should not be adding more experiments. It
should be proving or refuting the T0-recovery theorem and the
distinguishability-geometry theorem.

### 174.25. Fresh Pass: B0 To T0 To Projections

This pass restarts the route without assuming the earlier conclusion.

Starting point:

```text
B0 = (C, O, I, R, D)

C = admissible contexts
O = local outcome-event presheaf
I = inheritance transitions between contexts
R = facticization/readout witness relation
D = stable distinguishability relation
```

Target interface:

```text
T0 = (H, E, M, I)
```

Projection targets:

```text
Bell/global-section boundary
Hilbert carrier and Born readout
metric clock/source geometry
```

The first correction is that these are not one problem. They are four layers:

```text
1. context/sheaf layer
2. readout-interface recovery layer
3. operational/probability/composition layer
4. geometric/dynamical projection layer
```

B0 directly speaks only about layer 1. Everything above layer 1 must be a
theorem, a bridge assumption, or a rejected route.

### 174.26. B0 To Old T0: What Can Be Recovered

The clean recovery map is:

```text
M_readout := C
I_readout := I restricted to admissible context transitions
E_local(c) := event algebra generated by local sections O(c)
H_trace := admissible inheritance traces modulo R/D operational equivalence
```

This does not recover old T0 literally. It recovers a safer interface:

```text
T0_readout = (H_trace, E_local_family, M_readout, I_readout)
```

The old object:

```text
E subset 2^H
```

is too strong if read as a primitive global event algebra. In v7 it must split:

```text
E_local_family = always available inside contexts
E_global       = available only if compatible local sections glue
```

Therefore the first v7 theorem should be:

```text
B0 + finite context cover + local event closure + inheritance coherence
=> T0_readout
```

not:

```text
B0 => old global T0
```

This is a meaningful improvement. It preserves the executable v6 work while
removing the hidden global-ontology assumption.

Status:

```text
B0 -> T0_readout: plausible conditional theorem
B0 -> old global T0: rejected as primitive reading
```

### 174.27. B0 To Bell Projection

Bell fits B0 well because Bell is fundamentally a gluing obstruction.

Required extra layer:

```text
empirical/local readout valuation P_c over O(c)
```

This layer can be read as experimental readout data, not as a Hilbert import.

Then the route is:

```text
C gives measurement contexts
O gives local outcome sections
overlap discipline gives compatible restrictions
P_c gives local empirical tables
no global section/distribution exists
=> no primitive global fact table
```

This can support:

```text
Bell violations reject global noncontextual fact tables under declared
independence/locality/compatibility assumptions.
```

It cannot support:

```text
B0 derives Tsirelson bound
B0 derives singlet correlations
B0 derives spin geometry
B0 proves nature is nonlocal in one unique metaphysical sense
```

Fresh verdict:

```text
B0 -> Bell obstruction: strongest near-term proof target.
```

Bell is not the wall. Bell is the guide telling us not to primitive global
sections.

### 174.28. B0 To Hilbert Projection

Hilbert does not follow from B0 alone.

B0 can provide:

```text
contextual local sections
operational equivalence via R/D
obstruction to global fact tables
inheritance transitions
```

But Hilbert selection needs more:

```text
probability/frequency readout layer
convex state/effect structure
product composition
local tomography or declared separator
positive distinguishability geometry
enough reversible transformations
bounded correlations
minimal faithful representation
```

The dangerous hidden import is:

```text
D behaves like an inner product / PSD kernel.
```

If this is assumed, Hilbert has already entered through the back door.

The real theorem obligation is:

```text
B0 + finite witness discipline + operational equivalence
+ composition + recoverable transformations + bounded correlations
=> positive composable distinguishability geometry
```

Only after that can the carrier-selection route honestly ask whether complex
Hilbert is forced.

Fresh verdict:

```text
B0 -> contextual operational grammar: yes.
B0 -> Hilbert carrier: no.
B0 + strong representation principles -> possible, unproved.
```

This is the main wall.

### 174.29. B0 To Metric Projection

Metric geometry also does not follow from B0 alone.

B0 can provide:

```text
context transitions
cycle/holonomy candidates
stable distinguishability classes
facticized readout witnesses
```

Metric projection needs additional objects:

```text
clock-chain readout
source-response cochain
coarse-graining map
stability under refinement
calibration boundary for G_N
```

The honest route is:

```text
B0
+ stable clock chains
+ source-response cochain fixed before comparison
+ non-exact inheritance cycles
+ coarse-graining stability
=> metric-like clock/source readout
```

This still does not derive GR. It may derive a pre-metric obstruction calculus
whose coarse-grained limit can be compared to weak-field/GR readouts.

Fresh verdict:

```text
B0 -> premetric obstruction language: yes.
B0 -> metric spacetime / GR: no.
B0 + clock/source/coarse-graining theorems -> possible, unproved.
```

Gravity is not currently the shortcut through the Hilbert wall. It is a second
projection wall with a similar shape.

### 174.30. Shared Structure Across Bell, Hilbert, And Metric

The shared structure is not "Hilbert equals gravity" or "Bell comes from
spacetime".

The shared structure is:

```text
local contexts
+ admissible transitions
+ failed or nontrivial gluing
+ facticized witnesses
+ scale-dependent projection
```

Projection-specific forms:

```text
Bell:
  failed gluing of local fact tables

Hilbert:
  representation of contextual distinguishability and compatible composition

Metric:
  coarse-grained clock/source response to inheritance-cycle obstruction
```

This suggests a better central object:

```text
contextual obstruction calculus
```

not:

```text
primitive Hilbert space
primitive spacetime geometry
primitive global history algebra
```

### 174.31. What Must Be Proved Next

The correct proof order after this fresh pass is:

```text
P1. B0 -> T0_readout recovery theorem
P2. B0 -> Bell/global-section obstruction theorem
P3. B0 product contexts -> local tomography separator
P4. D/R -> positive distinguishability geometry or explicit failure
P5. positive geometry + composition + reversibility bounds -> carrier screen
P6. selected carrier + readout assumptions -> Born/quadratic theorem
P7. I + clock/source cochain + coarse-graining -> metric projection theorem
```

Expected difficulty:

```text
P1: tractable
P2: tractable
P3: tractable conditionally
P4: hard wall
P5: hard wall
P6: hard wall
P7: hard wall
```

If P4 fails, the theory can still be a strong research graph and operational
claim-control language, but it will not derive QM.

If P4 succeeds without Hilbert import, the QM program becomes serious.

### 174.32. Fresh Verdict

The new base is not enough, but it is the right cleanup.

Precise status:

```text
B0 removes false primitives.
B0 can likely recover a safer T0_readout interface.
B0 can likely formalize Bell/global-section obstruction.
B0 does not yet force Hilbert, Born, or metric geometry.
The wall is now localized at distinguishability geometry and source-response
projection, not hidden in vague primitive language.
```

This is progress, not closure.

### 174.33. Primitive Reformulation Needed To Attack The Wall

The wall will not be crossed by adding a primitive named after the desired
answer.

Forbidden primitive forms:

```text
D is a PSD kernel
states are Hilbert vectors
probability is squared amplitude
metric spacetime is fundamental
Born readout is primitive
```

These would only rename QM/GR imports.

The primitive must be lower than Hilbert and metric geometry, but strong enough
to force positive composable distinguishability if the theory is right.

Required shape:

```text
finite
contextual
readout-facing
stable under refinement
stable under independent spectator composition
falsifiable by finite counterexample
```

This points to a rule, not a carrier:

```text
finite_facticization_stability
```

Candidate statement:

```text
For every finite admissible context family, any stable facticizable
distinguishability table must remain facticizable under all admissible
coarse-grainings, refinements, and independent spectator extensions.

No such operation may create a negative, contradictory, or unwitnessed stable
fact.
```

This is not the same as saying "the table is PSD". The theorem obligation would
be:

```text
finite_facticization_stability
+ second-order actualization
=> positive comparison geometry
```

If this theorem works, PSD-like geometry is derived from finite facticity
stability rather than assumed.

If it fails, the Hilbert route probably fails.

### 174.34. Why Second-Order Facticization Matters

The existing QM gates already use the finite insight:

```text
I3 = 0
```

Interpreted below QM, this should not mean "quantum amplitudes are bilinear".
It should mean:

```text
facticization has no primitive third-order term;
all stable multi-alternative readout effects reduce to singleton and pairwise
comparison data.
```

Candidate primitive/rule:

```text
second_order_facticization
```

Candidate statement:

```text
For any finite context, stable actualization over a finite alternative family
is generated by local singleton witnesses and pairwise inherited comparison
witnesses. Primitive irreducible third-order facticization is forbidden unless
explicitly introduced as a new sector and independently gated.
```

This gives the route:

```text
second_order_facticization
+ finite_facticization_stability
=> positive pairwise comparison geometry
```

This is the cleanest possible way to attack the Hilbert wall from below QM.

Risk:

```text
second_order_facticization may be an empirical fact about our QM-scale readouts,
not a fundamental primitive.
```

Therefore it must be falsifiable:

```text
if stable nonzero I3 appears in a finite no-refit context, the primitive fails
or becomes sector-limited.
```

### 174.35. Why Orientation/Holonomy May Be Needed

Positive comparison geometry alone may still not select complex Hilbert.

Real-Hilbert-like carriers can survive many single-system screens. The existing
separator rejects them at composition only when local tomography/product-context
exhaustion is imposed.

The missing complex pressure likely needs an orientation primitive below
complex numbers:

```text
oriented_inheritance_holonomy
```

Candidate statement:

```text
Closed reversible inheritance cycles carry a gauge-invariant oriented
composition class. Exact cycle labels are gauge; non-exact oriented cycle
classes are admissible stable comparison witnesses.
```

This must not assign complex phases as primitive.

It only says:

```text
cycle orientation and inverse composition are physically meaningful when
facticized by stable witnesses.
```

The possible theorem route is:

```text
oriented_inheritance_holonomy
+ finite_facticization_stability
+ product-context exhaustion
=> real carriers hide orientation at composite level
=> complex-like carrier pressure
```

This connects the Hilbert and gravity fronts without claiming either is
derived:

```text
Hilbert projection: orientation appears as phase-like carrier structure.
Metric projection: orientation/non-exact cycles appear as curvature-like
clock/source obstruction.
```

### 174.36. Candidate B1 Base

The current B0 may be too weak:

```text
B0 = (C, O, I, R, D)
```

The next serious candidate is:

```text
B1 = (C, O, I, R, D, F, Q)
```

where:

```text
F = finite facticization stability rule
Q = oriented inheritance-cycle composition rule
```

`F` attacks the positive-geometry/Born wall:

```text
F + second_order_facticization -> positive comparison geometry
```

`Q` attacks the complex/holonomy/metric wall:

```text
Q + product/context composition -> orientation-aware carrier and curvature
projection pressure
```

This is still not a completed solution. It is a sharper primitive hypothesis.

The important boundary:

```text
F and Q are not Hilbert, Born, or metric primitives.
They are finite operational stability constraints.
```

### 174.37. First Wall-Break Test

The first nontrivial test should be:

```text
Can finite_facticization_stability + second_order_facticization force every
finite comparison matrix to be positive in the representation-independent
sense needed for a Gram/PSD embedding?
```

This can be attacked as a theorem:

```text
Assume every finite refinement and spectator extension remains facticizable.
Assume all multi-alternative actualization is generated by singleton and
pairwise comparison witnesses.
Show that any negative quadratic comparison direction would generate a finite
coarse-graining or spectator extension with a negative facticization weight.
Therefore stable facticization forbids that direction.
```

If valid, this is the bridge:

```text
facticity stability -> positivity -> Hilbert pressure
```

If invalid, we learn exactly what extra primitive is missing.

Current verdict:

```text
The wall is probably not crossed by B0.
The best next primitive candidate is F: finite facticization stability.
The second candidate is Q: oriented inheritance-cycle composition.
Together they define B1, the first serious wall-break base candidate.
```

### 174.38. External Pressure: Strong Positivity Is The Known Shape

The `F` candidate is not arbitrary. A close analogue already appears in quantum
measure/decoherence-functional work.

External pattern:

```text
I3 = 0 / grade-2 additivity alone is not enough.
Strong positivity is the condition that enables Hilbert-space representation.
Strong positivity is also tied to closure under composition.
```

Relevant external results:

```text
Gudder:
  a quantum measure has a Hilbert-space representation iff it is strongly
  positive.

Boes-Navascues:
  non-strongly-positive decoherence functionals create composition problems;
  strongly positive decoherence functionals are maximal under composition
  closure in the studied setting.

Dowker-Wilkes:
  strong positivity is argued to be the unique maximal tensor-product-closed
  class of quantum systems in that framework.

Craig-Dowker-Henson-Major-Rideout-Sorkin:
  Tsirelson-type bounds follow geometrically from associating Hilbert space to
  a strongly positive quantal measure.
```

IDT should not import this as a theorem, but it gives a strong diagnostic:

```text
If F is the right primitive, it must operationally reproduce the role of strong
positivity without naming PSD matrices as primitive.
```

Therefore `F` should be sharpened from:

```text
finite_facticization_stability
```

to:

```text
finite_compositional_facticization_stability
```

Meaning:

```text
Every finite stable readout table must remain facticizable under:
  1. finite refinement;
  2. finite coarse-graining;
  3. finite disjoint union;
  4. independent spectator composition;
  5. repeated spectator composition;
  6. operationally equivalent recoding.
```

This is still not PSD as an axiom. It is an operational closure demand.

### 174.39. Why F Must Include Spectator Composition

Without spectator composition, `F` is probably too weak.

A nonpositive comparison direction may be invisible inside the originally
tested context:

```text
local tests pass
but a refined or composite context exposes a negative facticization weight
```

This is exactly the kind of failure seen in composition problems for generalized
decoherence functionals.

Therefore the primitive wall-break form should be:

```text
F:
  A finite readout structure is admissible only if every finite independent
  spectator extension remains a valid finite readout structure.
```

The theorem attempt becomes:

```text
Assume second_order_facticization.
Assume finite rational refinements can approximate every operational comparison
direction.
Assume arbitrary finite spectator composition is admissible.
If the comparison form has a negative direction, some finite refinement or
spectator product produces a negative facticization weight.
Contradiction.
Therefore the comparison form must be positive.
```

New hidden assumption to watch:

```text
finite rational refinements can approximate every operational comparison
direction
```

If this accessibility assumption fails, the negative direction may be
mathematically present but operationally unreachable. Then `F` does not force
positivity; it only forces positivity on reachable directions.

This gives a sharper fork:

```text
F + direction_accessibility => strong positivity pressure
F without direction_accessibility => partial positivity only
```

### 174.40. Revised B1 Candidate

The stronger candidate base is:

```text
B1 = (C, O, I, R, D, F, Q, A)
```

where:

```text
F = finite compositional facticization stability
Q = oriented inheritance-cycle composition
A = finite comparison-direction accessibility
```

`A` is not a Hilbert primitive. It says that if a stable comparison direction is
claimed to exist, finite operational refinements must be able to witness it to
arbitrary declared finite precision.

The new wall-break route is:

```text
second_order_facticization
+ F
+ A
=> strong-positivity-like comparison geometry
=> Hilbert representation pressure
```

Then:

```text
Q
+ product-context exhaustion
+ local tomography separator
=> real-Hilbert-like hidden orientation rejected
=> complex-like carrier pressure
```

This is now much more serious than B0, but still honest:

```text
No Born rule is derived yet.
No complex Hilbert carrier is selected yet.
No metric geometry is derived yet.
```

The next proof target should be:

```text
finite_compositional_facticization_stability
+ second_order_facticization
+ finite_direction_accessibility
=> strong positivity or explicit finite counterexample
```

This is the first real attempt to cross the wall rather than just rename it.

### 174.41. First Counterpressure: F Plus A Is Still Too Weak

The previous route:

```text
second_order_facticization
+ F
+ A
=> strong-positivity-like comparison geometry
```

is still too optimistic unless `A` can access oriented/signed comparison
directions.

Reason:

```text
ordinary finite events only test nonnegative combinations of alternatives
```

But PSD positivity requires nonnegativity on all signed or phase-oriented
comparison directions.

Finite counterexample shape:

```text
G = [[1, 2],
     [2, 1]]
```

For nonnegative event weights \(x_1,x_2\ge 0\):

```text
x^T G x = x_1^2 + 4 x_1 x_2 + x_2^2 >= 0
```

So a readout system that only tests nonnegative event sums sees no problem.

But:

```text
(1,-1)^T G (1,-1) = -2
```

So \(G\) is not positive semidefinite.

This means:

```text
finite coarse-graining/refinement over ordinary events
=> at best copositivity-like constraints
=> not enough for Hilbert geometry
```

Spectator composition alone may still fail to expose the negative direction if
all accessible coefficients remain nonnegative.

Therefore the wall is sharper:

```text
F without oriented accessibility does not force strong positivity.
```

### 174.42. Q Must Enter The Positivity Proof

The orientation primitive `Q` cannot be postponed until after positivity.

It is needed to make signed/phase-like comparison directions operationally
reachable without importing complex Hilbert space.

Revised role:

```text
Q = oriented inheritance-cycle composition
```

not:

```text
Q = later phase decoration
```

`Q` must supply:

```text
orientation reversal
cycle inverse
gauge cancellation of exact labels
stable non-exact cycle comparison
```

This creates operational analogues of negative or phase-oriented comparison
directions:

```text
same local event support
different inherited orientation class
```

Then a negative comparison direction is no longer an unreachable mathematical
artifact. It can be tested by an oriented finite refinement or spectator
construction.

Revised theorem target:

```text
second_order_facticization
+ finite_compositional_facticization_stability
+ oriented_inheritance_cycle_accessibility
=> strong-positivity-like comparison geometry
```

This is stronger and more honest than the previous `F + A` route.

### 174.43. Revised B1: A Must Be Oriented

The base should be written as:

```text
B1 = (C, O, I, R, D, F, Q, A_Q)
```

where:

```text
F   = finite compositional facticization stability
Q   = oriented inheritance-cycle composition
A_Q = finite oriented comparison-direction accessibility
```

`A_Q` says:

```text
If a stable comparison direction is part of the theory's distinguishability
structure, then finite oriented refinements and spectator extensions must be
able to witness it to declared finite precision.
```

This is still not a Hilbert primitive. It does not say:

```text
all vectors in a complex Hilbert space are physical
```

It says:

```text
no stable distinguishability direction may be mathematically present while
permanently shielded from finite oriented facticization.
```

This blocks a common escape:

```text
negative directions exist, but no experiment can ever access them
```

If the direction is truly inaccessible, it must be removed from the stable
distinguishability structure rather than kept as hidden ontology.

### 174.44. Stronger Wall-Break Route

The route now becomes:

```text
B1
+ second_order_facticization
+ local event closure
+ finite spectator composition
+ oriented direction accessibility
=> strong positivity or explicit finite counterexample
```

Proof strategy:

```text
1. Build the finite comparison form from singleton and pairwise facticization
   witnesses.
2. Assume a negative oriented comparison direction exists.
3. Use A_Q to approximate that direction by finite oriented refinements and/or
   spectator extensions.
4. Use second-order facticization to express the corresponding readout weight
   using the same comparison form.
5. The negative direction yields a negative facticization weight.
6. This violates F.
7. Therefore admissible stable comparison forms must be strongly positive on
   all operationally accessible oriented directions.
```

The remaining exact gap:

```text
accessible oriented directions = all stable comparison directions
```

If this equality is proved, the wall moves:

```text
strong positivity-like geometry becomes plausible.
```

If it fails, IDT must choose:

```text
1. restrict the stable distinguishability structure to accessible directions;
2. add a stronger accessibility primitive;
3. accept that Hilbert is not derivable from this base.
```

Current verdict:

```text
B1 must include Q inside the positivity proof.
F alone is insufficient.
The wall is now reduced to oriented accessibility of stable comparison
directions.
```

### 174.45. Proof Attempt: B1 To Strong Positivity

Target theorem candidate:

```text
second_order_facticization
+ finite_compositional_facticization_stability
+ finite_oriented_direction_accessibility
+ operational_closure
=> strong-positivity-like comparison geometry
```

Set up a finite context \(c\) with finitely many local alternatives
\(a_1,\ldots,a_n\).

Let \(V_c\) be the finite oriented comparison module generated by local
alternatives and admissible oriented inheritance refinements. A vector
\(v\in V_c\) is not assumed to be a Hilbert vector. It is an operational
comparison instruction assembled from:

```text
local alternatives
orientation reversal
cycle inverse
finite refinements
spectator extensions
operational recoding
```

Second-order facticization says that every stable finite readout weight is
generated by singleton and pairwise comparison witnesses. Therefore there is a
Hermitian/symmetric comparison form \(G_c\) such that:

```text
mu_c(v) = <v, G_c v>
```

for every operationally admissible finite oriented comparison vector \(v\).

This is not yet positivity. It is only the second-order representation of
readout weights.

Now assume, for contradiction, that \(G_c\) has a negative stable comparison
direction:

```text
exists x in stable_direction_space(c): <x, G_c x> < 0.
```

By finite oriented direction accessibility \(A_Q\), every stable comparison
direction must be approximable by finite oriented facticization instructions.
So there is a finite operational vector \(v_\epsilon\in V_c\) such that:

```text
|<v_epsilon, G_c v_epsilon> - <x, G_c x>| < -<x, G_c x>/2.
```

Hence:

```text
<v_epsilon, G_c v_epsilon> < 0.
```

But \(v_\epsilon\) is a finite oriented facticization instruction. By finite
compositional facticization stability \(F\), every such finite refinement or
spectator extension must remain facticizable. Facticizable readout weights
cannot be negative.

Contradiction.

Therefore:

```text
<x, G_c x> >= 0
```

for every stable comparison direction \(x\).

So \(G_c\) is positive on the operationally closed stable comparison space.

### 174.46. What This Proof Actually Shows

The proof does not show:

```text
B0 proves Hilbert
B1 proves complex Hilbert
B1 proves Born rule
```

It shows the conditional result:

```text
If stable comparison directions are exactly the operational closure of finite
oriented facticization instructions, then F forbids negative directions.
```

This is a real reduction of the wall, but it moves the burden onto one exact
principle:

```text
operational_closure:
  stable distinguishability directions are no larger than the closure of
  finite oriented facticization witnesses.
```

Without this principle, the proof fails.

Failure mode:

```text
There may be mathematically stable but permanently inaccessible negative
directions.
```

IDT should not allow those directions to remain in \(D\). They are hidden
ontology. Therefore the cleaner primitive rule is:

```text
D is defined only up to operational closure of finite oriented witnesses.
```

With that rule, the proof becomes much stronger:

```text
D = closure(finite oriented witnesses)
F = nonnegative facticization under all finite composition/refinement
second_order_facticization = pairwise comparison form
=> positive comparison geometry on D
```

### 174.47. Revised Primitive: Operational Closure Of D

The wall-break base should not let \(D\) be an arbitrary relation.

Replace:

```text
D = stable distinguishability relation
```

with:

```text
D = operational closure of finite oriented facticization witnesses
```

Expanded:

```text
D(c) is the smallest stable distinguishability structure closed under:
  local finite witnesses;
  admissible inheritance transitions;
  oriented cycle reversal/inverse;
  finite refinement/coarse-graining;
  finite spectator composition;
  operational equivalence.
```

This is a serious primitive tightening. It blocks:

```text
unreachable hidden negative directions
unwitnessed stable invariants
global fact tables
PSD imported by declaration
```

The base becomes:

```text
B1' = (C, O, I, R, D_cl, F, Q)
```

where:

```text
D_cl = operationally closed stable distinguishability
```

Then `A_Q` is not a separate primitive. It is folded into the definition of
\(D_{cl}\).

### 174.48. Resulting Theorem Candidate

The theorem should now be stated as:

```text
finite_operational_closure_implies_positive_comparison_geometry
```

Statement:

```text
For any finite IDT context c, assume:
  1. second-order facticization;
  2. D_cl is the operational closure of finite oriented witnesses;
  3. finite compositional facticization stability F;
  4. readout weights are continuous under declared finite approximation.

Then the comparison form induced on D_cl is positive semidefinite on all stable
operational comparison directions.
```

Proof status:

```text
candidate_conditional_proof
```

Important boundary:

```text
This gives strong-positivity-like geometry, not yet complex Hilbert selection.
```

Next theorem after this:

```text
positive_comparison_geometry
+ oriented non-exact cycle composition
+ product-context exhaustion
+ local tomography separator
=> complex-like carrier pressure and real-Hilbert rejection
```

Current verdict:

```text
We can plausibly prove positivity if D is operationally closed.
The primitive correction is not adding PSD.
The primitive correction is forbidding stable distinguishability directions
that cannot be reached by finite oriented witnesses.
```

### 174.49. After Positivity: Carrier Selection Pressure

Assume the previous theorem succeeds:

```text
B1' + second_order_facticization
=> positive comparison geometry on D_cl
```

This still does not select complex Hilbert. It only gives a strong-positivity
like geometry.

The next pressure stack must explain why the surviving carrier is complex-like
rather than real-like, quaternionic-like, exceptional-Jordan-like, boxworld-like,
or generic GPT-like.

Existing finite screens already point to the correct separator roles:

```text
real-like carrier:
  fails product-context/local-tomography separator by hidden joint orientation

boxworld-like GPT:
  fails bounded-correlation and cone/symmetry discipline

unconstrained generic GPT:
  fails finite route-witness completeness

quaternionic/Jordan-like candidates:
  fail some mixture of local tomography, filtering, composition, or finite
  route closure
```

The new B1' interpretation is:

```text
D_cl + F blocks hidden unreachable distinguishability directions.
Q blocks carriers that hide orientation until composite formation.
Product-context exhaustion blocks hidden joint-only stable invariants.
Bounded-correlation discipline blocks superquantum composition.
```

This is not yet a universal carrier theorem, but it gives a single explanatory
shape for the screens.

### 174.50. Real-Hilbert Rejection From B1'

Real Hilbert fails for a precise B1' reason.

In the rebit pair:

```text
local rebit basis: I, X, Z
two-rebit hidden invariant: Y tensor Y
```

The hidden invariant is globally stable but has no local product-context
witness.

In B1' language:

```text
Y tensor Y is a stable composite distinguishability direction
but not in D_cl generated by finite local oriented product witnesses.
```

Therefore real-Hilbert-like composite structure violates:

```text
D_cl operational closure
product-context exhaustion
no hidden joint-only facticizable invariant
```

The rejection is no longer just parameter counting. It has a primitive-level
reason:

```text
real carriers suppress local orientation, then reintroduce it as a composite
hidden invariant.
```

B1' says this is inadmissible:

```text
stable orientation must be locally/finitely witnessable or excluded from D_cl.
```

This is a stronger explanation of why real Hilbert is not a fundamental
composite carrier under IDT.

### 174.51. Boxworld And Generic GPT Rejection From B1'

Boxworld-like theories fail a different part of B1'.

They can satisfy some no-signalling/contextual constraints, but they generally
allow correlations that are too strong for strong-positivity-like geometry.

B1' route:

```text
D_cl + F + second_order_facticization
=> positive comparison geometry
=> Tsirelson-like bounded-correlation pressure
```

So a boxworld/PR-like carrier is rejected if its finite composite tables cannot
be represented inside the positive comparison geometry forced by F.

Generic GPT cones fail unless they provide:

```text
finite route-witness completeness
operational closure of D
composition stability under spectators
bounded correlations
reversible/filtering discipline
```

Without these, generic GPT remains too broad and cannot be selected.

This reframes the generic GPT wall:

```text
not "GPT is too broad" in prose;
but "GPT lacks the B1' operational closure and composition-stability contract."
```

### 174.52. What Still Blocks Complex Hilbert Selection

Even after the above, complex Hilbert is not yet uniquely selected.

The remaining missing theorem is:

```text
positive comparison geometry
+ oriented inheritance cycles
+ local tomography
+ purification/filtering or recoverable transformations
+ bounded correlations
+ finite universal closure
=> complex Hilbert-like carrier
```

Known risk:

```text
These assumptions may already be equivalent to standard reconstruction axioms.
```

To avoid circularity, each assumption must be translated into B1' terms:

```text
local tomography
  = product-context exhaustion over D_cl

purification/filtering
  = recoverability of unfacticized orientation under admissible inheritance

bounded correlations
  = no finite composite table outside positive D_cl geometry

continuous/reversible symmetry
  = closure of oriented inheritance cycles, not primitive unitary dynamics
```

Only if those translations hold is this still below QM.

Current verdict:

```text
B1' plausibly gets us to positive geometry and real/boxworld rejection.
Complex Hilbert selection still needs a non-circular reconstruction theorem
in B1' terms.
```

### 174.53. Next Proof Target

The next theorem should not be full carrier selection.

It should be:

```text
B1_positive_geometry_rejects_real_and_boxworld_carriers
```

Statement:

```text
If B1' yields positive comparison geometry on D_cl, product-context exhaustion
holds for composites, and finite bounded-correlation closure is required, then:

1. real-Hilbert-like carriers with hidden joint-only orientation invariants are
   rejected;
2. boxworld-like carriers with PR/superquantum tables are rejected;
3. unconstrained generic GPT cones remain unselected unless they satisfy the
   B1' closure contract.
```

This is the correct intermediate theorem because it tests whether the new
primitives actually explain the existing finite separators.

If this theorem fails, B1' is probably not the right base.

If it succeeds, the remaining wall is narrower:

```text
complex Hilbert uniqueness from B1' reconstruction assumptions.
```

### 174.54. Translating Purification/Filtering Into B1'

Current finite purification/filtering gates are useful but still conditional.
They assume recoverable extension contexts and posterior support
renormalization. That is not yet below QM.

The B1' translation should avoid saying:

```text
every mixed state has a purification
filters are quantum operations
posterior update is Born renormalization
```

Instead:

```text
purification/filtering = recoverability of unfacticized oriented witnesses
```

Candidate B1' statement:

```text
If a readout packet is operationally mixed, then its missing distinctions must
correspond either to:
  1. finite oriented witnesses recoverable in an admissible extension context;
  2. declared environmental/facticity loss;
  3. an explicit failure ledger entry.
```

Filtering becomes:

```text
a finite facticization that restricts D_cl to a witnessed support while
preserving all recoverable oriented comparisons inside that support.
```

Reversibility of a filter is no longer a quantum postulate. It becomes:

```text
the support witness is bijective inside D_cl and the discarded orientation data
is recoverable from an admissible extension.
```

This matches the current finite route:

```text
nonzero support + bijective support witness => reversible on facticized support
zero support or nonbijective witness => rejected
```

But the B1' version adds a deeper requirement:

```text
support restriction must preserve operational closure of D_cl.
```

If a filter creates a stable direction not generated by finite oriented
witnesses, it is not admissible.

### 174.55. Translating Reversible Symmetry Into B1'

The existing open theorem is Wigner-like:

```text
reversible inheritance symmetries must force unitary or antiunitary context maps
```

This is dangerous as a primitive target because "unitary or antiunitary" is
already Hilbert language.

B1' translation:

```text
reversible symmetry = automorphism of D_cl preserving:
  1. local context incidence;
  2. facticization witnesses R;
  3. finite compositional stability F;
  4. oriented cycle composition Q;
  5. second-order comparison weights.
```

Only after positive comparison geometry is derived may one ask whether these
automorphisms are represented as unitary/antiunitary transformations.

The theorem order must be:

```text
B1' reversible inheritance automorphism
=> isometry of positive comparison geometry
=> Wigner-like representation, if the carrier representation has been built
```

not:

```text
assume unitary maps
=> call them reversible inheritance
```

This avoids importing QM dynamics through the symmetry axiom.

### 174.56. Non-Circular Reconstruction Stack

The carrier-selection route should now be restated as:

```text
1. B1' operational closure gives D_cl.
2. second_order_facticization + F gives positive comparison geometry on D_cl.
3. product-context exhaustion gives local tomography and rejects hidden
   joint-only invariants.
4. recoverable oriented witness extension replaces purification/filtering.
5. D_cl automorphisms replace primitive unitary/reversible symmetry.
6. bounded-correlation closure rejects PR/boxworld-like carriers.
7. only then attempt complex-Hilbert representation.
```

This is the first stack that might be genuinely below QM.

The major remaining risk:

```text
recoverable oriented witness extension may be as strong as purification.
D_cl automorphism richness may be as strong as continuous reversible symmetry.
```

So both need finite failure tests:

```text
recoverability failure:
  a mixed readout has missing distinctions not recoverable in any finite
  admissible extension and not declared as environmental/facticity loss.

symmetry failure:
  a claimed reversible inheritance map preserves local outcomes but fails to
  preserve D_cl, F, Q, or second-order comparison weights.
```

### 174.57. Revised Next Theorem

The next theorem target should be:

```text
B1_recoverable_oriented_filtering_is_non_circular
```

Statement:

```text
Under B1', a filter is admissible iff it restricts to a finite witnessed support,
preserves D_cl on that support, and any discarded oriented witness is either
recoverable in an admissible extension or explicitly recorded as facticity loss.
If the support witness is bijective on D_cl, the filter is reversible on the
facticized support.
```

This is useful because it upgrades the current purification/filtering route
from:

```text
assumed recoverable extension context
```

to:

```text
recoverability explained through D_cl and finite oriented witnesses
```

Status:

```text
candidate_conditional_proof
```

If this theorem works, purification/filtering becomes less circular.

If it fails, purification remains an imported reconstruction principle and
full carrier selection remains blocked.

### 174.58. Circularity Check For Recoverable Oriented Filtering

Question:

```text
Does recoverable_oriented_filtering follow from B1', or does it secretly assume
purification?
```

Minimal finite setting:

```text
context c with finite alternatives A
D_cl(c) generated by finite oriented witnesses
filter f selects support S subset A
```

A filter is B1'-admissible only if:

```text
1. S has at least one finite facticization witness;
2. restricting to S preserves D_cl on S;
3. any discarded oriented witness is either:
   a. recoverable in a declared finite extension context e;
   b. recorded as facticity loss;
4. no new stable direction appears after filtering outside operational closure.
```

This does not require every mixed readout to have a purification. It permits:

```text
irrecoverable loss
```

as long as the loss is explicit and not used later as reversible structure.

Therefore the B1' version is weaker than standard purification:

```text
standard purification-like demand:
  every mixed state has a reversible pure extension.

B1' demand:
  every missing stable distinction is classified as recoverable witness,
  irreversible facticity loss, or failure.
```

This is not circular if the theory never upgrades irreversible loss into
recoverable support.

### 174.59. Finite Failure Tests

Recoverable filtering fails in B1' if any of the following finite witnesses
exists.

Failure A: hidden discarded orientation

```text
filter discards an oriented witness q
q is later needed to restore a stable comparison
q was neither recoverable in an extension nor declared lost
```

Issue:

```text
hidden_recoverability_import
```

Failure B: support closure violation

```text
D_cl(S) contains a stable direction not generated by finite witnesses inside S
or inherited from admissible restriction
```

Issue:

```text
filter_creates_unwitnessed_direction
```

Failure C: zero-support renormalization

```text
filter has no facticized support witness
but posterior readout is still assigned
```

Issue:

```text
zero_support_filter_imports_probability_update
```

Failure D: nonbijective reversible claim

```text
filter is claimed reversible on support
but the support witness is not bijective on D_cl(S)
```

Issue:

```text
nonbijective_filter_claimed_reversible
```

Failure E: extension smuggles Hilbert carrier

```text
recoverable extension exists only by adding Hilbert vector space, unitary map,
or Born normalization as primitive data
```

Issue:

```text
recoverable_extension_imports_QM_carrier
```

These tests make the B1' filtering rule falsifiable.

### 174.60. Proof-Pressure Result

The non-circular theorem can be weakened and made plausible:

```text
B1' does not prove universal purification.
```

But:

```text
B1' can define admissible filtering without purification by separating:
  recoverable oriented witnesses;
  irreversible facticity loss;
  explicit failure ledger entries.
```

The theorem should therefore be:

```text
B1_filtering_does_not_require_universal_purification
```

not:

```text
B1 proves purification.
```

Precise statement:

```text
Under B1', support filtering is admissible if it preserves operational closure
of D_cl on witnessed support and classifies every discarded oriented witness as
recoverable, lost, or failed. Reversibility is allowed only for bijective
recoverable support witnesses.
```

This passes the circularity check because:

```text
irrecoverable loss is allowed and blocks reversibility;
recoverability must be finite-witnessed;
Hilbert/unitary/Born extensions are forbidden as primitive explanations.
```

What remains open:

```text
Whether this weaker B1' filtering principle is strong enough for complex
Hilbert selection.
```

Likely impact:

```text
It may reject bad carriers and prevent circularity,
but it may be weaker than the purification axiom used in standard
reconstructions.
```

So this helps honesty, but may not fully close the carrier-selection wall.

### 174.61. If B1' Is Too Weak: Source Of Purification-Level Strength

The weakened B1' filtering rule avoids circularity, but it may be too weak to
select complex Hilbert.

The missing strength in standard reconstructions is often purification-like:

```text
missing information is recoverable in a larger system
```

If IDT imports that sentence directly, it has probably imported QM
reconstruction structure.

The lower candidate must explain why recoverability holds before facticity.

Candidate principle:

```text
pre_facticity_reversible_accounting
```

Statement:

```text
Before a distinction becomes irreversibly facticized, every oriented
distinguishability loss must be accountably reversible in an admissible
source/context extension, or else it must already be declared as facticity loss.
```

This differs from purification:

```text
purification:
  every mixed state has a pure reversible extension.

pre_facticity_reversible_accounting:
  every pre-facticity loss of oriented distinguishability must be either
  recoverable, explicitly facticized as loss, or rejected as unaccounted.
```

The primitive motivation is not Hilbert. It is:

```text
fundamental unknownness cannot silently delete a stable distinction before
there is a fact that records the deletion.
```

This is stronger than B1' filtering and may supply purification-level pressure
without naming purification.

### 174.62. Why This Might Be The Right Base Principle

The principle fits the theory's central idea:

```text
unknownness becomes physical only through facticized witnesses.
```

Therefore:

```text
unwitnessed loss before facticity is not a physical fact;
unwitnessed loss after facticity must be recorded as irreversible loss;
recoverable loss remains inherited structure, not fact.
```

This creates a three-way accounting law:

```text
orientation/distinguishability channel:
  recoverable inheritance
  OR facticized loss
  OR inadmissible gap
```

In QM language this resembles purification/decoherence bookkeeping, but the IDT
statement is lower:

```text
no silent destruction of stable pre-facticity distinctions
```

It also connects to gravity/source-response:

```text
source-response cochains should account for stable clock/source distortions;
unaccounted source response is not allowed to be silently absorbed into metric
geometry.
```

So the same principle may underlie:

```text
QM: recoverable orientation before measurement
GR: accountable source response before metric projection
```

### 174.63. Circularity Risks

This principle is dangerous if overstated.

Forbidden form:

```text
all pre-measurement evolution is unitary
```

That is QM.

Allowed lower form:

```text
all pre-facticity distinguishability changes must be accounted for by finite
oriented inheritance, declared facticity loss, or failure.
```

Forbidden form:

```text
every mixed readout has a pure extension
```

Allowed lower form:

```text
every missing stable pre-facticity distinction has an accounting status:
recoverable, facticized loss, or inadmissible.
```

Forbidden form:

```text
information is conserved globally
```

Allowed lower form:

```text
no stable operational distinction can disappear from D_cl without an admissible
transition, a facticized loss witness, or a failure ledger entry.
```

The failure ledger is essential. Without it, the principle becomes too close to
universal purification.

### 174.64. Candidate B2 Base

The next candidate base is:

```text
B2 = (C, O, I, R, D_cl, F, Q, L)
```

where:

```text
L = pre-facticity reversible loss accounting
```

Operational rule:

```text
For every finite inheritance transition, the change in D_cl must be classified
as:
  1. preserved/recoverable through oriented inheritance;
  2. facticized loss with a finite witness;
  3. inadmissible unaccounted loss.
```

This gives a stronger filtering/recoverability route:

```text
B2
=> no silent pre-facticity loss
=> recoverable extension pressure
=> purification-like carrier pressure without primitive purification
```

But the status remains:

```text
candidate_base_principle
```

not:

```text
derived_QM
```

### 174.65. First B2 Test

The first test should be finite and brutal:

```text
Can L explain recoverable filtering without requiring universal purification?
```

Test pattern:

```text
input:
  finite context c
  oriented witness q in D_cl(c)
  transition/filter f that removes q from the visible support

required output:
  q is recoverable in an extension;
  OR q has a finite facticized loss witness;
  OR f is inadmissible.
```

Reject:

```text
q disappears silently
```

This is stronger than B1' because it does not merely classify discarded
witnesses after the filter. It requires every pre-facticity transition to
preserve an accounting trail.

If this works, the purification/filtering wall narrows to:

```text
Does L plus F/Q/D_cl imply enough recoverability for complex-Hilbert selection?
```

If it fails, the base is still too weak.

### 174.66. Current Best Base Candidate

The best current candidate is no longer B0 or B1'.

It is:

```text
B2 = (C, O, I, R, D_cl, F, Q, L)
```

with:

```text
C    admissible context cover/category
O    local outcome-event presheaf
I    admissible inheritance transitions
R    facticization/readout witness relation
D_cl operational closure of finite oriented facticization witnesses
F    finite compositional facticization stability
Q    oriented inheritance-cycle composition
L    pre-facticity reversible loss accounting
```

What B2 may plausibly give:

```text
T0_readout recovery
Bell/global-section obstruction
positive comparison geometry
real-Hilbert rejection
boxworld rejection
non-circular recoverability/filtering pressure
```

What B2 still does not yet give:

```text
full complex Hilbert uniqueness
Born rule
unitary dynamics
metric/GR projection
hbar_I or G_I
```

This is the most honest base so far.

### 174.67. L Is Not Unitarity: Three-Mode Accounting

The first risk is that \(L\) secretly says:

```text
all information is conserved
```

That would be unitarity/information conservation in disguise.

To avoid this, \(L\) must have three modes:

```text
1. recoverable inheritance
2. facticized loss
3. inadmissible unaccounted loss
```

Only mode 1 is reversible.

Mode 2 is explicitly irreversible but allowed:

```text
there is a finite witness that the distinction became unavailable as a fact
```

Mode 3 is rejected:

```text
the distinction disappears with no recoverable extension and no loss witness
```

So \(L\) does not forbid irreversibility. It forbids silent irreversibility.

This is the correct lower principle:

```text
not conservation of information;
accountability of distinguishability change.
```

### 174.68. Finite Transition Law

For a finite inheritance transition:

```text
t: c -> c'
```

and a stable oriented witness:

```text
q in D_cl(c)
```

the transition must produce exactly one admissible accounting status:

```text
preserved(q,t)
recoverable(q,t,e)
lost(q,t,l)
rejected(q,t)
```

where:

```text
preserved(q,t):
  q maps to a witness in D_cl(c')

recoverable(q,t,e):
  q maps to a witness in an admissible extension e whose restriction gives c'

lost(q,t,l):
  l is a finite facticized loss witness

rejected(q,t):
  no admissible accounting exists
```

Forbidden:

```text
q is neither preserved, recoverable, lost, nor rejected.
```

This is the precise form of:

```text
no silent pre-facticity loss.
```

### 174.69. Why L Helps Carrier Selection

Carrier selection needs enough recoverability to avoid generic irreversible
collapse at the primitive level.

Without \(L\), a carrier can evade purification/filtering constraints by saying:

```text
missing distinctions just disappeared.
```

With \(L\), that answer is inadmissible unless the disappearance is facticized
as loss.

Therefore:

```text
pre-facticity transformations become recoverability-pressured;
post-facticity transformations may be irreversible if loss is witnessed.
```

This splits dynamics:

```text
before facticity:
  accountable reversible/recoverable inheritance pressure

after facticity:
  irreversible loss allowed, but witnessed
```

This may be the missing non-circular substitute for purification:

```text
not every mixed readout has purification;
but every pre-facticity loss must be recoverable or witnessed as loss.
```

### 174.70. Relation To Measurement

In this language, measurement is not primitive collapse.

Measurement/facticity is:

```text
transition from recoverable oriented distinguishability
to witnessed loss or stable support restriction.
```

Before the fact:

```text
orientation/distinguishability must remain accountably recoverable.
```

After the fact:

```text
some distinctions may be lost, but the loss is itself a facticized witness.
```

This explains why reversible erasure and irreversible measurement differ:

```text
eraser:
  discarded orientation remains recoverable in extension

measurement:
  discarded orientation becomes facticized loss for the accessible context
```

This matches existing recoverability-loss gates but gives them a lower
primitive explanation.

### 174.71. B2 To Purification Pressure, Not Purification

The strongest honest theorem is:

```text
B2_implies_pre_facticity_recoverability_pressure
```

Statement:

```text
For any finite transition before facticity, every change in D_cl must be
preserved or recoverable in an admissible extension unless a finite loss witness
is already facticized. Therefore any carrier that allows silent loss of stable
oriented distinguishability is inadmissible.
```

This does not imply:

```text
all mixed states purify
```

It implies:

```text
all pre-facticity loss must be accountable
```

This may be enough to force many purification-like finite screens. It may still
be weaker than full reconstruction purification.

Status:

```text
candidate_conditional_proof
```

### 174.72. New Wall Location

If B2 works, the wall moves again.

Old wall:

```text
How do we get purification/reversibility without importing QM?
```

New wall:

```text
Is pre-facticity reversible loss accounting strong enough to force the
recoverability structure needed for complex Hilbert uniqueness?
```

This is a better wall because it is below QM vocabulary.

Failure outcome:

```text
B2 gives a clean measurement/recoverability theory but not full Hilbert
selection.
```

Success outcome:

```text
B2 supplies purification-level pressure from facticity accounting.
```

Current verdict:

```text
L is not unitarity if facticized loss is allowed.
L is not purification if universal pure extensions are not required.
L is a candidate lower replacement for both, but still needs a carrier
selection theorem.
```

### 174.73. Batch Primitive Screen

The previous analysis moved too slowly. This section screens ten candidate
principles at once against the same criteria.

Criteria:

```text
below_QM:
  does not name Hilbert, unitary, Born, tensor product, GR metric, hbar, or G

wall_power:
  can attack at least one hard wall: positivity, complex carrier, Born,
  metric/source projection, or Bell/local tomography

non_circular:
  does not smuggle in the target theorem under another name

finite_falsifier:
  admits a finite counterexample/gate shape

projection_value:
  helps at least two of Bell, Hilbert, metric/gravity rather than one isolated
  readout trick
```

Candidate list:

```text
C1  operational closure of D_cl
C2  finite compositional facticization stability F
C3  oriented inheritance-cycle composition Q
C4  pre-facticity loss accounting L
C5  second-order facticization S2
C6  product-context exhaustion P
C7  bounded-correlation closure B
C8  recoverable oriented extension R_o
C9  source-response accounting S_r
C10 scale-projection discipline S_p
```

### 174.74. Batch Result Table

| Candidate | Below QM | Wall Power | Circularity Risk | Finite Falsifier | Verdict |
|---|---:|---:|---:|---:|---|
| C1 `D_cl` | high | high | low | high | core primitive |
| C2 `F` | high | high | medium | high | core primitive |
| C3 `Q` | high | high | medium | high | core primitive |
| C4 `L` | high | medium-high | medium | high | core primitive if failure ledger remains mandatory |
| C5 `S2` | medium-high | high | medium | high | primitive candidate or sector law |
| C6 `P` | high | medium | low | high | theorem obligation, not primitive |
| C7 `B` | medium | medium-high | medium-high | high | theorem obligation, not primitive |
| C8 `R_o` | medium | high | high | medium | dangerous bridge/theorem, not primitive yet |
| C9 `S_r` | high | high for gravity | medium | medium | parallel gravity primitive candidate |
| C10 `S_p` | high | medium | low | medium | boundary principle, not core primitive |

Immediate conclusion:

```text
Core base should not contain all ten.
```

The base should contain the smallest set that blocks false primitives and gives
wall-breaking pressure:

```text
D_cl, F, Q, L, maybe S2
```

The rest should be theorem obligations or projection modules:

```text
P, B, R_o, S_r, S_p
```

### 174.75. Candidate-by-Candidate Pressure

C1 `D_cl`: operational closure of stable distinguishability

```text
Strength:
  forbids hidden unreachable distinguishability directions.

Wall attacked:
  positivity and hidden-joint invariants.

Failure test:
  stable direction exists but no finite oriented witness/refinement/spectator
  can access it.

Verdict:
  keep as core primitive.
```

C2 `F`: finite compositional facticization stability

```text
Strength:
  turns negative comparison directions into finite facticization failures.

Wall attacked:
  strong-positivity-like geometry.

Failure test:
  finite spectator/refinement creates negative or contradictory readout weight.

Risk:
  if composition is too weak, only copositivity follows.

Verdict:
  keep as core primitive, but require spectator composition.
```

C3 `Q`: oriented inheritance-cycle composition

```text
Strength:
  supplies operational signed/oriented directions without complex numbers.

Wall attacked:
  real-Hilbert hidden orientation and metric/holonomy projection.

Failure test:
  cycle orientation is needed for a stable comparison but cannot be
  facticized or inverted.

Risk:
  if phases are inserted numerically, this imports QM.

Verdict:
  keep as core primitive in purely oriented/gauge form.
```

C4 `L`: pre-facticity loss accounting

```text
Strength:
  supplies recoverability pressure without universal purification.

Wall attacked:
  filtering/reversibility circularity.

Failure test:
  stable oriented witness disappears before facticity with no recovery, loss
  witness, or rejection.

Risk:
  if facticized loss is disallowed, it becomes unitarity.

Verdict:
  keep as core primitive only with mandatory failure/loss ledger.
```

C5 `S2`: second-order facticization

```text
Strength:
  makes readout weights pairwise-comparison generated, matching I3=0.

Wall attacked:
  route from finite facticity to comparison geometry.

Failure test:
  stable no-refit finite I3 != 0.

Risk:
  may be QM-sector law, not universal base law.

Verdict:
  keep as a sector-limited primitive candidate unless/until broader evidence
  supports universality.
```

C6 `P`: product-context exhaustion

```text
Strength:
  rejects hidden joint-only invariants and gives local tomography separator.

Wall attacked:
  real-Hilbert and joint-only carrier excess.

Failure test:
  composite stable invariant has no product-context witness.

Risk:
  as primitive it may overconstrain nonlocal/field sectors.

Verdict:
  theorem obligation for composites, not base primitive.
```

C7 `B`: bounded-correlation closure

```text
Strength:
  rejects boxworld/PR-like superquantum tables.

Wall attacked:
  generic GPT cone.

Failure test:
  finite composite table exceeds positive-geometry/Tsirelson-like bound.

Risk:
  if stated as Tsirelson bound, it imports QM.

Verdict:
  theorem obligation derived from D_cl+F+Q, not primitive.
```

C8 `R_o`: recoverable oriented extension

```text
Strength:
  could replace purification if derived.

Wall attacked:
  purification/filtering and carrier selection.

Failure test:
  missing oriented witness in a mixed readout cannot be recovered, lost, or
  rejected.

Risk:
  very high: can easily become purification axiom.

Verdict:
  not primitive. It must be theorem pressure from L.
```

C9 `S_r`: source-response accounting

```text
Strength:
  gravity-facing analogue of L: source/clock distortions cannot disappear
  silently before projection.

Wall attacked:
  metric/source cochain and GR projection.

Failure test:
  stable clock/source response is absorbed into metric readout without
  source-response witness or loss/failure ledger.

Risk:
  if normalized by G_N, imports GR calibration.

Verdict:
  parallel gravity primitive candidate, probably not needed for QM carrier
  proof but needed for unified base.
```

C10 `S_p`: scale-projection discipline

```text
Strength:
  prevents QM-scale gates from silently claiming gravity-scale closure.

Wall attacked:
  Hilbert/Bell/metric common-source overclaim.

Failure test:
  route uses a projection at one scale to close a claim at another without
  suppression or transfer theorem.

Risk:
  weak wall-breaking power.

Verdict:
  boundary principle, not core primitive.
```

### 174.76. Batch Survivor Base

The best compact base after batch screening is:

```text
B2_QM = (C, O, I, R, D_cl, F, Q, L, S2?)
```

where `S2` remains marked:

```text
sector_limited_candidate
```

The broader base for Hilbert/Bell/metric should be:

```text
B2_full = (C, O, I, R, D_cl, F, Q, L, S_r, S_p)
```

with `S2`, `P`, `B`, and `R_o` treated as theorem obligations:

```text
S2 = second-order facticization theorem or sector law
P  = product-context exhaustion theorem
B  = bounded-correlation theorem
R_o = recoverable oriented extension theorem
```

This split matters:

```text
Core primitives:
  define what counts as admissible unknownness/facticity/inheritance.

Theorem obligations:
  prove the physical shape of QM-like and metric-like projections.
```

### 174.77. Batch Verdict

The most promising route is not:

```text
add purification
add unitary
add Hilbert
```

It is:

```text
D_cl + F + Q + L
=> positivity and recoverability pressure
```

Then:

```text
S2 + P + B + R_o
=> QM carrier-selection pressure
```

And in parallel:

```text
S_r + S_p
=> metric/source projection pressure
```

Current best status:

```text
strongest core primitive set:
  C, O, I, R, D_cl, F, Q, L

candidate sector law:
  S2

not primitives:
  product tomography, bounded correlations, purification/recoverability
  extension, metric projection
```

This is a much cleaner base than B0 and avoids putting reconstruction axioms
directly into the primitive layer.

### 174.78. Hypothesis Batch 1: Stop Cataloging Walls

This batch tests hypotheses directly. Each hypothesis gets a kill-test and a
verdict.

Batch target:

```text
B2_QM = (C, O, I, R, D_cl, F, Q, L, S2?)
```

Question:

```text
Can this base move toward Hilbert/Born/carrier selection, or does it only
produce better labels for the old walls?
```

Verdict labels:

```text
fails        = finite/logical counterexample survives the assumptions
conditional  = survives only with explicit extra condition
survives     = no current counterexample inside declared scope
```

### 174.79. H1-H10 Batch Table

| ID | Hypothesis | Kill Test | Verdict |
|---|---|---|---|
| H1 | `D_cl+F+Q+L => S2` | allow finite stable third-order facticization with witnesses and accounting | fails |
| H2 | `D_cl+F+Q+L+S2 => positivity` | negative oriented direction accessible by finite witness | conditional survives |
| H3 | positivity => bounded Bell correlations | require joint quantal/context measure for Bell table | conditional |
| H4 | positivity + product exhaustion rejects real Hilbert | rebit `Y tensor Y` hidden joint invariant | survives |
| H5 | positivity + bounded closure rejects boxworld | PR table outside positive geometry | conditional survives |
| H6 | H2-H5 imply complex Hilbert uniqueness | Euclidean/Jordan/route-closed GPT residuals | fails |
| H7 | `L => universal recoverable extension` | facticized loss is allowed by L | fails |
| H8 | stronger pre-facticity no-silent-loss gives recoverability pressure | irreversible facticity boundary must be explicit | conditional |
| H9 | `B2_full => metric projection` | source-response cochain missing or calibrated by GR | conditional/fails for now |
| H10 | positivity + S2 => Born readout | needs normalization/event-probability interpretation | conditional |

### 174.80. H1: Core Does Not Derive S2

Hypothesis:

```text
D_cl + F + Q + L => second_order_facticization
```

Kill construction:

```text
finite context with singleton, pairwise, and ternary facticization witnesses
all witnesses are operationally closed in D_cl
all transitions have L accounting
all finite compositions preserve nonnegative facticization weights
ternary witness produces stable I3 != 0
```

Nothing in `D_cl`, `F`, `Q`, or `L` forbids a primitive third-order witness if it
is finite, stable, accounted, and compositionally nonnegative.

Therefore:

```text
H1 fails.
```

Consequence:

```text
S2 cannot be claimed as derived from the current B2 core.
```

It must be one of:

```text
1. sector law for QM-like readouts;
2. additional primitive;
3. theorem requiring another principle not yet identified;
4. false outside QM-scale sectors.
```

This is a real result. It prevents pretending that `I3=0` has been derived.

### 174.81. H2: Positivity Survives If S2 Is Added

Hypothesis:

```text
D_cl + F + Q + L + S2 => positive comparison geometry
```

Kill test:

```text
assume negative oriented direction x
use D_cl/Q to approximate x by finite oriented witness v
use S2 to express readout weight as pairwise comparison form
negative <v,Gv> gives negative facticization weight
F rejects it
```

This works only if:

```text
D_cl includes operational closure of all stable oriented directions
readout weights are continuous under declared finite approximation
Q supplies signed/oriented access
```

Verdict:

```text
H2 conditional survives.
```

This is currently the strongest theorem candidate:

```text
B2_plus_S2_implies_positive_comparison_geometry
```

### 174.82. H3-H5: Separator Power

H3:

```text
positive comparison geometry => bounded Bell correlations
```

This is not automatic. It needs a joint context/quantal-measure analogue for
the Bell table. With that extra structure, strong positivity is known to create
Tsirelson-like geometric bounds in the analogous quantum-measure setting.

Verdict:

```text
conditional.
```

H4:

```text
positive geometry + product-context exhaustion => reject real Hilbert
```

The rebit separator survives:

```text
Y tensor Y is stable globally but absent from local product D_cl.
```

Verdict:

```text
survives.
```

H5:

```text
positive geometry + bounded-correlation closure => reject boxworld
```

PR/boxworld tables are rejected if the finite Bell table must live inside the
positive comparison geometry.

Verdict:

```text
conditional survives.
```

### 174.83. H6: Complex Hilbert Uniqueness Still Fails

Hypothesis:

```text
H2 + H3 + H4 + H5 => complex Hilbert uniqueness
```

Kill test:

```text
route-closed GPT and Jordan-like residuals can satisfy several screens while
remaining underclassified without a universal representation theorem.
```

Existing finite screens already show this pattern:

```text
complex Hilbert-like survives;
some non-complex candidates are rejected;
generic/route-closed residuals remain underdetermined.
```

Therefore:

```text
H6 fails.
```

This means the current base plus separator stack is not enough for full carrier
selection.

### 174.84. H7-H8: Recoverability Pressure

H7:

```text
L => universal recoverable extension
```

Kill test:

```text
L explicitly allows facticized loss.
```

Therefore:

```text
H7 fails.
```

This is good: it means L is not just purification in disguise.

H8:

```text
L gives recoverability pressure before facticity
```

This survives if the facticity boundary is explicit:

```text
before facticity:
  loss must be recoverable or rejected

at/after facticity:
  loss may be witnessed and irreversible
```

Verdict:

```text
conditional.
```

The next actual test should target this:

```text
pre_facticity_loss_accounting_gate
```

not another abstract wall.

### 174.85. H9-H10: Metric And Born

H9:

```text
B2_full => metric projection
```

This fails unless source-response accounting supplies a real cochain before GR
calibration:

```text
S_r must define source response without G_N or metric input.
S_p must prevent scale transfer without suppression theorem.
```

Verdict:

```text
conditional/fails for now.
```

H10:

```text
positive comparison geometry + S2 => Born readout
```

This is close but not complete. A positive comparison form gives a quadratic
measure-like object, but Born readout also needs:

```text
normalization
event-probability interpretation
context update/facticity rule
coarse-graining consistency
```

Verdict:

```text
conditional.
```

Candidate theorem:

```text
positive_S2_geometry_implies_quadratic_readout_measure
```

not yet:

```text
universal Born rule.
```

### 174.86. Batch 1 Result

The batch gives a sharper outcome than another wall list.

Failed hypotheses:

```text
H1: B2 core derives S2
H6: current separator stack uniquely selects complex Hilbert
H7: L implies universal purification
```

Surviving conditional hypotheses:

```text
H2: B2 + S2 gives positive comparison geometry
H3: positive geometry bounds Bell correlations with joint-table structure
H4: positive geometry + product exhaustion rejects real Hilbert
H5: positive geometry + bounded closure rejects boxworld
H8: L gives pre-facticity recoverability pressure
H10: positive S2 geometry gives quadratic readout measure
```

Current best action:

```text
stop trying to derive S2 from B2 core;
promote S2 to explicit sector-law candidate for QM-like readouts;
test H2, H8, and H10 as the next proof batch.
```

This is the highest-yield next route:

```text
Batch 2:
  T1 B2 + S2 => positive geometry
  T2 L => pre-facticity recoverability pressure
  T3 positive S2 geometry => quadratic readout measure
```

If Batch 2 fails, this base likely cannot derive QM.

If Batch 2 survives, carrier selection becomes the next batch rather than the
next slogan.

### 174.87. Hypothesis Batch 2: T1/T2/T3

Batch 2 tests the three survivors from Batch 1.

Targets:

```text
T1: B2 + S2 => positive comparison geometry
T2: L => pre-facticity recoverability pressure
T3: positive S2 geometry => quadratic readout measure
```

Batch verdict summary:

| Target | Verdict | Main Reason |
|---|---|---|
| T1 | conditional survives | works if D_cl is operationally closed and Q gives oriented access |
| T2 | survives as accounting theorem | L forbids silent pre-facticity loss without requiring purification |
| T3 | partial survives | gives quadratic measure-like readout, not full Born rule |

### 174.88. T1 Proof Pressure: B2 Plus S2 To Positivity

Assumptions:

```text
B2 core:
  C, O, I, R, D_cl, F, Q, L

S2:
  second-order facticization
```

Proof skeleton:

```text
1. In any finite context c, S2 makes stable readout weights depend only on
   singleton and pairwise oriented comparison witnesses.
2. Therefore each context has a finite comparison form G_c on D_cl(c).
3. Suppose G_c has a negative stable direction x.
4. Because D_cl is operational closure, x is approximable by finite oriented
   witnesses.
5. Because Q supplies orientation reversal/inverse, signed comparison
   directions are operationally meaningful.
6. For close enough finite witness v, the readout weight v*G_c*v is negative.
7. This violates F, because finite compositional facticization stability forbids
   negative facticization weights under refinement/spectator composition.
8. Therefore G_c is positive on D_cl(c).
```

Kill-test:

```text
negative stable direction exists but is not reachable by finite oriented
witnesses
```

This is blocked by the definition of \(D_{cl}\). If a direction is not in the
operational closure, it is not part of stable distinguishability.

Second kill-test:

```text
negative direction is reachable but S2 does not express its weight by the same
comparison form
```

This kills the theorem if S2 is absent or sector-limited away from the tested
context.

Verdict:

```text
T1 conditional survives.
```

Precise theorem:

```text
B2_plus_S2_implies_positive_comparison_geometry
```

Scope:

```text
finite contexts where S2 is declared active and D_cl/Q/F hold.
```

Not proved:

```text
S2 itself
complex Hilbert
Born rule
```

### 174.89. T2 Proof Pressure: L To Recoverability Pressure

Assumption:

```text
L = pre-facticity reversible loss accounting
```

Proof skeleton:

```text
1. Let q be a finite oriented witness in D_cl(c).
2. Let t be a finite inheritance transition before facticity.
3. L requires q under t to be classified as preserved, recoverable, lost, or
   rejected.
4. Before facticity, lost(q,t,l) is not allowed unless l is already a finite
   facticized loss witness.
5. Therefore any unfacticized disappearance must be preserved/recoverable or
   rejected.
6. Thus any carrier allowing silent pre-facticity loss is inadmissible.
```

Kill-test:

```text
q disappears before facticity with no extension, no loss witness, and no
failure.
```

This directly violates L.

Second kill-test:

```text
L forces every q to be recoverable in a pure extension.
```

This fails against L because L allows facticized loss and rejection. Therefore
T2 is not purification in disguise.

Verdict:

```text
T2 survives as an accounting theorem.
```

Precise theorem:

```text
B2_L_forbids_silent_pre_facticity_loss
```

Not proved:

```text
universal purification
unitary dynamics
full reversible evolution
```

### 174.90. T3 Proof Pressure: Positive S2 Geometry To Quadratic Readout

Assumptions:

```text
positive comparison geometry on D_cl
S2 second-order facticization
finite context c
```

Proof skeleton:

```text
1. S2 says finite readout weights are generated by singleton and pairwise
   comparison witnesses.
2. T1 supplies positivity of the comparison form on D_cl.
3. Therefore each admissible event/readout vector v has nonnegative weight:
   mu(v) = v*Gv >= 0.
4. Finite additivity over decohered/facticized exclusive alternatives follows
   only when cross terms vanish or are explicitly accounted by the context.
5. Normalized probabilities require a positive total context weight and an
   explicit normalization rule.
```

Kill-test:

```text
positive quadratic weights exist, but no rule identifies normalized context
weights with observed probabilities.
```

This kills the universal Born claim.

Second kill-test:

```text
coarse-graining changes context totals or leaves cross terms unaccounted.
```

This kills probability-readout unless context normalization and coarse-graining
consistency are added.

Verdict:

```text
T3 partial survives.
```

What it proves:

```text
positive_S2_geometry_implies_quadratic_measure_like_readout
```

What it does not prove:

```text
universal Born rule
measurement update
context normalization
probability interpretation for every readout
```

Extra assumptions needed:

```text
N = context normalization and positive total weight
Cg = coarse-graining consistency
Ex = exclusivity/decoherence condition for additivity
```

### 174.91. Batch 2 Result

Batch 2 does not close QM, but it yields real progress.

Survives:

```text
T1: B2 + S2 => positive comparison geometry
T2: L => no silent pre-facticity loss
```

Partial:

```text
T3: positive S2 geometry => quadratic measure-like readout
```

Fails as overclaim:

```text
positive S2 geometry => universal Born rule
```

New required assumptions for the readout layer:

```text
N  context normalization
Cg coarse-graining consistency
Ex exclusivity/decoherence additivity condition
```

These are not primitive candidates yet. They are readout theorem obligations.

### 174.92. Hypothesis Batch 3 Targets

Next batch should test:

```text
H11: quadratic measure-like readout + N + Cg + Ex => Born-like context
     probability

H12: T1 + T2 + H11 + product-context exhaustion => real/boxworld rejection
     from B2 terms

H13: T1 + T2 + H11 + P + bounded closure + recoverable oriented extension
     => complex-Hilbert pressure stronger than finite separators

H14: H13 => complex Hilbert uniqueness
```

Expected:

```text
H11 likely conditional survives.
H12 likely survives.
H13 uncertain.
H14 probably fails without a universal representation/classification theorem.
```

This is now a real hypothesis-testing pipeline:

```text
Batch 1 killed S2 derivation and complex uniqueness.
Batch 2 salvaged positivity and accounting, downgraded Born to quadratic
measure-like readout.
Batch 3 must test whether readout obligations plus separator obligations
produce actual carrier pressure.
```

### 174.93. Hypothesis Batch 3: Readout And Carrier Pressure

Batch 3 tests:

```text
H11: quadratic measure-like readout + N + Cg + Ex
     => Born-like context probability

H12: T1 + T2 + H11 + product-context exhaustion
     => real/boxworld rejection from B2 terms

H13: T1 + T2 + H11 + P + bounded closure + recoverable oriented extension
     => complex-Hilbert pressure stronger than finite separators

H14: H13 => complex Hilbert uniqueness
```

Summary:

| ID | Verdict | Reason |
|---|---|---|
| H11 | conditional survives | gives Born-like finite context probabilities, not universal Born |
| H12 | conditional survives | explains real/boxworld rejection through B2-derived screens |
| H13 | partial/conditional | gives stronger pressure, not uniqueness |
| H14 | fails | uniqueness still needs representation/classification theorem |

### 174.94. H11: Born-Like Context Probability

Hypothesis:

```text
quadratic measure-like readout + N + Cg + Ex
=> Born-like context probability
```

Definitions:

```text
N:
  every admissible finite readout context has positive total weight and a
  declared normalization.

Cg:
  coarse-graining preserves normalized weights when interference/cross terms
  are either absent or explicitly retained by the coarser context.

Ex:
  exclusive/facticized alternatives have no unaccounted cross terms.
```

Proof pressure:

```text
1. T3 gives nonnegative quadratic weights mu(E) for admissible events.
2. N gives total context weight Z_c > 0.
3. Define p(E|c)=mu(E)/Z_c.
4. Ex gives additivity over facticized exclusive alternatives.
5. Cg prevents probability drift under admissible coarse-graining.
```

Kill-test:

```text
context has positive quadratic weights but no stable total normalization
```

Then no probability table follows.

Second kill-test:

```text
exclusive alternatives retain unaccounted cross terms
```

Then additivity fails.

Verdict:

```text
H11 conditional survives.
```

Precise theorem:

```text
positive_quadratic_context_measure_with_N_Cg_Ex
=> Born-like finite context probability
```

Boundary:

```text
This is not universal Born rule.
It is a finite context probability theorem.
```

### 174.95. H12: Real/Boxworld Rejection From B2 Terms

Hypothesis:

```text
T1 + T2 + H11 + product-context exhaustion
=> real/boxworld rejection from B2 terms
```

Real-Hilbert path:

```text
T1 gives positive D_cl geometry.
Q makes orientation operationally meaningful.
P/product-context exhaustion requires composite stable orientations to have
local product witnesses.
Real-Hilbert rebit composition has Y tensor Y as a stable hidden orientation
with no local product witness.
Therefore it violates D_cl/P.
```

Verdict for real-Hilbert:

```text
survives.
```

Boxworld path:

```text
H11 gives finite context probability tables from positive quadratic readout.
T1 constrains those tables to positive comparison geometry.
Bounded closure rejects PR/superquantum composites outside that geometry.
Boxworld-like tables fail this bounded closure.
```

Verdict for boxworld:

```text
conditional survives.
```

Reason for conditional:

```text
bounded closure must be derived from positive geometry or explicitly declared
as theorem obligation, not inserted as Tsirelson primitive.
```

Batch verdict:

```text
H12 conditional survives.
```

### 174.96. H13: Complex-Hilbert Pressure Stronger Than Finite Screens

Hypothesis:

```text
T1 + T2 + H11 + P + bounded closure + recoverable oriented extension
=> complex-Hilbert pressure stronger than finite separators
```

This does give stronger pressure than the old finite screens because the
separators now have a common base-level explanation:

```text
D_cl:
  no hidden unreachable stable directions

F:
  no negative facticization under finite composition

Q:
  orientation must be locally/finitely accountable

L:
  no silent pre-facticity loss

H11:
  finite context probabilities come from positive quadratic readout
```

Together, these reject:

```text
real carriers:
  hidden composite orientation

boxworld carriers:
  superpositive/superquantum composite probabilities

unconstrained GPT:
  missing D_cl/F/Q/L closure contract
```

But the hypothesis still does not select complex Hilbert uniquely.

Kill-test:

```text
a route-closed GPT/Jordan-like subtheory satisfies D_cl/F/Q/L, finite context
probability, local tomography, bounded correlations, and recoverable filtering
on the checked finite family, but no universal representation theorem maps it
uniquely to complex Hilbert.
```

This remains possible at the current level.

Verdict:

```text
H13 partial/conditional.
```

It gives:

```text
complex-Hilbert pressure
```

not:

```text
complex-Hilbert selection.
```

### 174.97. H14: Complex Hilbert Uniqueness

Hypothesis:

```text
H13 => complex Hilbert uniqueness
```

Kill-test:

```text
No theorem currently proves that all carriers satisfying the B2-derived
pressure stack are equivalent to complex Hilbert spaces.
```

Known residuals:

```text
route-closed GPT subtheories
Jordan-like residuals
nonfinite/unwitnessed classifications
possible sector-limited S2
possible weakened recoverability vs full purification gap
```

Therefore:

```text
H14 fails.
```

This is not a vague wall. It is a precise missing theorem:

```text
B2_representation_classification_theorem
```

Statement needed:

```text
Every finite and nonfinite carrier satisfying:
  D_cl operational closure;
  F compositional facticization stability;
  Q oriented cycle composition;
  L pre-facticity loss accounting;
  S2 second-order facticization;
  N/Cg/Ex readout normalization;
  product-context exhaustion;
  bounded-correlation closure;
  recoverable oriented extension;
is representationally equivalent to a complex-Hilbert-like carrier.
```

This theorem is not currently proved.

### 174.98. Batch 3 Result

Survives:

```text
H11: finite Born-like context probability, conditional on N/Cg/Ex
H12: B2-derived real/boxworld rejection, conditional on bounded closure
```

Partial:

```text
H13: stronger complex-Hilbert pressure
```

Fails:

```text
H14: complex Hilbert uniqueness
```

New exact bottleneck:

```text
B2_representation_classification_theorem
```

Batch 4 should not invent more primitives.

Batch 4 should test representation/classification routes:

```text
R1: Can B2 pressure be reduced to known reconstruction assumptions without
    circularity?

R2: Can route-closed GPT/Jordan residuals be explicitly killed by one of the
    B2 obligations?

R3: Is there a finite countermodel satisfying all current B2 obligations but
    not complex Hilbert?

R4: If yes, what minimal non-QM assumption kills it?
```

If R3 finds a countermodel, the current base fails to derive QM.

If R3 cannot find one and R1/R2 survive, then the next step is a real
classification theorem attempt.

### 174.99. Hypothesis Batch 4: Classification And Countermodels

Batch 4 tests the current strongest route against the question that matters:

```text
Can a non-complex-Hilbert carrier pass the current B2 obligations?
```

The tested route is:

```text
B2 = C,O,I,R,D_cl,F,Q,L
+ S2
+ N/Cg/Ex
+ product-context exhaustion
+ bounded-correlation closure
+ recoverable oriented extension
```

where:

```text
D_cl:
  finite operational closure of distinguishability witnesses

F:
  compositional facticization stability

Q:
  oriented inheritance-cycle composition

L:
  pre-facticity loss accounting

S2:
  second-order facticization / no third-order interference

N/Cg/Ex:
  normalization, coarse-graining consistency, exclusivity additivity
```

This batch does not upgrade any claim to proof.

It asks whether the current wall is:

```text
missing representation theorem
```

or:

```text
known countermodel against the primitive base
```

### 174.100. R1: Reconstruction-Assumption Reduction

Question:

```text
Can the B2 pressure stack be reduced to known reconstruction assumptions
without importing QM?
```

Mapping:

```text
D_cl + F:
  finite operational state/effect closure and stable witness separation

S2 + N/Cg/Ex:
  quadratic-measure-like finite probability calculus

product-context exhaustion:
  local tomography/product readout separation

bounded-correlation closure:
  no boxworld-like superquantum composite excess

Q:
  accountable oriented phase/cycle composition

L + recoverable oriented extension:
  recoverability pressure, weaker than full purification
```

This does not directly assume Hilbert space, complex scalars, Born amplitudes,
or a tensor product as primitive ontology.

But it is not yet a derivation either.

The strongest honest statement is:

```text
B2 pressure can be expressed as a below-QM reconstruction constraint stack,
provided S2 and the readout axioms are treated as explicit sector obligations.
```

The possible circularity would be:

```text
Q/recoverability are secretly complex phase or purification in new words.
```

To avoid that, their allowed formulation must stay finite and operational:

```text
Q:
  finite oriented cycle composition must be witness-accountable.

recoverable oriented extension:
  lost pre-facticity orientation cannot disappear silently; if it becomes
  relevant to future distinguishability, the route must expose an accountable
  extension witness.
```

Verdict:

```text
R1 survives as a conditional reduction.
```

It supports a reconstruction route, not a uniqueness theorem.

### 174.101. R2: Residual Killer Check

Question:

```text
Can route-closed GPT/Jordan residuals be killed by existing B2 obligations?
```

Current graph signals:

```text
real-Hilbert-like composites:
  rejected by hidden joint-only invariant under context-product exhaustion

represented non-complex Jordan samples:
  conditionally rejected by the non-complex Jordan separator

unconstrained generic GPT:
  rejected when it lacks finite route closure and bounded composite control

finite route-closed GPT slices:
  collapse to complex-Hilbert-like under the finite sub-frontier
```

Remaining gap:

```text
broader generic GPT cone:
  reduced to nonfinite or unwitnessed residual
```

Therefore the existing B2 obligations do kill several important residuals, but
not all possible residuals.

The unresolved class is not:

```text
ordinary finite rebit counterexample
ordinary finite boxworld counterexample
represented finite non-complex Jordan sample
```

The unresolved class is:

```text
nonfinite or unwitnessed GPT-like carrier whose excess degrees never appear in
the finite witness routes currently required by the graph.
```

Verdict:

```text
R2 partial.
```

Existing obligations kill the finite represented residuals in the current
graph, but they do not kill the nonfinite/unwitnessed residual.

### 174.102. R3: Finite Countermodel Search

Question:

```text
Is there a known finite carrier that satisfies every current B2 obligation and
is not complex Hilbert?
```

The attempted countermodel classes:

| candidate | reason to test | current result |
|---|---|---|
| real Hilbert / rebit composite | locally invisible joint invariant | fails product-context exhaustion |
| boxworld-like GPT | boundedness and composite excess stress test | fails bounded-correlation closure |
| unconstrained GPT cone | too many possible state/effect cones | fails finite route closure contract |
| represented non-complex Jordan sample | finite alternative symmetric cone | conditionally rejected by separator |
| finite route-closed GPT slice | strongest finite generic residual | collapses to complex-Hilbert-like in current sub-frontier |

No current finite countermodel is present in the research graph that satisfies
all of:

```text
D_cl
F
Q
L
S2
N/Cg/Ex
product-context exhaustion
bounded-correlation closure
recoverable oriented extension
```

This is not a proof that no such countermodel exists.

It only says:

```text
the current graph has no explicit finite countermodel after the Batch 4
screens.
```

The remaining possible countermodel shape is narrower:

```text
finite-looking at every checked route, but with nonfinite or unwitnessed
degrees outside the route closure.
```

That means the next real question is compactness/witness completeness, not
another finite separator demo.

Verdict:

```text
R3: no explicit finite countermodel found in the current graph.
```

Residual status:

```text
open, because absence of a found finite countermodel is not a classification
theorem.
```

### 174.103. R4: Minimal Non-QM Assumption That Kills The Residual

The residual can be targeted by one assumption that is stronger than the
current screens but still not Hilbert-specific:

```text
finite_universal_witness_closure
```

Definition sketch:

```text
Every stable admissible carrier degree that can affect any facticizable
distinguishability relation must have a finite oriented witness route with a
uniformly bounded generator description.
```

Equivalent operational reading:

```text
No stable physical degree may exist only as a nonfinite or forever-unwitnessed
residual if it can change any possible readout.
```

This assumption would attack exactly the known blocker:

```text
nonfinite/unwitnessed GPT residual
```

It does not say:

```text
states are Hilbert vectors
effects are projectors
probabilities are Born probabilities
all systems purify
```

It says:

```text
stable distinguishability must be finitely route-witnessable.
```

So it is plausibly below-QM.

But it is also strong.

If added as an axiom without proof, it would become a major primitive. A cleaner
route is to treat it as a theorem obligation:

```text
D_cl + F + Q + L + finite context generation
=> finite_universal_witness_closure
```

or, if that fails:

```text
finite_universal_witness_closure
```

must be declared as a boundary assumption, not hidden inside "formal_proof".

Verdict:

```text
R4 identifies the exact next assumption/theorem candidate.
```

### 174.104. Batch 4 Result

Confirmed:

```text
1. The current B2 stack is not obviously circular if Q and recoverability stay
   finite, operational, and witness-accountable.

2. The current graph already rejects the main finite represented alternatives:
   real composites, boxworld-like excess, unconstrained GPT, represented
   non-complex Jordan samples, and finite route-closed GPT slices.

3. No explicit finite non-complex-Hilbert countermodel satisfying all current
   B2 obligations was found in the graph.
```

Still open:

```text
1. This is not a classification theorem.

2. The nonfinite/unwitnessed GPT residual remains.

3. Complex Hilbert uniqueness still requires a representation theorem or a
   compactness/witness-completeness theorem.
```

Exact next bottleneck:

```text
finite_universal_witness_closure
```

or:

```text
B2_compactness_witness_completeness_theorem
```

This is the first point in the current investigation where the wall is not
"many generic GPTs remain" but a sharper proposition:

```text
If all stable distinguishability must be finitely route-witnessable, then the
remaining nonfinite/unwitnessed GPT residual is inadmissible.
```

### 174.105. Batch 5 Targets

Batch 5 should test the compactness/witness-completeness route directly:

```text
H15:
  D_cl + F + Q + L + finite context generation
  => finite_universal_witness_closure

H16:
  finite_universal_witness_closure
  + S2 + N/Cg/Ex + product-context exhaustion + bounded closure
  => no nonfinite/unwitnessed GPT residual

H17:
  H16 + recoverable oriented extension
  => carrier-selection classification pressure

H18:
  H17 => complex Hilbert uniqueness
```

Expected risk:

```text
H15 may fail.
```

If H15 fails, the theory needs either:

```text
a new primitive below QM that justifies finite universal witness closure
```

or:

```text
an honest boundary that full carrier selection is conditional on finite
witness compactness.
```

That is the next non-micro step.

### 174.106. Hypothesis Batch 5: Witness Compactness

Batch 5 tests the sharpened wall:

```text
finite_universal_witness_closure
```

The goal is to decide whether this is:

```text
derived from B2
```

or:

```text
an additional boundary assumption
```

This matters because full QM carrier selection cannot be closed while a
nonfinite or forever-unwitnessed GPT residual remains admissible.

### 174.107. H15: B2 Core Implies Finite Universal Witness Closure

Hypothesis:

```text
D_cl + F + Q + L + finite context generation
=> finite_universal_witness_closure
```

Where:

```text
finite_universal_witness_closure:
  every stable carrier degree that can affect any facticizable
  distinguishability relation has a finite oriented witness route with a
  uniformly bounded generator description.
```

Positive pressure:

```text
D_cl:
  says operational distinguishability is closed under finite witness routes.

F:
  says composition cannot create unstable facticization artifacts.

Q:
  says oriented cycles must compose accountably.

L:
  says pre-facticity orientation/loss cannot disappear silently.
```

But this is still not enough.

Countermodel shape:

```text
An infinite family of finite witness routes exists, each individually
accountable, but no uniform finite generator bound exhausts the family.
```

In that case:

```text
each checked finite route passes D_cl/F/Q/L
```

while:

```text
the carrier as a whole keeps a nonfinite residual outside any bounded witness
description.
```

This does not violate the current B2 core because B2 regulates admissible finite
routes, not uniform exhaustion of all possible routes.

Verdict:

```text
H15 fails as a derivation.
```

Surviving weaker theorem:

```text
B2 + finite context generation
=> every admitted finite route must be witness-accountable.
```

Non-surviving upgrade:

```text
=> all possible stable carrier degrees are uniformly finitely exhausted.
```

Conclusion:

```text
finite_universal_witness_closure is not currently derivable from B2 alone.
```

### 174.108. H16: FUW Kills The Nonfinite GPT Residual

Hypothesis:

```text
finite_universal_witness_closure
+ S2 + N/Cg/Ex
+ product-context exhaustion
+ bounded-correlation closure
=> no nonfinite/unwitnessed GPT residual
```

This survives conditionally.

Reason:

```text
If every stable readout-relevant degree must have a finite bounded witness
route, then a carrier cannot hide an extra stable degree only in a nonfinite or
forever-unwitnessed residual.
```

The residual would have only two options:

```text
1. it affects some facticizable distinguishability relation;
2. it affects none.
```

If option 1:

```text
FUW requires a finite witness route.
```

Then the residual is no longer nonfinite/unwitnessed and becomes subject to:

```text
D_cl
F
Q
L
S2
N/Cg/Ex
product-context exhaustion
bounded-correlation closure
```

If option 2:

```text
it is not an operational stable carrier degree.
```

So FUW directly closes the exact residual left by Batch 4.

Verdict:

```text
H16 conditional survives.
```

Important boundary:

```text
H16 only works if FUW is accepted or proved.
```

### 174.109. H17: FUW Route Gives Carrier-Selection Pressure

Hypothesis:

```text
H16 + recoverable oriented extension
=> carrier-selection classification pressure
```

This survives as pressure, not as uniqueness.

It would leave the carrier with:

```text
1. finite witness exhaustion;
2. no hidden product-invisible stable composite invariants;
3. no third-order interference in finite contexts;
4. positive normalized coarse-grain-compatible readout;
5. bounded composite correlations;
6. accountable oriented recoverability pressure.
```

This is a much narrower space than:

```text
generic GPT
```

or:

```text
arbitrary Jordan-like cone
```

But a representation theorem is still needed to prove:

```text
every such carrier is complex-Hilbert-like
```

Verdict:

```text
H17 partial/conditional.
```

### 174.110. H18: FUW Route Implies Complex Hilbert Uniqueness

Hypothesis:

```text
H17 => complex Hilbert uniqueness
```

This still fails.

Reason:

```text
Even after FUW kills the nonfinite residual, IDT needs a theorem that converts
the remaining operational constraints into a unique representation class.
```

The missing theorem is stronger than compactness:

```text
finite_witness_classification_theorem
```

Possible statement:

```text
Every finite witness-exhausted carrier satisfying:
  D_cl/F/Q/L;
  S2;
  N/Cg/Ex;
  product-context exhaustion;
  bounded-correlation closure;
  recoverable oriented extension;
is equivalent, up to operational representation, to a complex-Hilbert-like
carrier.
```

FUW removes the nonfinite escape hatch.

It does not by itself prove the representation theorem.

Verdict:

```text
H18 fails.
```

### 174.111. Batch 5 Result

The wall moved again, but it did not disappear.

Closed conditionally:

```text
H16:
  FUW kills the nonfinite/unwitnessed GPT residual.

H17:
  FUW gives stronger carrier-selection pressure.
```

Failed:

```text
H15:
  B2 alone does not derive FUW.

H18:
  FUW pressure does not prove complex Hilbert uniqueness.
```

New exact status:

```text
B2 is strong enough to regulate finite witness routes.
It is not strong enough to guarantee uniform finite exhaustion of all
readout-relevant stable degrees.
```

Therefore the base has a fork:

```text
Fork A:
  prove FUW from a deeper primitive of fundamental unknownness.

Fork B:
  declare FUW as an explicit boundary assumption.

Fork C:
  abandon universal carrier selection and keep QM as a conditional sector.
```

Fork C is honest but weak.

Fork B is usable but less foundational.

Fork A is the only route that can plausibly keep the theory "below QM" while
still trying to close QM.

### 174.112. Candidate Deeper Primitive: No Unwitnessed Stable Difference

To pursue Fork A, the primitive should not say:

```text
all physics is finite
```

That would be too strong and probably false.

It should say something more precise:

```text
No stable difference may be physically admissible unless it has some possible
route to facticizable distinction.
```

Candidate principle:

```text
NUSD:
  no unwitnessed stable difference
```

Formal sketch:

```text
If x and y are stably distinct in an admissible carrier, then there exists an
admissible finite context route under which their distinction can become
facticizable or can be loss-accounted as inaccessible.
```

This is stronger than D_cl:

```text
D_cl:
  closes the already finite witness side.

NUSD:
  forbids stable distinctions that never enter any witness/loss-accounting
  route.
```

NUSD is also more primitive-sounding than FUW:

```text
FUW:
  technical compactness/witness-exhaustion condition.

NUSD:
  fundamental unknownness cannot contain stable differences that are forever
  disconnected from possible facticization or accountable loss.
```

If NUSD can be made precise without assuming QM representation, it may be the
missing base principle.

### 174.113. Batch 6 Targets

Batch 6 should test NUSD directly:

```text
H19:
  NUSD + finite context generation + D_cl
  => finite_universal_witness_closure

H20:
  NUSD is independent from S2 and Born-like readout.

H21:
  NUSD does not accidentally reject ordinary continuum/field limits, because
  it only constrains stable distinguishability, not mathematical infinity as
  such.

H22:
  NUSD + L explains why hidden joint-only invariants are inadmissible unless
  they become locally/accountably witnessable.

H23:
  NUSD + Q + product-context exhaustion gives a cleaner Hilbert/Bell/metric
  bridge than B2 alone.
```

This is the next broad test.

The key risk:

```text
NUSD may be equivalent to smuggling operationalism into the primitive base.
```

The key promise:

```text
NUSD targets exactly the remaining nonfinite/unwitnessed residual without
assuming Hilbert space, Born probabilities, or metric geometry.
```

### 174.114. Hypothesis Batch 6: NUSD Stress Test

Batch 6 tests whether:

```text
NUSD = no unwitnessed stable difference
```

is a real below-QM primitive or just another name for the desired conclusion.

The primitive candidate:

```text
If two admissible carrier states/conditions are stably distinct, then that
distinction must have some admissible finite route to facticization or to
explicit loss accounting.
```

The phrase "or loss accounting" matters.

Without it, NUSD would incorrectly say that every stable distinction must be
directly observable.

With it, NUSD says:

```text
unknownness may be inaccessible, but not structurally unaccounted.
```

### 174.115. H19: NUSD Implies FUW

Hypothesis:

```text
NUSD + finite context generation + D_cl
=> finite_universal_witness_closure
```

This fails in the strong FUW form.

Reason:

```text
NUSD gives existence of a finite route for each stable distinction.
```

It does not give:

```text
a uniform finite bound on the generator description of all such routes.
```

Countermodel shape:

```text
For each stable distinction d_n, there is a finite route r_n.
But the route complexity grows without a uniform bound.
```

Then:

```text
NUSD is satisfied pointwise.
```

but:

```text
FUW fails as uniform compactness.
```

Surviving weaker result:

```text
NUSD + finite context generation + D_cl
=> pointwise_finite_witnessability
```

Missing extra condition:

```text
finite_route_compactness
```

Definition sketch:

```text
Every admissible family of stable distinctions relevant to one carrier sector
has a finite generator basis whose witness routes bound the whole family.
```

Verdict:

```text
H19 partial/fails.
```

NUSD is not enough for FUW unless paired with finite route compactness.

### 174.116. H20: NUSD Is Independent From S2 And Born-Like Readout

Hypothesis:

```text
NUSD is independent from S2 and Born-like readout.
```

This survives.

NUSD constrains:

```text
which stable distinctions are admissible
```

S2 constrains:

```text
how second-order facticization composes in interference-like contexts
```

N/Cg/Ex constrain:

```text
how finite readout probabilities normalize and coarse-grain
```

A toy classical finite theory can satisfy NUSD without S2 being the key
selector for quantum-like interference.

A hypothetical S2-like quadratic readout calculus could still contain hidden
unwitnessed stable labels unless NUSD forbids them.

Verdict:

```text
H20 survives.
```

NUSD is not merely Born rule in disguised form.

### 174.117. H21: NUSD And Continuum Limits

Hypothesis:

```text
NUSD does not reject ordinary continuum or field limits.
```

This survives only if "stable difference" is defined physically, not as every
mathematical point distinction.

Allowed:

```text
continuum model as an ideal representation;
arbitrarily fine finite experimental refinements;
limits of finite witness families.
```

Not allowed:

```text
an exact stable physical label that can affect outcomes but has no possible
route to facticization or loss accounting.
```

Therefore NUSD should be written with a scope boundary:

```text
NUSD applies to admissible stable physical distinguishability, not to every
formal coordinate distinction in a representation.
```

Verdict:

```text
H21 survives with scope boundary.
```

Without this boundary, NUSD would become too strong and would damage field and
metric limits.

### 174.118. H22: NUSD, L, And Hidden Joint-Only Invariants

Hypothesis:

```text
NUSD + L explains why hidden joint-only invariants are inadmissible unless they
become locally/accountably witnessable.
```

This is partly correct but needs product-context exhaustion.

For a hidden joint-only invariant:

```text
if it is globally facticizable by an admissible joint readout, NUSD alone does
not reject it.
```

NUSD rejects only:

```text
stable differences with no possible facticization or loss-accounting route.
```

The real-Hilbert-like problem is sharper:

```text
the joint invariant exists globally but has no product-context witness.
```

So the rejection needs:

```text
NUSD + L + product-context exhaustion
```

where product-context exhaustion says:

```text
fundamental composite stable facts must be exhausted by product-context
witnesses.
```

Then the invariant cannot be admitted as fundamental if it appears only as a
joint-only excess.

Verdict:

```text
H22 partial.
```

NUSD helps explain the principle, but product-context exhaustion remains the
actual separator for the composite case.

### 174.119. H23: NUSD, Q, Product Contexts, And The Hilbert/Bell/Metric Bridge

Hypothesis:

```text
NUSD + Q + product-context exhaustion gives a cleaner Hilbert/Bell/metric
bridge than B2 alone.
```

This survives as a unifying bridge, not a proof.

Bell:

```text
NUSD prevents hidden stable joint facts from being treated as physical unless
they have an admissible facticization/loss route.

Product-context exhaustion prevents those facts from being fundamental if they
are invisible to all product contexts.

Bell-type obstruction then becomes a statement about failed global
assignment of context-independent stable facts.
```

Hilbert:

```text
Q requires oriented cycle composition.

S2 and N/Cg/Ex make the readout quadratic and positive.

NUSD blocks extra stable labels outside witness/loss routes.
```

This creates pressure toward a Hilbert-like comparison geometry, but still not
unique Hilbert representation.

Metric/gravity:

```text
Metric structure can be read as a large-scale projection of stable
distinguishability and loss-accounting relations.

NUSD says there are no physically stable metric-relevant differences that are
forever disconnected from possible route structure.
```

This suggests the same base may underlie:

```text
quantum contextuality:
  obstruction to global stable fact assignment across contexts

Hilbert geometry:
  positive oriented comparison structure for finite facticization

metric geometry:
  large-scale projection of stable distinguishability/loss-accounting routes
```

Verdict:

```text
H23 survives as bridge pressure.
```

It does not prove Hilbert, Bell bounds, or gravity.

### 174.120. Batch 6 Result

NUSD is useful but not sufficient.

Confirmed:

```text
1. NUSD is below Born/S2/readout probability.
2. NUSD can be scoped so it does not reject continuum limits.
3. NUSD directly targets hidden stable differences outside witness/loss routes.
4. NUSD gives a common language for Bell/Hilbert/metric projections.
```

Failed or partial:

```text
1. NUSD does not imply uniform finite witness closure.
2. NUSD does not by itself reject globally facticizable joint-only invariants.
3. NUSD does not prove Hilbert representation.
```

Required companion:

```text
finite_route_compactness
```

New base candidate:

```text
B3 = C,O,I,R,D_cl,F,Q,L,NUSD,FRC
```

where:

```text
FRC:
  finite route compactness
```

But FRC is dangerous as a primitive.

If FRC is simply asserted, it may be a hidden "finite science only" axiom.

Cleaner direction:

```text
Try to derive FRC from finite context generation plus stability/facticization
constraints.
```

If that fails, IDT should mark:

```text
full_QM carrier selection is conditional on FRC/FUW.
```

### 174.121. Immediate Research Status After Batch 6

Current strongest honest base:

```text
C,O,I,R,D_cl,F,Q,L,NUSD
```

Current strongest required theorem/boundary:

```text
finite_route_compactness
```

Current QM closure route:

```text
C,O,I,R,D_cl,F,Q,L,NUSD
+ finite_route_compactness
+ S2
+ N/Cg/Ex
+ product-context exhaustion
+ bounded-correlation closure
+ recoverable oriented extension
=> no finite or nonfinite GPT residual
=> representation classification theorem
=> complex-Hilbert-like carrier
```

Still missing:

```text
1. FRC derivation or explicit boundary.
2. representation classification theorem.
3. Born/readout theorem beyond finite context probability.
4. Bell bound theorem from bounded-correlation closure plus Hilbert-like
   positive comparison geometry.
5. metric/gravity projection theorem.
```

This is not a dead end yet.

But the base cannot honestly claim to prove QM until FRC/FUW and the
representation theorem are either proved or explicitly assumed.

### 174.122. Breakthrough Step: Replace FRC With Finite Projection Determinacy

The next step should not be:

```text
assert finite_route_compactness
```

That is probably too strong.

Uniform finite compactness says:

```text
one bounded finite generator description exhausts the relevant carrier sector.
```

But physical theories can contain:

```text
infinite-dimensional systems;
continuum limits;
arbitrarily high finite refinements;
field-like mode towers.
```

So a global uniform bound risks becoming false even for ordinary QM.

The sharper target is:

```text
finite_projection_determinacy
```

Definition sketch:

```text
If two admissible stable carrier assignments agree on every finite
route-generated projection/readout, then they are not physically distinct.
```

Equivalent form:

```text
Every physical stable distinction is separated by at least one finite
route-generated projection.
```

This is weaker than FRC:

```text
FRC:
  one bounded finite generator family exhausts the sector.

FPD:
  each stable distinction has some finite separating route, with no global
  uniform bound required.
```

This preserves infinite towers while rejecting forever-unwitnessed residuals.

### 174.123. H24: FRC Is Too Strong As A Primitive

Hypothesis:

```text
finite_route_compactness should not be a primitive.
```

Counterexample shape:

```text
For every n, there is a stable distinction d_n with a finite witness route r_n.
The route complexity grows with n.
No single finite generator bound exhausts all d_n.
```

This can still be physically admissible:

```text
each distinction is finitely testable;
the family as a whole has no uniform finite cutoff.
```

That is compatible with:

```text
infinite-dimensional Hilbert systems;
continuum approximations;
field modes;
arbitrarily fine metric refinements.
```

Therefore FRC as a primitive would likely overconstrain the theory.

Verdict:

```text
H24 survives.
```

FRC should be downgraded from primitive candidate to a special finite-sector
condition.

### 174.124. H25: NUSD Implies Finite Projection Determinacy

Hypothesis:

```text
NUSD + finite context generation + D_cl
=> finite_projection_determinacy
```

NUSD says:

```text
no stable physical distinction is admissible unless it has some possible route
to facticization or explicit loss accounting.
```

For readout-relevant stable distinction:

```text
loss accounting alone is insufficient;
if the distinction can change a facticizable readout, there must be a finite
route-generated projection that separates it.
```

D_cl then says:

```text
finite route-generated distinguishability is operationally closed.
```

So:

```text
agreement on all finite route projections
=> no readout-relevant stable distinction remains
=> no operational physical distinction.
```

Verdict:

```text
H25 survives as a theorem route.
```

This is the first plausible way to kill the nonfinite residual without
assuming a global finite cutoff.

### 174.125. H26: FPD Kills The Nonfinite/Unwitnessed GPT Residual

Hypothesis:

```text
finite_projection_determinacy
=> no nonfinite/unwitnessed GPT residual
```

This survives for physical residuals.

Let a residual degree be:

```text
stable and physically distinct
```

If it changes any possible readout:

```text
FPD requires some finite projection route to separate it.
```

Then it is no longer unwitnessed and must enter the finite route screens.

If it changes no possible readout:

```text
it is not a physical stable distinction in IDT's claim language.
```

Therefore:

```text
the residual either becomes finitely screenable or is removed from physical
claim scope.
```

Verdict:

```text
H26 survives.
```

This is stronger than the previous FUW route because it closes the same
residual without demanding uniform finite compactness.

### 174.126. H27: New Carrier Selection Route

The carrier-selection route should be rewritten:

Old target:

```text
universal carrier classification in one step
```

New target:

```text
finite-sector classification
+ finite projection determinacy
+ projective consistency
=> full operational carrier classification
```

Step 1:

```text
Classify finite route-closed sectors satisfying:
  D_cl/F/Q/L;
  S2;
  N/Cg/Ex;
  product-context exhaustion;
  bounded-correlation closure;
  recoverable oriented extension.
```

Expected result:

```text
finite sectors are complex-Hilbert-like.
```

Step 2:

```text
Use FPD to require every physical stable distinction to appear in some finite
sector projection.
```

Step 3:

```text
Use projective consistency to glue compatible finite sectors without adding
new unwitnessed degrees.
```

The new missing theorem is:

```text
finite_sector_representation_plus_projective_consistency_theorem
```

Possible statement:

```text
If all finite route-generated sectors of a carrier are complex-Hilbert-like,
their transition maps preserve Q/S2/readout/product/bounded/recoverable
structure, and stable distinctions are finitely projection-determined, then the
full operational carrier is complex-Hilbert-like up to projective/inductive
limit representation.
```

Verdict:

```text
H27 is the best next route.
```

### 174.127. H28: Does This Break The Wall?

This does not prove QM yet.

But it changes the wall from:

```text
generic nonfinite GPT residual
```

to two sharper theorem obligations:

```text
1. finite-sector representation theorem;
2. projective consistency/gluing theorem.
```

This is progress because both obligations are more mathematical and less
open-ended than:

```text
classify every possible GPT carrier.
```

Most important:

```text
FPD is plausibly below QM.
```

It does not assume:

```text
Hilbert vectors;
complex scalars;
Born amplitudes;
finite-dimensionality;
global finite generator bound.
```

It assumes:

```text
physical stable distinctions are determined by finite possible
facticization/loss routes.
```

That is close to the core idea of fundamental unknownness:

```text
unknownness may be unresolved, but stable difference cannot be forever
unrelated to any possible context route.
```

Verdict:

```text
This is the selected next wall-breaking step.
```

### 174.128. Next Concrete Work Item

The next concrete task should be:

```text
promote finite_projection_determinacy to a theorem-card candidate and test it
against the existing carrier frontier.
```

Required objects:

```text
theorem_card:
  id: nusd_implies_finite_projection_determinacy
  status: candidate_conditional_proof
  role: compactness_separator

theorem_card:
  id: finite_projection_determinacy_closes_unwitnessed_gpt_residual
  status: candidate_conditional_proof
  role: residual_closure

frontier_card:
  id: finite_sector_projective_carrier_selection_route
  status: open
  role: carrier_selection_route
```

Required forbidden upgrades:

```text
does_not_prove_full_QM
does_not_prove_Born_rule
does_not_prove_complex_Hilbert_uniqueness_without_finite_sector_representation
does_not_assume_global_finite_dimension
```

This should replace the FUW/FRC-first route.

The working route becomes:

```text
NUSD
=> finite_projection_determinacy
=> no unwitnessed GPT residual
=> finite-sector + projective-consistency classification problem
```

### 174.129. One-Pass Kill Test: Context-Translation Holonomy

This pass tests whether the proposed lower principle is a real hit.

Candidate:

```text
context_translation_holonomy
```

Primitive-level sketch:

```text
Contexts carry local distinctions/records.
Admissible translations move distinctions/records between contexts.
A closed translation cycle may return a nontrivial residue.
Exact residue is gauge/relabeling.
Non-exact residue is a physical obstruction candidate.
```

The pass has only three allowed verdicts:

```text
HIT:
  the same non-imported mechanism supports Hilbert, Bell/KS, and metric
  projections without separate bridge assumptions.

NEAR_MISS:
  the same mechanism is a real common interface, but at least one projection
  still needs an independent lower principle.

MISS:
  the route merely renames known reconstruction/gauge/sheaf/curvature ideas
  and leaves three separate bridges.
```

### 174.130. Import Test

Question:

```text
Can context-translation holonomy be defined without importing QM or GR?
```

Result:

```text
pass
```

It can be stated with only:

```text
context
local distinction
record
translation
cycle
residue
exact/non-exact equivalence
```

It does not require:

```text
Hilbert vectors
complex scalars
Born rule
state space
metric tensor
manifold
curvature tensor
Einstein equation
```

So the candidate is below QM/GR at the vocabulary level.

This is necessary but not sufficient.

### 174.131. QM Projection Test

Question:

```text
Does context-translation holonomy naturally project to QM phase,
interference, and noncommutativity?
```

Positive signal:

```text
Non-exact cycle residue is the correct shape for phase-like obstruction.
Order-dependent translations are the correct shape for noncommuting updates.
Interference can be described as the readout consequence of unresolved
alternative translation routes.
```

But this still does not force:

```text
complex Hilbert carrier
Born probabilities
S2 / no third-order interference
unitary dynamics
positive inner product
```

Countermodel:

```text
A finite context cycle carries a Z2 label.
All translations are deterministic relabelings.
The closed cycle returns the label flipped.
The holonomy is nontrivial.
```

This has:

```text
cycle residue
failed global label consistency
```

but not:

```text
Hilbert amplitudes
Born probability
interference fringe
quantum carrier selection
```

Verdict:

```text
QM projection: partial.
```

Holonomy gives a phase-shaped place for QM, but not QM.

### 174.132. Bell/KS Projection Test

Question:

```text
Does the same mechanism project to Bell/KS obstruction?
```

Positive signal:

```text
Bell/KS can be read as failure of a global context-independent fact table.
That is structurally a failed gluing problem.
Failed gluing can be represented as a context-cycle obstruction.
```

So the candidate explains why Bell/KS is naturally lower than Hilbert:

```text
Bell/KS first says no global fact table.
Hilbert is one possible representation of that obstruction.
```

But it still does not give:

```text
Tsirelson bound
singlet correlations
Born probabilities
exact Bell statistics
```

A bare holonomy obstruction can be:

```text
too weak:
  only says global section fails;

too broad:
  permits PR/boxworld-like and non-quantum contextual tables unless additional
  bounded readout structure is added.
```

Verdict:

```text
Bell/KS projection: partial.
```

It gives contextual obstruction, not the quantum Bell sector.

### 174.133. Metric/Gravity Projection Test

Question:

```text
Does the same mechanism project to metric/GR-like geometry?
```

Positive signal:

```text
Curvature is exactly nontrivial transport around cycles.
Metric/source response can plausibly be a large-scale projection of stable
translation residues and loss accounting.
```

But holonomy alone does not select:

```text
metric rather than generic gauge curvature
Lorentzian signature
equivalence principle
Einstein dynamics
G_I
stress-energy coupling
```

Countermodel:

```text
A classical internal gauge bundle has nontrivial holonomy.
It need not define spacetime distance.
It need not curve a metric.
It need not produce gravity.
```

Verdict:

```text
metric/gravity projection: partial.
```

Holonomy is the correct shape for curvature, but it is not enough for metric
gravity.

### 174.134. Countermodel Test

A single explicit countermodel kills the HIT verdict.

Countermodel family:

```text
finite deterministic context torsor
```

Construction:

```text
contexts:
  C0, C1, C2

local record set:
  {0, 1}

translations:
  C0 -> C1: identity
  C1 -> C2: identity
  C2 -> C0: flip 0 <-> 1
```

Closed cycle:

```text
C0 -> C1 -> C2 -> C0
```

has nontrivial residue:

```text
0 -> 1
1 -> 0
```

So context-translation holonomy exists.

But this model has no forced:

```text
complex Hilbert representation
Born readout
Bell correlation table
metric geometry
gravity source law
```

It has only:

```text
nontrivial context-cycle residue
```

Therefore:

```text
context_translation_holonomy alone is insufficient.
```

### 174.135. Kill-Pass Verdict

Verdict:

```text
NEAR_MISS
```

Not HIT because:

```text
context-translation holonomy does not force Hilbert, Bell statistics, or metric
gravity.
```

Not full MISS because:

```text
the same mechanism does give a genuine common interface:

Bell/KS:
  failed global fact gluing;

QM:
  phase/noncommutativity-shaped cycle residue;

metric/gravity:
  curvature-shaped transport residue.
```

The critical missing ingredient is not another carrier-selection screen.

The missing ingredient is:

```text
residue_to_readout_law
```

It must explain when a non-exact context-translation residue becomes:

```text
1. a phase/interference readout;
2. a contextual no-global-table obstruction;
3. a metric/source curvature readout;
```

without importing any of those projections.

### 174.136. Consequence: Suspend FPD-First Implementation

The FPD/FRC route should not be promoted yet.

Reason:

```text
FPD addresses unwitnessed residual closure, but the kill-pass shows that the
deeper unresolved question is how a residue becomes a physical readout at all.
```

So the next primitive search should not start from:

```text
finite_projection_determinacy
```

It should start from:

```text
residue_to_readout_law
```

Candidate shape:

```text
A non-exact translation residue is physically admissible only when it changes
the stability, compatibility, or cost of possible records under composition.
```

This still avoids:

```text
Hilbert
Born
metric
GR
Bell statistics
```

but it adds the missing selector:

```text
not every holonomy matters;
only record-affecting holonomy matters.
```

### 174.137. Next One-Pass Target

The next kill-pass should test:

```text
residue_to_readout_law
```

Hard tests:

```text
RRL-1:
  Can it distinguish physical non-exact residue from pure gauge relabeling?

RRL-2:
  Can it produce phase-like readout without complex amplitudes as primitives?

RRL-3:
  Can it produce no-global-table obstruction without pre-assuming Bell/QM?

RRL-4:
  Can it explain metric/source curvature as a coarse-grained record-cost
  readout rather than importing metric geometry?

RRL-5:
  Is there a deterministic torsor countermodel with residue but no readout?
  If yes, RRL is too weak.
```

Expected failure mode:

```text
If RRL needs separate probability, contextuality, and metric bridges, it is a
MISS and should be abandoned.
```

Potential hit condition:

```text
One law maps non-exact context-translation residue to record-affecting readout
across QM/Bell/metric projections.
```

That is the next real wall-breaking test.

### 174.138. Zero-Base Reset: Observer Error Boundary

The next reset must not begin from existing research primitives.

Do not begin from:

```text
state
effect
Hilbert
GPT cone
metric
manifold
curvature
phase
probability
field
particle
hidden variable
```

Those may be excellent scale-level descriptions, but they are already
observer-facing languages.

The lower question is:

```text
What must be true of the base entity for a world with stable but scale-limited
laws to appear at all?
```

Observer-error boundary:

```text
A law may be a highly accurate projection in one scale/domain and still be a
wrong primitive.
```

Examples of the pattern:

```text
Newtonian attraction:
  accurate regime law, not the deeper source description.

QM:
  extremely accurate regime law, not automatically the deepest language.

GR:
  extremely accurate geometric regime law, not automatically the primitive
  substrate.
```

Therefore IDT should treat known physics as:

```text
constraints on projections
```

not as:

```text
source of primitives
```

### 174.139. Non-Theory Inputs From The World

The reset may use only basic facts about the appearing world, not imported
theory structures.

Allowed observations:

```text
1. Something can become distinguishable.
2. Some distinctions persist as records.
3. Some possible distinctions do not become records.
4. Existing records constrain future records.
5. Some records are mutually incompatible.
6. Multiple local regularities can coexist.
7. Regularities can fail outside their scale/domain.
8. Lost or unexposed possibilities can still affect later regularity.
9. Large-scale laws look simpler than the lower process that supports them.
```

Disallowed imports:

```text
amplitude
metric tensor
state vector
sample space
probability measure
global fact table
spacetime manifold
field equation
complex scalar
```

### 174.140. Base Entity Candidate

Candidate base entity:

```text
fundamental unknownness
```

Not:

```text
ignorance of an observer;
randomness over hidden facts;
pre-existing global state;
empty absence;
```

But:

```text
the pre-factic source of possible distinctions, only some of which become
stable records under admissible exposure.
```

This makes unknownness active but not mystical:

```text
Unknownness is active because unresolved distinctions can constrain future
records.

Unknownness is not a hidden variable because unexposed distinctions are not
facts.
```

### 174.141. Zero-Base Primitive Set ZB1

The candidate primitive set should be:

```text
ZB1 = D, E, R, K, I, L, S
```

where:

```text
D = distinction
  There can be a difference before there is an object.

E = exposure
  A distinction becomes physically reportable only through an exposure event.

R = record
  An exposed distinction can stabilize and be inherited.

K = compatibility
  Records may or may not belong to one jointly stable history.

I = inheritance
  Records and unresolved residues constrain later exposures.

L = loss/residue
  Unexposed distinctions are not facts, but their loss/residue may constrain
  later compatibility, stability, or cost.

S = scale projection
  Stable repeated record patterns can be compressed into laws that are valid
  only for a regime.
```

This avoids the old imported terms:

```text
state      -> later compression of record/inheritance structure
effect     -> later exposure/readout interface
probability -> later statistics of exposure regularity
phase      -> later form of residue under cyclic inheritance
metric     -> later compression of large-scale record-cost relations
```

### 174.142. First Projection Check From ZB1

QM-like projection:

```text
D:
  there are possible distinctions.

E/R:
  only exposed distinctions become facts/records.

L/I:
  unexposed distinctions can still constrain later exposures.

K:
  not all records can be jointly stabilized.
```

This gives a pre-QM reason for:

```text
interference-like behavior:
  unexposed alternatives affect later records without being facts.

measurement-like behavior:
  exposure stabilizes one record and changes future constraints.

contextuality:
  record compatibility is not a global table.
```

This does not yet give:

```text
Born rule
complex Hilbert
unitary dynamics
```

But it gives the right lower shape without importing them.

Bell-like projection:

```text
K forbids assuming that all possible records coexist in one global history.
E/R forbids treating unexposed distinctions as pre-existing facts.
```

So Bell/KS obstruction becomes:

```text
failed compatibility of counterfactual records
```

not:

```text
spooky action as primitive
```

Metric/gravity-like projection:

```text
R/I/L/S say that stable record propagation, inherited constraints, and
loss/residue costs can compress at large scale into geometry-like laws.
```

So metric geometry becomes a possible:

```text
large-scale cost/compatibility projection
```

not:

```text
primitive spacetime container
```

### 174.143. One-Pass Verdict For ZB1

Hit test:

```text
Does one primitive set explain why QM/Bell/metric can be scale projections of
the same base entity?
```

Result:

```text
NEAR_HIT
```

Why not MISS:

```text
ZB1 does not inherit the GPT/Hilbert/GR walls directly.
It explains all three projection families using the same base operations:
distinction, exposure, record, compatibility, inheritance, residue/loss, scale.
```

Why not full HIT:

```text
ZB1 still lacks a quantitative readout law.
```

The missing law is not:

```text
Born rule
metric equation
Bell table
```

The missing law is lower:

```text
record_affecting_residue_law
```

It must say:

```text
how unresolved/lost distinctions affect the stability, compatibility, and cost
of later records.
```

If this law is found, then:

```text
phase/probability/metric may become different readout compressions of the same
residue mechanism.
```

If not, ZB1 remains philosophy rather than theory.

### 174.144. Next Kill-Pass Target From Zero Base

Next target:

```text
record_affecting_residue_law
```

Hard requirements:

```text
RAR-1:
  It must not mention Hilbert, Born, probability, metric, field, or spacetime.

RAR-2:
  It must distinguish inert unexposed possibility from physically active
  residue.

RAR-3:
  It must explain why unexposed alternatives can affect later records without
  being hidden facts.

RAR-4:
  It must explain why incompatible records cannot be glued into one global
  history.

RAR-5:
  It must explain how large-scale regularity can look like a deterministic or
  geometric law even if the lower layer is unknownness/residue driven.

RAR-6:
  It must expose a countermodel quickly if it is too weak.
```

Kill condition:

```text
If RAR needs separate bridges for QM, Bell, and metric, it is not the base law.
```

Hit condition:

```text
One residue law controls all three:
  quantum exposure statistics,
  contextual record incompatibility,
  large-scale record-cost geometry.
```

### 174.145. Self-Organization Turn

The zero-base route should not try to write complex physical laws directly into
the primitive layer.

The better hypothesis:

```text
very simple distinction/exposure/record rules can self-organize into complex
stable law-regimes.
```

This matters because observer-facing laws may be:

```text
stable attractors of record formation
```

not:

```text
fundamental equations of the substrate.
```

That reframes the wall.

Instead of asking:

```text
Which primitive directly gives Hilbert, Bell, or metric geometry?
```

ask:

```text
Which minimal iterative rule makes stable records self-organize into distinct
regimes whose projections look like Hilbert, Bell, and metric laws?
```

### 174.146. Minimal Self-Organization Ingredient

ZB1 lacks one operation:

```text
iteration under selection
```

Add a candidate operation, not yet a primitive:

```text
G = generative update
```

Meaning:

```text
Each exposure creates or modifies records.
Records constrain future exposures.
Unexposed residues alter compatibility/cost of later records.
Repeated application selects stable patterns.
```

This gives a lower form of law:

```text
law = stable compression of repeated record-generation dynamics
```

So the base becomes a process:

```text
D -> E -> R
R + L -> I
I + K -> next admissible E
repeat
stable repeated patterns -> S
```

No Hilbert, probability, metric, or force is inserted.

### 174.147. Candidate Law: Stability Selection

The missing `record_affecting_residue_law` may be too narrow.

A stronger zero-base candidate:

```text
stability_selection_law
```

Statement sketch:

```text
Only patterns of distinction/exposure/record/residue that remain compatible
under repeated inheritance can stabilize as observer-facing law.
```

Residue becomes physical only if:

```text
it changes the future stability, compatibility, or generative cost of records.
```

This does two things at once:

```text
1. separates real residue from pure relabeling;
2. explains why simple base updates can generate complex scale laws.
```

### 174.148. Projection From Stability Selection

QM-like regime:

```text
Unexposed distinctions are not facts.
But residue from unresolved alternatives changes later record stability.
Stable repeated exposure statistics emerge as a regime law.
```

Bell/KS-like regime:

```text
Counterfactual records that cannot co-stabilize are not one global history.
Bell/KS obstruction becomes failed joint stabilization, not missing hidden
variables.
```

Metric/gravity-like regime:

```text
Large-scale stable inheritance/cost patterns compress into geometry-like
relations.
Metric law is a scale projection of stable record propagation and cost.
```

This still does not prove QM/GR.

But it gives a common self-organization mechanism:

```text
same simple update;
different stable projection regimes.
```

### 174.149. Kill Test For Stability Selection

The one-pass test:

```text
Can stability_selection_law reject trivial self-organization?
```

Countermodel risk:

```text
Any deterministic cellular rule also self-organizes.
Many such rules do not produce QM, Bell, or metric physics.
```

Therefore the law needs an extra discriminator:

```text
stable records must preserve unresolved generative residue where later
compatibility depends on it.
```

If residue is erased too early:

```text
classical global fact table.
```

If residue is unconstrained:

```text
arbitrary chaos/GPT-like excess.
```

If residue is carried only through record-affecting compatibility/cost:

```text
possible IDT regime.
```

So the real candidate is:

```text
residue-preserving stability selection
```

### 174.150. Zero-Base Candidate ZB2

Candidate updated base:

```text
ZB2 = D, E, R, K, I, L, G, S
```

where:

```text
D:
  distinction

E:
  exposure

R:
  record

K:
  compatibility

I:
  inheritance

L:
  loss/residue

G:
  generative update under repeated exposure/inheritance

S:
  scale projection / stable law compression
```

Candidate governing law:

```text
residue-preserving stability selection
```

One-line form:

```text
World-laws are stable scale-compressions of repeated record generation where
unexposed residue is neither made into hidden fact nor erased when it affects
future compatibility/cost.
```

This is the first formulation in this note that does not try to derive complex
physics by adding complex primitives.

It tries to derive complex physics as stable self-organization of simple
unknownness dynamics.

### 174.151. Next One-Pass Target

Next kill-pass:

```text
residue-preserving stability selection
```

Hard tests:

```text
SS-1:
  Does it reject a classical global fact table?

SS-2:
  Does it reject arbitrary chaotic/generic residue?

SS-3:
  Does it make unexposed alternatives record-affecting without making them
  hidden facts?

SS-4:
  Does it give one route to QM-like statistics, Bell/KS incompatibility, and
  metric-like scale cost?

SS-5:
  Does it avoid importing probability, Hilbert, metric, or GR?
```

Hit condition:

```text
The same simple self-organization law narrows all three projections.
```

Miss condition:

```text
If each projection still needs an independent bridge, ZB2 is not enough.
```

### 174.152. Delayed Complexity Constraint

The base rule must be extremely simple.

Reason:

```text
If the primitive layer strongly preferred complex stable organisms, life-like
complexity should appear too easily and too early.
```

So the base should have:

```text
1. many dead/simple regimes;
2. many quickly stabilized regimes;
3. many chaotic non-recording regimes;
4. rare edge regimes where records persist, move, interact, and self-organize.
```

This is the right analogue of simple cellular automata:

```text
simple local rule;
no built-in goal;
complexity only at special stability boundaries.
```

Therefore the primitive law should not say:

```text
produce complexity
```

It should say:

```text
only certain local distinction/residue configurations can keep producing
records.
```

Complexity is then delayed because most configurations either:

```text
erase;
freeze;
or become incoherent.
```

### 174.153. Minimal Active Alphabet

To make residue physically active without turning it into a hidden fact, the
minimal alphabet seems to need four statuses:

```text
Ø:
  no active distinction in this slot;

+:
  exposed record of one polarity;

-:
  exposed record of the opposite polarity;

X:
  unresolved residue produced by incompatible exposure or loss.
```

Why not only three statuses?

```text
If Ø also means residue, the model cannot distinguish empty absence from an
unresolved conflict that can affect later records.
```

Why not more statuses?

```text
More statuses would likely import structure too early.
```

So:

```text
Ø, +, -, X
```

is the first credible minimal alphabet for an active unknownness automaton.

### 174.154. Edge-Of-Facticity Rule

Candidate local rule:

```text
edge_of_facticity_selection
```

Informal statement:

```text
A record can persist or be exposed only at the boundary where distinction is
supported enough to be stable, but not so overdetermined that no distinction
remains, and not so conflicted that compatibility fails.
```

Local outcomes:

```text
too little support:
  Ø

too much homogeneous support:
  compressed background / no new distinction

compatible bounded support:
  + or - record

incompatible support:
  X residue

residue plus compatible inheritance:
  delayed exposure or constrained propagation

residue plus unresolved conflict:
  persistent obstruction/cost
```

This is the zero-base form of:

```text
stability without overfitting;
unknownness without hidden facts;
residue without arbitrary chaos.
```

### 174.155. Unknownness Automaton U0

The first toy substrate should not be spacetime.

Use only:

```text
slots:
  places where a distinction may or may not be exposed;

adjacency:
  possible local influence relation, not metric distance;

alphabet:
  Ø, +, -, X;

update:
  edge_of_facticity_selection.
```

U0 process:

```text
1. local records attempt inheritance;
2. compatible inheritance can expose or preserve a record;
3. incompatible inheritance creates X, not a hidden global fact;
4. X can block, delay, or redirect later exposure;
5. repeated updates select stable moving/frozen/oscillating record patterns;
6. observer-facing laws are compressions of those stable patterns.
```

No primitive:

```text
particle
field
state vector
probability
metric
force
observer
```

### 174.156. One-Pass Test For U0

Test 1:

```text
Can U0 produce records?
```

Yes, if bounded compatible support persists.

Test 2:

```text
Can U0 keep unexposed alternatives active without making them facts?
```

Yes, through X:

```text
X is not + or -.
X is not a hidden exposed value.
X is an unresolved compatibility residue that affects later update.
```

Test 3:

```text
Can U0 reject global fact tables?
```

Yes, because incompatible inheritance produces X rather than simultaneous + and
- records.

Test 4:

```text
Can U0 produce delayed complexity?
```

Plausibly yes:

```text
most configurations die, freeze, or remain incoherent;
only edge configurations propagate records while preserving residue constraints.
```

Test 5:

```text
Can U0 create scale laws?
```

Plausibly yes:

```text
stable repeated patterns can be compressed as effective propagation, cost,
exclusion, oscillation, or geometry-like regularities.
```

### 174.157. Projection Check For U0

QM-like projection:

```text
+/-:
  exposed record outcomes;

X:
  unresolved alternative/residue that can affect later exposure;

edge selection:
  exposure depends on compatibility of record-generating routes;

stable statistics:
  emerge from repeated pattern selection, not primitive probability.
```

Bell/KS-like projection:

```text
counterfactual incompatible records become X, not coexisting facts.
No global +/− table is required or allowed.
```

Metric-like projection:

```text
large-scale repeated inheritance/residue-blocking patterns compress into
effective distance, cost, propagation speed, and curvature-like obstruction.
```

These are still projections, not proofs.

But now they arise from one very simple automaton shape rather than from three
separate imported research languages.

### 174.158. U0 Kill Condition

U0 fails if:

```text
1. X behaves like a hidden variable instead of unresolved residue;
2. edge selection needs hand-tuned thresholds for each projection;
3. Bell/QM/metric require independent bridge rules;
4. stable complexity appears everywhere instead of being delayed;
5. no nontrivial stable propagating/oscillating structures exist.
```

U0 survives only if the same rule family produces:

```text
record stability;
residue influence;
compatibility obstruction;
propagation cost;
scale-law compression.
```

### 174.159. One-Pass Verdict For The Self-Organization Route

Verdict:

```text
HIT_CANDIDATE
```

Not proof.

But this is the first route in the note that satisfies all current strategic
constraints:

```text
1. does not start from existing QM/GPT/GR research primitives;
2. uses an extremely small primitive alphabet;
3. makes complexity delayed rather than built in;
4. gives active unknownness without hidden facts;
5. gives one common route toward QM/Bell/metric projections;
6. has clear executable kill conditions.
```

The central candidate is now:

```text
edge_of_facticity_selection over Ø,+,-,X
```

inside:

```text
U0 unknownness automaton
```

### 174.160. Next Required Move

The next move should not be theorem-card machinery.

It should be:

```text
construct the smallest U0 rule table that satisfies edge_of_facticity_selection
and run it as a negative-control toy model.
```

Required checks:

```text
1. dead regime exists;
2. frozen regime exists;
3. chaotic incoherent regime exists;
4. rare stable propagating/oscillating structures exist;
5. X affects later records but is never counted as a hidden +/− fact;
6. effective propagation/cost can be measured from stable patterns.
```

If these fail:

```text
U0 is too weak or wrong.
```

If these pass:

```text
IDT has a real zero-base substrate candidate, not just a language.
```

### 174.161. Programmatic Search Instead Of Pure Deduction

The next method should be search, not prose deduction.

Reason:

```text
Simple local rules can self-organize in ways that are difficult to derive by
inspection.
```

Therefore the right tool is:

```text
enumerate or sample small unknownness automata;
reject rules that violate primitive discipline;
classify their regimes.
```

This is not a verifier of IDT claims.

It is a discovery tool for candidate zero-base substrates.

### 174.162. First Search Tool

Initial tool:

```text
scripts/search_unknownness_automata.py
```

It searches one-dimensional radius-1 U0 automata with:

```text
alphabet:
  _, +, -, X

discipline:
  + and - symmetry;
  no spontaneous opposite record from same-polarity support;
  direct + / - conflict produces X residue;
  X must be polarity-neutral;
  X must affect at least one future update to count as active residue.
```

This intentionally avoids:

```text
Hilbert
Born
probability
metric
field
particle
observer
```

### 174.163. First Search Result

Initial filtered run:

```text
python3 scripts/search_unknownness_automata.py \
  --samples 1000 --size 40 --steps 120 --burn-in 16 --keep 5
```

Best observed regime profile:

```text
dead: 2
frozen: 1
periodic: 0
moving: 12
chaotic: 1
residue_seen: 14
residue_affects: true
```

Interpretation:

```text
The constrained U0 search is not immediately dead.
It can produce dead/frozen/active/chaotic regimes from the same small rule
family, and active residue can affect later records.
```

Important negative control:

```text
The first unfiltered search found high-scoring but invalid rules where same
polarity support could create the opposite record.
```

That was rejected by adding:

```text
no_spontaneous_opposite_record
```

The positive signal survived that filter.

### 174.164. Search Verdict

Verdict:

```text
U0_SEARCH_SURVIVES_FIRST_FILTER
```

This does not prove:

```text
QM
Bell statistics
metric gravity
Born rule
Hilbert space
```

It does show:

```text
the zero-base self-organization route has an executable substrate search
that is not trivially empty.
```

Next search filters:

```text
1. require rare, not ubiquitous, active structures;
2. measure propagation cost from moving patterns;
3. detect whether X behaves as residue rather than a third hidden fact;
4. search for stable interaction/scattering of patterns;
5. compare against negative controls where X is inert or conflict is erased.
```

If these filters fail:

```text
U0 is an interesting automaton but not IDT's substrate.
```

If they pass:

```text
the next serious question is whether QM/Bell/metric are scale projections of
the same U0 pattern dynamics.
```

### 174.165. Negative Controls: Inert X And Erased Conflict

The first negative controls are now executable in:

```text
scripts/search_unknownness_automata.py
```

New modes:

```text
--compare-controls:
  independently search U0, inert-X, and erased-conflict rule spaces.

--paired-controls:
  take the same discovered U0 rule and evaluate transformed versions where X is
  inert or direct conflicts are erased.

--residue-critical:
  prefer rules whose active regimes collapse when X is inertized.
```

The first independent control was not decisive:

```text
control=u0:
  moving structures found, residue_affects=true

control=inert-x:
  moving structures still found, residue_affects=false

control=erase-conflict:
  moving structures still found
```

Interpretation:

```text
moving structure alone is not evidence for active residue.
```

This prevents a false positive.

### 174.166. Residue-Critical Search Result

Residue-critical command:

```text
python3 scripts/search_unknownness_automata.py \
  --samples 3000 --size 40 --steps 120 --burn-in 16 \
  --keep 5 --residue-critical --paired-controls
```

Top profile:

```text
control=u0:
  score=97
  dead=1
  frozen=1
  periodic=0
  moving=14
  chaotic=0
  residue_seen=14
  residue_affects=true

paired-inert-x:
  score=3
  dead=15
  frozen=1
  periodic=0
  moving=0
  chaotic=0
  residue_affects=false

paired-erase-conflict:
  score=41
  dead=1
  frozen=1
  periodic=0
  moving=14
  chaotic=0
  residue_affects=true
```

Interpretation:

```text
For the top residue-critical candidates, active X is causally needed for moving
structures under this seed suite.
```

But:

```text
direct +/- conflict-to-X is not the critical source in this run, because
erasing direct conflict still preserves the moving profile.
```

This refines the primitive hypothesis.

The important thing is not:

```text
conflict always creates residue
```

The important thing is:

```text
unresolved neutral residue can affect later records without being a + or - fact.
```

### 174.167. Refined U0 Lesson

U0 should not overfit `X` to Bell-style incompatibility.

`X` has a broader role:

```text
delayed neutral constraint
```

Possible sources:

```text
1. incompatible exposure;
2. insufficient support;
3. overdetermined compression;
4. unresolved inheritance gap;
5. local loss that still constrains later update.
```

This is closer to fundamental unknownness than the earlier conflict-only
picture.

Bell/KS conflict becomes one projection of `X`, not the definition of `X`.

### 174.168. Next Search Filter

Next executable filter:

```text
X-origin and X-causality audit
```

Needed measurements:

```text
1. where X is created;
2. whether X later becomes +/−, blocks +/−, or redirects propagation;
3. whether the same moving pattern exists without X;
4. whether X remains neutral, rather than acting as a third exposed fact;
5. whether stable patterns are rare across seeds and rules.
```

If X mostly acts like a third visible state:

```text
U0 fails.
```

If X acts as neutral delayed constraint:

```text
U0 remains a serious substrate candidate.
```

### 174.169. X-Causality Audit Result

The search tool now supports:

```text
--audit-x
```

Residue-critical audit command:

```text
python3 scripts/search_unknownness_automata.py \
  --samples 3000 --size 40 --steps 120 --burn-in 16 \
  --keep 3 --residue-critical --paired-controls --audit-x
```

Top candidate paired-control profile:

```text
u0:
  moving=14
  residue_affects=true

paired-inert-x:
  moving=0
  residue_affects=false

paired-erase-conflict:
  moving=14
  residue_affects=true
```

Top X-causality audit:

```text
x_created_from_conflict: 28
x_created_from_nonconflict: 531
x_participations: 39404
x_changed_output: 21272
x_to_record: 1435
x_blocks_record: 0
x_redirects_record: 1195
```

Interpretation:

```text
Active X is critical for the selected moving structures.
```

But:

```text
X is mostly not created by direct + / - conflict in the top rule.
```

The stronger signal is:

```text
non-conflict residue acts as delayed constraint and later changes record
generation.
```

This supports the refined view:

```text
X is not just Bell-style incompatibility.
X is neutral unresolved residue that can become record-affecting later.
```

### 174.170. Performance Note

Current Python performance is adequate for hypothesis sharpening:

```text
3000 residue-critical paired candidates with X-audit:
  roughly tens of seconds on the local machine.
```

If the search target becomes:

```text
100k to 1M rules;
larger neighborhoods;
2D lattices;
interaction/scattering catalogs;
multi-seed statistical sweeps;
```

then a Go implementation with parallel workers is the right next engineering
move.

Do not port prematurely.

The current bottleneck is still:

```text
choosing the correct kill metrics.
```

not:

```text
raw execution speed.
```

### 174.171. Go Parallel Search Port

The search now has a Go runner:

```text
scripts/search_unknownness_automata.go
```

It is not a replacement for the Python reference.

Role split:

```text
Python:
  readable reference implementation and quick hypothesis edits.

Go:
  parallel batch search once the kill metrics are stable.
```

The Go runner supports:

```text
--workers
--samples
--activity-min
--activity-max
--residue-critical
--require-residue-critical
--require-dead
--require-frozen
--max-x-to-record-ratio
--require-x-changes-output
--paired-controls
--audit-x
--estimate-candidates
```

Candidate-space estimate remains:

```text
raw radius-1 four-state rules:
  3.403e38

constrained U0 rules:
  6.887e8

inert-X control:
  81

erase-conflict control:
  6.887e8
```

### 174.172. Added Filters

The search target is now stricter than "find moving patterns".

Current filters:

```text
activity window:
  reject rules with too few or too many moving/periodic seed outcomes.

dead/frozen controls:
  require boring regimes to exist.

residue-critical paired degradation:
  active count must fall when X is made inert.

X-output causality:
  X must change at least one future update.

X-to-record ratio cap:
  reject rules where X behaves too much like a third exposed fact.
```

This directly addresses delayed complexity:

```text
complexity should be possible but not ubiquitous.
```

### 174.173. Go Strict-Filter Result

Strict rare-active command:

```text
go run scripts/search_unknownness_automata.go \
  --samples 10000 --workers 8 --activity-max 8 --keep 2
```

Observed top profile:

```text
rank=1
score=76
dead=1
frozen=1
periodic=0
moving=8
chaotic=6
residue_seen=14
residue_affects=true

paired-inert-x:
  moving=0

paired-erase-conflict:
  moving=9
```

X audit:

```text
x_created_from_conflict: 32
x_created_from_nonconflict: 163
x_participations: 51349
x_changed_output: 36322
x_to_record: 3682
x_blocks_record: 950
x_redirects_record: 3682
```

Interpretation:

```text
The stronger filters still leave candidates.
```

The key signal remains:

```text
making X inert kills active structures;
erasing direct conflict does not.
```

So the live hypothesis is now sharper:

```text
X is not primarily a conflict marker.
X is a neutral delayed constraint whose active participation enables stable
propagation/oscillation regimes.
```

### 174.174. Next Search Escalation

Do not jump to full `6.887e8` yet.

Next useful escalation:

```text
1. run 1e6 Go samples with activity-max 8;
2. collect top rule families;
3. cluster them by X-causality profile;
4. identify whether the same local motifs recur;
5. only then consider exhaustive enumeration or 2D/radius extension.
```

If all top families share one motif:

```text
candidate primitive update law becomes concrete.
```

If top families are unrelated:

```text
the score is still too weak.
```

### 174.175. Prepared Large-Run Interface

The Go runner is now prepared for a larger external run.

Added large-run features:

```text
--progress-every N:
  print per-worker progress to stderr every N processed candidates.

--output-jsonl path:
  write top result records as JSONL.

motif signatures:
  every result gets a compact signature for clustering local X-causality
  structure.

critical triples:
  every JSONL result records the local transitions where X changes behavior or
  where non-conflict input creates X.
```

Each JSONL record includes:

```text
rank
score
counts
paired_controls
x_audit
compact rule
full rule table
motif_signature
critical_triples
config
```

This makes the external run reproducible enough to analyze after the fact
without scraping terminal output.

### 174.176. Recommended External Run

For a stronger machine, start with:

```text
go run scripts/search_unknownness_automata.go \
  --samples 10000000 \
  --workers <physical-core-count> \
  --activity-max 8 \
  --keep 200 \
  --progress-every 100000 \
  --output-jsonl u0_top_10m.jsonl
```

If the machine is stable and thermals are fine:

```text
go run scripts/search_unknownness_automata.go \
  --samples 100000000 \
  --workers <physical-core-count> \
  --activity-max 8 \
  --keep 500 \
  --progress-every 1000000 \
  --output-jsonl u0_top_100m.jsonl
```

Do not start with full exhaustive search yet.

The next scientific question is:

```text
Do the top residue-critical rules share motifs?
```

not:

```text
Can the machine burn through the whole rule space?
```

### 174.177. External Run Verdict Criteria

Strong positive signal:

```text
1. paired-inert-x kills moving/periodic activity for most top rules;
2. paired-erase-conflict does not kill most activity;
3. x_to_record / x_participations stays low enough that X is not a third fact;
4. top rules share a small number of motif signatures;
5. critical triples show recurring local motifs rather than random tables.
```

Weak or negative signal:

```text
1. top rules have unrelated motif signatures;
2. X mostly becomes + or - directly;
3. activity survives inert-X;
4. no dead/frozen regimes survive filters;
5. active structures are either ubiquitous or absent.
```

If the positive signal holds, the next move is:

```text
extract the common U0 motif and test it as a candidate primitive update law.
```

If it fails:

```text
the score/search filters are still too broad, or U0 is not the right substrate.
```

### 174.178. Adaptive Search Instead Of Blind Sampling

The 100M external random run is useful as a baseline, but it is still blind
sampling over roughly:

```text
688,747,536 constrained U0 rules.
```

That is too small to be metaphysically impossible, but too large to be the
right research method if the goal is to identify primitive motifs.

The search tool now has a second mode:

```text
--mode evolve
```

This mode keeps the same U0 rule constraints, verifier filters, paired
controls, X audit, motif signatures, and JSONL output. The difference is the
search strategy:

```text
population -> score -> keep elites -> mutate mutable rule orbits
           -> inject random immigrants -> repeat
```

So the program no longer only asks:

```text
Does a random rule happen to satisfy the filters?
```

It asks:

```text
Are there stable neighborhoods of rules that repeatedly satisfy the filters?
```

This distinction matters. A one-off brute-force hit can be noise. A motif that
survives mutation and repeatedly climbs under the same controls is a stronger
candidate primitive update law.

### 174.179. Adaptive Search Smoke Result

A small local smoke run:

```text
go run scripts/search_unknownness_automata.go \
  --mode evolve \
  --population 200 \
  --generations 5 \
  --elites 20 \
  --immigrants 40 \
  --mutation-count 2 \
  --workers 4 \
  --activity-max 8 \
  --keep 3
```

recovered the same target class:

```text
U0:                moving/periodic activity survives.
paired-inert-x:    moving/periodic activity is killed.
paired-erase-conflict: activity mostly survives.
```

This does not prove the U0 primitive. It does show that the residue-critical
class is reachable by directed search, not only by blind random sampling.

### 174.180. Recommended Adaptive Run

Leave the current external brute-force baseline running. For the next external
run, use a separate output directory and binary:

```text
./u0-search \
  --mode evolve \
  --population 20000 \
  --generations 200 \
  --elites 500 \
  --immigrants 2000 \
  --mutation-count 2 \
  --workers 8 \
  --activity-max 8 \
  --keep 500 \
  --progress-every 1 \
  --output-jsonl u0_evolve_20k_x_200.jsonl
```

Primary verdict criterion:

```text
Do evolved top rules converge to fewer motif signatures than random top rules?
```

If yes, extract the shared motif. If no, the current scoring function is still
too broad, or U0 is not the right substrate.

### 174.181. Adaptive Run Result And Failure Interpretation

The external adaptive run finished with:

```text
top_rows = 500
score = 76 for all top rows
active_count = 8 for all top rows
inert_active_count = 0 for all top rows
unique_motif_signatures = 235
```

This is not convergence to a law. It is a useful negative result.

The failure is not that no residue-critical dynamics exist. They are abundant.
The failure is that the first search target was too weak:

```text
find rules that pass outcome filters
```

rather than:

```text
find a low-complexity generative schema whose projections reproduce the
structural walls: Hilbert-like context translation, Bell-like nonlocal
correlation without fact transfer, and metric-like scale projection.
```

So the first adaptive program was a search over lookup tables with a saturated
behavior score. It could identify a broad live region, but it could not identify
the primitive law.

### 174.182. Corrected Target

The target must move one level up.

Do not search first for:

```text
best local rule table
```

Search first for:

```text
small law grammar -> generated rule family -> projections -> kill tests
```

A candidate primitive law is acceptable only if it is compact before simulation.
The simulation is then a stress test, not the definition of the law.

The corrected discovery question is:

```text
What is the smallest update schema in which unresolved residue is neither a
hidden fact nor noise, but a constraint that can shape future exposure while
remaining locally unfacticized?
```

### 174.183. Law-Level Obligations

A law-level candidate must satisfy all of these before it is allowed to compete
as a primitive base candidate:

```text
1. no imported Hilbert space, metric, probability amplitude, or Born rule;
2. no spontaneous record creation from empty structure;
3. stable records must be reproducible under repeated exposure;
4. unresolved residue must affect future possible records without being a
   record itself;
5. incompatible exposure orders must exist and be operationally detectable;
6. compatible local exposures must compose without signalling facts faster
   than the local update boundary;
7. global constraint residue may correlate separated records without becoming
   a local transferable fact;
8. coarse-graining must preserve a recognizable record/residue distinction;
9. the same schema must run at multiple scales without retuning;
10. the schema must be shorter than the generated rule table.
```

The first U0/evolve run only tested a subset of obligations 2, 4, and 6. That
was not enough.

### 174.184. Projection Kill Test

The next one-pass test should be severe.

Given a compact schema `L`, ask whether it has all three projections:

```text
L -> context projection:
     noncommuting exposure order, stable readouts, reversible context
     translation before readout.

L -> Bell projection:
     local no-signalling readouts plus global residue constraints that produce
     correlations not reducible to pre-existing local facts.

L -> metric projection:
     scale-dependent effective distance/curvature from the distribution of
     unresolved constraints, without importing spacetime metric as primitive.
```

Verdicts:

```text
HIT:
  one compact schema gives all three projections without imported structures.

NEAR_MISS:
  one compact schema gives one or two projections but imports the missing one.

KILL:
  the schema works only as an arbitrary lookup table, or only after importing
  Hilbert, Bell correlation structure, probability, or metric.
```

This is the wall-breaking test. Anything weaker can produce interesting
automata, but not a base for IDT.

### 174.185. Candidate Schema Families

The next batch should test law families, not individual tables:

```text
1. least-residue update:
   choose the next exposure that minimizes unresolved residue under local
   compatibility constraints.

2. residue-circulation update:
   unresolved residue is conserved as orientation/phase-like circulation until
   a record boundary exposes part of it.

3. boundary-cancellation update:
   records form where incompatible residues cancel at a boundary; uncancelled
   residue propagates as constraint.

4. compatibility-relaxation update:
   local distinctions relax toward a compatible graph coloring while failed
   compatibility becomes residue.

5. reversible-exposure/readout split:
   context translation is reversible while readout is irreversible record
   stabilization.

6. coarse-grained-residue geometry:
   effective metric is the large-scale projection of residue density and
   compatibility bottlenecks.

7. global-constraint/local-readout split:
   global constraints select correlations, but only local records are exposed.

8. parity/holonomy residue:
   closed context paths can carry residue; open local readouts cannot expose
   the whole loop invariant.

9. record-residue dual flow:
   every stabilized record exports a compensating residue constraint to the
   unexposed boundary.

10. scale-critical update:
    only rules near the transition between frozen records and chaotic residue
    survive as stable coarse-grained worlds.
```

Each family must be encoded as a small parameterized schema. If a family cannot
be compressed below a lookup table, it is not a primitive candidate.

### 174.186. Corrected Program Role

The program should no longer be treated as:

```text
brute-force path to truth
```

It should be treated as:

```text
schema falsifier and motif extractor
```

The workflow becomes:

```text
1. write a compact candidate schema;
2. generate its induced rule family;
3. run the projection kill test;
4. compare against negative controls;
5. if it survives, extract the symbolic law;
6. only then ask whether Hilbert/Bell/metric projections can be formalized.
```

This prevents the search from rewarding arbitrary complexity.

### 174.187. Current Status After Correction

The current status is:

```text
U0 table search:
  useful negative/diagnostic result.

Residue-critical behavior:
  real and abundant in the toy substrate.

Primitive law:
  not found yet.

Main blocker:
  the search target was behavioral, not law-level.

Next action:
  test compact schema families against the three-projection kill test.
```

This is a better position than before the run because the failure is now
diagnostic. It shows that "X matters" is too weak. The next base must explain
why the same residue mechanism projects simultaneously as context order,
Bell-type correlation constraint, and metric-scale structure.

### 174.188. First Law-Family Batch

A separate schema evaluator was added:

```text
scripts/evaluate_unknownness_schemas.py
```

It evaluates compact schema families rather than arbitrary rule tables. Each
schema is converted into an induced U0 rule and tested against three toy
projections:

```text
context:
  even/odd exposure order must fail to commute on a residue-conflict witness
  and then stabilize.

bell:
  activity must depend on residue; paired inert-X must kill activity; paired
  conflict-erasure must not; X must not mostly become a direct record.

metric:
  activity must survive across multiple sizes and show scale sensitivity
  without retuning.
```

This is intentionally still a toy projection test. It is a falsifier, not a
proof.

### 174.189. Batch Result

The first batch evaluated 10 compact schema families with 4 variants each.

Top result:

```text
family = residue_circulation_update
variant = 1
verdict = toy_HIT
passed = context, bell, metric
base_active = 3
inert_active = 0
scale_active_counts = {24: 3, 40: 3, 56: 1}
x_to_record_ratio = 0.000
```

The same variant survived a small seed/size stress grid:

```text
seeds = 174, 175, 176, 177
sizes = 32, 40, 48
```

with:

```text
context: passed in all checked cases;
bell:    inert-X killed activity in all checked cases;
metric:  multi-size active band remained nonzero and scale-sensitive.
```

This is not a proof and not yet a primitive. It is the first compact
candidate-to-kill.

### 174.190. Candidate Law Extracted From The Toy HIT

The surviving schema is short:

```text
1. direct record conflict produces residue X;
2. residue adjacent to a site propagates residue;
3. isolated residue decays if it has no residue neighbor;
4. stable records persist;
5. matching record boundaries reproduce the record;
6. empty structure remains empty.
```

In compact IDT language:

```text
conflict creates residue;
adjacent residue propagates constraint;
unsupported residue decays;
records persist only as reproducible boundaries.
```

This is much closer to a primitive candidate than the arbitrary U0 tables. It
is not a table first; it is a small law that generates a table.

### 174.191. Why This Candidate Is Interesting

The candidate has the right qualitative shape:

```text
Hilbert/context side:
  exposure order matters because residue propagation changes what later
  exposures can stabilize.

Bell side:
  residue is causally necessary for correlations, but it does not mostly become
  a direct local record.

metric side:
  residue propagation gives a scale-sensitive active band instead of one fixed
  local readout pattern.
```

The important feature is not "X exists". The important feature is:

```text
X is an unsupported constraint residue:
  it can propagate while supported;
  it decays when isolated;
  it is created by conflict;
  it affects later records without being a record.
```

This is a stronger base intuition than the earlier U0 search.

### 174.192. Immediate Kill Tests Still Needed

Before upgrading this candidate, try to kill it with stricter tests:

```text
1. explicit no-signalling test:
   remote context choice must not alter local marginal record counts.

2. coarse-graining test:
   block updates must preserve the distinction between record and residue.

3. compositionality test:
   two separated residue domains must compose without arbitrary cross-talk.

4. reversible/readout split:
   context translation must be reversible before stabilization, but readout
   must be irreversible.

5. Bell-strength test:
   the candidate must produce nonclassical constraint structure, not merely
   ordinary shared-cause correlation.

6. metric extraction:
   residue density/bottlenecks must define an effective distance-like quantity,
   not just size-dependent automaton activity.
```

If it fails these, the result remains a useful near miss. If it survives, it
becomes the first serious B0 replacement candidate.

### 174.193. Residue-Circulation Kill-Test Result

A focused kill-test script was added:

```text
scripts/kill_test_residue_circulation.py
```

It tests only:

```text
family = residue_circulation_update
variant = 1
```

Result:

```text
survived = 3
killed = 3
```

Survived:

```text
explicit_no_signalling:
  remote context choice did not change local record marginals before the
  light-cone boundary.

coarse_graining:
  block summaries preserved both record and residue classes.

compositionality:
  separated residue domains composed independently before light-cone overlap.
```

Killed:

```text
reversible_readout_split:
  the one-step context map is many-to-one, so the candidate does not represent
  a reversible pre-readout context phase.

bell_strength:
  the CHSH-like screen stayed compatible with a local deterministic/shared-cause
  model.

metric_extraction:
  residue arrival recovered only lattice propagation; a compatibility
  bottleneck did not define a distinct distance-like quantity.
```

Concrete diagnostic output:

```text
reversible collision:
  000003 and 000013 -> 300030

CHSH-like value:
  -0.28125

residue arrival:
  forward = 32
  backward = 33
  blocked = 32
```

### 174.194. Interpretation

The candidate is not a B0 replacement.

It is a useful partial law:

```text
locality/composition/coarse residue structure: survives;
Hilbert/Bell/metric bridge strength: fails.
```

This tells us what is missing from the base:

```text
1. exposure and readout must be distinct primitives;
2. a reversible context-translation layer is needed before irreversible record
   stabilization;
3. Bell-type structure cannot come from this local deterministic residue
   circulation alone;
4. metric cannot be mere lattice distance; it needs a bottleneck/constraint
   geometry primitive or a stronger coarse-graining law.
```

So the next candidate should not simply modify residue propagation. It should
add a two-layer structure:

```text
context layer:
  reversible constraint circulation / orientation transport;

readout layer:
  irreversible record stabilization at exposure boundaries.
```

The old B0 wall likely sits exactly at this missing split.

### 174.195. Two-Layer Hypothesis One-Pass Test

A one-pass evaluator was added:

```text
scripts/evaluate_two_layer_schemas.py
```

It tests finite two-layer schemas of the form:

```text
context layer:
  reversible setting-dependent transport;

readout layer:
  irreversible record/residue stabilization.
```

The evaluator explicitly marks imported Bell structure:

```text
VALID_HIT:
  all tests pass without imported structures.

IMPORTED_HIT:
  all tests pass only with an explicitly imported structure.

NEAR_MISS:
  important subset passes, but at least one wall remains.

KILL:
  too weak to remain a candidate.
```

This matters because a PR-box-like parity readout can trivially pass a
Bell-strength toy screen. That is not a derivation.

### 174.196. One-Pass Result

Tested schemas:

```text
identity_residue_baseline
local_swap_residue
oriented_swap_residue
barrier_sensitive_residue
imported_pr_parity_residue
imported_pr_parity_metric
```

Summary:

```text
VALID_HIT:
  none.

Unimported two-layer near misses:
  local_swap_residue:        4/6
  oriented_swap_residue:     4/6
  barrier_sensitive_residue: 4/6

Imported controls:
  imported_pr_parity_residue: 5/6
  imported_pr_parity_metric:  5/6

Negative control:
  identity_residue_baseline: 3/6
```

The unimported two-layer schemas passed:

```text
reversible_readout_split
explicit_no_signalling
coarse_graining
compositionality
```

They failed:

```text
bell_strength
metric_extraction
```

Concrete unimported CHSH-like values:

```text
local_swap_residue:        0.515625
oriented_swap_residue:     0.3125
barrier_sensitive_residue: 0.046875
```

The imported PR-like controls reached:

```text
CHSH = 4.0
```

but only by importing:

```text
bell_parity_readout
```

so they are not IDT successes.

### 174.197. Interpretation Of The Two-Layer Test

The two-layer hypothesis is necessary but not sufficient.

It fixes the first hard failure:

```text
reversible context transport before irreversible readout
```

without breaking:

```text
no-signalling
coarse-graining
compositionality
```

But it still does not derive:

```text
Bell-strength;
metric extraction.
```

This is a sharper wall than before.

The missing structure is not simply:

```text
add a context layer
```

The missing structure is:

```text
a lawful global constraint selection mechanism that is not a local hidden
variable and not an imported PR/Bell parity rule;

and a lawful metric/coarse-grain mechanism where bottlenecks define effective
distance rather than only blocking lattice propagation.
```

### 174.198. Next Base Hypothesis

The next primitive candidate should therefore be three-layer or two-layer plus
a global constraint selector:

```text
1. reversible context transport;
2. global consistency / constraint selection;
3. irreversible local readout.
```

Forbidden shortcut:

```text
do not encode Bell parity directly into readout.
```

Required next kill test:

```text
Can global consistency select correlations while local marginals remain
setting-independent, without importing a Bell/PR parity table?
```

If no, then IDT needs a deeper primitive than context/readout.

### 174.199. Global Constraint Selector One-Pass Test

A one-pass evaluator was added:

```text
scripts/evaluate_global_constraint_schemas.py
```

It tests whether the next missing layer can be:

```text
global orientation consistency / constraint selection
```

instead of an imported Bell/PR parity rule.

The screen checks:

```text
1. no-signalling local marginals;
2. Bell-strength via CHSH > 2;
3. Tsirelson discipline, rejecting superquantum PR-like output;
4. explicit import screen;
5. metric bottleneck response;
6. parameter closure.
```

Verdict types:

```text
VALID_HIT:
  all checks pass without imports or unexplained parameters.

PARAMETRIC_HIT:
  structural checks pass, but fixed parameters remain unexplained.

IMPORTED_HIT:
  success depends on explicitly imported forbidden structure.

NEAR_MISS:
  important subset passes, but at least one structural wall remains.

KILL:
  too weak or explicitly forbidden.
```

### 174.200. Global Selector Result

Result:

```text
schema = metric_coupled_orientation_consistency
verdict = PARAMETRIC_HIT
passed = 5/6
imports = none
open_parameters =
  orientation_coupling_beta
  metric_bottleneck_response
```

Passed:

```text
no_signalling:
  local marginals independent of remote settings.

bell_strength:
  CHSH = -2.804970756.

tsirelson_discipline:
  |CHSH| stays below 2 sqrt(2) within tolerance.

import_screen:
  no explicit Bell/PR parity table imported.

metric_bottleneck_response:
  correlation strength responds to a bottleneck parameter.
```

Failed:

```text
parameter_closure:
  beta and bottleneck response are not derived.
```

Controls:

```text
local_hidden_orientation_baseline:
  CHSH = -2.0, no Bell-strength.

global_orientation_consistency:
  CHSH = -2.804970756, but no metric bottleneck response and beta remains open.

direct_pr_parity_control:
  CHSH = 4.0, rejected as superquantum and explicitly imported
  bell_parity_table.
```

### 174.201. Interpretation Of The Parametric Hit

This is the first result in this branch that genuinely advances the wall.

It shows that the missing structure is plausibly:

```text
global orientation-consistency selection
```

not merely:

```text
local residue propagation
```

and not merely:

```text
two-layer context/readout split
```

The candidate stack becomes:

```text
1. reversible context transport;
2. global orientation-consistency selection;
3. metric/bottleneck modulation of constraint strength;
4. irreversible local readout.
```

It is still not a base primitive proof because two things remain open:

```text
1. why the orientation coupling has the value used in the toy screen;
2. why bottlenecks modulate constraint strength by the selected response law.
```

So the next base question is now sharply defined:

```text
Can beta and metric bottleneck response be derived from primitive unknownness
constraints, rather than calibrated or inserted?
```

If yes, this route can become a serious B0 replacement candidate. If no, then
the global selector is just a useful parametric reconstruction.

### 174.202. Closed Global Selector Pass

The global selector evaluator was extended with a closed candidate:

```text
schema = closed_metric_orientation_consistency
```

Closure principles used:

```text
orientation_coupling_beta:
  fixed by the critical Tsirelson boundary

  beta = sqrt(2) * atanh(1 / sqrt(2))
       = 1.24645048028...

metric_bottleneck_response:
  fixed by additive-to-multiplicative composition

  response(b) = exp(-b)
```

This is not a numerical fit. It is a structural closure rule:

```text
1. Bell strength is fixed at the maximal non-superquantum boundary;
2. independent bottlenecks compose additively in obstruction measure and
   multiplicatively in constraint strength.
```

Result:

```text
schema = closed_metric_orientation_consistency
verdict = VALID_HIT
passed = 6/6
imports = none
open_parameters = none
CHSH = -2.828427125
```

Passed:

```text
no_signalling:
  worst_delta = 0.0

bell_strength:
  E00 = -0.707106781...
  E01 = -0.707106781...
  E10 = -0.707106781...
  E11 =  0.707106781...
  CHSH = -2 sqrt(2)

tsirelson_discipline:
  excess = 0.0

import_screen:
  no Bell/PR parity table

metric_bottleneck_response:
  open_strength = 2.828427125
  blocked_strength = 1.253340015
  response = 1.575087109

parameter_closure:
  beta closed by sqrt(2)*atanh(1/sqrt(2))
  metric response closed by exp(-bottleneck)
```

Controls remain meaningful:

```text
local_hidden_orientation_baseline:
  CHSH = -2.0

global_orientation_consistency:
  CHSH violation exists, but beta remains open and metric response is absent.

direct_pr_parity_control:
  CHSH = 4.0, rejected as superquantum and explicitly imported.
```

### 174.203. Interpretation Of The Closed Pass

This is the strongest result in the base-primitives branch so far.

It gives a coherent toy-level stack:

```text
1. reversible context transport;
2. global orientation-consistency selection;
3. critical non-superquantum coupling;
4. additive bottleneck / multiplicative constraint attenuation;
5. irreversible local readout.
```

It also gives a concrete answer to the previous wall:

```text
local residue propagation alone:
  fails Bell and metric.

two-layer context/readout:
  fixes reversibility/readout split but still fails Bell and metric.

global orientation consistency:
  fixes Bell but leaves beta and metric open.

closed metric orientation consistency:
  passes the toy no-signalling/Bell/Tsirelson/import/metric/parameter screen.
```

This is not yet a derivation of QM. It is a closed toy selector candidate that
should now be promoted into a formal theorem-card route with strict forbidden
upgrades.

### 174.204. New Candidate Primitive Stack

The candidate B0 replacement should be stated as a route, not as a final
primitive:

```text
B0-closed-selector route:

primitive distinctions are not states;
unexposed distinctions undergo reversible context transport;
global consistency selects joint record constraints;
selection is critical at the non-superquantum boundary;
metric obstruction attenuates constraint strength by additive/multiplicative
composition;
local readout stabilizes records and leaves unsupported residue.
```

Forbidden claims:

```text
does_not_prove_full_QM;
does_not_derive_Hilbert_space_yet;
does_not_derive_Born_rule_yet;
does_not_derive_metric_geometry_yet;
does_not_replace_experimental_physics;
does_not_claim parameter-free universe constants.
```

Allowed next claim:

```text
closed_metric_orientation_consistency is a finite toy candidate showing that
IDT-style primitives can jointly satisfy no-signalling, Bell-strength,
Tsirelson discipline, explicit import rejection, bottleneck response, and
parameter closure under stated closure principles.
```

### 174.205. Immediate Next Formalization

The next non-negotiable step is formalization:

```text
theorem_card:
  id: closed_metric_orientation_consistency_toy_selector
  role: base_route_candidate
  status: finite_toy_valid_hit
  assumptions:
    - reversible_context_transport
    - global_orientation_consistency_selection
    - critical_non_superquantum_boundary
    - additive_bottleneck_obstruction
    - multiplicative_constraint_attenuation
    - local_readout_stabilization
  conclusions:
    - no_signalling_on_selector_screen
    - CHSH_equals_2_sqrt_2_on_selector_screen
    - no_PR_import
    - bottleneck_sensitive_constraint_strength
    - no_open_numeric_parameter_on_toy_screen
  forbidden_upgrades:
    - full_QM
    - Hilbert_derivation
    - Born_rule_derivation
    - physical_metric_derivation
```

This is now a real route to work, not a vague search direction.

### 174.206. Final Route Closure Test

A final-route evaluator was added:

```text
scripts/evaluate_final_route_closure.py
```

It tests whether the closed selector is merely a CHSH/Tsirelson toy hit or a
route toward the full singlet/Born angle curve.

The screen checks:

```text
1. no-signalling zero-marginal probability validity;
2. canonical CHSH/Tsirelson boundary;
3. full angle-grid Born curve E(theta) = -cos(theta);
4. explicit import screen against inserted Born/Hilbert projection;
5. metric composition under additive bottlenecks;
6. parameter closure.
```

This is the first test in the branch that directly asks:

```text
Did we only hit the CHSH points, or did we get the whole QM angle law?
```

### 174.207. Final Route Result

Result:

```text
schema = closed_metric_orientation_consistency
verdict = NEW_WALL
passed = 4/6
imports = none
open_parameters = none
```

Passed:

```text
no_signalling;
CHSH/Tsirelson boundary;
import rejection;
parameter closure.
```

Failed:

```text
born_angle_curve;
metric_composition.
```

Concrete failure:

```text
closed selector correlation:
  E(theta) = -tanh(beta * cos(theta))

Born/singlet target:
  E(theta) = -cos(theta)

max_error = 0.152714699948
rms_error = 0.082268598746
max_error_delta = 0.0
```

The selector was closed to hit:

```text
E(pi/4) = -1/sqrt(2)
```

but at:

```text
theta = 0
```

it gives:

```text
-tanh(beta) = -0.847285300052...
```

instead of:

```text
-1
```

Metric composition also fails for the closed selector:

```text
direct = 0.043852863792
composed = 0.035204773658
```

because the bottleneck acts on the hidden coupling before a nonlinear `tanh`,
not linearly/multiplicatively on the observable correlation.

### 174.208. Control Result

The control:

```text
cosine_projection_control
```

passes the Born curve exactly:

```text
max_error = 0.0
rms_error = 0.0
```

and passes metric composition, but it is rejected as:

```text
IMPORTED_HIT
```

because it explicitly imports:

```text
born_cosine_projection
```

This confirms that the evaluator can distinguish:

```text
real route progress
```

from:

```text
inserting the answer.
```

### 174.209. Interpretation Of The New Wall

The new wall is precise:

```text
critical global orientation consistency explains the CHSH/Tsirelson point,
but not the full Hilbert/Born angle curve.
```

The missing primitive is not Bell parity and not merely global selection.

The missing primitive is:

```text
a lawful projection from context orientation to observable correlation that is
linear/cosine-like over the full angle continuum, not a Boltzmann/tanh
least-residue selector.
```

Also:

```text
metric attenuation must compose at the observable amplitude/correlation level,
or the pre-readout nonlinear selector must be replaced by a structure where
composition is preserved through readout.
```

So the current route status becomes:

```text
No final QM route yet.
No total failure either.
New wall located at:
  full Born angle law + metric composition through readout.
```

### 174.210. Maximum Safe Next Step

The next candidate must not tune another beta. It must replace the scalar
least-residue selector with a structure whose observable projection is cosine
by construction from primitive composition, without importing Hilbert space.

Candidate direction:

```text
context orientation composition:
  orientations compose by rotations;

readout projection:
  record correlation is the preserved bilinear overlap of transported
  orientations;

metric obstruction:
  bottlenecks attenuate transported overlap multiplicatively before local
  readout, while preserving composition.
```

Forbidden shortcut:

```text
do not insert E(theta) = -cos(theta) as a readout rule.
```

Required one-pass successor:

```text
derive cosine overlap from primitive reversible orientation composition and
local readout normalization, then rerun:
  no-signalling;
  CHSH/Tsirelson;
  full Born angle curve;
  import screen;
  metric composition;
  parameter closure.
```

This is the next true wall-breaking test.

### 174.211. Normalized Overlap Primitive One-Pass Test

A successor evaluator was added:

```text
scripts/evaluate_overlap_primitive_route.py
```

It tests a new primitive candidate rather than another selector parameter:

```text
normalized_orientation_overlap
```

Primitive content:

```text
1. unexposed distinctions carry reversible orientation constraints;
2. context transport composes by norm-preserving rotations;
3. local readout exposes the normalized bilinear overlap of transported
   orientations;
4. metric bottlenecks attenuate observable overlap multiplicatively;
5. no direct Born/cosine table is used.
```

This is the first test after the tanh wall that asks whether the full
singlet/Born curve can be obtained from a lower primitive:

```text
orientation transport + normalized overlap
```

rather than:

```text
E(theta) = -cos(theta) inserted as a readout law.
```

### 174.212. Normalized Overlap Result

Result:

```text
route = normalized_orientation_overlap
verdict = NEW_PRIMITIVE_HIT
passed = 8/8
imports = none
open_parameters = none
```

Passed:

```text
no_signalling:
  zero-marginal joint distribution valid on the angle grid.

context_composition:
  orientation transport composes reversibly and preserves norm.

chsh_boundary:
  CHSH = -2.828427124746 = -2 sqrt(2).

born_angle_curve:
  full singlet/Born angle curve recovered on the checked grid.

metric_composition:
  additive bottlenecks attenuate observable overlap multiplicatively.

import_screen:
  no Born/Hilbert/Bell table import.

parameter_closure:
  no open parameters on this screen.

primitive_minimality:
  uses reversible orientation transport and normalized bilinear overlap, not a
  direct angle-correlation table.
```

Concrete values:

```text
born_angle_curve:
  max_error = 0.0
  rms_error = 0.0

metric_composition:
  direct   = -0.04027858441
  composed = -0.04027858441
```

Controls:

```text
born_cosine_projection_control:
  recovers the curve, but is rejected as IMPORTED_HIT because it directly
  imports born_cosine_projection and has no primitive context composition.

closed_tanh_selector_previous:
  remains NEW_WALL because it hits CHSH/Tsirelson but fails the full Born curve,
  metric composition, and primitive-minimality screens.
```

### 174.213. Interpretation Of The New Primitive Hit

This is the strongest route result so far.

The new wall from 174.207 is bypassed on the finite screen:

```text
tanh selector wall:
  E(theta) = -tanh(beta cos theta)
  fails full Born curve.

normalized overlap route:
  E(theta) is exposed as the normalized bilinear overlap of reversibly
  transported orientations.
  passes full Born curve and metric composition.
```

This does not prove full QM. It does provide a much stronger B0 replacement
candidate:

```text
B0-overlap route:
  distinction is not a state;
  unexposed distinction carries orientation constraint;
  context is reversible orientation transport;
  readout exposes normalized overlap as a stable record correlation;
  unsupported mismatch remains residue;
  bottlenecks attenuate overlap multiplicatively.
```

The key conceptual move:

```text
probability is still not primitive;
Hilbert space is still not primitive;
Born rule is not inserted as a table.

The primitive candidate is normalized overlap of transported constraints.
```

### 174.214. New Remaining Wall

The remaining wall is now formal, not exploratory:

```text
Can normalized orientation overlap be justified as the unique stable readout
invariant of reversible context transport and record stabilization?
```

If yes, this becomes a route to:

```text
Hilbert-like inner product;
Born-like angle law;
Bell/Tsirelson screen;
metric attenuation.
```

If no, normalized overlap is just a well-chosen mathematical primitive.

So the next proof obligation is:

```text
reversible context transport + stable scalar readout invariant
=> normalized bilinear overlap
```

with forbidden upgrades:

```text
do not call this a derivation of Hilbert space yet;
do not call this a derivation of full Born rule yet;
do not claim full QM;
do not claim physical metric derivation.
```

### 174.215. Theorem-Card Candidate

```text
theorem_card:
  id: normalized_orientation_overlap_toy_route
  role: base_route_candidate
  status: finite_new_primitive_hit
  statement: >
    A finite toy route with reversible orientation transport, normalized
    bilinear overlap readout, and multiplicative bottleneck attenuation passes
    the no-signalling, CHSH/Tsirelson, full singlet angle-curve, import,
    metric-composition, parameter-closure, and primitive-minimality screens.
  assumptions:
    - reversible_orientation_transport
    - norm_preservation
    - normalized_bilinear_overlap_readout
    - zero_marginal_joint_readout_form
    - additive_bottleneck_obstruction
    - multiplicative_overlap_attenuation
  conclusions:
    - no_signalling_on_angle_grid
    - CHSH_equals_2_sqrt_2_on_canonical_screen
    - singlet_angle_curve_on_checked_grid
    - metric_composition_on_overlap_screen
    - no_direct_Born_or_PR_import
    - no_open_numeric_parameters_on_screen
  forbidden_upgrades:
    - full_QM
    - Hilbert_space_derivation
    - Born_rule_derivation
    - physical_metric_derivation
```

This is now the main route candidate.

### 174.216. Normalized Overlap Uniqueness Pass

A uniqueness evaluator was added:

```text
scripts/evaluate_overlap_uniqueness.py
```

It asks whether normalized overlap is forced by the primitive constraints, or
whether it is merely a renamed Hilbert inner product.

The one-pass screen separates two layers:

```text
weak invariants:
  reversible transport invariance;
  positive scale-gauge invariance;
  same/opposite normalization.

strong compositional invariant:
  the scale-restored readout kernel

    K(x, y) = ||x|| ||y|| R(x, y)

  must be additive in each compatible input.
```

The weak invariants alone are not enough.

Counterexamples:

```text
cubic_overlap:
  R(x,y) = cos(x,y)^3

tanh_overlap:
  R(x,y) = tanh(beta cos(x,y)) / tanh(beta)
```

Both pass the weak invariants but fail compositional additivity.

This is important: it prevents a false proof.

### 174.217. Uniqueness Result

Result:

```text
candidate = normalized_bilinear_overlap
verdict = UNIQUE_HIT
passed = 6/6
imports = none
```

Passed:

```text
transport_invariance:
  simultaneous reversible rotations preserve readout.

scale_gauge:
  readout ignores arbitrary positive support scale.

normalization:
  same/opposite orientations normalize to +1/-1.

kernel_additivity:
  scale-restored readout kernel is additive in each compatible input.

invariant_kernel_uniqueness:
  O(2)-invariant additive normalized scalar kernel reduces to the Euclidean
  dot product.

import_screen:
  no direct angle-correlation import.
```

Controls:

```text
direct_cosine_projection:
  passes the mathematical screens but is rejected as IMPORTED_HIT because it
  imports angle_cosine_projection.

cubic_overlap:
  WEAK_AMBIGUITY;
  fails kernel_additivity and invariant_kernel_uniqueness.

tanh_overlap:
  WEAK_AMBIGUITY;
  fails kernel_additivity and invariant_kernel_uniqueness.

absolute_overlap:
  rejected by opposite-orientation normalization and additivity.

local_linear_overlap:
  rejected by invariance/normalization/additivity.
```

### 174.218. Conditional Theorem Extracted

The finite screen supports this conditional theorem route:

```text
If:
  1. context transport is reversible and norm-preserving;
  2. readout is invariant under simultaneous context transport;
  3. readout ignores arbitrary positive support scale;
  4. same/opposite orientations normalize to +1/-1;
  5. compatible independent constraints compose additively at the
     scale-restored kernel level;

then:
  the unique stable scalar readout kernel is the normalized bilinear overlap.
```

In mathematical terms:

```text
K(x, y) = ||x|| ||y|| R(x, y)
```

Additivity makes `K` bilinear. Reversible norm-preserving transport invariance
makes `K` an O(2)-invariant bilinear form. Normalization fixes the scalar:

```text
K(x, y) = x dot y
R(x, y) = (x dot y) / (||x|| ||y||)
```

This is exactly the overlap primitive used in the route.

### 174.219. Updated Wall Status

The previous concern was:

```text
normalized overlap may be a hidden Hilbert import.
```

After this pass the status is sharper:

```text
not a hidden import if compatible-kernel additivity is accepted as an IDT
composition principle;

still open if compatible-kernel additivity itself cannot be justified from the
primitive base.
```

So the remaining proof obligation is no longer:

```text
why overlap?
```

It is:

```text
why must compatible constraints compose additively at the scalar kernel level?
```

This is a much smaller and cleaner primitive question.

### 174.220. New Theorem-Card Candidate

```text
theorem_card:
  id: reversible_context_transport_implies_normalized_overlap
  role: primitive_readout_separator
  status: candidate_conditional_proof
  statement: >
    Under reversible norm-preserving context transport, transport-invariant
    scale-gauge readout, same/opposite normalization, and additive compatible
    scalar-kernel composition, the unique scalar readout invariant is the
    normalized bilinear overlap.
  assumptions:
    - reversible_context_transport
    - norm_preservation
    - transport_invariant_scalar_readout
    - positive_scale_gauge
    - same_opposite_normalization
    - compatible_kernel_additivity
  conclusion:
    - normalized_bilinear_overlap_readout
  forbidden_upgrades:
    - full_QM
    - full_Hilbert_space_derivation
    - physical_metric_derivation
```

This is now the formal bridge candidate behind the overlap route.

### 174.221. Compatible-Kernel Additivity Principle Pass

A composition-principle evaluator was added:

```text
scripts/evaluate_kernel_additivity_principle.py
```

It asks whether the remaining assumption:

```text
compatible_kernel_additivity
```

can itself be justified as the only finite composition law surviving basic IDT
composition constraints.

The screen tests candidate laws against:

```text
1. commutative associative composition with empty identity;
2. refinement invariance under arbitrary splitting of compatible support;
3. exact cancellation of opposite compatible contributions;
4. monotone locality for positive support;
5. correct infinitesimal linear tangent at empty support;
6. finite Cauchy closure over compatible pieces;
7. import screen.
```

Candidates tested:

```text
additive_kernel_composition;
imported_additive_sum;
max_composition;
product_composition;
p_norm_composition;
bounded_tanh_composition;
saturating_sum_composition.
```

### 174.222. Additivity Result

Result:

```text
candidate = additive_kernel_composition
verdict = PRINCIPLE_HIT
passed = 7/7
imports = none
```

Control:

```text
imported_additive_sum:
  passed the mathematical screens but was rejected as IMPORTED_HIT by the
  import screen.
```

Rejected alternatives:

```text
max_composition:
  fails refinement, cancellation, infinitesimal linearity, finite closure.

product_composition:
  fails identity, refinement, cancellation, infinitesimal linearity, closure.

p_norm_composition:
  fails refinement, cancellation, infinitesimal linearity, closure.

bounded_tanh_composition:
  fails identity/associativity at the checked boundary, refinement, closure.

saturating_sum_composition:
  fails identity/associativity, refinement, closure.
```

### 174.223. Interpretation Of Additivity Pass

The previous remaining wall was:

```text
why must compatible constraints compose additively at the scalar kernel level?
```

The finite result is:

```text
because any non-additive alternative tested either depends on arbitrary
decomposition of the same support, cannot cancel opposite compatible
contributions, lacks the correct empty-support tangent, or fails finite closure.
```

This turns additivity from an arbitrary assumption into a candidate IDT
composition principle:

```text
compatible support is extensive under decomposition-invariant exposure.
```

Equivalently:

```text
if splitting the same compatible support is unobservable, and opposite support
can cancel, then the exposed scalar kernel must be additive.
```

### 174.224. Current Strongest Route

The strongest current route is now:

```text
1. primitive distinctions are not states;
2. unexposed distinctions carry orientation constraints;
3. compatible support composes additively at the scalar-kernel level;
4. reversible context transport preserves norm and composition;
5. the unique stable scalar readout is normalized bilinear overlap;
6. zero-marginal local readout gives no-signalling;
7. normalized overlap gives the singlet angle curve and CHSH/Tsirelson screen;
8. additive bottleneck obstruction gives multiplicative overlap attenuation.
```

Status:

```text
finite route candidate strengthened;
not full QM;
not full Hilbert derivation;
not physical metric derivation;
but no current toy-level wall remains in the tested Bell/Born/metric route.
```

The next wall is formalization/proof-engineering:

```text
encode these as theorem cards and verifier gates, then attempt machine-checkable
proof artifacts for the algebraic pieces.
```

### 174.225. Compressed QM Route Pass 1

A compressed finite-QM route evaluator was added:

```text
scripts/evaluate_qm_compressed_route.py
```

This pass asks whether the real normalized-overlap route can scale toward QM,
or whether it immediately hits the known real-carrier wall.

It compares:

```text
real_normalized_overlap
phase_bundle_normalized_overlap
```

against:

```text
1. finite projective Born normalization;
2. projective repeatability;
3. phase-gauge invariance;
4. relative phase interference;
5. tensor product multiplicativity;
6. local tomography parameter count;
7. singlet angle curve;
8. import screen.
```

### 174.226. Compressed Pass 1 Result

Result:

```text
route = real_normalized_overlap
verdict = NEW_WALL
passed = 3/8
```

It fails:

```text
finite_projective_born:
  max_sum_error = 0.643564356436

phase_gauge:
  global phase is exposed as a distinct record

relative_phase_interference:
  max_error = 0.25

tensor_multiplicativity:
  error = 0.254448484848

local_tomography_dimension:
  K_A = 3
  K_B = 3
  K_AB = 10
  K_A*K_B = 9
```

So the real overlap route reproduces the 2D singlet angle screen but cannot be
the finite-QM carrier route.

The successful route:

```text
route = phase_bundle_normalized_overlap
verdict = CARRIER_ROUTE_HIT
passed = 8/8
imports = none
open_principles = derive_phase_bundle_J_structure
```

It passes:

```text
finite_projective_born;
projective_repeatability;
phase_gauge;
relative_phase_interference;
tensor_multiplicativity;
local_tomography_dimension;
singlet_angle_curve;
import_screen.
```

Concrete local tomography result:

```text
K_A = 4
K_B = 4
K_AB = 16
K_A*K_B = 16
```

### 174.227. Interpretation Of Compressed Pass 1

This is a decisive compression result:

```text
real overlap:
  dead as a QM carrier route.

phase-bundle overlap:
  survives the finite carrier screen.
```

The next wall is precise and smaller:

```text
derive_phase_bundle_J_structure
```

Meaning:

```text
Why must an unexposed orientation constraint carry a phase/quadrature partner
J, so that global phase is gauge and relative phase is observable through
interference?
```

This is now the main route:

```text
compatible-kernel additivity
=> normalized overlap
=> phase-bundle normalized overlap
=> finite Born/projective/tensor/local-tomography screens
```

The maximum-three-pass plan becomes:

```text
Pass 1:
  real vs phase-bundle carrier screen.
  Result: phase-bundle route survives; real route rejected.

Pass 2:
  derive or kill phase-bundle J from reversible transport, gauge redundancy,
  and interference/composition constraints.

Pass 3:
  if Pass 2 survives, promote theorem cards + verifier gates for the finite
  QM route; if it fails, stop with exact wall.
```

### 174.228. Compressed QM Route Pass 2

Pass 2 tests the remaining open principle:

```text
derive_phase_bundle_J_structure
```

A targeted evaluator was added:

```text
scripts/evaluate_phase_bundle_j_derivation.py
```

It compares candidate one-parameter context transports against:

```text
1. reversible transport group;
2. norm preservation;
3. quadrature scale;
4. phase gauge;
5. relative phase interference;
6. import screen.
```

Result:

```text
candidate = canonical_quadrature_J
verdict = J_DERIVATION_HIT
passed = 6/6
imports = none
```

The imported control:

```text
candidate = imported_complex_J
verdict = IMPORTED_HIT
```

passes the mathematical screens but fails the import screen because it declares:

```text
complex_scalar_assumed
```

Near misses:

```text
no_phase_identity;
half_speed_rotation;
double_speed_rotation.
```

Rejected:

```text
hyperbolic_transport;
shear_transport.
```

Interpretation:

```text
The finite screen supports canonical quadrature J as the only non-imported
candidate among the checked transports that has reversible group structure,
norm preservation, correct quadrature scale, global phase gauge, and relative
phase interference.
```

Boundary:

```text
This does not derive complex scalars from IDT primitives.
It closes the current finite phase-bundle screen conditionally.
```

### 174.229. Pass 2 Theorem-Card Candidate

```text
theorem_card:
  id: reversible_phase_bundle_transport_selects_quadrature_J
  role: phase_bundle_separator
  status: candidate_conditional_proof
  statement: >
    Under reversible one-parameter context transport, norm preservation,
    quadrature scale, global phase-gauge equivalence, and relative-phase
    interference, the canonical quadrature transport J survives the finite
    screen while identity, wrong-speed rotations, hyperbolic transport, shear
    transport, and imported complex J controls are rejected or downgraded.
  assumptions:
    - reversible_context_transport_group
    - norm_preservation
    - quadrature_scale
    - global_phase_gauge
    - relative_phase_interference_screen
    - explicit_import_rejection
  conclusion:
    - canonical_quadrature_J_on_finite_screen
  forbidden_upgrades:
    - complex_scalar_derivation
    - full_Hilbert_space_derivation
    - full_QM
    - Born_rule_derivation
```

### 174.230. Compressed QM Route Pass 3

Pass 3 consolidates the finite route into one executable gate:

```text
scripts/verify_finite_qm_route.py
```

The gate checks the route as a dependency chain:

```text
compatible-kernel additivity
=> normalized bilinear overlap uniqueness
=> normalized orientation overlap route
=> phase-bundle quadrature J screen
=> compressed finite-QM carrier route
```

It also checks negative controls:

```text
imported additive control;
direct cosine/Born control;
previous tanh wall;
imported complex-J control;
real-carrier route wall.
```

The expected pass condition is not:

```text
full_QM_proved
```

It is:

```text
finite_qm_route_gate passes all current finite route and control verdicts.
```

### 174.231. Pass 3 Gate Meaning

If the gate passes, the current finite route status is:

```text
No current finite-screen wall remains in the tested route:
  additive compatible kernel;
  normalized overlap;
  phase-bundle J;
  finite Born/projective/phase/tensor/local-tomography screens.
```

Still open:

```text
1. machine-checkable formal proofs for the algebraic steps;
2. theorem-card/manifold integration into the main verifier graph;
3. full representation theorem from the finite route to complex Hilbert space;
4. universal Born rule beyond checked finite context probabilities;
5. physical metric/GR projection.
```

The honest claim is therefore:

```text
finite route consolidated;
full QM not closed.
```

### 174.232. Pass 3 Gate Result

The executable gate passed:

```text
python3 scripts/verify_finite_qm_route.py

finite_qm_route_gate=PASS
checks=13
```

Checked positive route verdicts:

```text
kernel.additive:
  PRINCIPLE_HIT

overlap.unique:
  UNIQUE_HIT

route.normalized_orientation_overlap:
  NEW_PRIMITIVE_HIT

phase_j.canonical_quadrature:
  J_DERIVATION_HIT

compressed_qm.phase_bundle_route:
  CARRIER_ROUTE_HIT
```

Checked negative controls:

```text
kernel.imported_control:
  IMPORTED_HIT

overlap.direct_cosine_control:
  IMPORTED_HIT

route.previous_tanh_wall:
  NEW_WALL

route.born_control:
  IMPORTED_HIT

phase_j.imported_complex_control:
  IMPORTED_HIT

compressed_qm.real_route:
  NEW_WALL
```

This matters because the route now has an executable dependency check:

```text
compatible-kernel additivity
=> normalized overlap uniqueness
=> finite orientation-overlap route
=> canonical quadrature J screen
=> phase-bundle finite-QM carrier screen
```

### 174.233. Status After The Three Compressed Passes

Closed on the current finite screens:

```text
1. real normalized-overlap carrier route is rejected;
2. phase-bundle normalized-overlap route passes finite carrier screens;
3. canonical quadrature J passes the finite derivation screen;
4. normalized overlap is unique under compatible-kernel additivity;
5. compatible-kernel additivity passes the finite composition-principle screen;
6. all route controls still reject imports and known walls.
```

Still not closed:

```text
1. full complex-Hilbert representation theorem;
2. universal Born-rule theorem beyond finite checked contexts;
3. machine-checkable proof artifacts for the algebraic theorem cards;
4. physical metric / GR projection;
5. full_QM_I.
```

Therefore the best current status is:

```text
The finite-QM route is consolidated and no current finite-screen wall remains
inside the tested dependency chain.

The theory has not proved full QM.

The next wall is formal theorem/proof-artifact work plus the representation
classification theorem from the finite route to complex Hilbert space.
```

### 174.234. Representation Wall Pass

The next pass attacked the representation/classification wall directly with:

```text
scripts/evaluate_finite_sector_classification.py
```

The screen compares finite carrier candidates against:

```text
1. phase-bundle route;
2. product-context local tomography;
3. hidden joint-only invariant rejection;
4. bounded Bell-strength / non-superquantum correlation window;
5. finite route closure;
6. representation classification status;
7. import screen.
```

Result:

```text
candidate = complex_hilbert_qubit_route
verdict = FINITE_SECTOR_HIT
passed = 7/7
```

Rejected controls:

```text
classical_simplex_bit:
  lacks phase/interference and Bell-strength contextual capacity.

real_hilbert_rebit:
  fails local tomography and has product-invisible Y tensor Y.

quaternionic_hilbert_bit:
  fails the current local tomography/composition route.

boxworld_pr:
  exceeds Tsirelson and imports PR table.

unconstrained_generic_gpt:
  lacks the finite route-closure contract and exceeds the bounded window.
```

But the explicit residual remains:

```text
candidate = finite_route_closed_residual
verdict = OPEN_RESIDUAL
passed = 5/7
open = 2
```

Open obligations:

```text
hidden_joint_invariant:
  residual declares finite route closure but lacks a proof that all hidden
  joint degrees are exhausted.

representation_classification:
  no theorem currently proves this residual equivalent to the complex route.
```

### 174.235. Updated Gate Status

The consolidated gate now includes the finite-sector frontier:

```text
scripts/verify_finite_qm_route.py
```

Expected status is deliberately not:

```text
no residual
```

Expected status is:

```text
complex finite route hits;
known finite controls reject;
route-closed residual remains open.
```

This prevents a false closure claim.

### 174.236. Exact Current Wall

The wall is now narrow:

```text
finite_route_closed_residual
```

To cross it, IDT needs:

```text
finite_sector_representation_classification_theorem
```

or a more precise pair:

```text
1. finite_projection_determinacy:
   if two stable carrier assignments agree on every finite route-generated
   projection, they are not physically distinct.

2. projective_consistency:
   compatible finite route sectors glue without adding new hidden
   distinguishability directions.
```

Then the route would become:

```text
all finite route sectors are complex-Hilbert-like
+ finite projection determinacy
+ projective consistency
=> full operational carrier is complex-Hilbert-like up to projective/inductive
   representation.
```

This is not yet proved.

### 174.237. Honest Status After This Pass

What improved:

```text
The wall is no longer "generic GPT space is broad".
The known finite represented alternatives are explicitly rejected.
The only surviving finite frontier object is an abstract route-closed residual.
```

What remains:

```text
We still need the representation/classification theorem that collapses the
route-closed residual into the complex route or rejects it.
```

Therefore:

```text
finite represented frontier: mostly crossed;
universal carrier classification: still open, but now localized.
```

### 174.238. Conditional Residual-Closure Pass

A follow-up evaluator was added:

```text
scripts/evaluate_projective_residual_closure.py
```

It tests which minimal closure principles are sufficient to remove the
remaining route-closed residual without importing Hilbert space.

Routes tested:

```text
unclosed_route_residual;
finite_projection_determinacy_only;
projective_consistency_only;
fpd_plus_projective_consistency;
imported_hilbert_completion.
```

Result:

```text
route = fpd_plus_projective_consistency
verdict = CONDITIONAL_CLOSURE_HIT
passed = 6/6
imports = none
```

Near misses:

```text
finite_projection_determinacy_only:
  closes hidden residual separation but not gluing/structure preservation.

projective_consistency_only:
  preserves compatible finite-sector gluing but does not exclude a residual
  that agrees on all checked finite projections.
```

Rejected control:

```text
imported_hilbert_completion:
  IMPORTED_HIT because it assumes complex_hilbert_completion_assumed.
```

### 174.239. Meaning Of The Conditional Hit

The residual can be closed by the pair:

```text
finite_projection_determinacy
+ projective_consistency
```

without naming Hilbert space.

But this is not a proof yet. The new theorem obligation is:

```text
IDT must prove finite_projection_determinacy and projective_consistency from
the primitive base, or mark carrier selection as conditional on them.
```

This is better than the previous wall because:

```text
1. one principle alone is insufficient;
2. the pair is sufficient on the finite frontier screen;
3. direct Hilbert completion is caught as circular import.
```

### 174.240. Current Route After Moving Past The Frontier

The strongest route now is:

```text
finite route gate
+ finite represented frontier
+ conditional residual closure by FPD/projective consistency
=> conditional complex-Hilbert-like carrier route
```

Allowed claim:

```text
The carrier-selection wall has been reduced to proving two non-Hilbert closure
principles: finite projection determinacy and projective consistency.
```

Forbidden claim:

```text
full QM proved.
complex Hilbert derived unconditionally.
Born rule derived universally.
```

### 174.241. FPD / Projective Consistency Derivation Pass

The next pass tested whether the closure pair itself can be derived from lower
IDT principles or whether it is just a renamed assumption.

Evaluator:

```text
scripts/evaluate_fpd_projective_derivation.py
```

Routes tested:

```text
b2_core_only;
nusd_finite_generation;
conservative_projective_gluing_only;
nusd_plus_conservative_projective_gluing;
declared_projective_consistency;
imported_hilbert_completion.
```

Result:

```text
route = nusd_plus_conservative_projective_gluing
verdict = DERIVATION_CANDIDATE
passed = 6/6
imports = none
```

Meaning:

```text
NUSD + finite context generation + D_cl
  -> finite projection determinacy.

structure-preserving restrictions + conservative projective gluing
  -> projective consistency.

D_cl + conservative gluing
  -> no new gluing direction unless a finite witness route exists.
```

Partial results:

```text
nusd_finite_generation:
  PARTIAL_DERIVATION
  derives FPD side but not projective gluing.

conservative_projective_gluing_only:
  PARTIAL_DERIVATION
  derives projective side but not finite projection determinacy.

b2_core_only:
  OPEN_WALL
  does not exclude stable distinctions outside finite projections and does not
  control projective gluing.
```

Rejected controls:

```text
declared_projective_consistency:
  IMPORTED_HIT

imported_hilbert_completion:
  IMPORTED_HIT
```

### 174.242. Status After FPD / Projective Pass

The wall has moved again.

Old wall:

```text
finite_route_closed_residual remains open.
```

This historical status is superseded by 174.280, where the residual placeholder
is rejected by constructive-carrier admissibility.

New wall:

```text
Prove or adopt two lower principles:

1. NUSD:
   no unwitnessed stable difference.

2. conservative projective gluing:
   compatible finite route sectors glue without adding new stable
   distinguishability directions unless D_cl supplies a finite witness route.
```

This is progress because neither principle names:

```text
Hilbert space;
complex scalars;
Born probabilities;
unitary dynamics;
metric geometry.
```

But it is still conditional:

```text
If NUSD and conservative projective gluing are accepted/proved,
then the current finite residual-closure wall is conditionally crossed.

If either principle fails, full carrier selection remains blocked.
```

The next theorem cards should therefore be:

```text
nusd_implies_finite_projection_determinacy
conservative_projective_gluing_implies_projective_consistency
```

with status:

```text
candidate_conditional_proof
```

### 174.243. One-Pass Full-QM Proof Attempt

A single full-stack proof-attempt evaluator was added:

```text
scripts/evaluate_full_qm_proof_attempt.py
```

It does not attempt to prove QM by prose. It audits the current theorem stack:

```text
finite route gate
-> route-closed residual closure
-> FPD/projective-consistency derivation
-> universal representation theorem
-> universal Born readout theorem
-> unitary dynamics theorem
-> general composite theorem
-> physical phase-scale boundary
```

Result:

```text
full_qm_proof_attempt = CONDITIONAL_ROUTE_ADVANCED
pass = 1
conditional = 2
open = 5
failed = 0
```

Passed:

```text
finite_route_gate:
  checks = 31
```

Conditional:

```text
finite_route_residual_closure:
  closed if finite projection determinacy and projective consistency hold.

fpd_projective_derivation:
  NUSD plus conservative projective gluing is a non-Hilbert derivation
  candidate for those two closure principles.
```

Open:

```text
universal_representation_theorem:
  prove all finite-projectively determined carriers satisfying the route
  contract are complex-Hilbert-like.

universal_born_readout_theorem:
  extend finite normalized-overlap screens to a universal Born readout theorem.

unitary_dynamics_theorem:
  derive reversible inheritance dynamics without assuming unitarity.

general_composite_theorem:
  prove product-context exhaustion/tensor composition for arbitrary admissible
  finite and projective-limit composites.

physical_phase_scale_boundary:
  keep hbar_I as calibration or prove an independent action-scale theorem.
```

### 174.244. Full-QM Attempt Verdict

The one-pass proof attempt did not prove full QM.

It did produce a cleaner theorem map:

```text
current route is not blocked by a failed finite gate;
current route is not blocked by known finite carrier controls;
current route is conditional on two lower closure principles;
full QM remains open at five named theorem obligations.
```

This is a useful result because the failure is not vague:

```text
No failed check.
No hidden Hilbert import in the current conditional route.
Five explicit missing theorems.
```

The next mathematically meaningful target is:

```text
universal_representation_theorem
```

because without it, the route cannot honestly upgrade from:

```text
finite route and conditional carrier pressure
```

to:

```text
complex Hilbert carrier selected.
```

### 174.245. Representation Theorem Attempt

The next one-pass target was the first open theorem from the full-QM proof
attempt:

```text
universal_representation_theorem
```

Evaluator:

```text
scripts/evaluate_representation_classification_attempt.py
```

It tests whether the current route can reach a complex-Hilbert-like
representation without directly importing Hilbert space.

Routes tested:

```text
finite_route_only;
fpd_projective_closed_route;
spectral_without_symmetry;
symmetry_without_spectral;
spectral_symmetry_route;
imported_complex_hilbert_representation.
```

Result:

```text
route = spectral_symmetry_route
verdict = CONDITIONAL_REPRESENTATION_ROUTE
passed = 8/8
imports = none
```

The conditional route requires:

```text
1. finite route contract;
2. FPD/projective residual closure;
3. phase-bundle J;
4. normalized overlap;
5. local tomography;
6. spectral decomposition into orthogonal exposed contexts;
7. rich D_cl-preserving reversible symmetry.
```

Controls:

```text
spectral_without_symmetry:
  OPEN_WALL

symmetry_without_spectral:
  OPEN_WALL

fpd_projective_closed_route:
  OPEN_WALL

imported_complex_hilbert_representation:
  IMPORTED_HIT
```

### 174.246. Meaning Of The Representation Attempt

The representation wall did not disappear.

It split into two sharper obligations:

```text
spectral_decomposition_theorem:
  finite stable states decompose into orthogonal exposed context records.

rich_reversible_symmetry_theorem:
  D_cl automorphisms are rich enough to connect pure exposed contexts while
  preserving normalized overlap and route structure.
```

If both are proved, the route has a non-imported representation theorem
candidate.

If either fails, complex-Hilbert carrier selection remains blocked.

This is progress because the missing theorem is no longer:

```text
some representation theorem
```

but:

```text
spectrality + rich reversible D_cl symmetry
```

with direct Hilbert import rejected by the executable control.

### 174.247. Updated One-Pass Full-QM Attempt

After the representation pass:

```text
full_qm_proof_attempt = CONDITIONAL_ROUTE_ADVANCED
pass = 1
conditional = 3
open = 4
failed = 0
```

Conditional:

```text
finite_route_residual_closure
fpd_projective_derivation
universal_representation_theorem
```

Still open:

```text
universal_born_readout_theorem
unitary_dynamics_theorem
general_composite_theorem
physical_phase_scale_boundary
```

This still does not prove QM.

But the one-pass strategy made progress:

```text
universal_representation_theorem moved from OPEN to CONDITIONAL.
```

The next full-proof pass should attack the next open theorem:

```text
universal_born_readout_theorem
```

### 174.248. Born / Readout Theorem Attempt

The next one-pass target was:

```text
universal_born_readout_theorem
```

Evaluator:

```text
scripts/evaluate_born_readout_attempt.py
```

It tests whether finite normalized-overlap readouts can be promoted to a
Born-like context probability theorem without importing the Born rule.

Routes tested:

```text
finite_overlap_screens_only;
normalization_only;
normalization_exclusivity;
normalization_exclusivity_coarse_graining;
quadratic_context_probability_route;
imported_born_rule.
```

Result:

```text
route = quadratic_context_probability_route
verdict = CONDITIONAL_BORN_ROUTE
passed = 7/7
imports = none
```

The conditional route requires:

```text
1. positive quadratic measure;
2. context normalization;
3. exclusivity additivity;
4. coarse-graining consistency;
5. operational equivalence.
```

The direct import control is rejected:

```text
route = imported_born_rule
verdict = IMPORTED_HIT
imports = born_rule_assumed
```

Near-wall controls show why each condition matters:

```text
finite_overlap_screens_only:
  lacks normalization, exclusivity, coarse-graining, and operational
  equivalence.

normalization_only:
  still lacks exclusivity, coarse-graining, and operational equivalence.

normalization_exclusivity:
  still lacks coarse-graining and operational equivalence.

normalization_exclusivity_coarse_graining:
  still lacks operational equivalence.
```

### 174.249. Meaning Of The Born Attempt

The Born wall did not disappear.

It split into four sharper readout obligations:

```text
context_normalization_theorem
exclusivity_additivity_theorem
coarse_graining_consistency_theorem
operational_equivalence_probability_theorem
```

If those are proved from IDT primitives and positive quadratic readout, the
route gives a non-imported Born-like finite context probability theorem.

If any fails, the universal Born/readout theorem remains blocked.

This is progress because:

```text
the route no longer says "derive Born rule" as one opaque demand;
it states exactly which readout obligations turn positive quadratic weights
into probabilities.
```

### 174.250. Updated One-Pass Full-QM Attempt After Born Pass

After the Born/readout pass:

```text
full_qm_proof_attempt = CONDITIONAL_ROUTE_ADVANCED
pass = 1
conditional = 4
open = 3
failed = 0
```

Conditional:

```text
finite_route_residual_closure
fpd_projective_derivation
universal_representation_theorem
universal_born_readout_theorem
```

Still open:

```text
unitary_dynamics_theorem
general_composite_theorem
physical_phase_scale_boundary
```

This still does not prove QM.

But the pass made measurable progress:

```text
universal_born_readout_theorem moved from OPEN to CONDITIONAL.
```

The next full-proof pass should attack:

```text
unitary_dynamics_theorem
```

### 174.251. Unitary / Generator Dynamics Attempt

The next one-pass target was:

```text
unitary_dynamics_theorem
```

Evaluator:

```text
scripts/evaluate_unitary_dynamics_attempt.py
```

It tests whether reversible inheritance dynamics can be routed to
unitary/antiunitary-like and generator-compatible maps without assuming
unitary evolution.

Routes tested:

```text
finite_unitary_gates_only;
dcl_automorphism_only;
wigner_like_symmetry_route;
continuity_without_generator;
continuous_generator_route;
imported_unitary_dynamics.
```

Result:

```text
route = continuous_generator_route
verdict = CONDITIONAL_DYNAMICS_ROUTE
passed = 8/8
imports = none
```

The conditional route requires:

```text
1. reversible D_cl automorphism;
2. normalized-overlap / transition-probability preservation;
3. projective action on operational rays/classes;
4. continuous one-parameter reversible inheritance family;
5. generator closure.
```

Controls:

```text
wigner_like_symmetry_route:
  reaches the transition-preserving projective symmetry route, but lacks
  continuity and generator closure.

continuity_without_generator:
  lacks a closed generator theorem.

finite_unitary_gates_only:
  finite gates are not a general dynamics theorem.

imported_unitary_dynamics:
  IMPORTED_HIT because it assumes unitary_evolution_assumed.
```

### 174.252. Meaning Of The Dynamics Attempt

The dynamics wall did not disappear.

It split into five sharper theorem obligations:

```text
dcl_automorphism_dynamics_theorem
overlap_preservation_dynamics_theorem
projective_action_theorem
continuous_inheritance_family_theorem
generator_closure_theorem
```

If those are proved, the route gives a non-imported dynamics theorem:

```text
D_cl-preserving reversible inheritance
-> transition-preserving projective symmetry
-> continuous generator-compatible dynamics.
```

If any fails, unitary/generator dynamics remains blocked.

This is progress because:

```text
unitary dynamics is not inserted;
the exact missing assumptions are explicit;
the direct unitary import is rejected by executable control.
```

### 174.253. Updated One-Pass Full-QM Attempt After Dynamics Pass

After the dynamics pass:

```text
full_qm_proof_attempt = CONDITIONAL_ROUTE_ADVANCED
pass = 1
conditional = 5
open = 2
failed = 0
```

Conditional:

```text
finite_route_residual_closure
fpd_projective_derivation
universal_representation_theorem
universal_born_readout_theorem
unitary_dynamics_theorem
```

Still open:

```text
general_composite_theorem
physical_phase_scale_boundary
```

This still does not prove QM.

But the pass made measurable progress:

```text
unitary_dynamics_theorem moved from OPEN to CONDITIONAL.
```

The next full-proof pass should attack:

```text
general_composite_theorem
```

### 174.254. General Composite Theorem Attempt

The next pass attacked:

```text
general_composite_theorem
```

Evaluator:

```text
scripts/evaluate_general_composite_attempt.py
```

It tests whether the finite product/tomography screens can be lifted to
arbitrary finite and projective-limit composites without importing the Hilbert
tensor product.

Routes tested:

```text
finite_qubit_product_screen;
monoidal_without_entanglement;
finite_entanglement_without_limits;
general_projective_composite_route;
imported_tensor_product.
```

Result:

```text
route = general_projective_composite_route
verdict = CONDITIONAL_COMPOSITE_ROUTE
passed = 9/9
imports = none
```

The conditional route requires:

```text
1. finite tensor/product multiplicativity;
2. product-context exhaustion;
3. local tomography;
4. no hidden joint-only invariants;
5. monoidal associativity/unit/symmetry coherence;
6. entanglement closure inside the same finite route contract;
7. projective-limit consistency.
```

Controls:

```text
finite_qubit_product_screen:
  does not establish arbitrary composites.

monoidal_without_entanglement:
  lacks entanglement and projective-limit closure.

finite_entanglement_without_limits:
  lacks projective-limit consistency.

imported_tensor_product:
  IMPORTED_HIT because it assumes hilbert_tensor_product_assumed.
```

### 174.255. Physical Phase-Scale Boundary Attempt

The same pass also attacked:

```text
physical_phase_scale_boundary
```

Evaluator:

```text
scripts/evaluate_phase_scale_boundary_attempt.py
```

It tests whether the mathematical QM route can connect to physical phase scale
without pretending to derive `hbar_I`.

Routes tested:

```text
mathematical_qm_only;
calibrated_phase_scale_boundary;
first_principles_action_scale_route;
imported_physical_hbar.
```

Result:

```text
route = calibrated_phase_scale_boundary
verdict = CONDITIONAL_SCALE_BOUNDARY
passed = 8/8
imports = none
```

The boundary route requires:

```text
1. scale-free mathematical QM route;
2. explicit calibrated_hbar_I anchor;
3. no first-principles hbar_I claim;
4. phase/action dimension consistency;
5. empirical our-universe anchor bridge.
```

Rejected:

```text
first_principles_action_scale_route:
  fails because first-principles hbar_I remains outside the accepted proof
  boundary.

imported_physical_hbar:
  IMPORTED_HIT because it treats hbar as derived/imported.
```

### 174.256. Full-QM Route Status After Composite And Scale Pass

After these two attempts:

```text
full_qm_proof_attempt = CONDITIONAL_FULL_QM_ROUTE
pass = 1
conditional = 7
open = 0
failed = 0
```

This is the first pass where every top-level full-QM cell has a route:

```text
finite_route_gate:
  PASS

finite_route_residual_closure:
  CONDITIONAL

fpd_projective_derivation:
  CONDITIONAL

universal_representation_theorem:
  CONDITIONAL

universal_born_readout_theorem:
  CONDITIONAL

unitary_dynamics_theorem:
  CONDITIONAL

general_composite_theorem:
  CONDITIONAL

physical_phase_scale_boundary:
  CONDITIONAL
```

This is not:

```text
FULL_QM_PROVED
```

because each conditional cell still requires theorem artifacts.

It is:

```text
CONDITIONAL_FULL_QM_ROUTE
```

Meaning:

```text
No top-level full-QM route cell is currently open.
No top-level full-QM route cell currently fails.
The remaining work is to prove the named conditional obligations, not to find
an unknown missing top-level bridge.
```

### 174.257. Exact Remaining Proof Burden

The conditional full-QM route now depends on these theorem clusters:

```text
closure:
  finite_projection_determinacy
  projective_consistency
  NUSD
  conservative_projective_gluing

representation:
  spectral_decomposition
  rich_D_cl_reversible_symmetry

Born/readout:
  context_normalization
  exclusivity_additivity
  coarse_graining_consistency
  operational_equivalence_probability

dynamics:
  D_cl_automorphism_dynamics
  overlap_preservation_dynamics
  projective_action
  continuous_inheritance_family
  generator_closure

composites:
  monoidal_associativity
  entanglement_closure
  projective_limit_consistency

physical scale:
  calibrated_hbar_I boundary
  or a future independent action-scale theorem
```

The next phase should therefore not search for another top-level QM bridge.
It should convert these conditional obligations into theorem cards and
machine-checkable proof artifacts.

### 174.258. Full QM Proof Closure Attempt

This pass tries the strongest honest upgrade available now:

```text
CONDITIONAL_FULL_QM_ROUTE
=> FULL_QM_PROVED
```

The upgrade rule is deliberately strict:

```text
no machine-checkable proof artifact
=> no formal proof upgrade
```

The current route aggregator reports:

```text
full_qm_proof_attempt = CONDITIONAL_FULL_QM_ROUTE
pass = 1
conditional = 7
open = 0
failed = 0
```

This is substantial. It means the top-level route has no remaining open cells,
but all seven non-finite cells are conditional theorem routes.

The closure gate expands those conditions into 21 proof obligations:

```text
finite_projection_determinacy
projective_consistency
nonunital_stable_distinguishability
conservative_projective_gluing
spectral_decomposition
rich_d_cl_reversible_symmetry
context_normalization
exclusivity_additivity
coarse_graining_consistency
operational_equivalence_probability
d_cl_automorphism_dynamics
overlap_preservation_dynamics
projective_action
continuous_inheritance_family
generator_closure
product_context_exhaustion
local_tomography
monoidal_associativity
entanglement_closure
projective_limit_consistency
physical_phase_scale_boundary
```

Executable result:

```text
full_qm_proof_closure = PROOF_ARTIFACTS_MISSING
route_status = CONDITIONAL_FULL_QM_ROUTE
proved = 0
missing_artifacts = 21
incomplete_artifacts = 0
imported_artifacts = 0
```

Therefore the one-pass full-proof attempt did not prove QM.

It did close a different and useful question:

```text
The remaining blocker is no longer an unspecified top-level route gap.
The blocker is a finite list of missing proof artifacts for the conditional
theorem obligations.
```

The next proof phase must produce artifacts of this kind:

```text
proof_artifact:
  system: Lean4 or another declared checker
  file: repository path
  theorem: checker-visible theorem name
  check_command: reproducible local command
  verified: true
```

Forbidden closure moves:

```text
declare the 21 obligations as axioms
assume Hilbert space to prove Hilbert selection
assume Born probabilities to prove Born readout
assume unitary dynamics to prove reversible inheritance
assume tensor products to prove composite structure
derive hbar_I by renaming a calibrated quantum scale
```

Current honest status:

```text
QM is not proved.
The conditional full-QM route is closed at the top level.
The formal closure wall is now exactly the 21 proof-artifact obligations.
```

### 174.259. Closure Pass With Proof-Ledger Grounding

The next one-pass closure attempt first repaired the lower proof-verification
baseline. The generated Lean artifact had fallen out of sync with the manifest
after the latest finite-gate registry changes.

Repair command:

```bash
python3 scripts/sync_formal_proof_ledger.py --write
```

After regeneration, the proof runner passes:

```text
python3 scripts/sync_formal_proof_ledger.py --check  -> ok
lake env lean Proofs/IDTCore.lean                    -> ok
python3 -m theory_verifier --json ...                -> ok
```

This does not prove QM. It restores the trust boundary needed before any QM
proof artifact can be accepted.

The closure gate was then tightened so it reads the existing
`formal_proof_ledger_audit` proof cards from the manifest. A closure artifact
for a QM obligation must now be registered through the repository proof-ledger,
not through an ad hoc local list.

Accepted claim refs are:

```text
full_qm_proof_closure.<obligation_id>
<obligation_id>
```

The grounded result remains:

```text
full_qm_proof_closure = PROOF_ARTIFACTS_MISSING
route_status = CONDITIONAL_FULL_QM_ROUTE
proved = 0
missing_artifacts = 21
incomplete_artifacts = 0
imported_artifacts = 0
```

Therefore this pass still does not close QM.

What it closes:

```text
1. proof-ledger baseline restored;
2. closure gate is now connected to the real manifest proof-ledger;
3. missing artifacts are verified against the repository ledger, not guessed;
4. the next valid upgrade path is explicit.
```

What remains:

```text
All 21 closure obligations still require real machine-checkable proof cards.
```

### 174.260. Monoidal Associativity Draft Artifact

Low-level mechanical artifact:

```text
obligation = monoidal_associativity
artifact = Proofs/QMClosure/MonoidalAssociativityDraft.lean
checker = lake env lean Proofs/QMClosure/MonoidalAssociativityDraft.lean
status = conditional scaffold, not formal closure
```

The artifact proves a narrow theorem:

```text
If a finite context product is encoded as list append, then the product
operation is associative.
```

This is machine-checkable, but it is not yet a proof of the full IDT composite
obligation. The missing bridge is:

```text
admissible IDT context products
=> finite list-append encoding up to operational equivalence
```

Proof-card draft:

```text
id: monoidal_associativity_finite_context_product_draft
claim_refs:
  - full_qm_proof_closure.monoidal_associativity
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/MonoidalAssociativityDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/MonoidalAssociativityDraft.lean
statement: >
  Finite context products encoded as list append are associative.
open_gaps:
  - prove admissible IDT context products reduce to this finite encoding
  - prove quotient/coherence under operational equivalence
forbidden_upgrades:
  - does_not_prove_full_QM_I
  - does_not_assume_hilbert_tensor_product
  - does_not_upgrade_monoidal_associativity_to_formal_proof
```

Status:

```text
conditional
```

### 174.261. Projective Limit Consistency Scaffold Artifact

Low-level mechanical artifact:

```text
obligation:
  - projective_limit_consistency
artifact = Proofs/QMClosure/ProjectiveLimitScaffoldDraft.lean
checker = lake env lean Proofs/QMClosure/ProjectiveLimitScaffoldDraft.lean
status = conditional scaffold, not formal closure
```

The artifact proves a narrow tower-compatibility lemma:

```text
if a finite tower is pairwise compatible by an explicit predicate, then it
satisfies the encoded projective-limit consistency predicate.
```

Missing bridge:

```text
IDT finite/projective route tower
=> FiniteTower encoding

IDT admissible transition/refinement
=> transition map in the scaffold

IDT consistency under projective limits
=> PairwiseCompatible, not assumed by hand
```

Proof-card draft:

```text
id: projective_limit_consistency_scaffold_draft
claim_refs:
  - full_qm_proof_closure.projective_limit_consistency
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/ProjectiveLimitScaffoldDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/ProjectiveLimitScaffoldDraft.lean
statement: >
  Explicit pairwise compatibility of an encoded finite tower implies the
  encoded projective-limit consistency predicate.
open_gaps:
  - derive the finite tower from IDT route/refinement structure
  - derive pairwise compatibility from IDT projective consistency
  - extend from finite scaffold to the required projective-limit boundary
forbidden_upgrades:
  - does_not_assume_infinite_dimensional_hilbert_space
  - does_not_assume_c_star_algebra
  - does_not_upgrade_projective_limit_consistency_to_formal_proof
```

Status:

```text
conditional
```

### 174.262. Phase Scale Boundary Scaffold Artifact

Low-level mechanical artifact:

```text
obligation:
  - physical_phase_scale_boundary
artifact = Proofs/QMClosure/BoundaryScaffoldsDraft.lean
checker = lake env lean Proofs/QMClosure/BoundaryScaffoldsDraft.lean
status = conditional boundary scaffold, not formal hbar derivation
```

The artifact proves a narrow negative-boundary fact:

```text
calibratedAnchor = true
firstPrinciplesDerivation = false
```

This is machine-checkable, but it deliberately does not derive `hbar_I`.

Missing bridge:

```text
IDT physical phase/action scale boundary
=> the ScaleBoundary encoding

calibrated_hbar_I public claim
=> calibratedAnchor = true

blocked first-principles hbar_I claim
=> firstPrinciplesDerivation = false
```

Proof-card draft:

```text
id: physical_phase_scale_boundary_scaffold_draft
claim_refs:
  - full_qm_proof_closure.physical_phase_scale_boundary
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/BoundaryScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/BoundaryScaffoldsDraft.lean
statement: >
  A calibrated-only boundary keeps calibrated action scale separate from a
  first-principles derivation claim.
open_gaps:
  - connect the public calibrated_hbar_I boundary to the Lean ScaleBoundary
  - keep first-principles hbar_I blocked until an independent action-scale
    theorem exists
forbidden_upgrades:
  - does_not_derive_hbar_I
  - does_not_use_planck_units_as_primitives
  - does_not_upgrade_phase_scale_boundary_to_formal_proof
```

Status:

```text
conditional
```

### 174.263. Composite / Local Tomography Scaffold Artifacts

Low-level mechanical artifact:

```text
obligations:
  - product_context_exhaustion
  - local_tomography
artifact = Proofs/QMClosure/CompositeScaffoldsDraft.lean
checker = lake env lean Proofs/QMClosure/CompositeScaffoldsDraft.lean
status = conditional scaffold, not formal closure
```

The artifact proves two narrow predicate/readout lemmas:

```text
if declared product readouts separate states, local tomography follows
equal states agree on all declared readouts
```

This is machine-checkable and does not assume a Hilbert tensor product.

Missing bridge:

```text
IDT product-context exhaustion
=> a declared product readout family covering all stable composite facts

IDT product readout separation
=> SeparatesStates for the encoded product readout list

IDT composite state identity
=> equality in the scaffold state type
```

Proof-card draft:

```text
id: local_tomography_scaffold_draft
claim_refs:
  - full_qm_proof_closure.product_context_exhaustion
  - full_qm_proof_closure.local_tomography
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/CompositeScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/CompositeScaffoldsDraft.lean
statement: >
  A declared product readout family that separates states yields local
  tomography in a predicate-readout encoding.
open_gaps:
  - derive product-context exhaustion from IDT composite rules
  - derive product readout separation from stable facticization witnesses
  - connect scaffold equality to operational state identity
forbidden_upgrades:
  - does_not_assume_hilbert_tensor_product
  - does_not_assume_trace_rule
  - does_not_upgrade_composite_obligations_to_formal_proof
```

Status:

```text
conditional
```

### 174.264. Projection / Conservative Gluing Scaffold Artifacts

Low-level mechanical artifact:

```text
obligations:
  - finite_projection_determinacy
  - projective_consistency
  - conservative_projective_gluing
artifact = Proofs/QMClosure/ProjectionScaffoldsDraft.lean
checker = lake env lean Proofs/QMClosure/ProjectionScaffoldsDraft.lean
status = conditional scaffold, not formal closure
```

The artifact proves two narrow endomap lemmas:

```text
identity endomap is idempotent
composition of commuting idempotent endomaps is idempotent
commuting encoded projections have order-independent composition
```

This is machine-checkable and does not assume Hilbert projectors.

Missing bridge:

```text
IDT finite projection determinacy
=> idempotent endomap on a finite fact/readout carrier

IDT conservative projective gluing
=> composition of commuting idempotent endomaps

IDT projective consistency
=> commutation/coherence conditions rather than hidden Hilbert projectors
```

Proof-card draft:

```text
id: projection_idempotence_scaffold_draft
claim_refs:
  - full_qm_proof_closure.finite_projection_determinacy
  - full_qm_proof_closure.projective_consistency
  - full_qm_proof_closure.conservative_projective_gluing
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/ProjectionScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/ProjectionScaffoldsDraft.lean
statement: >
  Identity is idempotent, and composition of commuting idempotent endomaps is
  idempotent.
open_gaps:
  - derive finite projection endomaps from IDT facticization
  - derive commutation/coherence from IDT conservative gluing
  - connect the scaffold to projective consistency without Hilbert projectors
forbidden_upgrades:
  - does_not_assume_hilbert_projectors
  - does_not_assume_born_rule
  - does_not_upgrade_projection_obligations_to_formal_proof
```

Status:

```text
conditional
```

### 174.265. Reversible Inheritance Scaffold Artifacts

Low-level mechanical artifact:

```text
obligations:
  - d_cl_automorphism_dynamics
  - overlap_preservation_dynamics
  - projective_action
artifact = Proofs/QMClosure/InheritanceScaffoldsDraft.lean
checker = lake env lean Proofs/QMClosure/InheritanceScaffoldsDraft.lean
status = conditional scaffold, not formal closure
```

The artifact proves narrow preservation lemmas:

```text
identity preserves an arbitrary distinguishability relation
composition of distinguishability-preserving maps preserves distinguishability
identity preserves an arbitrary overlap function
composition of overlap-preserving maps preserves overlap
identity projective action is extensionally equal to the original fact
```

This is machine-checkable and carrier-neutral. It does not assume Hilbert
space, unitary evolution, Wigner's theorem, Stone's theorem, or a Hamiltonian.

Missing bridge:

```text
IDT reversible inheritance
=> maps satisfying these preservation predicates

IDT normalized overlap
=> the abstract overlap function used in the scaffold

IDT projective facts
=> the predicate-level ProjectiveFact encoding

continuous inheritance
=> a continuity structure, absent from this finite scaffold

generator closure
=> a generator algebra, absent from this finite scaffold
```

Proof-card draft:

```text
id: reversible_inheritance_preservation_scaffold_draft
claim_refs:
  - full_qm_proof_closure.d_cl_automorphism_dynamics
  - full_qm_proof_closure.overlap_preservation_dynamics
  - full_qm_proof_closure.projective_action
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/InheritanceScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/InheritanceScaffoldsDraft.lean
statement: >
  Abstract inheritance maps that preserve supplied distinguishability and
  overlap predicates remain closed under identity and composition, and identity
  acts trivially on predicate-level projective facts.
open_gaps:
  - derive preservation predicates from IDT reversible inheritance
  - derive projective fact encoding from IDT facticization
  - formalize continuity and generator closure without importing unitary groups
forbidden_upgrades:
  - does_not_prove_unitary_dynamics
  - does_not_assume_wigner_theorem
  - does_not_assume_hilbert_space
  - does_not_upgrade_dynamics_obligations_to_formal_proof
```

Status:

```text
conditional
```

Reason:

```text
The Lean theorem is real, but it checks only the finite encoding scaffold.
It cannot be registered as a formal proof for the closure obligation until the
IDT admissibility-to-encoding bridge is also proved.
```

### 174.266. Born Readout Scaffold Artifacts

Low-level mechanical artifact:

```text
obligations:
  - context_normalization
  - exclusivity_additivity
  - coarse_graining_consistency
  - operational_equivalence_probability
artifact = Proofs/QMClosure/ReadoutScaffoldsDraft.lean
checker = lake env lean Proofs/QMClosure/ReadoutScaffoldsDraft.lean
status = conditional scaffold, not formal closure
```

The artifact proves four narrow finite-weight lemmas:

```text
contextTotal(readout) = readout.sum
contextTotal(left ++ right) = contextTotal(left) + contextTotal(right)
if coarse-graining preserves total by assumption, totals are equal
if two weights are operationally equivalent by equality, they are equal
```

These are machine-checkable, but they are not a Born-rule proof.

Missing bridge:

```text
IDT admissible readout context
=> finite weight table with stable total

IDT facticized exclusivity
=> append-like disjoint finite composition

IDT admissible coarse-graining
=> total-preserving map, not assumed by hand

IDT operational equivalence
=> equality of the finite readout weight, not merely a declared equality
```

Proof-card draft:

```text
id: finite_readout_scaffold_draft
claim_refs:
  - full_qm_proof_closure.context_normalization
  - full_qm_proof_closure.exclusivity_additivity
  - full_qm_proof_closure.coarse_graining_consistency
  - full_qm_proof_closure.operational_equivalence_probability
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/ReadoutScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/ReadoutScaffoldsDraft.lean
statement: >
  Finite natural-weight readout tables satisfy normalization-by-total,
  append additivity, assumption-explicit coarse-graining stability, and
  equality-explicit operational equivalence.
open_gaps:
  - derive finite readout weights from IDT facticization
  - derive disjoint append from IDT exclusivity
  - derive total-preserving coarse-graining from IDT admissibility
  - derive weight equality from IDT operational equivalence
forbidden_upgrades:
  - does_not_prove_Born_rule
  - does_not_assume_probability_axioms
  - does_not_assume_hilbert_space
  - does_not_upgrade_readout_obligations_to_formal_proof
```

Status:

```text
conditional
```
### 174.267. Strong Audit Of Low-Level Scaffolds

Strong-model audit result:

```text
No scaffold added in 174.260-174.266 is a formal proof of a full-QM closure
obligation.
```

They are still useful if treated correctly:

```text
Lean-checkable encoding sanity checks
proof-card drafts
future bridge theorem targets
anti-overclaim guards
```

They are not:

```text
formal_proof
FULL_QM_PROVED
Born-rule proof
Hilbert-carrier proof
unitary-dynamics proof
tensor-composition proof
```

Artifact classification:

```text
MonoidalAssociativityDraft:
  safe scaffold;
  real Lean theorem for list-append encoding;
  missing IDT context-product-to-list bridge.

ReadoutScaffoldsDraft:
  safe but very weak scaffold;
  checks finite natural-weight algebra;
  missing derivation of weights, disjointness, coarse-graining preservation,
  and operational-equivalence equality from IDT facticization.

InheritanceScaffoldsDraft:
  safe carrier-neutral scaffold;
  checks preservation predicates under identity/composition;
  missing derivation that reversible inheritance supplies those predicates;
  does not touch continuity or generator closure.

ProjectionScaffoldsDraft:
  safe scaffold;
  checks idempotent/commuting endomap algebra;
  missing derivation of projective endomaps and commutation from IDT
  projective consistency.

CompositeScaffoldsDraft:
  safe but mostly definitional scaffold;
  local tomography follows from an explicit separation predicate;
  missing product-context exhaustion and readout separation proofs.

BoundaryScaffoldsDraft:
  safe negative-boundary scaffold;
  preserves calibrated-not-derived distinction;
  does not derive hbar_I.

ProjectiveLimitScaffoldDraft:
  safe but definitional scaffold;
  consistency follows from an explicit compatibility predicate;
  missing derivation of compatibility from IDT refinement/projective route.
```

Closure-gate update:

```text
proof_kind = proof_sketch
=> SKETCH_ARTIFACT
=> still not PROVED
```

This prevents a future proof-ledger draft from being misreported as a broken
formal artifact. It also prevents a sketch from reducing the formal proof
burden.

Current grounded closure status remains:

```text
full_qm_proof_closure = PROOF_ARTIFACTS_MISSING
route_status = CONDITIONAL_FULL_QM_ROUTE
proved = 0
missing_artifacts = 21
sketch_artifacts = 0
incomplete_artifacts = 0
imported_artifacts = 0
```

The `sketch_artifacts` count is currently zero because the scaffold drafts have
not been registered in the manifest proof-ledger. That is correct for now:
registration should wait until the project decides whether proof sketches
belong in the public manifest.

The actual strong-model blocker is:

```text
bridge theorems from IDT primitives to the Lean encodings.
```

Hard obligations that should not be attacked by low-level mechanical work:

```text
nonunital_stable_distinguishability
spectral_decomposition
rich_d_cl_reversible_symmetry
continuous_inheritance_family
generator_closure
entanglement_closure
```

Reason:

```text
Any shallow scaffold for these would likely smuggle in Hilbert, spectral,
unitary, continuity, generator, or tensor assumptions under new names.
```

Best next strong proof target:

```text
IDT admissible context product
=> list-append-like finite product encoding up to operational equivalence
```

If this bridge works, `monoidal_associativity` can move from scaffold to a real
conditional proof artifact without importing Hilbert tensor products.

If it fails, the composite route needs a deeper primitive for context-product
coherence.

### 174.268. Monoidal Bridge Theorem Draft

The monoidal associativity scaffold has been strengthened.

New Lean theorem:

```text
encoded_context_product_assoc_up_to_operational_equivalence
product_context_expr_assoc_up_to_flatten
```

Artifact:

```text
Proofs/QMClosure/MonoidalAssociativityDraft.lean
```

Statement shape:

```text
Given any context product with a finite encoding such that

  encode(product(a,b)) = encode(a) ++ encode(b),

then product is associative up to operational equivalence induced by the
encoding.
```

This is stronger than the original list-only scaffold:

```text
old:
  list append is associative

new:
  any append-compatible encoded context product is associative up to encoded
  operational equivalence
```

Current proof status:

```text
conditional_bridge_proof
```

What is proved:

```text
append-compatible finite encoding
=> monoidal associativity up to encoding equivalence

free finite context-product syntax
=> append-compatible finite flattening
=> associativity up to flattening equivalence
```

What remains unproved:

```text
IDT admissible context product
=> append-compatible finite encoding

IDT admissible context product
=> embedding into free finite context-product syntax or an equivalent quotient
```

This remaining bridge is the actual scientific/mathematical obligation. It
must be derived from IDT context/product rules, not from Hilbert tensor
products.

Updated proof-card draft:

```text
id: monoidal_associativity_encoded_context_product_bridge
claim_refs:
  - full_qm_proof_closure.monoidal_associativity
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/MonoidalAssociativityDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/MonoidalAssociativityDraft.lean
statement: >
  Any context product admitting an append-compatible finite encoding is
  associative up to operational equivalence induced by that encoding.
open_gaps:
  - prove IDT admissible context products admit append-compatible finite
    encodings
  - prove the encoding equivalence matches IDT operational equivalence
forbidden_upgrades:
  - does_not_assume_hilbert_tensor_product
  - does_not_assume_quantum_channel_composition
  - does_not_upgrade_monoidal_associativity_to_formal_proof
```

Interpretation:

```text
The obstruction has moved one level lower.
The algebraic associativity part is now checkable.
The remaining problem is deriving the finite product encoding from IDT
primitives.
```

Stronger localization after the syntax theorem:

```text
The algebraic monoidal part is no longer the blocker.
The blocker is an IDT embedding/coherence theorem:

  admissible_context_product
  -> ContextProductExpr-like finite syntax
  -> flattening equivalence matches operational equivalence.
```

This bridge is not present in the current manifest. Existing executable
objects cover finite Cartesian product-context exhaustion and local tomography
separation, but they do not yet prove that every admissible context product has
the required free-product syntax or quotient coherence.

### 174.269. Finite Context-Product Encoding Witness

Executable finite witness:

```text
script = scripts/evaluate_context_product_encoding_bridge.py
verdict = FINITE_CARTESIAN_ENCODING_WITNESS
gate = context_product_exhaustion_demo
passed = 2
failed = 0
```

The evaluator checks the finite product-context data already present in
`context_product_exhaustion_demo`.

For each candidate it verifies:

```text
declared product contexts = left_contexts x right_contexts
```

Result:

```text
exhausted_product_readout_composite:
  left = 2
  right = 2
  declared = 4
  expected = 4
  PASS

hidden_joint_invariant_composite:
  left = 2
  right = 2
  declared = 4
  expected = 4
  PASS
```

This proves only the finite encoding layer:

```text
finite Cartesian product-context table
=> pair/list encoding witness
```

It does not prove product-context exhaustion for stable invariants. The hidden
joint candidate still fails the invariant-exhaustion layer even though its
declared product-context table has a valid finite encoding.

Current monoidal route status:

```text
finite Cartesian product table
=> pair/list encoding witness
=> append-compatible syntax theorem
=> associativity up to encoding equivalence
```

Remaining universal gap:

```text
arbitrary IDT admissible context product
=> finite Cartesian product table or free-product syntax quotient
```

Therefore this is not `formal_proof` for `monoidal_associativity`, but it is a
real finite bridge witness for the current executable context-product gate.

### 174.270. Finite Readout Normalization Bridge Draft

The readout scaffold has been strengthened.

New Lean objects:

```text
StableFiniteReadout
NormalizedWeight
normalizedReadout
flattenReadoutBlocks
coarseGrainBlocks
```

New Lean theorems:

```text
stable_finite_readout_has_positive_denominator
stable_finite_readout_denominator_is_total
normalized_readout_length_matches
normalized_readout_common_denominator
coarse_grain_blocks_preserve_total
operational_equivalence_respecting_weight_function_preserves_weight
```

Artifact:

```text
Proofs/QMClosure/ReadoutScaffoldsDraft.lean
```

What is proved:

```text
finite natural weights + positive total
=> a normalized readout representation with common positive denominator

explicit finite block coarse-graining
=> total weight is preserved

event weight function respects operational equivalence
=> operationally equivalent events receive equal weights
```

This is stronger than the original readout scaffold because normalization is
now represented as a checked finite object rather than only the statement that
the total is a sum.

What is not proved:

```text
IDT facticization
=> finite natural weights

IDT admissible readout context
=> positive total

IDT admissible coarse-graining
=> the explicit block coarse-graining used here

IDT operational equivalence
=> a weight function that respects the equivalence relation

finite common-denominator weights
=> Born rule
```

Current proof status:

```text
conditional_bridge_proof
```

Updated proof-card draft:

```text
id: finite_readout_normalization_bridge
claim_refs:
  - full_qm_proof_closure.context_normalization
  - full_qm_proof_closure.coarse_graining_consistency
  - full_qm_proof_closure.operational_equivalence_probability
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/ReadoutScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/ReadoutScaffoldsDraft.lean
statement: >
  Finite nonnegative readout weights with positive total admit a common
  positive-denominator normalization representation, and explicit finite block
  coarse-graining preserves total weight. Any event-weight function that
  respects operational equivalence assigns equal weights to equivalent events.
open_gaps:
  - derive finite nonnegative weights from IDT facticization
  - derive positive total from admissible readout contexts
  - derive block coarse-graining from IDT admissible coarse-graining
  - derive equivalence-respecting weight functions from IDT operational
    equivalence
  - connect common-denominator normalization to the probability layer without
    assuming the Born rule
forbidden_upgrades:
  - does_not_prove_Born_rule
  - does_not_assume_probability_axioms
  - does_not_assume_hilbert_space
  - does_not_upgrade_readout_obligations_to_formal_proof
```

Interpretation:

```text
The finite arithmetic normalization/coarse-graining part is now checkable.
The remaining blocker is deriving the finite weight model from IDT
facticization and readout admissibility.
```

### 174.271. Conservative Projection Gluing Bridge Draft

The projection scaffold has been strengthened.

New Lean objects:

```text
FixedBy
```

New Lean theorems:

```text
commuting_idempotent_composition_fixed_by_left
commuting_idempotent_composition_fixed_by_right
jointly_fixed_value_survives_composition
```

Artifact:

```text
Proofs/QMClosure/ProjectionScaffoldsDraft.lean
```

What is proved:

```text
commuting idempotent endomaps
=> their composition is fixed by the left projection
=> their composition is fixed by the right projection
=> a value already fixed by both projections survives the composition
```

This strengthens the finite gluing scaffold:

```text
old:
  composition of commuting idempotents is idempotent

new:
  composition of commuting idempotents lands in the jointly fixed part and
  preserves already jointly fixed values
```

What is not proved:

```text
IDT projective restriction
=> idempotent endomap

IDT structure-preserving restriction
=> commuting endomaps

IDT conservative projective gluing
=> jointly fixed part semantics

NUSD
=> no unwitnessed stable distinction outside this projection semantics
```

Current proof status:

```text
conditional_bridge_proof
```

Updated proof-card draft:

```text
id: conservative_projection_gluing_bridge
claim_refs:
  - full_qm_proof_closure.projective_consistency
  - full_qm_proof_closure.conservative_projective_gluing
proof_kind: proof_sketch
backend: lean4
artifact_paths:
  - Proofs/QMClosure/ProjectionScaffoldsDraft.lean
checker_commands:
  - lake env lean Proofs/QMClosure/ProjectionScaffoldsDraft.lean
statement: >
  Commuting idempotent endomaps compose conservatively: the composite is fixed
  by both projections and preserves values already fixed by both.
open_gaps:
  - derive IDT projective restrictions as idempotent endomaps
  - derive commutation from IDT projective consistency
  - derive jointly fixed semantics from IDT conservative gluing
  - derive NUSD rather than assuming it
forbidden_upgrades:
  - does_not_assume_hilbert_projectors
  - does_not_assume_complex_hilbert_completion
  - does_not_upgrade_projective_obligations_to_formal_proof
```

Interpretation:

```text
The endomap algebra for conservative gluing is now checkable.
The remaining blocker is deriving this endomap semantics from IDT projection
and NUSD rules.
```

### 174.272. QM Hard-Wall Probe

Executable probe:

```text
script = scripts/evaluate_qm_hard_wall_probe.py
verdict = OPEN_STRUCTURAL_WALL
fatal_now = false
route_status = CONDITIONAL_FULL_QM_ROUTE
closure_status = PROOF_ARTIFACTS_MISSING
proved = 0
scaffold_present = 15
proof_artifact_missing = 0
structural_walls = 6
import_walls = 0
```

Interpretation:

```text
No fatal contradiction or hidden imported proof artifact is detected in the
current route.

But the route is not wall-free. It still contains six structural open walls:

1. nonunital_stable_distinguishability
2. spectral_decomposition
3. rich_d_cl_reversible_symmetry
4. continuous_inheritance_family
5. generator_closure
6. entanglement_closure
```

The remaining 15 obligations have finite bridge scaffolds or executable route
witnesses, but none is a registered machine-checkable proof artifact for full
QM closure.

This gives a precise answer to the wall question:

```text
We are not currently blocked by a detected inconsistency or hidden Hilbert/Born
import.

We are blocked by structural theorem obligations that may require a stronger
primitive base or explicit boundary assumptions.
```

The decisive next wall is therefore not another finite experiment gate. It is
one of:

```text
NUSD from context-first facticization;
spectrality/rich reversible symmetry from D_cl;
continuity/generator closure from finite refinement limits;
entanglement closure from product-context exhaustion plus no hidden joint-only
invariants.
```

Forbidden upgrade:

```text
does_not_prove_full_QM_I
does_not_prove_absence_of_future_wall
does_not_treat_bridge_scaffold_as_formal_proof
does_not_hide_QM_imports
```

### 174.273. Multi-Wall Structural Pattern Probe

The six structural walls were tested together rather than one at a time.

Executable probe:

```text
script = scripts/evaluate_qm_structural_wall_patterns.py
verdict = PATTERN_CANDIDATE_FOUND
hard_wall_verdict = OPEN_STRUCTURAL_WALL
structural_walls = 6
covered = 6
uncovered = 0
axis_count = 5
candidate = context_generated_stable_closure
status = candidate_unifying_principle_not_proof
rejected_imports = 0
```

The structural walls are:

```text
nonunital_stable_distinguishability
spectral_decomposition
rich_d_cl_reversible_symmetry
continuous_inheritance_family
generator_closure
entanglement_closure
```

They are not independent. They share a common missing shape:

```text
stable facts, stable distinctions, reversible updates, refinement limits, and
composite facts must be generated by finite facticizable context witnesses,
with no extra carrier structure imported after the fact.
```

Candidate unifying principle:

```text
context_generated_stable_closure
```

Candidate reading:

```text
Any physically stable distinction, invariant, transformation family, or
composite fact must be generated inside finite context/readout/refinement
routes. A structure that is stable but has no admissible generating route is
not a hidden physical degree of freedom; it is either outside physical scope or
marks a failed primitive base.
```

Pattern axes:

```text
finite_facticizable_witness_closure:
  covers NUSD and entanglement hidden-invariant closure

exposed_context_geometry:
  covers spectral decomposition and part of rich D_cl symmetry

reversible_context_symmetry:
  covers rich D_cl symmetry and continuous inheritance

coherent_refinement_flow:
  covers continuous inheritance and generator closure

generated_composite_closure:
  covers entanglement closure and NUSD/no-hidden-invariant closure
```

This suggests the next strong move is not to invent six unrelated principles.
The next move is to formalize one stronger primitive/axiom candidate:

```text
context_generated_stable_closure
```

and then test whether it derives:

```text
1. NUSD;
2. exposed-context spectral decomposition;
3. rich reversible D_cl symmetry;
4. continuous refinement families;
5. generator-compatible closure;
6. entanglement/composite closure.
```

Negative controls must reject:

```text
hidden Hilbert carrier import
Born-rule import
unitary-group import
Hilbert tensor-product import
Stone/generator import
spectral-theorem import
```

Interpretation:

```text
The current wall is smaller than six independent theorem gaps.
It is one candidate primitive-base gap:

  context-generated stability.

If this candidate fails, the route probably needs a genuinely different base.
If it passes, it can turn several QM walls into one proof program.
```

Forbidden upgrade:

```text
does_not_prove_full_QM_I
does_not_derive_Hilbert_space
does_not_derive_Born_rule
does_not_derive_unitary_dynamics
does_not_treat_candidate_unifying_principle_as_formal_proof
```

### 174.274. Context-Generated Stable Closure Contract

The candidate principle was promoted from a pattern name to an executable
contract probe.

Executable probe:

```text
script = scripts/evaluate_context_generated_stable_closure.py
verdict = CONDITIONAL_MULTI_WALL_CLOSURE_CANDIDATE
principle = context_generated_stable_closure
status = candidate_principle_not_formal_proof
pattern = PATTERN_CANDIDATE_FOUND
targets = 6
conditional = 6
missing = 0
target_import_rejections = 0
controls = 6
rejected_controls = 6
survived_controls = 0
```

Candidate clauses:

```text
finite_generation:
  Stable physical structures must have finite context/readout/refinement
  generation routes or be outside physical scope.

facticizable_separation:
  A stable distinction that can affect a readout must be separated by an
  admissible finite facticizable witness.

exposed_context_decomposition:
  Finite generated stable states decompose into mutually exclusive exposed
  context records when the context family supplies a complete facticizable
  partition.

reversible_route_closure:
  Admissible reversible inheritance acts are route automorphisms preserving
  D_cl, normalized overlap, and exposed context records.

coherent_refinement_flow:
  Compatible finite refinement families add no new stable directions and admit
  generator-compatible bookkeeping without importing a continuum generator.

composite_route_generation:
  Composite facts, including non-product facts, must be generated inside
  admissible product/context refinement routes rather than by hidden joint-only
  carrier degrees.

import_boundary:
  The candidate principle may not cite Hilbert, Born, unitary, tensor, Stone,
  or spectral theorem imports.
```

Conditional target coverage:

```text
nonunital_stable_distinguishability:
  covered if readout-relevant stable distinctions require finite facticizable
  witnesses.

spectral_decomposition:
  covered only as exposed-context decomposition, not as an imported spectral
  theorem.

rich_d_cl_reversible_symmetry:
  covered if reversible inheritance acts close on exposed-context D_cl routes.

continuous_inheritance_family:
  covered only as coherent finite-refinement flow, not as a supplied Lie group.

generator_closure:
  covered only as bookkeeping of coherent refinement, not as Hamiltonian import.

entanglement_closure:
  covered only for non-product facts generated inside composite context routes.
```

Negative controls:

```text
hidden_hilbert_carrier_import: rejected
born_rule_import: rejected
unitary_group_import: rejected
hilbert_tensor_product_import: rejected
stone_generator_import: rejected
spectral_theorem_import: rejected
```

Current interpretation:

```text
This is the first broad candidate that conditionally covers all six structural
QM walls while rejecting the obvious target imports.

It still does not prove QM.
It does not prove the clauses from primitives.
It does not prove Hilbert, Born, unitary dynamics, tensor composition, or hbar.

The next step is to turn these seven clauses into a theorem-card/proof-route
draft and test each clause against IDT primitives before any status upgrade.
```

Forbidden upgrade:

```text
does_not_prove_full_QM_I
does_not_derive_Hilbert_space
does_not_derive_Born_rule
does_not_derive_unitary_dynamics
does_not_derive_tensor_composition
does_not_treat_candidate_principle_as_formal_proof
```

### 174.275. Context-Generated Stable Closure Route Draft

The candidate principle now has a machine-readable theorem-card/proof-route
draft.

Artifact:

```text
Proofs/QMClosure/ContextGeneratedStableClosureRouteDraft.json
```

Validator:

```text
script = scripts/evaluate_context_generated_stable_closure_route_draft.py
verdict = ROUTE_DRAFT_VALIDATED
contract = CONDITIONAL_MULTI_WALL_CLOSURE_CANDIDATE
checks_passed = 16
checks_failed = 0
```

The draft is intentionally not registered as a manifest theorem card yet. It
has:

```text
artifact_status = route_draft_not_formal_proof
theorem_card.proof_status = open
proof_route.expected_route_status = open
all clauses.status = candidate_clause
```

The validator checks:

```text
1. the theorem-card id and proof route id match;
2. proof_status stays open;
3. dependency refs are grounded in the repository;
4. forbidden claims include all current no-upgrade boundaries;
5. known failures keep the primitive-proof gap explicit;
6. all seven candidate clauses are present;
7. all clause primitive-grounding refs match the executable contract;
8. all six structural walls are listed as route targets;
9. all six negative controls are listed;
10. the live contract probe remains
    CONDITIONAL_MULTI_WALL_CLOSURE_CANDIDATE.
```

This is stronger than a prose note because the draft must stay synchronized
with the executable contract probe. It is still weaker than a theorem proof:

```text
the clauses are not proved from primitives;
no Lean/formal artifact proves the route;
full_qm_proof_closure remains PROOF_ARTIFACTS_MISSING.
```

Current broad status:

```text
The six structural walls have one coherent candidate closure principle and a
validated proof-route draft.

The next blocker is clause derivation from the primitive base, not experiment
coverage and not manifest bookkeeping.
```

Forbidden upgrade:

```text
does_not_prove_full_QM_I
does_not_derive_Hilbert_space
does_not_derive_Born_rule
does_not_derive_unitary_dynamics
does_not_derive_tensor_composition
does_not_derive_hbar_I
does_not_treat_route_draft_as_formal_proof
```

### 174.276. Hilbert/Born/Unitary/Tensor Inevitability Route

The four target QM structures were tested together:

```text
Hilbert-like representation
Born-like readout
Unitary-like reversible dynamics
Tensor-like composite structure
```

Machine-readable route draft:

```text
Proofs/QMClosure/QMInevitabilityRouteDraft.json
```

Executable validator:

```text
script = scripts/evaluate_qm_inevitability_route.py
verdict = CONDITIONAL_INEVITABILITY_ROUTE_VALIDATED
proof_status = OPEN_PRIMITIVE_CLAUSE_PROOFS_MISSING
cgsc_route_draft = ROUTE_DRAFT_VALIDATED
full_qm_closure = PROOF_ARTIFACTS_MISSING
targets = 4
conditional_targets = 4
open_targets = 0
failed_targets = 0
imported_targets = 0
missing_clause_proofs = 20
missing_proof_artifacts = 20
draft_checks_failed = 0
```

Per-target status:

```text
hilbert_representation:
  route = CONDITIONAL_REPRESENTATION_ROUTE
  missing_clause_proofs = 6
  missing_artifacts = 6

born_readout:
  route = CONDITIONAL_BORN_ROUTE
  missing_clause_proofs = 5
  missing_artifacts = 4

unitary_dynamics:
  route = CONDITIONAL_DYNAMICS_ROUTE
  missing_clause_proofs = 4
  missing_artifacts = 5

tensor_composition:
  route = CONDITIONAL_COMPOSITE_ROUTE
  missing_clause_proofs = 5
  missing_artifacts = 5
```

Interpretation:

```text
All four target structures now have validated conditional non-imported routes.
No target route imports Hilbert, Born, unitary dynamics, or tensor composition.

But inevitability is not proved.
The route is open because the CGSC clauses are candidate clauses, not formal
theorems from primitives, and the full-QM proof obligations are not registered
as machine-checkable proof artifacts.
```

This is the current exact blocker:

```text
primitives
=> CGSC clauses
=> target proof obligations
=> Hilbert/Born/unitary/tensor
```

The last two arrows are now organized as a validated conditional route. The
first arrow is still the real proof problem.

Next broad step:

```text
derive or refute the seven CGSC clauses from the primitive base as one package.
```

Forbidden upgrade:

```text
does_not_prove_full_QM_I
does_not_derive_Hilbert_space_as_formal_proof
does_not_derive_Born_rule_as_formal_proof
does_not_derive_unitary_dynamics_as_formal_proof
does_not_derive_tensor_composition_as_formal_proof
does_not_derive_hbar_I
does_not_treat_conditional_inevitability_route_as_proof
```

### 174.277. CGSC Primitive-Derivation Broad Probe

The seven CGSC clauses were tested together against the current primitive
base and the context-first B0 candidate.

Machine-readable route draft:

```text
Proofs/QMClosure/CGSCPrimitiveDerivationRouteDraft.json
```

Executable validator:

```text
script = scripts/evaluate_cgsc_primitive_derivation.py
verdict = PRIMITIVE_DERIVATION_NOT_CLOSED
cgsc_route_draft = ROUTE_DRAFT_VALIDATED
clauses = 7
formal = 0
candidate_supported = 2
extension_required = 4
boundary_grounded = 1
import_rejected = 0
missing_base_extensions = 6
route_draft_checks_failed = 0
```

Clause status:

```text
B0_CANDIDATE_SUPPORTED:
  finite_generation
  facticizable_separation

B0_EXTENSION_REQUIRED:
  exposed_context_decomposition
  reversible_route_closure
  coherent_refinement_flow
  composite_route_generation

BOUNDARY_GROUNDED:
  import_boundary
```

Missing base extensions:

```text
complete_exposed_context_partition
reversible_context_automorphism_closure
coherent_refinement_compactness
generator_bookkeeping_without_stone
product_context_generation_closure
no_hidden_joint_only_generation
```

The broad route now reads:

```text
current v6 core:
  useful executable scaffold, not enough for CGSC proof

B0 context-first candidate:
  supports finite generation and facticizable separation as candidate clauses
  grounds import boundary
  lacks four closure mechanisms needed by the remaining clauses

CGSC:
  not derived from primitives yet
```

This updates the QM inevitability route:

```text
qm_inevitability_route = CONDITIONAL_INEVITABILITY_ROUTE_VALIDATED
cgsc_primitive_derivation = PRIMITIVE_DERIVATION_NOT_CLOSED
missing_base_extensions = 6
```

Interpretation:

```text
The next blocker is no longer vague "prove CGSC".
It is the six missing base extensions above.

If those extensions can be derived from B0, CGSC may become a theorem route.
If they must be added as independent principles, the primitive base has to be
expanded and the theory must admit that B0 alone was too weak.
```

Forbidden upgrade:

```text
does_not_prove_CGSC
does_not_prove_full_QM_I
does_not_derive_Hilbert_space
does_not_derive_Born_rule
does_not_derive_unitary_dynamics
does_not_derive_tensor_composition
does_not_treat_B0_candidate_support_as_formal_proof
```

### 174.278. CGSC Extension Wall Probe

The six missing base extensions were tested as one broad front rather than as
six isolated micro-obligations.

Machine-readable wall-probe draft:

```text
Proofs/QMClosure/CGSCExtensionWallProbeDraft.json
```

Executable validator:

```text
script = scripts/evaluate_cgsc_extension_wall_probe.py
verdict = EXTENSION_WALL_LOCALIZED
primitive_derivation = PRIMITIVE_DERIVATION_NOT_CLOSED
missing_extensions = 6
extension_packages = 3
covered_extensions = 6
uncovered_extensions = 0
fatal_imports = 0
rejected_controls = 6
failed_controls = 0
draft_checks_failed = 0
```

The six missing extensions compress into three base-extension packages:

```text
finite_exposed_context_completion:
  covers:
    complete_exposed_context_partition
  open obligation:
    derive complete exposed finite context partition from B0 context cover,
    overlap discipline, and facticizable separation without importing spectral
    decomposition

route_automorphism_and_refinement_coherence:
  covers:
    reversible_context_automorphism_closure
    coherent_refinement_compactness
    generator_bookkeeping_without_stone
  open obligation:
    derive reversible context automorphisms, coherent refinement compactness,
    and generator bookkeeping from inheritance transitions without importing
    unitary group or Stone theorem

generated_composite_no_hidden_joint_closure:
  covers:
    product_context_generation_closure
    no_hidden_joint_only_generation
  open obligation:
    derive generated composite context closure and no hidden joint-only
    generation without importing Hilbert tensor product or Born readout
```

Negative controls rejected as imports:

```text
spectral_theorem
unitary_group
stone_theorem
hilbert_tensor_product
born_rule
complex_hilbert_space
```

Interpretation:

```text
There is a wall ahead, but it is localized rather than diffuse.

No fatal contradiction or mandatory QM import is currently detected.
However, CGSC is not derived from primitives until the three extension packages
above are proved from B0 or admitted as explicit new base principles.
```

This means the next broad proof pass should not target Hilbert/Born/unitary/
tensor directly. It should target the three extension packages as the actual
primitive-base bottleneck:

```text
B0
=> finite exposed context completion
=> route automorphism/refinement coherence
=> generated composite no-hidden-joint closure
=> CGSC
=> conditional Hilbert/Born/unitary/tensor route
```

Forbidden upgrade:

```text
does_not_prove_CGSC
does_not_prove_full_QM_I
does_not_derive_Hilbert_space
does_not_derive_Born_rule
does_not_derive_unitary_dynamics
does_not_derive_tensor_composition
does_not_treat_extension_wall_localization_as_wall_removal
```

### 174.279. CGSC/QM One-Pass Closure Attempt

A single broad closure attempt was added to test the whole current route in one
place:

```text
Proofs/QMClosure/CGSCQMOnePassClosureDraft.json
scripts/evaluate_cgsc_qm_one_pass_closure.py
```

The attempt combines:

```text
finite QM route gate
CGSC extension wall probe
CGSC primitive derivation probe
QM inevitability route probe
full QM proof-ledger closure
```

Result:

```text
cgsc_qm_one_pass_closure = STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL
proof_status = not_formal_proof
global_failed = 0
packages = 3
package_evidenced = 3
package_open_residual = 0
package_blocked = 0
finite_gate_failures = 0
missing_formal_proof_artifacts = 21
open_residuals = 0
draft_checks_failed = 0
```

Global requirements all matched the expected state:

```text
finite_qm_route_gate:
  PASS

extension_wall_probe:
  EXTENSION_WALL_LOCALIZED

primitive_derivation:
  PRIMITIVE_DERIVATION_NOT_CLOSED

qm_inevitability_route:
  CONDITIONAL_INEVITABILITY_ROUTE_VALIDATED

full_qm_proof_closure:
  PROOF_ARTIFACTS_MISSING
```

Package status:

```text
CANDIDATE_EVIDENCED:
  finite_exposed_context_completion
  route_automorphism_and_refinement_coherence
  generated_composite_no_hidden_joint_closure
```

The useful conclusion is sharp:

```text
No fatal structural wall was detected in the current broad route.
CGSC/QM is still not formally closed.
The next wall is now a formalization wall, not a vague conceptual wall.
```

At the time of the first one-pass attempt, the formal wall was:

```text
21 full-QM proof obligations lack machine-checkable proof artifacts.
```

This status is superseded by 174.281: the obligations now have conditional
machine-checkable package artifacts, but not formal proofs from primitives.

Therefore the route is:

```text
structurally ready for proof formalization:
  yes

CGSC proved from primitives:
  no

full QM proved:
  no

fatal import wall found:
  no

remaining blocker:
  produce machine-checkable proof artifacts for the registered obligations
  [superseded by 174.281: artifacts exist, but are conditional]
```

Forbidden upgrade:

```text
does_not_claim_CGSC_is_proved
does_not_claim_full_QM_is_proved
does_not_mark_conditional_routes_as_formal_proof
does_not_import_Hilbert_Born_unitary_tensor_or_Stone
does_not_treat_residual_rejection_as_full_QM_proof
```

### 174.280. Route-Closed Residual Admissibility Closure

The finite-sector residual was closed by admissibility, not by pretending it is
a represented carrier.

Updated finite-sector screen:

```text
script = scripts/evaluate_finite_sector_classification.py
```

New screen:

```text
constructive_carrier_witness:
  finite carriers must provide an explicit finite-route representation witness.
  An abstract route-closed placeholder is not an admissible carrier candidate.
```

Updated result:

```text
candidate = complex_hilbert_qubit_route
verdict = FINITE_SECTOR_HIT
passed = 8/8
failed = 0
open = 0

candidate = finite_route_closed_residual
verdict = REJECTED
passed = 5/8
failed = 1
open = 2
```

The residual still lacks:

```text
hidden_joint_invariant proof;
representation_classification proof.
```

But that no longer keeps the finite-sector gate open, because an unspecified
residual with no constructive witness is not a valid carrier in the finite
route classifier. Any future alternative carrier must be added as a concrete
candidate and rerun through the same screens.

Updated consolidated gate:

```text
script = scripts/verify_finite_qm_route.py
finite_qm_route_gate = PASS
finite_sector.route_closed_residual = REJECTED
```

Updated one-pass closure:

```text
cgsc_qm_one_pass_closure = STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL
package_evidenced = 3
package_open_residual = 0
open_residuals = 0
missing_formal_proof_artifacts = 21
```

This one-pass artifact count is superseded by 174.281.

Updated post-174.281 one-pass artifact status:

```text
conditional_artifacts = 21
missing_formal_proof_artifacts = 0
```

Interpretation:

```text
Residual wall:
  closed by admissibility.

Formal proof wall:
  still open.

Full QM:
  still not proved.
```

Forbidden upgrade:

```text
does_not_claim_unknown_future_carriers_are_impossible
does_not_treat_placeholder_rejection_as_universal_carrier_selection
does_not_claim_full_QM_is_proved
does_not_mark_conditional_routes_as_formal_proof
```

### 174.281. CGSC Package Conditional Artifact Pass

The technical "missing artifacts" wall was closed broadly with one Lean file:

```text
Proofs/QMClosure/CGSCPackageClosure.lean
```

The artifact defines three conditional package structures:

```text
FiniteExposedContextPackage
RouteAutomorphismRefinementPackage
GeneratedCompositePackage
```

and machine-checks package corollaries for all 21 registered full-QM closure
obligations.

The formal proof ledger now has three conditional proof cards:

```text
cgsc_finite_exposed_context_package_conditional_artifact
cgsc_route_automorphism_refinement_package_conditional_artifact
cgsc_generated_composite_package_conditional_artifact
```

Important boundary:

```text
proof_kind = conditional_proof
not machine_checked_finite_proof
```

Updated full-QM closure:

```text
full_qm_proof_closure = CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED
proved = 0
conditional_artifacts = 21
missing_artifacts = 0
sketch_artifacts = 0
incomplete_artifacts = 0
imported_artifacts = 0
```

Updated one-pass closure:

```text
cgsc_qm_one_pass_closure = STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL
package_evidenced = 3
package_open_residual = 0
open_residuals = 0
conditional_artifacts = 21
missing_formal_proof_artifacts = 0
```

Interpretation:

```text
Missing-artifact wall:
  closed.

Residual wall:
  closed by admissibility.

Formal primitive-proof wall:
  still open.

Full QM:
  still not proved.
```

The next real blocker is no longer artifact registration. It is:

```text
promote conditional package artifacts to formal primitive proofs:
  B0 or successor primitives
  => three CGSC packages
  => 21 obligations as formal corollaries
```

Forbidden upgrade:

```text
does_not_claim_conditional_package_artifacts_are_primitive_proofs
does_not_claim_full_QM_is_proved
does_not_mark_conditional_proof_cards_as_machine_checked_finite_proof
does_not_import_Hilbert_Born_unitary_tensor_or_Stone
```

### 174.282. CGSC Primitive-Extension Bridge Pass

The next broad pass inserted a machine-checked bridge between the primitive
extension wall and the conditional CGSC package artifacts:

```text
Proofs/QMClosure/CGSCPrimitiveBridge.lean
Proofs/QMClosure/CGSCPrimitiveBridgeDraft.json
scripts/evaluate_cgsc_primitive_bridge.py
```

The bridge is intentionally conditional. It proves the wiring:

```text
B0 candidate base
+ six primitive-extension witnesses
=> three CGSC packages
=> 21 full-QM closure obligations
```

It does not prove the six primitive-extension witnesses from B0.

Current bridge status:

```text
cgsc_primitive_bridge = CONDITIONAL_EXTENSION_BRIDGE_VALIDATED
lean = PASS
extensions = 6
packages = 3
obligations = 21
upstream_failed = 0
draft_checks_failed = 0
```

The one-pass closure now includes this bridge as a global requirement:

```text
cgsc_qm_one_pass_closure = STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL
global_failed = 0
conditional_artifacts = 21
missing_formal_proof_artifacts = 0
open_residuals = 0
```

The remaining wall is now sharper:

```text
prove or reject these six extension witnesses:
  complete_exposed_context_partition
  reversible_context_automorphism_closure
  coherent_refinement_compactness
  generator_bookkeeping_without_stone
  product_context_generation_closure
  no_hidden_joint_only_generation
```

If those six are proved from B0 or a successor primitive base, the existing
Lean bridge supplies the route into the three CGSC packages. If one of them is
unprovable without importing Hilbert/Born/unitary/tensor/Stone/spectral
structure, the wall becomes fatal for the current primitive base.

Forbidden upgrade:

```text
does_not_claim_extensions_are_proved_from_B0
does_not_claim_CGSC_is_proved
does_not_claim_full_QM_is_proved
does_not_mark_conditional_bridge_as_formal_proof
```

### 174.283. CGSC Semantic Content Wall

The next broad check found a sharper wall inside the bridge itself:

```text
Proofs/QMClosure/CGSCSemanticContentWall.lean
Proofs/QMClosure/CGSCSemanticContentWallDraft.json
scripts/evaluate_cgsc_semantic_content_wall.py
```

The current Lean bridge is structurally useful, but its extension slots are
still `CheckedProp` fields. That means the bridge can be satisfied by a
degenerate all-`True` extension base unless each extension witness is replaced
by a typed semantic predicate with a no-vacuity obligation.

Current wall status:

```text
cgsc_semantic_content_wall = SEMANTIC_CONTENT_WALL_DETECTED
lean = PASS
extension_witnesses = 6
draft_checks_failed = 0
```

This is not a regression. It prevents a false proof upgrade:

```text
bad route:
  B0
  => arbitrary CheckedProp packaging
  => CGSC packages
  => "QM proved"

blocked route:
  B0
  => grounded semantic source predicates
  => six extension proofs bound to those sources
  => CGSC packages
  => conditional QM route can be reconsidered
```

The one-pass status remains:

```text
cgsc_qm_one_pass_closure = STRUCTURAL_ROUTE_READY_FORMALIZATION_WALL
global_failed = 0
conditional_artifacts = 21
missing_formal_proof_artifacts = 0
```

But the next blocker is now more precise:

```text
replace schematic CheckedProp extension packaging with:
  typed semantic predicates;
  no-vacuity obligations;
  grounded semantic source binding;
  proof obligations from B0 or a successor primitive base.
```

Forbidden upgrade:

```text
does_not_treat_checked_prop_packaging_as_semantic_content
does_not_mark_vacuous_bridge_as_formal_proof
does_not_claim_extensions_are_proved_from_B0
does_not_claim_CGSC_is_proved
does_not_claim_full_QM_is_proved
```

### 174.284. Typed Semantic Extension Contract

The vacuity problem is now blocked by a typed semantic contract:

```text
Proofs/QMClosure/CGSCTypedSemanticExtensions.lean
```

The contract introduces typed semantic witnesses for all six extension slots:

```text
CompleteExposedContextPartitionSemantic
ReversibleContextAutomorphismClosureSemantic
CoherentRefinementCompactnessSemantic
GeneratorBookkeepingWithoutStoneSemantic
ProductContextGenerationClosureSemantic
NoHiddenJointOnlyGenerationSemantic
```

Each witness carries domain-specific typed content, not just `CheckedProp`.
The no-vacuity theorem checks concrete nontriviality obligations:

```text
typed_semantic_extension_base_has_no_vacuity
```

The semantic-content probe now reports:

```text
cgsc_semantic_content_wall = SEMANTIC_CONTENT_CONTRACT_REGISTERED
legacy_wall = PASS
typed_contract = PASS
extension_witnesses = 6
draft_checks_failed = 0
```

Meaning:

```text
old all-True CheckedProp route:
  still detected as a negative control.

typed semantic witness contract:
  registered and machine-checked.

proof from B0:
  still missing.
```

This solves the packaging problem but not the primitive-derivation problem.
The next proof target is now exact:

```text
B0 or successor primitives
=> six typed, non-vacuous semantic extension witnesses
=> CGSC primitive extension base
=> three CGSC packages
=> 21 conditional QM obligations
```

Forbidden upgrade:

```text
does_not_claim_typed_extensions_are_proved_from_B0
does_not_mark_semantic_contract_as_CGSC_proof
does_not_claim_full_QM_is_proved
```

### 174.285. Typed Decorative Semantic Wall

The typed contract removes the one-object/all-True vacuity failure, but it is
not yet enough for a QM proof. A second negative control shows that decorative
typed content can still be placed beside all-True `CheckedProp` obligations:

```text
Proofs/QMClosure/CGSCTypedDecorativeWall.lean
```

Machine-checked witness:

```text
typed_contract_still_admits_decorative_true_extensions
decorative_typed_base_yields_conditional_package_obligations
```

Meaning:

```text
Typed non-vacuity alone:
  not sufficient for proof upgrade.

Required next step:
  bind each QM closure obligation to grounded semantic source predicates,
  not to arbitrary CheckedProp fields carried beside a witness.
```

This changes the real target. We should not try to prove "six typed witnesses
exist" as the next theorem. The correct theorem must be stronger:

```text
B0 or successor primitives
=> grounded semantic source predicates
=> CGSC extension obligations as definitions/theorems over those sources
=> CGSC packages
=> full-QM closure obligations
```

Until that binding exists, any formal upgrade would still be structurally
forgeable.

### 174.286. Grounded Semantic Extension Kernel

The next proof object binds the six CGSC extension slots to semantic source
predicates instead of arbitrary `CheckedProp` payloads:

```text
Proofs/QMClosure/CGSCGroundedSemanticExtensions.lean
```

It introduces one grounded source for each extension family:

```text
completeExposedSource
reversibleSource
refinementSource
generatorSource
productSource
noHiddenJointSource
```

The generated extension records are computed from those sources. This removes
the previous pattern:

```text
witness exists beside arbitrary obligation statement
```

and replaces it with:

```text
obligation statement is the semantic source predicate
```

Machine-checked artifacts:

```text
grounded_semantic_extension_base_yields_six_extension_statements
grounded_semantic_extension_base_blocks_decorative_relations
grounded_semantic_extension_base_yields_package_import_guards
```

This is still not a proof of QM from B0. It is the stricter theorem shape that
the next primitive-base proof must instantiate:

```text
B0 or successor primitives
=> grounded semantic source predicates
=> six CGSC extension statements
=> CGSC package obligations
```

### 174.287. Full QM Assembly And Toy-Grounding Wall

The current proof graph can now assemble the whole QM closure bundle from a
grounded CGSC semantic extension base:

```text
Proofs/QMClosure/FullQMAssemblyFromGroundedSources.lean
```

Machine-checked theorem:

```text
grounded_semantic_sources_yield_full_qm_obligation_bundle
```

This packages all 21 current full-QM closure obligations:

```text
finite projection / projective consistency / NUSD / gluing / spectrality
Born-readout normalization / additivity / coarse graining / equivalence
reversible dynamics / overlap / projective action / continuity / generator
product exhaustion / local tomography / monoidal associativity / entanglement
projective limits / physical phase-scale boundary
```

However, the same pass also found the next wall:

```text
Proofs/QMClosure/CGSCGroundedToyWall.lean
```

Machine-checked negative control:

```text
grounded_kernel_admits_toy_full_qm_obligation_bundle
```

Meaning:

```text
grounded source satisfiability:
  enough to assemble the theorem mechanically;
  not enough to prove QM.

why:
  a small Bool/Unit toy source model can satisfy the grounded source shape and
  produce the full obligation bundle.

therefore:
  the remaining proof target is not "find any grounded sources";
  it is "derive universally scoped grounded sources from the primitive base".
```

The next theorem must quantify over the admissible primitive-generated context
universe, not over a freely chosen toy source model:

```text
B0 or successor primitives
=> universal admissible context/source kernel
=> grounded semantic sources for all admissible readouts/routes/composites
=> full QM obligation bundle
```

So the honest status is:

```text
full assembly from grounded sources: machine-checked conditional theorem
toy-grounding wall: machine-checked negative control
QM from primitives: still open
```

### 174.288. Universal Primitive Source Kernel

The two-point toy wall is now blocked by a stronger kernel:

```text
Proofs/QMClosure/UniversalPrimitiveSourceKernel.lean
```

The kernel wraps a grounded CGSC semantic source base with primitive-generated
scope and admissible-universe guards, plus anti-collapse rank predicates on the
key context/fact types:

```text
AtLeastThree exposed.Context
AtLeastThree reversible.Context
AtLeastThree product.LocalContext
AtLeastThree noHiddenJoint.LocalFact
```

Machine-checked assembly theorem:

```text
universal_primitive_source_kernel_yields_full_qm_obligation_bundle
```

Machine-checked rejection of the current toy wall:

```text
bool_has_no_at_least_three
toy_grounded_kernel_has_no_universal_exposed_rank
toy_grounded_kernel_has_no_universal_reversible_rank
toy_grounded_kernel_has_no_universal_product_rank
toy_grounded_kernel_has_no_universal_local_fact_rank
```

This removes the specific Bool/Unit toy counter-route from the previous pass.
It still does not prove QM, because the universal kernel itself is not yet
derived from B0 or successor primitives.

Current exact target:

```text
B0 or successor primitives
=> UniversalPrimitiveSourceKernel
=> full QM obligation bundle
```

Remaining honest blocker:

```text
derive the universal primitive source kernel from primitives;
rule out higher-cardinality toy kernels, not only the current two-point toy.
```

### 174.289. Universal Kernel Toy Wall

The previous `AtLeastThree` rank filter is not enough. A three-point toy model
still satisfies the universal kernel shape and mechanically assembles the full
QM obligation bundle:

```text
Proofs/QMClosure/UniversalPrimitiveToyWall.lean
```

Machine-checked negative control:

```text
universal_kernel_admits_three_point_toy_full_qm_obligation_bundle
universal_kernel_three_point_toy_keeps_import_guards
```

This is the important lesson of the broad pass:

```text
cardinality filters do not prove QM;
free source kernels do not prove QM;
ranked toy kernels still pass the assembly theorem.
```

The next target must stop adding local filters and instead remove free source
selection entirely:

```text
primitive-generated admissibility
=> source kernel constructed by definition
=> no external choice of Context/Fact/Route/ProductWitness types
=> full QM obligation bundle
```

Current status:

```text
full assembly from source kernels: machine-checked conditional theorem
two-point toy wall: rejected by AtLeastThree
three-point universal toy wall: detected and registered
QM from primitives: still open
```

### 174.290. Primitive-Generated Source Kernel

The next pass removes one source of fake progress: the six CGSC source slots are
no longer free independent types. They are now constructed as subtypes of one
primitive-generated atom universe:

```text
Proofs/QMClosure/PrimitiveGeneratedSourceKernel.lean
```

The central object is:

```text
PrimitiveGeneratedAdmissibility
```

It supplies a single `Atom` type plus predicates for contexts, facts, blocks,
routes, refinements, states, generators, and local facts. The grounded CGSC
source base is then built from those predicates by construction.

Machine-checked conditional assembly theorem:

```text
primitive_generated_admissibility_yields_full_qm_obligation_bundle
```

Machine-checked structural guard:

```text
primitive_generated_source_slots_share_one_atom_universe
```

This does not prove QM. It does prove that the current route can be tightened
from freely selected source types to one primitive-generated admissibility
interface. The remaining blocker is sharper:

```text
B0 or successor primitives
=> PrimitiveGeneratedAdmissibility
=> primitive-generated source kernel
=> full QM obligation bundle
```

So the wall moved from "choose a source kernel" to:

```text
derive PrimitiveGeneratedAdmissibility from the primitive base;
otherwise the source kernel remains a conditional interface.
```

### 174.291. Primitive-Generated Admissibility Wall

The one-`Atom` source construction is still not enough by itself. The current
formal B0 candidate contains proof-boundary flags, but it does not yet bind the
`Atom` universe or the admissibility predicates to the primitive context cover,
outcome presheaf, inheritance transitions, readout witnesses, and stable
distinguishability relation.

The negative control is machine-checked:

```text
Proofs/QMClosure/PrimitiveGeneratedAdmissibilityWall.lean
```

It constructs a free finite atom universe for any `B0CandidateBase` and proves:

```text
b0_alone_admits_free_primitive_generated_admissibility
b0_alone_can_feed_free_primitive_generated_source_kernel
free_primitive_generated_admissibility_keeps_import_guards
```

This is not a QM proof. It is a failure-ledger result:

```text
B0CandidateBase alone is too weak;
PrimitiveGeneratedAdmissibility can still be freely selected;
therefore the next base must bind admissibility to B0 or replace B0 with a
successor primitive base whose context/outcome/inheritance/readout/distinction
data generate the admissibility interface.
```

Sharper remaining target:

```text
context-first successor base
=> bound PrimitiveGeneratedAdmissibility
=> primitive-generated source kernel
=> full QM obligation bundle
```

### 174.292. Bound Primitive-Generated Base

The free-admissibility problem is now closed for the successor-base route:

```text
Proofs/QMClosure/BoundPrimitiveGeneratedBase.lean
```

Instead of accepting an arbitrary `Atom` plus arbitrary role predicates, the
successor base supplies typed primitive witness sorts:

```text
ContextWitness
FactWitness
BlockWitness
RouteWitness
RefinementWitness
StateWitness
GeneratorWitness
LocalFactWitness
```

The admissible atom universe is then generated by constructors:

```text
BoundSourceAtom.context
BoundSourceAtom.fact
BoundSourceAtom.block
BoundSourceAtom.route
BoundSourceAtom.refinement
BoundSourceAtom.state
BoundSourceAtom.generator
BoundSourceAtom.localFact
```

Machine-checked binding theorem:

```text
bound_admissibility_role_atoms_are_constructor_generated
```

Machine-checked assembly theorem:

```text
bound_primitive_generated_base_yields_full_qm_obligation_bundle
```

This is the positive result missing from the previous pass:

```text
BoundPrimitiveGeneratedBase
=> constructor-bound PrimitiveGeneratedAdmissibility
=> primitive-generated source kernel
=> full QM obligation bundle
```

It does not prove full QM, because the bound successor base itself must still
be accepted as the primitive base or derived from the older B0 candidate. But
the specific structural defect "PrimitiveGeneratedAdmissibility is freely
selected" is now resolved for the successor-base path.

Updated evaluator status:

```text
cgsc_semantic_content_wall = BOUND_PRIMITIVE_GENERATED_BASE_REGISTERED
cgsc_primitive_derivation = SUCCESSOR_BASE_DERIVATION_REGISTERED
cgsc_extension_wall_probe = EXTENSION_ROUTE_READY
```

Meaning:

```text
old B0CandidateBase alone: still too weak
bound successor base: constructor-bound CGSC source families registered
full QM proof: still conditional until the successor-base route is promoted
or derived and the 21 package artifacts become formal primitive proofs
```

### 174.293. B1 Primitive-Base Promotion

The successor-base route now has an explicit B1 promotion artifact:

```text
Proofs/QMClosure/B1PrimitiveBase.lean
```

It wraps `BoundPrimitiveGeneratedBase` with three proof-boundary commitments:

```text
successorBasePromoted
noFreeAdmissibilityBoundary
noTargetImportBoundary
```

Machine-checked theorems:

```text
b1_primitive_base_constructor_binds_admissibility
b1_primitive_base_promotes_successor_boundaries
b1_primitive_base_yields_full_qm_obligation_bundle
b1_primitive_base_yields_import_guards
```

Updated evaluator status:

```text
cgsc_semantic_content_wall = B1_PRIMITIVE_BASE_REGISTERED
cgsc_primitive_derivation = SUCCESSOR_BASE_DERIVATION_REGISTERED
cgsc_extension_wall_probe = EXTENSION_ROUTE_READY
```

This removes the previous blocker "promote the bound successor base" for the
B1 route. The new blocker is sharper:

```text
derive B1 from older B0 or explicitly migrate the primitive base to B1;
then turn B1 package projections into semantic target proofs.
```

This is still not a proof of QM. It is a registered conditional route from B1
to the current full-QM obligation bundle, with import guards preserved.
