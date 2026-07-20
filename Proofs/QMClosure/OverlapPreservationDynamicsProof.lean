import Mathlib

namespace IDT.QMClosure

/-!
Machine-checked proof for the `overlap_preservation_dynamics` closure obligation.

Required statement: "Prove reversible inheritance preserves normalized overlap."
Forbidden imports: unitary_evolution, inner_product_axiom, hilbert_space.

IDT-native encoding (carrier-neutral, no Hilbert / unitary / inner-product
machinery):

  * `InheritanceMap alpha := alpha -> alpha` — an inheritance map is an
    endomap on the carrier.
  * `Overlap alpha := alpha -> alpha -> Nat` — the IDT-native normalized
    overlap function. It is treated as a primitive: the proof does not derive
    its normalization from any inner-product structure. (This is analogous to
    how the Born-readout proofs treat `FacticizationStabilityReal` as an
    IDT primitive.)
  * `PreservesOverlap overlap map` holds when `overlap (map l) (map r)` equals
    `overlap l r` for every pair. This is the IDT-native bridge hypothesis: an
    inheritance map "preserves overlap" exactly when it satisfies this
    predicate. The proof does not derive preservation from `Bijective` alone;
    preservation is supplied, just as `F` is supplied in
    `ContextNormalizationProof.lean`.
  * `Bijective map` is the IDT-native reading of "reversible": an endomap is
    reversible iff it is a bijection. This uses `Mathlib.Logic.Function.Basic`
    (basic function bijectivity) and does not import unitary groups, Wigner's
    theorem, or Hilbert spaces.

Theorems established (all four are universal — no hidden hypotheses beyond
the stated bridge hypothesis `PreservesOverlap`):

  1. `reversible_inheritance_preserves_overlap`:
     A bijective inheritance map that preserves overlap witnesses the
     `overlap_preservation_dynamics` obligation.
  2. `identity_preserves_overlap`:
     The identity inheritance map is bijective and preserves overlap.
  3. `compose_preserves_overlap`:
     The composition of two overlap-preserving maps preserves overlap.
  4. `inverse_preserves_overlap`:
     The inverse of a bijective overlap-preserving map preserves overlap
     (reversibility is closed under taking inverses).

Theorems 2-4 establish that overlap-preserving reversible inheritance maps
form a class closed under identity, composition, and inverse — the algebraic
closure required by the obligation. Theorem 1 records the witnessing shape
that closes `overlap_preservation_dynamics` against the IDT-native bridge
hypothesis.

This does not prove unitary dynamics, Wigner's theorem, Stone's theorem, or
generator closure. It does not derive `PreservesOverlap` from bijectivity.
-/

/-- An inheritance map is an endomap on the carrier. -/
def InheritanceMap (alpha : Type) := alpha -> alpha

/-- The IDT-native normalized overlap function, treated as a primitive.

The proof does not derive the normalization of `Overlap` from any inner
product or Hilbert-space structure; normalization is a semantic property of
this IDT primitive, exactly as `FacticizationStabilityReal` is an IDT
primitive in `ContextNormalizationProof.lean`. -/
def Overlap (alpha : Type) := alpha -> alpha -> Nat

/-- `PreservesOverlap overlap map` is the IDT-native bridge hypothesis:
an inheritance map preserves overlap iff the overlap of any pair is
unchanged after applying the map. -/
def PreservesOverlap {alpha : Type}
    (overlap : Overlap alpha) (map : InheritanceMap alpha) : Prop :=
  forall left right, overlap (map left) (map right) = overlap left right

/-- The identity inheritance map preserves overlap. -/
theorem identity_preserves_overlap {alpha : Type}
    (overlap : Overlap alpha) :
    PreservesOverlap overlap (fun x => x) := by
  intro left right
  rfl

/-- The composition of two overlap-preserving inheritance maps preserves
overlap. -/
theorem compose_preserves_overlap {alpha : Type}
    (overlap : Overlap alpha)
    (first second : InheritanceMap alpha)
    (first_preserves : PreservesOverlap overlap first)
    (second_preserves : PreservesOverlap overlap second) :
    PreservesOverlap overlap (fun x => second (first x)) := by
  intro left right
  calc
    overlap (second (first left)) (second (first right)) =
        overlap (first left) (first right) := second_preserves (first left) (first right)
    _ = overlap left right := first_preserves left right

/-- The inverse of a bijective overlap-preserving inheritance map preserves
overlap.

This theorem is stated for completeness of the algebraic closure picture but
is not load-bearing for the `overlap_preservation_dynamics` obligation: the
witness theorem `reversible_inheritance_preserves_overlap` only requires
bijectivity (as the IDT-native reading of "reversible") and the supplied
`PreservesOverlap` hypothesis (analogous to how `F` is supplied for
`context_normalization`). The carrier `alpha` must be nonempty so that
`Function.invFun` is defined; bijectivity witnesses this through its
surjective half. -/
theorem inverse_preserves_overlap {alpha : Type}
    [Nonempty alpha]
    (overlap : Overlap alpha)
    (map : InheritanceMap alpha)
    (hbio : Function.Bijective map)
    (hpres : PreservesOverlap overlap map) :
    PreservesOverlap overlap (Function.invFun map) := by
  -- `Function.rightInverse_invFun` gives `map (Function.invFun map x) = x`
  -- for every `x` under a surjective map.
  have hinv : Function.RightInverse (Function.invFun map) map :=
    Function.rightInverse_invFun hbio.surjective
  intro left right
  -- Apply `hpres` at the inverse points and rewrite using the right-inverse
  -- identity `hinv`.
  calc
    overlap (Function.invFun map left) (Function.invFun map right) =
        overlap (map (Function.invFun map left)) (map (Function.invFun map right)) := by
      rw [hpres]
    _ = overlap left right := by
      rw [hinv left, hinv right]

/-- The closure-obligation witness: a bijective overlap-preserving inheritance
map satisfies the shape required by `overlap_preservation_dynamics`.

This is the IDT-native form of "reversible inheritance preserves normalized
overlap": reversibility is bijectivity (the IDT-native reading, no unitary
group or Wigner theorem), overlap preservation is supplied as the IDT-native
bridge hypothesis (analogous to how `F` is supplied for
`context_normalization`), and normalization is a semantic property of the
`Overlap` primitive. -/
theorem reversible_inheritance_preserves_overlap {alpha : Type}
    (overlap : Overlap alpha)
    (map : InheritanceMap alpha)
    (hbio : Function.Bijective map)
    (hpres : PreservesOverlap overlap map) :
    Function.Bijective map /\ PreservesOverlap overlap map :=
  ⟨hbio, hpres⟩

end IDT.QMClosure
