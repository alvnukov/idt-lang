"""Exact certificates for rational symmetric kernels of dimension 1--3.

Generation uses Schur complements. Verification uses only direct identities;
it does not trust or rerun the decomposition algorithm. Neither is Lean proof.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction as F

from theory_experiments.primitive_screen import (
    Matrix,
    PairKernel,
    Vector,
    object_fields,
)

SCHEMA = "idt-rational-positivity-certificate/1"


@dataclass(frozen=True)
class _Square:
    weight: F
    vector: Vector


@dataclass(frozen=True)
class _Factorization:
    terms: tuple[_Square, ...]


def _decompose(matrix: Matrix) -> _Factorization | Vector:
    size = len(matrix)
    for i in range(size):
        if matrix[i][i] < 0:
            return tuple(F(j == i) for j in range(size))
    pivot = next((i for i in range(size) if matrix[i][i] > 0), None)
    if pivot is None:
        for i in range(size):
            for j in range(i + 1, size):
                if matrix[i][j] != 0:
                    sign = 1 if matrix[i][j] > 0 else -1
                    return tuple(F(1 if k == i else -2*sign if k == j else 0)
                                 for k in range(size))
        return _Factorization(())
    a = matrix[pivot][pivot]
    rest = tuple(i for i in range(size) if i != pivot)
    schur = tuple(tuple(matrix[i][j] - matrix[i][pivot]*matrix[pivot][j]/a
                        for j in rest) for i in rest)
    result = _decompose(schur)
    if isinstance(result, _Factorization):
        first = _Square(a, tuple(F(1) if i == pivot else matrix[pivot][i]/a for i in range(size)))
        embedded = tuple(_Square(term.weight, tuple(F() if i == pivot else term.vector[rest.index(i)]
                                                   for i in range(size))) for term in result.terms)
        return _Factorization((first,) + embedded)
    lifted_pivot = -sum((matrix[pivot][i]*result[j] for j, i in enumerate(rest)), F())/a
    return tuple(lifted_pivot if i == pivot else result[rest.index(i)] for i in range(size))


def _quadratic(matrix: Matrix, vector: Vector) -> F:
    return sum((vector[i]*matrix[i][j]*vector[j]
                for i in range(len(matrix)) for j in range(len(matrix))), F())


def _nonzero_sum_direction(matrix: Matrix, vector: Vector) -> Vector:
    if sum(vector, F()) != 0:
        return vector
    q = _quadratic(matrix, vector)
    linear = 2*sum((matrix[0][i]*vector[i] for i in range(len(matrix))), F())
    # For 0<t<=1, the perturbation of q is at most t*(|linear|+|K00|).
    step = min(F(1), -q/(2*(abs(linear)+abs(matrix[0][0])+1)))
    return (vector[0]+step,) + vector[1:]


def certify(matrix: Matrix) -> dict[str, object]:
    """Return a positive Gram identity or a negative normalized-reference witness.

    The caller must validate the returned certificate with verify_certificate.
    """
    PairKernel("certificate_input", matrix)  # Enforce the supported mathematical domain.
    result = _decompose(matrix)
    if isinstance(result, _Factorization):
        return {"schema": SCHEMA, "kind": "weighted_squares", "terms": [
            {"weight": str(term.weight), "vector": list(map(str, term.vector))}
            for term in result.terms]}
    vector = _nonzero_sum_direction(matrix, result)
    q = _quadratic(matrix, vector)
    total = sum(vector, F())
    if total == 0 or q >= 0:
        raise ValueError("decomposition failed to produce a negative reference direction")
    return {"schema": SCHEMA, "kind": "negative_direction", "vector": list(map(str, vector)),
            "quadratic": str(q), "normalized_reference_weight": str(q/total**2)}


def _fraction(value: object) -> F:
    # Derived certificate fractions can exceed the input adapter's 12-digit bound.
    if not isinstance(value, str) or not re.fullmatch(r"-?\d{1,512}(?:/[1-9]\d{0,511})?", value):
        raise ValueError("invalid or oversized certificate fraction")
    return F(value)


def _vector(value: object, size: int) -> Vector:
    if not isinstance(value, list) or len(value) != size:
        raise ValueError("certificate vector dimension mismatch")
    return tuple(_fraction(x) for x in value)


def verify_certificate(matrix: Matrix, value: object) -> bool:
    """Check a serialized certificate by direct exact arithmetic, never search.

    False means invalid evidence, not a conclusion about the candidate matrix.
    """
    try:
        PairKernel("certificate_input", matrix)
        row = object_fields(value)
        if row.get("schema") != SCHEMA:
            return False
        size = len(matrix)
        if row.get("kind") == "weighted_squares":
            object_fields(row, {"schema", "kind", "terms"})
            raw_terms = row["terms"]
            if not isinstance(raw_terms, list) or len(raw_terms) > size:
                return False
            terms: list[tuple[F, Vector]] = []
            for raw in raw_terms:
                term = object_fields(raw, {"weight", "vector"})
                weight, vector = _fraction(term["weight"]), _vector(term["vector"], size)
                if weight <= 0:
                    return False
                terms.append((weight, vector))
            return all(matrix[i][j] == sum((w*v[i]*v[j] for w, v in terms), F())
                       for i in range(size) for j in range(size))
        if row.get("kind") == "negative_direction":
            object_fields(row, {"schema", "kind", "vector", "quadratic", "normalized_reference_weight"})
            vector = _vector(row["vector"], size)
            # Separate arithmetic path from generation: matrix-vector product, then dot product.
            product = tuple(sum((entry*x for entry, x in zip(line, vector, strict=True)), F())
                            for line in matrix)
            q = sum((x*y for x, y in zip(vector, product, strict=True)), F())
            total = sum(vector, F())
            return (q < 0 and total != 0 and _fraction(row["quadratic"]) == q
                    and _fraction(row["normalized_reference_weight"]) == q/total**2)
        return False
    except (TypeError, ValueError, ZeroDivisionError, OverflowError):
        return False
