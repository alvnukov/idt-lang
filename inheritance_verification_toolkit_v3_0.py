#!/usr/bin/env python3
"""
Inherited Distinguishability Verification Toolkit v0.1

Minimal utilities for checking mathematical invariants and simple predictive
bounds. This is not a full data-analysis package yet.
"""

from __future__ import annotations

import math
from typing import Sequence, Dict, Any
import numpy as np


def is_psd(matrix: np.ndarray, tol: float = 1e-10) -> bool:
    """Return True if Hermitian matrix is positive semidefinite within tolerance."""
    m = np.asarray(matrix, dtype=complex)
    if not np.allclose(m, m.conj().T, atol=tol):
        return False
    eigvals = np.linalg.eigvalsh(m)
    return bool(np.min(eigvals) >= -tol)


def schur_product(kernels: Sequence[np.ndarray]) -> np.ndarray:
    """Componentwise product of kernels."""
    if not kernels:
        raise ValueError("Need at least one kernel")
    out = np.ones_like(np.asarray(kernels[0], dtype=complex))
    for k in kernels:
        out = out * np.asarray(k, dtype=complex)
    return out


def actualization(A: Sequence[int], B: Sequence[int], W: np.ndarray, Gamma: np.ndarray) -> complex:
    """A(A,B)=sum_{h in A,h' in B} W(h) W(h')* Gamma(h,h')."""
    W = np.asarray(W, dtype=complex)
    G = np.asarray(Gamma, dtype=complex)
    total = 0.0 + 0.0j
    for h in A:
        for hp in B:
            total += W[h] * np.conj(W[hp]) * G[h, hp]
    return total


def mu(A: Sequence[int], W: np.ndarray, Gamma: np.ndarray) -> float:
    """Diagonal measure mu(A)=A(A,A)."""
    val = actualization(A, A, W, Gamma)
    return float(np.real_if_close(val))


def facticity(A: Sequence[int], B: Sequence[int], W: np.ndarray, Gamma: np.ndarray) -> float:
    """f(A,B)=1-|A(A,B)|/sqrt(A(A,A)A(B,B))."""
    aa = mu(A, W, Gamma)
    bb = mu(B, W, Gamma)
    if aa <= 0 or bb <= 0:
        raise ValueError("Facticity requires positive diagonal measures")
    ab = actualization(A, B, W, Gamma)
    eps = abs(ab) / math.sqrt(aa * bb)
    return 1.0 - eps


def sorkin_I3(A: Sequence[int], B: Sequence[int], C: Sequence[int], W: np.ndarray, Gamma: np.ndarray) -> float:
    """Third-order Sorkin interference term."""
    AuB = list(A) + list(B)
    AuC = list(A) + list(C)
    BuC = list(B) + list(C)
    all3 = list(A) + list(B) + list(C)
    return (
        mu(all3, W, Gamma)
        - mu(AuB, W, Gamma)
        - mu(AuC, W, Gamma)
        - mu(BuC, W, Gamma)
        + mu(A, W, Gamma)
        + mu(B, W, Gamma)
        + mu(C, W, Gamma)
    )


def chsh(E00: float, E01: float, E10: float, E11: float) -> float:
    """CHSH S = E00 + E01 + E10 - E11."""
    return E00 + E01 + E10 - E11


def residual_lambda(V_obs: float, V_env: float) -> float:
    """Y=-log(V_obs/V_env)."""
    if V_obs <= 0 or V_env <= 0:
        raise ValueError("Visibilities must be positive")
    return -math.log(V_obs / V_env)


def mass_spatial_residual(lambda_I: float, tau: float, m: float, m0: float, alpha: float, dx: float, rI: float) -> float:
    """M3 residual Y."""
    return lambda_I * tau * (m / m0) ** alpha * (1.0 - math.exp(-(dx * dx) / (4.0 * rI * rI)))


def lambda_bound(delta: float, tau: float, m: float, m0: float, alpha: float, dx: float, rI: float) -> float:
    """Upper bound on lambda_I from residual sensitivity delta."""
    factor = (m / m0) ** alpha * (1.0 - math.exp(-(dx * dx) / (4.0 * rI * rI)))
    if tau <= 0 or factor <= 0:
        raise ValueError("tau and sensitivity factor must be positive")
    return delta / (tau * factor)


def model_M1(tau: float, lamb: float) -> float:
    return lamb * tau


def model_M2(tau: float, kappa: float) -> float:
    return 0.5 * math.log(1.0 + kappa * tau)


def model_M3(tau: float, lambda_I: float, m: float, m0: float, alpha: float, dx: float, rI: float) -> float:
    return mass_spatial_residual(lambda_I, tau, m, m0, alpha, dx, rI)


def poisson_visibility_factor(R: float, tau: float, d: float) -> float:
    """E[exp(-d N_tau)] for N_tau~Poisson(R tau)."""
    return math.exp(R * tau * (math.exp(-d) - 1.0))


def demo_unit_tests() -> Dict[str, Any]:
    """Small built-in sanity demo."""
    K1 = np.array([[1, 0.7], [0.7, 1]], dtype=complex)
    K2 = np.array([[1, 0.5], [0.5, 1]], dtype=complex)
    Gamma = schur_product([K1, K2])
    W = np.array([1 / math.sqrt(2), 1 / math.sqrt(2)], dtype=complex)
    A = [0]
    B = [1]
    I3 = sorkin_I3([0], [], [1], W, Gamma)  # degenerate demo
    return {
        "K1_psd": is_psd(K1),
        "K2_psd": is_psd(K2),
        "Gamma_psd": is_psd(Gamma),
        "facticity_0_1": facticity(A, B, W, Gamma),
        "Gamma_offdiag": Gamma[0, 1].real,
        "demo_I3_degenerate": I3,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(demo_unit_tests(), indent=2))
