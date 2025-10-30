"""
Hierarchical Bayesian Model for Multi-Event 141.7001 Hz Analysis

This module implements a hierarchical Bayesian inference framework to assess
the global significance of a coherent spectral feature at 141.7001 Hz across
multiple gravitational wave events.

Model Structure:
- Global parameter π (pi): Fraction of events containing the coherent tone
- Per-event SNR: Mixture of H0 (noise) and H1 (signal+noise)
- H0: Gaussian with mean=0, std=1 (whitened noise)
- H1: Gaussian with mean=μ, std=σ (signal present)

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Date: October 2025
License: MIT
"""

import numpy as np
from scipy.special import logsumexp
from scipy.stats import beta, norm
import json
from typing import List, Dict, Tuple, Optional


def loglik_event(snr: float, pi: float, mu: float = 6.0, sigma: float = 1.0) -> float:
    """
    Log-likelihood of observing SNR given mixing parameter pi.

    Mixture model:
    - With probability (1-pi): SNR ~ N(0, 1)  [noise only]
    - With probability pi: SNR ~ N(mu, sigma) [signal present]

    Parameters
    ----------
    snr : float
        Observed signal-to-noise ratio
    pi : float
        Global mixing parameter (0 ≤ pi ≤ 1)
    mu : float, optional
        Expected SNR when signal is present (default: 6.0)
    sigma : float, optional
        Standard deviation of signal distribution (default: 1.0)

    Returns
    -------
    float
        Log-likelihood of the data
    """
    # Log-likelihood under H0 (noise only)
    ll0 = norm.logpdf(snr, loc=0, scale=1)

    # Log-likelihood under H1 (signal present)
    ll1 = norm.logpdf(snr, loc=mu, scale=sigma)

    # Mixture: log(p) = log(sum_i p_i * L_i)
    # Use logsumexp for numerical stability
    log_weights = [np.log1p(-pi), np.log(pi)] if pi > 0 else [0, -np.inf]
    return logsumexp([log_weights[0] + ll0, log_weights[1] + ll1])


def logpost(snr_list: List[float], pi: float,
            mu: float = 6.0, sigma: float = 1.0,
            prior_alpha: float = 1.0, prior_beta: float = 1.0) -> float:
    """
    Log-posterior of pi given observed SNRs.

    Parameters
    ----------
    snr_list : List[float]
        List of observed SNRs across events
    pi : float
        Global mixing parameter
    mu : float, optional
        Expected SNR when signal is present
    sigma : float, optional
        Standard deviation of signal distribution
    prior_alpha : float, optional
        Beta prior parameter α (default: 1.0 for uniform)
    prior_beta : float, optional
        Beta prior parameter β (default: 1.0 for uniform)

    Returns
    -------
    float
        Log-posterior density
    """
    if pi <= 0 or pi >= 1:
        return -np.inf

    # Log-likelihood: sum over events (assuming independence)
    log_lik = sum(loglik_event(snr, pi, mu, sigma) for snr in snr_list)

    # Log-prior: Beta(α, β)
    log_prior = beta.logpdf(pi, prior_alpha, prior_beta)

    return log_lik + log_prior


def bayes_factor(snr_list: List[float],
                 mu: float = 6.0, sigma: float = 1.0,
                 n_grid: int = 1001) -> Tuple[float, Dict]:
    """
    Compute Bayes Factor comparing H1 (signal in some events) vs H0 (noise only).

    BF = P(data | H1) / P(data | H0)
       = ∫ P(data | π, H1) P(π | H1) dπ / P(data | π=0, H0)

    Parameters
    ----------
    snr_list : List[float]
        Observed SNRs across events
    mu : float, optional
        Expected SNR when signal is present
    sigma : float, optional
        Standard deviation of signal distribution
    n_grid : int, optional
        Number of grid points for numerical integration

    Returns
    -------
    bf : float
        Bayes Factor (H1 / H0)
    diagnostics : Dict
        Additional diagnostic information
    """
    # Grid over π ∈ (0, 1)
    pi_grid = np.linspace(1e-6, 1 - 1e-6, n_grid)

    # Compute log-posterior at each grid point
    log_posts = np.array([logpost(snr_list, pi, mu, sigma) for pi in pi_grid])

    # Marginal likelihood under H1 (numerical integration via trapezoidal rule)
    # logZ1 = log ∫ P(data | π) P(π) dπ
    logZ1 = logsumexp(log_posts) - np.log(n_grid)

    # Marginal likelihood under H0 (π = 0, all noise)
    # P(data | H0) = ∏_i N(snr_i | 0, 1)
    logZ0 = sum(norm.logpdf(snr, loc=0, scale=1) for snr in snr_list)

    # Bayes Factor
    log_bf = logZ1 - logZ0
    bf = np.exp(log_bf)

    # Posterior mean of π (for interpretation)
    weights = np.exp(log_posts - np.max(log_posts))
    weights /= weights.sum()
    pi_mean = np.sum(pi_grid * weights)
    pi_std = np.sqrt(np.sum((pi_grid - pi_mean)**2 * weights))

    diagnostics = {
        'log_bf': float(log_bf),
        'logZ1': float(logZ1),
        'logZ0': float(logZ0),
        'pi_mean': float(pi_mean),
        'pi_std': float(pi_std),
        'n_events': len(snr_list),
        'mean_snr': float(np.mean(snr_list)),
        'std_snr': float(np.std(snr_list))
    }

    return bf, diagnostics


def posterior_pi(snr_list: List[float],
                 mu: float = 6.0, sigma: float = 1.0,
                 n_grid: int = 1001) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute normalized posterior distribution P(π | data).

    Parameters
    ----------
    snr_list : List[float]
        Observed SNRs across events
    mu : float, optional
        Expected SNR when signal is present
    sigma : float, optional
        Standard deviation of signal distribution
    n_grid : int, optional
        Number of grid points

    Returns
    -------
    pi_grid : np.ndarray
        Grid of π values
    posterior : np.ndarray
        Normalized posterior density
    """
    pi_grid = np.linspace(1e-6, 1 - 1e-6, n_grid)
    log_posts = np.array([logpost(snr_list, pi, mu, sigma) for pi in pi_grid])

    # Normalize
    posterior = np.exp(log_posts - logsumexp(log_posts))

    return pi_grid, posterior


def analyze_multi_event(snr_dict: Dict[str, float],
                       output_file: Optional[str] = None,
                       mu: float = 6.0,
                       sigma: float = 1.0) -> Dict:
    """
    Full hierarchical analysis of multi-event data.

    Parameters
    ----------
    snr_dict : Dict[str, float]
        Dictionary mapping event names to SNR values
    output_file : str, optional
        Path to save results JSON
    mu : float, optional
        Expected SNR when signal is present
    sigma : float, optional
        Standard deviation of signal distribution

    Returns
    -------
    Dict
        Complete analysis results
    """
    event_names = list(snr_dict.keys())
    snr_list = [snr_dict[name] for name in event_names]

    # Compute Bayes Factor
    bf, diagnostics = bayes_factor(snr_list, mu, sigma)

    # Compute posterior
    pi_grid, posterior = posterior_pi(snr_list, mu, sigma)

    # Credible intervals
    cumulative = np.cumsum(posterior)
    cumulative /= cumulative[-1]

    idx_025 = np.argmin(np.abs(cumulative - 0.025))
    idx_975 = np.argmin(np.abs(cumulative - 0.975))
    idx_median = np.argmin(np.abs(cumulative - 0.5))

    results = {
        'bayes_factor': float(bf),
        'log_bayes_factor': diagnostics['log_bf'],
        'posterior_pi': {
            'mean': diagnostics['pi_mean'],
            'std': diagnostics['pi_std'],
            'median': float(pi_grid[idx_median]),
            'ci_95': [float(pi_grid[idx_025]), float(pi_grid[idx_975])]
        },
        'diagnostics': diagnostics,
        'events': {name: snr for name, snr in snr_dict.items()},
        'interpretation': interpret_bayes_factor(bf)
    }

    if output_file:
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)

    return results


def interpret_bayes_factor(bf: float) -> str:
    """
    Interpret Bayes Factor according to Kass & Raftery (1995) scale.

    Parameters
    ----------
    bf : float
        Bayes Factor

    Returns
    -------
    str
        Interpretation string
    """
    log_bf = np.log10(bf)

    if log_bf < 0:
        return "Negative evidence (favors H0)"
    elif log_bf < 0.5:
        return "Barely worth mentioning"
    elif log_bf < 1:
        return "Substantial evidence for H1"
    elif log_bf < 2:
        return "Strong evidence for H1"
    else:
        return "Decisive evidence for H1"


# Example usage
if __name__ == "__main__":
    # Example: GWTC-1 events with hypothetical SNRs at 141.7001 Hz
    example_snrs = {
        'GW150914': 8.2,
        'GW151012': 4.5,
        'GW151226': 6.5,
        'GW170104': 7.9,
        'GW170608': 5.1,
        'GW170729': 4.8,
        'GW170809': 5.5,
        'GW170814': 6.2,
        'GW170817': 12.5,
        'GW170818': 5.9,
        'GW170823': 4.3
    }

    results = analyze_multi_event(example_snrs, output_file='bayes/example_results.json')

    print("=" * 60)
    print("HIERARCHICAL BAYESIAN ANALYSIS - 141.7001 Hz")
    print("=" * 60)
    print(f"Bayes Factor: {results['bayes_factor']:.2e}")
    print(f"log₁₀(BF): {np.log10(results['bayes_factor']):.2f}")
    print(f"Interpretation: {results['interpretation']}")
    print("\nPosterior π (fraction with signal):")
    print(f"  Mean: {results['posterior_pi']['mean']:.3f}")
    print(f"  Median: {results['posterior_pi']['median']:.3f}")
    print(f"  95% CI: [{results['posterior_pi']['ci_95'][0]:.3f}, {results['posterior_pi']['ci_95'][1]:.3f}]")
    print("=" * 60)
