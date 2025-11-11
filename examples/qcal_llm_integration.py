#!/usr/bin/env python3
"""
QCAL-LLM Integration Example

Demonstrates how to use the QCAL module to evaluate text coherence
and integrate with LLM evaluation pipelines.
"""

import sys  # noqa: E402

sys.path.insert(0, '.')

from qcal.coherence import psi_score  # noqa: E402
from qcal.metrics import kl_divergence, snr, strich_rate  # noqa: E402


def evaluate_text(text: str, label: str = "Sample"):
    """
    Evaluate a text using all QCAL metrics.

    Args:
        text: Text to evaluate
        label: Label for the text

    Returns:
        dict: Dictionary with all metrics
    """
    psi = psi_score(text)
    kld = kl_divergence(text)
    kld_inv = 1 / kld if kld > 0 else 0
    snr_val = snr(text)
    strich = strich_rate(text)

    results = {
        "label": label,
        "psi": psi,
        "kld": kld,
        "kld_inv": kld_inv,
        "snr": snr_val,
        "strich_rate": strich
    }

    return results


def print_evaluation(results: dict):
    """Pretty print evaluation results."""
    print(f"\n{'='*70}")
    print(f"📊 Evaluación QCAL: {results['label']}")
    print(f"{'='*70}")
    print(f"  Ψ (Coherencia):        {results['psi']:.3f}")
    print(f"  SNR:                   {results['snr']:.3f}")
    print(f"  KLD:                   {results['kld']:.3f}")
    print(f"  KLD⁻¹:                 {results['kld_inv']:.3f}")
    print(f"  ∴ Rate:                {results['strich_rate']:.4f}")
    print(f"{'='*70}")

    # Coherence threshold check
    coherent = results['psi'] >= 5.0
    print(f"\n✓ Estado: {'COHERENTE' if coherent else 'NO COHERENTE'}")
    print(f"  (Umbral Ψ ≥ 5.0: {results['psi']:.3f} {'≥' if coherent else '<'} 5.0)")


def main():
    """Run example evaluations."""
    print("\n" + "="*70)
    print("QCAL-LLM Integration Example")
    print("Quantum Coherence Analysis Library")
    print("="*70)

    # Example 1: High coherence text (Spanish keywords)
    text1 = """
    La intención de este análisis es demostrar la coherencia del modelo.
    El propósito fundamental es validar que f₀ = 141.7001 Hz representa
    una frecuencia de coherencia universal. ∴ La derivación matemática
    confirma que esta frecuencia emerge naturalmente del análisis espectral.
    """

    results1 = evaluate_text(text1, "Texto con Alta Coherencia")
    print_evaluation(results1)

    # Example 2: Technical text (English)
    text2 = """
    The fundamental frequency f₀ = 141.7001 Hz is derived from the Riemann
    zeta function zero at s=1/2, scaled by the golden ratio cubed. This
    represents a universal resonance pattern detected in gravitational wave
    ringdown phases. ∴ The spectral analysis confirms this prediction.
    """

    results2 = evaluate_text(text2, "Texto Técnico (Inglés)")
    print_evaluation(results2)

    # Example 3: Low coherence text (random)
    text3 = """
    This is just some random text without any specific meaning or
    connection to the quantum coherence framework or the fundamental
    frequency analysis. It lacks the key concepts and symbols.
    """

    results3 = evaluate_text(text3, "Texto de Baja Coherencia")
    print_evaluation(results3)

    # Summary comparison
    print("\n" + "="*70)
    print("📈 Comparación de Resultados")
    print("="*70)
    print(f"{'Texto':<35} {'Ψ':>8} {'SNR':>8} {'KLD⁻¹':>8} {'∴':>8}")
    print("-"*70)

    for res in [results1, results2, results3]:
        print(f"{res['label']:<35} {res['psi']:>8.3f} {res['snr']:>8.3f} "
              f"{res['kld_inv']:>8.3f} {res['strich_rate']:>8.4f}")

    print("="*70)
    print("\n✅ Ejemplo completado")
    print("\nPara más información, ver:")
    print("  - qcal/README.md")
    print("  - notebooks/benchmark_llama4.ipynb")
    print("  - tests/test_qcal_metrics.py")


if __name__ == "__main__":
    main()
