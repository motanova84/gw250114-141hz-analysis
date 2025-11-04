#!/usr/bin/env python3
"""
Tests for QCAL LLM Core Module

Tests the implementation of QCALLLMCore for evaluating LLM responses
against QCAL (Quantum Coherent Amplification Logic) standards.
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from qcal_llm_core import QCALLLMCore


class TestQCALLLMCoreInitialization:
    """Test initialization and parameter handling."""

    def test_default_initialization(self):
        """Test initialization with default parameters."""
        core = QCALLLMCore()
        assert core.f0 == 141.7001
        assert core.phi == 0.0
        assert core.tau == 0.07
        assert core.alpha == 1.0
        assert core.epsilon == pytest.approx(0.015, abs=1e-6)

    def test_custom_initialization(self):
        """Test initialization with custom parameters."""
        core = QCALLLMCore(alpha=1.5, f0=150.0, phi=np.pi/4, tau=0.1, epsilon=0.02, user_A_eff=0.9)
        assert core.f0 == 150.0
        assert core.phi == pytest.approx(np.pi/4, abs=1e-6)
        assert core.tau == 0.1
        assert core.alpha == 1.5
        # epsilon should be scaled by user_A_eff
        expected_epsilon = 0.02 * (0.9 / 0.85)
        assert core.epsilon == pytest.approx(expected_epsilon, abs=1e-6)

    def test_user_A_eff_scaling(self):
        """Test that epsilon scales correctly with user_A_eff."""
        core_default = QCALLLMCore(epsilon=0.015, user_A_eff=0.85)
        core_scaled = QCALLLMCore(epsilon=0.015, user_A_eff=0.92)

        ratio = core_scaled.epsilon / core_default.epsilon
        expected_ratio = 0.92 / 0.85
        assert ratio == pytest.approx(expected_ratio, abs=1e-6)

    def test_ground_truth_database(self):
        """Test that ground truth database is properly initialized."""
        core = QCALLLMCore()
        assert 'f0' in core.ground_truth_db
        assert 'zeta_prime_half' in core.ground_truth_db
        assert 'phi_cubed' in core.ground_truth_db
        assert 'snr_gw150914' in core.ground_truth_db

        # Check values
        assert core.ground_truth_db['f0'] == 141.7001
        assert core.ground_truth_db['zeta_prime_half'] == pytest.approx(-1.4603545, abs=1e-6)
        assert core.ground_truth_db['phi_cubed'] == pytest.approx(4.236067977, abs=1e-6)
        assert core.ground_truth_db['snr_gw150914'] == 20.95

    def test_benchmark_queries(self):
        """Test that benchmark queries are properly initialized."""
        core = QCALLLMCore()
        assert len(core.benchmark_queries) == 5
        assert all(isinstance(q, str) for q in core.benchmark_queries)
        assert "141.7001 Hz" in core.benchmark_queries[0]
        assert "GW150914" in core.benchmark_queries[1]


class TestSIPModulation:
    """Test Signal Integration Protocol modulation."""

    def test_sip_modulate_shape(self):
        """Test that SIP modulation returns correct shape."""
        core = QCALLLMCore()
        t = np.linspace(0, 1, 100)
        weights = core.sip_modulate(t)
        assert weights.shape == t.shape

    def test_sip_modulate_initial_value(self):
        """Test SIP modulation at t=0."""
        core = QCALLLMCore(alpha=1.0, epsilon=0.015, user_A_eff=0.85)
        t = np.array([0.0])
        weights = core.sip_modulate(t)
        # At t=0: envelope=1, modulation=cos(0)=1
        # weight = alpha * (1 + epsilon * 1) = 1.0 * (1 + 0.015) = 1.015
        expected = 1.0 * (1 + 0.015 * 1.0)
        assert weights[0] == pytest.approx(expected, abs=1e-6)

    def test_sip_modulate_decay(self):
        """Test exponential decay in SIP modulation."""
        core = QCALLLMCore(tau=0.07)
        t = np.array([0.0, 0.07, 0.14])
        weights = core.sip_modulate(t)
        # Envelope decays as e^(-t/tau)
        # At t=tau, envelope = e^(-1) ≈ 0.368
        assert weights[0] > weights[1] > weights[2]

    def test_sip_modulate_frequency(self):
        """Test oscillation frequency in SIP modulation."""
        core = QCALLLMCore(f0=141.7001)
        # Sample at frequency resolution
        t = np.linspace(0, 0.1, 1000)
        weights = core.sip_modulate(t)
        # Check oscillation exists
        assert np.max(weights) > np.mean(weights)
        assert np.min(weights) < np.mean(weights)

    def test_sip_modulate_mean_near_alpha(self):
        """Test that mean weight is near alpha for small epsilon."""
        core = QCALLLMCore(alpha=1.0, epsilon=0.015, user_A_eff=0.85)
        t = np.linspace(0, 1, 1000)
        weights = core.sip_modulate(t)
        # Mean should be close to alpha
        assert np.mean(weights) == pytest.approx(1.0, abs=0.01)


class TestPsiResponse:
    """Test Ψ response computation."""

    def test_compute_psi_response_basic(self):
        """Test basic Ψ computation."""
        core = QCALLLMCore()
        psi = core.compute_psi_response(8.2, 0.88)
        expected = 8.2 * (0.88 ** 2)
        assert psi == pytest.approx(expected, abs=1e-6)
        assert psi == pytest.approx(6.3501, abs=1e-4)

    def test_compute_psi_response_zero_coherence(self):
        """Test Ψ with zero coherence."""
        core = QCALLLMCore()
        psi = core.compute_psi_response(10.0, 0.0)
        assert psi == 0.0

    def test_compute_psi_response_unit_coherence(self):
        """Test Ψ with unit coherence."""
        core = QCALLLMCore()
        kld_inv = 5.0
        psi = core.compute_psi_response(kld_inv, 1.0)
        assert psi == kld_inv

    def test_is_coherent_above_threshold(self):
        """Test coherence check above threshold."""
        core = QCALLLMCore()
        is_coh, psi = core.is_coherent(8.2, 0.88, threshold=5.0)
        assert is_coh is True
        assert psi == pytest.approx(6.3501, abs=1e-4)

    def test_is_coherent_below_threshold(self):
        """Test coherence check below threshold."""
        core = QCALLLMCore()
        is_coh, psi = core.is_coherent(3.0, 0.5, threshold=5.0)
        assert is_coh is False
        assert psi == pytest.approx(0.75, abs=1e-6)

    def test_is_coherent_at_threshold(self):
        """Test coherence check exactly at threshold."""
        core = QCALLLMCore()
        # Set kld_inv such that psi = threshold
        # psi = kld_inv * coherence^2
        # 5.0 = kld_inv * 0.8^2
        # kld_inv = 5.0 / 0.64 = 7.8125
        is_coh, psi = core.is_coherent(7.8125, 0.8, threshold=5.0)
        assert is_coh is True
        assert psi == pytest.approx(5.0, abs=1e-6)


class TestCoherenceComputation:
    """Test semantic coherence computation."""

    def test_compute_coherence_all_symbols(self):
        """Test coherence with all symbols present."""
        core = QCALLLMCore()
        text = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz"
        coherence = core.compute_coherence(text)
        assert coherence == 1.0

    def test_compute_coherence_no_symbols(self):
        """Test coherence with no symbols."""
        core = QCALLLMCore()
        text = "This is random text without any relevant symbols"
        coherence = core.compute_coherence(text)
        assert coherence == 0.0

    def test_compute_coherence_partial_symbols(self):
        """Test coherence with partial symbol matches."""
        core = QCALLLMCore()
        # Only f0 present
        text = "The frequency is 141.7001 Hz"
        coherence = core.compute_coherence(text)
        assert coherence == pytest.approx(1/3, abs=1e-6)

        # f0 and zeta present
        text2 = "ζ'(1/2) gives 141.7 Hz"
        coherence2 = core.compute_coherence(text2)
        assert coherence2 == pytest.approx(2/3, abs=1e-6)

    def test_compute_coherence_case_insensitive(self):
        """Test that coherence matching is case-insensitive."""
        core = QCALLLMCore()
        text = "Zeta' gives 141.7 HZ"
        coherence = core.compute_coherence(text)
        assert coherence > 0.0

    def test_compute_coherence_alternative_notations(self):
        """Test alternative notations for symbols."""
        core = QCALLLMCore()
        # Test phi^3 notation
        text1 = "phi^3 = 4.236"
        coherence1 = core.compute_coherence(text1)
        assert coherence1 >= 1/3  # At least phi_cubed matches

        # Test numeric values with symbols
        text2 = "Values: φ³ = 4.236 and ζ'(1/2) at 141.7 Hz"
        coherence2 = core.compute_coherence(text2)
        assert coherence2 == 1.0


class TestEvaluate:
    """Test full LLM response evaluation."""

    def test_evaluate_structure(self):
        """Test that evaluate returns correct structure."""
        core = QCALLLMCore()
        result = core.evaluate("Some text", "Some query")

        # Check all required keys
        assert 'mean_psi' in result
        assert 'psi_ci_95' in result
        assert 'coherent' in result
        assert 'coherence' in result
        assert 'kld_inv' in result
        assert 'matches' in result

    def test_evaluate_types(self):
        """Test that evaluate returns correct types."""
        core = QCALLLMCore()
        result = core.evaluate("Some text", "Some query")

        assert isinstance(result['mean_psi'], float)
        assert isinstance(result['psi_ci_95'], tuple)
        assert isinstance(result['coherent'], bool)
        assert isinstance(result['coherence'], float)
        assert isinstance(result['kld_inv'], float)
        assert isinstance(result['matches'], int)

    def test_evaluate_confidence_interval(self):
        """Test that confidence interval is valid."""
        core = QCALLLMCore()
        result = core.evaluate("141.7001 Hz", "query")

        ci = result['psi_ci_95']
        assert len(ci) == 2
        assert ci[0] <= result['mean_psi'] <= ci[1]

    def test_evaluate_with_no_matches(self):
        """Test evaluation with no claim matches."""
        np.random.seed(42)
        core = QCALLLMCore()
        result = core.evaluate("Random unrelated text", "query")

        assert result['matches'] == 0
        assert result['coherence'] == 0.0
        # KLD can be negative with small log values
        assert isinstance(result['kld_inv'], float)

    def test_evaluate_with_all_matches(self):
        """Test evaluation with all claims matching."""
        np.random.seed(42)
        core = QCALLLMCore()
        text = "f₀ = 141.7001 Hz, ζ'(1/2) = -1.460, φ³ = 4.236, SNR = 20.95"
        result = core.evaluate(text, "query")

        assert result['matches'] == 4
        assert result['coherence'] == 1.0
        assert result['coherent'] is True

    def test_evaluate_reproducibility(self):
        """Test that evaluation is reproducible with same seed."""
        text = "141.7001 Hz and 4.236"
        query = "test"

        np.random.seed(123)
        core1 = QCALLLMCore()
        result1 = core1.evaluate(text, query, n_bootstrap=50)

        np.random.seed(123)
        core2 = QCALLLMCore()
        result2 = core2.evaluate(text, query, n_bootstrap=50)

        assert result1['mean_psi'] == pytest.approx(result2['mean_psi'], abs=1e-10)
        assert result1['kld_inv'] == pytest.approx(result2['kld_inv'], abs=1e-10)

    def test_evaluate_verified_output(self):
        """Test evaluation against verified output from problem statement."""
        np.random.seed(42)
        core = QCALLLMCore(user_A_eff=0.92)
        response_mock = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz. ζ'(1/2) = -1.460, φ³ = 4.236. Ψ coherent."
        result = core.evaluate(response_mock, "Deriva f₀")

        # Expected: mean_psi = 8.20 ± 0.15
        assert result['mean_psi'] == pytest.approx(8.20, abs=0.15)
        assert result['coherent'] is True

        # Check CI contains mean
        ci = result['psi_ci_95']
        assert ci[0] <= result['mean_psi'] <= ci[1]


class TestIntegration:
    """Integration tests for complete workflows."""

    def test_full_workflow(self):
        """Test complete evaluation workflow."""
        np.random.seed(42)
        core = QCALLLMCore(user_A_eff=0.92)

        # Generate time series
        t = np.linspace(0, 1, 1000)
        weights = core.sip_modulate(t)
        assert len(weights) == 1000

        # Test coherence check
        is_valid, psi_val = core.is_coherent(8.2, 0.88)
        assert is_valid is True
        assert psi_val == pytest.approx(6.3501, abs=1e-4)

        # Test evaluation
        response = "f₀ = 141.7001 Hz with ζ'(1/2) = -1.460 and φ³ = 4.236"
        result = core.evaluate(response, "Deriva f₀")
        assert result['coherent'] is True
        assert result['coherence'] == 1.0

    def test_benchmark_queries_accessible(self):
        """Test that benchmark queries can be used for evaluation."""
        core = QCALLLMCore()

        # Use first benchmark query
        query = core.benchmark_queries[0]
        assert "141.7001 Hz" in query

        # Create a response
        response = "The fundamental frequency f₀ = 141.7001 Hz is derived from ζ'(1/2) = -1.460"
        result = core.evaluate(response, query)

        assert result['matches'] >= 1
        assert result['coherence'] > 0.0

    def test_parameter_sensitivity(self):
        """Test sensitivity to user_A_eff parameter."""
        np.random.seed(42)

        core1 = QCALLLMCore(user_A_eff=0.85)
        core2 = QCALLLMCore(user_A_eff=0.92)

        # epsilon should be different
        assert core1.epsilon != core2.epsilon

        # SIP modulation should differ
        t = np.array([0.5])
        weights1 = core1.sip_modulate(t)
        weights2 = core2.sip_modulate(t)
        assert weights1[0] != weights2[0]


if __name__ == "__main__":
    """Run tests with pytest."""
    pytest.main([__file__, "-v", "--tb=short"])
