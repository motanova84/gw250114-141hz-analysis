"""
Unit tests for QCALLLMCore module
"""

import pytest
import sys
import numpy as np
from pathlib import Path

# Add the noesis-qcal-llm directory to the path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'noesis-qcal-llm'))

from core import QCALLLMCore


class TestQCALLLMCore:
    """Test suite for QCALLLMCore class"""

    def test_initialization_default(self):
        """Test default initialization"""
        core = QCALLLMCore()
        assert core.f0 == 141.7001
        assert core.phi == 0.0
        assert core.tau == 0.07
        assert core.alpha == 1.0
        assert abs(core.epsilon - 0.015) < 1e-6

    def test_initialization_custom_user_A_eff(self):
        """Test initialization with custom user_A_eff"""
        core = QCALLLMCore(user_A_eff=0.92)
        # epsilon should be adjusted: 0.015 * (0.92 / 0.85) ≈ 0.0162
        expected_epsilon = 0.015 * (0.92 / 0.85)
        assert abs(core.epsilon - expected_epsilon) < 1e-6

    def test_ground_truth_db(self):
        """Test ground_truth_db contains expected values"""
        core = QCALLLMCore()
        assert 'f0' in core.ground_truth_db
        assert 'zeta_prime_half' in core.ground_truth_db
        assert 'phi_cubed' in core.ground_truth_db
        assert 'snr_gw150914' in core.ground_truth_db
        assert core.ground_truth_db['f0'] == 141.7001
        assert core.ground_truth_db['zeta_prime_half'] == -1.460
        assert core.ground_truth_db['phi_cubed'] == 4.236
        assert core.ground_truth_db['snr_gw150914'] == 20.95

    def test_benchmark_queries(self):
        """Test benchmark_queries list exists and has content"""
        core = QCALLLMCore()
        assert len(core.benchmark_queries) == 5
        assert "Deriva f₀ = 141.7001 Hz desde ζ'(1/2) y φ" in core.benchmark_queries

    def test_sip_modulate(self):
        """Test SIP modulation function"""
        core = QCALLLMCore(user_A_eff=0.92)
        t = np.linspace(0, 1, 1000)
        weights = core.sip_modulate(t)

        # Check output shape
        assert len(weights) == 1000

        # Check that weights are reasonable (not NaN or Inf)
        assert np.all(np.isfinite(weights))

        # Check variance is low (as mentioned in problem statement: Var(weights)=1.24e-4)
        variance = np.var(weights)
        assert variance < 1e-3  # Should be low

    def test_compute_psi_response(self):
        """Test Ψ response computation"""
        core = QCALLLMCore()
        kld_inv = 8.2
        semantic_coherence = 0.88
        psi = core.compute_psi_response(kld_inv, semantic_coherence)

        # Ψ = kld_inv × semantic_coherence²
        expected_psi = 8.2 * (0.88 ** 2)
        assert abs(psi - expected_psi) < 1e-6

    def test_is_coherent_true(self):
        """Test is_coherent returns True for high coherence"""
        core = QCALLLMCore()
        is_valid, psi_val = core.is_coherent(8.2, 0.88, threshold=5.0)

        # Expected: Ψ=6.3501 ≥ 5.0 → True
        assert is_valid is True
        assert abs(psi_val - 6.3501) < 0.01

    def test_is_coherent_false(self):
        """Test is_coherent returns False for low coherence"""
        core = QCALLLMCore()
        is_valid, psi_val = core.is_coherent(1.0, 0.5, threshold=5.0)

        # Ψ = 1.0 × 0.5² = 0.25 < 5.0 → False
        assert is_valid is False
        assert abs(psi_val - 0.25) < 1e-6

    def test_compute_coherence_full_match(self):
        """Test compute_coherence with all symbols present"""
        core = QCALLLMCore()
        text = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz. Ψ coherent."
        coherence = core.compute_coherence(text)

        # All 3 symbols present: f0, zeta', phi³
        assert coherence == 1.0

    def test_compute_coherence_partial_match(self):
        """Test compute_coherence with some symbols"""
        core = QCALLLMCore()
        text = "The frequency is 141.7001 Hz"
        coherence = core.compute_coherence(text)

        # Only f0 present: 1/3
        assert abs(coherence - 1/3) < 1e-6

    def test_compute_coherence_no_match(self):
        """Test compute_coherence with no symbols"""
        core = QCALLLMCore()
        text = "This is just regular text without symbols"
        coherence = core.compute_coherence(text)

        # No symbols present: 0/3
        assert coherence == 0.0

    def test_evaluate_high_coherence(self):
        """Test evaluate method with high coherence text"""
        core = QCALLLMCore(user_A_eff=0.92)
        response_mock = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz. Ψ coherent."
        eval_res = core.evaluate(response_mock, "Deriva f₀")

        # Check return structure
        assert 'mean_psi' in eval_res
        assert 'coherent' in eval_res
        assert 'coherence' in eval_res

        # Check values match problem statement
        assert eval_res['coherent']
        assert eval_res['coherence'] == 1.0
        assert abs(eval_res['mean_psi'] - 8.20) < 0.1

    def test_evaluate_low_coherence(self):
        """Test evaluate method with low coherence text"""
        core = QCALLLMCore()
        response = "This is unrelated text"
        eval_res = core.evaluate(response, "Some query")

        # Should have low coherence
        assert eval_res['coherence'] == 0.0
        assert not eval_res['coherent']

    def test_main_execution_output(self):
        """Test that main execution produces expected output"""
        core = QCALLLMCore(user_A_eff=0.92)
        t = np.linspace(0, 1, 1000)
        _ = core.sip_modulate(t)  # Test modulation works
        is_valid, psi_val = core.is_coherent(8.2, 0.88)
        response_mock = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz. Ψ coherent."
        eval_res = core.evaluate(response_mock, "Deriva f₀")

        # Verify expected values from problem statement
        assert abs(psi_val - 6.3501) < 0.01
        assert is_valid is True
        assert abs(eval_res['mean_psi'] - 8.20) < 0.1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
