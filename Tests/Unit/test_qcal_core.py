"""
Unit tests for QCAL-LLM Core module
Tests the implementation of QCALLLMCore with SIP modulation
"""

import pytest
import numpy as np
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2] / 'API' / 'Python'))

from qc_llm.core import QCALLLMCore


class TestQCALLLMCore:
    """Test suite for QCALLLMCore class."""
    
    def test_initialization_default_params(self):
        """Test core initialization with default parameters"""
        core = QCALLLMCore()
        
        assert core.f0 == 141.7001
        assert core.alpha == 1.0
        assert core.phi == 0.0
        assert core.tau == 0.07
        assert abs(core.epsilon - 0.015) < 1e-6
        assert core.user_A_eff == 0.85
    
    def test_initialization_custom_params(self):
        """Test core initialization with custom parameters"""
        core = QCALLLMCore(
            alpha=1.5,
            f0=150.0,
            phi=0.5,
            tau=0.1,
            epsilon=0.02,
            user_A_eff=0.9
        )
        
        assert core.f0 == 150.0
        assert core.alpha == 1.5
        assert core.phi == 0.5
        assert core.tau == 0.1
        assert core.user_A_eff == 0.9
        # epsilon should be adapted: 0.02 * (0.9 / 0.85)
        expected_epsilon = 0.02 * (0.9 / 0.85)
        assert abs(core.epsilon - expected_epsilon) < 1e-6
    
    def test_ground_truth_db(self):
        """Test ground truth database is properly initialized"""
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
        """Test benchmark queries are defined"""
        core = QCALLLMCore()
        
        assert len(core.benchmark_queries) == 5
        assert isinstance(core.benchmark_queries, list)
        assert all(isinstance(q, str) for q in core.benchmark_queries)
    
    def test_sip_modulate_shape(self):
        """Test SIP modulation output shape"""
        core = QCALLLMCore()
        t = np.linspace(0, 1, 1000)
        weights = core.sip_modulate(t)
        
        assert weights.shape == t.shape
        assert len(weights) == 1000
    
    def test_sip_modulate_envelope_decay(self):
        """Test SIP modulation envelope decays exponentially"""
        core = QCALLLMCore()
        t = np.linspace(0, 1, 1000)
        weights = core.sip_modulate(t)
        
        # At t=0, envelope = 1
        # At large t, envelope approaches 0
        # Check that maximum is near start
        max_idx = np.argmax(np.abs(weights - core.alpha))
        assert max_idx < 100  # Should be in first 10%
        
        # Check decay: later values should be closer to alpha
        early_deviation = np.mean(np.abs(weights[:100] - core.alpha))
        late_deviation = np.mean(np.abs(weights[-100:] - core.alpha))
        assert late_deviation < early_deviation
    
    def test_sip_modulate_frequency(self):
        """Test SIP modulation has correct frequency component"""
        core = QCALLLMCore()
        # Use shorter time window where envelope is still significant
        t = np.linspace(0, 0.5, 5000)  # 0.5 seconds
        weights = core.sip_modulate(t)
        
        # Remove DC component
        weights_centered = weights - core.alpha
        
        # Count peaks instead of zero crossings (more robust with envelope)
        from scipy.signal import find_peaks
        peaks, _ = find_peaks(weights_centered)
        
        # Expected number of peaks in 0.5 seconds at 141.7 Hz
        # With exponential decay, we expect fewer peaks
        expected_peaks = core.f0 * 0.5  # ~70 peaks
        actual_peaks = len(peaks)
        
        # Allow 50% tolerance due to envelope decay and edge effects
        assert abs(actual_peaks - expected_peaks) < expected_peaks * 0.5
    
    def test_compute_psi_response_known_value(self):
        """Test Ψ computation with known values from problem statement"""
        core = QCALLLMCore()
        
        # From problem: kld_inv=8.2, coherence=0.88 → Ψ=6.3501
        psi = core.compute_psi_response(8.2, 0.88)
        expected = 8.2 * (0.88 ** 2)  # 8.2 * 0.7744 = 6.35008
        
        assert abs(psi - expected) < 1e-4
        assert abs(psi - 6.3501) < 0.001
    
    def test_compute_psi_response_edge_cases(self):
        """Test Ψ computation edge cases"""
        core = QCALLLMCore()
        
        # Perfect coherence
        psi_perfect = core.compute_psi_response(10.0, 1.0)
        assert psi_perfect == 10.0
        
        # Zero coherence
        psi_zero = core.compute_psi_response(10.0, 0.0)
        assert psi_zero == 0.0
        
        # Half coherence
        psi_half = core.compute_psi_response(8.0, 0.5)
        assert psi_half == 8.0 * 0.25
    
    def test_is_coherent_above_threshold(self):
        """Test coherence validation above threshold"""
        core = QCALLLMCore()
        
        is_valid, psi_val = core.is_coherent(kld_inv=8.2, semantic_coherence=0.88)
        
        assert is_valid is True
        assert abs(psi_val - 6.3501) < 0.001
        assert psi_val >= 5.0
    
    def test_is_coherent_below_threshold(self):
        """Test coherence validation below threshold"""
        core = QCALLLMCore()
        
        is_valid, psi_val = core.is_coherent(kld_inv=3.0, semantic_coherence=0.5)
        
        assert is_valid is False
        assert psi_val < 5.0
        expected = 3.0 * 0.25
        assert abs(psi_val - expected) < 1e-6
    
    def test_is_coherent_at_threshold(self):
        """Test coherence validation exactly at threshold"""
        core = QCALLLMCore()
        
        # Find values that give exactly 5.0
        # Ψ = kld_inv × coherence² = 5.0
        # If coherence = 0.8, then kld_inv = 5.0 / 0.64 ≈ 7.8125
        is_valid, psi_val = core.is_coherent(kld_inv=7.8125, semantic_coherence=0.8)
        
        assert is_valid is True
        assert abs(psi_val - 5.0) < 1e-6
    
    def test_is_coherent_custom_threshold(self):
        """Test coherence validation with custom threshold"""
        core = QCALLLMCore()
        
        is_valid_low, psi_val = core.is_coherent(
            kld_inv=3.0, 
            semantic_coherence=0.5, 
            threshold=0.5
        )
        
        assert is_valid_low is True  # 0.75 > 0.5
        assert psi_val >= 0.5
    
    def test_compute_coherence_full_match(self):
        """Test coherence computation with all symbols present"""
        core = QCALLLMCore()
        
        text = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz. Ψ coherent."
        coherence = core.compute_coherence(text)
        
        assert coherence == 1.0  # All 3 symbols present
    
    def test_compute_coherence_partial_match(self):
        """Test coherence computation with partial symbol match"""
        core = QCALLLMCore()
        
        text = "The frequency f₀ = 141.7 Hz is important"
        coherence = core.compute_coherence(text)
        
        assert coherence == pytest.approx(1/3, abs=0.01)  # Only f0 present
    
    def test_compute_coherence_no_match(self):
        """Test coherence computation with no symbols"""
        core = QCALLLMCore()
        
        text = "This is just regular text without any symbols"
        coherence = core.compute_coherence(text)
        
        assert coherence == 0.0
    
    def test_compute_coherence_alternative_notations(self):
        """Test coherence with alternative symbol notations"""
        core = QCALLLMCore()
        
        # Test phi**3 notation
        text1 = "phi**3 = 4.236"
        assert core.compute_coherence(text1) > 0
        
        # Test zeta' notation
        text2 = "zeta'(1/2) is negative"
        assert core.compute_coherence(text2) > 0
        
        # Test f0 notation
        text3 = "f0 = 141.7 Hz"
        assert core.compute_coherence(text3) > 0
    
    def test_evaluate_high_coherence(self):
        """Test evaluate method with high coherence text"""
        core = QCALLLMCore()
        
        text = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz"
        result = core.evaluate(text, "Deriva f₀")
        
        assert 'mean_psi' in result
        assert 'coherent' in result
        assert 'coherence' in result
        assert 'kld_inv' in result
        
        assert result['coherence'] == 1.0
        assert result['coherent'] is True
        assert result['mean_psi'] > 0
    
    def test_evaluate_low_coherence(self):
        """Test evaluate method with low coherence text"""
        core = QCALLLMCore()
        
        text = "This is random text without scientific content"
        result = core.evaluate(text, "Test query")
        
        assert result['coherence'] == 0.0
        assert result['coherent'] is False
        assert result['mean_psi'] == 0.0
    
    def test_evaluate_medium_coherence(self):
        """Test evaluate method with medium coherence text"""
        core = QCALLLMCore()
        
        text = "The frequency 141.7 Hz appears in gravitational waves"
        result = core.evaluate(text)
        
        assert 0 < result['coherence'] < 1
        assert isinstance(result['coherent'], bool)
        assert result['mean_psi'] > 0
    
    def test_adaptive_epsilon(self):
        """Test that epsilon adapts to user_A_eff"""
        core1 = QCALLLMCore(user_A_eff=0.85)
        core2 = QCALLLMCore(user_A_eff=0.92)
        
        # epsilon should be higher for higher A_eff
        assert core2.epsilon > core1.epsilon
        
        # Check the ratio
        expected_ratio = 0.92 / 0.85
        actual_ratio = core2.epsilon / core1.epsilon
        assert abs(actual_ratio - expected_ratio) < 1e-6
    
    def test_example_from_problem_statement(self):
        """Test the exact example from the problem statement"""
        core = QCALLLMCore()
        t = np.linspace(0, 1, 1000)
        weights = core.sip_modulate(t)
        is_valid, psi_val = core.is_coherent(kld_inv=8.2, semantic_coherence=0.88)
        
        assert is_valid is True
        assert abs(psi_val - 6.3501) < 0.001
        print(f"Ψ_response = {psi_val:.4f} | Coherente: {is_valid}")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
