"""Test suite for QCAL metrics and coherence functions."""
import sys  # noqa: E402

sys.path.insert(0, '.')

from qcal.coherence import psi_score  # noqa: E402
from qcal.metrics import kl_divergence, snr, strich_rate  # noqa: E402


def test_psi_score_basic():
    """Test basic psi_score calculation."""
    text = "intención propósito coherencia test"
    score = psi_score(text)
    assert score > 0, "Psi score should be positive"
    assert isinstance(score, float), "Psi score should be a float"


def test_psi_score_no_keywords():
    """Test psi_score with no keywords."""
    text = "random text without keywords"
    score = psi_score(text)
    assert score == 0, "Psi score should be 0 with no keywords"


def test_kl_divergence_basic():
    """Test basic KL divergence calculation."""
    text = "hello world hello world"
    kld = kl_divergence(text)
    assert kld > 0, "KLD should be positive"
    assert isinstance(kld, float), "KLD should be a float"


def test_snr_basic():
    """Test basic SNR calculation."""
    text = "hello world test data"
    snr_val = snr(text)
    assert snr_val > 0, "SNR should be positive"
    assert snr_val <= 1.0, "SNR should be <= 1.0 for non-empty text"
    assert isinstance(snr_val, float), "SNR should be a float"


def test_snr_all_unique():
    """Test SNR with all unique words."""
    text = "hello world test data"
    snr_val = snr(text)
    # SNR uses epsilon (1e-6) so won't be exactly 1.0
    assert snr_val > 0.99, "SNR should be very close to 1.0 for all unique words"


def test_strich_rate_basic():
    """Test basic strich_rate calculation."""
    text = "some text ∴ more text ∴"
    rate = strich_rate(text)
    assert rate > 0, "Strich rate should be positive when ∴ present"
    assert isinstance(rate, float), "Strich rate should be a float"


def test_strich_rate_no_symbol():
    """Test strich_rate with no ∴ symbol."""
    text = "some text without symbol"
    rate = strich_rate(text)
    assert rate == 0, "Strich rate should be 0 when no ∴ present"


if __name__ == "__main__":
    print("Running QCAL metrics tests...")

    test_psi_score_basic()
    print("✓ test_psi_score_basic passed")

    test_psi_score_no_keywords()
    print("✓ test_psi_score_no_keywords passed")

    test_kl_divergence_basic()
    print("✓ test_kl_divergence_basic passed")

    test_snr_basic()
    print("✓ test_snr_basic passed")

    test_snr_all_unique()
    print("✓ test_snr_all_unique passed")

    test_strich_rate_basic()
    print("✓ test_strich_rate_basic passed")

    test_strich_rate_no_symbol()
    print("✓ test_strich_rate_no_symbol passed")

    print("\n✅ All tests passed!")
