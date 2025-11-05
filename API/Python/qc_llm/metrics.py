"""
Core metrics for quantum coherence computation
"""

import numpy as np
from typing import Dict, List

# Fundamental constant
F0 = 141.7001  # Hz

def compute_frequency_alignment(text: str, target_freq: float = F0) -> float:
    """
    Compute alignment with target frequency
    
    Args:
        text: Input text to analyze
        target_freq: Target frequency (default: f₀ = 141.7001 Hz)
    
    Returns:
        Alignment score [0, 1]
    """
    # Tokenize
    tokens = text.split()
    n = len(tokens)
    
    if n < 2:
        return 0.0
    
    # Simulate spectral analysis
    # In practice: FFT of embedding vectors
    frequencies = np.fft.fftfreq(n, d=1.0)
    
    # Normalize target frequency to text domain
    norm_target = target_freq / 1000.0
    
    # Find closest peak
    # Placeholder: random for now
    peak_freq = np.random.uniform(0.1, 0.2)
    
    # Compute alignment
    alignment = np.exp(-abs(peak_freq - norm_target))
    
    return float(np.clip(alignment, 0, 1))

def compute_quantum_entropy(text: str) -> float:
    """
    Compute quantum entropy of text
    
    Based on token diversity and distribution.
    
    Returns:
        Entropy score [0, 1]
    """
    tokens = text.split()
    if not tokens:
        return 0.0
    
    # Token frequency distribution
    unique_tokens = set(tokens)
    n_unique = len(unique_tokens)
    n_total = len(tokens)
    
    # Shannon entropy
    freq_dist = np.array([tokens.count(t) / n_total for t in unique_tokens])
    entropy = -np.sum(freq_dist * np.log2(freq_dist + 1e-10))
    
    # Normalize to [0, 1]
    max_entropy = np.log2(n_total)
    normalized = entropy / max_entropy if max_entropy > 0 else 0.0
    
    return float(normalized)

def compute_coherence_score(text: str) -> Dict[str, float]:
    """
    Compute complete coherence score
    
    Returns:
        Dictionary with:
        - coherence: Overall coherence score
        - frequency_alignment: Alignment with f₀
        - quantum_entropy: Quantum entropy
        - recommendation: Text recommendation
    """
    freq_align = compute_frequency_alignment(text)
    entropy = compute_quantum_entropy(text)
    
    # Weighted average
    coherence = 0.6 * freq_align + 0.4 * entropy
    
    # Recommendation
    if coherence > 0.8:
        recommendation = "HIGH COHERENCE - Excellent quality"
    elif coherence > 0.6:
        recommendation = "MODERATE COHERENCE - Good quality"
    elif coherence > 0.4:
        recommendation = "LOW COHERENCE - Consider rephrasing"
    else:
        recommendation = "VERY LOW COHERENCE - Significant revision needed"
    
    return {
        "coherence": coherence,
        "frequency_alignment": freq_align,
        "quantum_entropy": entropy,
        "recommendation": recommendation
    }
