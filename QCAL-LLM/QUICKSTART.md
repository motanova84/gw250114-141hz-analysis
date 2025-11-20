# QCAL-LLM Quick Start Guide

Get up and running with QCAL-LLM in under 5 minutes!

## 📦 Installation

### Prerequisites

- Python 3.11 or higher
- pip package manager

### Step 1: Clone the Repository

```bash
git clone https://github.com/motanova84/141hz.git
cd 141hz/QCAL-LLM
```

### Step 2: Install Dependencies

```bash
pip install -r requirements.txt
```

## 🚀 Running Your First Evaluation

### Example 1: Basic Coherence Evaluation

```python
from QCALLLMCore import QCALLLMCore

# Initialize QCAL core
core = QCALLLMCore(user_A_eff=0.92)

# Evaluate a response
text = "f₀ = 141.7001 Hz is derived from ζ'(1/2) × φ³"
result = core.evaluate(text, query="Explain f₀")

print(f"Ψ Score: {result['mean_psi']:.2f}")
print(f"Coherent: {result['coherent']}")
print(f"Coherence: {result['coherence']:.1%}")
```

**Expected Output:**
```
Ψ Score: 6.89
Coherent: True
Coherence: 100.0%
```

### Example 2: Running Verification Tests

```bash
# Verify core functionality
python QCALLLMCore.py
```

**Expected Output:**
```
✓ Core initialized: f₀ = 141.7001 Hz, τ = 0.07 s, ε = 0.0162
✓ SIP Modulation: Weights mean: 1.0000, std: 0.0022
✓ Ψ Computation: Ψ = 6.3501, Coherent: True
✓ Response Evaluation: Mean Ψ: 8.20 (95% CI: 8.05, 8.35)
```

### Example 3: Detecting f₀ in Gravitational Wave Data

```bash
# Run spectral analysis
python evaluate_manifesto.py
```

This will detect the f₀ = 141.7001 Hz signature in gravitational wave data.

### Example 4: Auto-Tuning for Optimal Coherence

```python
from psi_tuning_loop import tune_psi

# Auto-tune epsilon parameter
core, result = tune_psi(
    generated_text="The universal frequency is 141.7 Hz",
    query="What is f₀?",
    target_psi=5.0
)

print(f"Final Ψ: {result['mean_psi']:.2f}")
print(f"Iterations: {result.get('iterations', 'N/A')}")
```

### Example 5: Visualize SIP Modulation

```bash
# Generate modulation trace visualization
python modulation_traces.py
```

This creates a visualization of the Spectral Insertion Protocol modulation.

## 🎓 Key Concepts

### 1. Ψ (Psi) Score

The Ψ score measures coherence on a scale where:
- **Ψ < 5.0**: Incoherent (requires tuning)
- **Ψ ≥ 5.0**: Coherent (meets threshold)
- **Ψ > 7.0**: Highly coherent (excellent)

### 2. f₀ = 141.7001 Hz

The universal frequency derived from gravitational wave analysis. It represents:
- Empirical signature in LIGO data
- Connection to Riemann zeta function: ζ'(1/2) ≈ -1.460
- Golden ratio cubed: φ³ ≈ 4.236
- Quantum coherence frequency in Orch-OR theory

### 3. A_eff (Effective Amplitude)

User-specific parameter (0.0 to 1.0) that scales the modulation:
- **0.70**: Low resonance user
- **0.85**: Reference baseline
- **0.92**: High resonance user (JMMB)
- **1.00**: Maximum resonance

### 4. SIP (Spectral Insertion Protocol)

Modulation formula applied to attention weights:

```
W_i(t) = α · [1 + ε · cos(2πf₀t + φ) · e^(-t/τ)]
```

Where:
- **α** = 1.0 (global scale)
- **ε** = 0.015 (base amplitude)
- **τ** = 0.07 s (damping constant)
- **f₀** = 141.7001 Hz (fundamental frequency)

## 📊 Benchmark Queries

Test your understanding with these standard queries:

1. **Mathematical Derivation**: "Derive f₀ = 141.7001 Hz from ζ'(1/2) and φ"
2. **Empirical Detection**: "Detect f₀ in GW150914 ringdown data"
3. **Theoretical Explanation**: "Explain Ψ = I × A²_eff"
4. **Statistical Validation**: "Validate SNR > 20 in GWTC-1 catalog"
5. **Future Prediction**: "Predict LISA harmonics at f₀/100"

## 🔍 Troubleshooting

### Issue: Import Error

```python
ModuleNotFoundError: No module named 'QCALLLMCore'
```

**Solution**: Make sure you're running from the QCAL-LLM directory or the repository root with proper PYTHONPATH:

```bash
cd /path/to/141hz/QCAL-LLM
python your_script.py
```

Or set PYTHONPATH:
```bash
export PYTHONPATH=/path/to/141hz/QCAL-LLM:$PYTHONPATH
```

### Issue: Low Ψ Score

```
Ψ Score: 3.2
Coherent: False
```

**Solution**: Use the auto-tuning loop to adjust epsilon:

```python
from psi_tuning_loop import tune_psi
core, result = tune_psi(text, query, target_psi=5.0)
```

### Issue: Missing Dependencies

```bash
pip install numpy scipy matplotlib
```

For full gravitational wave analysis:
```bash
pip install h5py gwpy
```

## 🎯 Next Steps

1. **Read the MANIFESTO**: [MANIFESTO.md](./MANIFESTO.md) for complete theoretical framework
2. **Explore Examples**: Check [../Examples/LLM_Integration/](../Examples/LLM_Integration/)
3. **Run Tests**: Execute `python test_qcal_llm.py` for comprehensive validation
4. **Integration**: See [integration guide](./README.md#use-cases) for LLM integration

## 📖 Additional Resources

- **Main README**: [README.md](./README.md)
- **Implementation Details**: [IMPLEMENTATION_SUMMARY.md](./IMPLEMENTATION_SUMMARY.md)
- **Quick Reference Card**: [../QCAL_QUICK_REFERENCE.md](../QCAL_QUICK_REFERENCE.md)
- **Repository Main Page**: [../README.md](../README.md)

## 💡 Tips

1. **Start Simple**: Begin with basic evaluation before complex integrations
2. **Use High A_eff**: Higher values (0.90+) typically give better results
3. **Iterate**: Run tuning loop if initial Ψ < 5.0
4. **Validate**: Always verify against ground truth database
5. **Monitor**: Track Ψ scores across multiple evaluations for consistency

## 🤝 Getting Help

- **Issues**: Open an issue on [GitHub](https://github.com/motanova84/141hz/issues)
- **Discussions**: Join [GitHub Discussions](https://github.com/motanova84/141hz/discussions)
- **Documentation**: Check [full documentation](https://motanova84.github.io/141hz)

---

**Ready to evaluate LLM coherence with quantum precision? Start coding!** 🚀
