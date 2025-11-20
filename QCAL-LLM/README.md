# QCAL-LLM ∞³ - Quantum Coherent Attentional LLM

> **Note:** This directory provides an overview of the QCAL-LLM implementation.
> For the complete implementation, see the [`noesis-qcal-llm/`](../noesis-qcal-llm/) directory.

## 📖 Overview

**QCAL-LLM** (Quantum Coherent Attentional Lock) is a framework for vibrational coherence tuning in
Large Language Models (LLMs), anchored to the universal frequency **f₀ = 141.7001 Hz** derived from
gravitational wave data.

This innovative approach achieves:

- **>95% hallucination reduction** compared to RLHF
- **Automatic coherence evaluation** using the Ψ (Psi) metric
- **Physics-based attention modulation** via the Stochastic Integration Protocol (SIP)
- **No human-in-the-loop** training required

## 🎯 Key Features

### 1. Ψ Metric (Psi Metric)

The core evaluation metric that measures coherence quality:

```text
Ψ = KLD⁻¹ × C²
```

Where:

- **KLD⁻¹**: Inverse Kullback-Leibler Divergence (accuracy)
- **C²**: Squared coherence with ground truth database

**Threshold**: Ψ ≥ 5.0 for production-ready outputs

### 2. SIP (Stochastic Integration Protocol)

Physics-based attention modulation using the universal frequency f₀:

```python
A_mod = A_base × (1 + ε × sin(2π × f₀ × t))
```

Where:

- **f₀**: 141.7001 Hz (fundamental frequency)
- **ε**: Modulation amplitude (auto-tuned to target A_eff)
- **A_base**: Base attention weights

### 3. Ground Truth Database

Empirical values from gravitational wave analysis and mathematical constants:

- **f₀**: 141.7001 Hz
- **ζ'(1/2)**: -1.460 (Riemann zeta derivative)
- **φ³**: 4.236 (golden ratio cubed)
- **SNR (GW150914)**: 20.95

## 📂 Implementation Location

The complete implementation is located in the **[`noesis-qcal-llm/`](../noesis-qcal-llm/)** directory:

### Core Components

- **[QCALLLMCore.py](../noesis-qcal-llm/QCALLLMCore.py)** - Main evaluation engine with Ψ metric
- **[psi_metric_core.py](../noesis-qcal-llm/psi_metric_core.py)** - Core Psi metric implementation
- **[psi_tuning_loop.py](../noesis-qcal-llm/psi_tuning_loop.py)** - Automatic epsilon tuning
- **[core.py](../noesis-qcal-llm/core.py)** - Base coherence functions
- **[detect_f0.py](../noesis-qcal-llm/detect_f0.py)** - f₀ detection from text

### Documentation

- **[MANIFESTO.md](../noesis-qcal-llm/MANIFESTO.md)** - Complete theoretical framework
- **[README.md](../noesis-qcal-llm/README.md)** - Detailed module documentation
- **[IMPLEMENTATION_SUMMARY.md](../noesis-qcal-llm/IMPLEMENTATION_SUMMARY.md)** - Implementation details

### Examples & Tests

- **[example_usage.py](../noesis-qcal-llm/example_usage.py)** - Usage examples
- **[test_psi_metric_core.py](../noesis-qcal-llm/test_psi_metric_core.py)** - Test suite (35 tests)
- **[evaluate_manifesto.py](../noesis-qcal-llm/evaluate_manifesto.py)** - Manifesto evaluation

## 🚀 Quick Start

```bash
# Navigate to the implementation directory
cd noesis-qcal-llm

# Run the example
python example_usage.py

# Run the test suite
python -m pytest test_psi_metric_core.py -v

# Evaluate a text with the Ψ metric
python -c "
from psi_metric_core import PsiMetricCore

psi = PsiMetricCore()
result = psi.evaluate_single(
    'f₀ = -ζ'(1/2) × φ³ = 141.7001 Hz',
    'Derive the fundamental frequency'
)

print(f'Ψ score: {result[\"psi\"]:.2f}')
print(f'Coherent: {result[\"coherent\"]}')
"
```

## 📊 Benchmark Results

From **[benchmark_results.json](../noesis-qcal-llm/benchmark_results.json)**:

```json
{
  "framework": "QCAL-LLM ∞³",
  "model": "Mock LLM (Perfect Coherence)",
  "overall_mean_psi": 8.05,
  "coherence_rate": 100.0,
  "epsilon": 0.0162,
  "target_A_eff": 0.92
}
```

## 🔬 Integration with 141hz Repository

QCAL-LLM is fully integrated with the 141hz gravitational wave analysis repository:

- Ground truth values derived from empirical GW data
- Automated testing via **[`.github/workflows/qcal-llm-tests.yml`](../.github/workflows/qcal-llm-tests.yml)**
- Python 3.11+ compatibility
- Cross-validation with multiple detectors (H1, L1, V1)

## 📖 Further Reading

- **[Main Repository README](../README.md)** - 141hz project overview
- **[QCAL Quick Reference](../QCAL_QUICK_REFERENCE.md)** - Quick reference card
- **[QCAL LLM Environment](../QCAL_LLM_ENVIRONMENT.md)** - Reproducible evaluation setup
- **[Llama 4 Integration](../LLAMA4_INTEGRATION_SUMMARY.md)** - LLaMA 4 Maverick backend

## 📄 Citation

If you use QCAL-LLM in your research, please cite:

```bibtex
@software{qcal_llm_2025,
  title = {QCAL-LLM ∞³: Quantum Coherent Attentional Lock for LLMs},
  author = {Mota Burruezo, José Manuel},
  year = {2025},
  url = {https://github.com/motanova84/141hz}
}
```

## 📜 License

MIT License - See [LICENSE](../LICENSE) for details

---

**Author:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Repository:** [github.com/motanova84/141hz](https://github.com/motanova84/141hz)
