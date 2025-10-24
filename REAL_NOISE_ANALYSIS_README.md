# 🔬 Real Noise Analysis - Validation Tests

This directory contains two validation scripts for analyzing real LIGO data to validate the 141.7 Hz component around GW150914.

## 📋 Overview

These scripts implement rigorous validation tests using real GWOSC (Gravitational Wave Open Science Center) data:

- **Test 2**: Off-source noise analysis 1 hour before GW150914
- **Test 3**: Multi-segment scan over 10 days before GW150914

## 🚀 Quick Start

### Option A: Local Machine

```bash
# 1. Clone or navigate to repository
cd 141hz_validation

# 2. Install dependencies
pip install gwpy pycbc numpy matplotlib

# 3. Create directories (if not exist)
mkdir -p data results

# 4. Run tests in order
python test2_real_noise_analysis.py  # Test 2
python test3_real_offsource_scan.py  # Test 3

# 5. View results
cat results/test2_real_results.json
cat results/test3_real_results.json
```

### Option B: Google Colab (EASIER)

Google Colab has access to GWOSC by default:

```python
# In a Colab notebook
!pip install gwpy

# Download the scripts
!wget https://raw.githubusercontent.com/motanova84/141hz/main/test2_real_noise_analysis.py
!wget https://raw.githubusercontent.com/motanova84/141hz/main/test3_real_offsource_scan.py

# Run the tests
!python test2_real_noise_analysis.py
!python test3_real_offsource_scan.py
```

## 🎯 What These Scripts Do

### Test 2: Real Noise Analysis

**Purpose**: Analyze off-source noise to determine if 141.7 Hz is more prominent in L1 than H1

**Process**:
1. ✅ Download 32s H1 and L1 off-source (1h before GW150914)
2. ✅ Preprocess with pipeline LIGO standard
3. ✅ Calculate ASD with 0.25 Hz resolution
4. ✅ Extract EXACT values at 141.7 Hz
5. ✅ Calculate ratio noise_L1/noise_H1
6. ✅ Generate visualizations
7. ✅ Save results to JSON

**Expected Output**:
```json
{
  "noise_ratio": X.XX,
  "coverage_percent": YY.Y,
  "verdict": "✅ FAVORABLE" or "❌ DESFAVORABLE"
}
```

**Verdict Criteria**:
- `noise_ratio > 1.5`: ✅ FAVORABLE (141.7 Hz more prominent in L1)
- `noise_ratio < 1.5`: ❌ DESFAVORABLE

### Test 3: Real Off-Source Scan

**Purpose**: Determine if 141.7 Hz is a persistent spectral line or transient feature

**Process**:
1. ✅ Download 10 segments of 32s (10 days before)
2. ✅ Analyze each with same pipeline
3. ✅ Search for peaks in 140-143 Hz band
4. ✅ Calculate SNR for each segment
5. ✅ Compare with SNR during GW150914 (H1 SNR = 7.47)
6. ✅ Determine if persistent line
7. ✅ Visualize SNR timeline

**Expected Output**:
```json
{
  "h1_snr_max": X.XX,
  "h1_n_above_7": N,
  "verdict": "✅ FAVORABLE" or "❌ DESFAVORABLE"
}
```

**Verdict Criteria**:
- `max_snr < 7.47` AND `n_above_7 == 0`: ✅ FAVORABLE (transient, not persistent)
- `max_snr >= 7.47` OR `n_above_7 > 0`: ❌ DESFAVORABLE (persistent line)

## 📊 Output Files

After running both scripts, you will have:

### JSON Results
- `results/test2_real_results.json` - Detailed noise analysis results
- `results/test3_real_results.json` - Multi-segment scan results

### Visualizations
- `results/test2_real_asd_analysis.png` - ASD plots with 141.7 Hz highlighted
- `results/test3_real_snr_timeline.png` - SNR timeline over 10 days
- `results/test3_real_asd_comparison.png` - ASD comparison of all segments

## 📖 Detailed Usage

### Test 2: Real Noise Analysis

```bash
python test2_real_noise_analysis.py
```

**What it analyzes**:
- GPS time: 1126255862 (1 hour before GW150914)
- Duration: 32 seconds
- Detectors: H1 and L1
- Frequency resolution: 0.25 Hz (4-second FFT)

**Key metrics**:
- `h1_asd_141hz`: H1 amplitude spectral density at 141.7 Hz
- `l1_asd_141hz`: L1 amplitude spectral density at 141.7 Hz
- `noise_ratio`: L1/H1 ratio (key metric)
- `coverage_percent`: Spectral coverage in 140-143 Hz band

### Test 3: Real Off-Source Scan

```bash
python test3_real_offsource_scan.py
```

**What it analyzes**:
- 10 segments of 32 seconds each
- Distributed over 10 days before GW150914
- Detector: H1 (primary)
- Frequency band: 140-143 Hz

**Key metrics**:
- `h1_snr_max`: Maximum SNR observed in all segments
- `h1_snr_mean`: Average SNR across segments
- `h1_n_above_7`: Number of segments with SNR ≥ 7.0
- Comparison with GW150914 SNR (7.47)

## 🔧 Requirements

### Python Packages
- `gwpy >= 3.0.0` - LIGO data access and analysis
- `numpy >= 1.21.0` - Numerical computations
- `matplotlib >= 3.5.0` - Visualization
- `scipy >= 1.7.0` - Scientific computing (dependency of gwpy)

### System Requirements
- Internet connection (to download GWOSC data)
- ~2 GB disk space (for cached data)
- Python 3.9+ recommended

### Installation

```bash
# Using pip
pip install gwpy numpy matplotlib

# Or using requirements.txt
pip install -r requirements.txt
```

## 🌐 Data Source

Both scripts download data from **GWOSC (Gravitational Wave Open Science Center)**:
- URL: https://www.gw-openscience.org/
- Event: GW150914
- GPS time: 1126259462
- Data is automatically cached locally

## ⚠️ Troubleshooting

### "Connection Error" or "Network Error"
- Check internet connection
- GWOSC servers may be temporarily unavailable
- Try again later or use cached data

### "No module named 'gwpy'"
```bash
pip install gwpy
```

### "Module 'matplotlib' has no attribute 'use'"
```bash
pip install --upgrade matplotlib
```

### Slow execution
- First run downloads data (~1-2 GB) and takes longer
- Subsequent runs use cached data and are faster
- Test 3 is slower (10 segments) - expect 5-10 minutes

## 📚 Scientific Context

These tests validate whether the 141.7 Hz component observed in GW150914 is:

1. **Noise artifact** (persistent spectral line)
2. **Instrumental feature** (detector characteristic)
3. **Astrophysical signal** (transient gravitational wave feature)

### Interpretation

**Favorable results** (✅):
- Test 2: Higher noise in L1 at 141.7 Hz suggests detector-specific feature
- Test 3: Low SNR in off-source segments suggests transient feature, not persistent line

**Unfavorable results** (❌):
- Test 2: Similar noise in H1 and L1 suggests common-mode or environmental noise
- Test 3: High SNR in off-source segments suggests persistent spectral line

## 🔗 References

- GWOSC: https://www.gw-openscience.org/
- GWpy Documentation: https://gwpy.github.io/
- GW150914 Paper: https://doi.org/10.1103/PhysRevLett.116.061102
- LIGO Open Science Tutorial: https://www.gw-openscience.org/tutorials/

## 📄 License

MIT License - See LICENSE file for details

## 👤 Author

José Manuel Mota Burruezo (JMMB Ψ✧)

## 🤝 Contributing

Contributions welcome! Please:
1. Fork the repository
2. Create a feature branch
3. Submit a pull request

## 📞 Support

For issues or questions:
- Open an issue on GitHub
- Check GWOSC documentation
- Review LIGO tutorials
