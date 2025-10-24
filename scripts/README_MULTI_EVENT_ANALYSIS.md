# Multi-Event Gravitational Wave Analysis Scripts

This directory contains scripts for analyzing gravitational wave events at the 141.7 Hz target frequency using data from the LIGO detectors (H1 - Hanford and L1 - Livingston).

## Scripts Overview

### 1. multi_event_snr_analysis.py
**Full H1/L1 SNR Analysis**

Analyzes 11 gravitational wave events from the GWTC catalog, calculating Signal-to-Noise Ratio (SNR) for both H1 and L1 detectors in the 141.7 Hz frequency band.

**Events analyzed:**
- GW150914, GW151012, GW151226
- GW170104, GW170608, GW170729, GW170809, GW170814, GW170817, GW170818, GW170823

**Outputs:**
- `multi_event_results.json`: SNR values for each event and detector
- `multi_event_analysis.png`: Comparative bar chart showing H1 vs L1 SNR

**Usage:**
```bash
python scripts/multi_event_snr_analysis.py
```

### 2. multi_event_h1_snr_analysis.py
**Simplified H1-Only SNR Analysis**

Faster version that analyzes only the H1 detector for the same 11 events.

**Outputs:**
- `multi_event_h1_results.json`: SNR values for H1 detector
- `multi_event_h1_analysis.png`: Bar chart of H1 SNR by event

**Usage:**
```bash
python scripts/multi_event_h1_snr_analysis.py
```

### 3. asd_noise_analysis.py
**Amplitude Spectral Density (ASD) Noise Comparison**

Calculates and compares noise levels between H1 and L1 detectors at 141.7 Hz using amplitude spectral density analysis.

**Features:**
- Configurable event selection via command-line arguments
- Computes noise ratio (L1/H1)
- Visualizes ASD in 140-143 Hz band

**Outputs:**
- `asd_noise_results.png`: ASD plot with 141.7 Hz marker

**Usage:**
```bash
# Default: GW150914
python scripts/asd_noise_analysis.py

# Custom event
python scripts/asd_noise_analysis.py --event GW170814 --start 1186741850 --end 1186741882

# Help
python scripts/asd_noise_analysis.py --help
```

## Requirements

All scripts require the following Python packages (already in `requirements.txt`):
- `gwpy>=3.0.0` - Gravitational wave data analysis
- `matplotlib>=3.5.0` - Plotting and visualization
- `numpy>=1.21.0` - Numerical computations

Install dependencies:
```bash
pip install -r requirements.txt
```

## Analysis Methodology

### SNR Calculation
Signal-to-Noise Ratio is calculated as:
```
SNR = max(|signal_filtered|) / std(signal_filtered)
```

Where the signal is bandpass-filtered in the range [140.7, 142.7] Hz around the target frequency of 141.7 Hz.

### ASD Analysis
Amplitude Spectral Density is computed using:
- FFT length: 4 seconds
- Overlap: 2 seconds
- Frequency band: 140-143 Hz

The noise level at exactly 141.7 Hz is extracted and compared between detectors.

## Expected Runtime

- **SNR Analysis (H1+L1)**: ~3-5 minutes per event (30-55 minutes total)
- **SNR Analysis (H1 only)**: ~2-3 minutes per event (20-35 minutes total)
- **ASD Analysis**: ~2-3 minutes per event

*Note: Runtime depends on network speed for data download from GWOSC (Gravitational Wave Open Science Center).*

## Output Files

The following files are generated in the current directory and are excluded from git by `.gitignore`:
- `multi_event_results.json`
- `multi_event_analysis.png`
- `multi_event_h1_results.json`
- `multi_event_h1_analysis.png`
- `asd_noise_results.png`

## Scientific Context

These scripts support the validation of the 141.7001 Hz frequency prediction from the quantum-classical correspondence in the GW250114-141Hz project. The multi-event analysis demonstrates the consistency of this frequency signature across multiple gravitational wave detections.

## Testing

A test suite is available to verify script structure and dependencies:
```bash
python scripts/test_multi_event_analysis.py
```

## References

- GWOSC (Gravitational Wave Open Science Center): https://www.gw-openscience.org/
- GWpy Documentation: https://gwpy.github.io/
- GWTC Catalogs: https://www.ligo.org/science/Publication-GWTC/
