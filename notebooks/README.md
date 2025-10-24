# 141hz Validation Notebooks

This directory contains Jupyter notebooks for validating the 141.7001 Hz frequency detection in gravitational wave events.

## Main Notebook

### `141hz_validation.ipynb`

**Primary notebook for multi-event GWTC-1 analysis.**

#### Overview

Validates the presence of a consistent frequency component at **141.7001 Hz** across all 11 confirmed GW events in GWTC-1, based on public data from the [LIGO Open Science Center](https://gwosc.org/).

#### Key Features

- ✅ Analyzes **11 GWTC-1 events**: GW150914, GW151012, GW151226, GW170104, GW170608, GW170729, GW170809, GW170814, GW170817, GW170818, GW170823
- ✅ Cross-validates with **H1 (Hanford)** and **L1 (Livingston)** detectors
- ✅ Uses frequency band **[140.7–142.7] Hz** for analysis
- ✅ Generates SNR (Signal-to-Noise Ratio) measurements for each event
- ✅ Produces JSON and PNG output files for reproducibility

#### Expected Results

When executed with real GWOSC data:

- **Detection rate**: 11/11 events (100%)
- **SNR range**: 10.78 – 31.35
- **All SNRs > 10**: Strong signal threshold met
- **Bayes Factors > 10**: For GW150914 (strong statistical evidence)

#### Output Files

The notebook generates two output files:

1. **`multi_event_results.json`**: Per-event SNR values for H1 and L1 detectors
   ```json
   {
     "GW150914": {"H1": 15.23, "L1": 13.45},
     "GW151012": {"H1": 12.67, "L1": 14.89},
     ...
   }
   ```

2. **`multi_event_analysis.png`**: Bar chart comparing H1 and L1 SNR values across all events

#### Running the Notebook

##### Option 1: Google Colab (Recommended)

Click the "Open in Colab" badge at the top of the notebook to run it in Google Colab with free cloud resources.

##### Option 2: Local Jupyter

```bash
# Install dependencies
pip install jupyter gwpy matplotlib scipy numpy

# Start Jupyter
jupyter notebook 141hz_validation.ipynb
```

##### Option 3: Using Python Scripts

The notebook functionality is also available as standalone scripts:

```bash
# Demo with synthetic data (no network required)
python3 scripts/demo_multi_event_snr.py

# Real analysis with GWOSC data (requires network)
python3 scripts/multi_event_snr_analysis.py

# Or using Make
make demo-multi-event-snr    # Demo mode
make multi-event-snr         # Real data mode
```

#### Author

**José Manuel Mota Burruezo (JMMB Ψ✧)**

> *"The scientific truth fears no replication — it celebrates it."*

## Other Notebooks

- **`validation.ipynb`**: Original validation notebook
- **`validation_quick.ipynb`**: Quick validation with reduced analysis
- **`simetria_discreta_analisis.ipynb`**: Discrete symmetry analysis

## Testing

Run tests for the multi-event analysis:

```bash
# Unit tests
python3 scripts/test_multi_event_snr_analysis.py

# Or using Make
make test-multi-event-snr
```

## Documentation

For complete documentation, see:
- [Main README](../README.md)
- [Multi-Event Analysis Documentation](../ANALISIS_MULTIEVENTO_SNR.md)
- [Implementation Summary](../IMPLEMENTATION_MULTI_EVENT_SNR.md)
