# LISA Search Pipeline

## Overview

This directory contains the LISA (Laser Interferometer Space Antenna) targeted continuous-wave search implementation for detecting gravitational wave harmonics predicted by the GQN model.

## Files

- `lisa_search_pipeline.ipynb` - Complete Jupyter notebook with LISA analysis

## Target Frequencies

The GQN model predicts descending harmonics of f₀ = 141.7001 Hz:

```
f_n = f₀ / (n·φ)
```

where φ ≈ 1.618034 (golden ratio).

For LISA's sensitivity band (0.1 mHz - 1 Hz):

| n | Frequency (Hz) | In LISA Range |
|---|---------------|---------------|
| 1 | 0.0876 | ✓ |
| 2 | 0.0438 | ✓ |
| 3 | 0.0292 | ✓ |
| 4 | 0.0219 | ✓ |

## Usage

```bash
# Open notebook
jupyter notebook lisa_search_pipeline.ipynb

# Or convert to script and run
jupyter nbconvert --to script lisa_search_pipeline.ipynb
python lisa_search_pipeline.py
```

## Method

1. Calculate harmonic frequencies using golden ratio scaling
2. Model LISA noise curve (acceleration and optical noise)
3. Calculate expected SNR for different strain amplitudes
4. Simulate continuous-wave search with Time Delay Interferometry (TDI)
5. Analyze spectral peaks and verify detection criteria

## Detection Criteria

- **SNR threshold:** ≥ 5σ
- **Frequency tolerance:** ±0.001 Hz
- **Observation time:** 1 year (LISA mission duration)
- **Method:** Time Delay Interferometry (TDI)

## Data Sources

### LISA Pathfinder (Archive Data)
- **URL:** https://archives.esac.esa.int/lisa/
- **Format:** HDF5 time series
- **Channels:** TDI X, Y, Z
- **Access:** Public (requires ESA registration)

## Falsification

The GQN model will be falsified if:
- No coherent signals detected at predicted harmonics with SNR > 5
- Frequency deviations > 0.3 Hz from predictions
- No stationarity in detected signals

## References

1. LISA Mission Proposal, ESA/NASA (2017)
2. LISA Pathfinder Results, Phys. Rev. Lett. 116, 231101 (2016)
3. Time-Delay Interferometry, Living Rev. Relativ. 14, 5 (2011)

## Contact

See main repository: https://github.com/motanova84/141hz
