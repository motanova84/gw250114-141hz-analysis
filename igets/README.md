# IGETS Gravimetry Analysis

## Overview

This directory contains the IGETS (International Geodynamics and Earth Tide Service) gravimetry analysis for searching Yukawa-modulated gravity oscillations predicted by the GQN model.

## Files

- `igets_fft_analysis.ipynb` - Jupyter notebook with FFT analysis

## GQN Prediction

The model predicts a Yukawa-modulated gravitational potential:

```
V(r,t) = -(GM/r)[1 + α_Y·e^(-r/λ̄)(1 + ε·cos(2πf₀t))]
```

where:
- λ̄ ≈ 3.37×10⁵ m (337 km) - Yukawa range
- f₀ = 141.7001 Hz - modulation frequency
- α_Y - coupling constant (~10⁻⁶)
- ε - modulation amplitude (~10⁻¹⁰)

## Usage

```bash
# Open notebook
jupyter notebook igets_fft_analysis.ipynb

# Or convert to script
jupyter nbconvert --to script igets_fft_analysis.ipynb
python igets_fft_analysis.py
```

## Method

1. Load superconducting gravimeter (SG) time series
2. Preprocess:
   - Remove tidal components (M2, S2, etc.)
   - Detrend instrumental drift
   - Bandpass filter 100-300 Hz
3. FFT analysis with Welch method
4. Search for peaks at f₀ ± 0.5 Hz with SNR > 6
5. Verify multi-station coherence

## IGETS Stations

Selected stations with high-quality SG data:

| Station | Country | Latitude | Longitude |
|---------|---------|----------|-----------|
| Cantley | Canada | 45.5°N | 75.8°W |
| Bad Homburg | Germany | 50.2°N | 8.6°E |
| Kyoto | Japan | 35.0°N | 135.8°E |
| Strasbourg | France | 48.6°N | 7.7°E |
| Boulder | USA | 40.0°N | 105.3°W |

## Detection Criteria

- **SNR threshold:** ≥ 6σ
- **Frequency tolerance:** ±0.5 Hz around f₀
- **Coherence:** Detection in ≥3 stations
- **Phase consistency:** Verified across stations

## Data Sources

### IGETS Level-1
- **URL:** http://igets.u-strasbg.fr/
- **Format:** ASCII time series (μGal)
- **Sampling:** Varies, typically 1 Hz to 1 kHz
- **Access:** Public (requires data use agreement)

## Output

The notebook generates:
1. Raw data visualization
2. Processed spectra (100-300 Hz)
3. Peak detection at f₀
4. Multi-station coherence analysis

## Falsification

The GQN model will be falsified if:
- No coherent signal at f₀ with SNR > 6
- No global coherence across stations
- Signal is local/instrumental artifact
- No phase consistency

## Next Steps

1. Access real IGETS Level-1 data
2. Analyze months of continuous data
3. Cross-validate between stations
4. Rule out instrumental effects

## References

1. IGETS: http://igets.u-strasbg.fr/
2. Superconducting Gravimeters, Van Camp et al., Geophysics (2017)
3. IGETS Data Standards, J. Geod. 89, 1123 (2015)
4. Yukawa Gravity Tests, Adelberger et al., Ann. Rev. Nucl. Part. Sci. 53, 77 (2003)

## Contact

See main repository: https://github.com/motanova84/141hz
