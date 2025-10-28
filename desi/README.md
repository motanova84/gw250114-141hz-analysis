# DESI Dark Energy Analysis

## Overview

This directory contains the DESI (Dark Energy Spectroscopic Instrument) cosmological analysis for testing the GQN model's prediction of dark energy evolution.

## Files

- `desi_wz_analysis.py` - Python script for w(z) analysis

## GQN Prediction

The model predicts:

```
w(z) = -1 + n/3
```

with n ≈ 0.3, giving:
- w₀ = -1.0 (current equation of state)
- w_a = +0.2 (evolution parameter)

This predicts slightly faster expansion than ΛCDM (w = -1 constant) at z > 1.

## Usage

```bash
# Run analysis
python desi_wz_analysis.py

# Output: desi_wz_analysis.png with 4 subplots
```

## Method

1. Generate/load DESI DR2 data (E(z) measurements)
2. Fit CPL parameterization: w(z) = w₀ + w_a·z/(1+z)
3. Calculate tension: Δw = |w_DESI - w_GQN|
4. Compare with ΛCDM and GQN predictions

## Output

The script generates visualizations showing:
1. Hubble parameter E(z) evolution
2. Dark energy equation of state w(z)
3. Fit residuals
4. Tension parameter |Δw|

## Detection Criteria

- **Compatibility:** |Δw| < 0.05 in z ∈ [0.5, 1.5]
- **Confidence:** χ²/dof < 2.0
- **MCMC:** Full uncertainty quantification (future work)

## Data Sources

### DESI DR2
- **URL:** https://www.legacysurvey.org/
- **Format:** FITS catalogs
- **Data:** BAO measurements, galaxy clustering
- **Papers:** arXiv:2404.03002 (DESI 2024 Results)
- **Access:** Public

## Next Steps

1. Implement full MCMC with `emcee`
2. Use real DESI DR2 BAO data
3. Include Planck priors
4. Generate confidence contours in (w₀, w_a) plane

## Falsification

The GQN model will be falsified if:
- |Δw| > 0.1 consistently across z ∈ [0.5, 1.5]
- χ²/dof > 3.0 (poor fit)
- Systematic deviation from GQN prediction at all redshifts

## References

1. DESI 2024 Results, arXiv:2404.03002
2. Dark Energy Survey, MNRAS 460, 1270 (2016)
3. CPL Parameterization, Phys. Rev. D 66, 023507 (2002)

## Contact

See main repository: https://github.com/motanova84/141hz
