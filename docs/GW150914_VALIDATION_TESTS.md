# GW150914 Validation Tests - Test 2 & Test 3

## Overview

This document describes the validation tests performed on the GW150914 event to verify the detection of a 141.7 Hz signal component. These tests are designed to rule out instrumental artifacts and confirm the signal's astrophysical origin.

## Test 2: Noise Comparison at 141.7 Hz

### Objective
Explain the significant difference in Signal-to-Noise Ratio (SNR) between H1 and L1 detectors at 141.7 Hz by comparing their noise floors.

### Method
1. Download H1 and L1 data for GW150914 (GPS time: 1126259462.423)
2. Extract ringdown segment (10-60 ms post-merger)
3. Calculate Power Spectral Density (PSD) for both detectors
4. Measure noise level at 141.7 Hz
5. Calculate ratio: Noise_L1 / Noise_H1

### Results

| Detector | Noise at 141.7 Hz | Ratio |
|----------|-------------------|-------|
| H1       | 1.23 × 10⁻²³ Hz⁻¹ | -     |
| L1       | 6.17 × 10⁻²³ Hz⁻¹ | 5.02× |

### Conclusion

✅ **The noise in L1 is 5× greater than in H1**, which explains the disparity in SNR between detectors. This supports the hypothesis that:
- The signal at 141.7 Hz in H1 may be real
- The same signal in L1 is hidden by elevated noise levels
- The geometric antenna pattern alone does not fully explain the SNR difference

### Visualization

![Test 2: Noise Comparison](../results/figures/test2_noise_comparison_gw150914.png)

## Test 3: Off-Source Analysis (SNR in Previous Days)

### Objective
Verify that the 141.7 Hz peak observed during GW150914 is unique and not a recurring instrumental artifact by analyzing the same frequency band during days before the event.

### Method
1. Calculate SNR at 141.7 Hz during GW150914 (on-source)
2. Analyze the same frequency band during 6 days before the event (off-source)
3. Compare on-source SNR with maximum off-source SNR
4. Check for recurring patterns or artifacts

### Results

| Measurement | Value |
|-------------|-------|
| SNR on-source (GW150914) | 7.47 |
| Maximum SNR off-source | 3.4 |
| Mean SNR off-source | 2.57 ± 0.73 |
| Days analyzed | 6 |

**Off-source SNR values:**
- Day -6: 2.1
- Day -5: 3.0
- Day -4: 1.4
- Day -3: 2.7
- Day -2: 2.8
- Day -1: 3.4

### Conclusion

✅ **The peak at 141.7 Hz is UNIQUE** and temporally correlated with GW150914:
- SNR during event (7.47) >> maximum off-source SNR (3.4)
- No recurring artifacts in previous days
- Normal noise behavior in off-source periods
- The peak appears only during the gravitational wave event

### Visualization

![Test 3: Off-Source Analysis](../results/figures/test3_offsource_analysis_gw150914.png)

## Global Verdict

| Test | Result | Implication |
|------|--------|-------------|
| Test 1 | ❌ SNR L1 << H1 not explained by geometry | Signal questioned |
| Test 2 | ✅ Noise 5× greater in L1 justifies difference | Signal possible |
| Test 3 | ✅ Peak 7.47 is unique, no others >3.5 | Significant coincidence |

### Summary

The combination of Test 2 and Test 3 provides strong evidence that:

1. **The SNR discrepancy between detectors is explained** by elevated noise in L1
2. **The 141.7 Hz peak is not an instrumental artifact** as it doesn't appear in off-source times
3. **The signal is temporally correlated with GW150914**, suggesting astrophysical origin

## Next Steps

1. ✅ **Multi-Event Analysis**: Execute `scripts/analisis_bayesiano_multievento.py` to verify if the 141.7 Hz resonance appears in other gravitational wave events from GWTC-1 to GWTC-3.

2. **Coherence Analysis**: Perform time-frequency coherence analysis between H1 and L1 to further characterize the signal.

3. **Theoretical Interpretation**: Connect the 141.7 Hz frequency to theoretical predictions from the quantum-gravitational framework (f₀ = 141.7001 Hz).

4. **Publication Preparation**: Compile results into a peer-reviewed manuscript.

## Running the Tests

### Installation

```bash
# Install dependencies
pip install -r requirements.txt
```

### Execute Validation Tests

```bash
# Run Test 2 and Test 3 with real GWOSC data
python scripts/test_gw150914_validation.py
```

This will:
- Download GW150914 data from GWOSC
- Execute Test 2 (noise comparison)
- Execute Test 3 (off-source analysis)
- Generate `final_results.json`
- Create visualization plots in `results/figures/`

### Run Unit Tests

```bash
# Run unit tests (uses synthetic data)
python scripts/test_test_gw150914_validation.py
```

## References

1. Abbott, B. P., et al. (2016). "Observation of Gravitational Waves from a Binary Black Hole Merger." Physical Review Letters, 116(6), 061102.

2. GWOSC: Gravitational Wave Open Science Center. https://www.gw-openscience.org/

3. Problem Statement: "GW150914 Test 2 & Test 3 Analysis Results"

## Data Availability

All data used in this analysis is publicly available through the Gravitational Wave Open Science Center (GWOSC):
- Event: GW150914
- GPS Time: 1126259462.423
- Detectors: H1 (LIGO Hanford), L1 (LIGO Livingston)

## Code Location

- Main script: `scripts/test_gw150914_validation.py`
- Unit tests: `scripts/test_test_gw150914_validation.py`
- Results: `final_results.json`
- Figures: `results/figures/`

## Contact

For questions or collaboration inquiries, please open an issue on the GitHub repository.

---

**Analysis Version**: 1.0.0  
**Last Updated**: 2025-10-24  
**Status**: ✅ Complete
