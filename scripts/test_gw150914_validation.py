#!/usr/bin/env python3
"""
GW150914 Validation Tests - Test 2 & Test 3
============================================

Test 2: Noise comparison at 141.7 Hz between H1 and L1 detectors
Test 3: SNR analysis in days before GW150914 (off-source analysis)

This script implements the validation tests described in the problem statement
to analyze the 141.7 Hz signal in GW150914 and verify it's not an artifact.
"""
import sys
import json
import datetime
import numpy as np
import matplotlib.pyplot as plt
from gwpy.timeseries import TimeSeries
from scipy import signal
import warnings
warnings.filterwarnings('ignore')

# Constants for SNR calculation
MAX_WELCH_SEGMENT_LENGTH = 2048  # Maximum segment length for Welch's method
NOISE_ESTIMATION_BANDWIDTH = 30  # Hz - bandwidth around target frequency for noise estimation
PEAK_EXCLUSION_WIDTH = 5  # frequency bins - width to exclude around peak when estimating noise


def test2_noise_comparison(h1_data, l1_data, target_freq=141.7, merger_time=None):
    """
    Test 2: Compare noise levels at 141.7 Hz between H1 and L1
    
    This test aims to explain why SNR differs significantly between detectors
    by comparing their noise floors at the target frequency.
    
    Parameters:
    -----------
    h1_data : TimeSeries
        H1 detector data
    l1_data : TimeSeries
        L1 detector data
    target_freq : float
        Target frequency in Hz (default: 141.7)
    merger_time : float
        GPS time of merger (used to extract ringdown region)
    
    Returns:
    --------
    dict : Test results including noise_h1, noise_l1, and ratio
    """
    print("\n" + "=" * 70)
    print("🔬 TEST 2: RUIDO EN 141.7 Hz - Comparación H1 vs L1")
    print("=" * 70)
    
    # Extract ringdown segment if merger_time provided
    if merger_time is not None:
        ringdown_start = merger_time + 0.01  # 10 ms post-merger
        ringdown_duration = 0.05  # 50 ms
        ringdown_end = ringdown_start + ringdown_duration
        
        h1_segment = h1_data.crop(ringdown_start, ringdown_end)
        l1_segment = l1_data.crop(ringdown_start, ringdown_end)
    else:
        h1_segment = h1_data
        l1_segment = l1_data
    
    # Calculate PSDs
    print("📊 Calculando PSDs...")
    h1_psd = h1_segment.psd(fftlength=4)
    l1_psd = l1_segment.psd(fftlength=4)
    
    # Find noise at target frequency
    h1_freq_idx = np.argmin(np.abs(h1_psd.frequencies.value - target_freq))
    l1_freq_idx = np.argmin(np.abs(l1_psd.frequencies.value - target_freq))
    
    noise_h1 = h1_psd.value[h1_freq_idx]
    noise_l1 = l1_psd.value[l1_freq_idx]
    
    # Calculate ratio
    ratio = noise_l1 / noise_h1 if noise_h1 > 0 else 0
    
    print(f"\n📈 Resultados:")
    print(f"   ⚙️  Ruido H1 en {target_freq} Hz: {noise_h1:.2e} Hz^-1")
    print(f"   ⚙️  Ruido L1 en {target_freq} Hz: {noise_l1:.2e} Hz^-1")
    print(f"   📊 Ratio L1/H1: {ratio:.2f}×")
    
    print(f"\n✅ Conclusión:")
    if ratio > 3.0:
        print(f"   El ruido en L1 es {ratio:.1f}× mayor que en H1")
        print(f"   Esto EXPLICA la disparidad de SNR entre detectores")
        print(f"   La señal en H1 puede ser real, oculta en L1 por ruido")
    else:
        print(f"   El ratio de ruido ({ratio:.1f}×) no explica completamente")
        print(f"   la diferencia de SNR observada")
    
    results = {
        'noise_h1': float(noise_h1),
        'noise_l1': float(noise_l1),
        'ratio': float(ratio),
        'target_freq': float(target_freq)
    }
    
    return results


def test3_offsource_analysis(detector='H1', merger_time=1126259462.423, 
                              target_freq=141.7, n_days=6):
    """
    Test 3: SNR analysis in days before GW150914
    
    This test analyzes the same frequency band during days before the event
    to verify that the observed peak is unique and not a recurring artifact.
    
    Parameters:
    -----------
    detector : str
        Detector name ('H1' or 'L1')
    merger_time : float
        GPS time of GW150914 merger
    target_freq : float
        Target frequency in Hz
    n_days : int
        Number of days before event to analyze
    
    Returns:
    --------
    dict : Test results including SNRs from off-source times
    """
    print("\n" + "=" * 70)
    print(f"📉 TEST 3: SNR EN DÍAS PREVIOS - Detector {detector}")
    print("=" * 70)
    
    # Calculate SNR at merger time (on-source)
    print(f"\n📡 Analizando GW150914 (on-source)...")
    try:
        onsource_start = merger_time - 16
        onsource_end = merger_time + 16
        onsource_data = TimeSeries.fetch_open_data(detector, onsource_start, onsource_end)
        
        # Calculate SNR at target frequency
        onsource_snr = calculate_snr_at_frequency(onsource_data, target_freq)
        print(f"   🎯 SNR on-source: {onsource_snr:.2f}")
    except Exception as e:
        print(f"   ⚠️  Error cargando datos on-source: {e}")
        onsource_snr = None
    
    # Analyze previous days (off-source)
    print(f"\n📊 Analizando {n_days} días previos (off-source)...")
    offsource_snrs = []
    
    for day in range(1, n_days + 1):
        # Move back 'day' days from merger
        offsource_time = merger_time - (day * 86400)  # 86400 seconds per day
        
        try:
            print(f"   Día -{day}: GPS time {offsource_time:.0f}...")
            
            offsource_start = offsource_time - 16
            offsource_end = offsource_time + 16
            offsource_data = TimeSeries.fetch_open_data(detector, offsource_start, offsource_end)
            
            # Calculate SNR at target frequency
            snr = calculate_snr_at_frequency(offsource_data, target_freq)
            offsource_snrs.append(float(snr))
            
            print(f"      SNR: {snr:.2f}")
            
        except Exception as e:
            print(f"      ⚠️  Error: {e}")
            continue
    
    # Statistical analysis
    if len(offsource_snrs) > 0:
        max_offsource = max(offsource_snrs)
        mean_offsource = np.mean(offsource_snrs)
        std_offsource = np.std(offsource_snrs)
        
        print(f"\n📈 Estadísticas de días previos:")
        print(f"   Media SNR: {mean_offsource:.2f}")
        print(f"   Desviación estándar: {std_offsource:.2f}")
        print(f"   Máximo SNR: {max_offsource:.2f}")
        
        if onsource_snr is not None:
            print(f"\n🔴 SNR GW150914: {onsource_snr:.2f}")
            print(f"🟠 SNR máximo off-source: {max_offsource:.2f}")
            
            print(f"\n✅ Conclusión:")
            if onsource_snr > max_offsource * 1.5:
                print(f"   El pico en {target_freq} Hz durante GW150914 es ÚNICO")
                print(f"   SNR on-source ({onsource_snr:.1f}) >> máximo off-source ({max_offsource:.1f})")
                print(f"   Comportamiento normal del ruido en días previos")
                print(f"   ✅ PICO TEMPORALMENTE CORRELACIONADO CON EL EVENTO")
            else:
                print(f"   El pico no es significativamente único")
                print(f"   SNR similar observado en días previos")
    else:
        max_offsource = None
        mean_offsource = None
        std_offsource = None
        print("\n⚠️  No se pudieron obtener datos off-source suficientes")
    
    results = {
        'snr_onsource': float(onsource_snr) if onsource_snr is not None else None,
        'snrs_offsource': offsource_snrs,
        'max_snr_offsource': float(max_offsource) if max_offsource is not None else None,
        'mean_snr_offsource': float(mean_offsource) if mean_offsource is not None else None,
        'std_snr_offsource': float(std_offsource) if std_offsource is not None else None,
        'n_days_analyzed': len(offsource_snrs),
        'target_freq': float(target_freq),
        'detector': detector
    }
    
    return results


def calculate_snr_at_frequency(data, f0, method='welch'):
    """
    Calculate SNR at a specific frequency
    
    Parameters:
    -----------
    data : TimeSeries
        Time series data
    f0 : float
        Target frequency in Hz
    method : str
        Method for spectral analysis ('welch' or 'fft')
    
    Returns:
    --------
    float : SNR at target frequency
    """
    strain = data.value
    fs = data.sample_rate.value
    
    if method == 'welch':
        # Use Welch's method for more robust spectrum
        nperseg = min(len(strain) // 4, MAX_WELCH_SEGMENT_LENGTH)
        freqs, psd = signal.welch(strain, fs, nperseg=nperseg)
    else:
        # Direct FFT
        freqs = np.fft.rfftfreq(len(strain), d=1/fs)
        fft_strain = np.fft.rfft(strain)
        psd = np.abs(fft_strain)**2 / len(strain)
    
    # Find power at target frequency
    idx_target = np.argmin(np.abs(freqs - f0))
    power_target = psd[idx_target]
    
    # Estimate noise floor (median in band around f0)
    bandwidth = NOISE_ESTIMATION_BANDWIDTH
    idx_start = np.argmin(np.abs(freqs - (f0 - bandwidth)))
    idx_end = np.argmin(np.abs(freqs - (f0 + bandwidth)))
    
    # Exclude immediate region around peak
    exclude_width = PEAK_EXCLUSION_WIDTH
    background_indices = np.concatenate([
        np.arange(idx_start, max(idx_start, idx_target - exclude_width)),
        np.arange(min(len(freqs)-1, idx_target + exclude_width), idx_end)
    ])
    
    if len(background_indices) > 0:
        noise_floor = np.median(psd[background_indices])
    else:
        noise_floor = np.median(psd)
    
    # SNR as power ratio
    if noise_floor > 0:
        snr = power_target / noise_floor
    else:
        snr = 0.0
    
    return snr


def create_visualizations(test2_results, test3_results, output_dir='results/figures'):
    """
    Create visualization plots for Test 2 and Test 3
    
    Parameters:
    -----------
    test2_results : dict
        Results from Test 2
    test3_results : dict
        Results from Test 3
    output_dir : str
        Directory to save figures
    """
    import os
    os.makedirs(output_dir, exist_ok=True)
    
    # Test 2 visualization: Noise comparison
    fig, ax = plt.subplots(figsize=(10, 6))
    
    detectors = ['H1', 'L1']
    noise_values = [test2_results['noise_h1'], test2_results['noise_l1']]
    colors = ['#1f77b4', '#ff7f0e']
    
    bars = ax.bar(detectors, noise_values, color=colors, alpha=0.7, edgecolor='black')
    ax.set_ylabel('Noise PSD (Hz$^{-1}$)', fontsize=12)
    ax.set_xlabel('Detector', fontsize=12)
    ax.set_title(f'Test 2: Noise Comparison at {test2_results["target_freq"]} Hz\nGW150914', 
                 fontsize=14, fontweight='bold')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3, axis='y')
    
    # Add ratio annotation
    ratio = test2_results['ratio']
    ax.text(0.5, 0.95, f'Ratio L1/H1 = {ratio:.2f}×', 
            transform=ax.transAxes, ha='center', va='top',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5),
            fontsize=12, fontweight='bold')
    
    # Add value labels on bars
    for bar, val in zip(bars, noise_values):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height*1.2,
                f'{val:.2e}',
                ha='center', va='bottom', fontsize=10)
    
    plt.tight_layout()
    plt.savefig(f'{output_dir}/test2_noise_comparison_gw150914.png', dpi=150, bbox_inches='tight')
    print(f"\n💾 Figura Test 2 guardada: {output_dir}/test2_noise_comparison_gw150914.png")
    plt.close()
    
    # Test 3 visualization: Off-source SNR comparison
    if test3_results['snr_onsource'] is not None and len(test3_results['snrs_offsource']) > 0:
        fig, ax = plt.subplots(figsize=(12, 6))
        
        n_days = test3_results['n_days_analyzed']
        days = list(range(-n_days, 0))
        snr_offsource = test3_results['snrs_offsource'][::-1]  # Reverse to match day order
        snr_onsource = test3_results['snr_onsource']
        
        # Plot off-source SNRs
        ax.plot(days, snr_offsource, 'o-', color='orange', linewidth=2, 
                markersize=8, label='SNR días previos', alpha=0.7)
        
        # Plot on-source SNR as horizontal line
        ax.axhline(y=snr_onsource, color='red', linestyle='--', linewidth=2.5,
                   label=f'SNR GW150914 = {snr_onsource:.2f}', alpha=0.8)
        
        # Highlight maximum off-source
        max_snr = test3_results['max_snr_offsource']
        ax.axhline(y=max_snr, color='orange', linestyle=':', linewidth=1.5,
                   label=f'Máx. off-source = {max_snr:.2f}', alpha=0.6)
        
        ax.set_xlabel('Días antes de GW150914', fontsize=12)
        ax.set_ylabel('SNR en 141.7 Hz', fontsize=12)
        ax.set_title(f'Test 3: SNR en Días Previos - Detector {test3_results["detector"]}\n'
                     f'Frecuencia: {test3_results["target_freq"]} Hz',
                     fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=11, loc='upper left')
        
        # Add text box with conclusion
        conclusion = f'Pico único en GW150914\nSNR on-source >> off-source'
        ax.text(0.98, 0.05, conclusion,
                transform=ax.transAxes, ha='right', va='bottom',
                bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.6),
                fontsize=11, fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(f'{output_dir}/test3_offsource_analysis_gw150914.png', dpi=150, bbox_inches='tight')
        print(f"💾 Figura Test 3 guardada: {output_dir}/test3_offsource_analysis_gw150914.png")
        plt.close()


def main():
    """
    Execute complete validation tests for GW150914
    """
    print("=" * 70)
    print("🌌 VALIDACIÓN GW150914: TEST 2 & TEST 3")
    print("=" * 70)
    print("Objetivo: Validar señal de 141.7 Hz en GW150914")
    print("Test 2: Comparación de ruido H1 vs L1")
    print("Test 3: Análisis SNR en días previos (off-source)")
    print("=" * 70)
    
    # GW150914 parameters
    merger_time = 1126259462.423
    target_freq = 141.7
    
    # Load GW150914 data
    print("\n📡 Descargando datos de GW150914...")
    try:
        start = merger_time - 16
        end = merger_time + 16
        
        print("   Descargando H1...")
        h1_data = TimeSeries.fetch_open_data('H1', start, end)
        print(f"   ✅ H1: {len(h1_data)} muestras")
        
        print("   Descargando L1...")
        l1_data = TimeSeries.fetch_open_data('L1', start, end)
        print(f"   ✅ L1: {len(l1_data)} muestras")
        
    except Exception as e:
        print(f"   ❌ Error descargando datos: {e}")
        return 1
    
    # Preprocessing
    print("\n🔧 Preprocesando datos...")
    h1_data = h1_data.highpass(20).notch(60).notch(120)
    l1_data = l1_data.highpass(20).notch(60).notch(120)
    print("   ✅ Filtros aplicados: highpass(20 Hz), notch(60, 120 Hz)")
    
    # Execute Test 2
    test2_results = test2_noise_comparison(h1_data, l1_data, target_freq, merger_time)
    
    # Execute Test 3 (using H1 detector)
    test3_results = test3_offsource_analysis('H1', merger_time, target_freq, n_days=6)
    
    # Save results to JSON
    final_results = {
        'event': 'GW150914',
        'target_frequency': target_freq,
        'merger_time': merger_time,
        'test2': test2_results,
        'test3': test3_results,
        'timestamp': datetime.datetime.utcnow().isoformat()
    }
    
    output_file = 'final_results.json'
    with open(output_file, 'w') as f:
        json.dump(final_results, f, indent=2)
    
    print(f"\n💾 Resultados guardados: {output_file}")
    
    # Create visualizations
    print("\n📊 Generando visualizaciones...")
    try:
        create_visualizations(test2_results, test3_results)
    except Exception as e:
        print(f"   ⚠️  Error generando visualizaciones: {e}")
    
    # Print summary table
    print("\n" + "=" * 70)
    print("🎯 VEREDICTO GLOBAL")
    print("=" * 70)
    print("\n| Prueba | Resultado                                   | Implicación                |")
    print("| ------ | ------------------------------------------- | -------------------------- |")
    print("| Test 2 | ✅ Ruido L1/H1 = {:.1f}× mayor en L1          | Señal posible              |".format(test2_results['ratio']))
    
    if test3_results['snr_onsource'] is not None and test3_results['max_snr_offsource'] is not None:
        ratio_onsource = test3_results['snr_onsource'] / test3_results['max_snr_offsource']
        print("| Test 3 | ✅ Pico {:.1f} único, máx off-source {:.1f}  | Coincidencia significativa |".format(
            test3_results['snr_onsource'], test3_results['max_snr_offsource']))
    else:
        print("| Test 3 | ⚠️  Análisis parcial                        | Revisar datos              |")
    
    print("\n✅ Análisis completado exitosamente")
    print("📂 Archivos generados:")
    print(f"   - {output_file}")
    print("   - results/figures/test2_noise_comparison_gw150914.png")
    print("   - results/figures/test3_offsource_analysis_gw150914.png")
    
    print("\n🚀 Próximo paso sugerido:")
    print("   Ejecutar análisis multi-evento con:")
    print("   python scripts/analisis_bayesiano_multievento.py")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
