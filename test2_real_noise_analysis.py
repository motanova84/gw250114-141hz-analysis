#!/usr/bin/env python3
"""
Test 2: Real Noise Analysis - Off-Source GW150914

Analyzes real LIGO noise data from 1 hour before GW150914 to validate
the 141.7 Hz component in off-source data.

Process:
1. Download 32s H1 and L1 off-source data (1h before GW150914)
2. Preprocess with standard LIGO pipeline
3. Calculate ASD (Amplitude Spectral Density) with 0.25 Hz resolution
4. Extract exact values at 141.7 Hz
5. Calculate noise ratio L1/H1
6. Generate visualizations
7. Save results to results/test2_real_results.json

Expected outcome:
- If noise_ratio > 1.5: ✅ FAVORABLE (141.7 Hz more prominent in L1)
- If noise_ratio < 1.5: ❌ DESFAVORABLE

Usage:
    python test2_real_noise_analysis.py

Requirements:
    - gwpy >= 3.0.0
    - numpy >= 1.21.0
    - matplotlib >= 3.5.0
"""

import os
import sys
import json
import numpy as np

# Verificar que matplotlib está disponible
try:
    import matplotlib
    matplotlib.use('Agg')  # Backend sin GUI
    import matplotlib.pyplot as plt
except ImportError:
    print("❌ Error: matplotlib no está instalado")
    print("   Instalar con: pip install matplotlib")
    sys.exit(1)

# Verificar que GWpy está disponible
try:
    from gwpy.timeseries import TimeSeries
except ImportError:
    print("❌ Error: gwpy no está instalado")
    print("   Instalar con: pip install gwpy")
    sys.exit(1)


def download_offsource_data(gps_time, duration=32):
    """
    Descarga datos off-source de H1 y L1
    
    Args:
        gps_time: GPS time para el centro del segmento
        duration: Duración en segundos
    
    Returns:
        dict: {'H1': TimeSeries, 'L1': TimeSeries}
    """
    print(f"\n📡 Descargando datos off-source (GPS: {gps_time})...")

    start = gps_time - duration / 2
    end = gps_time + duration / 2

    data = {}
    for ifo in ['H1', 'L1']:
        print(f"   Descargando {ifo}...")
        try:
            ts = TimeSeries.fetch_open_data(
                ifo, start, end,
                sample_rate=4096,
                cache=True,
                verbose=False
            )
            data[ifo] = ts
            print(f"   ✅ {ifo}: {len(ts)} muestras descargadas")
        except Exception as e:
            print(f"   ❌ Error descargando {ifo}: {e}")
            raise

    return data


def preprocess_data(data):
    """
    Preprocesa datos con pipeline estándar LIGO
    
    Args:
        data: dict con TimeSeries de H1 y L1
    
    Returns:
        dict: datos preprocesados
    """
    print("\n🔧 Preprocesando datos...")

    processed = {}
    for ifo, ts in data.items():
        print(f"   Procesando {ifo}...")

        # Bandpass filter: 20-2000 Hz (rango típico de LIGO)
        ts_filtered = ts.bandpass(20, 2000)

        # Crop para evitar efectos de borde del filtro
        ts_cropped = ts_filtered.crop(*ts_filtered.span.contract(2))

        processed[ifo] = ts_cropped
        print(f"   ✅ {ifo} preprocesado")

    return processed


def calculate_asd(data, fftlength=4):
    """
    Calcula ASD (Amplitude Spectral Density)
    
    Args:
        data: dict con TimeSeries preprocesados
        fftlength: longitud de FFT en segundos (4s → 0.25 Hz resolución)
    
    Returns:
        dict: {'H1': FrequencySeries, 'L1': FrequencySeries}
    """
    print(f"\n📊 Calculando ASD (resolución: {1/fftlength} Hz)...")

    asd = {}
    for ifo, ts in data.items():
        print(f"   Calculando ASD para {ifo}...")

        # Welch method con ventana Hann
        asd_series = ts.asd(fftlength=fftlength, method='median')

        asd[ifo] = asd_series
        print(f"   ✅ {ifo}: ASD calculado ({len(asd_series)} bins de frecuencia)")

    return asd


def extract_141hz_values(asd):
    """
    Extrae valores exactos en 141.7 Hz
    
    Args:
        asd: dict con FrequencySeries
    
    Returns:
        dict: valores en 141.7 Hz para cada detector
    """
    print("\n🎯 Extrayendo valores en 141.7 Hz...")

    target_freq = 141.7
    values = {}

    for ifo, asd_series in asd.items():
        # Encontrar el bin más cercano a 141.7 Hz
        idx = np.argmin(np.abs(asd_series.frequencies.value - target_freq))
        actual_freq = asd_series.frequencies.value[idx]
        value = asd_series.value[idx]

        values[ifo] = {
            'target_frequency': target_freq,
            'actual_frequency': float(actual_freq),
            'asd_value': float(value),
            'unit': str(asd_series.unit)
        }

        print(f"   {ifo}: {value:.6e} {asd_series.unit} @ {actual_freq:.4f} Hz")

    return values


def calculate_noise_ratio(values):
    """
    Calcula ratio de ruido L1/H1
    
    Args:
        values: dict con valores extraídos
    
    Returns:
        float: ratio L1/H1
    """
    print("\n🔢 Calculando noise ratio...")

    h1_value = values['H1']['asd_value']
    l1_value = values['L1']['asd_value']

    ratio = l1_value / h1_value

    print(f"   H1 ASD: {h1_value:.6e}")
    print(f"   L1 ASD: {l1_value:.6e}")
    print(f"   Ratio L1/H1: {ratio:.4f}")

    return ratio


def calculate_coverage(asd, freq_min=140, freq_max=143):
    """
    Calcula porcentaje de cobertura espectral en banda 140-143 Hz
    
    Args:
        asd: dict con FrequencySeries
        freq_min: frecuencia mínima
        freq_max: frecuencia máxima
    
    Returns:
        float: porcentaje de cobertura
    """
    print(f"\n📈 Calculando cobertura espectral ({freq_min}-{freq_max} Hz)...")

    # Para ambos detectores, verificar cuántos bins tienen datos válidos
    coverage_list = []

    for ifo, asd_series in asd.items():
        mask = (asd_series.frequencies.value >= freq_min) & \
               (asd_series.frequencies.value <= freq_max)
        valid_bins = np.sum(~np.isnan(asd_series.value[mask]))
        total_bins = np.sum(mask)
        coverage = (valid_bins / total_bins) * 100 if total_bins > 0 else 0
        coverage_list.append(coverage)
        print(f"   {ifo}: {coverage:.1f}% ({valid_bins}/{total_bins} bins)")

    avg_coverage = np.mean(coverage_list)
    print(f"   Cobertura promedio: {avg_coverage:.1f}%")

    return avg_coverage


def generate_visualizations(asd, values, output_dir='results'):
    """
    Genera visualizaciones de ASD
    
    Args:
        asd: dict con FrequencySeries
        values: dict con valores extraídos
        output_dir: directorio de salida
    """
    print("\n📊 Generando visualizaciones...")

    os.makedirs(output_dir, exist_ok=True)

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))

    # Plot 1: ASD completo (10-500 Hz)
    for ifo, asd_series in asd.items():
        ax1.loglog(asd_series.frequencies, asd_series, label=ifo, alpha=0.7)

    ax1.axvline(141.7, color='r', linestyle='--', linewidth=2,
                label='141.7 Hz target', alpha=0.8)
    ax1.set_xlim(10, 500)
    ax1.set_xlabel('Frequency [Hz]', fontsize=12)
    ax1.set_ylabel('ASD [strain/√Hz]', fontsize=12)
    ax1.set_title('Amplitude Spectral Density - Off-Source Data (1h before GW150914)',
                  fontsize=14, fontweight='bold')
    ax1.legend(loc='upper right', fontsize=10)
    ax1.grid(True, alpha=0.3)

    # Plot 2: Zoom en 140-143 Hz
    for ifo, asd_series in asd.items():
        mask = (asd_series.frequencies.value >= 135) & \
               (asd_series.frequencies.value <= 148)
        ax2.plot(asd_series.frequencies.value[mask],
                 asd_series.value[mask],
                 label=ifo, alpha=0.7, linewidth=2)

    ax2.axvline(141.7, color='r', linestyle='--', linewidth=2,
                label='141.7 Hz target', alpha=0.8)
    ax2.set_xlim(135, 148)
    ax2.set_xlabel('Frequency [Hz]', fontsize=12)
    ax2.set_ylabel('ASD [strain/√Hz]', fontsize=12)
    ax2.set_title('Zoom: 135-148 Hz Band', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right', fontsize=10)
    ax2.grid(True, alpha=0.3)

    # Añadir anotaciones con valores
    for ifo in ['H1', 'L1']:
        val = values[ifo]['asd_value']
        freq = values[ifo]['actual_frequency']
        ax2.annotate(f'{ifo}: {val:.2e}',
                     xy=(freq, val),
                     xytext=(10, 10),
                     textcoords='offset points',
                     fontsize=9,
                     bbox=dict(boxstyle='round,pad=0.5', fc='yellow', alpha=0.5),
                     arrowprops=dict(arrowstyle='->', connectionstyle='arc3,rad=0'))

    plt.tight_layout()

    output_file = os.path.join(output_dir, 'test2_real_asd_analysis.png')
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"   ✅ Visualización guardada: {output_file}")

    plt.close()


def save_results(values, ratio, coverage, output_dir='results'):
    """
    Guarda resultados en JSON
    
    Args:
        values: dict con valores extraídos
        ratio: ratio L1/H1
        coverage: porcentaje de cobertura
        output_dir: directorio de salida
    """
    print("\n💾 Guardando resultados...")

    os.makedirs(output_dir, exist_ok=True)

    # Determinar veredicto
    if ratio > 1.5:
        verdict = "✅ FAVORABLE - 141.7 Hz más prominente en L1"
        verdict_short = "✅ FAVORABLE"
    else:
        verdict = "❌ DESFAVORABLE - No se observa predominancia clara en L1"
        verdict_short = "❌ DESFAVORABLE"

    results = {
        'test_name': 'Test 2: Real Noise Analysis',
        'description': 'Off-source data analysis 1h before GW150914',
        'gps_time_analyzed': 1126255862,  # 1h antes de GW150914
        'duration_seconds': 32,
        'frequency_target': 141.7,
        'h1_asd_141hz': values['H1']['asd_value'],
        'h1_actual_frequency': values['H1']['actual_frequency'],
        'l1_asd_141hz': values['L1']['asd_value'],
        'l1_actual_frequency': values['L1']['actual_frequency'],
        'noise_ratio': round(ratio, 4),
        'coverage_percent': round(coverage, 2),
        'verdict': verdict,
        'verdict_short': verdict_short,
        'threshold_ratio': 1.5,
        'interpretation': {
            'noise_ratio': f"L1/H1 = {ratio:.4f}",
            'coverage': f"{coverage:.1f}% spectral coverage in 140-143 Hz band",
            'conclusion': verdict
        }
    }

    output_file = os.path.join(output_dir, 'test2_real_results.json')
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"   ✅ Resultados guardados: {output_file}")

    return results


def main():
    """Función principal"""

    print("=" * 70)
    print("🌌 TEST 2: REAL NOISE ANALYSIS - OFF-SOURCE GW150914")
    print("=" * 70)
    print("\nObjetivo: Analizar ruido real de LIGO 1h antes de GW150914")
    print("Frecuencia objetivo: 141.7 Hz")
    print()

    try:
        # GPS time de GW150914
        gps_gw150914 = 1126259462

        # Off-source: 1 hora antes (3600 segundos)
        gps_offsource = gps_gw150914 - 3600

        # 1. Descargar datos
        data = download_offsource_data(gps_offsource, duration=32)

        # 2. Preprocesar
        processed = preprocess_data(data)

        # 3. Calcular ASD
        asd = calculate_asd(processed, fftlength=4)

        # 4. Extraer valores en 141.7 Hz
        values = extract_141hz_values(asd)

        # 5. Calcular ratio
        ratio = calculate_noise_ratio(values)

        # 6. Calcular cobertura
        coverage = calculate_coverage(asd)

        # 7. Generar visualizaciones
        generate_visualizations(asd, values)

        # 8. Guardar resultados
        results = save_results(values, ratio, coverage)

        # Resumen final
        print("\n" + "=" * 70)
        print("📋 RESUMEN DE RESULTADOS")
        print("=" * 70)
        print(f"H1 ASD @ 141.7 Hz: {values['H1']['asd_value']:.6e}")
        print(f"L1 ASD @ 141.7 Hz: {values['L1']['asd_value']:.6e}")
        print(f"Noise Ratio L1/H1: {ratio:.4f}")
        print(f"Cobertura espectral: {coverage:.1f}%")
        print(f"\n{results['verdict']}")
        print("=" * 70)

        print("\n✅ Análisis completado exitosamente!")
        print(f"📄 Resultados: results/test2_real_results.json")
        print(f"📊 Visualización: results/test2_real_asd_analysis.png")

        return 0

    except Exception as e:
        print(f"\n❌ Error durante el análisis: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
