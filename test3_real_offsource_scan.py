#!/usr/bin/env python3
"""
Test 3: Real Off-Source Scan - 10-Day Survey

Analyzes 10 segments of 32s off-source data from 10 days before GW150914
to determine if 141.7 Hz is a persistent spectral line or a transient feature.

Process:
1. Download 10 segments of 32s (spaced over 10 days before GW150914)
2. Analyze each with same pipeline as Test 2
3. Search for peaks in 140-143 Hz band
4. Calculate SNR for each segment
5. Compare with SNR during GW150914 (H1 SNR = 7.47)
6. Determine if persistent line
7. Visualize SNR timeline
8. Save results to results/test3_real_results.json

Expected outcome:
- If max(SNR) < 7.47 and n_above_7 == 0: ✅ FAVORABLE (transient, not persistent)
- If max(SNR) ≥ 7.47 or n_above_7 > 0: ❌ DESFAVORABLE (persistent line)

Usage:
    python test3_real_offsource_scan.py

Requirements:
    - gwpy >= 3.0.0
    - numpy >= 1.21.0
    - matplotlib >= 3.5.0
"""

import os
import sys
import json
import numpy as np
from datetime import datetime, timedelta

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


def generate_scan_times(gps_center, n_segments=10, days_before=10):
    """
    Genera tiempos GPS para escaneo
    
    Args:
        gps_center: GPS time central (GW150914)
        n_segments: número de segmentos
        days_before: días antes del evento
    
    Returns:
        list: tiempos GPS para cada segmento
    """
    print(f"\n📅 Generando {n_segments} tiempos de escaneo ({days_before} días antes)...")

    seconds_before = days_before * 24 * 3600  # días a segundos
    gps_start = gps_center - seconds_before

    # Distribuir uniformemente en el tiempo
    time_step = seconds_before / (n_segments + 1)

    scan_times = []
    for i in range(1, n_segments + 1):
        gps_time = gps_start + i * time_step
        scan_times.append(gps_time)

        # Convertir GPS a fecha legible (aproximado)
        # GPS epoch: 1980-01-06 00:00:00 UTC
        # GPS offset: ~18 segundos (leap seconds al 2015)
        unix_time = gps_time - 315964800 + 18
        date = datetime.utcfromtimestamp(unix_time)

        print(f"   Segmento {i}: GPS {gps_time:.0f} ({date.strftime('%Y-%m-%d %H:%M:%S')} UTC)")

    return scan_times


def download_segment_data(gps_time, duration=32, ifo='H1'):
    """
    Descarga un segmento de datos
    
    Args:
        gps_time: GPS time central
        duration: duración en segundos
        ifo: detector (H1 o L1)
    
    Returns:
        TimeSeries o None si falla
    """
    start = gps_time - duration / 2
    end = gps_time + duration / 2

    try:
        ts = TimeSeries.fetch_open_data(
            ifo, start, end,
            sample_rate=4096,
            cache=True,
            verbose=False
        )
        return ts
    except Exception as e:
        print(f"      ⚠️ Error descargando {ifo} @ GPS {gps_time:.0f}: {e}")
        return None


def analyze_segment(ts, segment_id):
    """
    Analiza un segmento: preprocesa, calcula ASD, busca picos
    
    Args:
        ts: TimeSeries
        segment_id: identificador del segmento
    
    Returns:
        dict: resultados del análisis
    """
    if ts is None:
        return None

    try:
        # Preprocesar
        ts_filtered = ts.bandpass(20, 2000)
        ts_cropped = ts_filtered.crop(*ts_filtered.span.contract(2))

        # Calcular ASD
        asd = ts_cropped.asd(fftlength=4, method='median')

        # Buscar en banda 140-143 Hz
        mask = (asd.frequencies.value >= 140) & (asd.frequencies.value <= 143)
        band_freqs = asd.frequencies.value[mask]
        band_asd = asd.value[mask]

        # Encontrar pico máximo
        if len(band_asd) > 0:
            max_idx = np.argmax(band_asd)
            peak_freq = band_freqs[max_idx]
            peak_asd = band_asd[max_idx]

            # Valor en 141.7 Hz (lo más cercano)
            target_idx = np.argmin(np.abs(asd.frequencies.value - 141.7))
            asd_141hz = asd.value[target_idx]
            freq_141hz = asd.frequencies.value[target_idx]
        else:
            peak_freq = np.nan
            peak_asd = np.nan
            asd_141hz = np.nan
            freq_141hz = np.nan

        # Calcular SNR (relativo al ruido medio de la banda)
        if len(band_asd) > 0 and not np.isnan(peak_asd):
            noise_floor = np.median(band_asd)
            snr = peak_asd / noise_floor if noise_floor > 0 else 0
        else:
            snr = 0

        return {
            'segment_id': segment_id,
            'success': True,
            'peak_frequency': float(peak_freq) if not np.isnan(peak_freq) else None,
            'peak_asd': float(peak_asd) if not np.isnan(peak_asd) else None,
            'asd_141hz': float(asd_141hz) if not np.isnan(asd_141hz) else None,
            'freq_141hz': float(freq_141hz) if not np.isnan(freq_141hz) else None,
            'snr': float(snr),
            'asd_object': asd  # para visualización
        }

    except Exception as e:
        print(f"      ⚠️ Error analizando segmento {segment_id}: {e}")
        return None


def scan_offsource_segments(scan_times, ifo='H1'):
    """
    Escanea múltiples segmentos off-source
    
    Args:
        scan_times: lista de GPS times
        ifo: detector
    
    Returns:
        list: resultados de cada segmento
    """
    print(f"\n🔍 Escaneando {len(scan_times)} segmentos ({ifo})...")

    results = []

    for i, gps_time in enumerate(scan_times, 1):
        print(f"\n   Segmento {i}/{len(scan_times)} (GPS {gps_time:.0f})...")

        # Descargar
        print(f"      Descargando...")
        ts = download_segment_data(gps_time, ifo=ifo)

        if ts is None:
            results.append({
                'segment_id': i,
                'gps_time': gps_time,
                'success': False,
                'snr': 0
            })
            continue

        # Analizar
        print(f"      Analizando...")
        analysis = analyze_segment(ts, i)

        if analysis is None:
            results.append({
                'segment_id': i,
                'gps_time': gps_time,
                'success': False,
                'snr': 0
            })
            continue

        # Añadir GPS time
        analysis['gps_time'] = gps_time
        results.append(analysis)

        if analysis['success']:
            print(f"      ✅ Peak: {analysis['peak_frequency']:.2f} Hz, "
                  f"ASD: {analysis['peak_asd']:.2e}, SNR: {analysis['snr']:.2f}")

    return results


def calculate_statistics(results):
    """
    Calcula estadísticas del escaneo
    
    Args:
        results: lista de resultados
    
    Returns:
        dict: estadísticas
    """
    print("\n📊 Calculando estadísticas...")

    successful = [r for r in results if r.get('success', False)]
    snrs = [r['snr'] for r in successful if 'snr' in r]

    if len(snrs) == 0:
        print("   ⚠️ No hay datos válidos para calcular estadísticas")
        return {
            'n_segments': len(results),
            'n_successful': 0,
            'max_snr': 0,
            'mean_snr': 0,
            'std_snr': 0,
            'n_above_7': 0
        }

    max_snr = np.max(snrs)
    mean_snr = np.mean(snrs)
    std_snr = np.std(snrs)
    n_above_7 = np.sum(np.array(snrs) >= 7.0)

    stats = {
        'n_segments': len(results),
        'n_successful': len(successful),
        'max_snr': float(max_snr),
        'mean_snr': float(mean_snr),
        'std_snr': float(std_snr),
        'n_above_7': int(n_above_7)
    }

    print(f"   Segmentos exitosos: {stats['n_successful']}/{stats['n_segments']}")
    print(f"   SNR máximo: {stats['max_snr']:.2f}")
    print(f"   SNR promedio: {stats['mean_snr']:.2f} ± {stats['std_snr']:.2f}")
    print(f"   Segmentos con SNR ≥ 7.0: {stats['n_above_7']}")

    return stats


def generate_timeline_visualization(results, stats, output_dir='results'):
    """
    Genera visualización de timeline de SNR
    
    Args:
        results: lista de resultados
        stats: estadísticas
        output_dir: directorio de salida
    """
    print("\n📊 Generando visualización de timeline...")

    os.makedirs(output_dir, exist_ok=True)

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(14, 10))

    # Extraer datos válidos
    valid_results = [r for r in results if r.get('success', False)]
    segment_ids = [r['segment_id'] for r in valid_results]
    snrs = [r['snr'] for r in valid_results]

    if len(snrs) == 0:
        print("   ⚠️ No hay datos válidos para graficar")
        return

    # Plot 1: SNR Timeline
    ax1.plot(segment_ids, snrs, 'bo-', linewidth=2, markersize=8, label='SNR observado')
    ax1.axhline(7.47, color='r', linestyle='--', linewidth=2,
                label='SNR de GW150914 (H1)', alpha=0.8)
    ax1.axhline(stats['mean_snr'], color='g', linestyle=':', linewidth=2,
                label=f"SNR promedio: {stats['mean_snr']:.2f}", alpha=0.8)

    # Sombrear región ±1σ
    ax1.fill_between(segment_ids,
                     stats['mean_snr'] - stats['std_snr'],
                     stats['mean_snr'] + stats['std_snr'],
                     alpha=0.2, color='g', label='±1σ')

    ax1.set_xlabel('Segment ID', fontsize=12)
    ax1.set_ylabel('SNR', fontsize=12)
    ax1.set_title('SNR Timeline - Off-Source Scan (10 days before GW150914)',
                  fontsize=14, fontweight='bold')
    ax1.legend(loc='upper right', fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.set_ylim(bottom=0)

    # Plot 2: Histograma de SNR
    ax2.hist(snrs, bins=10, alpha=0.7, color='blue', edgecolor='black')
    ax2.axvline(7.47, color='r', linestyle='--', linewidth=2,
                label='SNR de GW150914 (H1)')
    ax2.axvline(stats['mean_snr'], color='g', linestyle=':', linewidth=2,
                label=f"SNR promedio: {stats['mean_snr']:.2f}")

    ax2.set_xlabel('SNR', fontsize=12)
    ax2.set_ylabel('Frequency', fontsize=12)
    ax2.set_title('SNR Distribution', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right', fontsize=10)
    ax2.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()

    output_file = os.path.join(output_dir, 'test3_real_snr_timeline.png')
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"   ✅ Visualización guardada: {output_file}")

    plt.close()


def generate_asd_comparison(results, output_dir='results'):
    """
    Genera comparación de ASD de todos los segmentos
    
    Args:
        results: lista de resultados
        output_dir: directorio de salida
    """
    print("\n📊 Generando comparación de ASD...")

    os.makedirs(output_dir, exist_ok=True)

    fig, ax = plt.subplots(figsize=(12, 8))

    # Plotear ASD de cada segmento válido
    valid_results = [r for r in results if r.get('success', False) and 'asd_object' in r]

    if len(valid_results) == 0:
        print("   ⚠️ No hay datos ASD válidos para graficar")
        return

    for r in valid_results:
        asd = r['asd_object']
        mask = (asd.frequencies.value >= 135) & (asd.frequencies.value <= 148)
        ax.plot(asd.frequencies.value[mask], asd.value[mask],
                alpha=0.5, linewidth=1, label=f"Seg {r['segment_id']}")

    # Marcar 141.7 Hz
    ax.axvline(141.7, color='r', linestyle='--', linewidth=2,
               label='141.7 Hz target', alpha=0.8)

    ax.set_xlim(135, 148)
    ax.set_xlabel('Frequency [Hz]', fontsize=12)
    ax.set_ylabel('ASD [strain/√Hz]', fontsize=12)
    ax.set_title('ASD Comparison - All Off-Source Segments (135-148 Hz)',
                 fontsize=14, fontweight='bold')

    # Leyenda fuera del gráfico si hay muchos segmentos
    if len(valid_results) > 5:
        ax.legend(loc='center left', bbox_to_anchor=(1, 0.5), fontsize=8)
    else:
        ax.legend(loc='upper right', fontsize=9)

    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    output_file = os.path.join(output_dir, 'test3_real_asd_comparison.png')
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"   ✅ Comparación ASD guardada: {output_file}")

    plt.close()


def save_results(results, stats, output_dir='results'):
    """
    Guarda resultados en JSON
    
    Args:
        results: lista de resultados
        stats: estadísticas
        output_dir: directorio de salida
    """
    print("\n💾 Guardando resultados...")

    os.makedirs(output_dir, exist_ok=True)

    # Determinar veredicto
    gw150914_snr_h1 = 7.47

    if stats['max_snr'] < gw150914_snr_h1 and stats['n_above_7'] == 0:
        verdict = "✅ FAVORABLE - 141.7 Hz es transitorio, no línea persistente"
        verdict_short = "✅ FAVORABLE"
    else:
        verdict = "❌ DESFAVORABLE - Posible línea espectral persistente"
        verdict_short = "❌ DESFAVORABLE"

    # Limpiar resultados para JSON (remover objetos ASD)
    results_clean = []
    for r in results:
        r_clean = {k: v for k, v in r.items() if k != 'asd_object'}
        results_clean.append(r_clean)

    output_data = {
        'test_name': 'Test 3: Real Off-Source Scan',
        'description': '10 segments scanned over 10 days before GW150914',
        'detector': 'H1',
        'gps_gw150914': 1126259462,
        'n_segments': stats['n_segments'],
        'n_successful': stats['n_successful'],
        'frequency_band': [140, 143],
        'target_frequency': 141.7,
        'statistics': {
            'h1_snr_max': round(stats['max_snr'], 2),
            'h1_snr_mean': round(stats['mean_snr'], 2),
            'h1_snr_std': round(stats['std_snr'], 2),
            'h1_n_above_7': stats['n_above_7']
        },
        'comparison': {
            'gw150914_h1_snr': gw150914_snr_h1,
            'max_offsource_snr': round(stats['max_snr'], 2),
            'ratio': round(stats['max_snr'] / gw150914_snr_h1, 3) if gw150914_snr_h1 > 0 else 0
        },
        'verdict': verdict,
        'verdict_short': verdict_short,
        'segments': results_clean
    }

    output_file = os.path.join(output_dir, 'test3_real_results.json')
    with open(output_file, 'w') as f:
        json.dump(output_data, f, indent=2)

    print(f"   ✅ Resultados guardados: {output_file}")

    return output_data


def main():
    """Función principal"""

    print("=" * 70)
    print("🌌 TEST 3: REAL OFF-SOURCE SCAN - 10-DAY SURVEY")
    print("=" * 70)
    print("\nObjetivo: Determinar si 141.7 Hz es línea persistente o transitoria")
    print("Método: Escanear 10 segmentos de 32s durante 10 días antes de GW150914")
    print()

    try:
        # GPS time de GW150914
        gps_gw150914 = 1126259462

        # Generar tiempos de escaneo
        scan_times = generate_scan_times(gps_gw150914, n_segments=10, days_before=10)

        # Escanear segmentos (H1)
        results = scan_offsource_segments(scan_times, ifo='H1')

        # Calcular estadísticas
        stats = calculate_statistics(results)

        # Generar visualizaciones
        generate_timeline_visualization(results, stats)
        generate_asd_comparison(results)

        # Guardar resultados
        output_data = save_results(results, stats)

        # Resumen final
        print("\n" + "=" * 70)
        print("📋 RESUMEN DE RESULTADOS")
        print("=" * 70)
        print(f"Segmentos analizados: {stats['n_successful']}/{stats['n_segments']}")
        print(f"SNR máximo observado: {stats['max_snr']:.2f}")
        print("SNR durante GW150914 (H1): 7.47")
        print(f"Segmentos con SNR ≥ 7.0: {stats['n_above_7']}")
        print(f"\n{output_data['verdict']}")
        print("=" * 70)

        print("\n✅ Análisis completado exitosamente!")
        print("📄 Resultados: results/test3_real_results.json")
        print("📊 Visualizaciones:")
        print("   - results/test3_real_snr_timeline.png")
        print("   - results/test3_real_asd_comparison.png")

        return 0

    except Exception as e:
        print(f"\n❌ Error durante el análisis: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
