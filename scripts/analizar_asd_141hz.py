#!/usr/bin/env python3
"""
Análisis de ASD (Amplitude Spectral Density) a 141.7 Hz para GW150914
======================================================================

Este script implementa los 5 pasos del análisis de ruido:
1. 📥 Descargar segmentos de 32–64 s para H1 y L1 alrededor de GW150914
2. 🧪 Calcular el ASD con gwpy.timeseries.TimeSeries.asd()
3. 📉 Extraer el valor exacto del ASD en 141.7 Hz
4. ⚖️ Comparar amplitud de ruido en L1 vs H1
5. 🔁 Repetir en días sin eventos, mismo tiempo UTC

Uso:
    python scripts/analizar_asd_141hz.py [--duration SECONDS] [--control-days DAYS]
    
Opciones:
    --duration SECONDS    : Duración del segmento en segundos (default: 64)
    --control-days DAYS   : Días antes del evento para control (default: 1,7,30)
    --output-dir DIR      : Directorio de salida (default: results/asd_analysis)
    --no-plot             : No generar gráficas
    --verbose             : Mostrar información detallada

Requiere:
    - gwpy >= 3.0.0
    - numpy >= 1.21.0
    - matplotlib >= 3.5.0
    
Autor: Análisis GW150914 - 141.7 Hz Project
Fecha: 2025-10-24
"""

import argparse
import os
import sys
from datetime import datetime, timedelta

try:
    import numpy as np
    from gwpy.timeseries import TimeSeries
    import matplotlib
    matplotlib.use('Agg')  # Backend sin GUI
    import matplotlib.pyplot as plt
except ImportError as e:
    print(f"❌ Error: Falta dependencia requerida: {e}")
    print("   Instalar con: pip install gwpy numpy matplotlib")
    sys.exit(1)


# Parámetros del evento GW150914
GW150914_GPS_TIME = 1126259462.423  # Tiempo GPS del merger
TARGET_FREQUENCY = 141.7  # Hz - Frecuencia objetivo del análisis


def download_segment(detector, gps_start, duration, verbose=False):
    """
    Descargar segmento de datos de un detector LIGO.
    
    Args:
        detector: Nombre del detector ('H1' o 'L1')
        gps_start: Tiempo GPS de inicio
        duration: Duración del segmento en segundos
        verbose: Mostrar información detallada
        
    Returns:
        TimeSeries con los datos descargados o None si hay error
    """
    gps_end = gps_start + duration
    
    if verbose:
        print(f"   Descargando {detector}: GPS {gps_start} - {gps_end} ({duration}s)")
    
    try:
        data = TimeSeries.fetch_open_data(
            detector, 
            gps_start, 
            gps_end,
            sample_rate=4096,
            verbose=verbose
        )
        
        if verbose:
            print(f"   ✅ {detector}: {len(data)} muestras @ {data.sample_rate} Hz")
        
        return data
        
    except Exception as e:
        print(f"   ❌ Error descargando {detector}: {e}")
        return None


def calculate_asd(data, fftlength=4, overlap=None, verbose=False):
    """
    Calcular ASD (Amplitude Spectral Density) usando el método de Welch.
    
    Args:
        data: TimeSeries con los datos
        fftlength: Longitud de cada FFT en segundos (default: 4)
        overlap: Solapamiento entre FFTs (default: fftlength/2)
        verbose: Mostrar información detallada
        
    Returns:
        FrequencySeries con el ASD calculado
    """
    if verbose:
        print(f"   Calculando ASD (fftlength={fftlength}s)...")
    
    try:
        # Calcular ASD usando el método integrado de gwpy
        asd = data.asd(fftlength=fftlength, overlap=overlap)
        
        if verbose:
            print(f"   ✅ ASD calculado: {len(asd)} puntos de frecuencia")
            print(f"   Rango de frecuencias: {asd.frequencies[0]:.2f} - {asd.frequencies[-1]:.2f} Hz")
        
        return asd
        
    except Exception as e:
        print(f"   ❌ Error calculando ASD: {e}")
        return None


def extract_asd_at_frequency(asd, target_freq, verbose=False):
    """
    Extraer el valor exacto del ASD en una frecuencia específica.
    
    Args:
        asd: FrequencySeries con el ASD
        target_freq: Frecuencia objetivo en Hz
        verbose: Mostrar información detallada
        
    Returns:
        tuple: (frecuencia exacta, valor del ASD)
    """
    if verbose:
        print(f"   Extrayendo ASD en {target_freq} Hz...")
    
    # Encontrar el índice más cercano a la frecuencia objetivo
    freqs = asd.frequencies.value
    idx = np.argmin(np.abs(freqs - target_freq))
    
    exact_freq = freqs[idx]
    asd_value = asd.value[idx]
    
    if verbose:
        freq_diff = exact_freq - target_freq
        print(f"   ✅ Frecuencia más cercana: {exact_freq:.6f} Hz (Δ = {freq_diff:.6f} Hz)")
        print(f"   ✅ ASD en {exact_freq:.6f} Hz: {asd_value:.6e} Hz^(-1/2)")
    
    return exact_freq, asd_value


def analyze_detector_pair(h1_data, l1_data, duration, verbose=False):
    """
    Analizar par de detectores y comparar ruido en 141.7 Hz.
    
    Args:
        h1_data: TimeSeries de H1
        l1_data: TimeSeries de L1
        duration: Duración del segmento
        verbose: Mostrar información detallada
        
    Returns:
        dict con resultados del análisis
    """
    results = {
        'duration': duration,
        'h1': {},
        'l1': {},
        'comparison': {}
    }
    
    # Calcular ASD para ambos detectores
    print(f"\n🧪 Calculando ASD para ambos detectores...")
    
    # H1
    print(f"📡 H1 (Hanford):")
    h1_asd = calculate_asd(h1_data, verbose=verbose)
    if h1_asd is None:
        print("❌ No se pudo calcular ASD para H1")
        return None
    
    h1_freq, h1_asd_value = extract_asd_at_frequency(h1_asd, TARGET_FREQUENCY, verbose=verbose)
    results['h1'] = {
        'asd': h1_asd,
        'freq': h1_freq,
        'asd_value': h1_asd_value
    }
    
    # L1
    print(f"📡 L1 (Livingston):")
    l1_asd = calculate_asd(l1_data, verbose=verbose)
    if l1_asd is None:
        print("❌ No se pudo calcular ASD para L1")
        return None
    
    l1_freq, l1_asd_value = extract_asd_at_frequency(l1_asd, TARGET_FREQUENCY, verbose=verbose)
    results['l1'] = {
        'asd': l1_asd,
        'freq': l1_freq,
        'asd_value': l1_asd_value
    }
    
    # Comparar amplitudes de ruido
    print(f"\n⚖️  Comparación de ruido en {TARGET_FREQUENCY} Hz:")
    ratio = l1_asd_value / h1_asd_value
    diff_percent = (ratio - 1.0) * 100
    
    results['comparison'] = {
        'ratio_l1_h1': ratio,
        'diff_percent': diff_percent
    }
    
    print(f"   H1 ASD: {h1_asd_value:.6e} Hz^(-1/2)")
    print(f"   L1 ASD: {l1_asd_value:.6e} Hz^(-1/2)")
    print(f"   Ratio L1/H1: {ratio:.4f}")
    print(f"   Diferencia: {diff_percent:+.2f}%")
    
    if abs(diff_percent) < 10:
        print(f"   ✅ Niveles de ruido similares (< 10% diferencia)")
    elif ratio > 1:
        print(f"   ⚠️  L1 tiene {diff_percent:.1f}% MÁS ruido que H1")
    else:
        print(f"   ⚠️  H1 tiene {-diff_percent:.1f}% MÁS ruido que L1")
    
    return results


def plot_asd_comparison(results_list, output_dir, verbose=False):
    """
    Generar gráficas comparativas de ASD.
    
    Args:
        results_list: Lista de diccionarios con resultados
        output_dir: Directorio de salida
        verbose: Mostrar información detallada
    """
    if verbose:
        print(f"\n📊 Generando gráficas...")
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Gráfica 1: ASDs completos de todos los análisis
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))
    
    colors = plt.cm.viridis(np.linspace(0, 1, len(results_list)))
    
    for i, result in enumerate(results_list):
        label = result.get('label', f'Analysis {i+1}')
        color = colors[i]
        
        if result is None or 'h1' not in result or 'l1' not in result:
            continue
        
        # H1
        h1_asd = result['h1']['asd']
        ax1.loglog(h1_asd.frequencies, h1_asd, 
                   label=label, color=color, alpha=0.7)
        
        # L1
        l1_asd = result['l1']['asd']
        ax2.loglog(l1_asd.frequencies, l1_asd,
                   label=label, color=color, alpha=0.7)
    
    # Marcar frecuencia objetivo
    for ax in [ax1, ax2]:
        ax.axvline(TARGET_FREQUENCY, color='red', linestyle='--', 
                   linewidth=2, label=f'{TARGET_FREQUENCY} Hz', zorder=10)
        ax.set_xlabel('Frequency (Hz)')
        ax.set_ylabel('ASD [Hz$^{-1/2}$]')
        ax.grid(True, which='both', alpha=0.3)
        ax.legend(loc='best', fontsize=8)
        ax.set_xlim(10, 500)
    
    ax1.set_title('H1 (Hanford) - Amplitude Spectral Density')
    ax2.set_title('L1 (Livingston) - Amplitude Spectral Density')
    
    plt.tight_layout()
    output_file = os.path.join(output_dir, 'asd_comparison_full.png')
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    if verbose:
        print(f"   ✅ Guardado: {output_file}")
    
    # Gráfica 2: Zoom en 141.7 Hz
    fig, ax = plt.subplots(figsize=(12, 6))
    
    freq_range = [TARGET_FREQUENCY - 10, TARGET_FREQUENCY + 10]
    
    for i, result in enumerate(results_list):
        if result is None or 'h1' not in result or 'l1' not in result:
            continue
        
        label = result.get('label', f'Analysis {i+1}')
        color = colors[i]
        
        # Extraer y plotear región de interés
        h1_asd = result['h1']['asd']
        l1_asd = result['l1']['asd']
        
        # Máscara de frecuencias
        h1_mask = (h1_asd.frequencies.value >= freq_range[0]) & \
                  (h1_asd.frequencies.value <= freq_range[1])
        l1_mask = (l1_asd.frequencies.value >= freq_range[0]) & \
                  (l1_asd.frequencies.value <= freq_range[1])
        
        ax.semilogy(h1_asd.frequencies.value[h1_mask], 
                    h1_asd.value[h1_mask],
                    label=f'H1 - {label}', color=color, 
                    linestyle='-', alpha=0.7)
        ax.semilogy(l1_asd.frequencies.value[l1_mask], 
                    l1_asd.value[l1_mask],
                    label=f'L1 - {label}', color=color, 
                    linestyle='--', alpha=0.7)
    
    ax.axvline(TARGET_FREQUENCY, color='red', linestyle=':', 
               linewidth=2, label=f'{TARGET_FREQUENCY} Hz', zorder=10)
    ax.set_xlabel('Frequency (Hz)')
    ax.set_ylabel('ASD [Hz$^{-1/2}$]')
    ax.set_title(f'ASD Zoom around {TARGET_FREQUENCY} Hz')
    ax.grid(True, alpha=0.3)
    ax.legend(loc='best', fontsize=8)
    
    plt.tight_layout()
    output_file = os.path.join(output_dir, 'asd_comparison_zoom.png')
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    if verbose:
        print(f"   ✅ Guardado: {output_file}")
    
    # Gráfica 3: Comparación de ratios L1/H1
    fig, ax = plt.subplots(figsize=(10, 6))
    
    labels = []
    ratios = []
    
    for i, result in enumerate(results_list):
        if result is None or 'comparison' not in result:
            continue
        
        label = result.get('label', f'Analysis {i+1}')
        ratio = result['comparison']['ratio_l1_h1']
        
        labels.append(label)
        ratios.append(ratio)
    
    if ratios:
        bars = ax.bar(range(len(ratios)), ratios, color=colors[:len(ratios)])
        ax.axhline(1.0, color='red', linestyle='--', linewidth=2, label='Equal noise')
        ax.set_xticks(range(len(labels)))
        ax.set_xticklabels(labels, rotation=45, ha='right')
        ax.set_ylabel('L1/H1 Noise Ratio at 141.7 Hz')
        ax.set_title('Noise Comparison: L1 vs H1')
        ax.grid(True, axis='y', alpha=0.3)
        ax.legend()
        
        plt.tight_layout()
        output_file = os.path.join(output_dir, 'noise_ratio_comparison.png')
        plt.savefig(output_file, dpi=150, bbox_inches='tight')
        plt.close()
        
        if verbose:
            print(f"   ✅ Guardado: {output_file}")


def analyze_gw150914(duration=64, control_days=None, output_dir='results/asd_analysis', 
                     make_plots=True, verbose=False):
    """
    Ejecutar análisis completo de ASD para GW150914.
    
    Args:
        duration: Duración del segmento en segundos (default: 64)
        control_days: Lista de días antes del evento para análisis de control
        output_dir: Directorio de salida
        make_plots: Generar gráficas
        verbose: Mostrar información detallada
        
    Returns:
        dict con todos los resultados
    """
    print("🌌 ANÁLISIS DE ASD EN 141.7 Hz - GW150914")
    print("=" * 70)
    print(f"Frecuencia objetivo: {TARGET_FREQUENCY} Hz")
    print(f"Duración del segmento: {duration} s")
    print("=" * 70)
    
    if control_days is None:
        control_days = [1, 7, 30]  # Default: 1 día, 1 semana, 1 mes antes
    
    all_results = []
    
    # Paso 1 & 2: Análisis del evento GW150914
    print(f"\n📥 PASO 1-2: Descargando y analizando GW150914 (evento)")
    print("-" * 70)
    
    gps_start = GW150914_GPS_TIME - duration / 2
    
    h1_data = download_segment('H1', gps_start, duration, verbose=verbose)
    l1_data = download_segment('L1', gps_start, duration, verbose=verbose)
    
    if h1_data is None or l1_data is None:
        print("❌ Error: No se pudieron descargar los datos del evento")
        return None
    
    event_results = analyze_detector_pair(h1_data, l1_data, duration, verbose=verbose)
    if event_results:
        event_results['label'] = 'GW150914 (Event)'
        event_results['type'] = 'event'
        event_results['gps_start'] = gps_start
        all_results.append(event_results)
    
    # Paso 5: Repetir análisis en días sin eventos (controles)
    print(f"\n🔁 PASO 5: Analizando días de control (sin eventos)")
    print("-" * 70)
    
    for days in control_days:
        print(f"\n📅 Control: {days} día(s) antes del evento")
        
        # Calcular GPS time del control (mismo tiempo UTC, diferente día)
        control_gps = GW150914_GPS_TIME - (days * 86400)  # 86400 s = 1 día
        control_gps_start = control_gps - duration / 2
        
        h1_control = download_segment('H1', control_gps_start, duration, verbose=verbose)
        l1_control = download_segment('L1', control_gps_start, duration, verbose=verbose)
        
        if h1_control is None or l1_control is None:
            print(f"⚠️  No se pudieron descargar datos del control ({days} días antes)")
            continue
        
        control_results = analyze_detector_pair(h1_control, l1_control, duration, verbose=verbose)
        if control_results:
            control_results['label'] = f'Control -{days}d'
            control_results['type'] = 'control'
            control_results['days_before'] = days
            control_results['gps_start'] = control_gps_start
            all_results.append(control_results)
    
    # Generar resumen
    print(f"\n📊 RESUMEN DE RESULTADOS")
    print("=" * 70)
    
    for result in all_results:
        if result is None:
            continue
        
        label = result['label']
        h1_asd = result['h1']['asd_value']
        l1_asd = result['l1']['asd_value']
        ratio = result['comparison']['ratio_l1_h1']
        
        print(f"\n{label}:")
        print(f"  H1 @ {TARGET_FREQUENCY} Hz: {h1_asd:.6e} Hz^(-1/2)")
        print(f"  L1 @ {TARGET_FREQUENCY} Hz: {l1_asd:.6e} Hz^(-1/2)")
        print(f"  Ratio L1/H1: {ratio:.4f}")
    
    # Generar gráficas si está habilitado
    if make_plots and all_results:
        plot_asd_comparison(all_results, output_dir, verbose=verbose)
    
    # Guardar resultados en archivo
    save_results_to_file(all_results, output_dir, verbose=verbose)
    
    print(f"\n✅ ANÁLISIS COMPLETADO")
    print("=" * 70)
    
    return {
        'all_results': all_results,
        'output_dir': output_dir
    }


def save_results_to_file(results, output_dir, verbose=False):
    """Guardar resultados en archivo de texto."""
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, 'asd_results.txt')
    
    with open(output_file, 'w') as f:
        f.write("ANÁLISIS DE ASD EN 141.7 Hz - GW150914\n")
        f.write("=" * 70 + "\n")
        f.write(f"Fecha de análisis: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Frecuencia objetivo: {TARGET_FREQUENCY} Hz\n")
        f.write("=" * 70 + "\n\n")
        
        for result in results:
            if result is None:
                continue
            
            label = result['label']
            f.write(f"\n{label}:\n")
            f.write("-" * 40 + "\n")
            f.write(f"GPS Start: {result['gps_start']:.3f}\n")
            f.write(f"Duration: {result['duration']} s\n")
            f.write(f"\nH1 (Hanford):\n")
            f.write(f"  Frequency: {result['h1']['freq']:.6f} Hz\n")
            f.write(f"  ASD: {result['h1']['asd_value']:.6e} Hz^(-1/2)\n")
            f.write(f"\nL1 (Livingston):\n")
            f.write(f"  Frequency: {result['l1']['freq']:.6f} Hz\n")
            f.write(f"  ASD: {result['l1']['asd_value']:.6e} Hz^(-1/2)\n")
            f.write(f"\nComparison:\n")
            f.write(f"  Ratio L1/H1: {result['comparison']['ratio_l1_h1']:.4f}\n")
            f.write(f"  Difference: {result['comparison']['diff_percent']:+.2f}%\n")
    
    if verbose:
        print(f"   ✅ Resultados guardados: {output_file}")


def main():
    """Función principal con parsing de argumentos."""
    parser = argparse.ArgumentParser(
        description='Análisis de ASD en 141.7 Hz para GW150914',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Ejemplos:
  # Análisis básico con 64 segundos
  python scripts/analizar_asd_141hz.py
  
  # Análisis con 32 segundos y controles personalizados
  python scripts/analizar_asd_141hz.py --duration 32 --control-days 1 3 7
  
  # Análisis sin gráficas
  python scripts/analizar_asd_141hz.py --no-plot
  
  # Análisis detallado
  python scripts/analizar_asd_141hz.py --verbose
        """
    )
    
    parser.add_argument('--duration', type=float, default=64,
                        help='Duración del segmento en segundos (default: 64)')
    parser.add_argument('--control-days', type=int, nargs='+', default=[1, 7, 30],
                        help='Días antes del evento para controles (default: 1 7 30)')
    parser.add_argument('--output-dir', type=str, default='results/asd_analysis',
                        help='Directorio de salida (default: results/asd_analysis)')
    parser.add_argument('--no-plot', action='store_true',
                        help='No generar gráficas')
    parser.add_argument('--verbose', action='store_true',
                        help='Mostrar información detallada')
    
    args = parser.parse_args()
    
    # Validaciones
    if args.duration < 4:
        print("❌ Error: La duración debe ser al menos 4 segundos (para calcular FFT)")
        return 1
    
    if args.duration > 128:
        print("⚠️  Advertencia: Duración > 128s puede requerir mucho tiempo de descarga")
    
    # Ejecutar análisis
    try:
        results = analyze_gw150914(
            duration=args.duration,
            control_days=args.control_days,
            output_dir=args.output_dir,
            make_plots=not args.no_plot,
            verbose=args.verbose
        )
        
        if results is None:
            print("❌ El análisis falló")
            return 1
        
        print(f"\n📁 Resultados guardados en: {args.output_dir}")
        return 0
        
    except KeyboardInterrupt:
        print("\n\n⚠️  Análisis interrumpido por el usuario")
        return 1
    except Exception as e:
        print(f"\n❌ Error inesperado: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
