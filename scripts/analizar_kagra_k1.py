#!/usr/bin/env python3
"""
Análisis de 141.7 Hz en KAGRA (K1) - O4 Open Data
Analiza un segmento de datos públicos de KAGRA para detectar la señal de 141.7 Hz

GPS: 1370294440 – 1370294472 (32 s)
Fecha: 2023-06-16
Detector: K1 (KAGRA)
"""

import os
import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
from gwpy.timeseries import TimeSeries

def analyze_kagra_141hz():
    """
    Analiza datos de KAGRA para detectar señal en 141.7 Hz
    
    Returns:
        dict: Resultados del análisis incluyendo SNR, frecuencia detectada, etc.
    """
    # Configuración
    start = 1370294440
    end = 1370294472
    target_band = [141.4, 142.0]
    target_freq = 141.7
    
    print("🔍 Test de 141.7 Hz en KAGRA (K1)")
    print("=" * 60)
    print(f"GPS Time: {start} - {end} (32 segundos)")
    print(f"Fecha: 2023-06-16")
    print(f"Banda objetivo: {target_band[0]} - {target_band[1]} Hz")
    print(f"Frecuencia objetivo: {target_freq} Hz")
    print()
    
    # Descargar datos de KAGRA
    print("⏳ Descargando datos de KAGRA...")
    try:
        k1 = TimeSeries.fetch_open_data('K1', start, end, cache=True)
        print("✅ Datos recibidos.")
        print(f"   Duración: {k1.duration.value:.2f} s")
        print(f"   Tasa de muestreo: {k1.sample_rate.value:.0f} Hz")
    except Exception as e:
        print(f"❌ Error descargando datos: {e}")
        return None
    
    # Procesamiento - aplicar filtro de banda
    print(f"\n🔧 Aplicando filtro de banda {target_band[0]}-{target_band[1]} Hz...")
    k1_band = k1.bandpass(*target_band)
    
    # Calcular SNR
    max_amplitude = np.max(np.abs(k1_band.value))
    std_deviation = np.std(k1_band.value)
    snr_k1 = max_amplitude / std_deviation
    
    print(f"\n📊 SNR KAGRA @141.7 Hz = {snr_k1:.2f}")
    
    # Interpretación del resultado
    print("\n📈 INTERPRETACIÓN:")
    if snr_k1 > 5.0:
        print("   ✅ SNR > 5.0: Posible señal coherente también en KAGRA")
        interpretation = "coherent_signal"
    elif snr_k1 >= 2.0:
        print("   ⚠️  SNR 2-4.9: Marginal – investigar más")
        interpretation = "marginal"
    else:
        print("   ❌ SNR < 2.0: No aparece – no universal")
        interpretation = "no_signal"
    
    # Crear directorio de resultados
    output_dir = '../results/figures'
    os.makedirs(output_dir, exist_ok=True)
    
    # Visualización
    print("\n📊 Generando visualización...")
    plt.figure(figsize=(10, 4))
    k1_band.plot()
    plt.axhline(std_deviation, color='red', linestyle='--', 
                label=f'1σ = {std_deviation:.2e}', linewidth=2)
    plt.axhline(-std_deviation, color='red', linestyle='--', linewidth=2)
    plt.title(f"KAGRA – Señal filtrada en 141.7 Hz (SNR = {snr_k1:.2f})", 
              fontsize=14, fontweight='bold')
    plt.xlabel('Tiempo (GPS)', fontsize=12)
    plt.ylabel('Amplitud (strain)', fontsize=12)
    plt.legend(fontsize=10)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    
    output_file = f'{output_dir}/kagra_k1_141hz_analysis.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"💾 Visualización guardada en: {output_file}")
    
    # Guardar resultados numéricos
    results_file = f'{output_dir}/kagra_k1_141hz_results.txt'
    with open(results_file, 'w') as f:
        f.write("=" * 60 + "\n")
        f.write("RESULTADOS: Análisis de 141.7 Hz en KAGRA (K1)\n")
        f.write("=" * 60 + "\n\n")
        f.write(f"Detector: K1 (KAGRA)\n")
        f.write(f"GPS Time: {start} - {end}\n")
        f.write(f"Fecha: 2023-06-16\n")
        f.write(f"Duración: {k1.duration.value:.2f} s\n")
        f.write(f"Tasa de muestreo: {k1.sample_rate.value:.0f} Hz\n\n")
        f.write(f"Banda analizada: {target_band[0]} - {target_band[1]} Hz\n")
        f.write(f"Frecuencia objetivo: {target_freq} Hz\n\n")
        f.write(f"SNR calculado: {snr_k1:.2f}\n")
        f.write(f"Amplitud máxima: {max_amplitude:.2e}\n")
        f.write(f"Desviación estándar (1σ): {std_deviation:.2e}\n\n")
        f.write("Interpretación:\n")
        if interpretation == "coherent_signal":
            f.write("  ✅ SNR > 5.0: Posible señal coherente también en KAGRA\n")
        elif interpretation == "marginal":
            f.write("  ⚠️  SNR 2-4.9: Marginal – investigar más\n")
        else:
            f.write("  ❌ SNR < 2.0: No aparece – no universal\n")
    
    print(f"💾 Resultados guardados en: {results_file}")
    
    # Retornar resultados
    results = {
        'detector': 'K1',
        'gps_start': start,
        'gps_end': end,
        'date': '2023-06-16',
        'duration': k1.duration.value,
        'sample_rate': k1.sample_rate.value,
        'target_freq': target_freq,
        'target_band': target_band,
        'snr': snr_k1,
        'max_amplitude': max_amplitude,
        'std_deviation': std_deviation,
        'interpretation': interpretation,
        'output_file': output_file,
        'results_file': results_file
    }
    
    print("\n" + "=" * 60)
    print("✅ ANÁLISIS COMPLETADO")
    print("=" * 60)
    
    return results


def main():
    """Función principal"""
    print("\n🌌 ANÁLISIS KAGRA - Búsqueda de 141.7 Hz en O4 Data")
    print()
    
    try:
        results = analyze_kagra_141hz()
        
        if results is None:
            print("\n❌ Error: No se pudo completar el análisis")
            return 1
        
        print(f"\n📋 RESUMEN:")
        print(f"   Detector: {results['detector']}")
        print(f"   SNR: {results['snr']:.2f}")
        print(f"   Interpretación: {results['interpretation']}")
        
        return 0
        
    except Exception as e:
        print(f"\n❌ Error en el análisis: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
