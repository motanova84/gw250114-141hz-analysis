#!/usr/bin/env python3
"""
ASD Noise Analysis at 141.7 Hz
Análisis de densidad espectral de amplitud (ASD) para comparar ruido H1/L1

Este script calcula la densidad espectral de amplitud (ASD) en la banda
140-143 Hz para los detectores H1 y L1, y compara el nivel de ruido en
la frecuencia objetivo de 141.7 Hz.

Genera:
  - asd_noise_results.png: Visualización del ASD con la marca en 141.7 Hz

Por defecto analiza el evento GW150914, pero se puede configurar para otros eventos.
"""

import numpy as np
import matplotlib.pyplot as plt
from gwpy.timeseries import TimeSeries
import argparse


def analyze_asd_noise(event_name="GW150914", start=1126259462, end=1126259494):
    """
    Analiza el ruido ASD en 141.7 Hz para un evento específico.

    Args:
        event_name (str): Nombre del evento
        start (int): Tiempo GPS de inicio
        end (int): Tiempo GPS de fin
    """
    print(f"📡 Analizando evento: {event_name}")
    print(f"   Ventana GPS: {start} - {end}")
    print()

    # Descargar datos
    print("⏳ Descargando datos de H1 y L1...")
    h1 = TimeSeries.fetch_open_data('H1', start, end, cache=True)
    l1 = TimeSeries.fetch_open_data('L1', start, end, cache=True)
    print("✅ Datos descargados")
    print()

    # Calcular ASD en banda 140–143 Hz
    print("🔬 Calculando ASD (fftlength=4s, overlap=2s)...")
    h1_asd = h1.asd(fftlength=4, overlap=2).crop(140, 143)
    l1_asd = l1.asd(fftlength=4, overlap=2).crop(140, 143)
    print("✅ ASD calculado")
    print()

    # Extraer ruido en 141.7 Hz
    f_target = 141.7
    idx_h1 = np.argmin(abs(h1_asd.frequencies.value - f_target))
    idx_l1 = np.argmin(abs(l1_asd.frequencies.value - f_target))

    noise_h1 = h1_asd.value[idx_h1]
    noise_l1 = l1_asd.value[idx_l1]
    noise_ratio = noise_l1 / noise_h1

    print("📊 RESULTADOS:")
    print(f"⚙️ Ruido H1 @141.7 Hz = {noise_h1:.4e} 1/√Hz")
    print(f"⚙️ Ruido L1 @141.7 Hz = {noise_l1:.4e} 1/√Hz")
    print(f"📊 Ratio L1 / H1 = {noise_ratio:.2f}×")
    print()

    # Visualización
    print("📈 Generando visualización...")
    plt.figure(figsize=(10, 5))
    plt.semilogy(h1_asd.frequencies, h1_asd.value, label='H1')
    plt.semilogy(l1_asd.frequencies, l1_asd.value, label='L1')
    plt.axvline(f_target, color='red', linestyle='--', label='141.7 Hz')
    plt.title(f"Amplitud espectral (ASD) en banda 140–143 Hz - {event_name}")
    plt.xlabel("Frecuencia [Hz]")
    plt.ylabel("ASD [1/√Hz]")
    plt.grid(True)
    plt.legend()
    plt.tight_layout()
    plt.savefig("asd_noise_results.png", dpi=150)
    plt.show()
    print("✅ Gráfica guardada: asd_noise_results.png")
    print()

    return {
        'event': event_name,
        'noise_h1': float(noise_h1),
        'noise_l1': float(noise_l1),
        'ratio': float(noise_ratio)
    }


def main():
    """Función principal con soporte para argumentos de línea de comandos."""
    parser = argparse.ArgumentParser(
        description='Análisis de ASD en 141.7 Hz para eventos gravitacionales'
    )
    parser.add_argument(
        '--event',
        type=str,
        default='GW150914',
        help='Nombre del evento (default: GW150914)'
    )
    parser.add_argument(
        '--start',
        type=int,
        default=1126259462,
        help='Tiempo GPS de inicio (default: 1126259462 para GW150914)'
    )
    parser.add_argument(
        '--end',
        type=int,
        default=1126259494,
        help='Tiempo GPS de fin (default: 1126259494 para GW150914)'
    )

    args = parser.parse_args()

    print("=" * 70)
    print("🔬 ANÁLISIS DE RUIDO ASD @ 141.7 Hz")
    print("=" * 70)
    print()

    analyze_asd_noise(args.event, args.start, args.end)

    print("=" * 70)
    print("✅ ANÁLISIS COMPLETADO")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
