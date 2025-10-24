#!/usr/bin/env python3
"""
Comparación H1 vs L1 - SNR @ 141.7 Hz
Análisis multi-evento de 11 eventos gravitacionales comparando deteccion SNR entre detectores

Este script analiza 11 eventos del catálogo GWTC para comparar la relación señal-ruido (SNR)
en la frecuencia de 141.7 Hz entre los detectores Hanford (H1) y Livingston (L1).
"""
from gwpy.timeseries import TimeSeries
import matplotlib.pyplot as plt
import numpy as np
import json
import warnings
warnings.filterwarnings('ignore')

events = {
    "GW150914": [1126259462, 1126259494],
    "GW151012": [1128678900, 1128678932],
    "GW151226": [1135136350, 1135136382],
    "GW170104": [1167559936, 1167559968],
    "GW170608": [1180922440, 1180922472],
    "GW170729": [1185389790, 1185389822],
    "GW170809": [1186302506, 1186302538],
    "GW170814": [1186741851, 1186741883],
    "GW170817": [1187008882, 1187008914],
    "GW170818": [1187058312, 1187058344],
    "GW170823": [1187529246, 1187529278]
}

h1_snr = []
l1_snr = []


def estimate_snr(ts):
    """
    Estima la relación señal-ruido (SNR) de una serie temporal.

    Args:
        ts: TimeSeries de GWPy con los datos del detector

    Returns:
        float: SNR estimado como max(abs(señal)) / std(señal)
    """
    return np.max(np.abs(ts.value)) / np.std(ts.value)


def main():
    """
    Ejecuta el análisis de comparación H1 vs L1 para 11 eventos.
    """
    print("=" * 70)
    print("🌌 COMPARACIÓN H1 vs L1 - SNR @ 141.7 Hz")
    print("=" * 70)
    print()
    print(f"Total de eventos a analizar: {len(events)}")
    print()

    for name, (start, end) in events.items():
        print(f"⏳ Analizando {name}...")

        try:
            h1 = TimeSeries.fetch_open_data('H1', start, end, cache=True).bandpass(140.7, 142.7)
            l1 = TimeSeries.fetch_open_data('L1', start, end, cache=True).bandpass(140.7, 142.7)

            h1_snr_val = estimate_snr(h1)
            l1_snr_val = estimate_snr(l1)

            h1_snr.append(h1_snr_val)
            l1_snr.append(l1_snr_val)

            print(f"   ✅ H1 SNR = {h1_snr_val:.2f}, L1 SNR = {l1_snr_val:.2f}")
        except Exception as e:
            print(f"   ⚠️ Error en {name}: {str(e)}")
            h1_snr.append(0)
            l1_snr.append(0)

    # Visualización
    print()
    print("📊 Generando visualización...")
    labels = list(events.keys())
    x = np.arange(len(labels))
    width = 0.35

    fig, ax = plt.subplots(figsize=(14, 6))
    ax.bar(x - width / 2, h1_snr, width, label='H1')
    ax.bar(x + width / 2, l1_snr, width, label='L1')

    ax.set_ylabel('SNR estimado @ 141.7 Hz')
    ax.set_title('Comparación H1 vs L1 – Frecuencia 141.7 Hz')
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45)
    ax.legend()
    plt.tight_layout()

    # Guardar figura en results
    import os
    os.makedirs('results/figures', exist_ok=True)
    output_png = 'results/figures/snr_h1_l1.png'
    plt.savefig(output_png)
    print(f"   ✅ Gráfico guardado en: {output_png}")

    # Mostrar gráfico si es posible
    try:
        plt.show()
    except Exception:
        pass  # En entornos sin display, simplemente guarda el archivo

    # Guardar resultados
    print()
    print("💾 Guardando resultados...")
    results = {
        label: {"H1_SNR": round(h1_snr[i], 2), "L1_SNR": round(l1_snr[i], 2)}
        for i, label in enumerate(labels)
    }

    output_json = 'results/snr_h1_l1_comparison.json'
    with open(output_json, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"   ✅ Resultados guardados en: {output_json}")

    print()
    print("=" * 70)
    print("✅ Comparación H1 vs L1 finalizada.")
    print("=" * 70)

    # Resumen estadístico
    print()
    print("📈 RESUMEN ESTADÍSTICO")
    print("-" * 70)
    h1_array = np.array([snr for snr in h1_snr if snr > 0])
    l1_array = np.array([snr for snr in l1_snr if snr > 0])

    if len(h1_array) > 0:
        print(f"H1 - Media: {np.mean(h1_array):.2f}, Std: {np.std(h1_array):.2f}, Max: {np.max(h1_array):.2f}")
    if len(l1_array) > 0:
        print(f"L1 - Media: {np.mean(l1_array):.2f}, Std: {np.std(l1_array):.2f}, Max: {np.max(l1_array):.2f}")

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
