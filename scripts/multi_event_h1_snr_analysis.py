#!/usr/bin/env python3
"""
Multi-Event H1 SNR Analysis
Análisis simplificado de SNR en banda 141.7 Hz para detector H1

Este script analiza 11 eventos del catálogo GWTC para detectar señales
en la banda de frecuencia de 141.7 Hz usando únicamente el detector H1 (Hanford).

Genera:
  - multi_event_h1_results.json: Resultados de SNR por evento
  - multi_event_h1_analysis.png: Visualización de SNR por evento
"""

from gwpy.timeseries import TimeSeries
import matplotlib.pyplot as plt
import json
import numpy as np

events = {
    "GW150914": [1126259462, 1126259494],
    "GW151012": [1128678900, 1128678932],
    "GW151226": [1135136350, 1135136382],
    "GW170104": [1167559936, 1167559968],
    "GW170608": [1180922440, 1180922472],
    "GW170729": [1185389806, 1185389838],
    "GW170809": [1186302508, 1186302540],
    "GW170814": [1186741850, 1186741882],
    "GW170817": [1187008882, 1187008914],
    "GW170818": [1187058327, 1187058359],
    "GW170823": [1187529256, 1187529288],
}

snr_threshold = 5.0
target_band = [140.7, 142.7]
target_freq = 141.7

results = {}
snrs = []
labels = []

for name, (start, end) in events.items():
    print(f"⏳ Procesando {name}:")
    try:
        h1 = TimeSeries.fetch_open_data('H1', start, end, cache=True)
        h1_band = h1.bandpass(target_band[0], target_band[1])
        snr = np.max(np.abs(h1_band.value)) / np.std(h1_band.value)
        results[name] = {"snr": snr}
        snrs.append(snr)
        labels.append(name)
        print(f"   ✅ SNR = {snr:.2f}")
    except Exception as e:
        print(f"   ❌ Error: {e}")
        results[name] = {"snr": None, "error": str(e)}

# Guardar resultados
with open("multi_event_h1_results.json", "w") as f:
    json.dump(results, f, indent=2)

# Plot
plt.figure(figsize=(12, 5))
plt.bar(labels, snrs)
plt.axhline(snr_threshold, color='red', linestyle='--', label=f'SNR > {snr_threshold}')
plt.xticks(rotation=45)
plt.ylabel("SNR @ 141.7 Hz")
plt.title("SNR en Banda de 141.7 Hz para Eventos GWTC-1")
plt.legend()
plt.tight_layout()
plt.savefig("multi_event_h1_analysis.png")
plt.show()

print("\n✅ Análisis completado. Archivos generados:")
print("  - multi_event_h1_results.json")
print("  - multi_event_h1_analysis.png")
