#!/usr/bin/env python3
"""
Multi-Event SNR Analysis (H1 vs L1)
Análisis de SNR en banda 141.7 Hz para múltiples eventos gravitacionales

Este script analiza 11 eventos del catálogo GWTC para detectar señales
en la banda de frecuencia de 141.7 Hz, comparando los detectores H1 (Hanford)
y L1 (Livingston).

Genera:
  - multi_event_results.json: Resultados de SNR por evento
  - multi_event_analysis.png: Visualización comparativa H1 vs L1
"""

from gwpy.timeseries import TimeSeries
import matplotlib.pyplot as plt
import json
import numpy as np

# ===============================
# CONFIGURACIÓN GENERAL
# ===============================
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
snr_h1 = []
snr_l1 = []
labels = []

# ===============================
# BUCLE DE ANÁLISIS
# ===============================
for name, (start, end) in events.items():
    print(f"⏳ Analizando {name}...")
    try:
        h1 = TimeSeries.fetch_open_data('H1', start, end, cache=True)
        l1 = TimeSeries.fetch_open_data('L1', start, end, cache=True)

        h1_band = h1.bandpass(*target_band)
        l1_band = l1.bandpass(*target_band)

        snr1 = np.max(np.abs(h1_band.value)) / np.std(h1_band.value)
        snr2 = np.max(np.abs(l1_band.value)) / np.std(l1_band.value)

        results[name] = {"H1": snr1, "L1": snr2}
        snr_h1.append(snr1)
        snr_l1.append(snr2)
        labels.append(name)
        print(f"   ✅ H1 SNR = {snr1:.2f}, L1 SNR = {snr2:.2f}")
    except Exception as e:
        print(f"   ⚠️ Error en {name}: {e}")
        results[name] = {"error": str(e)}

# ===============================
# GUARDAR RESULTADOS
# ===============================
with open("multi_event_results.json", "w") as f:
    json.dump(results, f, indent=2)

# ===============================
# VISUALIZAR RESULTADOS
# ===============================
x = np.arange(len(labels))
plt.figure(figsize=(12, 6))
plt.bar(x - 0.15, snr_h1, width=0.3, label="H1")
plt.bar(x + 0.15, snr_l1, width=0.3, label="L1")
plt.axhline(snr_threshold, color='r', linestyle='--', label='SNR=5')
plt.xticks(x, labels, rotation=45)
plt.ylabel("SNR @ 141.7 Hz")
plt.title("SNR por Evento (H1 vs L1) — Banda 141.7 Hz")
plt.legend()
plt.tight_layout()
plt.savefig("multi_event_analysis.png")
plt.show()

print("\n✅ Análisis completado. Archivos generados:")
print("  - multi_event_results.json")
print("  - multi_event_analysis.png")
