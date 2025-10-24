#!/usr/bin/env python3
"""
============================================================================
DEMOSTRACIÓN: ANÁLISIS MULTI-EVENTO 141.7 Hz
============================================================================

Demostración del análisis multi-evento completo usando datos sintéticos.
No requiere conectividad a GWOSC.

Este script simula:
- Análisis de SNR en banda 141.7 Hz (140.7-142.7 Hz)
- Procesamiento de 11 eventos de GWTC-1
- Detección de señales consistentes en H1 y L1
- Generación de visualizaciones completas
- Interpretación estadística y recomendaciones

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 2025-10-24
"""

import matplotlib.pyplot as plt
import json
import numpy as np
import sys
import os

print("="*70)
print("DEMOSTRACIÓN: ANÁLISIS MULTI-EVENTO 141.7 Hz")
print("="*70)
print()
print("⚠️  NOTA: Esta es una demostración con datos sintéticos")
print("    Para análisis con datos reales de GWOSC, ejecutar:")
print("    python3 scripts/analisis_multi_evento_final.py")
print()

# ============================================================================
# CONFIGURACIÓN
# ============================================================================

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

target_band = [140.7, 142.7]
snr_threshold = 5.0

# Fijar semilla para reproducibilidad
np.random.seed(42)

results = {}
snr_h1_list = []
snr_l1_list = []
labels = []

# ============================================================================
# SIMULAR ANÁLISIS DE CADA EVENTO
# ============================================================================

for i, (name, (start, end)) in enumerate(events.items(), 1):
    print(f"[{i}/11] Simulando {name}...", end=" ")

    # Generar SNR sintéticos con variación realista
    # Algunos eventos tienen señales más fuertes que otros
    base_snr_h1 = 6.0 + (i % 5) * 1.2 + np.random.uniform(-0.8, 0.8)
    base_snr_l1 = 5.5 + (i % 5) * 1.1 + np.random.uniform(-0.7, 0.7)

    # Algunos eventos no tienen datos L1 disponibles (simular)
    l1_available = np.random.random() > 0.2  # 80% tienen L1

    # Guardar
    results[name] = {
        "H1": float(base_snr_h1),
        "L1": float(base_snr_l1) if l1_available else None
    }

    snr_h1_list.append(base_snr_h1)
    if l1_available:
        snr_l1_list.append(base_snr_l1)
    labels.append(name)

    detected = "✅" if base_snr_h1 > snr_threshold else "🔵"
    print(f"{detected} H1={base_snr_h1:.2f}", end="")
    if l1_available:
        print(f", L1={base_snr_l1:.2f}")
    else:
        print(" (L1 N/A)")

# ============================================================================
# RESULTADOS
# ============================================================================

print("\n" + "="*70)
print("RESULTADOS FINALES")
print("="*70)

n_total = len(events)
n_success = len(snr_h1_list)
n_detected = sum(1 for snr in snr_h1_list if snr > snr_threshold)

print("\n📊 Estadísticas H1:")
print(f"  Eventos totales: {n_total}")
print(f"  Análisis exitosos: {n_success}")
print(f"  Detectados (SNR>5): {n_detected}")
print(f"  Tasa de detección: {n_detected/n_success*100:.1f}%")

if n_success > 0:
    print("\n📐 SNR @ 141.7 Hz (H1):")
    print(f"  Media: {np.mean(snr_h1_list):.2f}")
    print(f"  Desv. std: {np.std(snr_h1_list):.2f}")
    print(f"  Mínimo: {np.min(snr_h1_list):.2f}")
    print(f"  Máximo: {np.max(snr_h1_list):.2f}")

print("\n📋 Desglose por evento:")
for name in sorted(results.keys()):
    data = results[name]
    if "error" not in data:
        h1 = data["H1"]
        l1 = data.get("L1")
        marker = "✅" if h1 > snr_threshold else "🔵"
        l1_str = f"{l1:.2f}" if l1 else "N/A"
        print(f"  {marker} {name}: H1={h1:.2f}, L1={l1_str}")
    else:
        print(f"  ❌ {name}: ERROR")

# ============================================================================
# VISUALIZACIÓN
# ============================================================================

print("\n📊 Generando gráficas...")

fig, axes = plt.subplots(2, 1, figsize=(12, 8))

# Panel 1: SNR por evento
ax = axes[0]
x = np.arange(len(labels))
ax.bar(x, snr_h1_list, color=['green' if s > snr_threshold else 'blue' for s in snr_h1_list],
       alpha=0.7, edgecolor='black')
ax.axhline(snr_threshold, color='red', linestyle='--', linewidth=2, label=f'Threshold (SNR={snr_threshold})')
ax.set_xticks(x)
ax.set_xticklabels(labels, rotation=45, ha='right')
ax.set_ylabel('SNR @ 141.7 Hz (H1)')
ax.set_title('SNR en Banda 141.7 Hz para GWTC-1 (Datos Sintéticos - Demo)')
ax.legend()
ax.grid(True, alpha=0.3, axis='y')

# Panel 2: Distribución
ax = axes[1]
ax.hist(snr_h1_list, bins=8, alpha=0.7, edgecolor='black', color='blue')
ax.axvline(snr_threshold, color='red', linestyle='--', linewidth=2, label='Threshold')
ax.axvline(np.mean(snr_h1_list), color='green', linestyle='--', linewidth=2,
           label=f'Media: {np.mean(snr_h1_list):.2f}')
ax.set_xlabel('SNR @ 141.7 Hz')
ax.set_ylabel('Número de Eventos')
ax.set_title('Distribución de SNR (Datos Sintéticos - Demo)')
ax.legend()
ax.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('demo_multi_event_final.png', dpi=150, bbox_inches='tight')
print("✅ demo_multi_event_final.png guardado")

# No mostrar en modo no interactivo
if not os.environ.get('DISPLAY'):
    plt.close()
else:
    plt.show()

# ============================================================================
# GUARDAR JSON
# ============================================================================

summary = {
    "analysis_type": "DEMO - Synthetic Data",
    "analysis_date": "2025-10-24",
    "frequency_target": 141.7,
    "frequency_band": target_band,
    "snr_threshold": snr_threshold,
    "statistics": {
        "n_total": n_total,
        "n_success": n_success,
        "n_detected": n_detected,
        "detection_rate": float(n_detected / n_success) if n_success > 0 else 0,
        "snr_mean": float(np.mean(snr_h1_list)) if n_success > 0 else 0,
        "snr_std": float(np.std(snr_h1_list)) if n_success > 0 else 0,
        "snr_min": float(np.min(snr_h1_list)) if n_success > 0 else 0,
        "snr_max": float(np.max(snr_h1_list)) if n_success > 0 else 0
    },
    "results": results
}

with open('demo_multi_event_final.json', 'w') as f:
    json.dump(summary, f, indent=2)

print("✅ demo_multi_event_final.json guardado")

# ============================================================================
# INTERPRETACIÓN
# ============================================================================

print("\n" + "="*70)
print("INTERPRETACIÓN")
print("="*70)

detection_rate = n_detected / n_success if n_success > 0 else 0

if detection_rate >= 0.90:
    verdict = "✅ CONFIRMACIÓN ABSOLUTA"
    recommendation = "PUBLICAR INMEDIATAMENTE"
elif detection_rate >= 0.70:
    verdict = "✅ EVIDENCIA MUY FUERTE"
    recommendation = "Publicar con análisis adicional de GWTC-2"
elif detection_rate >= 0.50:
    verdict = "⚠️ EVIDENCIA MODERADA"
    recommendation = "Análisis de correlaciones necesario"
else:
    verdict = "❌ EVIDENCIA INSUFICIENTE"
    recommendation = "Revisar metodología"

print(f"\n{verdict}")
print(f"Tasa de detección: {detection_rate*100:.1f}%")
print(f"Eventos detectados: {n_detected}/{n_success}")
print(f"\n📋 Recomendación: {recommendation}")

print("\n" + "="*70)
print("ANÁLISIS COMPLETADO (DEMO)")
print("="*70)
print()
print("💡 Para ejecutar análisis con datos reales de GWOSC:")
print("   python3 scripts/analisis_multi_evento_final.py")
print("="*70)

sys.exit(0)
