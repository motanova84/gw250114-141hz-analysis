#!/usr/bin/env python3
"""
Demo del análisis GW250114 usando datos de GW150914
Muestra cómo funcionará el análisis cuando GW250114 esté disponible
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy import signal
import os
import sys
import json

# Importar nuestro analizador principal
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from analizar_gw250114 import GW250114Analyzer


class GW150914Demo(GW250114Analyzer):
    """Demo usando datos sintéticos basados en GW150914"""
    
    def __init__(self, target_frequency: float = 141.7001):
        super().__init__(target_frequency)
        print("🔬 Modo DEMO - Simulación con datos sintéticos")
        
    def generate_synthetic_data(self) -> tuple:
        """Generar datos sintéticos que incluyen la señal de 141.7 Hz"""
        print("🧪 Generando datos sintéticos...")
        
        # Parámetros temporales
        sample_rate = 4096
        duration = 32  # segundos
        t = np.arange(0, duration, 1/sample_rate)
        
        # Tiempo GPS simulado
        gps_sim = 1126259462.423  # Tiempo de GW150914
        
        # 1. Ruido gaussiano blanco
        np.random.seed(42)  # Para reproducibilidad
        noise_h1 = np.random.normal(0, 1e-21, len(t))
        noise_l1 = np.random.normal(0, 1e-21, len(t))
        
        # 2. Añadir picos espectrales típicos de LIGO
        # Líneas de calibración
        calib_freqs = [35.9, 36.7, 37.3, 331.3, 1144.3]
        for freq in calib_freqs:
            phase_h1 = np.random.uniform(0, 2*np.pi)
            phase_l1 = np.random.uniform(0, 2*np.pi)
            amp = 5e-22
            noise_h1 += amp * np.sin(2*np.pi*freq*t + phase_h1)
            noise_l1 += amp * np.sin(2*np.pi*freq*t + phase_l1)
            
        # 3. Añadir líneas de red eléctrica (60 Hz y armónicos)
        for n in range(1, 4):
            freq = 60 * n
            amp = 3e-22 / n
            noise_h1 += amp * np.sin(2*np.pi*freq*t)
            noise_l1 += amp * np.sin(2*np.pi*freq*t)
        
        # 4. ¡AÑADIR LA SEÑAL DE 141.7 Hz EN EL RINGDOWN!
        merger_idx = len(t) // 2  # Centro temporal
        ringdown_start = merger_idx + int(0.01 * sample_rate)  # 10 ms después
        ringdown_duration = int(0.05 * sample_rate)  # 50 ms de duración
        
        if ringdown_start + ringdown_duration < len(t):
            # Crear ventana de ringdown
            ringdown_indices = slice(ringdown_start, ringdown_start + ringdown_duration)
            ringdown_t = t[ringdown_indices] - t[ringdown_start]
            
            # Señal senoidal amortiguada en 141.7001 Hz (frecuencia noésica)
            freq_target = self.target_frequency
            amplitude = 2e-21  # Amplitud más fuerte para mejor detección
            decay_time = 0.025  # 25 ms de tiempo de decaimiento (Q~200)
            phase_h1 = 0.5  # Fase ligeramente diferente entre detectores
            phase_l1 = 0.8
            
            # Crear señal más coherente
            signal_h1 = amplitude * np.exp(-ringdown_t/decay_time) * \
                       np.sin(2*np.pi*freq_target*ringdown_t + phase_h1)
            signal_l1 = amplitude * 0.9 * np.exp(-ringdown_t/decay_time) * \
                       np.sin(2*np.pi*freq_target*ringdown_t + phase_l1)
            
            # Añadir al ruido en toda la región del ringdown para mejor coherencia
            noise_h1[ringdown_indices] += signal_h1
            noise_l1[ringdown_indices] += signal_l1
            
            # También añadir algo de señal antes del ringdown (débil)
            pre_merger = slice(merger_idx - int(0.01 * sample_rate), merger_idx)
            pre_t = t[pre_merger] - t[merger_idx - int(0.01 * sample_rate)]
            weak_signal_h1 = amplitude * 0.3 * np.sin(2*np.pi*freq_target*pre_t + phase_h1)
            weak_signal_l1 = amplitude * 0.3 * np.sin(2*np.pi*freq_target*pre_t + phase_l1)
            noise_h1[pre_merger] += weak_signal_h1
            noise_l1[pre_merger] += weak_signal_l1
            
            print(f"   ✅ Señal inyectada en {freq_target} Hz")
            print(f"   📍 Ringdown: {ringdown_start/sample_rate:.3f} - {(ringdown_start+ringdown_duration)/sample_rate:.3f} s")
            print(f"   💪 Amplitud: {amplitude:.2e}, Q ≈ {freq_target*decay_time:.0f}")
        
        # Crear objetos TimeSeries simulados
        from gwpy.timeseries import TimeSeries
        from astropy import units as u
        
        h1_ts = TimeSeries(noise_h1, sample_rate=sample_rate*u.Hz, 
                          t0=gps_sim*u.s, name='H1:GWOSC-16KHZ_R1_STRAIN')
        l1_ts = TimeSeries(noise_l1, sample_rate=sample_rate*u.Hz,
                          t0=gps_sim*u.s, name='L1:GWOSC-16KHZ_R1_STRAIN')
        
        return h1_ts, l1_ts, gps_sim
    
    def download_official_data(self, event_name: str = 'GW150914-DEMO') -> tuple:
        """Override para usar datos sintéticos"""
        print(f"🌐 Generando datos demo para {event_name}...")
        return self.generate_synthetic_data()
    
    def run_demo(self):
        """Ejecutar demostración completa"""
        print("\n" + "="*70)
        print("🔬 DEMO: Análisis GW250114 con datos sintéticos")
        print("   (Simulación de cómo funcionará con datos reales)")
        print("="*70)
        
        # Ejecutar análisis completo
        results = self.analyze_complete('GW150914-DEMO')
        
        # Análisis de resultados
        print("\n" + "="*50)
        print("📊 INTERPRETACIÓN DE RESULTADOS")
        print("="*50)
        
        if 'error' not in results:
            h1_freq = results['h1_frequency']
            l1_freq = results['l1_frequency']
            freq_diff = abs(h1_freq - l1_freq)
            
            print(f"Frecuencia objetivo: {self.target_frequency} Hz")
            print(f"Detectada en H1: {h1_freq:.4f} Hz")
            print(f"Detectada en L1: {l1_freq:.4f} Hz")
            print(f"Diferencia H1-L1: {freq_diff:.4f} Hz")
            print(f"SNR H1: {results['h1_snr']:.2f}")
            print(f"SNR L1: {results['l1_snr']:.2f}")
            print(f"p-value: {results['p_value']:.4f}")
            print(f"Bayes Factor: {results['bayes_factor_combined']:.2f}")
            print(f"Validación cruzada: {'✅ PASÓ' if results['validation_passed'] else '❌ FALLÓ'}")
            
            # Verificar criterios de detección
            criteria = {
                'Frecuencia precisa (±0.01 Hz)': abs(h1_freq - self.target_frequency) < 0.01,
                'Consistencia H1-L1 (±0.1 Hz)': freq_diff < 0.1,
                'Significancia estadística (p<0.01)': results['p_value'] < 0.01,
                'Evidencia bayesiana fuerte (BF>10)': results['bayes_factor_combined'] > 10,
                'SNR suficiente (>3 en ambos)': results['h1_snr'] > 3 and results['l1_snr'] > 3
            }
            
            print("\n🎯 CRITERIOS DE DETECCIÓN:")
            all_passed = True
            for criterion, passed in criteria.items():
                status = "✅" if passed else "❌"
                print(f"   {status} {criterion}")
                if not passed:
                    all_passed = False
            
            print(f"\n{'🎉 DETECCIÓN CONFIRMADA' if all_passed else '⚠️  DETECCIÓN PARCIAL'}")
            
            if all_passed:
                print("\n📝 RESULTADO CIENTÍFICO:")
                print(f"\"Detectamos una componente espectral en {self.target_frequency:.4f} Hz")
                print(f" en el ringdown del evento simulado, con Bayes Factor BF = {results['bayes_factor_combined']:.1f}")
                print(f" (>10), significancia p = {results['p_value']:.4f} (<0.01),")
                print(f" consistente entre los detectores H1 y L1.\"")
        
        return results


def main():
    """Función principal del demo"""
    # Crear y ejecutar demo
    demo = GW150914Demo(target_frequency=141.7001)
    results = demo.run_demo()
    
    # Guardar resultados del demo
    output_dir = '../results'
    os.makedirs(output_dir, exist_ok=True)
    
    demo_file = f'{output_dir}/demo_results.json'
    with open(demo_file, 'w') as f:
        # Preparar datos para JSON
        json_results = {}
        for key, value in results.items():
            if isinstance(value, (np.integer, np.floating)):
                json_results[key] = float(value)
            elif isinstance(value, np.ndarray):
                json_results[key] = value.tolist()
            else:
                json_results[key] = value
        json.dump(json_results, f, indent=2)
    
    print(f"\n💾 Resultados del demo guardados en: {demo_file}")
    print("\n" + "="*70)
    print("ℹ️  Este demo muestra cómo funcionará el análisis cuando")
    print("   GWOSC libere los datos oficiales de GW250114.")
    print("   La señal de 141.7001 Hz fue inyectada sintéticamente.")
    print("="*70)


if __name__ == "__main__":
    main()