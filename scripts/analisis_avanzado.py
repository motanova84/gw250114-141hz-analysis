#!/usr/bin/env python3
"""
Análisis avanzado de la componente en 141.7 Hz usando GWPy
"""
from gwpy.timeseries import TimeSeries
from gwpy.signal import filter_design
from gwpy.plot import Plot
import numpy as np
import matplotlib.pyplot as plt
import os

def main():
    output_dir = '../results/figures'
    os.makedirs(output_dir, exist_ok=True)
    
    archivo_h1 = '../data/raw/H1-GW150914-32s.hdf5'
    
    if os.path.exists(archivo_h1):
        print("🔍 Análisis avanzado de GW150914...")
        
        try:
            # Cargar datos
            data = TimeSeries.read(archivo_h1)
            print(f"Datos cargados: {len(data)} muestras a {data.sample_rate} Hz")
            
            # Tiempo del merger (1126259462.423 GPS)
            merger_time = 1126259462.423
            merger_index = int((merger_time - data.t0.value) * data.sample_rate.value)
            
            # Aislar el ringdown (primeros 50 ms post-merger)
            ringdown_start = merger_index
            ringdown_end = merger_index + int(0.05 * data.sample_rate.value)
            ringdown = data[ringdown_start:ringdown_end]
            
            print(f"Ringdown: {len(ringdown)} muestras ({len(ringdown)/data.sample_rate.value*1000:.1f} ms)")
            
            # 1. Espectro de potencia del ringdown
            spectrum = ringdown.asd(fftlength=0.01, overlap=0.005)
            
            # 2. Filtrar alrededor de 141.7 Hz para mejor visualización
            bp = filter_design.bandpass(130, 160, data.sample_rate)
            filtered = ringdown.filter(bp, filtfilt=True)
            
            # 3. Q-transform para ver la evolución temporal
            qtransform = ringdown.q_transform(outseg=(0, 0.05), qrange=(4, 64), frange=(130, 160))
            
            # 4. Análisis de la frecuencia específica
            target_freq = 141.7
            freq_idx = np.argmin(np.abs(spectrum.frequencies.value - target_freq))
            detected_freq = spectrum.frequencies.value[freq_idx]
            power_at_target = spectrum.value[freq_idx]
            
            # Calcular SNR en banda estrecha
            freq_mask = (spectrum.frequencies.value >= 130) & (spectrum.frequencies.value <= 160)
            noise_floor = np.median(spectrum.value[freq_mask])
            snr = power_at_target / noise_floor
            
            print(f"\n📊 Resultados avanzados:")
            print(f"   Frecuencia objetivo: {target_freq} Hz")
            print(f"   Frecuencia detectada: {detected_freq:.2f} Hz")
            print(f"   Potencia: {power_at_target:.2e}")
            print(f"   SNR en banda estrecha: {snr:.2f}")
            print(f"   Diferencia: {abs(detected_freq - target_freq):.3f} Hz")
            
            # Crear figura con múltiples subplots
            fig = plt.figure(figsize=(15, 12))
            
            # Subplot 1: Serie temporal del ringdown
            ax1 = fig.add_subplot(3, 1, 1)
            times = ringdown.times.value - ringdown.times.value[0]
            ax1.plot(times * 1000, ringdown.value, 'b-', alpha=0.8)
            ax1.set_xlabel('Tiempo post-merger (ms)')
            ax1.set_ylabel('Strain')
            ax1.set_title('Señal de Ringdown - GW150914 H1')
            ax1.grid(True, alpha=0.3)
            
            # Subplot 2: Espectro de potencia
            ax2 = fig.add_subplot(3, 1, 2)
            ax2.plot(spectrum.frequencies.value, spectrum.value, 'r-', linewidth=1.5)
            ax2.axvline(target_freq, color='green', linestyle='--', linewidth=2, 
                       label=f'141.7 Hz objetivo')
            ax2.axvline(detected_freq, color='magenta', linestyle='--', linewidth=2,
                       label=f'Detectado: {detected_freq:.2f} Hz')
            ax2.set_xlim(130, 160)
            ax2.set_xlabel('Frecuencia (Hz)')
            ax2.set_ylabel('ASD (1/√Hz)')
            ax2.set_title('Espectro de Potencia - Ringdown')
            ax2.legend()
            ax2.grid(True, alpha=0.3)
            
            # Subplot 3: Q-transform
            ax3 = fig.add_subplot(3, 1, 3)
            im = qtransform.plot(ax=ax3)
            ax3.axhline(target_freq, color='green', linestyle='--', linewidth=2)
            ax3.set_ylim(130, 160)
            ax3.set_xlabel('Tiempo post-merger (s)')
            ax3.set_ylabel('Frecuencia (Hz)')
            ax3.set_title('Q-Transform - Evolución Temporal')
            plt.colorbar(im, ax=ax3, label='Energía')
            
            plt.tight_layout()
            plt.savefig(f'{output_dir}/analisis_avanzado_H1.png', dpi=300, bbox_inches='tight')
            plt.close()
            
            print(f"\n💾 Gráficos guardados en {output_dir}/analisis_avanzado_H1.png")
            
            # Análisis de significancia adicional
            print(f"\n🎯 Significancia:")
            print(f"   La componente a {detected_freq:.2f} Hz está a {abs(detected_freq - target_freq):.3f} Hz del objetivo")
            print(f"   SNR de {snr:.2f} sugiere detección significativa")
            
            if abs(detected_freq - target_freq) < 0.1:
                print("   ✅ EXCELENTE COINCIDENCIA con la frecuencia objetivo")
            elif abs(detected_freq - target_freq) < 0.5:
                print("   ✅ Buena coincidencia con la frecuencia objetivo")
            else:
                print("   ⚠️  Coincidencia moderada - investigar más")
                
        except Exception as e:
            print(f"Error: {e}")
            import traceback
            traceback.print_exc()
    
    else:
        print("Archivo no encontrado.")

if __name__ == "__main__":
    main()
