#!/usr/bin/env python3
"""
Análisis de datos de Livingston (L1) para comparación
"""
from gwpy.timeseries import TimeSeries
import numpy as np
import matplotlib.pyplot as plt
import os

def main():
    output_dir = '../results/figures'
    os.makedirs(output_dir, exist_ok=True)
    
    archivo_l1 = '../data/raw/L1-GW150914-32s.hdf5'
    
    if os.path.exists(archivo_l1):
        print("🔍 Analizando datos de Livingston (L1)...")
        
        try:
            data = TimeSeries.read(archivo_l1)
            spectrum = data.asd(fftlength=4)
            
            target_freq = 141.7
            freq_idx = np.argmin(np.abs(spectrum.frequencies.value - target_freq))
            detected_freq = spectrum.frequencies.value[freq_idx]
            power = spectrum.value[freq_idx]
            
            # SNR
            freq_mask = (spectrum.frequencies.value >= 130) & (spectrum.frequencies.value <= 160)
            noise_floor = np.median(spectrum.value[freq_mask])
            snr = power / noise_floor
            
            print(f"\n📊 Resultados L1 - GW150914:")
            print(f"   Frecuencia detectada: {detected_freq:.2f} Hz")
            print(f"   SNR: {snr:.2f}")
            print(f"   Diferencia con objetivo: {abs(detected_freq - target_freq):.3f} Hz")
            
            # Gráfico comparativo
            plt.figure(figsize=(10, 6))
            plt.semilogy(spectrum.frequencies.value, spectrum.value, 'b-', label='L1', alpha=0.8)
            plt.axvline(target_freq, color='r', linestyle='--', label='141.7 Hz objetivo')
            plt.axvline(detected_freq, color='g', linestyle='--', label=f'L1: {detected_freq:.2f} Hz')
            plt.xlim(130, 160)
            plt.xlabel('Frecuencia (Hz)')
            plt.ylabel('ASD (1/√Hz)')
            plt.title('Comparación L1 - Componente en 141.7 Hz')
            plt.legend()
            plt.grid(True, alpha=0.3)
            plt.savefig(f'{output_dir}/comparacion_L1.png', dpi=150, bbox_inches='tight')
            plt.close()
            
            print(f"💾 Gráfico guardado en {output_dir}/comparacion_L1.png")
            
        except Exception as e:
            print(f"Error: {e}")
    
    else:
        print("Datos L1 no encontrados.")

if __name__ == "__main__":
    main()
