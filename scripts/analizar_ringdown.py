#!/usr/bin/env python3
"""
Análisis de componente en 141.7 Hz en el ringdown - CORREGIDO
"""
import h5py
import numpy as np
import matplotlib.pyplot as plt
from scipy import signal
import os

def cargar_datos_gwosc(archivo_hdf5):
    """Cargar datos desde archivo HDF5 de GWOSC (formato correcto)"""
    with h5py.File(archivo_hdf5, 'r') as hdf:
        # El formato de GWOSC tiene la estructura diferente
        strain = hdf['strain']['Strain'][:]
        meta = hdf['meta']
        gps_start = meta['GPSstart'][()]
        duration = meta['Duration'][()]
        sample_rate = meta['SampleRate'][()]
    
    tiempo = np.arange(len(strain)) / sample_rate + gps_start
    return tiempo, strain, sample_rate

def analizar_espectro(tiempo, datos, sample_rate, frecuencia_objetivo=141.7):
    """Analizar el espectro en busca de la frecuencia objetivo"""
    # Calcular FFT
    n = len(datos)
    freqs = np.fft.rfftfreq(n, d=1/sample_rate)
    fft_vals = np.fft.rfft(datos)
    potencia = np.abs(fft_vals)**2
    
    # Encontrar pico más cercano a la frecuencia objetivo
    idx_objetivo = np.argmin(np.abs(freqs - frecuencia_objetivo))
    freq_pico = freqs[idx_objetivo]
    potencia_pico = potencia[idx_objetivo]
    
    # Calcular significancia (SNR aproximado)
    noise_floor = np.median(potencia)
    snr = potencia_pico / noise_floor
    
    return freqs, potencia, freq_pico, potencia_pico, snr

def crear_graficos(tiempo, datos, freqs, potencia, freq_pico, snr, detector, output_dir):
    """Crear gráficos de diagnóstico"""
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(15, 10))
    
    # Serie temporal (solo mostramos una parte)
    ax1.plot(tiempo[:10000], datos[:10000], 'b-', linewidth=1)
    ax1.set_xlabel('Tiempo (s)')
    ax1.set_ylabel('Strain')
    ax1.set_title(f'Señal Temporal - {detector}')
    ax1.grid(True)
    
    # Espectro de potencia
    ax2.semilogy(freqs, potencia, 'b-', linewidth=1)
    ax2.axvline(141.7, color='r', linestyle='--', alpha=0.7, label='141.7 Hz objetivo')
    ax2.axvline(freq_pico, color='g', linestyle='--', alpha=0.7, label=f'Pico: {freq_pico:.1f} Hz')
    ax2.set_xlabel('Frecuencia (Hz)')
    ax2.set_ylabel('Potencia')
    ax2.set_title(f'Espectro (SNR: {snr:.2f})')
    ax2.legend()
    ax2.grid(True)
    ax2.set_xlim(100, 200)
    
    # Zoom alrededor de 141.7 Hz
    ax3.semilogy(freqs, potencia, 'b-', linewidth=1.5)
    ax3.axvline(141.7, color='r', linestyle='--', alpha=0.7, linewidth=2, label='141.7 Hz')
    ax3.set_xlabel('Frecuencia (Hz)')
    ax3.set_ylabel('Potencia')
    ax3.set_title('Zoom: 130-160 Hz')
    ax3.grid(True)
    ax3.set_xlim(130, 160)
    ax3.legend()
    
    # Histograma para ver distribución de potencia
    ax4.hist(np.log10(potencia + 1e-10), bins=50, alpha=0.7)
    ax4.axvline(np.log10(potencia_pico + 1e-10), color='r', linestyle='--', 
                label=f'Pico: {potencia_pico:.2e}')
    ax4.set_xlabel('log10(Potencia)')
    ax4.set_ylabel('Frecuencia')
    ax4.set_title('Distribución de Potencia (log)')
    ax4.legend()
    ax4.grid(True)
    
    plt.tight_layout()
    plt.savefig(f'{output_dir}/analisis_{detector}.png', dpi=150, bbox_inches='tight')
    plt.close()

def main():
    # Configuración
    output_dir = '../results/figures'
    os.makedirs(output_dir, exist_ok=True)
    
    # Para GW150914 (datos reales de control)
    archivo_h1 = '../data/raw/H1-GW150914-32s.hdf5'
    
    if os.path.exists(archivo_h1):
        print("Analizando datos de GW150914 (control)...")
        
        # Cargar datos con formato correcto
        tiempo, strain, sample_rate = cargar_datos_gwosc(archivo_h1)
        print(f"Sample rate: {sample_rate} Hz")
        print(f"Duración: {len(strain)/sample_rate:.1f} segundos")
        print(f"Tiempo GPS inicio: {tiempo[0]:.1f}")
        
        # Encontrar el tiempo del merger (1126259462.423)
        merger_time = 1126259462.423
        merger_index = np.argmin(np.abs(tiempo - merger_time))
        
        # Analizar espectro completo
        freqs, potencia, freq_pico, potencia_pico, snr = analizar_espectro(
            tiempo, strain, sample_rate
        )
        
        print(f"\nResultados para H1 - GW150914:")
        print(f"  - Frecuencia del pico más cercano: {freq_pico:.2f} Hz")
        print(f"  - SNR aproximado: {snr:.2f}")
        print(f"  - ¿Coincide con 141.7 Hz? {'SÍ' if abs(freq_pico-141.7)<1 else 'NO'}")
        
        # Crear gráficos
        crear_graficos(tiempo, strain, freqs, potencia, freq_pico, snr, 'H1_GW150914', output_dir)
        print(f"Gráficos guardados en {output_dir}/")
    
    else:
        print("¡Los datos de GW150914 no se encontraron!")
        print("Ejecuta primero: python scripts/descargar_datos.py")

if __name__ == "__main__":
    main()
