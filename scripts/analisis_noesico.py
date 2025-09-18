#!/usr/bin/env python3
"""
ANÁLISIS DE RESONANCIA NOÉSICA - 141.7001 Hz - CORREGIDO
"""
import h5py
import numpy as np
import matplotlib.pyplot as plt
from scipy import signal
import os

class AnalizadorNoesico:
    def __init__(self, frecuencia_objetivo=141.7001):
        self.frecuencia_objetivo = frecuencia_objetivo
        self.frecuencias_armonicas = self.calcular_armonicos()
        
    def calcular_armonicos(self):
        """Calcular armónicos de la frecuencia noésica"""
        return [self.frecuencia_objetivo * n for n in [1, 1.618, 3.1416, 4.669]]
    
    def cargar_datos(self, archivo_hdf5):
        """Cargar datos desde archivo HDF5 de GWOSC"""
        with h5py.File(archivo_hdf5, 'r') as hdf:
            strain = hdf['strain']['Strain'][:]
            meta = hdf['meta']
            sample_rate = meta['SampleRate'][()]
        return strain, sample_rate
    
    def analizar_resonancia(self, data, sample_rate):
        """Análisis completo de resonancia"""
        print(f"🔭 Analizando resonancia en {self.frecuencia_objetivo} Hz...")
        
        # Transformada de Fourier
        freqs = np.fft.rfftfreq(len(data), 1/sample_rate)
        fft_val = np.fft.rfft(data)
        espectro = np.abs(fft_val)**2
        
        # Buscar pico exacto en 141.7001 Hz
        idx_target = np.argmin(np.abs(freqs - self.frecuencia_objetivo))
        potencia_target = espectro[idx_target]
        freq_actual = freqs[idx_target]
        
        # Análisis de armónicos
        resultados_armonicos = {}
        for arm in self.frecuencias_armonicas:
            idx_arm = np.argmin(np.abs(freqs - arm))
            resultados_armonicos[arm] = {
                'potencia': espectro[idx_arm],
                'snr': espectro[idx_arm] / np.median(espectro),
                'frecuencia_detectada': freqs[idx_arm]
            }
        
        return {
            'frecuencia_objetivo': self.frecuencia_objetivo,
            'frecuencia_detectada': freq_actual,
            'potencia': potencia_target,
            'snr': potencia_target / np.median(espectro),
            'armonicos': resultados_armonicos,
            'frecuencias': freqs,
            'espectro': espectro
        }
    
    def visualizar_resonancia(self, data, sample_rate, output_path):
        """Visualización completa de la resonancia"""
        resultados = self.analizar_resonancia(data, sample_rate)
        
        fig, axes = plt.subplots(2, 1, figsize=(12, 10))
        
        # Espectro de potencia
        axes[0].semilogy(resultados['frecuencias'], resultados['espectro'], 'r-', alpha=0.8)
        for arm, datos in resultados['armonicos'].items():
            axes[0].axvline(arm, color='green', linestyle='--', alpha=0.7, 
                          label=f'Armónico {arm:.1f} Hz (SNR: {datos["snr"]:.2f})')
        axes[0].axvline(self.frecuencia_objetivo, color='magenta', linewidth=2, 
                       label=f'Objetivo {self.frecuencia_objetivo} Hz (SNR: {resultados["snr"]:.2f})')
        axes[0].set_xlim(100, 200)
        axes[0].set_xlabel('Frecuencia (Hz)')
        axes[0].set_ylabel('Potencia')
        axes[0].set_title('Espectro de Potencia - Análisis Noésico')
        axes[0].legend()
        axes[0].grid(True, alpha=0.3)
        
        # Espectrograma
        try:
            f, t, Sxx = signal.spectrogram(data, fs=sample_rate, nperseg=1024, noverlap=900)
            freq_mask = (f >= 130) & (f <= 160)
            im = axes[1].pcolormesh(t, f[freq_mask], 10*np.log10(Sxx[freq_mask] + 1e-10), 
                                  shading='gouraud', cmap='viridis', alpha=0.9)
            axes[1].axhline(self.frecuencia_objetivo, color='magenta', linewidth=2)
            for arm in self.frecuencias_armonicas:
                axes[1].axhline(arm, color='green', linestyle='--', alpha=0.7)
            axes[1].set_ylim(130, 160)
            axes[1].set_xlabel('Tiempo (s)')
            axes[1].set_ylabel('Frecuencia (Hz)')
            axes[1].set_title('Espectrograma - Zona de Resonancia Noésica')
            plt.colorbar(im, ax=axes[1], label='dB')
        except Exception as e:
            axes[1].text(0.5, 0.5, f'Error en espectrograma:\n{str(e)}', 
                        transform=axes[1].transAxes, ha='center', va='center')
            axes[1].set_title('Espectrograma no disponible')
        
        plt.tight_layout()
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        return resultados

def main():
    analizador = AnalizadorNoesico()
    print("🌀 Analizador Noésico inicializado")
    print(f"🎯 Frecuencia objetivo: {analizador.frecuencia_objetivo} Hz")
    print(f"📊 Armónicos: {[f'{f:.1f}' for f in analizador.frecuencias_armonicas]} Hz")
    
    # Analizar datos de H1
    archivo_h1 = '../data/raw/H1-GW150914-32s.hdf5'
    if os.path.exists(archivo_h1):
        print("\n📡 Analizando datos de Hanford (H1)...")
        data, sample_rate = analizador.cargar_datos(archivo_h1)
        print(f"   Muestras: {len(data)}, Sample rate: {sample_rate} Hz")
        
        # Ejecutar análisis
        output_path = '../results/figures/resonancia_noesica_H1.png'
        resultados = analizador.visualizar_resonancia(data, sample_rate, output_path)
        
        print(f"\n📊 Resultados del análisis noésico:")
        print(f"   Frecuencia detectada: {resultados['frecuencia_detectada']:.4f} Hz")
        print(f"   SNR: {resultados['snr']:.2f}")
        print(f"   Potencia: {resultados['potencia']:.2e}")
        
        print("\n🎵 Armónicos detectados:")
        for freq, datos in resultados['armonicos'].items():
            print(f"   {freq:.1f} Hz: SNR = {datos['snr']:.2f} (detectado: {datos['frecuencia_detectada']:.1f} Hz)")
            
        print(f"\n💾 Gráfico guardado en: {output_path}")
    else:
        print("¡Datos no encontrados! Ejecuta primero: python scripts/descargar_datos.py")

if __name__ == "__main__":
    main()
