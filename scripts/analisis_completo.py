#!/usr/bin/env python3
"""
Análisis completo de la componente en 141.7 Hz - Script unificado
"""
import h5py
import numpy as np
import matplotlib.pyplot as plt
from scipy import signal
import os
import json

def cargar_datos_hdf5(archivo_hdf5):
    """Cargar datos desde archivo HDF5 personalizado"""
    with h5py.File(archivo_hdf5, 'r') as hdf:
        strain = hdf['strain']['Strain'][:]
        meta = hdf['meta']
        gps_start = meta['GPSstart'][()]
        sample_rate = meta['SampleRate'][()]
        duration = meta['Duration'][()]
        detector = meta['Detector'][()].decode('utf-8') if isinstance(meta['Detector'][()], bytes) else meta['Detector'][()]
    
    tiempo = np.arange(len(strain)) / sample_rate + gps_start
    return tiempo, strain, sample_rate, detector

def analizar_espectro_completo(strain, sample_rate, frecuencia_objetivo=141.7):
    """Análisis espectral completo con múltiples métricas"""
    # FFT
    freqs = np.fft.rfftfreq(len(strain), 1/sample_rate)
    fft_vals = np.fft.rfft(strain)
    potencia = np.abs(fft_vals)**2
    
    # Buscar pico más cercano
    idx_objetivo = np.argmin(np.abs(freqs - frecuencia_objetivo))
    freq_pico = freqs[idx_objetivo]
    potencia_pico = potencia[idx_objetivo]
    
    # Calcular SNR en banda estrecha
    banda_mask = (freqs >= frecuencia_objetivo-10) & (freqs <= frecuencia_objetivo+10)
    banda_potencia = potencia[banda_mask]
    banda_freqs = freqs[banda_mask]
    
    # Piso de ruido local
    ruido_mask = ((freqs >= frecuencia_objetivo-50) & (freqs <= frecuencia_objetivo-20)) | \
                 ((freqs >= frecuencia_objetivo+20) & (freqs <= frecuencia_objetivo+50))
    piso_ruido = np.median(potencia[ruido_mask]) if np.any(ruido_mask) else np.median(potencia)
    
    snr = potencia_pico / piso_ruido
    
    return {
        'frecuencias': freqs,
        'potencia': potencia,
        'freq_detectada': freq_pico,
        'potencia_pico': potencia_pico,
        'snr': snr,
        'piso_ruido': piso_ruido,
        'banda_freqs': banda_freqs,
        'banda_potencia': banda_potencia
    }

def analizar_ringdown(tiempo, strain, sample_rate, merger_time=1126259462.423):
    """Análisis específico del ringdown"""
    # Encontrar índice del merger
    merger_idx = np.argmin(np.abs(tiempo - merger_time))
    
    # Extraer ringdown (primeros 100 ms post-merger)
    ringdown_samples = int(0.1 * sample_rate)  # 100 ms
    if merger_idx + ringdown_samples < len(strain):
        ringdown = strain[merger_idx:merger_idx + ringdown_samples]
        ringdown_time = tiempo[merger_idx:merger_idx + ringdown_samples]
    else:
        ringdown = strain[merger_idx:]
        ringdown_time = tiempo[merger_idx:]
    
    # Análisis espectral del ringdown
    resultado_ringdown = analizar_espectro_completo(ringdown, sample_rate)
    
    return {
        'merger_idx': merger_idx,
        'ringdown': ringdown,
        'ringdown_time': ringdown_time,
        'duracion_ms': len(ringdown) / sample_rate * 1000,
        'espectro': resultado_ringdown
    }

def crear_graficos_completos(tiempo, strain, analisis_completo, analisis_ringdown, detector, output_dir):
    """Crear gráficos completos del análisis"""
    fig = plt.figure(figsize=(16, 12))
    
    # 1. Serie temporal completa
    ax1 = plt.subplot(3, 2, 1)
    plt.plot(tiempo - tiempo[0], strain * 1e21, 'b-', alpha=0.7, linewidth=0.8)
    merger_time_rel = tiempo[analisis_ringdown['merger_idx']] - tiempo[0]
    plt.axvline(merger_time_rel, color='red', linestyle='--', alpha=0.8, label='Merger')
    plt.xlabel('Tiempo (s)')
    plt.ylabel('Strain (×10⁻²¹)')
    plt.title(f'Serie Temporal Completa - {detector}')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    # 2. Ringdown
    ax2 = plt.subplot(3, 2, 2)
    ringdown_time_ms = (analisis_ringdown['ringdown_time'] - analisis_ringdown['ringdown_time'][0]) * 1000
    plt.plot(ringdown_time_ms, analisis_ringdown['ringdown'] * 1e21, 'g-', linewidth=1.2)
    plt.xlabel('Tiempo post-merger (ms)')
    plt.ylabel('Strain (×10⁻²¹)')
    plt.title(f'Ringdown - Duración: {analisis_ringdown["duracion_ms"]:.1f} ms')
    plt.grid(True, alpha=0.3)
    
    # 3. Espectro completo (log-log)
    ax3 = plt.subplot(3, 2, 3)
    plt.loglog(analisis_completo['frecuencias'][1:], analisis_completo['potencia'][1:], 'b-', alpha=0.8, linewidth=1)
    plt.axvline(141.7, color='red', linestyle='--', linewidth=2, alpha=0.9, label='141.7 Hz objetivo')
    plt.axvline(analisis_completo['freq_detectada'], color='green', linestyle='--', 
                linewidth=1.5, alpha=0.8, label=f'Detectado: {analisis_completo["freq_detectada"]:.1f} Hz')
    plt.xlabel('Frecuencia (Hz)')
    plt.ylabel('Potencia')
    plt.title(f'Espectro Completo - SNR: {analisis_completo["snr"]:.2f}')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.xlim(10, 2000)
    
    # 4. Zoom espectral alrededor de 141.7 Hz
    ax4 = plt.subplot(3, 2, 4)
    mask_zoom = (analisis_completo['frecuencias'] >= 120) & (analisis_completo['frecuencias'] <= 170)
    plt.semilogy(analisis_completo['frecuencias'][mask_zoom], 
                 analisis_completo['potencia'][mask_zoom], 'r-', linewidth=1.5)
    plt.axvline(141.7, color='red', linestyle='--', linewidth=2, alpha=0.9, label='141.7 Hz')
    plt.axvline(analisis_completo['freq_detectada'], color='green', linestyle='--', 
                linewidth=1.5, alpha=0.8, label=f'Pico: {analisis_completo["freq_detectada"]:.2f} Hz')
    plt.axhline(analisis_completo['piso_ruido'], color='orange', linestyle=':', 
                alpha=0.7, label=f'Piso ruido')
    plt.xlabel('Frecuencia (Hz)')
    plt.ylabel('Potencia')
    plt.title('Zoom: Zona de Interés (120-170 Hz)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    # 5. Espectro del ringdown
    ax5 = plt.subplot(3, 2, 5)
    plt.semilogy(analisis_ringdown['espectro']['frecuencias'], 
                 analisis_ringdown['espectro']['potencia'], 'purple', alpha=0.8, linewidth=1.2)
    plt.axvline(141.7, color='red', linestyle='--', linewidth=2, alpha=0.9)
    plt.axvline(analisis_ringdown['espectro']['freq_detectada'], color='green', linestyle='--', 
                linewidth=1.5, alpha=0.8, 
                label=f'Ringdown: {analisis_ringdown["espectro"]["freq_detectada"]:.2f} Hz (SNR: {analisis_ringdown["espectro"]["snr"]:.2f})')
    plt.xlabel('Frecuencia (Hz)')
    plt.ylabel('Potencia')
    plt.title('Espectro del Ringdown')
    plt.xlim(100, 300)
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    # 6. Espectrograma
    ax6 = plt.subplot(3, 2, 6)
    try:
        # Usar solo el ringdown para el espectrograma
        f, t, Sxx = signal.spectrogram(analisis_ringdown['ringdown'], 
                                       fs=sample_rate, nperseg=512, noverlap=400)
        freq_mask = (f >= 100) & (f <= 200)
        im = plt.pcolormesh(t * 1000, f[freq_mask], 10*np.log10(Sxx[freq_mask] + 1e-50), 
                           shading='gouraud', cmap='viridis', alpha=0.9)
        plt.axhline(141.7, color='red', linestyle='--', linewidth=2, alpha=0.9)
        plt.xlabel('Tiempo post-merger (ms)')
        plt.ylabel('Frecuencia (Hz)')
        plt.title('Espectrograma - Ringdown')
        plt.colorbar(im, label='dB')
    except Exception as e:
        plt.text(0.5, 0.5, f'Error en espectrograma:\n{str(e)}', 
                transform=ax6.transAxes, ha='center', va='center')
        plt.title('Espectrograma no disponible')
    
    plt.tight_layout()
    
    # Guardar figura
    filename = f'{output_dir}/analisis_completo_{detector}.png'
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    plt.close()
    
    return filename

def guardar_resultados(resultados, detector, output_dir):
    """Guardar resultados en formato JSON"""
    filename = f'{output_dir}/resultados_{detector}.json'
    
    # Convertir arrays numpy a listas para JSON
    resultados_json = {}
    for key, value in resultados.items():
        if isinstance(value, np.ndarray):
            resultados_json[key] = value.tolist()
        elif isinstance(value, (np.int64, np.int32, np.float64, np.float32)):
            resultados_json[key] = float(value)
        elif isinstance(value, dict):
            resultados_json[key] = {}
            for k2, v2 in value.items():
                if isinstance(v2, np.ndarray):
                    resultados_json[key][k2] = v2.tolist()
                elif isinstance(v2, (np.int64, np.int32, np.float64, np.float32)):
                    resultados_json[key][k2] = float(v2)
                else:
                    resultados_json[key][k2] = v2
        else:
            resultados_json[key] = value
    
    with open(filename, 'w') as f:
        json.dump(resultados_json, f, indent=2)
    
    return filename

def main():
    """Análisis completo"""
    print("🌀 Análisis Completo - Componente 141.7 Hz")
    print("="*50)
    
    # Configuración
    output_dir = '../results/figures'
    data_dir = '../data/processed'
    os.makedirs(output_dir, exist_ok=True)
    os.makedirs(data_dir, exist_ok=True)
    
    # Analizar ambos detectores
    detectores = ['H1', 'L1']
    
    for detector in detectores:
        archivo = f'../data/raw/{detector}-GW150914-32s.hdf5'
        
        if not os.path.exists(archivo):
            print(f"❌ {detector}: Archivo no encontrado - {archivo}")
            continue
            
        print(f"\n🔍 Analizando {detector}...")
        
        try:
            # Cargar datos
            tiempo, strain, sample_rate, det_name = cargar_datos_hdf5(archivo)
            print(f"   ✅ Datos cargados: {len(strain)} muestras a {sample_rate} Hz")
            print(f"   📅 GPS inicio: {tiempo[0]:.1f}, Duración: {len(strain)/sample_rate:.1f}s")
            
            # Análisis espectral completo
            analisis_completo = analizar_espectro_completo(strain, sample_rate)
            
            # Análisis del ringdown
            analisis_ringdown = analizar_ringdown(tiempo, strain, sample_rate)
            
            # Resultados
            print(f"\n📊 Resultados {detector}:")
            print(f"   🎯 Frecuencia objetivo: 141.7 Hz")
            print(f"   📈 Frecuencia detectada (completo): {analisis_completo['freq_detectada']:.3f} Hz")
            print(f"   📈 Frecuencia detectada (ringdown): {analisis_ringdown['espectro']['freq_detectada']:.3f} Hz")
            print(f"   🔊 SNR (completo): {analisis_completo['snr']:.2f}")
            print(f"   🔊 SNR (ringdown): {analisis_ringdown['espectro']['snr']:.2f}")
            print(f"   📏 Diferencia con objetivo: {abs(analisis_completo['freq_detectada'] - 141.7):.3f} Hz")
            print(f"   ⏱️ Duración ringdown: {analisis_ringdown['duracion_ms']:.1f} ms")
            
            # Crear gráficos
            grafico_file = crear_graficos_completos(tiempo, strain, analisis_completo, 
                                                   analisis_ringdown, detector, output_dir)
            print(f"   💾 Gráfico: {grafico_file}")
            
            # Crear resumen simple sin arrays numpy
            resumen = {
                'detector': detector,
                'frecuencia_objetivo': 141.7,
                'freq_detectada_completo': float(analisis_completo['freq_detectada']),
                'freq_detectada_ringdown': float(analisis_ringdown['espectro']['freq_detectada']),
                'snr_completo': float(analisis_completo['snr']),
                'snr_ringdown': float(analisis_ringdown['espectro']['snr']),
                'diferencia_hz': float(abs(analisis_completo['freq_detectada'] - 141.7)),
                'duracion_ringdown_ms': float(analisis_ringdown['duracion_ms']),
                'sample_rate': float(sample_rate),
                'gps_start': float(tiempo[0]),
                'duration_s': float(len(strain) / sample_rate),
                'n_samples': int(len(strain))
            }
            
            # Guardar resumen
            resumen_file = f'{data_dir}/resumen_{detector}.json'
            with open(resumen_file, 'w') as f:
                json.dump(resumen, f, indent=2)
            print(f"   💾 Resumen: {resumen_file}")
            
            # Evaluación
            coincidencia = abs(analisis_completo['freq_detectada'] - 141.7) < 1.0
            print(f"   {'✅' if coincidencia else '⚠️'} Coincidencia con 141.7 Hz: {'SÍ' if coincidencia else 'NO'}")
            
        except Exception as e:
            print(f"   ❌ Error procesando {detector}: {e}")
            import traceback
            traceback.print_exc()
    
    print(f"\n🎉 Análisis completo terminado. Resultados en:")
    print(f"   📁 Gráficos: {output_dir}/")
    print(f"   📁 Datos: {data_dir}/")

if __name__ == "__main__":
    main()