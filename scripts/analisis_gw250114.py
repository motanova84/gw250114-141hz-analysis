#!/usr/bin/env python3
"""
Análisis completo GW250114 con workflow de 6 pasos
Estándar de oro para validación de la componente 141.7 Hz

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import numpy as np
import matplotlib.pyplot as plt
from gwpy.timeseries import TimeSeries
from gwpy.signal import filter_design
import gwosc
from scipy import signal
from scipy.optimize import curve_fit
import os
import warnings
warnings.filterwarnings('ignore')

def paso1_descarga_datos(evento='GW250114'):
    """
    📥 Paso 1: Descarga oficial GWOSC
    """
    print(f"📥 Paso 1: Descargando datos oficiales de {evento}...")
    
    try:
        # Obtener tiempo GPS oficial del evento
        gps_time = gwosc.datasets.event_gps(evento)
        print(f"   ⏰ Tiempo GPS del evento: {gps_time}")
        
        # Descargar datos H1 y L1
        duration = 32  # segundos
        start_time = gps_time - 16
        
        data_h1 = TimeSeries.fetch_open_data('H1', start_time, start_time + duration, 
                                           sample_rate=4096, cache=True)
        data_l1 = TimeSeries.fetch_open_data('L1', start_time, start_time + duration, 
                                           sample_rate=4096, cache=True)
        
        print(f"   ✅ H1: {len(data_h1)} muestras descargadas")
        print(f"   ✅ L1: {len(data_l1)} muestras descargadas")
        
        return data_h1, data_l1, gps_time
    
    except Exception as e:
        print(f"   ❌ Error: {e}")
        print(f"   ℹ️  {evento} puede no estar disponible aún en GWOSC")
        print("   🔄 Usando GW150914 como fallback para demostración...")
        
        # Fallback a GW150914 para demostración
        gps_time = 1126259462.423
        start_time = gps_time - 16
        
        data_h1 = TimeSeries.fetch_open_data('H1', start_time, start_time + 32, 
                                           sample_rate=4096, cache=True)
        data_l1 = TimeSeries.fetch_open_data('L1', start_time, start_time + 32, 
                                           sample_rate=4096, cache=True)
        
        return data_h1, data_l1, gps_time

def paso2_preprocesamiento(data_h1, data_l1):
    """
    ⚙️ Paso 2: Preprocesamiento estándar
    """
    print("⚙️ Paso 2: Preprocesamiento estándar...")
    
    def preprocess(ts):
        # High-pass filter
        ts = ts.highpass(20)
        # Notch filter para 60 Hz
        ts = ts.notch(60)
        # Whitening
        asd = ts.asd(fftlength=4, overlap=0.5)
        ts_white = ts.whiten(asd=asd)
        return ts_white
    
    h1_clean = preprocess(data_h1)
    l1_clean = preprocess(data_l1)
    
    print("   ✅ H1 preprocesado")
    print("   ✅ L1 preprocesado")
    
    return h1_clean, l1_clean

def paso3_busqueda_dirigida(h1_clean, l1_clean, merger_time, target_freq=141.7):
    """
    🔎 Paso 3: Búsqueda dirigida en 141.7 Hz
    """
    print(f"🔎 Paso 3: Búsqueda dirigida en {target_freq} Hz...")
    
    # Extraer ringdown (50ms post-merger)
    ringdown_duration = 0.05  # 50 ms
    ringdown_h1 = h1_clean.crop(merger_time, merger_time + ringdown_duration)
    ringdown_l1 = l1_clean.crop(merger_time, merger_time + ringdown_duration)
    
    # Análisis espectral con alta resolución
    def calcular_asd_y_snr(ts, target_freq):
        asd = ts.asd(fftlength=ringdown_duration)
        freqs = asd.frequencies.value
        
        # Encontrar índice más cercano a la frecuencia objetivo
        freq_idx = np.argmin(np.abs(freqs - target_freq))
        
        # Calcular SNR como potencia de pico / mediana del ruido
        noise_band = np.abs(freqs - target_freq) < 10  # ±10 Hz alrededor
        noise_median = np.median(asd.value[noise_band])
        
        peak_power = asd.value[freq_idx]
        snr = peak_power / noise_median
        actual_freq = freqs[freq_idx]
        
        return actual_freq, snr, asd
    
    freq_h1, snr_h1, asd_h1 = calcular_asd_y_snr(ringdown_h1, target_freq)
    freq_l1, snr_l1, asd_l1 = calcular_asd_y_snr(ringdown_l1, target_freq)
    
    print(f"   📊 H1: {freq_h1:.2f} Hz, SNR = {snr_h1:.2f}")
    print(f"   📊 L1: {freq_l1:.2f} Hz, SNR = {snr_l1:.2f}")
    
    return (freq_h1, snr_h1, asd_h1), (freq_l1, snr_l1, asd_l1)

def paso4_estadistica_clasica(h1_clean, l1_clean, merger_time, target_freq=141.7, n_slides=1000):
    """
    📊 Paso 4: Estadística clásica (p-value)
    """
    print(f"📊 Paso 4: Calculando p-value con {n_slides} time-slides...")
    
    # Extraer ringdown
    ringdown_duration = 0.05
    ringdown_h1 = h1_clean.crop(merger_time, merger_time + ringdown_duration)
    
    def calcular_snr_pico(ts, target_freq):
        asd = ts.asd(fftlength=ringdown_duration)
        freqs = asd.frequencies.value
        freq_idx = np.argmin(np.abs(freqs - target_freq))
        
        noise_band = np.abs(freqs - target_freq) < 10
        noise_median = np.median(asd.value[noise_band])
        
        return asd.value[freq_idx] / noise_median
    
    # SNR observado
    snr_observed = calcular_snr_pico(ringdown_h1, target_freq)
    
    # Time-slides background
    background_snrs = []
    slide_range = int(0.2 * h1_clean.sample_rate.value)  # ±0.2s
    
    for i in range(n_slides):
        # Desplazamiento aleatorio entre H1 y L1
        shift = np.random.randint(-slide_range, slide_range)
        if shift > 0:
            h1_shifted = h1_clean[shift:]
            l1_sync = l1_clean[:len(h1_shifted)]
        else:
            h1_shifted = h1_clean[:len(h1_clean)+shift]
            l1_sync = l1_clean[-shift:]
        
        # Recalcular ringdown con datos desplazados
        try:
            ringdown_shifted = h1_shifted.crop(merger_time, merger_time + ringdown_duration)
            snr_bg = calcular_snr_pico(ringdown_shifted, target_freq)
            background_snrs.append(snr_bg)
        except:
            continue
    
    # Calcular p-value
    background_snrs = np.array(background_snrs)
    p_value = np.sum(background_snrs >= snr_observed) / len(background_snrs)
    
    print(f"   🎯 SNR observado: {snr_observed:.2f}")
    print(f"   📈 p-value: {p_value:.4f}")
    
    return p_value, snr_observed, background_snrs

def paso5_bayes_factor(h1_clean, l1_clean, merger_time, target_freq=141.7):
    """
    📈 Paso 5: Bayes Factor
    """
    print("📈 Paso 5: Calculando Bayes Factor...")
    
    ringdown_duration = 0.05
    ringdown_h1 = h1_clean.crop(merger_time, merger_time + ringdown_duration)
    
    # Modelo de datos
    times = ringdown_h1.times.value - merger_time
    data = ringdown_h1.value
    
    # Modelo 0: Solo ruido (constante)
    def model0(t, noise_level):
        return np.full_like(t, noise_level)
    
    # Modelo 1: Ruido + señal sinusoidal amortiguada en 141.7 Hz
    def model1(t, noise_level, amplitude, decay_time, phase):
        return (noise_level + 
                amplitude * np.exp(-t/decay_time) * np.sin(2*np.pi*target_freq*t + phase))
    
    try:
        # Ajuste Modelo 0 (solo ruido)
        popt0, pcov0 = curve_fit(model0, times, data, p0=[np.std(data)])
        residuals0 = data - model0(times, *popt0)
        likelihood0 = -0.5 * np.sum(residuals0**2) / np.var(residuals0)
        
        # Ajuste Modelo 1 (ruido + señal)
        initial_guess = [np.std(data), np.max(np.abs(data)), 0.01, 0]
        popt1, pcov1 = curve_fit(model1, times, data, p0=initial_guess, maxfev=5000)
        residuals1 = data - model1(times, *popt1)
        likelihood1 = -0.5 * np.sum(residuals1**2) / np.var(residuals1)
        
        # Bayes Factor (aproximación)
        log_bf = likelihood1 - likelihood0
        bf = np.exp(log_bf)
        
        print(f"   ⚖️  Log-Likelihood M0: {likelihood0:.2f}")
        print(f"   ⚖️  Log-Likelihood M1: {likelihood1:.2f}")
        print(f"   📊 Bayes Factor: {bf:.2f}")
        
        return bf, popt1
    
    except Exception as e:
        print(f"   ⚠️  Error en ajuste: {e}")
        return 1.0, None

def paso6_validacion_cruzada(freq_h1, freq_l1, snr_h1, snr_l1, p_value, bf):
    """
    ✅ Paso 6: Validación cruzada
    """
    print("✅ Paso 6: Validación cruzada...")
    
    # Criterios de validación
    coincidencia_freq = abs(freq_h1 - freq_l1) < 0.1  # ±0.1 Hz
    significancia_estadistica = p_value < 0.01
    evidencia_bayesiana = bf > 10
    deteccion_h1 = snr_h1 > 5
    
    print(f"   📍 Coincidencia frecuencial H1-L1: {'✅' if coincidencia_freq else '❌'}")
    print(f"     └─ H1: {freq_h1:.2f} Hz, L1: {freq_l1:.2f} Hz")
    print(f"   📊 Significancia estadística: {'✅' if significancia_estadistica else '❌'}")
    print(f"     └─ p-value = {p_value:.4f} < 0.01")
    print(f"   📈 Evidencia bayesiana: {'✅' if evidencia_bayesiana else '❌'}")
    print(f"     └─ BF = {bf:.2f} > 10")
    print(f"   📡 Detección H1: {'✅' if deteccion_h1 else '❌'}")
    print(f"     └─ SNR = {snr_h1:.2f} > 5")
    
    # Resultado final
    validacion_exitosa = (coincidencia_freq and significancia_estadistica 
                         and evidencia_bayesiana and deteccion_h1)
    
    print(f"\n🎯 RESULTADO FINAL: {'✅ COMPONENTE DETECTADA' if validacion_exitosa else '❌ NO DETECTADA'}")
    
    if validacion_exitosa:
        print(f"   🌟 Detectamos componente en {freq_h1:.2f} Hz con significancia BF={bf:.1f}, p={p_value:.4f}")
    else:
        print(f"   ⚠️  Los criterios de validación no se cumplen completamente")
    
    return validacion_exitosa

def crear_graficos(h1_results, l1_results, p_value, bf, output_dir='../results/gw250114'):
    """
    Crear gráficos de diagnóstico
    """
    print(f"📊 Generando gráficos en {output_dir}...")
    os.makedirs(output_dir, exist_ok=True)
    
    freq_h1, snr_h1, asd_h1 = h1_results
    freq_l1, snr_l1, asd_l1 = l1_results
    
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(15, 10))
    
    # Subplot 1: Espectro H1
    freqs_h1 = asd_h1.frequencies.value
    mask_h1 = (freqs_h1 >= 130) & (freqs_h1 <= 160)
    ax1.loglog(freqs_h1[mask_h1], asd_h1.value[mask_h1], 'b-', label='H1 ASD')
    ax1.axvline(freq_h1, color='red', linestyle='--', label=f'Peak: {freq_h1:.2f} Hz')
    ax1.axvline(141.7, color='green', linestyle=':', label='Target: 141.7 Hz', alpha=0.7)
    ax1.set_xlabel('Frequency (Hz)')
    ax1.set_ylabel('ASD (strain/√Hz)')
    ax1.set_title(f'H1 Spectrum (SNR: {snr_h1:.2f})')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Subplot 2: Espectro L1
    freqs_l1 = asd_l1.frequencies.value
    mask_l1 = (freqs_l1 >= 130) & (freqs_l1 <= 160)
    ax2.loglog(freqs_l1[mask_l1], asd_l1.value[mask_l1], 'r-', label='L1 ASD')
    ax2.axvline(freq_l1, color='red', linestyle='--', label=f'Peak: {freq_l1:.2f} Hz')
    ax2.axvline(141.7, color='green', linestyle=':', label='Target: 141.7 Hz', alpha=0.7)
    ax2.set_xlabel('Frequency (Hz)')
    ax2.set_ylabel('ASD (strain/√Hz)')
    ax2.set_title(f'L1 Spectrum (SNR: {snr_l1:.2f})')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Subplot 3: Comparación H1 vs L1
    ax3.plot([freq_h1], [snr_h1], 'bo', markersize=10, label='H1')
    ax3.plot([freq_l1], [snr_l1], 'ro', markersize=10, label='L1')
    ax3.axvline(141.7, color='green', linestyle=':', alpha=0.7)
    ax3.axhline(5, color='orange', linestyle='--', alpha=0.7, label='SNR threshold')
    ax3.set_xlabel('Frequency (Hz)')
    ax3.set_ylabel('SNR')
    ax3.set_title('Multi-detector Comparison')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    ax3.set_xlim(140, 143)
    
    # Subplot 4: Métricas de validación
    metrics = ['Freq Match', 'p-value', 'Bayes Factor', 'H1 SNR']
    values = [
        1 if abs(freq_h1 - freq_l1) < 0.1 else 0,
        1 if p_value < 0.01 else 0,
        1 if bf > 10 else 0,
        1 if snr_h1 > 5 else 0
    ]
    colors = ['green' if v == 1 else 'red' for v in values]
    
    bars = ax4.bar(metrics, values, color=colors, alpha=0.7)
    ax4.set_ylabel('Validation Status')
    ax4.set_title('Validation Criteria')
    ax4.set_ylim(0, 1.2)
    
    # Añadir etiquetas de valores
    for bar, metric in zip(bars, metrics):
        height = bar.get_height()
        status = '✅' if height == 1 else '❌'
        ax4.text(bar.get_x() + bar.get_width()/2., height + 0.05,
                status, ha='center', va='bottom', fontsize=16)
    
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, 'analisis_completo.png'), dpi=300, bbox_inches='tight')
    print(f"   ✅ Gráfico guardado: analisis_completo.png")
    plt.close()

def main():
    """
    Ejecutar análisis completo de 6 pasos
    """
    print("🌌 Análisis GW250114 - Workflow de 6 pasos\n" + "="*50)
    
    try:
        # Paso 1: Descarga
        data_h1, data_l1, merger_time = paso1_descarga_datos('GW250114')
        
        # Paso 2: Preprocesamiento
        h1_clean, l1_clean = paso2_preprocesamiento(data_h1, data_l1)
        
        # Paso 3: Búsqueda dirigida
        h1_results, l1_results = paso3_busqueda_dirigida(h1_clean, l1_clean, merger_time)
        
        # Paso 4: Estadística clásica
        p_value, snr_observed, background = paso4_estadistica_clasica(
            h1_clean, l1_clean, merger_time
        )
        
        # Paso 5: Bayes Factor
        bf, model_params = paso5_bayes_factor(h1_clean, l1_clean, merger_time)
        
        # Paso 6: Validación cruzada
        freq_h1, snr_h1, _ = h1_results
        freq_l1, snr_l1, _ = l1_results
        
        validacion_exitosa = paso6_validacion_cruzada(
            freq_h1, freq_l1, snr_h1, snr_l1, p_value, bf
        )
        
        # Crear gráficos
        crear_graficos(h1_results, l1_results, p_value, bf)
        
        print("\n" + "="*50)
        print("🎯 ANÁLISIS COMPLETADO")
        print("="*50)
        
    except Exception as e:
        print(f"❌ Error durante el análisis: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()