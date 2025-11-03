#!/usr/bin/env python3
"""
Validador científico GW150914 - Control con Bayes Factor y p-values
Implementa validación rigurosa de la detección de 141.7 Hz en GW150914 como control.
"""
import sys
import os
import numpy as np
import matplotlib.pyplot as plt
from gwpy.timeseries import TimeSeries
from scipy import signal, stats
from scipy.optimize import curve_fit
import warnings

def load_gw150914_data():
    """Cargar datos de GW150914 desde GWOSC"""
    print("📡 Descargando datos de GW150914...")
    
    try:
        # Parámetros del evento GW150914
        merger_time = 1126259462.423
        start = merger_time - 16  # 32 segundos de datos
        end = merger_time + 16
        
        # Descargar datos de ambos detectores
        print("   Descargando H1...")
        h1_data = TimeSeries.fetch_open_data('H1', start, end, sample_rate=4096)
        
        print("   Descargando L1...")
        l1_data = TimeSeries.fetch_open_data('L1', start, end, sample_rate=4096)
        
        print(f"   ✅ Datos cargados: {len(h1_data)} muestras a {h1_data.sample_rate} Hz")
        
        return h1_data, l1_data, merger_time
        
    except Exception as e:
        print(f"   ❌ Error cargando datos: {e}")
        return None, None, None

def preprocess_data(data):
    """Preprocesamiento estándar de datos LIGO"""
    # Filtros estándar
    data = data.highpass(20)  # Remover ruido de baja frecuencia
    data = data.notch(60)     # Remover línea de 60 Hz
    data = data.notch(120)    # Remover armónico de 120 Hz
    
    return data

def extract_ringdown(data, merger_time, duration=0.05):
    """Extraer segmento de ringdown post-merger"""
    ringdown_start = merger_time + 0.01  # 10 ms post-merger
    ringdown_end = ringdown_start + duration  # 50 ms de ringdown
    
    ringdown = data.crop(ringdown_start, ringdown_end)
    return ringdown

def damped_sine_model(t, A, tau, f, phi):
    """Modelo de seno amortiguado para fitting"""
    return A * np.exp(-t/tau) * np.cos(2*np.pi*f*t + phi)

def two_mode_model(t, A1, tau1, f1, phi1, A2, tau2, f2, phi2):
    """Modelo de dos modos amortiguados"""
    mode1 = A1 * np.exp(-t/tau1) * np.cos(2*np.pi*f1*t + phi1)
    mode2 = A2 * np.exp(-t/tau2) * np.cos(2*np.pi*f2*t + phi2)
    return mode1 + mode2

def calculate_bayes_factor(data, target_freq=141.7):
    """Calcular Bayes Factor comparando modelos con y sin 141.7 Hz"""
    print(f"🧮 Calculando Bayes Factor para {target_freq} Hz...")
    
    time_data = data.times.value - data.t0.value
    strain_data = data.value
    
    # Modelo 1: Sin 141.7 Hz (solo modo dominante ~250 Hz)
    p0_single = [1e-21, 0.01, 250, 0]  # A, tau, f, phi
    
    try:
        popt_single, pcov_single = curve_fit(
            damped_sine_model, time_data, strain_data, 
            p0=p0_single, maxfev=1000
        )
        
        # Calcular residuales y likelihood
        model_single = damped_sine_model(time_data, *popt_single)
        residuals_single = strain_data - model_single
        chi2_single = np.sum(residuals_single**2)
        
    except Exception as e:
        print(f"   ⚠️  Error en ajuste modo único: {e}")
        chi2_single = np.inf
    
    # Modelo 2: Con 141.7 Hz (dos modos)
    p0_double = list(p0_single) + [1e-23, 0.01, target_freq, 0]
    
    try:
        popt_double, pcov_double = curve_fit(
            two_mode_model, time_data, strain_data, 
            p0=p0_double, maxfev=1000
        )
        
        # Calcular residuales y likelihood
        model_double = two_mode_model(time_data, *popt_double)
        residuals_double = strain_data - model_double
        chi2_double = np.sum(residuals_double**2)
        
    except Exception as e:
        print(f"   ⚠️  Error en ajuste dos modos: {e}")
        chi2_double = np.inf
    
    # Calcular Bayes Factor (aproximación usando chi-cuadrado)
    # BF = exp(-0.5 * (chi2_double - chi2_single)) ajustado por parámetros
    delta_chi2 = chi2_single - chi2_double
    n_extra_params = 4  # Parámetros adicionales en modelo doble
    
    # Penalización por complejidad (AIC-like)
    bayes_factor = np.exp(0.5 * (delta_chi2 - n_extra_params))
    
    print(f"   Chi² modelo único: {chi2_single:.2e}")
    print(f"   Chi² modelo doble: {chi2_double:.2e}")
    print(f"   Δχ²: {delta_chi2:.2e}")
    print(f"   Bayes Factor: {bayes_factor:.2f}")
    
    return bayes_factor, chi2_single, chi2_double

def estimate_p_value_timeslides(data, target_freq=141.7, n_slides=1000):
    """Estimar p-value usando time-slides"""
    print(f"📊 Estimando p-value con {n_slides} time-slides...")
    
    strain = data.value
    sample_rate = data.sample_rate.value
    
    # Calcular SNR observado en la frecuencia objetivo
    freqs = np.fft.rfftfreq(len(strain), d=1/sample_rate)
    fft_strain = np.fft.rfft(strain)
    power_spectrum = np.abs(fft_strain)**2
    
    # Encontrar potencia en frecuencia objetivo
    target_idx = np.argmin(np.abs(freqs - target_freq))
    observed_power = power_spectrum[target_idx]
    
    # Calcular SNR como potencia / mediana del espectro
    noise_floor = np.median(power_spectrum)
    observed_snr = observed_power / noise_floor
    
    # Realizar time-slides para estimar background
    background_snrs = []
    
    for i in range(n_slides):
        # Desplazamiento aleatorio que preserve la estructura temporal
        max_shift = len(strain) - sample_rate
        if max_shift <= sample_rate:
            # Para datos muy cortos, usar todo el rango disponible
            shift = np.random.randint(1, max(2, len(strain)))
        else:
            shift = np.random.randint(sample_rate, max_shift)
        shifted_strain = np.roll(strain, shift)
        
        # Calcular espectro del strain desplazado
        fft_shifted = np.fft.rfft(shifted_strain)
        power_shifted = np.abs(fft_shifted)**2
        
        # SNR en la frecuencia objetivo
        bg_power = power_shifted[target_idx]
        bg_noise = np.median(power_shifted)
        bg_snr = bg_power / bg_noise
        
        background_snrs.append(bg_snr)
    
    # Calcular p-value
    background_snrs = np.array(background_snrs)
    p_value = np.sum(background_snrs >= observed_snr) / n_slides
    
    print(f"   SNR observado: {observed_snr:.2f}")
    print(f"   SNR medio background: {np.mean(background_snrs):.2f}")
    print(f"   SNR std background: {np.std(background_snrs):.2f}")
    print(f"   p-value estimado: {p_value:.4f}")
    
    return p_value, observed_snr, background_snrs

def validate_detector(detector_data, detector_name, merger_time):
    """Validar un detector individual"""
    print(f"\n🔍 Validando {detector_name}...")
    
    # Preprocesamiento
    processed_data = preprocess_data(detector_data)
    
    # Extraer ringdown
    ringdown = extract_ringdown(processed_data, merger_time)
    
    # Calcular Bayes Factor
    bf, chi2_single, chi2_double = calculate_bayes_factor(ringdown)
    
    # Estimar p-value
    p_value, snr, bg_snrs = estimate_p_value_timeslides(ringdown)
    
    # Criterios de validación
    bf_threshold = 10.0  # Evidencia fuerte
    p_threshold = 0.01   # Significancia del 1%
    
    bf_passed = bf > bf_threshold
    p_passed = p_value < p_threshold
    
    print(f"   📊 Resultados {detector_name}:")
    print(f"      Bayes Factor: {bf:.2f} ({'✅' if bf_passed else '❌'} > {bf_threshold})")
    print(f"      p-value: {p_value:.4f} ({'✅' if p_passed else '❌'} < {p_threshold})")
    print(f"      SNR: {snr:.2f}")
    
    return {
        'detector': detector_name,
        'bayes_factor': bf,
        'p_value': p_value,
        'snr': snr,
        'bf_passed': bf_passed,
        'p_passed': p_passed,
        'chi2_single': chi2_single,
        'chi2_double': chi2_double
    }

def main():
    """Ejecutar validación completa de GW150914"""
    print("🌌 VALIDACIÓN CIENTÍFICA GW150914 (CONTROL)")
    print("=" * 60)
    print("Criterios: BF > 10, p < 0.01, coherencia H1-L1")
    print("=" * 60)
    
    # Cargar datos
    h1_data, l1_data, merger_time = load_gw150914_data()
    
    if h1_data is None:
        print("❌ Error cargando datos - abortando validación")
        return 1
    
    # Validar cada detector
    h1_results = validate_detector(h1_data, 'H1', merger_time)
    l1_results = validate_detector(l1_data, 'L1', merger_time)
    
    # Evaluación final
    print(f"\n📈 RESUMEN DE VALIDACIÓN:")
    print("=" * 40)
    
    all_criteria_met = True
    
    # H1 criteria
    print(f"H1: BF={h1_results['bayes_factor']:.2f}, p={h1_results['p_value']:.4f}")
    h1_valid = h1_results['bf_passed'] and h1_results['p_passed']
    if not h1_valid:
        all_criteria_met = False
    
    # L1 criteria
    print(f"L1: BF={l1_results['bayes_factor']:.2f}, p={l1_results['p_value']:.4f}")
    l1_valid = l1_results['bf_passed'] and l1_results['p_passed']
    if not l1_valid:
        all_criteria_met = False
    
    # Coherencia (frecuencias similares en ambos detectores)
    freq_diff = abs(h1_results['snr'] - l1_results['snr'])  # Usando SNR como proxy
    coherence_ok = freq_diff < 10  # Tolerancia en SNR
    print(f"Coherencia H1-L1: {'✅' if coherence_ok else '❌'} (ΔSNR = {freq_diff:.2f})")
    
    if not coherence_ok:
        all_criteria_met = False
    
    print("\n🎯 RESULTADO FINAL:")
    if all_criteria_met:
        print("✅ VALIDACIÓN GW150914 EXITOSA")
        print("🚀 Framework listo para aplicar a GW250114")
        return 0
    else:
        print("❌ VALIDACIÓN GW150914 FALLIDA") 
        print("💡 Revisar métodos o criterios de validación")
        return 1

if __name__ == "__main__":
    # Suprimir warnings de scipy que pueden aparecer en fitting
    warnings.filterwarnings('ignore', category=RuntimeWarning)
    sys.exit(main())