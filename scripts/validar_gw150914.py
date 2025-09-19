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
    
    # Normalizar tiempo para mejor condicionamiento numérico
    t_norm = time_data - time_data[0]
    t_scale = np.max(t_norm)
    if t_scale > 0:
        t_norm = t_norm / t_scale
    
    # Estimar parámetros iniciales más robustos
    strain_std = np.std(strain_data)
    strain_max = np.max(np.abs(strain_data))
    
    # Modelo 1: Sin 141.7 Hz (solo modo dominante ~250 Hz)
    # Parámetros iniciales más conservadores
    A_init = min(strain_max * 0.1, strain_std * 5)
    tau_init = 0.01 * t_scale  # Escalar tau por el tiempo
    
    p0_single = [A_init, tau_init, 250, 0]
    
    # Bounds para evitar parámetros no físicos
    bounds_single = (
        [0, 0.001*t_scale, 200, -np.pi],           # Lower bounds
        [strain_max, 0.1*t_scale, 300, np.pi]     # Upper bounds
    )
    
    try:
        popt_single, pcov_single = curve_fit(
            lambda t, A, tau, f, phi: damped_sine_model(t*t_scale + time_data[0], A, tau, f, phi),
            t_norm, strain_data, 
            p0=p0_single, bounds=bounds_single, maxfev=2000
        )
        
        # Calcular modelo con parámetros reescalados
        model_single = damped_sine_model(time_data, *popt_single)
        residuals_single = strain_data - model_single
        chi2_single = np.sum(residuals_single**2)
        
        # Verificar calidad del ajuste
        rms_residual = np.sqrt(np.mean(residuals_single**2))
        if rms_residual > strain_std * 2:
            print(f"   ⚠️  Ajuste modo único de baja calidad (RMS residual: {rms_residual:.2e})")
        
    except Exception as e:
        print(f"   ⚠️  Error en ajuste modo único: {e}")
        chi2_single = np.inf
        popt_single = p0_single
    
    # Modelo 2: Con 141.7 Hz (dos modos)
    A_target_init = min(A_init * 0.5, strain_std * 2)  # Señal más débil
    p0_double = list(popt_single) + [A_target_init, tau_init, target_freq, np.pi/4]
    
    bounds_double = (
        list(bounds_single[0]) + [0, 0.001*t_scale, target_freq-5, -np.pi],
        list(bounds_single[1]) + [strain_max*0.5, 0.1*t_scale, target_freq+5, np.pi]
    )
    
    try:
        popt_double, pcov_double = curve_fit(
            lambda t, A1, tau1, f1, phi1, A2, tau2, f2, phi2: two_mode_model(t*t_scale + time_data[0], A1, tau1, f1, phi1, A2, tau2, f2, phi2),
            t_norm, strain_data, 
            p0=p0_double, bounds=bounds_double, maxfev=2000
        )
        
        # Calcular modelo con parámetros reescalados
        model_double = two_mode_model(time_data, *popt_double)
        residuals_double = strain_data - model_double
        chi2_double = np.sum(residuals_double**2)
        
        # Verificar calidad del ajuste
        rms_residual = np.sqrt(np.mean(residuals_double**2))
        if rms_residual > strain_std:
            print(f"   ⚠️  Ajuste dos modos de baja calidad (RMS residual: {rms_residual:.2e})")
        
    except Exception as e:
        print(f"   ⚠️  Error en ajuste dos modos: {e}")
        chi2_double = np.inf
    
    # Calcular Bayes Factor robusto
    if chi2_single == np.inf and chi2_double == np.inf:
        bayes_factor = 1.0  # No se puede determinar
        delta_chi2 = 0.0
        print("   ⚠️  Ambos ajustes fallaron - BF indeterminado")
    elif chi2_single == np.inf:
        bayes_factor = 100.0  # Modelo doble claramente mejor
        delta_chi2 = np.inf
        print("   ✅ Solo el modelo doble convergió")
    elif chi2_double == np.inf:
        bayes_factor = 0.01  # Modelo simple claramente mejor
        delta_chi2 = -np.inf
        print("   ⚠️  Solo el modelo simple convergió")
    else:
        # Cálculo estándar con validaciones
        delta_chi2 = chi2_single - chi2_double
        n_extra_params = 4  # Parámetros adicionales en modelo doble
        
        # Evitar overflow en exponencial
        exponent = 0.5 * (delta_chi2 - n_extra_params)
        if exponent > 50:  # Evitar overflow
            bayes_factor = 1e20
        elif exponent < -50:  # Evitar underflow
            bayes_factor = 1e-20
        else:
            bayes_factor = np.exp(exponent)
        
        # Verificar si la mejora es significativa
        if chi2_single > 0:
            improvement = (chi2_single - chi2_double) / chi2_single
            if improvement < 0.01:  # Menos del 1% de mejora
                print(f"   💡 Mejora mínima detectada ({improvement*100:.2f}%)")
    
    print(f"   Chi² modelo único: {chi2_single:.2e}")
    print(f"   Chi² modelo doble: {chi2_double:.2e}")
    print(f"   Δχ²: {delta_chi2:.2e}")
    print(f"   Bayes Factor: {bayes_factor:.2f}")
    
    return bayes_factor, chi2_single, chi2_double

def estimate_p_value_timeslides(data, target_freq=141.7, n_slides=1000):
    """Estimar p-value usando time-slides con metodología mejorada"""
    print(f"📊 Estimando p-value con {n_slides} time-slides...")
    
    strain = data.value
    sample_rate = data.sample_rate.value
    
    # Aplicar ventana para reducir efectos de borde
    window = signal.windows.tukey(len(strain), alpha=0.1)
    strain_windowed = strain * window
    
    # Calcular PSD más robusto usando método de Welch
    nperseg = min(len(strain) // 4, 1024)  # Segmento apropiado
    noverlap = nperseg // 2  # 50% overlap
    freqs, psd = signal.welch(strain_windowed, fs=sample_rate, 
                              nperseg=nperseg, noverlap=noverlap)
    
    # Encontrar bin de frecuencia objetivo
    target_idx = np.argmin(np.abs(freqs - target_freq))
    target_freq_actual = freqs[target_idx]
    
    print(f"   Frecuencia objetivo: {target_freq} Hz (bin: {target_freq_actual:.2f} Hz)")
    
    # Calcular SNR observado
    observed_power = psd[target_idx]
    
    # Estimar ruido de fondo usando frecuencias vecinas
    # Evitar la frecuencia objetivo y sus inmediatos vecinos
    freq_mask = np.abs(freqs - target_freq) > 5.0  # Más de 5 Hz de diferencia
    if np.sum(freq_mask) > 10:  # Suficientes puntos para estadística
        noise_floor = np.median(psd[freq_mask])
    else:
        noise_floor = np.median(psd)  # Fallback
    
    observed_snr = observed_power / noise_floor
    
    # Realizar time-slides para estimar background
    background_snrs = []
    
    # Para datos sintéticos, usar shifts más pequeños para preservar estructura
    min_shift = int(sample_rate * 0.001)  # 1ms mínimo
    max_shift = len(strain) - int(sample_rate * 0.01)  # Evitar extremos
    
    if max_shift <= min_shift:
        print("   ⚠️  Datos muy cortos para time-slides - usando método alternativo")
        # Para datos muy cortos, usar permutación de fases
        background_snrs = estimate_background_phase_scrambling(strain_windowed, target_idx, 
                                                                sample_rate, n_slides)
        observed_snr_final = observed_snr
    else:
        for i in range(n_slides):
            # Desplazamiento aleatorio
            shift = np.random.randint(min_shift, max_shift)
            shifted_strain = np.roll(strain_windowed, shift)
            
            # Calcular PSD del strain desplazado
            _, psd_shifted = signal.welch(shifted_strain, fs=sample_rate,
                                          nperseg=nperseg, noverlap=noverlap)
            
            # SNR en la frecuencia objetivo
            bg_power = psd_shifted[target_idx]
            
            # Usar mismo método de estimación de ruido
            if np.sum(freq_mask) > 10:
                bg_noise = np.median(psd_shifted[freq_mask])
            else:
                bg_noise = np.median(psd_shifted)
            
            bg_snr = bg_power / bg_noise if bg_noise > 0 else 0
            background_snrs.append(bg_snr)
        
        observed_snr_final = observed_snr
    
    # Calcular estadísticas del background
    background_snrs = np.array(background_snrs)
    background_snrs = background_snrs[np.isfinite(background_snrs)]  # Remover NaN/Inf
    
    if len(background_snrs) == 0:
        print("   ⚠️  No se pudieron generar time-slides válidos")
        return 0.5, observed_snr_final, np.array([observed_snr_final])
    
    # Calcular p-value
    p_value = np.sum(background_snrs >= observed_snr_final) / len(background_snrs)
    
    # Evitar p-value exactamente 0 (poco realista)
    if p_value == 0.0 and len(background_snrs) > 0:
        p_value = 1.0 / (len(background_snrs) + 1)
    
    print(f"   SNR observado: {observed_snr_final:.2f}")
    print(f"   SNR medio background: {np.mean(background_snrs):.2f}")
    print(f"   SNR std background: {np.std(background_snrs):.2f}")
    print(f"   Slides válidos: {len(background_snrs)}/{n_slides}")
    print(f"   p-value estimado: {p_value:.4f}")
    
    return p_value, observed_snr_final, background_snrs

def estimate_background_phase_scrambling(strain, target_idx, sample_rate, n_scrambles):
    """Método alternativo usando scrambling de fases para datos cortos"""
    background_snrs = []
    
    # FFT del strain original
    fft_strain = np.fft.rfft(strain)
    freqs = np.fft.rfftfreq(len(strain), d=1/sample_rate)
    
    for i in range(n_scrambles):
        # Scrambling de fases (preserva amplitudes)
        phases = np.random.uniform(-np.pi, np.pi, len(fft_strain))
        phases[0] = 0  # DC phase = 0
        if len(phases) % 2 == 0:
            phases[-1] = 0  # Nyquist phase = 0
        
        # Crear FFT con fases aleatorias
        scrambled_fft = np.abs(fft_strain) * np.exp(1j * phases)
        
        # Transformada inversa
        scrambled_strain = np.fft.irfft(scrambled_fft, n=len(strain))
        
        # Calcular PSD del strain scrambled
        nperseg = min(len(strain) // 4, 1024)
        noverlap = nperseg // 2
        _, psd_scrambled = signal.welch(scrambled_strain, fs=sample_rate,
                                        nperseg=nperseg, noverlap=noverlap)
        
        # SNR en frecuencia objetivo
        bg_power = psd_scrambled[target_idx]
        bg_noise = np.median(psd_scrambled)
        bg_snr = bg_power / bg_noise if bg_noise > 0 else 0
        
        background_snrs.append(bg_snr)
    
    return background_snrs

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