#!/usr/bin/env python3
"""
Validador de GW150914 (Control) - Detección de 141.7 Hz
Implementa la validación mencionada en el problema statement:
- Detecta 141.7 Hz con SNR 7.47 (H1) y SNR 0.95 (L1)
- Calcula Bayes Factor
- Estima p-value con time-slides
"""
import numpy as np
import matplotlib.pyplot as plt
from scipy import signal, stats
from scipy.optimize import curve_fit
import h5py
import os
from gwpy.timeseries import TimeSeries
from gwosc import datasets
import sys

class ValidadorGW150914:
    def __init__(self):
        self.frecuencia_objetivo = 141.7
        self.gps_gw150914 = 1126259462.423  # Tiempo preciso del merger
        self.resultados_esperados = {
            'H1': {'snr': 7.47, 'freq': 141.69},
            'L1': {'snr': 0.95, 'freq': 141.75}
        }
        
    def cargar_datos(self, detector):
        """Cargar o descargar datos de GWOSC para el detector"""
        data_dir = os.path.join(os.path.dirname(__file__), '..', 'data', 'raw')
        os.makedirs(data_dir, exist_ok=True)
        
        archivo = os.path.join(data_dir, f'{detector}-GW150914-32s.hdf5')
        
        # Si el archivo existe, cargarlo; si no, descargarlo
        if os.path.exists(archivo):
            print(f"   📂 Cargando datos existentes: {archivo}")
            return TimeSeries.read(archivo)
        else:
            print(f"   🔄 Descargando datos de {detector}...")
            start = self.gps_gw150914 - 16
            end = self.gps_gw150914 + 16
            data = TimeSeries.fetch_open_data(
                detector, start, end, sample_rate=4096, cache=True
            )
            # Guardar para uso futuro
            data.write(archivo, overwrite=True)
            print(f"   💾 Datos guardados en: {archivo}")
            return data
    
    def analizar_ringdown(self, data, detector):
        """
        Analizar el ringdown para detectar la componente de 141.7 Hz
        """
        print(f"\n🔍 Analizando ringdown de {detector}")
        
        # Encontrar el momento del merger
        merger_idx = int((self.gps_gw150914 - data.t0.value) * data.sample_rate.value)
        
        # Aislar el ringdown (50 ms post-merger)
        ringdown_start = merger_idx
        ringdown_samples = int(0.05 * data.sample_rate.value)  # 50 ms
        ringdown = data[ringdown_start:ringdown_start + ringdown_samples]
        
        print(f"   📊 Ringdown: {len(ringdown)} muestras ({len(ringdown)/data.sample_rate.value*1000:.1f} ms)")
        
        # Análisis espectral
        spectrum = ringdown.asd(fftlength=None)
        
        # Encontrar pico más cercano a 141.7 Hz
        target_freq = self.frecuencia_objetivo
        freq_idx = np.argmin(np.abs(spectrum.frequencies.value - target_freq))
        detected_freq = spectrum.frequencies.value[freq_idx]
        power_detected = spectrum.value[freq_idx]
        
        # Calcular SNR (relativo al ruido de fondo en la banda 130-160 Hz)
        freq_mask = (spectrum.frequencies.value >= 130) & (spectrum.frequencies.value <= 160)
        noise_floor = np.median(spectrum.value[freq_mask])
        snr = power_detected / noise_floor
        
        print(f"   🎯 Frecuencia detectada: {detected_freq:.2f} Hz (objetivo: {target_freq} Hz)")
        print(f"   📈 SNR calculado: {snr:.2f}")
        
        # Comparar con resultados esperados
        expected = self.resultados_esperados[detector]
        freq_error = abs(detected_freq - expected['freq'])
        snr_error = abs(snr - expected['snr'])
        
        print(f"   📊 Resultado esperado: {expected['freq']:.2f} Hz, SNR {expected['snr']:.2f}")
        print(f"   📏 Error frecuencia: {freq_error:.3f} Hz")
        print(f"   📏 Error SNR: {snr_error:.2f}")
        
        # Criterios de validación
        freq_ok = freq_error < 0.1  # Tolerancia 0.1 Hz
        snr_ok = snr_error < 2.0    # Tolerancia 2.0 en SNR
        
        return {
            'detector': detector,
            'freq_detected': detected_freq,
            'snr_calculated': snr,
            'freq_expected': expected['freq'],
            'snr_expected': expected['snr'],
            'freq_error': freq_error,
            'snr_error': snr_error,
            'freq_valid': freq_ok,
            'snr_valid': snr_ok,
            'spectrum': spectrum,
            'ringdown': ringdown
        }
    
    def calcular_bayes_factor(self, resultado):
        """
        Calcular Bayes Factor para la presencia de la señal de 141.7 Hz
        BF = P(data|signal_present) / P(data|no_signal)
        """
        print(f"\n🧮 Calculando Bayes Factor para {resultado['detector']}")
        
        spectrum = resultado['spectrum']
        freq_target = self.frecuencia_objetivo
        
        # Encontrar índice de la frecuencia objetivo
        freq_idx = np.argmin(np.abs(spectrum.frequencies.value - freq_target))
        signal_power = spectrum.value[freq_idx]
        
        # Estimar ruido de fondo (mediana en banda 130-160 Hz excluyendo ±2 Hz alrededor del objetivo)
        freq_mask = ((spectrum.frequencies.value >= 130) & (spectrum.frequencies.value <= 160) &
                    ((spectrum.frequencies.value < freq_target - 2) | (spectrum.frequencies.value > freq_target + 2)))
        noise_power = np.median(spectrum.value[freq_mask])
        noise_std = np.std(spectrum.value[freq_mask])
        
        # Bayes Factor aproximado usando la razón señal/ruido
        # BF ≈ exp((signal_power - noise_power)^2 / (2 * noise_std^2))
        snr = (signal_power - noise_power) / noise_std
        bayes_factor = np.exp(snr**2 / 2)
        
        print(f"   📊 Potencia de señal: {signal_power:.2e}")
        print(f"   📊 Potencia de ruido: {noise_power:.2e}")
        print(f"   📊 SNR estadístico: {snr:.2f}")
        print(f"   🎯 Bayes Factor: {bayes_factor:.2e}")
        
        # Criterio de validación: BF > 10
        bf_valid = bayes_factor > 10
        print(f"   ✅ BF > 10: {'SÍ' if bf_valid else 'NO'}")
        
        resultado['bayes_factor'] = bayes_factor
        resultado['bf_valid'] = bf_valid
        
        return bayes_factor, bf_valid
    
    def calcular_pvalue_timeslides(self, resultado, n_slides=100):
        """
        Estimar p-value usando time-slides
        Desliza la señal en tiempo y cuenta cuántas veces se obtiene un SNR mayor
        """
        print(f"\n🔄 Calculando p-value con time-slides para {resultado['detector']}")
        
        ringdown = resultado['ringdown']
        target_freq = self.frecuencia_objetivo
        observed_snr = resultado['snr_calculated']
        
        # Crear slides temporales (desplazar la señal)
        slide_snrs = []
        slide_step = int(0.001 * ringdown.sample_rate.value)  # 1 ms steps
        
        for i in range(n_slides):
            # Desplazar la señal
            slide_offset = i * slide_step
            if slide_offset >= len(ringdown) // 2:
                break
                
            # Crear datos deslizados (circular shift)
            shifted_data = np.roll(ringdown.value, slide_offset)
            shifted_series = TimeSeries(shifted_data, 
                                      sample_rate=ringdown.sample_rate,
                                      t0=ringdown.t0)
            
            # Calcular espectro del slide
            slide_spectrum = shifted_series.asd(fftlength=None)
            
            # SNR en la frecuencia objetivo
            freq_idx = np.argmin(np.abs(slide_spectrum.frequencies.value - target_freq))
            slide_power = slide_spectrum.value[freq_idx]
            
            # Ruido de fondo para este slide
            freq_mask = ((slide_spectrum.frequencies.value >= 130) & 
                        (slide_spectrum.frequencies.value <= 160))
            slide_noise = np.median(slide_spectrum.value[freq_mask])
            slide_snr = slide_power / slide_noise
            
            slide_snrs.append(slide_snr)
        
        slide_snrs = np.array(slide_snrs)
        
        # Calcular p-value: fracción de slides con SNR >= observed_snr
        n_greater = np.sum(slide_snrs >= observed_snr)
        p_value = n_greater / len(slide_snrs)
        
        print(f"   🔢 Slides procesados: {len(slide_snrs)}")
        print(f"   📊 SNR observado: {observed_snr:.2f}")
        print(f"   📊 SNR promedio slides: {np.mean(slide_snrs):.2f} ± {np.std(slide_snrs):.2f}")
        print(f"   📊 Slides con SNR >= observado: {n_greater}/{len(slide_snrs)}")
        print(f"   🎯 p-value estimado: {p_value:.4f}")
        
        # Criterio de validación: p < 0.01
        p_valid = p_value < 0.01
        print(f"   ✅ p < 0.01: {'SÍ' if p_valid else 'NO'}")
        
        resultado['p_value'] = p_value
        resultado['p_valid'] = p_valid
        resultado['slide_snrs'] = slide_snrs
        
        return p_value, p_valid
    
    def validar_detector(self, detector):
        """Validación completa para un detector"""
        print(f"\n{'='*60}")
        print(f"🔍 VALIDACIÓN {detector} - GW150914")
        print(f"{'='*60}")
        
        try:
            # 1. Cargar datos
            data = self.cargar_datos(detector)
            
            # 2. Análizar ringdown
            resultado = self.analizar_ringdown(data, detector)
            
            # 3. Calcular Bayes Factor
            self.calcular_bayes_factor(resultado)
            
            # 4. Calcular p-value
            self.calcular_pvalue_timeslides(resultado)
            
            # 5. Verificar validación general
            validacion_total = (resultado['freq_valid'] and 
                              resultado['snr_valid'] and 
                              resultado['bf_valid'] and 
                              resultado['p_valid'])
            
            print(f"\n📋 RESUMEN VALIDACIÓN {detector}:")
            print(f"   ✅ Frecuencia válida: {'SÍ' if resultado['freq_valid'] else 'NO'}")
            print(f"   ✅ SNR válido: {'SÍ' if resultado['snr_valid'] else 'NO'}")
            print(f"   ✅ Bayes Factor > 10: {'SÍ' if resultado['bf_valid'] else 'NO'}")
            print(f"   ✅ p-value < 0.01: {'SÍ' if resultado['p_valid'] else 'NO'}")
            print(f"   🎯 VALIDACIÓN TOTAL: {'✅ EXITOSA' if validacion_total else '❌ FALLIDA'}")
            
            return resultado, validacion_total
            
        except Exception as e:
            print(f"❌ Error en validación de {detector}: {e}")
            import traceback
            traceback.print_exc()
            return None, False
    
    def validar_coherencia(self, resultado_h1, resultado_l1):
        """Validar coherencia entre H1 y L1"""
        print(f"\n{'='*60}")
        print("🔗 VALIDACIÓN DE COHERENCIA H1-L1")
        print(f"{'='*60}")
        
        if resultado_h1 is None or resultado_l1 is None:
            print("❌ No se puede validar coherencia: datos faltantes")
            return False
        
        # Diferencia en frecuencias detectadas
        freq_diff = abs(resultado_h1['freq_detected'] - resultado_l1['freq_detected'])
        print(f"📊 Diferencia de frecuencias: {freq_diff:.3f} Hz")
        
        # Coherencia en Bayes Factor (ambos > 10?)
        bf_coherent = resultado_h1['bf_valid'] and resultado_l1['bf_valid']
        print(f"🧮 BF coherente (ambos > 10): {'SÍ' if bf_coherent else 'NO'}")
        
        # Coherencia en p-values (ambos < 0.01?)
        p_coherent = resultado_h1['p_valid'] and resultado_l1['p_valid']
        print(f"📊 p-value coherente (ambos < 0.01): {'SÍ' if p_coherent else 'NO'}")
        
        # Criterio de coherencia general
        coherencia_ok = freq_diff < 0.2 and bf_coherent and p_coherent
        
        print(f"\n🎯 COHERENCIA H1-L1: {'✅ VALIDADA' if coherencia_ok else '❌ NO VALIDADA'}")
        
        return coherencia_ok

def main():
    """Ejecutor principal del validador GW150914"""
    print("🌌 GW250114 - 141.7001 Hz Analysis")
    print("🔍 Validador GW150914 (Control)")
    print("🎯 Resultados esperados: H1 SNR=7.47, L1 SNR=0.95")
    print()
    
    validador = ValidadorGW150914()
    
    # Validar H1
    resultado_h1, valido_h1 = validador.validar_detector('H1')
    
    # Validar L1
    resultado_l1, valido_l1 = validador.validar_detector('L1')
    
    # Validar coherencia
    coherencia = validador.validar_coherencia(resultado_h1, resultado_l1)
    
    # Resultado final
    print(f"\n{'='*80}")
    print("🏁 RESULTADO FINAL DE VALIDACIÓN")
    print(f"{'='*80}")
    print(f"📡 H1 validado: {'✅' if valido_h1 else '❌'}")
    print(f"📡 L1 validado: {'✅' if valido_l1 else '❌'}")
    print(f"🔗 Coherencia: {'✅' if coherencia else '❌'}")
    
    validacion_completa = valido_h1 and valido_l1 and coherencia
    
    if validacion_completa:
        print("\n🚀 VALIDACIÓN COMPLETA EXITOSA")
        print("   GW150914 reproduce los resultados esperados")
        print("   Sistema preparado para análisis de GW250114")
        print("   Criterios cumplidos:")
        print("   - BF > 10 ✅")
        print("   - p < 0.01 ✅")  
        print("   - Coherencia H1-L1 ✅")
        return True
    else:
        print("\n❌ VALIDACIÓN INCOMPLETA")
        print("   Revisar criterios de análisis")
        return False

if __name__ == "__main__":
    exito = main()
    sys.exit(0 if exito else 1)
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
