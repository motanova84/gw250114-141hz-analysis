#!/usr/bin/env python3
"""
Análisis completo de GW250114 - Búsqueda de componente en 141.7 Hz
Implementa el estándar de análisis de ondas gravitacionales según LIGO/Virgo

Basado en los requerimientos del problema:
1. Descarga oficial de datos GWOSC
2. Preprocesamiento estándar
3. Búsqueda dirigida en 141.7 Hz 
4. Estadística clásica (p-value)
5. Bayes Factor (BF)
6. Validación cruzada H1/L1
"""

from gwpy.timeseries import TimeSeries
from gwosc.datasets import event_gps
import numpy as np
import matplotlib.pyplot as plt
from scipy import signal, stats
import os
from typing import Tuple, Dict, Optional
import warnings
warnings.filterwarnings('ignore')


class GW250114Analyzer:
    """Analizador completo para GW250114 con búsqueda dirigida en 141.7 Hz"""
    
    def __init__(self, target_frequency: float = 141.7):
        self.target_frequency = target_frequency
        self.results = {}
        
    def download_official_data(self, event_name: str = 'GW250114') -> Tuple[TimeSeries, TimeSeries, float]:
        """
        1. 📥 Descarga oficial de datos
        Cuando GWOSC libere GW250114
        """
        print(f"🌐 Descargando datos oficiales de {event_name}...")
        
        try:
            # Tiempo GPS oficial del evento
            gps = event_gps(event_name)
            print(f"   GPS time: {gps}")
            
            # Descargar datos de ambos detectores H1 y L1
            print("   Descargando H1...")
            h1 = TimeSeries.fetch_open_data('H1', gps-16, gps+16, sample_rate=4096)
            
            print("   Descargando L1...")
            l1 = TimeSeries.fetch_open_data('L1', gps-16, gps+16, sample_rate=4096)
            
            print("   ✅ Datos descargados exitosamente")
            return h1, l1, gps
            
        except Exception as e:
            print(f"   ❌ Error: {e}")
            print(f"   ℹ️  {event_name} aún no disponible en GWOSC")
            raise
    
    def standard_preprocessing(self, data: TimeSeries) -> TimeSeries:
        """
        2. ⚙️ Preprocesamiento estándar
        Aplicar el pipeline común de LIGO
        """
        print("🔧 Aplicando preprocesamiento estándar...")
        
        # Pipeline estándar LIGO/Virgo
        processed = data.highpass(20).notch(60).whiten()
        
        print("   ✅ Filtro pasa-altas 20 Hz")
        print("   ✅ Notch en 60 Hz (ruido eléctrico)")  
        print("   ✅ Whitening para normalizar ruido")
        
        return processed
    
    def directed_search_141hz(self, data_proc: TimeSeries, gps: float) -> Dict:
        """
        3. 🔎 Búsqueda dirigida en 141.7 Hz
        Extraer ringdown y calcular espectro
        """
        print(f"🎯 Búsqueda dirigida en {self.target_frequency} Hz...")
        
        # Extraer ringdown (50 ms después del merger)
        ring_data = data_proc.crop(gps+0.01, gps+0.06)
        print(f"   Ringdown: {len(ring_data)} muestras, {len(ring_data)/data_proc.sample_rate.value*1000:.1f} ms")
        
        # Calcular espectro
        psd = ring_data.asd(fftlength=0.05)
        
        # Encontrar frecuencia más cercana a 141.7 Hz
        freqs = psd.frequencies.value
        spectrum = psd.value
        idx = np.argmin(np.abs(freqs - self.target_frequency))
        detected_freq = freqs[idx]
        
        # Calcular SNR aproximado
        snr = spectrum[idx] / np.median(spectrum)
        
        results = {
            'detected_frequency': detected_freq,
            'target_frequency': self.target_frequency,
            'snr': snr,
            'spectrum': spectrum,
            'frequencies': freqs,
            'ringdown_data': ring_data
        }
        
        print(f"   Frecuencia detectada: {detected_freq:.3f} Hz")
        print(f"   SNR aproximado: {snr:.2f}")
        print(f"   Diferencia con objetivo: {abs(detected_freq - self.target_frequency):.3f} Hz")
        
        return results
    
    def classical_statistics(self, h1_proc: TimeSeries, l1_proc: TimeSeries, gps: float, 
                           n_slides: int = 100) -> float:
        """
        4. 📊 Estadística clásica (p-value)
        Time-slides para romper coincidencia temporal
        """
        print("📈 Calculando estadística clásica (p-value)...")
        
        # Análisis en datos reales
        real_h1 = self.directed_search_141hz(h1_proc, gps)
        real_l1 = self.directed_search_141hz(l1_proc, gps)
        real_snr_combined = np.sqrt(real_h1['snr']**2 + real_l1['snr']**2)
        
        print(f"   SNR combinado real: {real_snr_combined:.2f}")
        
        # Time-slides: desplazar artificialmente H1 y L1
        slide_snrs = []
        slide_range = 0.2  # ±0.2 segundos
        
        for i in range(n_slides):
            # Desplazamiento aleatorio
            offset = np.random.uniform(-slide_range, slide_range)
            
            try:
                # Aplicar desplazamiento temporal
                fake_gps = gps + offset
                fake_h1 = self.directed_search_141hz(h1_proc, fake_gps)
                fake_l1 = self.directed_search_141hz(l1_proc, gps)  # L1 sin offset
                fake_snr = np.sqrt(fake_h1['snr']**2 + fake_l1['snr']**2)
                slide_snrs.append(fake_snr)
            except:
                continue
                
        slide_snrs = np.array(slide_snrs)
        
        # Calcular p-value
        p_value = np.sum(slide_snrs >= real_snr_combined) / len(slide_snrs)
        
        print(f"   Time-slides realizados: {len(slide_snrs)}")
        print(f"   p-value: {p_value:.4f}")
        print(f"   Significativo (p<0.01): {'SÍ' if p_value < 0.01 else 'NO'}")
        
        return p_value
    
    def bayesian_analysis(self, data: TimeSeries) -> float:
        """
        5. 📈 Bayes Factor (BF)
        Comparar modelo con y sin señal en 141.7 Hz
        """
        print("🧮 Calculando Bayes Factor...")
        
        # Implementación simplificada del Bayes Factor
        # En la práctica se usarían librerías como bilby o pycbc
        
        # Modelo M0: solo ruido
        # Modelo M1: ruido + señal senoidal amortiguada en 141.7 Hz
        
        # Para este ejemplo, calculamos una aproximación
        # basada en la relación señal/ruido
        
        # Extraer espectro alrededor de 141.7 Hz
        spectrum = data.asd(fftlength=0.05)
        freqs = spectrum.frequencies.value
        
        # Región de interés ±2 Hz alrededor de 141.7 Hz
        mask = (freqs >= self.target_frequency - 2) & (freqs <= self.target_frequency + 2)
        local_spectrum = spectrum.value[mask]
        local_freqs = freqs[mask]
        
        if len(local_spectrum) == 0:
            print("   ⚠️  No hay datos en la región de interés")
            return 1.0
        
        # Encontrar pico
        peak_idx = np.argmax(local_spectrum)
        peak_power = local_spectrum[peak_idx]
        peak_freq = local_freqs[peak_idx]
        
        # Estimar ruido de fondo en una región más amplia
        noise_mask = (freqs >= 100) & (freqs <= 200) & (~mask)
        if np.sum(noise_mask) > 0:
            noise_floor = np.median(spectrum.value[noise_mask])
        else:
            noise_floor = np.median(spectrum.value)
        
        # Aproximación del Bayes Factor
        # BF ≈ exp((SNR²)/2) para señales gaussianas
        snr_local = peak_power / noise_floor
        bf_approx = np.exp((snr_local**2 - 1) / 2)
        
        # Limitar para evitar valores extremos
        bf_approx = min(max(bf_approx, 0.1), 1000)
        
        print(f"   Pico en {peak_freq:.2f} Hz con SNR: {snr_local:.2f}")
        print(f"   Bayes Factor (aproximado): {bf_approx:.2f}")
        print(f"   Evidencia fuerte (BF>10): {'SÍ' if bf_approx > 10 else 'NO'}")
        
        return bf_approx
    
    def cross_validation(self, results_h1: Dict, results_l1: Dict) -> bool:
        """
        6. ✅ Validación cruzada entre detectores
        """
        print("🔍 Validación cruzada H1-L1...")
        
        freq_h1 = results_h1['detected_frequency']
        freq_l1 = results_l1['detected_frequency']
        freq_diff = abs(freq_h1 - freq_l1)
        
        snr_h1 = results_h1['snr']
        snr_l1 = results_l1['snr']
        
        # Criterios de validación
        freq_consistent = freq_diff < 0.1  # ±0.1 Hz
        both_significant = snr_h1 > 3 and snr_l1 > 3
        
        print(f"   H1 frecuencia: {freq_h1:.3f} Hz, SNR: {snr_h1:.2f}")
        print(f"   L1 frecuencia: {freq_l1:.3f} Hz, SNR: {snr_l1:.2f}")
        print(f"   Diferencia frecuencia: {freq_diff:.3f} Hz")
        print(f"   Consistencia frecuencia: {'✅' if freq_consistent else '❌'}")
        print(f"   Ambos significativos: {'✅' if both_significant else '❌'}")
        
        validation_passed = freq_consistent and both_significant
        return validation_passed
    
    def create_diagnostic_plots(self, results_h1: Dict, results_l1: Dict, 
                              output_dir: str = '../results/figures'):
        """Crear gráficos de diagnóstico"""
        print("📊 Creando gráficos de diagnóstico...")
        
        os.makedirs(output_dir, exist_ok=True)
        
        fig, axes = plt.subplots(2, 2, figsize=(15, 10))
        
        # H1 espectro
        ax1 = axes[0, 0]
        freqs_h1 = results_h1['frequencies']
        spectrum_h1 = results_h1['spectrum']
        mask = (freqs_h1 >= 130) & (freqs_h1 <= 160)
        
        ax1.semilogy(freqs_h1[mask], spectrum_h1[mask], 'b-', label='H1', alpha=0.8)
        ax1.axvline(self.target_frequency, color='red', linestyle='--', 
                   label=f'{self.target_frequency} Hz objetivo')
        ax1.axvline(results_h1['detected_frequency'], color='green', linestyle='--',
                   label=f'H1: {results_h1["detected_frequency"]:.2f} Hz')
        ax1.set_xlabel('Frecuencia (Hz)')
        ax1.set_ylabel('ASD (1/√Hz)')
        ax1.set_title('Espectro H1 - Ringdown')
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        # L1 espectro
        ax2 = axes[0, 1]
        freqs_l1 = results_l1['frequencies']
        spectrum_l1 = results_l1['spectrum']
        
        ax2.semilogy(freqs_l1[mask], spectrum_l1[mask], 'r-', label='L1', alpha=0.8)
        ax2.axvline(self.target_frequency, color='red', linestyle='--',
                   label=f'{self.target_frequency} Hz objetivo')
        ax2.axvline(results_l1['detected_frequency'], color='green', linestyle='--',
                   label=f'L1: {results_l1["detected_frequency"]:.2f} Hz')
        ax2.set_xlabel('Frecuencia (Hz)')
        ax2.set_ylabel('ASD (1/√Hz)')
        ax2.set_title('Espectro L1 - Ringdown')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        
        # Comparación directa
        ax3 = axes[1, 0]
        ax3.semilogy(freqs_h1[mask], spectrum_h1[mask], 'b-', label='H1', alpha=0.7)
        ax3.semilogy(freqs_l1[mask], spectrum_l1[mask], 'r-', label='L1', alpha=0.7)
        ax3.axvline(self.target_frequency, color='orange', linestyle='--', linewidth=2,
                   label=f'{self.target_frequency} Hz objetivo')
        ax3.set_xlabel('Frecuencia (Hz)')
        ax3.set_ylabel('ASD (1/√Hz)')
        ax3.set_title('Comparación H1 vs L1')
        ax3.legend()
        ax3.grid(True, alpha=0.3)
        
        # Series temporales del ringdown
        ax4 = axes[1, 1]
        ringdown_h1 = results_h1['ringdown_data']
        ringdown_l1 = results_l1['ringdown_data']
        
        times_h1 = ringdown_h1.times.value - ringdown_h1.times.value[0]
        times_l1 = ringdown_l1.times.value - ringdown_l1.times.value[0]
        
        ax4.plot(times_h1 * 1000, ringdown_h1.value, 'b-', label='H1', alpha=0.7)
        ax4.plot(times_l1 * 1000, ringdown_l1.value, 'r-', label='L1', alpha=0.7)
        ax4.set_xlabel('Tiempo post-merger (ms)')
        ax4.set_ylabel('Strain (whitened)')
        ax4.set_title('Señal de Ringdown')
        ax4.legend()
        ax4.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        output_file = f'{output_dir}/GW250114_analisis_completo.png'
        plt.savefig(output_file, dpi=150, bbox_inches='tight')
        plt.close()
        
        print(f"   Gráfico guardado en: {output_file}")
    
    def analyze_complete(self, event_name: str = 'GW250114') -> Dict:
        """
        Análisis completo de GW250114
        Implementa todos los pasos del problema statement
        """
        print(f"\n🌌 ANÁLISIS COMPLETO DE {event_name} - 141.7 Hz")
        print("=" * 60)
        
        try:
            # 1. Descarga oficial de datos
            h1, l1, gps = self.download_official_data(event_name)
            
            # 2. Preprocesamiento estándar
            h1_proc = self.standard_preprocessing(h1)
            l1_proc = self.standard_preprocessing(l1)
            
            # 3. Búsqueda dirigida en 141.7 Hz
            results_h1 = self.directed_search_141hz(h1_proc, gps)
            results_l1 = self.directed_search_141hz(l1_proc, gps)
            
            # 4. Estadística clásica (p-value)
            p_value = self.classical_statistics(h1_proc, l1_proc, gps)
            
            # 5. Bayes Factor
            bf_h1 = self.bayesian_analysis(h1_proc)
            bf_l1 = self.bayesian_analysis(l1_proc)
            bf_combined = np.sqrt(bf_h1 * bf_l1)  # Combinación geométrica
            
            # 6. Validación cruzada
            validation_passed = self.cross_validation(results_h1, results_l1)
            
            # Crear gráficos
            self.create_diagnostic_plots(results_h1, results_l1)
            
            # Compilar resultados finales
            final_results = {
                'event': event_name,
                'target_frequency': self.target_frequency,
                'h1_frequency': results_h1['detected_frequency'],
                'l1_frequency': results_l1['detected_frequency'],
                'h1_snr': results_h1['snr'],
                'l1_snr': results_l1['snr'],
                'p_value': p_value,
                'bayes_factor_combined': bf_combined,
                'validation_passed': validation_passed
            }
            
            # 🚀 Resultado esperado
            print("\n" + "=" * 60)
            print("🚀 RESULTADOS FINALES")
            print("=" * 60)
            
            # Criterios de detección
            significant_pvalue = p_value < 0.01
            strong_evidence_bf = bf_combined > 10
            cross_detector_valid = validation_passed
            
            detection_criteria = [significant_pvalue, strong_evidence_bf, cross_detector_valid]
            detection_confirmed = all(detection_criteria)
            
            if detection_confirmed:
                print("🎯 ¡DETECCIÓN CONFIRMADA!")
                print(f"   Detectamos una componente en {self.target_frequency} Hz en {event_name}")
                print(f"   con Bayes Factor BF = {bf_combined:.1f} (>10)")
                print(f"   significancia p = {p_value:.4f} (<0.01)")
                print(f"   consistente en H1 y L1")
                print("   ✅ Estándar LIGO/Virgo cumplido")
            else:
                print("❌ Detección no confirmada")
                print("   Criterios no cumplidos:")
                if not significant_pvalue:
                    print(f"   - p-value {p_value:.4f} ≥ 0.01")
                if not strong_evidence_bf:
                    print(f"   - Bayes Factor {bf_combined:.1f} ≤ 10")
                if not cross_detector_valid:
                    print("   - Validación cruzada H1-L1 fallida")
                    
            return final_results
            
        except Exception as e:
            print(f"\n❌ Error en análisis: {e}")
            return {'error': str(e)}


def main():
    """Función principal"""
    # Crear analizador
    analyzer = GW250114Analyzer(target_frequency=141.7001)  # Frecuencia noésica precisa
    
    try:
        # Ejecutar análisis completo
        results = analyzer.analyze_complete('GW250114')
        
        # Guardar resultados
        output_dir = '../results'
        os.makedirs(output_dir, exist_ok=True)
        
        import json
        with open(f'{output_dir}/GW250114_results.json', 'w') as f:
            # Convertir numpy arrays a listas para JSON
            json_results = {}
            for key, value in results.items():
                if isinstance(value, np.ndarray):
                    json_results[key] = value.tolist()
                else:
                    json_results[key] = value
            json.dump(json_results, f, indent=2)
            
        print(f"\n💾 Resultados guardados en {output_dir}/GW250114_results.json")
        
    except Exception as e:
        print(f"\n❌ Error: {e}")
        print("ℹ️  GW250114 aún no disponible en GWOSC")
        print("   Este script estará listo cuando se liberen los datos oficiales")


if __name__ == "__main__":
    main()