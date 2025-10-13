#!/usr/bin/env python3
"""
Validación Estadística Completa
Tests estadísticos rigurosos para validar detección de 141.7001 Hz
"""
import numpy as np
from scipy import stats, signal
import warnings
warnings.filterwarnings('ignore')

class ValidacionEstadisticaCompleta:
    def __init__(self):
        self.resultados = {}
        
    def test_significancia_estadistica(self, datos, frecuencia_objetivo=141.7001, fs=4096):
        """Test de significancia estadística usando distribución de background"""
        print("📊 TEST DE SIGNIFICANCIA ESTADÍSTICA")
        
        # Calcular espectro
        freqs, psd = signal.welch(datos, fs, nperseg=min(len(datos)//4, 2048))
        
        # Encontrar potencia en frecuencia objetivo
        idx_target = np.argmin(np.abs(freqs - frecuencia_objetivo))
        potencia_target = psd[idx_target]
        
        # Estimar distribución de background
        banda_inicio = max(0, idx_target - 100)
        banda_fin = min(len(freqs), idx_target + 100)
        background = np.concatenate([psd[banda_inicio:idx_target-10], 
                                     psd[idx_target+10:banda_fin]])
        
        # Calcular p-value
        background_mean = np.mean(background)
        background_std = np.std(background)
        
        if background_std > 0:
            z_score = (potencia_target - background_mean) / background_std
            p_value = 1 - stats.norm.cdf(z_score)
        else:
            z_score = 0
            p_value = 1.0
        
        resultado = {
            'p_value': float(p_value),
            'z_score': float(z_score),
            'potencia_target': float(potencia_target),
            'background_mean': float(background_mean),
            'background_std': float(background_std),
            'significativo': p_value < 0.01
        }
        
        print(f"   • p-value: {resultado['p_value']:.6f}")
        print(f"   • z-score: {resultado['z_score']:.2f}")
        print(f"   • Significativo (p < 0.01): {'✅ SÍ' if resultado['significativo'] else '❌ NO'}")
        
        self.resultados['test_significancia'] = resultado
        return resultado
    
    def calcular_bayes_factor_simplificado(self, datos, frecuencia_objetivo=141.7001, fs=4096):
        """Cálculo simplificado de Bayes Factor"""
        print("🧮 CÁLCULO DE BAYES FACTOR")
        
        # Análisis espectral
        freqs, psd = signal.welch(datos, fs, nperseg=min(len(datos)//4, 2048))
        
        # Modelo 1: Sin frecuencia objetivo (H0)
        idx_target = np.argmin(np.abs(freqs - frecuencia_objetivo))
        banda_inicio = max(0, idx_target - 50)
        banda_fin = min(len(freqs), idx_target + 50)
        
        # Excluir frecuencia objetivo
        background_indices = np.concatenate([
            np.arange(banda_inicio, idx_target - 5),
            np.arange(idx_target + 5, banda_fin)
        ])
        
        background = psd[background_indices]
        chi2_h0 = np.sum((background - np.mean(background))**2) / np.var(background)
        
        # Modelo 2: Con frecuencia objetivo (H1)
        full_band = psd[banda_inicio:banda_fin]
        chi2_h1 = np.sum((full_band - np.mean(full_band))**2) / np.var(full_band)
        
        # Bayes Factor aproximado
        delta_chi2 = chi2_h0 - chi2_h1
        bayes_factor = np.exp(0.5 * delta_chi2)
        
        # Limitar valores extremos
        bayes_factor = np.clip(bayes_factor, 0.1, 1000)
        
        resultado = {
            'bayes_factor': float(bayes_factor),
            'chi2_h0': float(chi2_h0),
            'chi2_h1': float(chi2_h1),
            'delta_chi2': float(delta_chi2),
            'evidencia_fuerte': bayes_factor > 10
        }
        
        print(f"   • Bayes Factor: {resultado['bayes_factor']:.2f}")
        print(f"   • Evidencia fuerte (BF > 10): {'✅ SÍ' if resultado['evidencia_fuerte'] else '❌ NO'}")
        
        self.resultados['bayes_factor'] = resultado
        return resultado
    
    def test_coherencia_multi_detector(self, datos_h1, datos_l1, fs=4096):
        """Test de coherencia entre detectores"""
        print("🔗 TEST DE COHERENCIA MULTI-DETECTOR")
        
        # Calcular espectros
        freqs1, psd1 = signal.welch(datos_h1, fs, nperseg=min(len(datos_h1)//4, 2048))
        freqs2, psd2 = signal.welch(datos_l1, fs, nperseg=min(len(datos_l1)//4, 2048))
        
        # Calcular coherencia
        f, Cxy = signal.coherence(datos_h1, datos_l1, fs, nperseg=min(len(datos_h1)//4, 2048))
        
        # Coherencia en frecuencia objetivo
        idx_target = np.argmin(np.abs(f - 141.7001))
        coherencia_target = Cxy[idx_target]
        
        # Coherencia promedio en banda
        banda_indices = np.where((f >= 130) & (f <= 160))[0]
        coherencia_banda = np.mean(Cxy[banda_indices])
        
        resultado = {
            'coherencia_target': float(coherencia_target),
            'coherencia_banda': float(coherencia_banda),
            'coherente': coherencia_target > 0.5
        }
        
        print(f"   • Coherencia en 141.7 Hz: {resultado['coherencia_target']:.3f}")
        print(f"   • Coherencia banda 130-160 Hz: {resultado['coherencia_banda']:.3f}")
        print(f"   • Señal coherente (> 0.5): {'✅ SÍ' if resultado['coherente'] else '❌ NO'}")
        
        self.resultados['coherencia'] = resultado
        return resultado
    
    def test_estacionariedad(self, datos, fs=4096):
        """Test de estacionariedad de la señal"""
        print("📉 TEST DE ESTACIONARIEDAD")
        
        # Dividir en segmentos
        n_segmentos = 4
        segmento_len = len(datos) // n_segmentos
        
        medias = []
        varianzas = []
        
        for i in range(n_segmentos):
            inicio = i * segmento_len
            fin = (i + 1) * segmento_len
            segmento = datos[inicio:fin]
            
            medias.append(np.mean(segmento))
            varianzas.append(np.var(segmento))
        
        # Test de Levene para homogeneidad de varianzas
        segmentos = [datos[i*segmento_len:(i+1)*segmento_len] for i in range(n_segmentos)]
        statistic, p_value = stats.levene(*segmentos)
        
        resultado = {
            'p_value_levene': float(p_value),
            'estacionaria': p_value > 0.05,
            'medias': [float(m) for m in medias],
            'varianzas': [float(v) for v in varianzas]
        }
        
        print(f"   • p-value (Levene): {resultado['p_value_levene']:.4f}")
        print(f"   • Señal estacionaria (p > 0.05): {'✅ SÍ' if resultado['estacionaria'] else '❌ NO'}")
        
        self.resultados['estacionariedad'] = resultado
        return resultado
    
    def ejecutar_validacion_completa(self, datos_h1=None, datos_l1=None, fs=4096):
        """Ejecuta todos los tests de validación"""
        print("🚀 VALIDACIÓN ESTADÍSTICA COMPLETA")
        print("=" * 70)
        
        # Generar datos sintéticos si no se proporcionan
        if datos_h1 is None or datos_l1 is None:
            print("\n🧪 Generando datos sintéticos para validación...")
            t = np.linspace(0, 2, fs*2)
            señal = 1e-21 * np.exp(-np.pi * 141.7001 * t / 8.5) * \
                    np.sin(2 * np.pi * 141.7001 * t)
            
            datos_h1 = señal + np.random.normal(0, 2e-22, len(t))
            datos_l1 = señal + np.random.normal(0, 2e-22, len(t))
        
        # Ejecutar tests
        print("\n1️⃣ Test de Significancia Estadística (H1)")
        self.test_significancia_estadistica(datos_h1, fs=fs)
        
        print("\n2️⃣ Cálculo de Bayes Factor (H1)")
        self.calcular_bayes_factor_simplificado(datos_h1, fs=fs)
        
        print("\n3️⃣ Test de Coherencia Multi-Detector")
        self.test_coherencia_multi_detector(datos_h1, datos_l1, fs=fs)
        
        print("\n4️⃣ Test de Estacionariedad (H1)")
        self.test_estacionariedad(datos_h1, fs=fs)
        
        # Resumen
        print("\n" + "=" * 70)
        print("📊 RESUMEN DE VALIDACIÓN ESTADÍSTICA")
        print("=" * 70)
        
        criterios_cumplidos = 0
        total_criterios = 4
        
        if self.resultados.get('test_significancia', {}).get('significativo'):
            print("✅ Significancia estadística (p < 0.01)")
            criterios_cumplidos += 1
        else:
            print("❌ Significancia estadística NO cumplida")
        
        if self.resultados.get('bayes_factor', {}).get('evidencia_fuerte'):
            print("✅ Bayes Factor (BF > 10)")
            criterios_cumplidos += 1
        else:
            print("❌ Bayes Factor NO cumplido")
        
        if self.resultados.get('coherencia', {}).get('coherente'):
            print("✅ Coherencia multi-detector")
            criterios_cumplidos += 1
        else:
            print("❌ Coherencia NO cumplida")
        
        if self.resultados.get('estacionariedad', {}).get('estacionaria'):
            print("✅ Estacionariedad")
            criterios_cumplidos += 1
        else:
            print("❌ Estacionariedad NO cumplida")
        
        print(f"\n📈 Criterios cumplidos: {criterios_cumplidos}/{total_criterios}")
        
        return self.resultados

# EJECUCIÓN INMEDIATA
if __name__ == "__main__":
    try:
        validador = ValidacionEstadisticaCompleta()
        resultados = validador.ejecutar_validacion_completa()
        
        print("\n✅ VALIDACIÓN ESTADÍSTICA COMPLETADA")
        
    except Exception as e:
        print(f"\n❌ Error en validación estadística: {e}")
        import traceback
        traceback.print_exc()
        exit(1)
