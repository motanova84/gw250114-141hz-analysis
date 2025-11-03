#!/usr/bin/env python3
"""
Sistema de verificación en tiempo real para GW250114
Verifica la disponibilidad y analiza el evento GW250114 automáticamente cuando esté disponible.
"""
import sys
import os
import time
import json
from datetime import datetime
import numpy as np
from gwpy.timeseries import TimeSeries
from gwpy.time import to_gps

# Importar funciones de validación existentes
try:
    from validar_gw150914 import (
        preprocess_data, extract_ringdown, calculate_bayes_factor, 
        estimate_p_value_timeslides, damped_sine_model
    )
except ImportError:
    print("⚠️  No se pudieron importar funciones de validación")
    sys.exit(1)


class VerificadorGW250114:
    """Verificador en tiempo real para evento GW250114"""
    
    def __init__(self, check_interval=3600):
        """
        Inicializar verificador
        
        Args:
            check_interval: Intervalo de verificación en segundos (default: 1 hora)
        """
        self.check_interval = check_interval
        self.target_frequency = 141.7001  # Hz
        self.event_name = "GW250114"
        self.results_dir = "../resultados"
        
        # Crear directorio de resultados si no existe
        os.makedirs(self.results_dir, exist_ok=True)
        
    def verificar_disponibilidad(self):
        """
        Verificar si GW250114 está disponible en GWOSC
        
        Returns:
            tuple: (disponible, gps_time, mensaje)
        """
        print(f"🔍 Verificando disponibilidad de {self.event_name}...")
        
        # Eventos conocidos para verificar conectividad
        eventos_conocidos = {
            'GW150914': 1126259462.423,
            'GW151226': 1135136350.6,
            'GW170104': 1167559936.6
        }
        
        try:
            # Verificar conectividad con evento conocido
            test_gps = eventos_conocidos['GW150914']
            test_data = TimeSeries.fetch_open_data('H1', test_gps-1, test_gps+1, verbose=False)
            print("   ✅ Conectividad GWOSC verificada")
            
            # Intentar buscar GW250114
            # Fecha estimada: 2025-01-14
            gw250114_date = datetime(2025, 1, 14, 0, 0, 0)
            gw250114_gps = to_gps(gw250114_date)
            
            try:
                # Intentar acceder a datos de GW250114
                data = TimeSeries.fetch_open_data('H1', gw250114_gps, gw250114_gps+1, verbose=False)
                print(f"   ✅ {self.event_name} disponible en GWOSC!")
                return True, gw250114_gps, "Evento disponible"
            except Exception:
                print(f"   ℹ️  {self.event_name} aún no disponible en GWOSC")
                return False, gw250114_gps, "Evento no disponible aún"
                
        except Exception as e:
            print(f"   ❌ Error verificando disponibilidad: {e}")
            return False, None, str(e)
    
    def analizar_evento(self, gps_time):
        """
        Analizar GW250114 cuando esté disponible
        
        Args:
            gps_time: Tiempo GPS del evento
            
        Returns:
            dict: Resultados del análisis
        """
        print(f"\n📊 Analizando {self.event_name}...")
        
        resultados = {
            'evento': self.event_name,
            'gps_time': gps_time,
            'timestamp': datetime.now().isoformat(),
            'frecuencia_objetivo': self.target_frequency,
            'detectores': {}
        }
        
        try:
            # Descargar datos de ambos detectores
            start = gps_time - 16
            end = gps_time + 16
            
            print(f"   Descargando datos H1...")
            h1_data = TimeSeries.fetch_open_data('H1', start, end, sample_rate=4096)
            
            print(f"   Descargando datos L1...")
            l1_data = TimeSeries.fetch_open_data('L1', start, end, sample_rate=4096)
            
            # Analizar cada detector
            for detector, data in [('H1', h1_data), ('L1', l1_data)]:
                print(f"\n   Procesando {detector}...")
                
                # Preprocesar datos
                data_proc = preprocess_data(data)
                
                # Extraer ringdown
                ringdown = extract_ringdown(data_proc, gps_time)
                
                # Análisis espectral
                freqs, psd = self._calcular_espectro(ringdown)
                
                # Buscar componente en 141.7 Hz
                idx_target = np.argmin(np.abs(freqs - self.target_frequency))
                power_target = psd[idx_target]
                
                # Calcular SNR
                snr = self._calcular_snr(freqs, psd, self.target_frequency)
                
                # Calcular Bayes Factor
                bf = calculate_bayes_factor(ringdown, self.target_frequency)
                
                resultados['detectores'][detector] = {
                    'frecuencia_pico': float(freqs[np.argmax(psd)]),
                    'power_141hz': float(power_target),
                    'snr': float(snr),
                    'bayes_factor': float(bf),
                    'significancia': self._evaluar_significancia(snr, bf)
                }
                
                print(f"      Frecuencia pico: {freqs[np.argmax(psd)]:.4f} Hz")
                print(f"      SNR @ 141.7 Hz: {snr:.2f}")
                print(f"      Bayes Factor: {bf:.2e}")
            
            # Evaluación combinada
            resultados['evaluacion_combinada'] = self._evaluar_combinado(resultados['detectores'])
            
            # Guardar resultados
            self._guardar_resultados(resultados)
            
            return resultados
            
        except Exception as e:
            print(f"   ❌ Error analizando evento: {e}")
            resultados['error'] = str(e)
            return resultados
    
    def _calcular_espectro(self, data):
        """Calcular espectro de potencia"""
        from scipy import signal
        
        freqs, psd = signal.welch(
            data.value,
            fs=data.sample_rate.value,
            nperseg=min(len(data), 2048),
            window='hann'
        )
        
        return freqs, psd
    
    def _calcular_snr(self, freqs, psd, freq_target, bandwidth=1.0):
        """Calcular SNR en banda de frecuencia"""
        # Banda de señal
        mask_signal = (freqs >= freq_target - bandwidth/2) & (freqs <= freq_target + bandwidth/2)
        signal_power = np.mean(psd[mask_signal])
        
        # Banda de ruido (excluyendo señal)
        mask_noise = ((freqs >= freq_target - 10) & (freqs < freq_target - bandwidth)) | \
                     ((freqs > freq_target + bandwidth) & (freqs <= freq_target + 10))
        noise_power = np.mean(psd[mask_noise])
        
        if noise_power > 0:
            snr = signal_power / noise_power
        else:
            snr = 0.0
            
        return snr
    
    def _evaluar_significancia(self, snr, bayes_factor):
        """Evaluar significancia estadística"""
        if snr > 3.0 and bayes_factor > 10:
            return "ALTA"
        elif snr > 2.0 and bayes_factor > 3:
            return "MODERADA"
        elif snr > 1.5:
            return "BAJA"
        else:
            return "NO_SIGNIFICATIVA"
    
    def _evaluar_combinado(self, detectores):
        """Evaluación combinada de múltiples detectores"""
        if len(detectores) < 2:
            return {"status": "INSUFICIENTE", "mensaje": "Se requieren al menos 2 detectores"}
        
        # Verificar coherencia entre detectores
        significancias = [d['significancia'] for d in detectores.values()]
        snrs = [d['snr'] for d in detectores.values()]
        
        coherente = all(s in ['ALTA', 'MODERADA'] for s in significancias)
        snr_medio = np.mean(snrs)
        
        if coherente and snr_medio > 2.5:
            status = "DETECCION_CONFIRMADA"
        elif snr_medio > 2.0:
            status = "DETECCION_PROBABLE"
        else:
            status = "NO_DETECTADO"
        
        return {
            "status": status,
            "snr_medio": float(snr_medio),
            "coherencia": coherente,
            "detectores_activos": list(detectores.keys())
        }
    
    def _guardar_resultados(self, resultados):
        """Guardar resultados en formato JSON"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"{self.results_dir}/verificacion_gw250114_{timestamp}.json"
        
        with open(filename, 'w') as f:
            json.dump(resultados, f, indent=2)
        
        print(f"\n💾 Resultados guardados en: {filename}")
    
    def monitorear(self, max_checks=None):
        """
        Monitorear continuamente la disponibilidad de GW250114
        
        Args:
            max_checks: Número máximo de verificaciones (None = infinito)
        """
        print(f"🚀 Iniciando monitoreo de {self.event_name}")
        print(f"   Intervalo de verificación: {self.check_interval} segundos")
        
        check_count = 0
        
        while True:
            check_count += 1
            
            if max_checks and check_count > max_checks:
                print(f"\n✅ Monitoreo completado ({max_checks} verificaciones)")
                break
            
            print(f"\n🔄 Verificación #{check_count} - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            
            disponible, gps_time, mensaje = self.verificar_disponibilidad()
            
            if disponible:
                print(f"\n🎯 {self.event_name} DISPONIBLE!")
                resultados = self.analizar_evento(gps_time)
                
                # Mostrar resumen
                if 'evaluacion_combinada' in resultados:
                    eval_comb = resultados['evaluacion_combinada']
                    print(f"\n📋 RESUMEN:")
                    print(f"   Status: {eval_comb['status']}")
                    print(f"   SNR medio: {eval_comb['snr_medio']:.2f}")
                    print(f"   Coherencia: {eval_comb['coherencia']}")
                
                break
            else:
                print(f"   {mensaje}")
                
                if max_checks and check_count < max_checks:
                    print(f"   ⏳ Próxima verificación en {self.check_interval} segundos...")
                    time.sleep(self.check_interval)
                elif not max_checks:
                    print(f"   ⏳ Próxima verificación en {self.check_interval} segundos...")
                    time.sleep(self.check_interval)


def main():
    """Función principal"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Verificador en tiempo real para GW250114'
    )
    parser.add_argument(
        '--interval',
        type=int,
        default=3600,
        help='Intervalo de verificación en segundos (default: 3600)'
    )
    parser.add_argument(
        '--max-checks',
        type=int,
        default=None,
        help='Número máximo de verificaciones (default: infinito)'
    )
    parser.add_argument(
        '--once',
        action='store_true',
        help='Verificar solo una vez'
    )
    
    args = parser.parse_args()
    
    # Crear verificador
    verificador = VerificadorGW250114(check_interval=args.interval)
    
    if args.once:
        # Verificación única
        disponible, gps_time, mensaje = verificador.verificar_disponibilidad()
        if disponible:
            resultados = verificador.analizar_evento(gps_time)
        else:
            print(f"   {mensaje}")
    else:
        # Monitoreo continuo
        verificador.monitorear(max_checks=args.max_checks)


if __name__ == "__main__":
    main()
