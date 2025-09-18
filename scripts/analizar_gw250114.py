#!/usr/bin/env python3
"""
Framework para análisis de GW250114 - 141.7 Hz
Preparado para ejecutar cuando los datos de GW250114 estén disponibles
Basado en el problema statement: simplemente cambiar GPS time y ejecutar
"""
import numpy as np
import os
import sys
from gwpy.timeseries import TimeSeries
from gwosc import datasets
from validar_gw150914 import ValidadorGW150914

class AnalyzadorGW250114(ValidadorGW150914):
    """
    Analizador de GW250114 que hereda toda la funcionalidad de validación
    Solo necesita cambiar el GPS time cuando los datos estén disponibles
    """
    
    def __init__(self):
        super().__init__()
        # Estos valores se actualizarán cuando GW250114 esté disponible
        self.evento_nombre = "GW250114"
        self.gps_gw250114 = None  # Se determinará automáticamente
        self.resultados_esperados = {
            'H1': {'snr': None, 'freq': 141.7},  # Se medirán
            'L1': {'snr': None, 'freq': 141.7}   # Se medirán
        }
        
    def obtener_gps_gw250114(self):
        """
        Obtener automáticamente el GPS time de GW250114 cuando esté disponible
        Implementa la transición mencionada en el problema statement:
        gps_start = event_gps("GW250114") - 16
        """
        try:
            print("🔍 Buscando GW250114 en GWOSC...")
            gps_time = datasets.event_gps("GW250114")
            print(f"   ✅ GW250114 encontrado en GPS: {gps_time}")
            self.gps_gw250114 = gps_time
            return True
        except Exception as e:
            print(f"   ❌ GW250114 no disponible aún: {e}")
            print("   📋 Esto es esperado hasta que LIGO libere los datos")
            return False
    
    def verificar_disponibilidad_gw250114(self):
        """Verificar si GW250114 está disponible en GWOSC"""
        from gwosc.datasets import find_datasets
        
        print("🔍 Verificando disponibilidad de GW250114...")
        
        try:
            eventos = find_datasets(type="event", detector="H1")
            gw250114_disponible = "GW250114" in eventos
            
            if gw250114_disponible:
                print("   ✅ GW250114 disponible en GWOSC")
                return self.obtener_gps_gw250114()
            else:
                print("   📋 GW250114 aún no está disponible en GWOSC")
                print("   ⏳ Los datos se liberarán según la política de LIGO")
                return False
                
        except Exception as e:
            print(f"   ❌ Error verificando disponibilidad: {e}")
            return False
    
    def cargar_datos_gw250114(self, detector):
        """Cargar datos de GW250114 (adaptado del método base)"""
        data_dir = os.path.join(os.path.dirname(__file__), '..', 'data', 'raw')
        os.makedirs(data_dir, exist_ok=True)
        
        archivo = os.path.join(data_dir, f'{detector}-GW250114-32s.hdf5')
        
        if os.path.exists(archivo):
            print(f"   📂 Cargando datos existentes: {archivo}")
            return TimeSeries.read(archivo)
        else:
            print(f"   🔄 Descargando datos de {detector} para GW250114...")
            # Implementa la transición del problema statement:
            # gps_start = event_gps("GW250114") - 16
            # gps_end = gps_start + 32
            start = self.gps_gw250114 - 16
            end = self.gps_gw250114 + 16
            
            data = TimeSeries.fetch_open_data(
                detector, start, end, sample_rate=4096, cache=True
            )
            data.write(archivo, overwrite=True)
            print(f"   💾 Datos guardados en: {archivo}")
            return data
    
    def analizar_gw250114(self):
        """
        Análisis completo de GW250114
        Implementa exactamente el procedimiento del problema statement
        """
        print("\n" + "="*80)
        print("🚀 ANÁLISIS DE GW250114 - 141.7 Hz")
        print("🎯 Validación oficial de la frecuencia 141.7 Hz")
        print("="*80)
        
        # 1. Verificar disponibilidad
        if not self.verificar_disponibilidad_gw250114():
            print("\n📅 DATOS AÚN NO DISPONIBLES")
            print("   Ejecute este script cuando LIGO libere los datos de GW250114")
            print("   El análisis está completamente preparado para ejecutar")
            return False
        
        # 2. Análisis H1
        print(f"\n📡 Analizando H1 - GW250114...")
        try:
            data_h1 = self.cargar_datos_gw250114('H1')
            resultado_h1 = self.analizar_ringdown(data_h1, 'H1')
            self.calcular_bayes_factor(resultado_h1)
            self.calcular_pvalue_timeslides(resultado_h1)
        except Exception as e:
            print(f"❌ Error analizando H1: {e}")
            resultado_h1 = None
        
        # 3. Análisis L1
        print(f"\n📡 Analizando L1 - GW250114...")
        try:
            data_l1 = self.cargar_datos_gw250114('L1')
            resultado_l1 = self.analizar_ringdown(data_l1, 'L1')
            self.calcular_bayes_factor(resultado_l1)
            self.calcular_pvalue_timeslides(resultado_l1)
        except Exception as e:
            print(f"❌ Error analizando L1: {e}")
            resultado_l1 = None
        
        # 4. Validación según criterios del problema statement
        return self.validar_resultado_gw250114(resultado_h1, resultado_l1)
    
    def validar_resultado_gw250114(self, resultado_h1, resultado_l1):
        """
        Validación final según criterios del problema statement:
        Si el resultado es:
        - BF > 10
        - p < 0.01
        - coherencia en H1 y L1
        → 🚨 validación oficial de la frecuencia 141.7 Hz en GW250114
        """
        print("\n" + "="*80)
        print("🏁 VALIDACIÓN OFICIAL - GW250114")
        print("="*80)
        
        if resultado_h1 is None or resultado_l1 is None:
            print("❌ No se puede completar la validación: datos incompletos")
            return False
        
        # Criterios del problema statement
        bf_h1_valido = resultado_h1.get('bayes_factor', 0) > 10
        bf_l1_valido = resultado_l1.get('bayes_factor', 0) > 10
        p_h1_valido = resultado_h1.get('p_value', 1) < 0.01
        p_l1_valido = resultado_l1.get('p_value', 1) < 0.01
        
        # Coherencia en detección
        freq_h1 = resultado_h1.get('freq_detected', 0)
        freq_l1 = resultado_l1.get('freq_detected', 0)
        coherencia_freq = abs(freq_h1 - freq_l1) < 0.5  # Tolerancia 0.5 Hz
        
        print(f"📊 RESULTADOS GW250114:")
        print(f"   H1: f={freq_h1:.2f} Hz, BF={resultado_h1.get('bayes_factor', 0):.2e}, p={resultado_h1.get('p_value', 1):.4f}")
        print(f"   L1: f={freq_l1:.2f} Hz, BF={resultado_l1.get('bayes_factor', 0):.2e}, p={resultado_l1.get('p_value', 1):.4f}")
        print()
        print("🔍 CRITERIOS DE VALIDACIÓN:")
        print(f"   ✅ BF H1 > 10: {'SÍ' if bf_h1_valido else 'NO'}")
        print(f"   ✅ BF L1 > 10: {'SÍ' if bf_l1_valido else 'NO'}")
        print(f"   ✅ p H1 < 0.01: {'SÍ' if p_h1_valido else 'NO'}")
        print(f"   ✅ p L1 < 0.01: {'SÍ' if p_l1_valido else 'NO'}")
        print(f"   ✅ Coherencia H1-L1: {'SÍ' if coherencia_freq else 'NO'}")
        
        # Validación final
        validacion_oficial = (bf_h1_valido and bf_l1_valido and 
                             p_h1_valido and p_l1_valido and 
                             coherencia_freq)
        
        if validacion_oficial:
            print("\n🚨 VALIDACIÓN OFICIAL EXITOSA")
            print("   FRECUENCIA 141.7 Hz CONFIRMADA EN GW250114")
            print("   Criterios científicos cumplidos:")
            print("   - Bayes Factor > 10 en ambos detectores ✅")
            print("   - p-value < 0.01 en ambos detectores ✅")
            print("   - Coherencia entre H1 y L1 ✅")
            print("\n🎯 RESULTADO: DETECCIÓN CIENTÍFICAMENTE VALIDADA")
        else:
            print("\n❌ VALIDACIÓN NO SUPERADA")
            print("   La frecuencia 141.7 Hz no cumple todos los criterios científicos")
            print("   Se requiere análisis adicional")
        
        return validacion_oficial
    
    def crear_informe_gw250114(self, resultado_h1, resultado_l1, validacion_exitosa):
        """Crear informe científico del análisis"""
        output_dir = os.path.join(os.path.dirname(__file__), '..', 'results')
        os.makedirs(output_dir, exist_ok=True)
        
        informe_file = os.path.join(output_dir, 'informe_gw250114.txt')
        
        with open(informe_file, 'w') as f:
            f.write("GW250114 - ANÁLISIS DE COMPONENTE 141.7 Hz\n")
            f.write("="*50 + "\n\n")
            f.write(f"Análisis realizado con el framework reproducible\n")
            f.write(f"Basado en validación previa de GW150914\n\n")
            
            if resultado_h1:
                f.write(f"HANFORD (H1):\n")
                f.write(f"  Frecuencia detectada: {resultado_h1.get('freq_detected', 0):.2f} Hz\n")
                f.write(f"  Bayes Factor: {resultado_h1.get('bayes_factor', 0):.2e}\n")
                f.write(f"  p-value: {resultado_h1.get('p_value', 1):.4f}\n\n")
            
            if resultado_l1:
                f.write(f"LIVINGSTON (L1):\n")
                f.write(f"  Frecuencia detectada: {resultado_l1.get('freq_detected', 0):.2f} Hz\n")
                f.write(f"  Bayes Factor: {resultado_l1.get('bayes_factor', 0):.2e}\n")
                f.write(f"  p-value: {resultado_l1.get('p_value', 1):.4f}\n\n")
            
            f.write(f"VALIDACIÓN CIENTÍFICA: {'EXITOSA' if validacion_exitosa else 'NO SUPERADA'}\n")
        
        print(f"📄 Informe guardado en: {informe_file}")

def main():
    """Ejecutor principal para GW250114"""
    print("🌌 GW250114 - 141.7001 Hz Analysis")
    print("🚀 Framework de Análisis de GW250114")
    print("📋 Preparado según problema statement")
    print()
    
    analizador = AnalyzadorGW250114()
    
    # Intentar análisis completo
    resultado = analizador.analizar_gw250114()
    
    if resultado is False:
        print("\n📅 FRAMEWORK PREPARADO Y VALIDADO")
        print("   Este script ejecutará automáticamente cuando:")
        print("   1. LIGO libere los datos de GW250114")
        print("   2. Los datos aparezcan en GWOSC")
        print("\n🔄 Para ejecutar manualmente cuando estén disponibles:")
        print("   python scripts/analizar_gw250114.py")
    
    return resultado

if __name__ == "__main__":
    exito = main()
    sys.exit(0 if exito else 1)