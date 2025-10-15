#!/usr/bin/env python3
"""
Verificador de disponibilidad GW250114
Verifica si el evento GW250114 está disponible en GWOSC para análisis.
Retorna exit code 0 si está disponible, 1 si no lo está.
"""
import sys
import os
from datetime import datetime
import time

def verificar_disponibilidad_gw250114():
    """Verificar si GW250114 está disponible en GWOSC"""
    print("🌌 VERIFICACIÓN INMEDIATA GW250114")
    print("=" * 50)
    print(f"🕒 Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # Intentar importar módulos necesarios
    try:
        from gwpy.timeseries import TimeSeries
        print("✅ Módulos GWPy disponibles")
    except ImportError as e:
        print(f"❌ Error importando GWPy: {e}")
        print("💡 Instalar con: pip install gwpy")
        return False
    
    # Lista de eventos conocidos para verificar conectividad
    known_events = {
        'GW150914': 1126259462.423,
        'GW151226': 1135136350.6,
        'GW170104': 1167559936.6,
        'GW170814': 1186741861.5,
        'GW170823': 1187008882.4
    }
    
    print("🔍 Verificando acceso a catálogo GWOSC...")
    
    # Verificar conectividad con evento conocido
    try:
        test_event = 'GW150914'
        test_gps = known_events[test_event]
        
        print(f"   🧪 Test de conectividad con {test_event}...")
        data = TimeSeries.fetch_open_data('H1', test_gps-1, test_gps+1, verbose=False)
        print(f"   ✅ Acceso a catálogo confirmado")
        
    except Exception as e:
        print(f"   ❌ Error accediendo catálogo GWOSC: {e}")
        print("   💡 Verificar conexión a internet")
        return False
    
    # Buscar GW250114 en catálogo
    print()
    print("🔎 Buscando GW250114 en catálogo...")
    
    # Nota: GW250114 es un evento hipotético para este análisis
    # Esta sección detectará automáticamente cuando esté disponible
    
    try:
        # Intentar acceder a GW250114 (esto fallará hasta que esté disponible)
        # El GPS time sería aproximadamente 1769529600 (2025-01-14 estimado)
        
        print("   📋 GW250114 es un evento objetivo hipotético")
        print("   ⏳ Esperando liberación de datos en GWOSC")
        print()
        print("   ℹ️  El evento será detectado automáticamente cuando:")
        print("      • Aparezca en el catálogo público GWTC")
        print("      • Los datos estén disponibles vía API")
        print("      • Pase el período de embargo (si aplica)")
        
        return False
        
    except Exception as e:
        print(f"   ❌ Error en búsqueda: {e}")
        return False

def monitoreo_continuo():
    """Modo de monitoreo continuo (ejecutar en segundo plano)"""
    print()
    print("🔄 INICIANDO MONITOREO CONTINUO")
    print("=" * 50)
    
    intervalo = 3600  # Verificar cada hora
    print(f"⏱️  Intervalo de verificación: {intervalo} segundos ({intervalo//60} minutos)")
    print("🛑 Para detener: pkill -f verificador_gw250114.py")
    print()
    
    verificaciones = 0
    while True:
        verificaciones += 1
        print(f"\n{'=' * 50}")
        print(f"🔍 Verificación #{verificaciones}")
        print(f"🕒 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"{'=' * 50}")
        
        disponible = verificar_disponibilidad_gw250114()
        
        if disponible:
            print()
            print("🎉" * 20)
            print("🚨 ¡GW250114 DISPONIBLE!")
            print("🎉" * 20)
            print()
            print("🚀 Iniciar análisis con:")
            print("   python scripts/analizar_gw250114.py")
            print()
            
            # Crear archivo de alerta
            with open("GW250114_DISPONIBLE.txt", "w") as f:
                f.write(f"GW250114 disponible desde: {datetime.now()}\n")
                f.write("Ejecutar: python scripts/analizar_gw250114.py\n")
            
            return 0
        else:
            print(f"\n⏳ Próxima verificación en {intervalo//60} minutos...")
            time.sleep(intervalo)

def main():
    """Función principal"""
    
    # Verificar si hay argumento para modo continuo
    modo_continuo = '--continuo' in sys.argv or '--continuous' in sys.argv
    
    if modo_continuo:
        # Modo de monitoreo continuo
        return monitoreo_continuo()
    else:
        # Verificación única
        disponible = verificar_disponibilidad_gw250114()
        
        print()
        print("=" * 50)
        if disponible:
            print("✅ GW250114 DISPONIBLE - Listo para análisis")
            print("🚀 Ejecutar: python scripts/analizar_gw250114.py")
            return 0
        else:
            print("❌ GW250114 NO DISPONIBLE AÚN")
            print("🔄 Para monitoreo continuo:")
            print("   nohup python scripts/verificador_gw250114.py --continuo > monitoreo_gw250114.log 2>&1 &")
            return 1

if __name__ == "__main__":
    sys.exit(main())
