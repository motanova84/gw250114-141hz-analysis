#!/usr/bin/env python3
"""
Test script para verificar la funcionalidad de VerificadorGW250114
Ejecuta el código del problema statement para validar la implementación.
"""
import sys
import os
from datetime import datetime

# Asegurar que podemos importar desde scripts
sys.path.insert(0, os.path.dirname(__file__))

from analizar_gw250114 import VerificadorGW250114

def test_online_mode():
    """Prueba en modo online (intenta conectarse a GWOSC)"""
    print("=" * 70)
    print("🎯 RESULTADO DE LA VERIFICACIÓN ACTUAL")
    print("=" * 70)
    print("Ejecutando verificación inmediata...\n")
    
    # EJECUTAR ESTO PARA VER EL ESTADO ACTUAL
    verificador = VerificadorGW250114()
    estado_actual = verificador.verificar_disponibilidad_evento()
    
    print(f"\n📅 FECHA ACTUAL: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"🎯 ESTADO GW250114: {verificador.estado_actual}")
    
    if verificador.estado_actual == "NO_DISPONIBLE":
        print("\n🔍 BUSCANDO EVENTOS SIMILARES DISPONIBLES...")
        verificador.verificar_eventos_similares()
    
    print("\n" + "=" * 70)
    print("✅ Verificación completada")
    print("=" * 70)
    
    return verificador

def test_offline_mode():
    """Prueba en modo offline (sin conectarse a GWOSC)"""
    print("\n\n")
    print("=" * 70)
    print("🎯 MODO OFFLINE - DEMOSTRACIÓN")
    print("=" * 70)
    print("Ejecutando verificación sin conectividad a GWOSC...\n")
    
    verificador = VerificadorGW250114()
    estado_actual = verificador.verificar_disponibilidad_evento(offline_mode=True)
    
    print(f"\n📅 FECHA ACTUAL: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"🎯 ESTADO GW250114: {verificador.estado_actual}")
    
    if verificador.estado_actual == "NO_DISPONIBLE":
        print("\n🔍 BUSCANDO EVENTOS SIMILARES DISPONIBLES...")
        eventos = verificador.verificar_eventos_similares(offline_mode=True)
    
    print("\n" + "=" * 70)
    print("✅ Verificación offline completada")
    print("=" * 70)
    
    return verificador

def main():
    """Ejecutar verificación según problema statement"""
    # Primero intentar modo online
    print("🌐 Intentando verificación ONLINE...")
    verificador_online = test_online_mode()
    
    # Si falla la conectividad, mostrar también modo offline
    if verificador_online.estado_actual == "NO_DISPONIBLE":
        print("\n💡 También ejecutando demostración en MODO OFFLINE...")
        verificador_offline = test_offline_mode()
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
