#!/usr/bin/env python3
"""
Tests para el Sistema de Alertas Avanzado
Prueba todas las funcionalidades del sistema sin requerir credenciales reales
"""

import sys
import asyncio
import unittest
from pathlib import Path
from unittest.mock import Mock, patch, AsyncMock

# Agregar directorio de scripts al path
sys.path.insert(0, str(Path(__file__).parent))

from sistema_alertas_avanzado import SistemaAlertasAvanzado


class TestSistemaAlertasAvanzado(unittest.TestCase):
    """Tests para el sistema de alertas"""
    
    def setUp(self):
        """Configurar tests"""
        self.sistema = SistemaAlertasAvanzado()
    
    def test_inicializacion(self):
        """Test: Sistema se inicializa correctamente"""
        self.assertIsNotNone(self.sistema)
        self.assertIn('maxima', self.sistema.canales_prioridad)
        self.assertIn('alta', self.sistema.canales_prioridad)
        self.assertIn('media', self.sistema.canales_prioridad)
        self.assertIn('baja', self.sistema.canales_prioridad)
    
    def test_canales_por_prioridad(self):
        """Test: Canales correctos para cada prioridad"""
        # Prioridad máxima debe incluir todos los canales críticos
        canales_maxima = self.sistema.canales_prioridad['maxima']
        self.assertIn('sms', canales_maxima)
        self.assertIn('llamada', canales_maxima)
        self.assertIn('pushbullet', canales_maxima)
        self.assertIn('webhook_emergencia', canales_maxima)
        
        # Prioridad baja solo email
        canales_baja = self.sistema.canales_prioridad['baja']
        self.assertEqual(len(canales_baja), 1)
        self.assertIn('email', canales_baja)
    
    def test_configuracion_cargada(self):
        """Test: Configuración se carga correctamente"""
        self.assertIn('twilio', self.sistema.config)
        self.assertIn('pushbullet', self.sistema.config)
        self.assertIn('email', self.sistema.config)
        self.assertIn('webhooks', self.sistema.config)
    
    def test_registro_alertas(self):
        """Test: Registro de alertas funciona"""
        inicial = len(self.sistema.alertas_enviadas)
        self.sistema._registrar_alerta("Test mensaje", "alta", ["email"])
        self.assertEqual(len(self.sistema.alertas_enviadas), inicial + 1)
    
    def test_generar_reporte(self):
        """Test: Generación de reporte"""
        # Registrar algunas alertas
        self.sistema._registrar_alerta("Test 1", "maxima", ["sms"])
        self.sistema._registrar_alerta("Test 2", "alta", ["email"])
        self.sistema._registrar_alerta("Test 3", "media", ["webhook"])
        
        reporte = self.sistema.generar_reporte_alertas()
        
        self.assertIn('total_alertas', reporte)
        self.assertIn('alertas_por_prioridad', reporte)
        self.assertTrue(reporte['total_alertas'] >= 3)


class TestAlertasAsync(unittest.IsolatedAsyncioTestCase):
    """Tests asíncronos para el sistema de alertas"""
    
    async def asyncSetUp(self):
        """Configurar tests asíncronos"""
        self.sistema = SistemaAlertasAvanzado()
    
    async def test_enviar_email_prioridad(self):
        """Test: Envío de email"""
        resultado = await self.sistema.enviar_email_prioridad("Test mensaje", "alta")
        self.assertTrue(resultado)
    
    async def test_webhook_estandar(self):
        """Test: Webhook estándar con mock"""
        with patch('aiohttp.ClientSession') as mock_session:
            # Configurar mock
            mock_response = AsyncMock()
            mock_response.status = 200
            mock_response.__aenter__.return_value = mock_response
            mock_response.__aexit__.return_value = None
            
            mock_post = AsyncMock()
            mock_post.return_value = mock_response
            
            mock_session.return_value.__aenter__.return_value.post = mock_post
            mock_session.return_value.__aexit__.return_value = None
            
            resultado = await self.sistema.enviar_webhook_estandar(
                "Test mensaje",
                {"nombre": "GW250114"},
                {"snr": 15.2}
            )
            
            # En modo simulado, debe retornar resultado
            self.assertIsNotNone(resultado)
    
    async def test_alerta_validacion_psi(self):
        """Test: Alerta de validación PSI completa"""
        evento = {
            'nombre': 'GW250114',
            'detector': 'H1-L1'
        }
        
        resultados = {
            'frecuencia': 141.7001,
            'snr': 15.2,
            'p_value': 0.0001,
            'diferencia': 0.0000
        }
        
        # Esta prueba verifica que no haya errores de ejecución
        try:
            await self.sistema.alerta_validacion_psi(evento, resultados)
            success = True
        except Exception as e:
            print(f"Error en test: {e}")
            success = False
        
        self.assertTrue(success)


async def test_integracion_completa():
    """Test de integración completa del sistema"""
    print("\n" + "=" * 70)
    print("🧪 TEST DE INTEGRACIÓN COMPLETA")
    print("=" * 70)
    
    sistema = SistemaAlertasAvanzado()
    
    # Test 1: Alerta de prioridad baja
    print("\n1️⃣ Test: Alerta de prioridad BAJA")
    await sistema.enviar_alertas_multicanal(
        "Test alerta baja",
        'baja',
        {"nombre": "Test"},
        {"snr": 3.0}
    )
    
    # Test 2: Alerta de prioridad media
    print("\n2️⃣ Test: Alerta de prioridad MEDIA")
    await sistema.enviar_alertas_multicanal(
        "Test alerta media",
        'media',
        {"nombre": "Test"},
        {"snr": 7.0}
    )
    
    # Test 3: Alerta de prioridad alta
    print("\n3️⃣ Test: Alerta de prioridad ALTA")
    await sistema.enviar_alertas_multicanal(
        "Test alerta alta",
        'alta',
        {"nombre": "Test"},
        {"snr": 12.0}
    )
    
    # Test 4: Alerta de prioridad máxima
    print("\n4️⃣ Test: Alerta de prioridad MÁXIMA")
    evento = {
        'nombre': 'GW250114',
        'detector': 'H1-L1'
    }
    
    resultados = {
        'frecuencia': 141.7001,
        'snr': 15.2,
        'p_value': 0.0001,
        'diferencia': 0.0000
    }
    
    await sistema.alerta_validacion_psi(evento, resultados)
    
    # Verificar reporte
    print("\n" + "=" * 70)
    print("📊 REPORTE DE TESTS")
    print("=" * 70)
    
    reporte = sistema.generar_reporte_alertas()
    print(f"Total de alertas enviadas: {reporte['total_alertas']}")
    print("\nAlertas por prioridad:")
    for prioridad, cantidad in reporte['alertas_por_prioridad'].items():
        if cantidad > 0:
            print(f"   • {prioridad}: {cantidad}")
    
    print("\n✅ TEST DE INTEGRACIÓN COMPLETADO")


def run_sync_tests():
    """Ejecutar tests síncronos"""
    print("=" * 70)
    print("🧪 EJECUTANDO TESTS SÍNCRONOS")
    print("=" * 70)
    
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Agregar tests
    suite.addTests(loader.loadTestsFromTestCase(TestSistemaAlertasAvanzado))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


async def run_async_tests():
    """Ejecutar tests asíncronos"""
    print("\n" + "=" * 70)
    print("🧪 EJECUTANDO TESTS ASÍNCRONOS")
    print("=" * 70)
    
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Agregar tests asíncronos
    suite.addTests(loader.loadTestsFromTestCase(TestAlertasAsync))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


async def main():
    """Ejecutar todos los tests"""
    print("🌌 SISTEMA DE TESTS - ALERTAS AVANZADAS")
    print("=" * 70)
    
    try:
        # Tests síncronos
        sync_success = run_sync_tests()
        
        # Tests asíncronos
        async_success = await run_async_tests()
        
        # Test de integración
        print("\n" + "=" * 70)
        print("🧪 EJECUTANDO TEST DE INTEGRACIÓN")
        print("=" * 70)
        
        await test_integracion_completa()
        
        # Resumen final
        print("\n" + "=" * 70)
        print("📈 RESUMEN DE TESTS")
        print("=" * 70)
        print(f"Tests síncronos: {'✅ PASSED' if sync_success else '❌ FAILED'}")
        print(f"Tests asíncronos: {'✅ PASSED' if async_success else '❌ FAILED'}")
        print("Test de integración: ✅ COMPLETADO")
        
        if sync_success and async_success:
            print("\n🎉 ¡TODOS LOS TESTS PASARON!")
            return 0
        else:
            print("\n⚠️  Algunos tests fallaron")
            return 1
            
    except Exception as e:
        print(f"\n❌ Error ejecutando tests: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    exit_code = asyncio.run(main())
    sys.exit(exit_code)
