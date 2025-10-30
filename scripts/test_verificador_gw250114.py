#!/usr/bin/env python3
"""
Tests para el sistema de verificación GW250114
"""
import unittest
import sys
import os
import json
import numpy as np
from unittest.mock import Mock, patch, MagicMock
from datetime import datetime

# Añadir directorio scripts al path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    from verificador_gw250114 import VerificadorGW250114
except ImportError as e:
    print(f"⚠️ Cannot import verificador_gw250114: {e}")
    print("This test requires gwpy and other dependencies")
    print("Install with: pip install gwpy")
    sys.exit(0)


class TestVerificadorGW250114(unittest.TestCase):
    """Tests para VerificadorGW250114"""
    
    def setUp(self):
        """Configurar test"""
        self.verificador = VerificadorGW250114(check_interval=1)
    
    def test_inicializacion(self):
        """Test: Inicialización correcta del verificador"""
        self.assertEqual(self.verificador.event_name, "GW250114")
        self.assertEqual(self.verificador.target_frequency, 141.7001)
        self.assertEqual(self.verificador.check_interval, 1)
        self.assertTrue(os.path.exists(self.verificador.results_dir))
    
    @patch('verificador_gw250114.TimeSeries.fetch_open_data')
    @patch('verificador_gw250114.to_gps')
    def test_verificar_disponibilidad_no_disponible(self, mock_to_gps, mock_fetch):
        """Test: Verificar cuando GW250114 no está disponible"""
        # Mock para evento de prueba (GW150914)
        mock_test_data = MagicMock()
        
        # Mock para GW250114 (no disponible)
        def side_effect(detector, start, end, **kwargs):
            if start < 1126259462:  # GW150914
                return mock_test_data
            else:  # GW250114
                raise Exception("Event not found")
        
        mock_fetch.side_effect = side_effect
        mock_to_gps.return_value = 1358035218.0  # GPS time estimado para 2025-01-14
        
        disponible, gps_time, mensaje = self.verificador.verificar_disponibilidad()
        
        self.assertFalse(disponible)
        self.assertIsNotNone(gps_time)
        self.assertIn("no disponible", mensaje.lower())
    
    @patch('verificador_gw250114.TimeSeries.fetch_open_data')
    @patch('verificador_gw250114.to_gps')
    def test_verificar_disponibilidad_disponible(self, mock_to_gps, mock_fetch):
        """Test: Verificar cuando GW250114 está disponible"""
        mock_data = MagicMock()
        mock_fetch.return_value = mock_data
        mock_to_gps.return_value = 1358035218.0
        
        disponible, gps_time, mensaje = self.verificador.verificar_disponibilidad()
        
        self.assertTrue(disponible)
        self.assertEqual(gps_time, 1358035218.0)
        self.assertIn("disponible", mensaje.lower())
    
    def test_calcular_espectro(self):
        """Test: Cálculo de espectro de potencia"""
        # Crear señal sintética
        sample_rate = 4096
        duration = 1.0
        t = np.arange(0, duration, 1/sample_rate)
        
        # Señal con componente en 141.7 Hz
        signal_data = np.sin(2 * np.pi * 141.7 * t)
        
        # Crear mock de TimeSeries
        mock_data = MagicMock()
        mock_data.value = signal_data
        mock_data.sample_rate = MagicMock()
        mock_data.sample_rate.value = sample_rate
        mock_data.__len__ = lambda self: len(signal_data)
        
        freqs, psd = self.verificador._calcular_espectro(mock_data)
        
        # Verificar que hay pico cerca de 141.7 Hz
        idx_peak = np.argmax(psd)
        freq_peak = freqs[idx_peak]
        
        self.assertIsNotNone(freqs)
        self.assertIsNotNone(psd)
        self.assertGreater(len(freqs), 0)
        self.assertGreater(len(psd), 0)
        # Verificar que el pico está cerca de 141.7 Hz (con tolerancia)
        self.assertAlmostEqual(freq_peak, 141.7, delta=5.0)
    
    def test_calcular_snr(self):
        """Test: Cálculo de SNR"""
        # Crear espectro sintético
        freqs = np.linspace(100, 200, 1000)
        
        # PSD con ruido gaussiano y pico en 141.7 Hz
        psd = np.random.normal(1.0, 0.1, len(freqs))
        
        # Agregar pico en 141.7 Hz
        idx_target = np.argmin(np.abs(freqs - 141.7))
        psd[idx_target-5:idx_target+5] *= 5.0  # Amplificar señal
        
        snr = self.verificador._calcular_snr(freqs, psd, 141.7)
        
        self.assertIsNotNone(snr)
        self.assertGreater(snr, 1.0)  # Debería haber SNR > 1
    
    def test_evaluar_significancia(self):
        """Test: Evaluación de significancia"""
        # Alta significancia
        sig_alta = self.verificador._evaluar_significancia(snr=3.5, bayes_factor=15)
        self.assertEqual(sig_alta, "ALTA")
        
        # Moderada significancia
        sig_mod = self.verificador._evaluar_significancia(snr=2.5, bayes_factor=5)
        self.assertEqual(sig_mod, "MODERADA")
        
        # Baja significancia
        sig_baja = self.verificador._evaluar_significancia(snr=1.8, bayes_factor=2)
        self.assertEqual(sig_baja, "BAJA")
        
        # No significativa
        sig_no = self.verificador._evaluar_significancia(snr=1.0, bayes_factor=1)
        self.assertEqual(sig_no, "NO_SIGNIFICATIVA")
    
    def test_evaluar_combinado_deteccion_confirmada(self):
        """Test: Evaluación combinada - detección confirmada"""
        detectores = {
            'H1': {
                'snr': 3.5,
                'bayes_factor': 15,
                'significancia': 'ALTA'
            },
            'L1': {
                'snr': 3.2,
                'bayes_factor': 12,
                'significancia': 'ALTA'
            }
        }
        
        resultado = self.verificador._evaluar_combinado(detectores)
        
        self.assertEqual(resultado['status'], 'DETECCION_CONFIRMADA')
        self.assertTrue(resultado['coherencia'])
        self.assertGreater(resultado['snr_medio'], 2.5)
    
    def test_evaluar_combinado_no_detectado(self):
        """Test: Evaluación combinada - no detectado"""
        detectores = {
            'H1': {
                'snr': 1.0,
                'bayes_factor': 1,
                'significancia': 'NO_SIGNIFICATIVA'
            },
            'L1': {
                'snr': 0.8,
                'bayes_factor': 0.9,
                'significancia': 'NO_SIGNIFICATIVA'
            }
        }
        
        resultado = self.verificador._evaluar_combinado(detectores)
        
        self.assertEqual(resultado['status'], 'NO_DETECTADO')
        self.assertFalse(resultado['coherencia'])
    
    def test_evaluar_combinado_insuficiente(self):
        """Test: Evaluación combinada - datos insuficientes"""
        detectores = {
            'H1': {
                'snr': 3.5,
                'bayes_factor': 15,
                'significancia': 'ALTA'
            }
        }
        
        resultado = self.verificador._evaluar_combinado(detectores)
        
        self.assertEqual(resultado['status'], 'INSUFICIENTE')
    
    def test_guardar_resultados(self):
        """Test: Guardar resultados en JSON"""
        resultados = {
            'evento': 'GW250114',
            'gps_time': 1358035218.0,
            'timestamp': datetime.now().isoformat(),
            'frecuencia_objetivo': 141.7001
        }
        
        self.verificador._guardar_resultados(resultados)
        
        # Verificar que el archivo se creó
        files = os.listdir(self.verificador.results_dir)
        json_files = [f for f in files if f.startswith('verificacion_gw250114_') and f.endswith('.json')]
        
        self.assertGreater(len(json_files), 0)
        
        # Leer y verificar contenido
        latest_file = sorted(json_files)[-1]
        filepath = os.path.join(self.verificador.results_dir, latest_file)
        
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        self.assertEqual(data['evento'], 'GW250114')
        self.assertEqual(data['gps_time'], 1358035218.0)
        
        # Limpiar archivo de prueba
        os.remove(filepath)
    
    @patch('verificador_gw250114.VerificadorGW250114.verificar_disponibilidad')
    def test_monitorear_una_verificacion(self, mock_verificar):
        """Test: Monitoreo con una sola verificación"""
        mock_verificar.return_value = (False, None, "No disponible")
        
        self.verificador.monitorear(max_checks=1)
        
        # Verificar que se llamó una vez
        self.assertEqual(mock_verificar.call_count, 1)
    
    @patch('verificador_gw250114.VerificadorGW250114.analizar_evento')
    @patch('verificador_gw250114.VerificadorGW250114.verificar_disponibilidad')
    def test_monitorear_evento_disponible(self, mock_verificar, mock_analizar):
        """Test: Monitoreo cuando el evento está disponible"""
        mock_verificar.return_value = (True, 1358035218.0, "Evento disponible")
        mock_analizar.return_value = {
            'evento': 'GW250114',
            'evaluacion_combinada': {
                'status': 'DETECCION_CONFIRMADA',
                'snr_medio': 3.5,
                'coherencia': True
            }
        }
        
        self.verificador.monitorear(max_checks=1)
        
        # Verificar que se llamaron las funciones correctas
        self.assertEqual(mock_verificar.call_count, 1)
        self.assertEqual(mock_analizar.call_count, 1)


class TestIntegracionVerificador(unittest.TestCase):
    """Tests de integración para el verificador"""
    
    @patch('verificador_gw250114.TimeSeries.fetch_open_data')
    @patch('verificador_gw250114.to_gps')
    def test_flujo_completo_no_disponible(self, mock_to_gps, mock_fetch):
        """Test: Flujo completo cuando evento no está disponible"""
        # Mock datos de prueba
        mock_test_data = MagicMock()
        
        def side_effect(detector, start, end, **kwargs):
            if start < 1126259462:
                return mock_test_data
            else:
                raise Exception("Event not found")
        
        mock_fetch.side_effect = side_effect
        mock_to_gps.return_value = 1358035218.0
        
        verificador = VerificadorGW250114(check_interval=1)
        disponible, gps_time, mensaje = verificador.verificar_disponibilidad()
        
        self.assertFalse(disponible)
        self.assertIn("no disponible", mensaje.lower())


def run_tests():
    """Ejecutar todos los tests"""
    print("🧪 Ejecutando tests del verificador GW250114...\n")
    
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Agregar tests
    suite.addTests(loader.loadTestsFromTestCase(TestVerificadorGW250114))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegracionVerificador))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Resumen
    print("\n" + "="*70)
    print(f"Tests ejecutados: {result.testsRun}")
    print(f"Exitosos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Fallidos: {len(result.failures)}")
    print(f"Errores: {len(result.errors)}")
    print("="*70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
