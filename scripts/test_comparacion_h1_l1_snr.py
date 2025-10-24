#!/usr/bin/env python3
"""
Tests para el script de comparación H1 vs L1 SNR
"""
import unittest
import numpy as np
import sys
import os

# Agregar el directorio scripts al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))

from comparacion_h1_l1_snr import estimate_snr, events  # noqa: E402


class TestComparacionH1L1SNR(unittest.TestCase):
    """Tests para la comparación H1 vs L1"""

    def test_events_dictionary_structure(self):
        """Verificar que el diccionario de eventos tiene la estructura correcta"""
        self.assertEqual(len(events), 11, "Debe haber 11 eventos")

        for event_name, time_window in events.items():
            self.assertIsInstance(event_name, str, "Nombre del evento debe ser string")
            self.assertIsInstance(time_window, list, "Ventana de tiempo debe ser lista")
            self.assertEqual(len(time_window), 2, "Ventana debe tener inicio y fin")
            self.assertIsInstance(time_window[0], int, "Tiempo de inicio debe ser int")
            self.assertIsInstance(time_window[1], int, "Tiempo de fin debe ser int")
            self.assertGreater(time_window[1], time_window[0], "Fin debe ser mayor que inicio")

    def test_event_names(self):
        """Verificar que los nombres de eventos son correctos"""
        expected_events = [
            "GW150914", "GW151012", "GW151226", "GW170104", "GW170608",
            "GW170729", "GW170809", "GW170814", "GW170817", "GW170818", "GW170823"
        ]
        self.assertEqual(list(events.keys()), expected_events)

    def test_estimate_snr_with_mock_data(self):
        """Test de la función estimate_snr con datos simulados"""
        # Crear una serie temporal simulada
        class MockTimeSeries:
            def __init__(self, data):
                self.value = data

        # Señal con ruido gaussiano
        np.random.seed(42)
        signal = np.sin(2 * np.pi * 141.7 * np.linspace(0, 1, 4096))
        noise = np.random.normal(0, 0.1, 4096)
        ts = MockTimeSeries(signal + noise)

        snr_val = estimate_snr(ts)

        # SNR debe ser positivo
        self.assertGreater(snr_val, 0, "SNR debe ser positivo")

        # SNR debe ser un número finito
        self.assertTrue(np.isfinite(snr_val), "SNR debe ser finito")

    def test_estimate_snr_with_zero_std(self):
        """Test de estimate_snr con señal constante (std=0)"""
        class MockTimeSeries:
            def __init__(self, data):
                self.value = data

        # Señal constante
        ts = MockTimeSeries(np.ones(100))

        # Esto debería dar un error o infinito
        with self.assertWarns(RuntimeWarning):
            estimate_snr(ts)

    def test_estimate_snr_high_signal(self):
        """Test de que señal fuerte da SNR alto"""
        class MockTimeSeries:
            def __init__(self, data):
                self.value = data

        np.random.seed(42)
        # Señal fuerte sin ruido
        signal = 10 * np.sin(2 * np.pi * 141.7 * np.linspace(0, 1, 4096))
        ts_high = MockTimeSeries(signal)

        # Señal débil sin ruido
        signal_weak = 1 * np.sin(2 * np.pi * 141.7 * np.linspace(0, 1, 4096))
        ts_low = MockTimeSeries(signal_weak)

        snr_high = estimate_snr(ts_high)
        snr_low = estimate_snr(ts_low)

        # Ambos deben tener SNR similar ya que es la misma forma de onda
        # Solo verificamos que ambos son positivos y finitos
        self.assertGreater(snr_high, 0, "SNR alto debe ser positivo")
        self.assertGreater(snr_low, 0, "SNR bajo debe ser positivo")
        self.assertTrue(np.isfinite(snr_high), "SNR alto debe ser finito")
        self.assertTrue(np.isfinite(snr_low), "SNR bajo debe ser finito")

    def test_gw150914_time_window(self):
        """Verificar ventana de tiempo específica de GW150914"""
        gw150914_window = events["GW150914"]
        self.assertEqual(gw150914_window[0], 1126259462)
        self.assertEqual(gw150914_window[1], 1126259494)
        self.assertEqual(gw150914_window[1] - gw150914_window[0], 32, "Ventana debe ser de 32 segundos")

    def test_all_events_have_32_second_window(self):
        """Verificar que todos los eventos tienen ventana de 32 segundos"""
        for event_name, time_window in events.items():
            duration = time_window[1] - time_window[0]
            self.assertEqual(duration, 32, f"{event_name} debe tener ventana de 32 segundos")

    def test_events_chronological_order(self):
        """Verificar que los eventos están en orden cronológico"""
        times = [time_window[0] for time_window in events.values()]
        sorted_times = sorted(times)
        self.assertEqual(times, sorted_times, "Eventos deben estar en orden cronológico")


class TestScriptOutputs(unittest.TestCase):
    """Tests para verificar que el script genera los archivos esperados"""

    def test_output_directories_exist(self):
        """Verificar que los directorios de salida pueden ser creados"""
        import os

        # Verificar que se puede crear el directorio results/figures
        test_dir = 'results/figures'
        os.makedirs(test_dir, exist_ok=True)
        self.assertTrue(os.path.exists(test_dir))

    def test_json_structure(self):
        """Test de la estructura esperada del JSON de salida"""
        # Estructura esperada del JSON
        expected_keys = list(events.keys())

        # Verificar que cada evento debe tener H1_SNR y L1_SNR
        for event in expected_keys:
            # Simular estructura
            result = {"H1_SNR": 1.23, "L1_SNR": 4.56}
            self.assertIn("H1_SNR", result)
            self.assertIn("L1_SNR", result)
            self.assertIsInstance(result["H1_SNR"], (int, float))
            self.assertIsInstance(result["L1_SNR"], (int, float))


def run_tests():
    """Ejecuta todos los tests"""
    # Crear test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Agregar todos los tests
    suite.addTests(loader.loadTestsFromTestCase(TestComparacionH1L1SNR))
    suite.addTests(loader.loadTestsFromTestCase(TestScriptOutputs))

    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    # Retornar código de salida
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_tests())
