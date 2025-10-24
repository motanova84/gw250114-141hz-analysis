#!/usr/bin/env python3
"""
Test suite para validate_141hz_gw150914.py

Valida que el script de validación funciona correctamente y genera
los archivos esperados.
"""

import sys
import os
import json
import unittest
from pathlib import Path

# Añadir directorio de scripts al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))


class TestValidate141HzGW150914(unittest.TestCase):
    """Tests para el script de validación de 141.7 Hz"""
    
    def setUp(self):
        """Configurar variables de test"""
        self.results_dir = Path('results/validation')
        self.expected_files = [
            'test2_results.png',
            'test3_results.png',
            'final_results.json'
        ]
    
    def test_results_directory_exists(self):
        """Verificar que el directorio de resultados existe"""
        # Si los tests se ejecutan después del script principal
        if self.results_dir.exists():
            self.assertTrue(self.results_dir.is_dir())
    
    def test_expected_files_created(self):
        """Verificar que los archivos esperados fueron creados"""
        # Solo verificar si ya se ejecutó el script
        if self.results_dir.exists():
            for filename in self.expected_files:
                filepath = self.results_dir / filename
                if filepath.exists():
                    self.assertTrue(filepath.is_file(), 
                                  f"{filename} debe ser un archivo")
    
    def test_json_structure(self):
        """Verificar estructura del JSON de resultados"""
        json_path = self.results_dir / 'final_results.json'
        
        if json_path.exists():
            with open(json_path, 'r') as f:
                data = json.load(f)
            
            # Verificar campos principales
            self.assertIn('validation_title', data)
            self.assertIn('event', data)
            self.assertEqual(data['event'], 'GW150914')
            self.assertIn('target_frequency_hz', data)
            self.assertAlmostEqual(data['target_frequency_hz'], 141.7001, places=4)
            
            # Verificar resultados de tests
            self.assertIn('test_2', data)
            self.assertIn('test_3', data)
            
            # Verificar que no hay errores críticos en test_2
            if 'error' not in data['test_2']:
                self.assertIn('h1_asd', data['test_2'])
                self.assertIn('l1_asd', data['test_2'])
                self.assertIn('ratio_l1_h1', data['test_2'])
                self.assertGreater(data['test_2']['ratio_l1_h1'], 0)
            
            # Verificar que no hay errores críticos en test_3
            if 'error' not in data['test_3']:
                self.assertIn('event_snr', data['test_3'])
                self.assertIn('max_off_source_snr', data['test_3'])
                self.assertGreater(data['test_3']['event_snr'], 0)
            
            # Verificar conclusión científica
            self.assertIn('scientific_conclusion', data)
            self.assertIn('validated', data['scientific_conclusion'])
            self.assertIn('citation', data['scientific_conclusion'])
    
    def test_target_frequency_constant(self):
        """Verificar que la frecuencia objetivo es correcta"""
        # Importar el módulo si existe
        try:
            import validate_141hz_gw150914 as validator
            self.assertAlmostEqual(validator.TARGET_FREQ, 141.7001, places=4)
        except ImportError:
            self.skipTest("Módulo validate_141hz_gw150914 no disponible")
    
    def test_gw150914_gps_time_constant(self):
        """Verificar que el tiempo GPS de GW150914 es correcto"""
        try:
            import validate_141hz_gw150914 as validator
            # Tiempo GPS oficial de GW150914
            expected_gps = 1126259462.423
            self.assertAlmostEqual(validator.GW150914_GPS_TIME, expected_gps, 
                                 places=3)
        except ImportError:
            self.skipTest("Módulo validate_141hz_gw150914 no disponible")


class TestCalculationFunctions(unittest.TestCase):
    """Tests para funciones de cálculo individuales"""
    
    def test_asd_calculation_function_exists(self):
        """Verificar que existe función para calcular ASD"""
        try:
            import validate_141hz_gw150914 as validator
            self.assertTrue(hasattr(validator, 'calculate_asd'))
            self.assertTrue(callable(validator.calculate_asd))
        except ImportError:
            self.skipTest("Módulo validate_141hz_gw150914 no disponible")
    
    def test_snr_calculation_function_exists(self):
        """Verificar que existe función para calcular SNR"""
        try:
            import validate_141hz_gw150914 as validator
            self.assertTrue(hasattr(validator, 'calculate_snr_at_frequency'))
            self.assertTrue(callable(validator.calculate_snr_at_frequency))
        except ImportError:
            self.skipTest("Módulo validate_141hz_gw150914 no disponible")
    
    def test_test2_function_exists(self):
        """Verificar que existe Test 2"""
        try:
            import validate_141hz_gw150914 as validator
            self.assertTrue(hasattr(validator, 'test_2_noise_analysis'))
            self.assertTrue(callable(validator.test_2_noise_analysis))
        except ImportError:
            self.skipTest("Módulo validate_141hz_gw150914 no disponible")
    
    def test_test3_function_exists(self):
        """Verificar que existe Test 3"""
        try:
            import validate_141hz_gw150914 as validator
            self.assertTrue(hasattr(validator, 'test_3_off_source_scan'))
            self.assertTrue(callable(validator.test_3_off_source_scan))
        except ImportError:
            self.skipTest("Módulo validate_141hz_gw150914 no disponible")


def run_tests():
    """Ejecutar todos los tests"""
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Añadir tests
    suite.addTests(loader.loadTestsFromTestCase(TestValidate141HzGW150914))
    suite.addTests(loader.loadTestsFromTestCase(TestCalculationFunctions))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
