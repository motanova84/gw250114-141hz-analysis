#!/usr/bin/env python3
"""
Tests for Universal Validation Framework.
"""

import unittest
import numpy as np
import sys
import os
from pathlib import Path

# Import the framework
from universal_validation_framework import (
    UniversalFrequency,
    DESIValidator,
    IGETSValidator,
    LISAValidator,
    EEGValidator,
    HelioseismologyValidator,
    UniversalValidator
)


class TestUniversalFrequency(unittest.TestCase):
    """Tests para UniversalFrequency."""
    
    def setUp(self):
        """Configure frequency for tests."""
        self.f0 = UniversalFrequency()
    
    def test_f0_value(self):
        """Test que f0 tiene el valor correcto."""
        self.assertAlmostEqual(self.f0.f0, 141.7001, places=4)
    
    def test_harmonics(self):
        """Test cálculo de armónicos."""
        harmonics = self.f0.harmonics(n_max=3)
        
        # Verificar dimensiones
        self.assertEqual(len(harmonics), 3)
        
        # Verificar valores
        self.assertAlmostEqual(harmonics[0], 141.7001, places=4)
        self.assertAlmostEqual(harmonics[1], 283.4002, places=4)
        self.assertAlmostEqual(harmonics[2], 425.1003, places=4)
    
    def test_subharmonics(self):
        """Test cálculo de subarmónicos."""
        subharmonics = self.f0.subharmonics(n_max=2)
        
        # Verificar dimensiones
        self.assertEqual(len(subharmonics), 2)
        
        # Verificar valores
        self.assertAlmostEqual(subharmonics[0], 141.7001 / 2, places=4)
        self.assertAlmostEqual(subharmonics[1], 141.7001 / 3, places=4)
    
    def test_tolerance_band(self):
        """Test cálculo de banda de tolerancia."""
        f_min, f_max = self.f0.tolerance_band(tolerance_pct=0.5)
        
        # Verificar que están alrededor de f0
        self.assertLess(f_min, self.f0.f0)
        self.assertGreater(f_max, self.f0.f0)
        
        # Verificar el ancho correcto
        delta = (f_max - f_min) / 2
        expected_delta = self.f0.f0 * 0.5 / 100
        self.assertAlmostEqual(delta, expected_delta, places=6)


class TestDESIValidator(unittest.TestCase):
    """Tests para DESIValidator."""
    
    def setUp(self):
        """Configure validator for tests."""
        self.validator = DESIValidator()
    
    def test_initialization(self):
        """Test inicialización correcta."""
        self.assertIsNotNone(self.validator.f0)
        self.assertEqual(self.validator.name, "DESI (Estructura Cósmica)")
    
    def test_search_signal(self):
        """Test búsqueda de señal."""
        result = self.validator.search_signal({})
        
        # Verificar estructura del resultado
        self.assertIn('system', result)
        self.assertIn('frequency_detected', result)
        self.assertIn('snr', result)
        self.assertIn('significance_sigma', result)
        self.assertIn('method', result)
        self.assertIn('data_source', result)
        self.assertIn('detection_confidence', result)
        
        # Verificar valores
        self.assertEqual(result['system'], "DESI (Estructura Cósmica)")
        self.assertGreater(result['snr'], 0)


class TestIGETSValidator(unittest.TestCase):
    """Tests para IGETSValidator."""
    
    def setUp(self):
        """Configure validator for tests."""
        self.validator = IGETSValidator()
    
    def test_initialization(self):
        """Test inicialización correcta."""
        self.assertIsNotNone(self.validator.f0)
        self.assertEqual(self.validator.name, "IGETS (Mareas Terrestres)")
    
    def test_generate_synthetic_data(self):
        """Test generación de datos sintéticos."""
        t, g = self.validator.generate_synthetic_data(duration_hours=1)
        
        # Verificar dimensiones
        self.assertEqual(len(t), len(g))
        self.assertGreater(len(t), 3600)  # Al menos 1 hora a 1 Hz
        
        # Verificar que no todos los valores son iguales (hay señal)
        self.assertGreater(np.std(g), 0)
    
    def test_search_signal(self):
        """Test búsqueda de señal."""
        t, g = self.validator.generate_synthetic_data(duration_hours=1)
        result = self.validator.search_signal(t, g)
        
        # Verificar estructura del resultado
        self.assertIn('system', result)
        self.assertIn('frequency_detected', result)
        self.assertIn('frequency_expected', result)
        self.assertIn('frequency_error_hz', result)
        self.assertIn('snr', result)
        self.assertIn('significance_sigma', result)
        
        # Verificar valores razonables
        self.assertGreater(result['frequency_detected'], 0)
        self.assertGreater(result['snr'], 0)


class TestLISAValidator(unittest.TestCase):
    """Tests para LISAValidator."""
    
    def setUp(self):
        """Configure validator for tests."""
        self.validator = LISAValidator()
    
    def test_initialization(self):
        """Test inicialización correcta."""
        self.assertIsNotNone(self.validator.f0)
        self.assertEqual(self.validator.name, "LISA (Ondas Gravitacionales)")
    
    def test_search_signal(self):
        """Test búsqueda de señal."""
        result = self.validator.search_signal()
        
        # Verificar estructura del resultado
        self.assertIn('system', result)
        self.assertIn('frequency_target', result)
        self.assertIn('frequency_fundamental', result)
        self.assertIn('harmonic_number', result)
        self.assertIn('detection_confidence', result)
        
        # Verificar que se busca subarmónico
        self.assertEqual(result['harmonic_number'], -1000)
        self.assertEqual(result['detection_confidence'], 'pending')


class TestEEGValidator(unittest.TestCase):
    """Tests para EEGValidator."""
    
    def setUp(self):
        """Configure validator for tests."""
        self.validator = EEGValidator()
    
    def test_initialization(self):
        """Test inicialización correcta."""
        self.assertIsNotNone(self.validator.f0)
        self.assertEqual(self.validator.name, "EEG (Actividad Cerebral)")
    
    def test_generate_synthetic_eeg(self):
        """Test generación de datos sintéticos EEG."""
        t, eeg = self.validator.generate_synthetic_eeg(duration_s=10)
        
        # Verificar dimensiones
        self.assertEqual(len(t), len(eeg))
        self.assertGreater(len(t), 10000)  # Al menos 10 segundos a 1000 Hz
        
        # Verificar que no todos los valores son iguales (hay señal)
        self.assertGreater(np.std(eeg), 0)
    
    def test_search_signal(self):
        """Test búsqueda de señal."""
        t, eeg = self.validator.generate_synthetic_eeg(duration_s=10)
        result = self.validator.search_signal(t, eeg)
        
        # Verificar estructura del resultado
        self.assertIn('system', result)
        self.assertIn('frequency_detected', result)
        self.assertIn('frequency_expected', result)
        self.assertIn('snr', result)
        self.assertIn('significance_sigma', result)
        self.assertIn('detection_confidence', result)
        
        # Verificar valores razonables
        self.assertGreater(result['frequency_detected'], 0)


class TestHelioseismologyValidator(unittest.TestCase):
    """Tests para HelioseismologyValidator."""
    
    def setUp(self):
        """Configure validator for tests."""
        self.validator = HelioseismologyValidator()
    
    def test_initialization(self):
        """Test inicialización correcta."""
        self.assertIsNotNone(self.validator.f0)
        self.assertEqual(self.validator.name, "Heliosismología (Sol)")
    
    def test_search_signal(self):
        """Test búsqueda de señal."""
        result = self.validator.search_signal()
        
        # Verificar estructura del resultado
        self.assertIn('system', result)
        self.assertIn('frequency_target', result)
        self.assertIn('frequency_fundamental', result)
        self.assertIn('harmonic_number', result)
        self.assertIn('detection_confidence', result)
        
        # Verificar que se busca subarmónico muy bajo
        self.assertEqual(result['harmonic_number'], -50000)
        self.assertEqual(result['detection_confidence'], 'pending')


class TestUniversalValidator(unittest.TestCase):
    """Tests para UniversalValidator (orquestador)."""
    
    def setUp(self):
        """Configure validator for tests."""
        self.validator = UniversalValidator()
    
    def test_initialization(self):
        """Test inicialización correcta."""
        self.assertIsNotNone(self.validator.f0)
    
    def test_run_all_validations(self):
        """Test ejecución de todas las validaciones."""
        results = self.validator.run_all_validations()
        
        # Verificar que hay 5 resultados (5 sistemas)
        self.assertEqual(len(results), 5)
        
        # Verificar que todos tienen la estructura esperada
        for result in results:
            self.assertIn('system', result)
            self.assertIn('method', result)
            self.assertIn('data_source', result)
            self.assertIn('detection_confidence', result)
    
    def test_generate_report(self):
        """Test generación de reporte."""
        results = self.validator.run_all_validations()
        report = self.validator.generate_report(results)
        
        # Verificar que el reporte contiene información clave
        self.assertIn('VALIDACIÓN UNIVERSAL', report)
        self.assertIn('141.7', report)
        self.assertIn('JMMB', report)
        self.assertIn('DESI', report)
        self.assertIn('IGETS', report)
        self.assertIn('LISA', report)
        self.assertIn('EEG', report)
        self.assertIn('Heliosismología', report)


if __name__ == '__main__':
    unittest.main()
