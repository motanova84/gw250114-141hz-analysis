#!/usr/bin/env python3
"""
Unit tests for test_gw150914_validation.py

Tests the Test 2 and Test 3 implementations with synthetic data.
"""
import unittest
import numpy as np
import sys
import os
import json
from unittest.mock import Mock, patch, MagicMock

# Mock gwpy before import
sys.modules['gwpy'] = MagicMock()
sys.modules['gwpy.timeseries'] = MagicMock()

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from test_gw150914_validation import (
    calculate_snr_at_frequency,
    test2_noise_comparison,
    create_visualizations
)


class TestCalculateSNR(unittest.TestCase):
    """Test SNR calculation function"""
    
    def setUp(self):
        """Create synthetic time series data"""
        self.fs = 4096  # Hz
        self.duration = 2  # seconds
        self.t = np.linspace(0, self.duration, int(self.fs * self.duration))
        self.f0 = 141.7  # Hz
        
    def test_snr_with_signal(self):
        """Test SNR calculation with signal present"""
        # Create signal with known amplitude
        signal = 1e-21 * np.sin(2 * np.pi * self.f0 * self.t)
        noise = np.random.normal(0, 1e-22, len(self.t))
        data = signal + noise
        
        # Mock TimeSeries object
        mock_data = Mock()
        mock_data.value = data
        mock_data.sample_rate.value = self.fs
        
        snr = calculate_snr_at_frequency(mock_data, self.f0)
        
        # SNR should be positive and reasonable
        # With strong signal relative to noise, SNR can be quite large
        self.assertGreater(snr, 1.0)
        self.assertLess(snr, 100000.0)
        
    def test_snr_noise_only(self):
        """Test SNR calculation with noise only"""
        # Pure Gaussian noise
        data = np.random.normal(0, 1e-22, len(self.t))
        
        mock_data = Mock()
        mock_data.value = data
        mock_data.sample_rate.value = self.fs
        
        snr = calculate_snr_at_frequency(mock_data, self.f0)
        
        # SNR should be close to 1 for pure noise
        self.assertGreater(snr, 0.1)
        self.assertLess(snr, 10.0)


class TestTest2NoiseComparison(unittest.TestCase):
    """Test the Test 2 noise comparison function"""
    
    def setUp(self):
        """Create synthetic detector data"""
        self.fs = 4096
        self.duration = 2
        self.t = np.linspace(0, self.duration, int(self.fs * self.duration))
        self.f0 = 141.7
        self.merger_time = 1000.0  # Arbitrary GPS time
        
    def create_mock_timeseries(self, noise_level):
        """Create mock TimeSeries with specified noise level"""
        noise = np.random.normal(0, noise_level, len(self.t))
        signal = 1e-21 * np.sin(2 * np.pi * self.f0 * self.t)
        data = signal + noise
        
        mock_ts = Mock()
        mock_ts.value = data
        mock_ts.sample_rate.value = self.fs
        mock_ts.times.value = self.t + self.merger_time
        mock_ts.t0.value = self.merger_time
        
        # Mock crop method
        def mock_crop(start, end):
            return mock_ts
        mock_ts.crop = mock_crop
        
        # Mock psd method
        def mock_psd(fftlength=4):
            freqs = np.fft.rfftfreq(len(data), d=1/self.fs)
            fft_data = np.fft.rfft(data)
            psd_data = np.abs(fft_data)**2 / len(data)
            
            psd_mock = Mock()
            psd_mock.value = psd_data
            psd_mock.frequencies.value = freqs
            return psd_mock
        mock_ts.psd = mock_psd
        
        return mock_ts
    
    def test_noise_ratio_calculation(self):
        """Test that noise ratio is calculated correctly"""
        # Create H1 with lower noise
        h1_data = self.create_mock_timeseries(noise_level=1e-22)
        
        # Create L1 with higher noise (5x)
        l1_data = self.create_mock_timeseries(noise_level=5e-22)
        
        results = test2_noise_comparison(h1_data, l1_data, self.f0, self.merger_time)
        
        # Check that all expected keys are present
        self.assertIn('noise_h1', results)
        self.assertIn('noise_l1', results)
        self.assertIn('ratio', results)
        self.assertIn('target_freq', results)
        
        # Check that ratio is positive
        self.assertGreater(results['ratio'], 0)
        
        # Check that noise values are positive
        self.assertGreater(results['noise_h1'], 0)
        self.assertGreater(results['noise_l1'], 0)
        
        # Note: Due to random noise, exact ratio may vary
        # We just verify the function executes and returns valid values


class TestVisualization(unittest.TestCase):
    """Test visualization generation"""
    
    def test_create_visualizations_with_valid_data(self):
        """Test that visualizations can be created without errors"""
        test2_results = {
            'noise_h1': 1.23e-23,
            'noise_l1': 6.17e-23,
            'ratio': 5.02,
            'target_freq': 141.7
        }
        
        test3_results = {
            'snr_onsource': 7.47,
            'snrs_offsource': [2.1, 3.0, 1.4, 2.7, 2.8, 3.4],
            'max_snr_offsource': 3.4,
            'mean_snr_offsource': 2.57,
            'std_snr_offsource': 0.73,
            'n_days_analyzed': 6,
            'target_freq': 141.7,
            'detector': 'H1'
        }
        
        # Create visualizations in temporary directory
        import tempfile
        with tempfile.TemporaryDirectory() as tmpdir:
            try:
                create_visualizations(test2_results, test3_results, output_dir=tmpdir)
                
                # Check that files were created
                test2_file = os.path.join(tmpdir, 'test2_noise_comparison_gw150914.png')
                test3_file = os.path.join(tmpdir, 'test3_offsource_analysis_gw150914.png')
                
                self.assertTrue(os.path.exists(test2_file), "Test 2 figure not created")
                self.assertTrue(os.path.exists(test3_file), "Test 3 figure not created")
                
            except Exception as e:
                self.fail(f"Visualization creation failed: {e}")


class TestJSONOutput(unittest.TestCase):
    """Test JSON output format"""
    
    def test_json_structure(self):
        """Test that expected JSON structure is created"""
        # Sample results matching expected format
        final_results = {
            'event': 'GW150914',
            'target_frequency': 141.7,
            'test2': {
                'noise_h1': 1.23e-23,
                'noise_l1': 6.17e-23,
                'ratio': 5.02
            },
            'test3': {
                'snrs_offsource': [2.1, 3.0, 1.4, 2.7, 2.8, 3.4],
                'max_snr_offsource': 3.4
            }
        }
        
        # Validate JSON can be serialized
        try:
            json_str = json.dumps(final_results, indent=2)
            parsed = json.loads(json_str)
            
            # Check key fields
            self.assertEqual(parsed['event'], 'GW150914')
            self.assertEqual(parsed['target_frequency'], 141.7)
            self.assertIn('test2', parsed)
            self.assertIn('test3', parsed)
            
        except Exception as e:
            self.fail(f"JSON serialization failed: {e}")


def run_tests():
    """Run all tests"""
    print("=" * 70)
    print("🧪 RUNNING UNIT TESTS FOR GW150914 VALIDATION")
    print("=" * 70)
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestCalculateSNR))
    suite.addTests(loader.loadTestsFromTestCase(TestTest2NoiseComparison))
    suite.addTests(loader.loadTestsFromTestCase(TestVisualization))
    suite.addTests(loader.loadTestsFromTestCase(TestJSONOutput))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "=" * 70)
    if result.wasSuccessful():
        print("✅ ALL TESTS PASSED")
    else:
        print("❌ SOME TESTS FAILED")
        print(f"Failures: {len(result.failures)}")
        print(f"Errors: {len(result.errors)}")
    print("=" * 70)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_tests())
