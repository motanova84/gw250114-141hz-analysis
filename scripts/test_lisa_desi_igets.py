#!/usr/bin/env python3
"""
Test script for LISA-DESI-IGETS implementations

This script verifies that all three validation pipelines can be imported
and their key functions work correctly.
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def test_imports():
    """Test that all required packages can be imported."""
    print("Testing imports...")
    
    try:
        import numpy as np
        print("  ✓ numpy")
    except ImportError as e:
        print(f"  ✗ numpy: {e}")
        return False
    
    try:
        import scipy
        print("  ✓ scipy")
    except ImportError as e:
        print(f"  ✗ scipy: {e}")
        return False
    
    try:
        import matplotlib
        print("  ✓ matplotlib")
    except ImportError as e:
        print(f"  ✗ matplotlib: {e}")
        return False
    
    # Optional dependencies
    try:
        import emcee
        print("  ✓ emcee (optional)")
    except ImportError:
        print("  ⚠ emcee not installed (optional for MCMC)")
    
    try:
        import healpy
        print("  ✓ healpy (optional)")
    except ImportError:
        print("  ⚠ healpy not installed (optional for cosmology)")
    
    return True


def test_desi_script():
    """Test DESI analysis functions."""
    print("\nTesting DESI analysis...")
    
    try:
        # Import the script as a module
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'desi'))
        import desi_wz_analysis as desi
        
        # Test hubble_parameter function
        import numpy as np
        z = np.array([0.0, 0.5, 1.0])
        E_z = desi.hubble_parameter(z, w0=-1.0, wa=0.0)
        
        assert len(E_z) == len(z), "Output length mismatch"
        assert E_z[0] > 0, "E(z=0) should be positive"
        assert all(E_z > 0), "All E(z) values should be positive"
        
        print(f"  ✓ hubble_parameter: E(z=0)={E_z[0]:.3f}, E(z=1)={E_z[2]:.3f}")
        
        # Test mock data generation
        z_data, E_data, E_err = desi.generate_desi_mock_data(n_points=10)
        assert len(z_data) == 10, "Mock data length mismatch"
        assert all(E_err > 0), "All errors should be positive"
        
        print(f"  ✓ generate_desi_mock_data: {len(z_data)} points generated")
        
        return True
        
    except Exception as e:
        print(f"  ✗ DESI test failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def test_notebooks_syntax():
    """Test that notebooks have valid JSON syntax."""
    print("\nTesting notebook syntax...")
    
    import json
    notebooks = [
        ('LISA', '../lisa/lisa_search_pipeline.ipynb'),
        ('IGETS', '../igets/igets_fft_analysis.ipynb')
    ]
    
    all_valid = True
    for name, path in notebooks:
        try:
            full_path = os.path.join(os.path.dirname(__file__), path)
            with open(full_path, 'r') as f:
                nb = json.load(f)
            
            # Check basic structure
            assert 'cells' in nb, f"{name} notebook missing 'cells'"
            assert 'metadata' in nb, f"{name} notebook missing 'metadata'"
            
            # Count code cells
            code_cells = sum(1 for cell in nb['cells'] if cell['cell_type'] == 'code')
            print(f"  ✓ {name} notebook: {len(nb['cells'])} cells ({code_cells} code)")
            
        except Exception as e:
            print(f"  ✗ {name} notebook failed: {e}")
            all_valid = False
    
    return all_valid


def test_file_structure():
    """Test that all required files exist."""
    print("\nTesting file structure...")
    
    base_dir = os.path.join(os.path.dirname(__file__), '..')
    
    required_files = [
        'lisa/lisa_search_pipeline.ipynb',
        'lisa/README.md',
        'desi/desi_wz_analysis.py',
        'desi/README.md',
        'igets/igets_fft_analysis.ipynb',
        'igets/README.md',
        'LISA_DESI_IGETS_README.md',
        'requirements.txt'
    ]
    
    all_exist = True
    for file_path in required_files:
        full_path = os.path.join(base_dir, file_path)
        if os.path.exists(full_path):
            size = os.path.getsize(full_path)
            print(f"  ✓ {file_path} ({size:,} bytes)")
        else:
            print(f"  ✗ {file_path} NOT FOUND")
            all_exist = False
    
    return all_exist


def main():
    """Run all tests."""
    print("="*70)
    print("LISA-DESI-IGETS Implementation Tests")
    print("="*70)
    
    results = {
        'File structure': test_file_structure(),
        'Imports': test_imports(),
        'Notebook syntax': test_notebooks_syntax(),
        'DESI script': test_desi_script()
    }
    
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    
    for test_name, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{test_name:<30} {status}")
    
    all_passed = all(results.values())
    
    print("="*70)
    if all_passed:
        print("✓ ALL TESTS PASSED")
        return 0
    else:
        print("✗ SOME TESTS FAILED")
        return 1


if __name__ == '__main__':
    sys.exit(main())
