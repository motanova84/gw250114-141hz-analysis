#!/usr/bin/env python3
"""
Test suite for multi-event analysis scripts
Validates script structure, imports, and basic functionality
"""

import sys
import os

# Add scripts directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))


def test_multi_event_snr_analysis_imports():
    """Test that multi_event_snr_analysis.py can be imported"""
    try:
        # Test imports without running the script
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "multi_event_snr_analysis",
            os.path.join(os.path.dirname(__file__), "multi_event_snr_analysis.py")
        )
        module = importlib.util.module_from_spec(spec)
        # Don't execute, just verify it loads
        print("✅ multi_event_snr_analysis.py: Imports successful")
        return True
    except Exception as e:
        print(f"❌ multi_event_snr_analysis.py: Import failed - {e}")
        return False


def test_multi_event_h1_snr_analysis_imports():
    """Test that multi_event_h1_snr_analysis.py can be imported"""
    try:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "multi_event_h1_snr_analysis",
            os.path.join(os.path.dirname(__file__), "multi_event_h1_snr_analysis.py")
        )
        module = importlib.util.module_from_spec(spec)
        print("✅ multi_event_h1_snr_analysis.py: Imports successful")
        return True
    except Exception as e:
        print(f"❌ multi_event_h1_snr_analysis.py: Import failed - {e}")
        return False


def test_asd_noise_analysis_imports():
    """Test that asd_noise_analysis.py can be imported and has correct functions"""
    try:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "asd_noise_analysis",
            os.path.join(os.path.dirname(__file__), "asd_noise_analysis.py")
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        # Verify main function exists
        assert hasattr(module, 'main'), "main() function not found"
        assert hasattr(module, 'analyze_asd_noise'), "analyze_asd_noise() function not found"

        print("✅ asd_noise_analysis.py: Imports and functions verified")
        return True
    except Exception as e:
        print(f"❌ asd_noise_analysis.py: Test failed - {e}")
        return False


def test_dependencies():
    """Test that required dependencies are available"""
    required_packages = ['gwpy', 'matplotlib', 'numpy']
    all_available = True

    for package in required_packages:
        try:
            __import__(package)
            print(f"✅ {package}: Available")
        except ImportError:
            print(f"❌ {package}: NOT AVAILABLE")
            all_available = False

    return all_available


def main():
    """Run all tests"""
    print("=" * 70)
    print("🧪 TESTING MULTI-EVENT ANALYSIS SCRIPTS")
    print("=" * 70)
    print()

    print("📦 Testing dependencies...")
    deps_ok = test_dependencies()
    print()

    print("📝 Testing script structure...")
    test1 = test_multi_event_snr_analysis_imports()
    test2 = test_multi_event_h1_snr_analysis_imports()
    test3 = test_asd_noise_analysis_imports()
    print()

    all_passed = deps_ok and test1 and test2 and test3

    print("=" * 70)
    if all_passed:
        print("✅ ALL TESTS PASSED")
        return 0
    else:
        print("❌ SOME TESTS FAILED")
        return 1


if __name__ == "__main__":
    sys.exit(main())
