#!/usr/bin/env python3
"""
Validate synthetic gravitational wave datasets

Checks format, physical properties, and signal quality of synthetic datasets.

Author: José Manuel Mota Burruezo (JMMB)
"""

import h5py
import numpy as np
import argparse
from pathlib import Path
from scipy import signal


def validate_hdf5_format(filepath):
    """
    Validate HDF5 file format and structure
    
    Args:
        filepath: Path to HDF5 file
        
    Returns:
        (success, messages): Validation result and messages
    """
    messages = []
    success = True
    
    try:
        with h5py.File(filepath, 'r') as f:
            # Check required groups
            if 'strain' not in f:
                messages.append("❌ Missing 'strain' group")
                success = False
            else:
                messages.append("✅ Found 'strain' group")
                
                # Check required datasets
                required = ['Strain', 'Xstart', 'Xspacing']
                for dataset in required:
                    if dataset not in f['strain']:
                        messages.append(f"❌ Missing 'strain/{dataset}' dataset")
                        success = False
                    else:
                        messages.append(f"✅ Found 'strain/{dataset}'")
            
            # Check metadata (optional but recommended)
            if 'metadata' in f:
                messages.append("✅ Found 'metadata' group")
            else:
                messages.append("⚠️  No 'metadata' group (optional)")
                
    except Exception as e:
        messages.append(f"❌ Error reading file: {e}")
        success = False
    
    return success, messages


def validate_physical_properties(filepath):
    """
    Validate physical properties of the data
    
    Args:
        filepath: Path to HDF5 file
        
    Returns:
        (success, messages): Validation result and messages
    """
    messages = []
    success = True
    
    try:
        with h5py.File(filepath, 'r') as f:
            strain = f['strain/Strain'][:]
            dt = f['strain/Xspacing'][()]
            
            # Sample rate
            sample_rate = 1.0 / dt
            messages.append(f"📊 Sample rate: {sample_rate} Hz")
            
            if sample_rate < 1024:
                messages.append("⚠️  Sample rate < 1024 Hz (may miss high frequencies)")
            elif sample_rate > 16384:
                messages.append("⚠️  Sample rate > 16384 Hz (unusually high)")
            else:
                messages.append("✅ Sample rate in typical range")
            
            # Duration
            duration = len(strain) * dt
            messages.append(f"⏱️  Duration: {duration:.1f} seconds")
            
            if duration < 4:
                messages.append("⚠️  Duration < 4s (may be too short for FFT)")
            else:
                messages.append("✅ Duration adequate for analysis")
            
            # Amplitude check
            rms = np.sqrt(np.mean(strain**2))
            max_val = np.max(np.abs(strain))
            messages.append(f"📈 RMS amplitude: {rms:.2e}")
            messages.append(f"📈 Max amplitude: {max_val:.2e}")
            
            if rms < 1e-23:
                messages.append("⚠️  RMS very low (signal may be too weak)")
            elif rms > 1e-18:
                messages.append("⚠️  RMS very high (check scaling)")
            else:
                messages.append("✅ Amplitude in physical range")
            
            # Check for NaN or Inf
            if np.any(np.isnan(strain)):
                messages.append("❌ Data contains NaN values")
                success = False
            elif np.any(np.isinf(strain)):
                messages.append("❌ Data contains Inf values")
                success = False
            else:
                messages.append("✅ No NaN or Inf values")
                
    except Exception as e:
        messages.append(f"❌ Error validating properties: {e}")
        success = False
    
    return success, messages


def validate_signal_content(filepath, expected_freq=None):
    """
    Validate signal content and frequency
    
    Args:
        filepath: Path to HDF5 file
        expected_freq: Expected signal frequency (Hz) if known
        
    Returns:
        (success, messages): Validation result and messages
    """
    messages = []
    success = True
    
    try:
        with h5py.File(filepath, 'r') as f:
            strain = f['strain/Strain'][:]
            dt = f['strain/Xspacing'][()]
            sample_rate = 1.0 / dt
            
            # Check if frequency is in metadata
            if 'metadata/parameters/frequency' in f:
                meta_freq = f['metadata/parameters/frequency'][()]
                messages.append(f"📌 Metadata frequency: {meta_freq} Hz")
                if expected_freq is None:
                    expected_freq = meta_freq
            
            # Compute FFT
            fft_vals = np.fft.rfft(strain)
            freqs = np.fft.rfftfreq(len(strain), dt)
            psd = np.abs(fft_vals)**2
            
            # Find peak in relevant range (100-500 Hz for typical GW)
            mask = (freqs > 50) & (freqs < 500)
            if np.sum(mask) > 0:
                peak_idx = np.argmax(psd[mask])
                peak_freq = freqs[mask][peak_idx]
                messages.append(f"🎯 Peak frequency: {peak_freq:.2f} Hz")
                
                if expected_freq is not None:
                    freq_error = abs(peak_freq - expected_freq)
                    messages.append(f"   Error from expected: {freq_error:.2f} Hz")
                    
                    if freq_error > 1.0:
                        messages.append(f"⚠️  Peak differs from expected by > 1 Hz")
                    else:
                        messages.append("✅ Peak frequency matches expected")
            else:
                messages.append("⚠️  No significant peak found in 50-500 Hz")
            
            # Estimate SNR
            # Signal: peak region ±5 Hz
            if expected_freq is not None:
                signal_mask = (freqs > expected_freq - 5) & (freqs < expected_freq + 5)
                noise_mask = ((freqs > 50) & (freqs < expected_freq - 10)) | \
                           ((freqs > expected_freq + 10) & (freqs < 500))
                
                if np.sum(signal_mask) > 0 and np.sum(noise_mask) > 0:
                    signal_power = np.mean(psd[signal_mask])
                    noise_power = np.mean(psd[noise_mask])
                    snr = np.sqrt(signal_power / noise_power)
                    messages.append(f"📊 Estimated SNR: {snr:.2f}")
                    
                    if snr < 1.0:
                        messages.append("⚠️  SNR < 1 (signal may be undetectable)")
                    else:
                        messages.append("✅ SNR indicates detectable signal")
                        
    except Exception as e:
        messages.append(f"❌ Error analyzing signal: {e}")
        success = False
    
    return success, messages


def validate_file(filepath, expected_freq=None, verbose=True):
    """
    Perform complete validation of synthetic data file
    
    Args:
        filepath: Path to HDF5 file
        expected_freq: Expected signal frequency (Hz) if known
        verbose: Print detailed messages
        
    Returns:
        overall_success: True if all validations pass
    """
    filepath = Path(filepath)
    
    if verbose:
        print("=" * 70)
        print(f"VALIDATING: {filepath.name}")
        print("=" * 70)
    
    all_success = True
    
    # Format validation
    if verbose:
        print("\n1. FORMAT VALIDATION")
        print("-" * 70)
    success, messages = validate_hdf5_format(filepath)
    all_success = all_success and success
    if verbose:
        for msg in messages:
            print(f"  {msg}")
    
    # Physical properties
    if verbose:
        print("\n2. PHYSICAL PROPERTIES")
        print("-" * 70)
    success, messages = validate_physical_properties(filepath)
    all_success = all_success and success
    if verbose:
        for msg in messages:
            print(f"  {msg}")
    
    # Signal content
    if verbose:
        print("\n3. SIGNAL CONTENT")
        print("-" * 70)
    success, messages = validate_signal_content(filepath, expected_freq)
    all_success = all_success and success
    if verbose:
        for msg in messages:
            print(f"  {msg}")
    
    # Overall result
    if verbose:
        print("\n" + "=" * 70)
        if all_success:
            print("✅ VALIDATION PASSED")
        else:
            print("❌ VALIDATION FAILED")
        print("=" * 70)
    
    return all_success


def main():
    parser = argparse.ArgumentParser(
        description='Validate synthetic gravitational wave datasets'
    )
    parser.add_argument('--input', type=str,
                       help='Input HDF5 file to validate')
    parser.add_argument('--all', action='store_true',
                       help='Validate all files in data/synthetic/')
    parser.add_argument('--expected-freq', type=float,
                       help='Expected signal frequency (Hz)')
    parser.add_argument('--quiet', action='store_true',
                       help='Suppress detailed output')
    
    args = parser.parse_args()
    
    if not args.input and not args.all:
        parser.error("Must specify --input or --all")
    
    verbose = not args.quiet
    
    if args.all:
        # Validate all synthetic datasets
        synthetic_dir = Path('data/synthetic')
        if not synthetic_dir.exists():
            print(f"❌ Directory not found: {synthetic_dir}")
            return
        
        hdf5_files = list(synthetic_dir.glob('*.hdf5'))
        if not hdf5_files:
            print(f"⚠️  No HDF5 files found in {synthetic_dir}")
            return
        
        print(f"Found {len(hdf5_files)} HDF5 files to validate\n")
        
        results = {}
        for filepath in hdf5_files:
            success = validate_file(filepath, args.expected_freq, verbose)
            results[filepath.name] = success
            if verbose:
                print()
        
        # Summary
        print("=" * 70)
        print("VALIDATION SUMMARY")
        print("=" * 70)
        for filename, success in results.items():
            status = "✅ PASS" if success else "❌ FAIL"
            print(f"  {status}  {filename}")
        
        total_pass = sum(results.values())
        print(f"\nTotal: {total_pass}/{len(results)} passed")
        
    else:
        # Validate single file
        filepath = Path(args.input)
        if not filepath.exists():
            print(f"❌ File not found: {filepath}")
            return
        
        validate_file(filepath, args.expected_freq, verbose)


if __name__ == '__main__':
    main()
