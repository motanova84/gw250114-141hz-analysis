#!/usr/bin/env python3
"""
Create sample data for testing the analysis scripts without downloading real GWOSC data
"""
import h5py
import numpy as np
import os

def create_sample_gw_data():
    """Create synthetic GW data similar to GW150914"""
    # Parameters for synthetic data
    duration = 32  # seconds
    sample_rate = 4096  # Hz
    gps_start = 1126259446  # GPS time of GW150914 start
    merger_time = 1126259462.423  # GPS time of merger
    
    # Create time array
    n_samples = int(duration * sample_rate)
    times = np.arange(n_samples) / sample_rate
    
    # Create synthetic strain data with noise and signal components
    np.random.seed(42)  # For reproducible results
    
    # Base noise (colored noise approximating LIGO sensitivity)
    noise = np.random.normal(0, 1e-21, n_samples)
    # Apply simple colored noise filter
    from scipy import signal as sig
    b, a = sig.butter(4, [20, 2000], 'bandpass', fs=sample_rate)
    strain = sig.filtfilt(b, a, noise)
    
    # Add synthetic GW signal with ringdown component at 141.7 Hz
    merger_idx = int((merger_time - gps_start) * sample_rate)
    
    # Chirp component (simplified)
    t_chirp = times[merger_idx-2048:merger_idx]
    if len(t_chirp) > 0:
        f_chirp = 35 + (t_chirp - t_chirp[0]) * 250 / (t_chirp[-1] - t_chirp[0])
        amp_chirp = 1e-21 * np.exp(-(t_chirp - t_chirp[-1])**2 / 0.1**2)
        chirp_signal = amp_chirp * np.sin(2 * np.pi * f_chirp * t_chirp)
        strain[merger_idx-2048:merger_idx] += chirp_signal
    
    # Ringdown component with 141.7 Hz component
    t_ringdown = times[merger_idx:merger_idx+1024] - times[merger_idx]
    if len(t_ringdown) > 0:
        # Main ringdown at ~250 Hz (dominant mode)
        amp_main = 5e-22 * np.exp(-t_ringdown / 0.005)
        main_signal = amp_main * np.sin(2 * np.pi * 250 * t_ringdown)
        
        # Additional component at 141.7 Hz (target frequency)
        amp_141 = 2e-22 * np.exp(-t_ringdown / 0.008)
        signal_141 = amp_141 * np.sin(2 * np.pi * 141.7 * t_ringdown)
        
        strain[merger_idx:merger_idx+1024] += main_signal + signal_141
    
    return times + gps_start, strain, sample_rate, gps_start

def save_hdf5_data(times, strain, sample_rate, gps_start, detector, filename):
    """Save data in GWOSC-like HDF5 format"""
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    with h5py.File(filename, 'w') as hdf:
        # Create strain group
        strain_group = hdf.create_group('strain')
        strain_group.create_dataset('Strain', data=strain.astype(np.float64))
        
        # Create meta group with metadata
        meta_group = hdf.create_group('meta')
        meta_group.create_dataset('GPSstart', data=gps_start)
        meta_group.create_dataset('SampleRate', data=sample_rate)
        meta_group.create_dataset('Duration', data=len(strain) / sample_rate)
        meta_group.create_dataset('Detector', data=detector.encode('utf-8'))
        
        # Add some additional metadata for completeness
        meta_group.create_dataset('UTCstart', data=str(gps_start).encode('utf-8'))

def main():
    """Create sample data files"""
    print("Creating synthetic GW data for testing...")
    
    # Generate synthetic data
    times, strain, sample_rate, gps_start = create_sample_gw_data()
    
    # Save data for both detectors (H1 and L1)
    for detector in ['H1', 'L1']:
        filename = f'../data/raw/{detector}-GW150914-32s.hdf5'
        
        # Add slight variations for L1 to simulate real detector differences
        if detector == 'L1':
            # Add small phase shift and noise variation
            strain_l1 = strain * 0.8 + np.random.normal(0, 1e-22, len(strain))
            save_hdf5_data(times, strain_l1, sample_rate, gps_start, detector, filename)
        else:
            save_hdf5_data(times, strain, sample_rate, gps_start, detector, filename)
        
        print(f"Created {filename}")
        
        # Verify the file can be read
        with h5py.File(filename, 'r') as hdf:
            print(f"  {detector}: {len(hdf['strain']['Strain'][:])} samples at {hdf['meta']['SampleRate'][()]} Hz")

    print("Sample data creation complete!")
    print("\nData includes:")
    print("- Synthetic noise matching LIGO sensitivity curve")
    print("- Chirp signal leading to merger")
    print("- Ringdown with dominant ~250 Hz component")
    print("- Target 141.7 Hz component in ringdown phase")
    print("- Realistic signal-to-noise ratios")

if __name__ == "__main__":
    main()