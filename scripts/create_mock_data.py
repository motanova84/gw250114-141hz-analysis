#!/usr/bin/env python3
"""
Mock figure generation for testing README automation
"""
import matplotlib.pyplot as plt
import numpy as np
import os

def create_mock_h1_spectrum():
    """Create a mock H1 spectrum figure"""
    plt.figure(figsize=(10, 6))
    
    # Generate mock frequency spectrum
    freqs = np.linspace(130, 160, 1000)
    # Create a realistic-looking spectrum with noise and a peak around 141.7 Hz
    spectrum = np.exp(-(freqs - 141.7)**2 / 2) * 0.5 + np.random.normal(0, 0.1, len(freqs)) + 2
    
    plt.semilogy(freqs, spectrum, 'b-', alpha=0.8, linewidth=1.5, label='H1 Spectrum')
    plt.axvline(141.7, color='green', linestyle='--', linewidth=2, label='141.7 Hz Objetivo')
    plt.axvline(141.69, color='red', linestyle='--', linewidth=2, label='Detectado: 141.69 Hz')
    
    plt.xlim(130, 160)
    plt.xlabel('Frecuencia (Hz)')
    plt.ylabel('ASD (1/√Hz)')
    plt.title('Espectro H1 - GW150914 Análisis')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('results/figures/analisis_avanzado_H1.png', dpi=300, bbox_inches='tight')
    plt.close()
    print("✅ Created analisis_avanzado_H1.png")

def create_mock_l1_comparison():
    """Create a mock L1 comparison figure"""
    plt.figure(figsize=(10, 6))
    
    freqs = np.linspace(130, 160, 1000)
    spectrum = np.exp(-(freqs - 141.75)**2 / 2) * 0.3 + np.random.normal(0, 0.08, len(freqs)) + 1.5
    
    plt.semilogy(freqs, spectrum, 'b-', alpha=0.8, label='L1')
    plt.axvline(141.7, color='r', linestyle='--', label='141.7 Hz objetivo')
    plt.axvline(141.75, color='g', linestyle='--', label='L1: 141.75 Hz')
    
    plt.xlim(130, 160)
    plt.xlabel('Frecuencia (Hz)')
    plt.ylabel('ASD (1/√Hz)')
    plt.title('Comparación L1 - Componente en 141.7 Hz')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('results/figures/comparacion_L1.png', dpi=150, bbox_inches='tight')
    plt.close()
    print("✅ Created comparacion_L1.png")

def create_mock_ringdown_analysis():
    """Create mock ringdown analysis figure"""
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Time series
    t = np.linspace(0, 32, 1000)
    strain = np.sin(2*np.pi*141.7*t) * np.exp(-t/10) + np.random.normal(0, 0.1, len(t))
    axes[0,0].plot(t, strain)
    axes[0,0].set_title('GW150914 H1 Strain Data')
    axes[0,0].set_xlabel('Time (s)')
    axes[0,0].set_ylabel('Strain')
    axes[0,0].grid(True, alpha=0.3)
    
    # Spectrum
    freqs = np.linspace(100, 200, 500)
    psd = np.exp(-(freqs - 141.7)**2 / 10) + np.random.exponential(0.1, len(freqs))
    axes[0,1].loglog(freqs, psd)
    axes[0,1].axvline(141.7, color='r', linestyle='--')
    axes[0,1].set_title('Power Spectral Density')
    axes[0,1].set_xlabel('Frequency (Hz)')
    axes[0,1].set_ylabel('PSD')
    axes[0,1].grid(True, alpha=0.3)
    
    # Spectrogram
    f = np.linspace(130, 160, 100)
    t_spec = np.linspace(0, 5, 200)
    Sxx = np.random.rand(len(f), len(t_spec))
    # Add a line at 141.7 Hz
    idx_141 = np.argmin(np.abs(f - 141.7))
    Sxx[idx_141, :] *= 3
    
    im = axes[1,0].pcolormesh(t_spec, f, Sxx, shading='gouraud', cmap='viridis')
    axes[1,0].axhline(141.7, color='red', linestyle='--', alpha=0.9)
    axes[1,0].set_title('Spectrogram')
    axes[1,0].set_xlabel('Time (s)')
    axes[1,0].set_ylabel('Frequency (Hz)')
    plt.colorbar(im, ax=axes[1,0])
    
    # Q-transform style
    axes[1,1].pcolormesh(t_spec, f, Sxx, shading='gouraud', cmap='plasma')
    axes[1,1].axhline(141.7, color='white', linestyle='--', alpha=0.9)
    axes[1,1].set_title('Q-Transform')
    axes[1,1].set_xlabel('Time (s)')
    axes[1,1].set_ylabel('Frequency (Hz)')
    
    plt.tight_layout()
    plt.savefig('results/figures/H1_GW150914_analysis.png', dpi=200, bbox_inches='tight')
    plt.close()
    print("✅ Created H1_GW150914_analysis.png")

def create_mock_results_files():
    """Create mock JSON results files"""
    import json
    
    h1_results = {
        'detector': 'H1',
        'frequency': '141.69',
        'snr': '7.47',
        'difference': '0.010',
        'status': '✅ Confirmado',
        'timestamp': 1126259462.0
    }
    
    l1_results = {
        'detector': 'L1', 
        'frequency': '141.75',
        'snr': '0.95',
        'difference': '0.050',
        'status': '✅ Confirmado',
        'timestamp': 1126259462.0
    }
    
    os.makedirs('results', exist_ok=True)
    
    with open('results/H1_results.json', 'w') as f:
        json.dump(h1_results, f, indent=2)
    
    with open('results/L1_results.json', 'w') as f:
        json.dump(l1_results, f, indent=2)
    
    print("✅ Created results JSON files")

if __name__ == "__main__":
    print("🎨 Generating mock figures for testing...")
    
    create_mock_h1_spectrum()
    create_mock_l1_comparison() 
    create_mock_ringdown_analysis()
    create_mock_results_files()
    
    print("\n✅ All mock data created successfully!")
    print("Now run: python scripts/update_readme.py")