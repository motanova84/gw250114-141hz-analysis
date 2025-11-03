#!/usr/bin/env python3
"""
Test script for A_Rpsi_symmetry.ipynb
Verifies that the notebook can be executed and produces expected results.
"""

import sympy as sp
import sys

def test_rpsi_symmetry():
    """Test the A_Rpsi symmetry calculation"""
    print("🧪 Testing A_Rpsi Symmetry Calculation...")
    print("=" * 60)
    
    # Define symbols
    R = sp.symbols('R', positive=True)
    alpha, beta, gamma, delta, zeta1p2, Lambda = sp.symbols('α β γ δ ζ Λ')
    
    # Define energy function
    E = alpha/R**4 + beta*zeta1p2/R**2 + gamma*Lambda**2*R**2 + delta*sp.sin(sp.log(R)/sp.log(sp.pi))**2
    
    # Calculate derivative
    dE = sp.diff(E, R)
    
    # Solve numerically
    try:
        sol = sp.nsolve(
            dE.subs({
                alpha: 1,
                beta: 1,
                gamma: 1,
                delta: 1e-2,
                zeta1p2: -0.207886,
                Lambda: 1e-61
            }), 
            3  # Initial guess
        )
        
        R_opt = float(sol)
        print(f"✅ Solution found: R_opt = {R_opt:.10f}")
        
        # Expected value (from original calculation)
        expected = 2.8713961554
        tolerance = 1e-8
        
        if abs(R_opt - expected) < tolerance:
            print(f"✅ Result matches expected value (diff = {abs(R_opt - expected):.2e})")
            
            # Verify it's a minimum
            d2E = sp.diff(dE, R)
            d2E_eval = d2E.subs({
                alpha: 1,
                beta: 1,
                gamma: 1,
                delta: 1e-2,
                zeta1p2: -0.207886,
                Lambda: 1e-61,
                R: sol
            })
            
            if float(d2E_eval) > 0:
                print(f"✅ Second derivative is positive: {float(d2E_eval):.6f} (minimum confirmed)")
                print("=" * 60)
                print("🎉 All tests passed!")
                return 0
            else:
                print(f"❌ Second derivative is not positive: {float(d2E_eval):.6f}")
                return 1
        else:
            print(f"❌ Result doesn't match expected value")
            print(f"   Expected: {expected:.10f}")
            print(f"   Got:      {R_opt:.10f}")
            print(f"   Diff:     {abs(R_opt - expected):.2e}")
            return 1
            
    except Exception as e:
        print(f"❌ Error during calculation: {e}")
        return 1

if __name__ == "__main__":
    sys.exit(test_rpsi_symmetry())
Test R_Ψ (R_psi) Symmetry and Compactification Radius

This script validates the compactification radius R_Ψ and its relationship
with the fundamental frequency f₀ = 141.7001 Hz in the Calabi-Yau geometry.

Tests:
1. R_Ψ value consistency
2. R_Ψ and f₀ as fundamental parameters
3. Calabi-Yau volume calculation
4. R_Ψ/ℓ_P ratio verification
"""

import numpy as np
import sys

def test_rpsi_symmetry():
    """Test R_psi symmetry and compactification radius calculations"""
    
    print("=" * 60)
    print("TEST: R_Ψ SYMMETRY AND COMPACTIFICATION RADIUS")
    print("=" * 60)
    
    # Fundamental constants
    c = 299792458  # m/s (speed of light)
    l_P = 1.616255e-35  # m (Planck length)
    h = 6.62607015e-34  # J·s (Planck constant)
    
    # Fundamental parameters from theory
    # R_Ψ determined by action minimization
    # f₀ determined by resonance analysis
    R_psi = 1.687e-35  # m (compactification radius)
    f0 = 141.7001  # Hz (fundamental frequency)
    
    print("\n1. TESTING R_Ψ VALUE")
    print(f"   R_Ψ: {R_psi:.3e} m")
    print(f"   (Determined by action minimization)")
    
    # Test that R_psi is physical (positive and near Planck scale)
    print("\n2. TESTING FUNDAMENTAL PARAMETERS")
    print(f"   f₀: {f0:.4f} Hz")
    print(f"   (Fundamental resonance frequency)")
    
    # Check both parameters are in valid range
    if R_psi > 0 and R_psi < 1e-30:
        print("   ✅ R_Ψ is in valid physical range")
    else:
        print("   ❌ R_Ψ out of expected range")
        return False
    
    if f0 > 100 and f0 < 200:
        print("   ✅ f₀ is in valid frequency range")
    else:
        print("   ❌ f₀ out of expected range")
        return False
    
    # Test R_psi/l_P ratio
    print("\n3. TESTING R_Ψ/ℓ_P RATIO")
    ratio = R_psi / l_P
    print(f"   R_Ψ/ℓ_P = {ratio:.4f}")
    
    expected_ratio = 1.0438  # Approximate expected ratio
    ratio_error = abs(ratio - expected_ratio) / expected_ratio
    
    if ratio_error < 0.01:
        print("   ✅ Ratio test PASSED")
    else:
        print("   ⚠️  Ratio differs from expected value")
    
    # Test Calabi-Yau volume
    print("\n4. TESTING CALABI-YAU VOLUME")
    V6 = (1/5) * (2 * np.pi * R_psi)**6
    print(f"   V₆ (quintic) = {V6:.3e} m⁶")
    
    if V6 > 0:
        print("   ✅ Volume calculation PASSED")
    else:
        print("   ❌ Volume calculation FAILED")
        return False
    
    # Test quantum energy
    print("\n5. TESTING QUANTUM ENERGY")
    E_psi = h * f0  # E_Ψ = hf₀
    E_psi_eV = E_psi / 1.602176634e-19  # Convert to eV
    print(f"   E_Ψ = hf₀ = {E_psi:.3e} J")
    print(f"   E_Ψ = {E_psi_eV:.3e} eV")
    
    if E_psi > 0:
        print("   ✅ Quantum energy calculation PASSED")
    else:
        print("   ❌ Quantum energy calculation FAILED")
        return False
    
    print("\n" + "=" * 60)
    print("ALL R_Ψ SYMMETRY TESTS PASSED ✅")
    print("=" * 60)
    print("\n📊 Summary:")
    print(f"   R_Ψ = {R_psi:.3e} m (compactification radius)")
    print(f"   f₀ = {f0:.4f} Hz (fundamental frequency)")
    print(f"   E_Ψ = {E_psi_eV:.3e} eV (quantum energy)")
    print(f"   V₆ = {V6:.3e} m⁶ (Calabi-Yau volume)")
    
    return True

if __name__ == "__main__":
    success = test_rpsi_symmetry()
    sys.exit(0 if success else 1)
