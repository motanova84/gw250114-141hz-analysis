#!/usr/bin/env python3
"""
Test unitario para el script de potencial de energía del vacío
"""
import os
import sys
import numpy as np
from scipy.optimize import minimize_scalar

def test_E_vac_function():
    """Prueba la función E_vac para verificar comportamiento correcto"""
    print("🧪 Test: Verificando función E_vac_log")
    
    # Parámetros constantes
    beta = -0.207886
    gamma = 1.0
    Lambda = 1e-61
    delta = 0.1
    pi_val = np.pi
    
    def E_vac_log(logR):
        R = 10**logR
        term1 = 1 / R**4
        term2 = beta / R**2
        term3 = gamma * Lambda**2 * R**2
        term4 = delta * np.sin(np.log(R) / np.log(pi_val))**2
        return term1 + term2 + term3 + term4
    
    # Test 1: Verificar que la función devuelve valores numéricos válidos
    try:
        val = E_vac_log(43.0)
        assert np.isfinite(val), "E_vac debe devolver un valor finito"
        assert val > 0, "E_vac debe ser positivo en el rango de interés"
        print("   ✅ Test 1 PASSED: Función devuelve valores válidos")
    except Exception as e:
        print(f"   ❌ Test 1 FAILED: {e}")
        return False
    
    # Test 2: Verificar que el mínimo existe en el rango [40, 50]
    try:
        res = minimize_scalar(E_vac_log, bounds=(40, 50), method='bounded')
        assert res.success, "La minimización debe converger"
        assert 40 <= res.x <= 50, "El mínimo debe estar en el rango [40, 50]"
        print(f"   ✅ Test 2 PASSED: Mínimo encontrado en log10(R/lP) = {res.x:.4f}")
    except Exception as e:
        print(f"   ❌ Test 2 FAILED: {e}")
        return False
    
    # Test 3: Verificar que el valor en el mínimo es menor que en los extremos
    try:
        E_min = E_vac_log(res.x)
        E_40 = E_vac_log(40.0)
        E_50 = E_vac_log(50.0)
        assert E_min < E_40, "El mínimo debe ser menor que el valor en 40"
        assert E_min < E_50, "El mínimo debe ser menor que el valor en 50"
        print(f"   ✅ Test 3 PASSED: Valor mínimo E_vac = {E_min:.2e}")
    except Exception as e:
        print(f"   ❌ Test 3 FAILED: {e}")
        return False
    
    # Test 4: Verificar que los términos individuales tienen el orden de magnitud esperado
    try:
        logR_test = 43.73
        R = 10**logR_test
        term1 = 1 / R**4
        term2 = beta / R**2
        term3 = gamma * Lambda**2 * R**2
        term4 = delta * np.sin(np.log(R) / np.log(pi_val))**2
        
        # El término 1/R^4 debe ser positivo
        assert term1 > 0, "Término 1/R^4 debe ser positivo"
        # El término beta/R^2 debe ser negativo (beta < 0)
        assert term2 < 0, "Término beta/R^2 debe ser negativo"
        # El término cosmológico debe ser muy pequeño en magnitud absoluta
        assert abs(term3) < 1e-30, "Término cosmológico debe ser muy pequeño"
        # El término log-periódico debe estar acotado entre 0 y delta
        assert 0 <= term4 <= delta, "Término log-periódico debe estar acotado"
        
        print("   ✅ Test 4 PASSED: Todos los términos tienen el orden de magnitud correcto")
    except Exception as e:
        print(f"   ❌ Test 4 FAILED: {e}")
        return False
    
    print("\n✅ Todos los tests pasaron correctamente")
    return True


def test_plot_generation():
    """Prueba que el script genera el gráfico correctamente"""
    print("\n🧪 Test: Verificando generación de gráfico")
    
    # Ejecutar el script
    script_path = os.path.join(os.path.dirname(__file__), 'potencial_evac.py')
    
    # Eliminar plot anterior si existe
    if os.path.exists('potential_plot.png'):
        os.remove('potential_plot.png')
    
    # Ejecutar script
    import subprocess
    result = subprocess.run([sys.executable, script_path], 
                          capture_output=True, 
                          text=True,
                          cwd=os.path.dirname(os.path.dirname(script_path)))
    
    if result.returncode != 0:
        print(f"   ❌ Test FAILED: Script falló con código {result.returncode}")
        print(f"   Error: {result.stderr}")
        return False
    
    # Verificar que el plot fue creado
    if not os.path.exists('potential_plot.png'):
        print("   ❌ Test FAILED: Plot no fue creado")
        return False
    
    # Verificar que el plot tiene tamaño razonable (> 10KB)
    size = os.path.getsize('potential_plot.png')
    if size < 10000:
        print(f"   ❌ Test FAILED: Plot muy pequeño ({size} bytes)")
        return False
    
    print(f"   ✅ Test PASSED: Plot generado correctamente ({size} bytes)")
    return True


if __name__ == "__main__":
    print("=" * 80)
    print("TEST: potencial_evac.py")
    print("=" * 80)
    
    success = True
    success = test_E_vac_function() and success
    success = test_plot_generation() and success
    
    print("\n" + "=" * 80)
    if success:
        print("✅ TODOS LOS TESTS PASARON")
        sys.exit(0)
    else:
        print("❌ ALGUNOS TESTS FALLARON")
        sys.exit(1)
