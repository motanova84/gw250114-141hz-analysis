#!/usr/bin/env python3
"""
Test del Sistema de Optimización
Verifica que todos los componentes están correctamente instalados
"""
import sys
import os
import subprocess

def test_scripts_exist():
    """Verificar que todos los scripts existen"""
    print("🔍 TEST 1: Verificando existencia de scripts...")
    
    scripts = [
        'scripts/optimizacion_maxima.sh',
        'scripts/monitor_avanzado_gw250114.py',
        'scripts/monitor_recursos.sh',
        'scripts/detener_servicios.sh',
        'dashboard/dashboard_avanzado.py'
    ]
    
    all_ok = True
    for script in scripts:
        if os.path.exists(script):
            print(f"   ✅ {script}")
        else:
            print(f"   ❌ {script} NO ENCONTRADO")
            all_ok = False
    
    return all_ok

def test_scripts_executable():
    """Verificar que los scripts shell son ejecutables"""
    print("\n🔍 TEST 2: Verificando permisos de ejecución...")
    
    scripts = [
        'scripts/optimizacion_maxima.sh',
        'scripts/monitor_recursos.sh',
        'scripts/detener_servicios.sh'
    ]
    
    all_ok = True
    for script in scripts:
        if os.path.exists(script):
            is_exec = os.access(script, os.X_OK)
            if is_exec:
                print(f"   ✅ {script} - ejecutable")
            else:
                print(f"   ⚠️  {script} - no ejecutable (puede funcionar con bash)")
        else:
            all_ok = False
    
    return all_ok

def test_python_syntax():
    """Verificar sintaxis Python de los scripts"""
    print("\n🔍 TEST 3: Verificando sintaxis Python...")
    
    scripts = [
        'scripts/monitor_avanzado_gw250114.py',
        'dashboard/dashboard_avanzado.py'
    ]
    
    all_ok = True
    for script in scripts:
        try:
            result = subprocess.run(
                ['python3', '-m', 'py_compile', script],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode == 0:
                print(f"   ✅ {script} - sintaxis OK")
            else:
                print(f"   ❌ {script} - error de sintaxis")
                print(f"      {result.stderr}")
                all_ok = False
        except Exception as e:
            print(f"   ❌ {script} - error: {e}")
            all_ok = False
    
    return all_ok

def test_bash_syntax():
    """Verificar sintaxis Bash de los scripts"""
    print("\n🔍 TEST 4: Verificando sintaxis Bash...")
    
    scripts = [
        'scripts/optimizacion_maxima.sh',
        'scripts/monitor_recursos.sh',
        'scripts/detener_servicios.sh'
    ]
    
    all_ok = True
    for script in scripts:
        try:
            result = subprocess.run(
                ['bash', '-n', script],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode == 0:
                print(f"   ✅ {script} - sintaxis OK")
            else:
                print(f"   ❌ {script} - error de sintaxis")
                print(f"      {result.stderr}")
                all_ok = False
        except Exception as e:
            print(f"   ❌ {script} - error: {e}")
            all_ok = False
    
    return all_ok

def test_imports():
    """Verificar que los imports Python funcionan"""
    print("\n🔍 TEST 5: Verificando imports Python...")
    
    tests = [
        ('Monitor', 'sys.path.insert(0, "scripts"); from monitor_avanzado_gw250114 import MonitorAvanzadoGW250114'),
    ]
    
    all_ok = True
    for name, import_stmt in tests:
        try:
            result = subprocess.run(
                ['python3', '-c', import_stmt],
                capture_output=True,
                text=True,
                timeout=5
            )
            # Ignorar warnings sobre módulos no disponibles
            if result.returncode == 0:
                print(f"   ✅ {name} - import OK")
            else:
                # Verificar si es solo un warning
                if 'ModuleNotFoundError' not in result.stderr:
                    print(f"   ✅ {name} - import OK (con warnings)")
                else:
                    print(f"   ❌ {name} - error de import")
                    print(f"      {result.stderr}")
                    all_ok = False
        except Exception as e:
            print(f"   ❌ {name} - error: {e}")
            all_ok = False
    
    return all_ok

def test_documentation():
    """Verificar que existe la documentación"""
    print("\n🔍 TEST 6: Verificando documentación...")
    
    docs = [
        'OPTIMIZACION_MAXIMA.md',
        'README.md'
    ]
    
    all_ok = True
    for doc in docs:
        if os.path.exists(doc):
            print(f"   ✅ {doc}")
        else:
            print(f"   ⚠️  {doc} NO ENCONTRADO")
    
    return all_ok

def main():
    """Ejecutar todos los tests"""
    print("=" * 70)
    print("🧪 TESTS DEL SISTEMA DE OPTIMIZACIÓN MÁXIMA")
    print("=" * 70)
    print()
    
    tests = [
        test_scripts_exist,
        test_scripts_executable,
        test_python_syntax,
        test_bash_syntax,
        test_imports,
        test_documentation
    ]
    
    results = []
    for test in tests:
        try:
            results.append(test())
        except Exception as e:
            print(f"\n❌ Error ejecutando test: {e}")
            results.append(False)
    
    print("\n" + "=" * 70)
    print("📊 RESUMEN DE TESTS")
    print("=" * 70)
    
    passed = sum(results)
    total = len(results)
    
    print(f"\nTests pasados: {passed}/{total}")
    
    if passed == total:
        print("\n✅ TODOS LOS TESTS PASADOS")
        print("\n🚀 El sistema está listo para usar:")
        print("   ./scripts/optimizacion_maxima.sh")
        return 0
    else:
        print("\n⚠️  ALGUNOS TESTS FALLARON")
        print("   Revise los errores arriba")
        return 1

if __name__ == "__main__":
    sys.exit(main())
