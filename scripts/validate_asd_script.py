#!/usr/bin/env python3
"""
Script de validación para analizar_asd_141hz.py
===============================================

Valida la estructura y sintaxis del script sin ejecutarlo.
No requiere dependencias externas.
"""

import ast
import os
import sys


def validate_python_syntax(filepath):
    """Validar sintaxis de Python."""
    print(f"📝 Validando sintaxis de {os.path.basename(filepath)}...")
    
    try:
        with open(filepath, 'r') as f:
            code = f.read()
        
        ast.parse(code)
        print("   ✅ Sintaxis válida")
        return True
    except SyntaxError as e:
        print(f"   ❌ Error de sintaxis: {e}")
        return False


def check_required_functions(filepath):
    """Verificar que existan las funciones requeridas."""
    print(f"\n🔍 Verificando funciones requeridas...")
    
    required_functions = [
        'download_segment',
        'calculate_asd',
        'extract_asd_at_frequency',
        'analyze_detector_pair',
        'plot_asd_comparison',
        'save_results_to_file',
        'analyze_gw150914',
        'main'
    ]
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    all_found = True
    for func_name in required_functions:
        if f"def {func_name}(" in content:
            print(f"   ✅ {func_name}")
        else:
            print(f"   ❌ {func_name} no encontrada")
            all_found = False
    
    return all_found


def check_docstrings(filepath):
    """Verificar que las funciones tengan docstrings."""
    print(f"\n📚 Verificando documentación...")
    
    with open(filepath, 'r') as f:
        tree = ast.parse(f.read())
    
    functions_with_docs = 0
    total_functions = 0
    
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            total_functions += 1
            if ast.get_docstring(node):
                functions_with_docs += 1
    
    percentage = (functions_with_docs / total_functions * 100) if total_functions > 0 else 0
    
    print(f"   Funciones con docstrings: {functions_with_docs}/{total_functions} ({percentage:.1f}%)")
    
    if percentage >= 80:
        print("   ✅ Buena documentación")
        return True
    else:
        print("   ⚠️  Considerar agregar más docstrings")
        return False


def check_constants(filepath):
    """Verificar que las constantes estén definidas."""
    print(f"\n🔢 Verificando constantes...")
    
    required_constants = [
        'GW150914_GPS_TIME',
        'TARGET_FREQUENCY'
    ]
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    all_found = True
    for const in required_constants:
        if const in content:
            # Extraer valor
            for line in content.split('\n'):
                if line.startswith(const):
                    print(f"   ✅ {line.strip()}")
                    break
        else:
            print(f"   ❌ {const} no encontrada")
            all_found = False
    
    return all_found


def check_imports(filepath):
    """Verificar que se importen los módulos necesarios."""
    print(f"\n📦 Verificando imports...")
    
    required_imports = [
        'argparse',
        'numpy',
        'gwpy',
        'matplotlib'
    ]
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    all_found = True
    for module in required_imports:
        if f"import {module}" in content or f"from {module}" in content:
            print(f"   ✅ {module}")
        else:
            print(f"   ⚠️  {module} no importado directamente")
    
    return all_found


def check_command_line_interface(filepath):
    """Verificar que tenga interfaz de línea de comandos."""
    print(f"\n⌨️  Verificando interfaz CLI...")
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    checks = [
        ('ArgumentParser', 'argparse.ArgumentParser'),
        ('--duration', 'opción --duration'),
        ('--control-days', 'opción --control-days'),
        ('--output-dir', 'opción --output-dir'),
        ('--no-plot', 'opción --no-plot'),
        ('--verbose', 'opción --verbose')
    ]
    
    all_found = True
    for check, desc in checks:
        if check in content:
            print(f"   ✅ {desc}")
        else:
            print(f"   ❌ {desc} no encontrada")
            all_found = False
    
    return all_found


def check_test_file(filepath):
    """Verificar archivo de test."""
    print(f"\n🧪 Validando archivo de test...")
    
    if not os.path.exists(filepath):
        print(f"   ❌ Archivo no encontrado: {filepath}")
        return False
    
    # Validar sintaxis
    try:
        with open(filepath, 'r') as f:
            ast.parse(f.read())
        print("   ✅ Sintaxis válida")
    except SyntaxError as e:
        print(f"   ❌ Error de sintaxis: {e}")
        return False
    
    # Contar clases de test
    with open(filepath, 'r') as f:
        tree = ast.parse(f.read())
    
    test_classes = 0
    test_methods = 0
    
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef) and node.name.startswith('Test'):
            test_classes += 1
        if isinstance(node, ast.FunctionDef) and node.name.startswith('test_'):
            test_methods += 1
    
    print(f"   ✅ Clases de test: {test_classes}")
    print(f"   ✅ Métodos de test: {test_methods}")
    
    return test_classes > 0 and test_methods > 0


def main():
    """Ejecutar todas las validaciones."""
    print("🌌 VALIDACIÓN DE SCRIPT DE ANÁLISIS ASD 141.7 Hz")
    print("=" * 70)
    
    script_path = 'scripts/analizar_asd_141hz.py'
    test_path = 'scripts/test_analizar_asd_141hz.py'
    
    if not os.path.exists(script_path):
        print(f"❌ Script no encontrado: {script_path}")
        return 1
    
    results = []
    
    # Validaciones del script principal
    results.append(("Sintaxis", validate_python_syntax(script_path)))
    results.append(("Funciones", check_required_functions(script_path)))
    results.append(("Documentación", check_docstrings(script_path)))
    results.append(("Constantes", check_constants(script_path)))
    results.append(("Imports", check_imports(script_path)))
    results.append(("CLI", check_command_line_interface(script_path)))
    
    # Validación del archivo de test
    results.append(("Tests", check_test_file(test_path)))
    
    # Resumen
    print("\n" + "=" * 70)
    print("📊 RESUMEN DE VALIDACIÓN")
    print("=" * 70)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for check_name, result in results:
        status = "✅" if result else "❌"
        print(f"{status} {check_name}")
    
    print("\n" + "=" * 70)
    print(f"Resultado: {passed}/{total} checks pasaron ({passed/total*100:.1f}%)")
    
    if passed == total:
        print("✅ VALIDACIÓN EXITOSA - Script listo para usar")
        return 0
    else:
        print("⚠️  VALIDACIÓN PARCIAL - Revisar checks fallidos")
        return 1


if __name__ == '__main__':
    sys.exit(main())
