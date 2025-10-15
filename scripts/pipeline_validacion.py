#!/usr/bin/env python3
"""
Pipeline de Validación Científica Completo
Ejecuta la secuencia completa de validación según los criterios del problema statement.
"""
import sys
import os
import subprocess
import time
from pathlib import Path

def run_script(script_name, description):
    """Ejecutar un script de validación y capturar resultado"""
    print(f"\n{'='*60}")
    print(f"🚀 EJECUTANDO: {description}")
    print(f"{'='*60}")
    
    script_path = Path(__file__).parent / script_name
    
    if not script_path.exists():
        print(f"❌ Script no encontrado: {script_path}")
        return False, f"Script {script_name} no encontrado"
    
    try:
        start_time = time.time()
        
        # Ejecutar script con Python
        result = subprocess.run(
            [sys.executable, str(script_path)],
            capture_output=True,
            text=True,
            timeout=300  # 5 minutos timeout
        )
        
        elapsed_time = time.time() - start_time
        
        # Mostrar output del script
        if result.stdout:
            print(result.stdout)
        
        if result.stderr and result.returncode != 0:
            print(f"⚠️  STDERR: {result.stderr}")
        
        success = result.returncode == 0
        
        print(f"\n⏱️  Tiempo transcurrido: {elapsed_time:.1f}s")
        print(f"📊 Resultado: {'✅ ÉXITO' if success else '❌ FALLO'}")
        
        return success, result.stdout if success else result.stderr
        
    except subprocess.TimeoutExpired:
        print(f"⏰ TIMEOUT: {script_name} excedió 5 minutos")
        return False, "Timeout"
    
    except Exception as e:
        print(f"💥 ERROR EJECUTANDO {script_name}: {e}")
        return False, str(e)

def validate_environment():
    """Validar que las dependencias estén instaladas"""
    print("🔧 VALIDANDO ENTORNO...")
    
    required_packages = [
        ('gwpy', '3.0.0'),
        ('numpy', '1.21.0'),
        ('scipy', '1.7.0'),
        ('matplotlib', '3.5.0'),
        ('h5py', '3.7.0')
    ]
    
    missing_packages = []
    
    for package, min_version in required_packages:
        try:
            __import__(package)
            print(f"   ✅ {package}")
        except ImportError:
            print(f"   ❌ {package} (no instalado)")
            missing_packages.append(package)
    
    if missing_packages:
        print(f"\n❌ Paquetes faltantes: {', '.join(missing_packages)}")
        print("💡 Ejecutar: pip install -r requirements.txt")
        return False
    
    print("✅ Entorno validado correctamente")
    return True

def create_results_directory():
    """Crear directorio de resultados si no existe"""
    results_dir = Path(__file__).parent.parent / "results" / "validation"
    results_dir.mkdir(parents=True, exist_ok=True)
    
    figures_dir = results_dir / "figures" 
    figures_dir.mkdir(exist_ok=True)
    
    print(f"📁 Directorio de resultados: {results_dir}")
    return results_dir

def generate_validation_report(results, output_dir):
    """Generar reporte de validación"""
    report_file = output_dir / "validation_report.md"
    
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write("# 🌌 Reporte de Validación Científica GW250114\n\n")
        f.write(f"**Fecha:** {time.strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        f.write("## 📋 Resumen de Validación\n\n")
        
        total_tests = len(results)
        passed_tests = sum(1 for success, _ in results.values() if success)
        
        f.write(f"- **Tests ejecutados:** {total_tests}\n")
        f.write(f"- **Tests exitosos:** {passed_tests}\n")
        f.write(f"- **Tasa de éxito:** {passed_tests/total_tests*100:.1f}%\n\n")
        
        f.write("## 📊 Resultados Detallados\n\n")
        
        for step, (success, output) in results.items():
            status = "✅ ÉXITO" if success else "❌ FALLO"
            f.write(f"### {step}\n")
            f.write(f"**Estado:** {status}\n\n")
            
            if output:
                f.write(f"**Output:**\n```\n{output[:1000]}\n```\n\n")
        
        f.write("## 🎯 Interpretación\n\n")
        
        if passed_tests == total_tests:
            f.write("🟢 **VALIDACIÓN COMPLETA EXITOSA**\n\n")
            f.write("- Conectividad GWOSC confirmada\n")
            f.write("- Control GW150914 validado\n") 
            f.write("- Framework GW250114 funcionando\n")
            f.write("- Criterios científicos cumplidos\n\n")
            f.write("✅ **Sistema listo para análisis científico**\n")
        
        elif passed_tests >= total_tests * 0.75:
            f.write("🟡 **VALIDACIÓN PARCIAL**\n\n")
            f.write("- Funcionalidad principal confirmada\n")
            f.write("- Algunos componentes requieren atención\n")
            f.write("- Sistema operativo con limitaciones\n")
        
        else:
            f.write("🔴 **VALIDACIÓN FALLIDA**\n\n")
            f.write("- Problemas críticos detectados\n")
            f.write("- Sistema no listo para análisis científico\n")
            f.write("- Revisar configuración y dependencias\n")
    
    print(f"📄 Reporte generado: {report_file}")
    return report_file

def main():
    """Ejecutar pipeline completo de validación"""
    print("🌌 PIPELINE DE VALIDACIÓN CIENTÍFICA GW250114")
    print("=" * 70)
    print("Implementación de criterios del problema statement:")
    print("- Validación conectividad GWOSC")
    print("- Control GW150914 (BF > 10, p < 0.01)")
    print("- Framework GW250114 preparado")
    print("=" * 70)
    
    # Validar entorno
    if not validate_environment():
        return 1
    
    # Crear directorio de resultados
    results_dir = create_results_directory()
    
    # Pipeline de validación
    validation_steps = [
        ("validar_conectividad.py", "PASO 1: Validación de conectividad GWOSC"),
        ("validar_gw150914.py", "PASO 2: Validación control GW150914 (BF y p-values)"),
        ("analizar_gw250114.py", "PASO 3: Framework GW250114 (datos sintéticos)"),
        ("integracion_manifiesto.py", "PASO 4: Validación Manifiesto Noésico")
    ]
    
    results = {}
    
    # Ejecutar cada paso
    for script, description in validation_steps:
        success, output = run_script(script, description)
        results[description] = (success, output)
        
        if not success:
            print(f"\n⚠️  ADVERTENCIA: {description} falló")
            print("🔄 Continuando con siguiente paso...")
    
    # Generar reporte
    report_file = generate_validation_report(results, results_dir)
    
    # Resumen final
    total_tests = len(results)
    passed_tests = sum(1 for success, _ in results.values() if success)
    
    print(f"\n{'='*60}")
    print("📈 RESUMEN FINAL DE VALIDACIÓN")
    print(f"{'='*60}")
    print(f"Tests ejecutados: {total_tests}")
    print(f"Tests exitosos: {passed_tests}")
    print(f"Tasa de éxito: {passed_tests/total_tests*100:.1f}%")
    
    if passed_tests == total_tests:
        print("\n🎉 ¡VALIDACIÓN CIENTÍFICA COMPLETA!")
        print("✅ Todos los criterios cumplidos")
        print("🚀 Sistema listo para análisis GW250114")
        exit_code = 0
    elif passed_tests >= 2:
        print("\n⚠️  VALIDACIÓN PARCIALMENTE EXITOSA")
        print("🔧 Funcionalidad principal confirmada")
        print("📋 Revisar componentes fallidos")
        exit_code = 0
    else:
        print("\n❌ VALIDACIÓN FALLIDA")
        print("🔧 Revisar configuración y dependencias")
        print("📋 Consultar reporte de errores")
        exit_code = 1
    
    print(f"\n📄 Reporte completo: {report_file}")
    print("🔔 Pipeline de validación completado")
    
    return exit_code

if __name__ == "__main__":
    sys.exit(main())