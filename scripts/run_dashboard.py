#!/usr/bin/env python3
"""
Script conveniente para ejecutar el dashboard de GW250114
Permite ejecutar desde cualquier directorio del proyecto
"""
import os
import sys

# Asegurar que estamos en el directorio correcto
script_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.dirname(script_dir)
os.chdir(project_root)

# Importar y ejecutar la aplicación
from dashboard.estado_gw250114 import app

if __name__ == '__main__':
    print("🌌 Iniciando Dashboard GW250114...")
    print(f"📁 Directorio de trabajo: {os.getcwd()}")
    print(f"🌐 Dashboard disponible en: http://localhost:5000/monitor-gw")
    print(f"📊 API JSON disponible en: http://localhost:5000/estado-gw250114")
    print()
    print("Presiona Ctrl+C para detener el servidor")
    print("-" * 60)
    # Only enable debug in development (controlled by environment variable)
    debug_mode = os.getenv('FLASK_DEBUG', 'False').lower() in ('true', '1', 't')
    app.run(debug=debug_mode, host='0.0.0.0', port=5000)
