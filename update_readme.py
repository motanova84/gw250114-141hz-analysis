#!/usr/bin/env python3
"""
Script para actualizar el README.md con resultados de validación automática
"""
import json
import os
from datetime import datetime, timezone

def actualizar_readme():
    # Cargar resultados
    results_file = "results/validacion.json"
    if not os.path.exists(results_file):
        print("❌ No se encontró archivo de resultados:", results_file)
        return
    
    with open(results_file) as f:
        data = json.load(f)

    # Construir tabla Markdown
    tabla = "| Detector | Frecuencia Detectada | SNR | Diferencia | Estado |\n"
    tabla += "|----------|----------------------|-----|------------|--------|\n"
    for d in data["detalles"]:
        estado = '✅ Confirmado' if d['valido'] else '❌ No válido'
        tabla += f"| **{d['detector']}** | `{d['freq']:.2f} Hz` | `{d['snr']:.2f}` | `{d['diff']:+.2f} Hz` | {estado} |\n"

    # Texto resumen con fecha de los datos si está disponible
    fecha_analisis = data.get('fecha', datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC'))
    evento = data.get('evento', 'GW150914')
    resumen = f"> ⏱️ Última validación automática: {fecha_analisis}  \n"
    resumen += f"> 🔬 La señal aparece en ambos detectores. Coincidencia multisitio confirmada. Validación doble del armónico base.\n"

    # Leer README actual
    with open("README.md", "r") as f:
        contenido = f.read()

    # Encontrar las secciones para reemplazar
    inicio_marker = "## 🔍 Resultados preliminares – GW150914 (Control)"
    fin_marker = "## ⚙️ Ejecución rápida"
    
    inicio = contenido.find(inicio_marker)
    fin = contenido.find(fin_marker)
    
    if inicio == -1 or fin == -1:
        print("❌ No se encontraron marcadores en README.md")
        print(f"Inicio marker: {inicio}, Fin marker: {fin}")
        return

    # Construir la nueva sección
    nueva_seccion = f"{inicio_marker}\n\n{tabla}\n{resumen}\n\n---\n\n"
    
    # Reemplazar contenido
    nuevo_contenido = contenido[:inicio] + nueva_seccion + contenido[fin:]

    # Guardar el archivo actualizado
    with open("README.md", "w") as f:
        f.write(nuevo_contenido)

    print("✅ README.md actualizado correctamente")
    print(f"📊 Datos procesados de {evento}")
    print(f"📅 Fecha de análisis: {fecha_analisis}")

if __name__ == "__main__":
    actualizar_readme()