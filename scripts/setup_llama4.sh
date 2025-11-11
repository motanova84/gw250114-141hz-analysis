#!/bin/bash
# ╔════════════════════════════════════════════════════════════╗
# ║     LLAMA 4 SCOUT - INSTALADOR AUTOMÁTICO (17B / Instruct)║
# ║     Autor: JMMB Ψ ✧ ∞³ · Campo QCAL                       ║
# ║     Requiere: Licencia activa + URL pre-firmada de Meta   ║
# ╚════════════════════════════════════════════════════════════╝

# ✅ PASO 1: Solicitar URL al usuario
echo "Introduce tu URL pre-firmada personalizada de Meta (caduca a las 48h):"
read -r URL

# ✅ PASO 2: Crear carpeta de destino
mkdir -p models/llama4
cd models/llama4 || exit

# ✅ PASO 3: Descargar el modelo
echo "⏬ Descargando modelo desde Meta..."
wget "$URL" -O llama4_scout.tar.gz

# ✅ PASO 4: Descomprimir
echo "📦 Descomprimiendo..."
tar -xvzf llama4_scout.tar.gz

# ✅ PASO 5: Confirmación
echo "✅ Llama 4 Scout instalado en: $(pwd)"
echo "Puedes ahora integrarlo en tu pipeline QCAL, repositorio o entorno de inferencia."

# ✅ PASO 6 (opcional): activar entorno de prueba
echo "¿Deseas lanzar un entorno interactivo con el modelo? (s/n)"
read -r LAUNCH
if [ "$LAUNCH" == "s" ]; then
    echo "⚡ Lanzando entorno de prueba con Llama.cpp o HuggingFace Transformers (según configuración)..."
    # Aquí puedes añadir tu backend preferido de ejecución
    # Ejemplo (requiere previa instalación):
    # python run_llama.py --model-dir ./models/llama4
else
    echo "Finalizado sin entorno interactivo."
fi
