#!/bin/bash
echo "🔍 Verificando estado del repositorio..."
echo ""

# Verificar estructura
echo "📁 Estructura de archivos:"
find . -maxdepth 2 -type f -name "*.py" -o -name "*.md" -o -name "*.txt" | sort

echo ""
echo "📊 Figuras generadas:"
ls -la results/figures/ 2>/dev/null || echo "Directorio results/figures/ no encontrado"

echo ""
echo "🐍 Entorno Python:"
python --version
python -c "import gwpy; print(f'GWPy: {gwpy.__version__}')" 2>/dev/null || echo "GWPy no instalado"

echo ""
echo "✅ Verificación completada. Repositorio listo para ciencia!"