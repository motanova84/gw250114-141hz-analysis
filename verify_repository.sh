#!/bin/bash
# Repository verification script

echo "🔍 VERIFICACIÓN DEL REPOSITORIO - GW250114 141.7 Hz Analysis"
echo "============================================================="

# Check file structure
echo ""
echo "📁 Archivos Python (.py):"
find . -name "*.py" -not -path "./venv/*" | sort

echo ""
echo "📄 Archivos Markdown (.md):"
find . -name "*.md" | sort

echo ""
echo "📋 Archivos de configuración (.txt):"
find . -name "*.txt" | sort

# Check results/figures directory
echo ""
echo "📊 Directorio results/figures:"
if [ -d "results/figures" ]; then
    echo "✅ Existe"
    echo "Tamaño total: $(du -sh results/figures 2>/dev/null | cut -f1 || echo '0')"
    echo "Archivos:"
    ls -la results/figures/ 2>/dev/null || echo "  (vacío o sin permisos)"
else
    echo "❌ No existe"
fi

# Check data directory
echo ""
echo "🗄️ Directorio data/raw:"
if [ -d "data/raw" ]; then
    echo "✅ Existe"
    echo "Tamaño total: $(du -sh data/raw 2>/dev/null | cut -f1 || echo '0')"
    echo "Archivos:"
    ls -la data/raw/ 2>/dev/null || echo "  (vacío o sin permisos)"
else
    echo "❌ No existe"
fi

# Python environment check
echo ""
echo "🐍 Versiones de librerías:"
if command -v python3 &> /dev/null; then
    python3 -c "
try:
    import gwpy
    print(f'✅ gwpy: {gwpy.__version__}')
except ImportError:
    print('❌ gwpy: No instalado')

try:
    import numpy
    print(f'✅ numpy: {numpy.__version__}')
except ImportError:
    print('❌ numpy: No instalado')
    
try:
    import scipy
    print(f'✅ scipy: {scipy.__version__}')
except ImportError:
    print('❌ scipy: No instalado')

try:
    import matplotlib
    print(f'✅ matplotlib: {matplotlib.__version__}')
except ImportError:
    print('❌ matplotlib: No instalado')
"
else
    echo "❌ Python3 no disponible"
fi

echo ""
echo "🔗 Enlaces y URLs:"
if [ -f "README.md" ]; then
    echo "✅ README.md existe"
    grep -n "http" README.md || echo "  No hay enlaces externos"
else
    echo "❌ README.md no existe"
fi

echo ""
echo "🏷️ Git status:"
git status --porcelain 2>/dev/null | head -5 || echo "No es un repositorio git o no hay cambios"

echo ""
echo "✅ VERIFICACIÓN COMPLETADA"
echo "============================================================="