#!/bin/bash
# detener_servicios.sh
# Script para detener todos los servicios del sistema de optimización

echo "🛑 DETENIENDO SERVICIOS DEL SISTEMA NOÉSICO"
echo "==========================================="
echo ""

# Colores
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

print_success() {
    echo -e "${GREEN}✅ $1${NC}"
}

print_warning() {
    echo -e "${YELLOW}⚠️  $1${NC}"
}

print_error() {
    echo -e "${RED}❌ $1${NC}"
}

# Función para detener proceso por PID file
detener_por_pid() {
    local pid_file=$1
    local nombre=$2
    
    if [ -f "$pid_file" ]; then
        local pid=$(cat "$pid_file")
        if ps -p "$pid" > /dev/null 2>&1; then
            kill "$pid" 2>/dev/null
            sleep 1
            
            if ps -p "$pid" > /dev/null 2>&1; then
                kill -9 "$pid" 2>/dev/null
                print_warning "$nombre detenido forzosamente"
            else
                print_success "$nombre detenido correctamente"
            fi
        else
            print_warning "$nombre no estaba corriendo"
        fi
        rm -f "$pid_file"
    else
        print_warning "Archivo PID de $nombre no encontrado"
    fi
}

# Detener monitor avanzado
echo "🔧 Deteniendo Monitor Avanzado..."
detener_por_pid "/tmp/monitor_avanzado.pid" "Monitor Avanzado"

# Detener monitor de recursos
echo "📊 Deteniendo Monitor de Recursos..."
detener_por_pid "/tmp/monitor_recursos.pid" "Monitor de Recursos"

# Detener dashboard
echo "🌐 Deteniendo Dashboard..."
detener_por_pid "/tmp/dashboard.pid" "Dashboard"

# También intentar detener gunicorn si está corriendo
if pgrep -f "gunicorn.*dashboard" > /dev/null 2>&1; then
    echo "🔧 Deteniendo procesos Gunicorn..."
    pkill -f "gunicorn.*dashboard" && print_success "Gunicorn detenido" || print_warning "No se pudo detener Gunicorn"
fi

# Limpiar archivos temporales
echo ""
echo "🧹 Limpiando archivos temporales..."
rm -f /tmp/monitor_avanzado.log /tmp/monitor_recursos.log /tmp/dashboard.log
rm -f /tmp/dashboard_access.log /tmp/dashboard_error.log
rm -f /tmp/monitor_gw250114_estado.json /tmp/monitor_recursos_gw250114.log
print_success "Archivos temporales limpiados"

echo ""
echo "✅ TODOS LOS SERVICIOS DETENIDOS"
echo ""
