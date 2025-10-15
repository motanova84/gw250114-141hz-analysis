#!/bin/bash
# optimizacion_maxima.sh
# Script de Optimización Máxima del Sistema Noésico GW250114

echo "🚀 OPTIMIZACIÓN MÁXIMA DEL SISTEMA NOÉSICO"
echo "==========================================="
echo ""

# Detectar directorio del script
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Colores para output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Función para imprimir con color
print_success() {
    echo -e "${GREEN}✅ $1${NC}"
}

print_error() {
    echo -e "${RED}❌ $1${NC}"
}

print_warning() {
    echo -e "${YELLOW}⚠️  $1${NC}"
}

print_info() {
    echo -e "${BLUE}ℹ️  $1${NC}"
}

# Verificar si se está ejecutando como root para algunas operaciones
if [ "$EUID" -ne 0 ]; then 
    print_warning "Algunas optimizaciones requieren privilegios de root (sudo)"
    print_info "Continuando con optimizaciones que no requieren root..."
    HAS_ROOT=0
else
    HAS_ROOT=1
fi

# 1. Optimización del sistema
echo "🔧 OPTIMIZANDO SISTEMA..."
if [ $HAS_ROOT -eq 1 ]; then
    # Optimizaciones de red para mejor rendimiento
    sysctl -w net.core.rmem_max=268435456 2>/dev/null && print_success "Buffer de recepción maximizado" || print_warning "No se pudo optimizar buffer de recepción"
    sysctl -w net.core.wmem_max=268435456 2>/dev/null && print_success "Buffer de envío maximizado" || print_warning "No se pudo optimizar buffer de envío"
    sysctl -w net.ipv4.tcp_rmem="4096 87380 268435456" 2>/dev/null && print_success "TCP rmem configurado" || print_warning "No se pudo configurar TCP rmem"
    sysctl -w net.ipv4.tcp_wmem="4096 65536 268435456" 2>/dev/null && print_success "TCP wmem configurado" || print_warning "No se pudo configurar TCP wmem"
else
    print_info "Saltando optimizaciones de sistema (requieren root)"
    print_info "Para aplicarlas, ejecute: sudo $0"
fi
echo ""

# 2. Configuración de máxima prioridad
echo "🎯 CONFIGURANDO MÁXIMA PRIORIDAD..."

# Verificar si Python está disponible
if ! command -v python3 &> /dev/null; then
    print_error "Python3 no está instalado"
    exit 1
fi

# Activar entorno virtual si existe
if [ -d "$SCRIPT_DIR/../venv" ]; then
    source "$SCRIPT_DIR/../venv/bin/activate" 2>/dev/null || true
    print_success "Entorno virtual activado"
fi

# Iniciar monitor avanzado en background
if [ -f "$SCRIPT_DIR/monitor_avanzado_gw250114.py" ]; then
    if [ $HAS_ROOT -eq 1 ]; then
        nice -n -20 python3 "$SCRIPT_DIR/monitor_avanzado_gw250114.py" > /tmp/monitor_avanzado.log 2>&1 &
    else
        python3 "$SCRIPT_DIR/monitor_avanzado_gw250114.py" > /tmp/monitor_avanzado.log 2>&1 &
    fi
    MONITOR_PID=$!
    
    # Guardar PID para control posterior
    echo $MONITOR_PID > /tmp/monitor_avanzado.pid
    print_success "Monitor avanzado iniciado (PID: $MONITOR_PID)"
    
    # Verificar que el proceso está corriendo
    sleep 1
    if ps -p $MONITOR_PID > /dev/null 2>&1; then
        print_success "Monitor verificado y funcionando"
    else
        print_warning "Monitor podría no haber iniciado correctamente"
    fi
else
    print_error "Script monitor_avanzado_gw250114.py no encontrado"
fi
echo ""

# 3. Monitoreo de recursos
echo "📊 INICIANDO MONITOREO DE RECURSOS..."
if [ -f "$SCRIPT_DIR/monitor_recursos.sh" ]; then
    # Hacer el script ejecutable si no lo es
    chmod +x "$SCRIPT_DIR/monitor_recursos.sh" 2>/dev/null
    
    # Iniciar monitor de recursos en background
    nohup "$SCRIPT_DIR/monitor_recursos.sh" > /tmp/monitor_recursos.log 2>&1 &
    RECURSOS_PID=$!
    echo $RECURSOS_PID > /tmp/monitor_recursos.pid
    print_success "Monitor de recursos iniciado (PID: $RECURSOS_PID)"
    
    # Verificar que el proceso está corriendo
    sleep 1
    if ps -p $RECURSOS_PID > /dev/null 2>&1; then
        print_success "Monitor de recursos verificado"
    else
        print_warning "Monitor de recursos podría no haber iniciado correctamente"
    fi
else
    print_error "Script monitor_recursos.sh no encontrado"
fi
echo ""

# 4. Dashboard de alta performance
echo "🌐 INICIANDO DASHBOARD AVANZADO..."

# Verificar si Flask y gunicorn están instalados
if ! python3 -c "import flask" 2>/dev/null; then
    print_warning "Flask no está instalado. Instalando..."
    pip install flask --quiet 2>/dev/null || print_error "Error instalando Flask"
fi

if ! command -v gunicorn &> /dev/null; then
    print_warning "Gunicorn no está instalado. Instalando..."
    pip install gunicorn --quiet 2>/dev/null || print_error "Error instalando Gunicorn"
fi

# Verificar que el módulo dashboard existe
if [ -f "$SCRIPT_DIR/../dashboard/dashboard_avanzado.py" ]; then
    # Cambiar al directorio del proyecto para que los imports funcionen
    cd "$SCRIPT_DIR/.." || exit 1
    
    # Iniciar dashboard con gunicorn
    if command -v gunicorn &> /dev/null; then
        gunicorn -w 4 -b 0.0.0.0:5000 dashboard.dashboard_avanzado:app --daemon --pid /tmp/dashboard.pid --access-logfile /tmp/dashboard_access.log --error-logfile /tmp/dashboard_error.log
        
        if [ $? -eq 0 ]; then
            print_success "Dashboard iniciado con Gunicorn (4 workers)"
        else
            print_warning "Error con Gunicorn, intentando con Flask directamente..."
            python3 -m dashboard.dashboard_avanzado > /tmp/dashboard.log 2>&1 &
            DASHBOARD_PID=$!
            echo $DASHBOARD_PID > /tmp/dashboard.pid
            print_success "Dashboard iniciado con Flask (PID: $DASHBOARD_PID)"
        fi
    else
        print_warning "Gunicorn no disponible, usando Flask directamente..."
        python3 -m dashboard.dashboard_avanzado > /tmp/dashboard.log 2>&1 &
        DASHBOARD_PID=$!
        echo $DASHBOARD_PID > /tmp/dashboard.pid
        print_success "Dashboard iniciado con Flask (PID: $DASHBOARD_PID)"
    fi
else
    print_error "Módulo dashboard no encontrado"
fi
echo ""

# 5. Verificación del sistema
echo "✅ VERIFICANDO SISTEMA OPTIMIZADO..."
sleep 2

# Verificar que los procesos están corriendo
PROCESOS_OK=0

if [ -f /tmp/monitor_avanzado.pid ]; then
    MONITOR_PID=$(cat /tmp/monitor_avanzado.pid)
    if ps -p $MONITOR_PID > /dev/null 2>&1; then
        print_success "Monitor avanzado: ACTIVO"
        PROCESOS_OK=$((PROCESOS_OK + 1))
    else
        print_warning "Monitor avanzado: INACTIVO"
    fi
fi

if [ -f /tmp/monitor_recursos.pid ]; then
    RECURSOS_PID=$(cat /tmp/monitor_recursos.pid)
    if ps -p $RECURSOS_PID > /dev/null 2>&1; then
        print_success "Monitor de recursos: ACTIVO"
        PROCESOS_OK=$((PROCESOS_OK + 1))
    else
        print_warning "Monitor de recursos: INACTIVO"
    fi
fi

# Verificar dashboard
if [ -f /tmp/dashboard.pid ]; then
    DASHBOARD_PID=$(cat /tmp/dashboard.pid)
    if ps -p $DASHBOARD_PID > /dev/null 2>&1; then
        print_success "Dashboard: ACTIVO"
        PROCESOS_OK=$((PROCESOS_OK + 1))
    else
        print_warning "Dashboard: INACTIVO"
    fi
fi

# Verificar conectividad al dashboard
sleep 1
if command -v curl &> /dev/null; then
    if curl -s http://localhost:5000/health > /dev/null 2>&1; then
        print_success "Dashboard responde correctamente"
        echo ""
        echo "📊 Estado del sistema:"
        curl -s http://localhost:5000/api/estado-completo | python3 -m json.tool 2>/dev/null || echo "  (No se pudo obtener estado completo)"
    else
        print_warning "Dashboard no responde en puerto 5000"
    fi
else
    print_info "curl no disponible para verificar dashboard"
fi

echo ""
echo "🎉 SISTEMA OPTIMIZADO AL MÁXIMO"
echo "================================"
echo "📊 Dashboard: http://localhost:5000"
echo "📈 Stream: http://localhost:5000/api/stream"
echo "🔧 Monitor: scripts/monitor_avanzado_gw250114.py"
echo ""
echo "📝 Logs disponibles en:"
echo "   • /tmp/monitor_avanzado.log"
echo "   • /tmp/monitor_recursos.log"
echo "   • /tmp/dashboard.log (o /tmp/dashboard_error.log)"
echo ""
echo "🛑 Para detener todos los servicios, ejecute:"
echo "   kill \$(cat /tmp/monitor_avanzado.pid /tmp/monitor_recursos.pid /tmp/dashboard.pid 2>/dev/null)"
echo ""

if [ $PROCESOS_OK -ge 2 ]; then
    print_success "Sistema operativo con $PROCESOS_OK/3 componentes activos"
    exit 0
else
    print_warning "Sistema operativo con solo $PROCESOS_OK/3 componentes activos"
    print_info "Revise los logs para más detalles"
    exit 0
fi
