#!/bin/bash
# Monitor de Recursos del Sistema
# Monitorea CPU, memoria, disco y red del sistema noésico

# Configuración
INTERVALO=5  # segundos entre chequeos
LOG_FILE="/tmp/monitor_recursos_gw250114.log"

# Colores
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Función para obtener uso de CPU
obtener_cpu() {
    if command -v top &> /dev/null; then
        # Usar top para obtener CPU usage
        top -bn1 | grep "Cpu(s)" | sed "s/.*, *\([0-9.]*\)%* id.*/\1/" | awk '{print 100 - $1}'
    else
        echo "N/A"
    fi
}

# Función para obtener uso de memoria
obtener_memoria() {
    if [ -f /proc/meminfo ]; then
        total=$(grep MemTotal /proc/meminfo | awk '{print $2}')
        available=$(grep MemAvailable /proc/meminfo | awk '{print $2}')
        usado=$((total - available))
        porcentaje=$(awk "BEGIN {printf \"%.2f\", ($usado/$total)*100}")
        echo "$porcentaje"
    else
        echo "N/A"
    fi
}

# Función para obtener uso de disco
obtener_disco() {
    if command -v df &> /dev/null; then
        df -h / | awk 'NR==2 {print $5}' | sed 's/%//'
    else
        echo "N/A"
    fi
}

# Función para obtener número de procesos
obtener_procesos() {
    if command -v ps &> /dev/null; then
        ps aux | wc -l
    else
        echo "N/A"
    fi
}

# Función para formatear timestamp
timestamp() {
    date '+%Y-%m-%d %H:%M:%S'
}

# Función de monitoreo principal
monitorear() {
    local cpu=$(obtener_cpu)
    local memoria=$(obtener_memoria)
    local disco=$(obtener_disco)
    local procesos=$(obtener_procesos)
    local ts=$(timestamp)
    
    # Formatear línea de log
    log_line="[$ts] CPU: ${cpu}% | MEM: ${memoria}% | DISK: ${disco}% | PROC: $procesos"
    
    # Guardar en log
    echo "$log_line" >> "$LOG_FILE"
    
    # Imprimir en consola con colores
    printf "[$ts] "
    
    # CPU
    if (( $(echo "$cpu > 80" | bc -l 2>/dev/null || echo "0") )); then
        printf "${RED}CPU: ${cpu}%%${NC} | "
    elif (( $(echo "$cpu > 50" | bc -l 2>/dev/null || echo "0") )); then
        printf "${YELLOW}CPU: ${cpu}%%${NC} | "
    else
        printf "${GREEN}CPU: ${cpu}%%${NC} | "
    fi
    
    # Memoria
    if (( $(echo "$memoria > 80" | bc -l 2>/dev/null || echo "0") )); then
        printf "${RED}MEM: ${memoria}%%${NC} | "
    elif (( $(echo "$memoria > 60" | bc -l 2>/dev/null || echo "0") )); then
        printf "${YELLOW}MEM: ${memoria}%%${NC} | "
    else
        printf "${GREEN}MEM: ${memoria}%%${NC} | "
    fi
    
    # Disco
    if (( $(echo "$disco > 90" | bc -l 2>/dev/null || echo "0") )); then
        printf "${RED}DISK: ${disco}%%${NC} | "
    elif (( $(echo "$disco > 75" | bc -l 2>/dev/null || echo "0") )); then
        printf "${YELLOW}DISK: ${disco}%%${NC} | "
    else
        printf "${GREEN}DISK: ${disco}%%${NC} | "
    fi
    
    # Procesos
    printf "PROC: $procesos\n"
}

# Función para limpiar al salir
cleanup() {
    echo ""
    echo "🛑 Monitor de recursos detenido"
    echo "📊 Log guardado en: $LOG_FILE"
    exit 0
}

# Capturar señales
trap cleanup SIGINT SIGTERM

# Banner inicial
echo "📊 MONITOR DE RECURSOS GW250114"
echo "================================"
echo "Intervalo: ${INTERVALO}s"
echo "Log: $LOG_FILE"
echo "================================"
echo ""

# Crear log si no existe
touch "$LOG_FILE"

# Loop de monitoreo
while true; do
    monitorear
    sleep "$INTERVALO"
done
