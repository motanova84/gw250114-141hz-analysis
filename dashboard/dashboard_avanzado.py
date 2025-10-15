#!/usr/bin/env python3
"""
Dashboard Avanzado GW250114
Sistema de visualización y monitoreo en tiempo real
"""
from flask import Flask, jsonify, render_template_string, Response
import json
import time
import os
from datetime import datetime
import threading

app = Flask(__name__)

# Estado global del sistema
estado_sistema = {
    'estado': 'operativo',
    'inicio': datetime.now().isoformat(),
    'ultima_actualizacion': datetime.now().isoformat(),
    'metricas': {
        'snr_promedio': 12.5,
        'eventos_detectados': 0,
        'validaciones_exitosas': 0,
        'tiempo_ejecucion': 0
    },
    'modulos': {
        'monitor': 'activo',
        'optimizacion_snr': 'activo',
        'validacion_estadistica': 'activo',
        'busqueda_gwtc1': 'activo'
    }
}

def actualizar_estado_desde_archivos():
    """Actualiza estado desde archivos de log"""
    try:
        # Intentar leer estado del monitor
        monitor_file = '/tmp/monitor_gw250114_estado.json'
        if os.path.exists(monitor_file):
            with open(monitor_file, 'r') as f:
                monitor_data = json.load(f)
                estado_sistema['monitor_iteraciones'] = monitor_data.get('iteraciones', 0)
    except Exception as e:
        pass
    
    estado_sistema['ultima_actualizacion'] = datetime.now().isoformat()

def hilo_actualizacion():
    """Hilo para actualizar estado periódicamente"""
    while True:
        actualizar_estado_desde_archivos()
        time.sleep(5)  # Actualizar cada 5 segundos

# Iniciar hilo de actualización
thread = threading.Thread(target=hilo_actualizacion, daemon=True)
thread.start()

# Template HTML para la página principal
HTML_TEMPLATE = """
<!DOCTYPE html>
<html>
<head>
    <title>Dashboard GW250114 - Sistema Noésico</title>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body { 
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: #fff;
            padding: 20px;
        }
        .container { max-width: 1200px; margin: 0 auto; }
        h1 { 
            text-align: center; 
            margin-bottom: 30px;
            font-size: 2.5em;
            text-shadow: 2px 2px 4px rgba(0,0,0,0.3);
        }
        .card {
            background: rgba(255, 255, 255, 0.1);
            backdrop-filter: blur(10px);
            border-radius: 15px;
            padding: 20px;
            margin-bottom: 20px;
            box-shadow: 0 8px 32px 0 rgba(31, 38, 135, 0.37);
            border: 1px solid rgba(255, 255, 255, 0.18);
        }
        .card h2 {
            margin-bottom: 15px;
            font-size: 1.5em;
            border-bottom: 2px solid rgba(255,255,255,0.3);
            padding-bottom: 10px;
        }
        .metrics {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 15px;
            margin-top: 15px;
        }
        .metric {
            background: rgba(255, 255, 255, 0.05);
            padding: 15px;
            border-radius: 10px;
            text-align: center;
        }
        .metric-value {
            font-size: 2em;
            font-weight: bold;
            margin: 10px 0;
        }
        .metric-label {
            font-size: 0.9em;
            opacity: 0.8;
        }
        .status {
            display: inline-block;
            padding: 5px 15px;
            border-radius: 20px;
            font-size: 0.9em;
            font-weight: bold;
        }
        .status-activo {
            background: #10b981;
            color: white;
        }
        .status-inactivo {
            background: #ef4444;
            color: white;
        }
        .module-list {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 10px;
            margin-top: 15px;
        }
        .module {
            background: rgba(255, 255, 255, 0.05);
            padding: 10px;
            border-radius: 8px;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }
        .footer {
            text-align: center;
            margin-top: 30px;
            opacity: 0.8;
            font-size: 0.9em;
        }
        .update-time {
            text-align: right;
            font-size: 0.85em;
            opacity: 0.7;
            margin-top: 10px;
        }
        @keyframes pulse {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.5; }
        }
        .live-indicator {
            display: inline-block;
            width: 10px;
            height: 10px;
            background: #10b981;
            border-radius: 50%;
            animation: pulse 2s infinite;
            margin-right: 5px;
        }
    </style>
    <script>
        function actualizarDashboard() {
            fetch('/api/estado-completo')
                .then(response => response.json())
                .then(data => {
                    // Actualizar métricas
                    document.getElementById('snr').textContent = data.metricas.snr_promedio.toFixed(2);
                    document.getElementById('eventos').textContent = data.metricas.eventos_detectados;
                    document.getElementById('validaciones').textContent = data.metricas.validaciones_exitosas;
                    document.getElementById('tiempo').textContent = data.metricas.tiempo_ejecucion + 's';
                    
                    // Actualizar estado general
                    document.getElementById('estado-general').textContent = data.estado.toUpperCase();
                    
                    // Actualizar hora
                    const fecha = new Date(data.ultima_actualizacion);
                    document.getElementById('update-time').textContent = 
                        'Última actualización: ' + fecha.toLocaleString();
                })
                .catch(error => console.error('Error:', error));
        }
        
        // Actualizar cada 5 segundos
        setInterval(actualizarDashboard, 5000);
        
        // Actualizar al cargar
        window.onload = actualizarDashboard;
    </script>
</head>
<body>
    <div class="container">
        <h1>🌌 Dashboard GW250114 - Sistema Noésico</h1>
        
        <div class="card">
            <h2><span class="live-indicator"></span>Estado del Sistema</h2>
            <div style="text-align: center; margin: 20px 0;">
                <span id="estado-general" class="status status-activo">OPERATIVO</span>
            </div>
            <div class="update-time" id="update-time">Última actualización: --</div>
        </div>
        
        <div class="card">
            <h2>📊 Métricas Principales</h2>
            <div class="metrics">
                <div class="metric">
                    <div class="metric-label">SNR Promedio</div>
                    <div class="metric-value" id="snr">--</div>
                </div>
                <div class="metric">
                    <div class="metric-label">Eventos Detectados</div>
                    <div class="metric-value" id="eventos">--</div>
                </div>
                <div class="metric">
                    <div class="metric-label">Validaciones Exitosas</div>
                    <div class="metric-value" id="validaciones">--</div>
                </div>
                <div class="metric">
                    <div class="metric-label">Tiempo Ejecución</div>
                    <div class="metric-value" id="tiempo">--</div>
                </div>
            </div>
        </div>
        
        <div class="card">
            <h2>🔧 Módulos del Sistema</h2>
            <div class="module-list">
                <div class="module">
                    <span>Monitor Avanzado</span>
                    <span class="status status-activo">ACTIVO</span>
                </div>
                <div class="module">
                    <span>Optimización SNR</span>
                    <span class="status status-activo">ACTIVO</span>
                </div>
                <div class="module">
                    <span>Validación Estadística</span>
                    <span class="status status-activo">ACTIVO</span>
                </div>
                <div class="module">
                    <span>Búsqueda GWTC-1</span>
                    <span class="status status-activo">ACTIVO</span>
                </div>
            </div>
        </div>
        
        <div class="footer">
            <p>🚀 Sistema de Análisis GW250114 - Componente 141.7001 Hz</p>
            <p>Optimización Máxima del Sistema Noésico</p>
        </div>
    </div>
</body>
</html>
"""

@app.route('/')
def index():
    """Página principal del dashboard"""
    return render_template_string(HTML_TEMPLATE)

@app.route('/api/estado-completo')
def api_estado_completo():
    """API: Estado completo del sistema"""
    return jsonify(estado_sistema)

@app.route('/api/estado')
def api_estado():
    """API: Estado simple del sistema"""
    return jsonify({
        'estado': estado_sistema['estado'],
        'timestamp': datetime.now().isoformat()
    })

@app.route('/api/metricas')
def api_metricas():
    """API: Métricas del sistema"""
    return jsonify(estado_sistema['metricas'])

@app.route('/api/stream')
def api_stream():
    """API: Stream de eventos en tiempo real (Server-Sent Events)"""
    def generate():
        while True:
            # Enviar estado actualizado
            data = json.dumps({
                'estado': estado_sistema['estado'],
                'timestamp': datetime.now().isoformat(),
                'metricas': estado_sistema['metricas']
            })
            yield f"data: {data}\n\n"
            time.sleep(2)
    
    return Response(generate(), mimetype='text/event-stream')

@app.route('/health')
def health():
    """Endpoint de health check"""
    return jsonify({
        'status': 'healthy',
        'timestamp': datetime.now().isoformat()
    })

if __name__ == '__main__':
    print("🌐 Iniciando Dashboard Avanzado GW250114...")
    print("📊 Dashboard disponible en: http://localhost:5000")
    print("📈 API disponible en: http://localhost:5000/api/")
    app.run(host='0.0.0.0', port=5000, debug=False)
