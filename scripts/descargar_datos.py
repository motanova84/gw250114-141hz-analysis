#!/usr/bin/env python3
"""
Script para descargar datos de GWOSC para GW150914 (control)
"""
from gwpy.timeseries import TimeSeries
import os

def main():
    # Crear directorio de datos si no existe
    os.makedirs('../data/raw', exist_ok=True)
    
    # Para GW150914 (control - datos reales disponibles)
    print("Descargando datos de control GW150914...")
    try:
        # Datos de 32 segundos alrededor del merger
        gps_gw150914 = 1126259462  # Tiempo GPS del merger
        duration = 32  # segundos
        start = gps_gw150914 - 16
        end = gps_gw150914 + 16
        
        # Descargar datos de ambos detectores
        for detector in ['H1', 'L1']:
            print(f"Descargando {detector}...")
            data = TimeSeries.fetch_open_data(
                detector, start, end, sample_rate=4096, cache=True, verbose=True
            )
            # Guardar en formato HDF5
            filename = f'../data/raw/{detector}-GW150914-32s.hdf5'
            data.write(filename, overwrite=True)
            print(f"Datos guardados en {filename}")
            
    except Exception as e:
        print(f"Error descargando datos: {e}")
        print("¿Estás conectado a internet?")
    
    print("¡Descarga completada!")

if __name__ == "__main__":
    main()
