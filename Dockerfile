FROM python:3.9-slim

# Configurar entorno
WORKDIR /app
COPY . .

# Instalar dependencias
RUN pip install --upgrade pip && pip install -r requirements.txt

# Ejecutar análisis completo automáticamente
CMD ["make", "analyze"]
