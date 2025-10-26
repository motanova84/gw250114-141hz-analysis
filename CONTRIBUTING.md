# 🤝 Guía de Contribución

¡Gracias por tu interés en contribuir al análisis GW250114-141Hz! Este documento describe cómo contribuir efectivamente al proyecto.

## 🤖 Colaboradores Automatizados

Este proyecto cuenta con **8 bots inteligentes** que te ayudarán durante el proceso de contribución:

- 🏷️ **Auto-Labeler**: Etiqueta tu PR automáticamente
- 👀 **PR Review Bot**: Asigna revisores y envía recordatorios
- 📋 **Issue Management**: Te guía para proporcionar información completa
- 📚 **Documentation Bot**: Mantiene documentación actualizada
- 🔒 **Dependabot**: Mantiene dependencias actualizadas
- 🏥 **Dependency Health**: Monitorea seguridad
- 🧠 **Workflow Intelligence**: Optimiza CI/CD
- 🔄 **Coherence Viz**: Actualiza visualizaciones

📖 **Ver detalles completos**: [AUTOMATED_COLLABORATORS.md](AUTOMATED_COLLABORATORS.md)

## 🚀 CI/CD y Calidad de Código

Este proyecto utiliza **CI/CD automatizado real** para garantizar la calidad y reproducibilidad:

### Pipeline Automático

Cada push o pull request ejecuta automáticamente:

1. **Unit Tests** - Suite completa de tests (9 archivos, >50 casos)
2. **Code Quality** - Validación de sintaxis y estilo con flake8
3. **Scientific Analysis** - Validación con datos GWOSC (cuando disponibles)
4. **Auto-Labeling** - Etiquetado inteligente de PRs
5. **Review Assignment** - Asignación automática de revisores

Ver estado actual: [![CI/CD](https://github.com/motanova84/gw250114-141hz-analysis/actions/workflows/analyze.yml/badge.svg)](https://github.com/motanova84/gw250114-141hz-analysis/actions/workflows/analyze.yml)

### Requisitos de Calidad

Para que tu contribución sea aceptada, debe:

- ✅ **Pasar todos los tests** - `make test` o `python scripts/run_all_tests.py`
- ✅ **Sin errores críticos de lint** - `flake8 scripts/ --select=E9,F63,F7,F82`
- ✅ **Código documentado** - Docstrings en funciones públicas
- ✅ **Tests para nuevo código** - Añade tests para nuevas funcionalidades

💡 **Nota**: Los bots automatizados verificarán automáticamente muchos de estos requisitos.

## 📋 Proceso de Contribución

### 1. Fork y Clone

```bash
# Fork el repositorio en GitHub
# Luego clona tu fork
git clone https://github.com/TU_USUARIO/gw250114-141hz-analysis.git
cd gw250114-141hz-analysis
```

### 2. Configurar Entorno

```bash
# Crear entorno virtual
python3 -m venv venv
source venv/bin/activate

# Instalar dependencias
pip install -r requirements.txt
```

### 3. Crear Branch

```bash
# Crear branch descriptivo
git checkout -b feature/mi-mejora
# o
git checkout -b fix/mi-correccion
```

### 4. Desarrollo

```bash
# Hacer cambios
# Ejecutar tests frecuentemente
python scripts/run_all_tests.py

# Verificar calidad de código
flake8 scripts/ --select=E9,F63,F7,F82
```

### 5. Commit y Push

```bash
# Commit con mensaje descriptivo
git add .
git commit -m "feat: descripción clara de la mejora"

# Push a tu fork
git push origin feature/mi-mejora
```

### 6. Pull Request

- Abre un PR desde tu fork al repositorio principal
- Describe claramente los cambios
- Espera la revisión automática de CI/CD
- Responde a comentarios de revisión

## 🧪 Ejecutar Tests Localmente

### Suite Completa

```bash
# Ejecutar todos los tests
python scripts/run_all_tests.py

# O usando Make
make setup  # primera vez
python scripts/run_all_tests.py
```

### Tests Individuales

```bash
# Test de energía cuántica
python scripts/test_energia_cuantica.py

# Test de análisis bayesiano
python scripts/test_analisis_bayesiano_multievento.py

# Test de simetría discreta
python scripts/test_simetria_discreta.py
```

### Linting

```bash
# Errores críticos (sintaxis, nombres indefinidos)
flake8 scripts/ --select=E9,F63,F7,F82 --show-source

# Todas las advertencias
flake8 scripts/ --max-line-length=120
```

## 📝 Estándares de Código

### Python

- **Estilo**: PEP 8 (con líneas hasta 120 caracteres)
- **Docstrings**: Todas las funciones públicas
- **Type hints**: Preferidos para funciones principales
- **Tests**: unittest para tests científicos

### Ejemplo de Función

```python
def calcular_energia_cuantica(frecuencia: float) -> float:
    """
    Calcula la energía cuántica E = hf.
    
    Args:
        frecuencia: Frecuencia en Hz
        
    Returns:
        Energía en Joules
        
    Raises:
        ValueError: Si frecuencia es negativa
    """
    if frecuencia < 0:
        raise ValueError("Frecuencia debe ser positiva")
    
    h = 6.62607015e-34  # Constante de Planck (J·s)
    return h * frecuencia
```

### Tests

```python
import unittest

class TestEnergiaCuantica(unittest.TestCase):
    def test_energia_positiva(self):
        """Verificar que energía sea positiva"""
        E = calcular_energia_cuantica(141.7001)
        self.assertGreater(E, 0)
    
    def test_frecuencia_invalida(self):
        """Verificar que frecuencia negativa lance error"""
        with self.assertRaises(ValueError):
            calcular_energia_cuantica(-1)

if __name__ == '__main__':
    unittest.main()
```

## 🔬 Tipos de Contribuciones

### Muy Bienvenidas

- ✅ **Correcciones de bugs** en análisis o cálculos
- ✅ **Nuevos tests** para aumentar cobertura
- ✅ **Mejoras de documentación** técnica
- ✅ **Optimizaciones** de rendimiento con pruebas
- ✅ **Nuevos análisis** basados en framework existente

### Requieren Discusión Previa

- ⚠️ **Cambios en teoría fundamental** (abrir issue primero)
- ⚠️ **Refactorizaciones grandes** (discutir arquitectura)
- ⚠️ **Nuevas dependencias** (justificar necesidad)

### No Aceptadas

- ❌ **Cambios que rompen reproducibilidad** sin justificación
- ❌ **Código sin tests** para funcionalidad crítica
- ❌ **Violaciones de estándares científicos** (GWOSC, LIGO)

## 📊 Estructura del Proyecto

```
scripts/
├── test_*.py           # Tests unitarios (ejecutados por CI/CD)
├── analizar_*.py       # Scripts de análisis principal
├── validar_*.py        # Scripts de validación
└── run_all_tests.py    # Runner de tests (usado por CI/CD)

notebooks/
├── *.ipynb             # Notebooks reproducibles
└── validation_quick.ipynb  # Validación rápida

results/
└── figures/            # Gráficos generados (no commiteados)

.github/
└── workflows/
    └── analyze.yml     # Pipeline CI/CD (tests, lint, análisis)
```

## 🐛 Reportar Bugs

### Información a Incluir

1. **Descripción clara** del problema
2. **Pasos para reproducir**
3. **Comportamiento esperado** vs. observado
4. **Entorno**: Python version, OS, dependencias
5. **Logs/errores** completos

### Template de Issue

```markdown
## Descripción
[Descripción clara del problema]

## Pasos para Reproducir
1. Ejecutar `python scripts/...`
2. Observar error en...

## Comportamiento Esperado
[Qué debería suceder]

## Comportamiento Observado
[Qué sucede actualmente]

## Entorno
- Python: 3.9.x
- OS: Ubuntu 22.04
- GWPy: 3.0.13

## Logs
```
[Pegar logs aquí]
```
```

## ✨ Sugerir Mejoras

Abre un issue con:

1. **Motivación**: ¿Por qué es útil?
2. **Propuesta**: ¿Qué cambiarías?
3. **Alternativas**: ¿Consideraste otras opciones?
4. **Impacto**: ¿Afecta reproducibilidad?

## 💰 Apoyo al Proyecto

[![Sponsor](https://img.shields.io/badge/Sponsor-❤️-ff69b4)](https://github.com/sponsors/motanova84)

Tu apoyo ayuda a:
- Mantener análisis actualizado con GWTC-3, GWTC-4
- Desarrollar nuevas herramientas open source
- Mejorar documentación y tutoriales
- Infraestructura de CI/CD y tests

## 📧 Contacto

**José Manuel Mota Burruezo**  
📧 institutoconsciencia@proton.me  
🐙 GitHub: [@motanova84](https://github.com/motanova84)

## 📜 Licencia

Al contribuir, aceptas que tu código se distribuya bajo la misma licencia MIT del proyecto.

---

**¡Gracias por hacer que la ciencia sea más abierta y reproducible! 🌌✨**
