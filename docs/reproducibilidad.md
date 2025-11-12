# Reproducibilidad

```bash
cd repro/GWTC-1
pip-compile --generate-hashes requirements.in -o env.lock
./run.sh
```

Esto crea un entorno con hashes inmutables y reproduce tablas/figuras de GWTC-1.
