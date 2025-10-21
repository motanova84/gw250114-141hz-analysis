"""Herramientas para generar reportes de validación de los tres pilares."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Iterable, List, Union


PathLike = Union[str, Path]


def _serialise_section(section: object) -> object:
    """Normalise sections before serialisation.

    El helper garantiza que las secciones no nulas se serialicen correctamente.
    Las estructuras tipo ``dict`` o ``list`` se mantienen, mientras que valores
    ``None`` se convierten en diccionarios vacíos para evitar que ``json.dump``
    genere ``null`` donde se esperan estructuras.
    """

    if section is None:
        return {}
    return section


def generar_reporte_pilares(data: Dict[str, object], output_dir: PathLike) -> List[Path]:
    """Genera los archivos JSON para cada pilar del método científico.

    Parameters
    ----------
    data:
        Diccionario que contiene las claves ``reproducibilidad``, ``falsabilidad``
        y ``evidencia_empirica``. Cada una puede ser cualquier estructura
        serializable a JSON.
    output_dir:
        Directorio donde se escribirán los archivos. Se crea automáticamente si
        no existe.

    Returns
    -------
    list of :class:`pathlib.Path`
        Rutas completas de los archivos generados, en el mismo orden en que se
        escribieron.
    """

    base_path = Path(output_dir)
    base_path.mkdir(parents=True, exist_ok=True)

    archivos = {
        "reproducibilidad.json": _serialise_section(data.get("reproducibilidad")),
        "falsabilidad.json": _serialise_section(data.get("falsabilidad")),
        "evidencia_empirica.json": _serialise_section(data.get("evidencia_empirica")),
    }

    rutas: List[Path] = []
    for nombre, contenido in archivos.items():
        ruta = base_path / nombre
        with ruta.open("w", encoding="utf-8") as handler:
            json.dump(contenido, handler, indent=2, ensure_ascii=False)
        rutas.append(ruta)

    return rutas


__all__: Iterable[str] = ["generar_reporte_pilares"]
