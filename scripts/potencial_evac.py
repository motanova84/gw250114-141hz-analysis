#!/usr/bin/env python3
"""
Visualización del Potencial de Energía del Vacío E_vac

Este script calcula y grafica el potencial de energía del vacío como función
de log10(R/lP), incluyendo términos clásicos, cuánticos, cosmológicos y 
log-periódicos.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: Octubre 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import minimize_scalar

# Parámetros constantes
beta = -0.207886     # zeta'(1/2)
gamma = 1.0          # factor adimensional (puede ajustarse)
Lambda = 1e-61       # constante cosmológica muy pequeña
delta = 0.1          # amplitud término log-periódico
pi_val = np.pi

# Potencial Evac en función de log10(R / lP)
def E_vac_log(logR):
    R = 10**logR
    term1 = 1 / R**4
    term2 = beta / R**2
    term3 = gamma * Lambda**2 * R**2
    term4 = delta * np.sin(np.log(R) / np.log(pi_val))**2
    return term1 + term2 + term3 + term4

# Minimización en rango plausible log10 R
res = minimize_scalar(E_vac_log, bounds=(40, 50), method='bounded')
min_log_r = res.x
min_E = res.fun

# Valores para gráfico
log_r_vals = np.linspace(40, 50, 1000)
E_vals = [E_vac_log(lr) for lr in log_r_vals]

# Crear gráfico
fig, ax = plt.subplots(figsize=(8,5))
ax.plot(log_r_vals, E_vals, label='E_vac')
ax.scatter(min_log_r, min_E, color='red', label=f'Mínimo en {min_log_r:.2f}')
ax.set_xlabel(r'$\log_{10}(R_\Psi / \ell_P)$')
ax.set_ylabel(r'$E_{\mathrm{vac}}$ (normalizado)')
ax.set_title('Potencial de Energía del Vacío $E_{vac}$')
ax.legend()
plt.tight_layout()
plt.savefig('potential_plot.png')
plt.show()

print(f"Mínimo en log10(R_ / ℓP) = {min_log_r:.2f}, R ≈ 10^{min_log_r:.2f} ℓP")
print("Gráfico guardado como potential_plot.png")
