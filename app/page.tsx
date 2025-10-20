export default function Home() {
  return (
    <div className="grid grid-rows-[20px_1fr_20px] items-center justify-items-center min-h-screen p-8 pb-20 gap-16 sm:p-20 font-[family-name:var(--font-geist-sans)]">
      <main className="flex flex-col gap-8 row-start-2 items-center sm:items-start">
        <h1 className="text-4xl font-bold">
          🌌 GW250114 – Análisis de Componente 141.7001 Hz
        </h1>
        <div className="flex flex-col gap-4">
          <p className="text-xl">
            <strong>Frecuencia Objetivo:</strong> <code className="font-[family-name:var(--font-geist-mono)] bg-black/[.05] dark:bg-white/[.06] px-1 py-0.5 rounded">141.7001 Hz</code>
          </p>
          <p className="text-xl">
            <strong>Autor:</strong> José Manuel Mota Burruezo (JMMB Ψ✧)
          </p>
          <p className="text-xl">
            <strong>Ecuación de Campo:</strong> <code className="font-[family-name:var(--font-geist-mono)] bg-black/[.05] dark:bg-white/[.06] px-1 py-0.5 rounded">Ψ = mc² · A_eff²</code>
          </p>
        </div>
        
        <div className="flex gap-4 items-center flex-col sm:flex-row mt-8">
          <a
            className="rounded-full border border-solid border-transparent transition-colors flex items-center justify-center bg-foreground text-background gap-2 hover:bg-[#383838] dark:hover:bg-[#ccc] text-sm sm:text-base h-10 sm:h-12 px-4 sm:px-5"
            href="/docs"
            rel="noopener noreferrer"
          >
            Ver Documentación
          </a>
          <a
            className="rounded-full border border-solid border-black/[.08] dark:border-white/[.145] transition-colors flex items-center justify-center hover:bg-[#f2f2f2] dark:hover:bg-[#1a1a1a] hover:border-transparent text-sm sm:text-base h-10 sm:h-12 px-4 sm:px-5 sm:min-w-44"
            href="https://github.com/motanova84/gw250114-141hz-analysis"
            target="_blank"
            rel="noopener noreferrer"
          >
            Ver en GitHub
          </a>
        </div>

        <div className="mt-8">
          <h2 className="text-2xl font-bold mb-4">⚛️ Energía Cuántica del Modo Fundamental</h2>
          <p className="text-lg">
            Cálculo de la energía cuántica del modo fundamental del campo noésico:
          </p>
          <p className="text-lg mt-2">
            <code className="font-[family-name:var(--font-geist-mono)] bg-black/[.05] dark:bg-white/[.06] px-2 py-1 rounded text-base">
              E_Ψ = hf₀ = 9.39×10⁻³² J ≈ 5.86×10⁻¹³ eV
            </code>
          </p>
        </div>
      </main>
      <footer className="row-start-3 flex gap-6 flex-wrap items-center justify-center">
        <a
          className="flex items-center gap-2 hover:underline hover:underline-offset-4"
          href="https://github.com/motanova84/gw250114-141hz-analysis/blob/main/README.md"
          target="_blank"
          rel="noopener noreferrer"
        >
          Más información →
        </a>
      </footer>
    </div>
  );
}
