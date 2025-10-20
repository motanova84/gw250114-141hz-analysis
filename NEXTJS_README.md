# 🚀 Servidor de Desarrollo Next.js

Este proyecto ahora incluye una interfaz web construida con Next.js que se puede ejecutar localmente.

## Requisitos Previos

- Node.js 18.17 o superior
- npm, yarn, pnpm, o bun

## Instalación

Primero, instala las dependencias:

```bash
npm install
# o
yarn install
# o
pnpm install
# o
bun install
```

## Ejecución del Servidor de Desarrollo

Ejecuta el servidor de desarrollo con uno de los siguientes comandos:

```bash
npm run dev
# o
yarn dev
# o
pnpm dev
# o
bun dev
```

Abre [http://localhost:3000](http://localhost:3000) con tu navegador para ver el resultado.

## Edición de la Página

Puedes empezar a editar la página modificando `app/page.tsx`. La página se actualiza automáticamente a medida que editas el archivo gracias a la función de Hot Module Replacement (HMR) de Next.js.

## Optimización de Fuentes

Este proyecto utiliza [`next/font`](https://nextjs.org/docs/basic-features/font-optimization) para optimizar y cargar automáticamente **Geist**, una nueva familia de fuentes para Vercel. Las fuentes se cargan de manera optimizada para mejorar el rendimiento:

- **Geist Sans**: Fuente sans-serif variable
- **Geist Mono**: Fuente monoespaciada variable

Las fuentes están configuradas en `app/layout.tsx` y se aplican mediante variables CSS.

## Estructura del Proyecto

```
app/
├── layout.tsx      # Layout raíz con configuración de fuentes
├── page.tsx        # Página principal
└── globals.css     # Estilos globales
```

## Comandos Disponibles

- `npm run dev` - Inicia el servidor de desarrollo
- `npm run build` - Construye la aplicación para producción
- `npm run start` - Inicia el servidor de producción
- `npm run lint` - Ejecuta el linter de Next.js

## Más Información

Para aprender más sobre Next.js, consulta los siguientes recursos:

- [Documentación de Next.js](https://nextjs.org/docs) - aprende sobre las características y API de Next.js
- [Learn Next.js](https://nextjs.org/learn) - un tutorial interactivo de Next.js
