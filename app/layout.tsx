import type { Metadata } from "next";
import { GeistSans } from "geist/font/sans";
import { GeistMono } from "geist/font/mono";
import "./globals.css";

export const metadata: Metadata = {
  title: "GW250114 - Análisis de Componente 141.7001 Hz",
  description: "Análisis de ondas gravitacionales y frecuencia fundamental del campo noésico",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="es" className={`${GeistSans.variable} ${GeistMono.variable}`}>
      <body>
        {children}
      </body>
    </html>
  );
}
