import VersoManual
import CubingSite

open Verso.Genre Manual

/-- Each chapter gets its own page; its sections stay on it. -/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  -- Verso's theme is light only: text is black and the page leaves its background transparent,
  -- so a host with a dark backdrop (dark mode in some embedded browsers) shows black on black.
  -- Pin the page to its light palette.
  extraCss := {⟨"html { color-scheme: light; background: white; }"⟩}

def main := manualMain (%doc CubingSite) (config := config)
