import VersoManual
import CubingSite

open Verso.Genre Manual

/-- Each chapter gets its own page; its sections stay on it. -/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc CubingSite) (config := config)
