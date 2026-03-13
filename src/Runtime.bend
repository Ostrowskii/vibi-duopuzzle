# Runtime.bend
# ============
# Minimal Bend entrypoint plus exported map registry for the JS shell.

import /Model/ as M
import /maps/ as Maps

main : App =
  app{U32, U32, 0, render, on_event}

def render(state: U32) -> HTML(U32):
  <div />

def on_event(evt: U32, state: U32) -> U32:
  state

def map_get(level: U32) -> M.MapDef:
  Maps.get(level)
