# maps/_.bend
# ===========
# Level registry for the 10 DuoPuzzle stages.

import /Model/ as M
import /maps/lv01/ as L01
import /maps/lv02/ as L02
import /maps/lv03/ as L03
import /maps/lv04/ as L04
import /maps/lv05/ as L05
import /maps/lv06/ as L06
import /maps/lv07/ as L07
import /maps/lv08/ as L08
import /maps/lv09/ as L09
import /maps/lv10/ as L10

def get(level: U32) -> M.MapDef:
  match level:
    case 1:
      L01.map
    case 2:
      L02.map
    case 3:
      L03.map
    case 4:
      L04.map
    case 5:
      L05.map
    case 6:
      L06.map
    case 7:
      L07.map
    case 8:
      L08.map
    case 9:
      L09.map
    case _:
      L10.map
