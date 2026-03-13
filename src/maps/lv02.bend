# maps/lv02.bend
# ==============
# Twin slalom.

import /Model/ as M

F : U32 = 0
W : U32 = 1
N : U32 = 0
P : U32 = 1
Q : U32 = 2
A : U32 = 3
B : U32 = 4

floor : List(List(U32)) =
  [ [F F F F F F F F F F F F F F F F F F F F]
    [F F W W W F F F F W W W F F F F W W F F]
    [F F F F W F W W F F F W F W W F F W F F]
    [F W W F W F W F F W F W F W F F F W F F]
    [F F F F F F W F W W F F F W F W F F F F]
    [F F W W W F W F F F F W F W F W W W F F]
    [F F F F F F F F W W F W F F F F F F F F]
    [F W W W F W W F F F F W W W F W W F W F]
    [F F F F F F F F F F F F F F F F F F F F]
    [F F F F F F F F F F F F F F F F F F F F] ]

entity : List(List(U32)) =
  [ [P N N N N N N N N N N N N N N N N N N A]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [N N N N N N N N N N N N N N N N N N N N]
    [Q N N N N N N N N N N N N N N N N N N B] ]

map : M.MapDef =
  map_def{
    "Level 2",
    floor,
    entity,
    point{0, 0},
    point{0, 9},
    point{19, 0},
    point{19, 9},
  }
