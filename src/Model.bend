# Model.bend
# ==========
# Shared types for the DuoPuzzle app, room, and maps.

import /Dir/

type Point {
  point{x:U32, y:U32}
}

type SlotShape {
  square{}
  circle{}
}

type SharedPost {
  join{uid:U32, name:String}
  heartbeat{uid:U32}
  leave{uid:U32}
  ready{uid:U32}
  unready{uid:U32}
  chat{uid:U32, name:String, text:String}
  move{uid:U32, dir:Dir}
  victory_ready{uid:U32}
}

type Person {
  person{
    uid:U32,
    name:String,
    online:U32,
    ready:U32,
    last_seen:U32,
  }
}

type SlotState {
  slot_state{
    occupied:U32,
    occupant:U32,
    occupant_name:String,
    pos:Point,
    shape:SlotShape,
    color_index:U32,
  }
}

type ChatMsg {
  chat_msg{
    kind:U32,
    name:String,
    text:String,
    tick:U32,
  }
}

type MapDef {
  map_def{
    title:String,
    floor:List(List(U32)),
    entity:List(List(U32)),
    spawn1:Point,
    spawn2:Point,
    exit1:Point,
    exit2:Point,
  }
}

type SharedState {
  shared_state{
    tick:U32,
    phase:U32,
    current_level:U32,
    people:List(Person),
    slot1:SlotState,
    slot2:SlotState,
    chat:List(ChatMsg),
    current_run_start:U32,
    level_start:U32,
    split_times:List(U32),
    best_level_times:List(U32),
    best_total_time:U32,
    best_total_done:U32,
  }
}

type AppState {
  app_state{
    user_input:String,
    room_input:String,
    chat_input:String,
    session_uid:U32,
    session_user:String,
    session_room:String,
    has_session:U32,
    connected:U32,
    ping:U32,
    shared:SharedState,
  }
}

type AppEvent {
  set_user{value:String}
  set_room{value:String}
  set_chat{value:String}
  connect{user:String, room:String}
  sync_session{uid:U32, user:String, room:String}
  sync_room{room:SharedState}
  sync_meta{connected:U32, ping:U32}
  toggle_ready{uid:U32}
  leave_room{uid:U32}
  send_chat{uid:U32, name:String, text:String}
  move_up{uid:U32}
  move_down{uid:U32}
  move_left{uid:U32}
  move_right{uid:U32}
  victory_next{uid:U32}
  ignore{}
}
