import * as runtime from "./runtime.generated.js";

function hexPath(path) {
  return Array.from(new TextEncoder().encode(path), (byte) =>
    byte.toString(16).padStart(2, "0")
  ).join("");
}

function resolve(path) {
  const name = `n2f${hexPath(path)}`;
  const got = runtime[name];
  if (typeof got !== "function") {
    throw new Error(`Missing Bend export: ${path}`);
  }
  return got();
}

function listToArray(list) {
  const out = [];
  let node = list;
  while (node && node.$ === "cons") {
    out.push(node.head);
    node = node.tail;
  }
  return out;
}

function pointToJs(point) {
  return {
    x: point.x >>> 0,
    y: point.y >>> 0,
  };
}

function mapToJs(map) {
  return {
    title: map.title,
    floor: listToArray(map.floor).map((row) => listToArray(row).map((value) => value >>> 0)),
    entity: listToArray(map.entity).map((row) => listToArray(row).map((value) => value >>> 0)),
    spawn1: pointToJs(map.spawn1),
    spawn2: pointToJs(map.spawn2),
    exit1: pointToJs(map.exit1),
    exit2: pointToJs(map.exit2),
  };
}

const bendMapGet = resolve("Runtime/map_get");

export function getMap(level) {
  return mapToJs(bendMapGet(level >>> 0));
}
