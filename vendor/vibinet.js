var __defProp = Object.defineProperty;
var __defNormalProp = (obj, key, value) => key in obj ? __defProp(obj, key, { enumerable: true, configurable: true, writable: true, value }) : obj[key] = value;
var __publicField = (obj, key, value) => __defNormalProp(obj, typeof key !== "symbol" ? key + "" : key, value);

// src/packer.ts
var MAX_SAFE_BITS = 53;
var text_decoder = new TextDecoder();
var union_cache = /* @__PURE__ */ new WeakMap();
var struct_cache = /* @__PURE__ */ new WeakMap();
var BitWriter = class {
  constructor(buf) {
    __publicField(this, "buf");
    __publicField(this, "bit_pos");
    this.buf = buf;
    this.bit_pos = 0;
  }
  write_bit(bit) {
    const byte_index = this.bit_pos >>> 3;
    const bit_index = this.bit_pos & 7;
    if (bit) {
      this.buf[byte_index] |= 1 << bit_index;
    }
    this.bit_pos++;
  }
  write_bitsUnsigned(value, bits) {
    if (bits === 0) return;
    if (typeof value === "number") {
      if (bits <= 32) {
        const aligned = (this.bit_pos & 7) === 0 && (bits & 7) === 0;
        if (aligned) {
          let v2 = value >>> 0;
          let byte_index = this.bit_pos >>> 3;
          for (let i = 0; i < bits; i += 8) {
            this.buf[byte_index++] = v2 & 255;
            v2 >>>= 8;
          }
          this.bit_pos += bits;
          return;
        }
        let v = value >>> 0;
        for (let i = 0; i < bits; i++) {
          this.write_bit(v & 1);
          v >>>= 1;
        }
        return;
      }
      this.write_bitsBigint(BigInt(value), bits);
      return;
    }
    this.write_bitsBigint(value, bits);
  }
  write_bitsBigint(value, bits) {
    if (bits === 0) return;
    const aligned = (this.bit_pos & 7) === 0 && (bits & 7) === 0;
    if (aligned) {
      let v2 = value;
      let byte_index = this.bit_pos >>> 3;
      for (let i = 0; i < bits; i += 8) {
        this.buf[byte_index++] = Number(v2 & 0xffn);
        v2 >>= 8n;
      }
      this.bit_pos += bits;
      return;
    }
    let v = value;
    for (let i = 0; i < bits; i++) {
      this.write_bit((v & 1n) === 0n ? 0 : 1);
      v >>= 1n;
    }
  }
};
var BitReader = class {
  constructor(buf) {
    __publicField(this, "buf");
    __publicField(this, "bit_pos");
    this.buf = buf;
    this.bit_pos = 0;
  }
  read_bit() {
    const byte_index = this.bit_pos >>> 3;
    const bit_index = this.bit_pos & 7;
    const bit = this.buf[byte_index] >>> bit_index & 1;
    this.bit_pos++;
    return bit;
  }
  read_bitsUnsigned(bits) {
    if (bits === 0) return 0;
    if (bits <= 32) {
      const aligned = (this.bit_pos & 7) === 0 && (bits & 7) === 0;
      if (aligned) {
        let v2 = 0;
        let shift = 0;
        let byte_index = this.bit_pos >>> 3;
        for (let i = 0; i < bits; i += 8) {
          v2 |= this.buf[byte_index++] << shift;
          shift += 8;
        }
        this.bit_pos += bits;
        return v2 >>> 0;
      }
      let v = 0;
      for (let i = 0; i < bits; i++) {
        if (this.read_bit()) {
          v |= 1 << i;
        }
      }
      return v >>> 0;
    }
    if (bits <= MAX_SAFE_BITS) {
      let v = 0;
      let pow = 1;
      for (let i = 0; i < bits; i++) {
        if (this.read_bit()) {
          v += pow;
        }
        pow *= 2;
      }
      return v;
    }
    return this.read_bitsBigint(bits);
  }
  read_bitsBigint(bits) {
    if (bits === 0) return 0n;
    const aligned = (this.bit_pos & 7) === 0 && (bits & 7) === 0;
    if (aligned) {
      let v2 = 0n;
      let shift = 0n;
      let byte_index = this.bit_pos >>> 3;
      for (let i = 0; i < bits; i += 8) {
        v2 |= BigInt(this.buf[byte_index++]) << shift;
        shift += 8n;
      }
      this.bit_pos += bits;
      return v2;
    }
    let v = 0n;
    let pow = 1n;
    for (let i = 0; i < bits; i++) {
      if (this.read_bit()) {
        v += pow;
      }
      pow <<= 1n;
    }
    return v;
  }
};
function assert_integer(value, name) {
  if (!Number.isInteger(value)) {
    throw new TypeError(`${name} must be an integer`);
  }
}
function assert_size(size) {
  assert_integer(size, "size");
  if (size < 0) throw new RangeError("size must be >= 0");
}
function assert_vector_size(expected, actual) {
  if (actual !== expected) {
    throw new RangeError(`vector size mismatch: expected ${expected}, got ${actual}`);
  }
}
function size_bits(type, val) {
  switch (type.$) {
    case "UInt":
    case "Int":
      assert_size(type.size);
      return type.size;
    case "Nat": {
      if (typeof val === "bigint") {
        if (val < 0n) throw new RangeError("Nat must be >= 0");
        if (val > BigInt(Number.MAX_SAFE_INTEGER)) {
          throw new RangeError("Nat too large to size");
        }
        return Number(val) + 1;
      }
      assert_integer(val, "Nat");
      if (val < 0) throw new RangeError("Nat must be >= 0");
      return val + 1;
    }
    case "Tuple": {
      const fields = type.fields;
      const arr = as_array(val, "Tuple");
      let bits = 0;
      for (let i = 0; i < fields.length; i++) {
        bits += size_bits(fields[i], arr[i]);
      }
      return bits;
    }
    case "Vector": {
      assert_size(type.size);
      const arr = as_array(val, "Vector");
      assert_vector_size(type.size, arr.length);
      let bits = 0;
      for (let i = 0; i < type.size; i++) {
        bits += size_bits(type.type, arr[i]);
      }
      return bits;
    }
    case "Struct": {
      let bits = 0;
      const keys = struct_keys(type.fields);
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i];
        const v = get_struct_field(val, key);
        bits += size_bits(type.fields[key], v);
      }
      return bits;
    }
    case "List": {
      let bits = 1;
      for_each_list(val, (item) => {
        bits += 1;
        bits += size_bits(type.type, item);
      });
      return bits;
    }
    case "Map": {
      let bits = 1;
      for_each_map(val, (k, v) => {
        bits += 1;
        bits += size_bits(type.key, k);
        bits += size_bits(type.value, v);
      });
      return bits;
    }
    case "Union": {
      const info = union_info(type);
      const tag = get_union_tag(val);
      const variant_type = type.variants[tag];
      if (!variant_type) {
        throw new RangeError(`Unknown union variant: ${tag}`);
      }
      const payload = get_union_payload(val, variant_type);
      return info.tag_bits + size_bits(variant_type, payload);
    }
    case "String": {
      const byte_len = utf8_byte_length(val);
      return 1 + byte_len * 9;
    }
  }
}
function encode_into(writer, type, val) {
  switch (type.$) {
    case "UInt": {
      assert_size(type.size);
      if (type.size === 0) {
        if (val === 0 || val === 0n) return;
        throw new RangeError("UInt out of range");
      }
      if (typeof val === "bigint") {
        if (val < 0n) throw new RangeError("UInt must be >= 0");
        const max2 = 1n << BigInt(type.size);
        if (val >= max2) throw new RangeError("UInt out of range");
        writer.write_bitsUnsigned(val, type.size);
        return;
      }
      assert_integer(val, "UInt");
      if (val < 0) throw new RangeError("UInt must be >= 0");
      if (type.size > MAX_SAFE_BITS) {
        throw new RangeError("UInt too large for number; use bigint");
      }
      const max = 2 ** type.size;
      if (val >= max) throw new RangeError("UInt out of range");
      writer.write_bitsUnsigned(val, type.size);
      return;
    }
    case "Int": {
      assert_size(type.size);
      if (type.size === 0) {
        if (val === 0 || val === 0n) return;
        throw new RangeError("Int out of range");
      }
      if (typeof val === "bigint") {
        const size = BigInt(type.size);
        const min2 = -(1n << size - 1n);
        const max2 = (1n << size - 1n) - 1n;
        if (val < min2 || val > max2) throw new RangeError("Int out of range");
        let unsigned2 = val;
        if (val < 0n) unsigned2 = (1n << size) + val;
        writer.write_bitsUnsigned(unsigned2, type.size);
        return;
      }
      assert_integer(val, "Int");
      if (type.size > MAX_SAFE_BITS) {
        throw new RangeError("Int too large for number; use bigint");
      }
      const min = -(2 ** (type.size - 1));
      const max = 2 ** (type.size - 1) - 1;
      if (val < min || val > max) throw new RangeError("Int out of range");
      let unsigned = val;
      if (val < 0) unsigned = 2 ** type.size + val;
      writer.write_bitsUnsigned(unsigned, type.size);
      return;
    }
    case "Nat": {
      if (typeof val === "bigint") {
        if (val < 0n) throw new RangeError("Nat must be >= 0");
        let n = val;
        while (n > 0n) {
          writer.write_bit(1);
          n -= 1n;
        }
        writer.write_bit(0);
        return;
      }
      assert_integer(val, "Nat");
      if (val < 0) throw new RangeError("Nat must be >= 0");
      for (let i = 0; i < val; i++) {
        writer.write_bit(1);
      }
      writer.write_bit(0);
      return;
    }
    case "Tuple": {
      const fields = type.fields;
      const arr = as_array(val, "Tuple");
      for (let i = 0; i < fields.length; i++) {
        encode_into(writer, fields[i], arr[i]);
      }
      return;
    }
    case "Vector": {
      assert_size(type.size);
      const arr = as_array(val, "Vector");
      assert_vector_size(type.size, arr.length);
      for (let i = 0; i < type.size; i++) {
        encode_into(writer, type.type, arr[i]);
      }
      return;
    }
    case "Struct": {
      const keys = struct_keys(type.fields);
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i];
        encode_into(writer, type.fields[key], get_struct_field(val, key));
      }
      return;
    }
    case "List": {
      for_each_list(val, (item) => {
        writer.write_bit(1);
        encode_into(writer, type.type, item);
      });
      writer.write_bit(0);
      return;
    }
    case "Map": {
      for_each_map(val, (k, v) => {
        writer.write_bit(1);
        encode_into(writer, type.key, k);
        encode_into(writer, type.value, v);
      });
      writer.write_bit(0);
      return;
    }
    case "Union": {
      const info = union_info(type);
      const tag = get_union_tag(val);
      const index = info.index_by_tag.get(tag);
      if (index === void 0) {
        throw new RangeError(`Unknown union variant: ${tag}`);
      }
      if (info.tag_bits > 0) {
        writer.write_bitsUnsigned(index, info.tag_bits);
      }
      const variant_type = type.variants[tag];
      const payload = get_union_payload(val, variant_type);
      encode_into(writer, variant_type, payload);
      return;
    }
    case "String": {
      write_utf8_list(writer, val);
      return;
    }
  }
}
function decode_from(reader, type) {
  switch (type.$) {
    case "UInt": {
      assert_size(type.size);
      return reader.read_bitsUnsigned(type.size);
    }
    case "Int": {
      assert_size(type.size);
      if (type.size === 0) return 0;
      const unsigned = reader.read_bitsUnsigned(type.size);
      if (typeof unsigned === "bigint") {
        const sign_bit2 = 1n << BigInt(type.size - 1);
        if (unsigned & sign_bit2) {
          return unsigned - (1n << BigInt(type.size));
        }
        return unsigned;
      }
      const sign_bit = 2 ** (type.size - 1);
      if (unsigned >= sign_bit) {
        return unsigned - 2 ** type.size;
      }
      return unsigned;
    }
    case "Nat": {
      let n = 0;
      let big = null;
      while (reader.read_bit()) {
        if (big !== null) {
          big += 1n;
        } else if (n === Number.MAX_SAFE_INTEGER) {
          big = BigInt(n) + 1n;
        } else {
          n++;
        }
      }
      return big ?? n;
    }
    case "Tuple": {
      const out = new Array(type.fields.length);
      for (let i = 0; i < type.fields.length; i++) {
        out[i] = decode_from(reader, type.fields[i]);
      }
      return out;
    }
    case "Vector": {
      const out = new Array(type.size);
      for (let i = 0; i < type.size; i++) {
        out[i] = decode_from(reader, type.type);
      }
      return out;
    }
    case "Struct": {
      const out = {};
      const keys = struct_keys(type.fields);
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i];
        out[key] = decode_from(reader, type.fields[key]);
      }
      return out;
    }
    case "List": {
      const out = [];
      while (reader.read_bit()) {
        out.push(decode_from(reader, type.type));
      }
      return out;
    }
    case "Map": {
      const out = /* @__PURE__ */ new Map();
      while (reader.read_bit()) {
        const key = decode_from(reader, type.key);
        const value = decode_from(reader, type.value);
        out.set(key, value);
      }
      return out;
    }
    case "Union": {
      const info = union_info(type);
      let raw_index = 0;
      if (info.tag_bits > 0) {
        raw_index = reader.read_bitsUnsigned(info.tag_bits);
      }
      let index;
      if (typeof raw_index === "bigint") {
        if (raw_index > BigInt(Number.MAX_SAFE_INTEGER)) {
          throw new RangeError("Union tag index too large");
        }
        index = Number(raw_index);
      } else {
        index = raw_index;
      }
      if (index < 0 || index >= info.keys.length) {
        throw new RangeError("Union tag index out of range");
      }
      const tag = info.keys[index];
      const variant_type = type.variants[tag];
      const payload = decode_from(reader, variant_type);
      if (variant_type.$ === "Struct") {
        if (payload && typeof payload === "object") {
          payload.$ = tag;
          return payload;
        }
      }
      return { $: tag, value: payload };
    }
    case "String": {
      return read_utf8_list(reader);
    }
  }
}
function as_array(val, label) {
  if (!Array.isArray(val)) {
    throw new TypeError(`${label} value must be an Array`);
  }
  return val;
}
function get_struct_field(val, key) {
  if (val && typeof val === "object") {
    return val[key];
  }
  throw new TypeError("Struct value must be an object");
}
function union_info(type) {
  const cached = union_cache.get(type);
  if (cached) return cached;
  const keys = Object.keys(type.variants).sort();
  if (keys.length === 0) {
    throw new RangeError("Union must have at least one variant");
  }
  const index_by_tag = /* @__PURE__ */ new Map();
  for (let i = 0; i < keys.length; i++) {
    index_by_tag.set(keys[i], i);
  }
  const tag_bits = keys.length <= 1 ? 0 : Math.ceil(Math.log2(keys.length));
  const info = { keys, index_by_tag, tag_bits };
  union_cache.set(type, info);
  return info;
}
function struct_keys(fields) {
  const cached = struct_cache.get(fields);
  if (cached) return cached;
  const keys = Object.keys(fields);
  struct_cache.set(fields, keys);
  return keys;
}
function get_union_tag(val) {
  if (!val || typeof val !== "object") {
    throw new TypeError("Union value must be an object with a $ tag");
  }
  const tag = val.$;
  if (typeof tag !== "string") {
    throw new TypeError("Union value must have a string $ tag");
  }
  return tag;
}
function get_union_payload(val, variant_type) {
  if (variant_type.$ !== "Struct" && val && typeof val === "object" && Object.prototype.hasOwnProperty.call(val, "value")) {
    return val.value;
  }
  return val;
}
function for_each_list(val, fn) {
  if (!Array.isArray(val)) {
    throw new TypeError("List value must be an Array");
  }
  for (let i = 0; i < val.length; i++) {
    fn(val[i]);
  }
}
function for_each_map(val, fn) {
  if (val == null) return;
  if (val instanceof Map) {
    for (const [k, v] of val) {
      fn(k, v);
    }
    return;
  }
  if (typeof val === "object") {
    for (const key of Object.keys(val)) {
      fn(key, val[key]);
    }
    return;
  }
  throw new TypeError("Map value must be a Map or object");
}
function utf8_byte_length(value) {
  if (typeof value !== "string") {
    throw new TypeError("String value must be a string");
  }
  let len = 0;
  for (let i = 0; i < value.length; i++) {
    const code = value.charCodeAt(i);
    if (code < 128) {
      len += 1;
    } else if (code < 2048) {
      len += 2;
    } else if (code >= 55296 && code <= 56319) {
      const next = i + 1 < value.length ? value.charCodeAt(i + 1) : 0;
      if (next >= 56320 && next <= 57343) {
        i++;
        len += 4;
      } else {
        len += 3;
      }
    } else if (code >= 56320 && code <= 57343) {
      len += 3;
    } else {
      len += 3;
    }
  }
  return len;
}
function write_utf8_list(writer, value) {
  if (typeof value !== "string") {
    throw new TypeError("String value must be a string");
  }
  for (let i = 0; i < value.length; i++) {
    let code = value.charCodeAt(i);
    if (code < 128) {
      writer.write_bit(1);
      writer.write_bitsUnsigned(code, 8);
      continue;
    }
    if (code < 2048) {
      writer.write_bit(1);
      writer.write_bitsUnsigned(192 | code >>> 6, 8);
      writer.write_bit(1);
      writer.write_bitsUnsigned(128 | code & 63, 8);
      continue;
    }
    if (code >= 55296 && code <= 56319) {
      const next = i + 1 < value.length ? value.charCodeAt(i + 1) : 0;
      if (next >= 56320 && next <= 57343) {
        i++;
        const cp = (code - 55296 << 10) + (next - 56320) + 65536;
        writer.write_bit(1);
        writer.write_bitsUnsigned(240 | cp >>> 18, 8);
        writer.write_bit(1);
        writer.write_bitsUnsigned(128 | cp >>> 12 & 63, 8);
        writer.write_bit(1);
        writer.write_bitsUnsigned(128 | cp >>> 6 & 63, 8);
        writer.write_bit(1);
        writer.write_bitsUnsigned(128 | cp & 63, 8);
        continue;
      }
      code = 65533;
    } else if (code >= 56320 && code <= 57343) {
      code = 65533;
    }
    writer.write_bit(1);
    writer.write_bitsUnsigned(224 | code >>> 12, 8);
    writer.write_bit(1);
    writer.write_bitsUnsigned(128 | code >>> 6 & 63, 8);
    writer.write_bit(1);
    writer.write_bitsUnsigned(128 | code & 63, 8);
  }
  writer.write_bit(0);
}
function read_utf8_list(reader) {
  let bytes = new Uint8Array(16);
  let len = 0;
  while (reader.read_bit()) {
    const byte = reader.read_bitsUnsigned(8);
    if (len === bytes.length) {
      const next = new Uint8Array(bytes.length * 2);
      next.set(bytes);
      bytes = next;
    }
    bytes[len++] = byte;
  }
  return text_decoder.decode(bytes.subarray(0, len));
}
function encode(type, val) {
  const bits = size_bits(type, val);
  const buf = new Uint8Array(bits + 7 >>> 3);
  const writer = new BitWriter(buf);
  encode_into(writer, type, val);
  return buf;
}
function decode(type, buf) {
  const reader = new BitReader(buf);
  return decode_from(reader, type);
}

// src/protocol.ts
var TIME_BITS = 53;
var BYTE_LIST_PACKED = { $: "List", type: { $: "UInt", size: 8 } };
var MESSAGE_PACKED = {
  $: "Union",
  variants: {
    get_time: { $: "Struct", fields: {} },
    info_time: {
      $: "Struct",
      fields: {
        time: { $: "UInt", size: TIME_BITS }
      }
    },
    post: {
      $: "Struct",
      fields: {
        room: { $: "String" },
        time: { $: "UInt", size: TIME_BITS },
        name: { $: "String" },
        payload: BYTE_LIST_PACKED
      }
    },
    info_post: {
      $: "Struct",
      fields: {
        room: { $: "String" },
        index: { $: "UInt", size: 32 },
        server_time: { $: "UInt", size: TIME_BITS },
        client_time: { $: "UInt", size: TIME_BITS },
        name: { $: "String" },
        payload: BYTE_LIST_PACKED
      }
    },
    load: {
      $: "Struct",
      fields: {
        room: { $: "String" },
        from: { $: "UInt", size: 32 }
      }
    },
    watch: {
      $: "Struct",
      fields: {
        room: { $: "String" }
      }
    },
    unwatch: {
      $: "Struct",
      fields: {
        room: { $: "String" }
      }
    }
  }
};
function bytes_to_list(bytes) {
  const out = new Array(bytes.length);
  for (let i = 0; i < bytes.length; i++) {
    out[i] = bytes[i];
  }
  return out;
}
function list_to_bytes(list) {
  const out = new Uint8Array(list.length);
  for (let i = 0; i < list.length; i++) {
    out[i] = list[i] & 255;
  }
  return out;
}
function to_wire_message(message) {
  switch (message.$) {
    case "post":
      return {
        $: "post",
        room: message.room,
        time: message.time,
        name: message.name,
        payload: bytes_to_list(message.payload)
      };
    case "info_post":
      return {
        $: "info_post",
        room: message.room,
        index: message.index,
        server_time: message.server_time,
        client_time: message.client_time,
        name: message.name,
        payload: bytes_to_list(message.payload)
      };
    default:
      return message;
  }
}
function from_wire_message(message) {
  switch (message.$) {
    case "post":
      return {
        $: "post",
        room: message.room,
        time: message.time,
        name: message.name,
        payload: list_to_bytes(message.payload)
      };
    case "info_post":
      return {
        $: "info_post",
        room: message.room,
        index: message.index,
        server_time: message.server_time,
        client_time: message.client_time,
        name: message.name,
        payload: list_to_bytes(message.payload)
      };
    default:
      return message;
  }
}
function encode_message(message) {
  return encode(MESSAGE_PACKED, to_wire_message(message));
}
function decode_message(buf) {
  const message = decode(MESSAGE_PACKED, buf);
  return from_wire_message(message);
}

// src/server_url.ts
var OFFICIAL_SERVER_URL = "wss://net.studiovibi.com";
function normalize_ws_url(raw_url) {
  let ws_url = raw_url;
  try {
    const url = new URL(raw_url);
    if (url.protocol === "http:") {
      url.protocol = "ws:";
    } else if (url.protocol === "https:") {
      url.protocol = "wss:";
    }
    ws_url = url.toString();
  } catch {
    ws_url = raw_url;
  }
  if (typeof window !== "undefined" && window.location.protocol === "https:" && ws_url.startsWith("ws://")) {
    const upgraded = `wss://${ws_url.slice("ws://".length)}`;
    console.warn(
      `[VibiNet] Upgrading insecure WebSocket URL "${ws_url}" to "${upgraded}" because the page is HTTPS.`
    );
    return upgraded;
  }
  return ws_url;
}

// src/client.ts
function now() {
  return Math.floor(Date.now());
}
function default_ws_url() {
  return OFFICIAL_SERVER_URL;
}
function gen_name() {
  const alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-";
  const bytes = new Uint8Array(8);
  const can_crypto = typeof crypto !== "undefined" && typeof crypto.getRandomValues === "function";
  if (can_crypto) {
    crypto.getRandomValues(bytes);
  } else {
    for (let i = 0; i < 8; i++) {
      bytes[i] = Math.floor(Math.random() * 256);
    }
  }
  let out = "";
  for (let i = 0; i < 8; i++) {
    out += alphabet[bytes[i] % 64];
  }
  return out;
}
function create_client(server) {
  const time_sync = {
    clock_offset: Infinity,
    lowest_ping: Infinity,
    request_sent_at: 0,
    last_ping: Infinity
  };
  const room_watchers = /* @__PURE__ */ new Map();
  let is_synced = false;
  const sync_listeners = [];
  const ws_url = normalize_ws_url(server ?? default_ws_url());
  const ws = new WebSocket(ws_url);
  ws.binaryType = "arraybuffer";
  function server_time() {
    if (!isFinite(time_sync.clock_offset)) {
      throw new Error("server_time() called before initial sync");
    }
    return Math.floor(now() + time_sync.clock_offset);
  }
  function ensure_open() {
    if (ws.readyState !== WebSocket.OPEN) {
      throw new Error("WebSocket not open");
    }
  }
  function send(buf) {
    ensure_open();
    ws.send(buf);
  }
  function register_handler(room, packer, handler) {
    const existing = room_watchers.get(room);
    if (existing) {
      if (existing.packer !== packer) {
        throw new Error(`Packed schema already registered for room: ${room}`);
      }
      if (handler) {
        existing.handler = handler;
      }
      return;
    }
    room_watchers.set(room, { handler, packer });
  }
  ws.addEventListener("open", () => {
    console.log("[WS] Connected");
    time_sync.request_sent_at = now();
    send(encode_message({ $: "get_time" }));
    setInterval(() => {
      time_sync.request_sent_at = now();
      send(encode_message({ $: "get_time" }));
    }, 2e3);
  });
  ws.addEventListener("message", (event) => {
    const data = event.data instanceof ArrayBuffer ? new Uint8Array(event.data) : new Uint8Array(event.data);
    const msg = decode_message(data);
    switch (msg.$) {
      case "info_time": {
        const t = now();
        const ping = t - time_sync.request_sent_at;
        time_sync.last_ping = ping;
        if (ping < time_sync.lowest_ping) {
          const local_avg = Math.floor((time_sync.request_sent_at + t) / 2);
          time_sync.clock_offset = msg.time - local_avg;
          time_sync.lowest_ping = ping;
        }
        if (!is_synced) {
          is_synced = true;
          for (const cb of sync_listeners) {
            cb();
          }
          sync_listeners.length = 0;
        }
        break;
      }
      case "info_post": {
        const watcher = room_watchers.get(msg.room);
        if (watcher && watcher.handler) {
          const data2 = decode(watcher.packer, msg.payload);
          watcher.handler({
            $: "info_post",
            room: msg.room,
            index: msg.index,
            server_time: msg.server_time,
            client_time: msg.client_time,
            name: msg.name,
            data: data2
          });
        }
        break;
      }
    }
  });
  return {
    on_sync: (callback) => {
      if (is_synced) {
        callback();
        return;
      }
      sync_listeners.push(callback);
    },
    watch: (room, packer, handler) => {
      register_handler(room, packer, handler);
      send(encode_message({ $: "watch", room }));
    },
    load: (room, from, packer) => {
      register_handler(room, packer);
      send(encode_message({ $: "load", room, from }));
    },
    post: (room, data, packer) => {
      const name = gen_name();
      const payload = encode(packer, data);
      send(encode_message({ $: "post", room, time: server_time(), name, payload }));
      return name;
    },
    server_time,
    ping: () => time_sync.last_ping,
    close: () => ws.close()
  };
}

// src/vibi.ts
var _VibiNet = class _VibiNet {
  // Create a VibiNet instance and hook the client sync/load/watch callbacks.
  constructor(options) {
    __publicField(this, "room");
    __publicField(this, "init");
    __publicField(this, "on_tick");
    __publicField(this, "on_post");
    __publicField(this, "packer");
    __publicField(this, "smooth");
    __publicField(this, "tick_rate");
    __publicField(this, "tolerance");
    __publicField(this, "client_api");
    __publicField(this, "remote_posts");
    __publicField(this, "local_posts");
    __publicField(this, "timeline");
    __publicField(this, "cache_enabled");
    __publicField(this, "snapshot_stride");
    __publicField(this, "snapshot_count");
    __publicField(this, "snapshots");
    __publicField(this, "snapshot_start_tick");
    __publicField(this, "initial_time_value");
    __publicField(this, "initial_tick_value");
    __publicField(this, "max_remote_index");
    const default_smooth = (remote, _local) => remote;
    const smooth = options.smooth ?? default_smooth;
    const cache = options.cache ?? true;
    const snapshot_stride = options.snapshot_stride ?? 8;
    const snapshot_count = options.snapshot_count ?? 256;
    const client_api = options.client ?? create_client(options.server);
    this.room = options.room;
    this.init = options.initial;
    this.on_tick = options.on_tick;
    this.on_post = options.on_post;
    this.packer = options.packer;
    this.smooth = smooth;
    this.tick_rate = options.tick_rate;
    this.tolerance = options.tolerance;
    this.client_api = client_api;
    this.remote_posts = /* @__PURE__ */ new Map();
    this.local_posts = /* @__PURE__ */ new Map();
    this.timeline = /* @__PURE__ */ new Map();
    this.cache_enabled = cache;
    this.snapshot_stride = Math.max(1, Math.floor(snapshot_stride));
    this.snapshot_count = Math.max(1, Math.floor(snapshot_count));
    this.snapshots = /* @__PURE__ */ new Map();
    this.snapshot_start_tick = null;
    this.initial_time_value = null;
    this.initial_tick_value = null;
    this.max_remote_index = -1;
    this.client_api.on_sync(() => {
      console.log(`[VIBI] synced; watching+loading room=${this.room}`);
      this.client_api.watch(this.room, this.packer, (post) => {
        if (post.name) {
          this.remove_local_post(post.name);
        }
        this.add_remote_post(post);
      });
      this.client_api.load(this.room, 0, this.packer);
    });
  }
  // Compute the authoritative time a post takes effect.
  official_time(post) {
    if (post.client_time <= post.server_time - this.tolerance) {
      return post.server_time - this.tolerance;
    } else {
      return post.client_time;
    }
  }
  // Convert a post into its authoritative tick.
  official_tick(post) {
    return this.time_to_tick(this.official_time(post));
  }
  // Get or create the timeline bucket for a tick.
  get_bucket(tick) {
    let bucket = this.timeline.get(tick);
    if (!bucket) {
      bucket = { remote: [], local: [] };
      this.timeline.set(tick, bucket);
    }
    return bucket;
  }
  // Insert an authoritative post into a tick bucket (kept sorted by index).
  insert_remote_post(post, tick) {
    const bucket = this.get_bucket(tick);
    bucket.remote.push(post);
    bucket.remote.sort((a, b) => a.index - b.index);
  }
  // Drop snapshots at or after tick; earlier snapshots remain valid.
  invalidate_from_tick(tick) {
    if (!this.cache_enabled) {
      return;
    }
    const start_tick = this.snapshot_start_tick;
    if (start_tick !== null && tick < start_tick) {
      return;
    }
    if (start_tick === null || this.snapshots.size === 0) {
      return;
    }
    const stride = this.snapshot_stride;
    const end_tick = start_tick + (this.snapshots.size - 1) * stride;
    if (tick > end_tick) {
      return;
    }
    if (tick <= start_tick) {
      this.snapshots.clear();
      return;
    }
    for (let t = end_tick; t >= tick; t -= stride) {
      this.snapshots.delete(t);
    }
  }
  // Apply on_tick/on_post from (from_tick, to_tick] to advance a state.
  advance_state(state, from_tick, to_tick) {
    let next = state;
    for (let tick = from_tick + 1; tick <= to_tick; tick++) {
      next = this.apply_tick(next, tick);
    }
    return next;
  }
  // Drop all cached timeline/post data older than prune_tick.
  prune_before_tick(prune_tick) {
    if (!this.cache_enabled) {
      return;
    }
    for (const tick of this.timeline.keys()) {
      if (tick < prune_tick) {
        this.timeline.delete(tick);
      }
    }
    for (const [index, post] of this.remote_posts.entries()) {
      if (this.official_tick(post) < prune_tick) {
        this.remote_posts.delete(index);
      }
    }
    for (const [name, post] of this.local_posts.entries()) {
      if (this.official_tick(post) < prune_tick) {
        this.local_posts.delete(name);
      }
    }
  }
  // Ensure snapshots exist through at_tick, filling forward as needed.
  ensure_snapshots(at_tick, initial_tick) {
    if (!this.cache_enabled) {
      return;
    }
    if (this.snapshot_start_tick === null) {
      this.snapshot_start_tick = initial_tick;
    }
    let start_tick = this.snapshot_start_tick;
    if (start_tick === null) {
      return;
    }
    if (at_tick < start_tick) {
      return;
    }
    const stride = this.snapshot_stride;
    const target_tick = start_tick + Math.floor((at_tick - start_tick) / stride) * stride;
    let state;
    let current_tick;
    if (this.snapshots.size === 0) {
      state = this.init;
      current_tick = start_tick - 1;
    } else {
      const end_tick = start_tick + (this.snapshots.size - 1) * stride;
      state = this.snapshots.get(end_tick);
      current_tick = end_tick;
    }
    let next_tick = current_tick + stride;
    if (this.snapshots.size === 0) {
      next_tick = start_tick;
    }
    for (; next_tick <= target_tick; next_tick += stride) {
      state = this.advance_state(state, current_tick, next_tick);
      this.snapshots.set(next_tick, state);
      current_tick = next_tick;
    }
    const count = this.snapshots.size;
    if (count > this.snapshot_count) {
      const overflow = count - this.snapshot_count;
      const drop_until = start_tick + overflow * stride;
      for (let t = start_tick; t < drop_until; t += stride) {
        this.snapshots.delete(t);
      }
      start_tick = drop_until;
      this.snapshot_start_tick = start_tick;
    }
    this.prune_before_tick(start_tick);
  }
  // Add or replace an authoritative post and update the timeline.
  add_remote_post(post) {
    const tick = this.official_tick(post);
    if (post.index === 0 && this.initial_time_value === null) {
      const t = this.official_time(post);
      this.initial_time_value = t;
      this.initial_tick_value = this.time_to_tick(t);
    }
    const before_window = this.cache_enabled && this.snapshot_start_tick !== null && tick < this.snapshot_start_tick;
    if (before_window) {
      if (post.index > this.max_remote_index) {
        this.max_remote_index = post.index;
      }
      return;
    }
    if (this.remote_posts.has(post.index)) {
      return;
    }
    this.remote_posts.set(post.index, post);
    if (post.index > this.max_remote_index) {
      this.max_remote_index = post.index;
    }
    this.insert_remote_post(post, tick);
    this.invalidate_from_tick(tick);
  }
  // Add a local predicted post (applied after remote posts for the same tick).
  add_local_post(name, post) {
    if (this.local_posts.has(name)) {
      this.remove_local_post(name);
    }
    const tick = this.official_tick(post);
    const before_window = this.cache_enabled && this.snapshot_start_tick !== null && tick < this.snapshot_start_tick;
    if (before_window) {
      return;
    }
    this.local_posts.set(name, post);
    this.get_bucket(tick).local.push(post);
    this.invalidate_from_tick(tick);
  }
  // Remove a local predicted post once the authoritative echo arrives.
  remove_local_post(name) {
    const post = this.local_posts.get(name);
    if (!post) {
      return;
    }
    this.local_posts.delete(name);
    const tick = this.official_tick(post);
    const bucket = this.timeline.get(tick);
    if (bucket) {
      const index = bucket.local.indexOf(post);
      if (index !== -1) {
        bucket.local.splice(index, 1);
      } else {
        const by_name = bucket.local.findIndex((p) => p.name === name);
        if (by_name !== -1) {
          bucket.local.splice(by_name, 1);
        }
      }
      if (bucket.remote.length === 0 && bucket.local.length === 0) {
        this.timeline.delete(tick);
      }
    }
    this.invalidate_from_tick(tick);
  }
  // Apply on_tick plus any posts for a single tick.
  apply_tick(state, tick) {
    let next = this.on_tick(state);
    const bucket = this.timeline.get(tick);
    if (bucket) {
      for (const post of bucket.remote) {
        next = this.on_post(post.data, next);
      }
      for (const post of bucket.local) {
        next = this.on_post(post.data, next);
      }
    }
    return next;
  }
  // Recompute state from scratch without caching.
  compute_state_at_uncached(initial_tick, at_tick) {
    let state = this.init;
    for (let tick = initial_tick; tick <= at_tick; tick++) {
      state = this.apply_tick(state, tick);
    }
    return state;
  }
  // Convert a server-time timestamp to a tick index.
  time_to_tick(server_time) {
    return Math.floor(server_time * this.tick_rate / 1e3);
  }
  // Read the synchronized server time.
  server_time() {
    return this.client_api.server_time();
  }
  // Read the current server tick.
  server_tick() {
    return this.time_to_tick(this.server_time());
  }
  // Total authoritative remote posts seen so far.
  post_count() {
    return this.max_remote_index + 1;
  }
  // Build a render state from a past (remote) tick and current (local) tick.
  compute_render_state() {
    const curr_tick = this.server_tick();
    const tick_ms = 1e3 / this.tick_rate;
    const tol_ticks = Math.ceil(this.tolerance / tick_ms);
    const rtt_ms = this.client_api.ping();
    const half_rtt = isFinite(rtt_ms) ? Math.ceil(rtt_ms / 2 / tick_ms) : 0;
    const remote_lag = Math.max(tol_ticks, half_rtt + 1);
    const remote_tick = Math.max(0, curr_tick - remote_lag);
    const remote_state = this.compute_state_at(remote_tick);
    const local_state = this.compute_state_at(curr_tick);
    return this.smooth(remote_state, local_state);
  }
  // Return the authoritative time of the first post (index 0).
  initial_time() {
    if (this.initial_time_value !== null) {
      return this.initial_time_value;
    }
    const post = this.remote_posts.get(0);
    if (!post) {
      return null;
    }
    const t = this.official_time(post);
    this.initial_time_value = t;
    this.initial_tick_value = this.time_to_tick(t);
    return t;
  }
  // Return the authoritative tick of the first post (index 0).
  initial_tick() {
    if (this.initial_tick_value !== null) {
      return this.initial_tick_value;
    }
    const t = this.initial_time();
    if (t === null) {
      return null;
    }
    this.initial_tick_value = this.time_to_tick(t);
    return this.initial_tick_value;
  }
  // Compute state at an arbitrary tick, using snapshots when enabled.
  compute_state_at(at_tick) {
    const initial_tick = this.initial_tick();
    if (initial_tick === null) {
      return this.init;
    }
    if (at_tick < initial_tick) {
      return this.init;
    }
    if (!this.cache_enabled) {
      return this.compute_state_at_uncached(initial_tick, at_tick);
    }
    this.ensure_snapshots(at_tick, initial_tick);
    const start_tick = this.snapshot_start_tick;
    if (start_tick === null || this.snapshots.size === 0) {
      return this.init;
    }
    if (at_tick < start_tick) {
      return this.snapshots.get(start_tick) ?? this.init;
    }
    const stride = this.snapshot_stride;
    const end_tick = start_tick + (this.snapshots.size - 1) * stride;
    const max_index = Math.floor((end_tick - start_tick) / stride);
    const snap_index = Math.floor((at_tick - start_tick) / stride);
    const index = Math.min(snap_index, max_index);
    const snap_tick = start_tick + index * stride;
    const base_state = this.snapshots.get(snap_tick) ?? this.init;
    return this.advance_state(base_state, snap_tick, at_tick);
  }
  // Post data to the room.
  post(data) {
    const name = this.client_api.post(this.room, data, this.packer);
    const t = this.server_time();
    const local_post = {
      room: this.room,
      index: -1,
      server_time: t,
      client_time: t,
      name,
      data
    };
    this.add_local_post(name, local_post);
  }
  // Convenience for compute_state_at(current_server_tick).
  compute_current_state() {
    return this.compute_state_at(this.server_tick());
  }
  on_sync(callback) {
    this.client_api.on_sync(callback);
  }
  ping() {
    return this.client_api.ping();
  }
  static gen_name() {
    return gen_name();
  }
};
__publicField(_VibiNet, "game", _VibiNet);
var VibiNet = _VibiNet;
export {
  OFFICIAL_SERVER_URL,
  VibiNet,
  create_client,
  gen_name
};
