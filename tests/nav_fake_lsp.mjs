// Process-boundary double for a Lean LSP child: speaks real Content-Length framing,
// records every request, and replies with an echo unless a behavior overrides it.
// No Lean, no Lake, no project code runs.
import { EventEmitter } from "node:events";
import { PassThrough } from "node:stream";

export function makeFakeLsp(log, behavior = {}) {
  log.spawns ??= [];
  log.requests ??= [];
  return function fakeSpawn(command, args, opts) {
    const child = new EventEmitter();
    const id = log.spawns.length + 1;
    child.stdout = new PassThrough();
    child.pid = 4000 + id;
    child.exitCode = null;
    log.spawns.push({ id, command, args, opts, child });
    let buf = Buffer.alloc(0);
    const send = (obj) => {
      const body = JSON.stringify(obj);
      child.stdout.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
    };
    const handle = (msg) => {
      // Like real Lean: opening/changing a document starts processing, then reports it done.
      if (msg.id === undefined && (msg.method === "textDocument/didOpen" || msg.method === "textDocument/didChange")) {
        const uri = msg.params?.textDocument?.uri;
        if (behavior.__neverFinish) return;
        return setImmediate(() => send({ jsonrpc: "2.0", method: "$/lean/fileProgress", params: { textDocument: { uri }, processing: [] } }));
      }
      if (msg.id === undefined || !msg.method) return; // notification
      log.requests.push({ session: id, method: msg.method, params: msg.params });
      setImmediate(() => {
        if (msg.method === "initialize") return send({ jsonrpc: "2.0", id: msg.id, result: { capabilities: {} } });
        const custom = behavior[msg.method];
        const out = custom ? custom(msg.params) : { echo: msg.method, params: msg.params };
        if (out && out.__error) return send({ jsonrpc: "2.0", id: msg.id, error: { code: -32603, message: out.__error } });
        send({ jsonrpc: "2.0", id: msg.id, result: out });
      });
    };
    const drain = () => {
      for (;;) {
        const idx = buf.indexOf("\r\n\r\n");
        if (idx === -1) return;
        const len = Number(/Content-Length:\s*(\d+)/i.exec(buf.subarray(0, idx).toString())?.[1]);
        if (buf.length < idx + 4 + len) return;
        const body = buf.subarray(idx + 4, idx + 4 + len).toString("utf-8");
        buf = buf.subarray(idx + 4 + len);
        handle(JSON.parse(body));
      }
    };
    child.stdin = {
      write(chunk) { buf = Buffer.concat([buf, Buffer.from(chunk)]); drain(); return true; },
      end() {}, destroy() {}, on() {}, once() {},
    };
    child.kill = () => { child.exitCode = 0; child.emit("exit", 0); return true; };
    return child;
  };
}
