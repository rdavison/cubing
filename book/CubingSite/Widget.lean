import VersoManual
import Cubing

/-!
The cube widget. A code block such as

```
```cube
R U R' U'
```
```

is parsed by the library's own Singmaster parser while the book is elaborated. Every intermediate
state is coloured by `Cubing.Cube3x3.colors`, the colouring proved to agree with the sticker
action. The page receives only the finished colours, so the browser draws but never computes:
no picture in the book can disagree with the theorems. A move the parser rejects fails the build.

The widget draws either the unfolded net or, where the browser has WebGPU, a cube in 3D. The 3D
view places each facelet by `Facelet.cubie` and `Facelet.normal`, and animates a move by turning
the facelets in `Face.layer` through the rotation `Face.turnVec`. `colors_move_mul` proves that
this rotation carries each frame's colours exactly to the next frame's, so the animation cannot
disagree with the model either.
-/

open Lean Elab
open Verso Doc Elab Output Html
open Verso.Genre Manual
open Cubing.Cube3x3

namespace CubingSite

/-- One letter per colour, named by the face whose centre has it. -/
def faceLetter : Face → String
  | .U => "U" | .D => "D" | .F => "F" | .B => "B" | .L => "L" | .R => "R"

/-- The faces in the order the widget lists them. -/
def faceOrder : List Face := [.U, .R, .F, .D, .L, .B]

/-- The 54 facelets of the net, face by face in {name}`faceOrder`, each face row by row. -/
def netFacelets : List Facelet :=
  faceOrder.flatMap fun f => (List.finRange 9).map (netFacelet f)

/-- The 54 colours of a state, in the order of {name}`netFacelets`. -/
def netString (g : Cube) : String :=
  String.join <| netFacelets.map fun p => faceLetter (colors g p)

/-- A vector as a JSON-ready list. -/
def vecList (v : Vec) : List Int := [v.1, v.2.1, v.2.2]

/-- For each facelet of the net, its cubie's centre followed by its outward direction. -/
def netGeometry : List (List Int) :=
  netFacelets.map fun p => vecList p.cubie ++ vecList p.normal

/-- For each face, the positions in the net of the facelets that turn with it. -/
def netLayers : List (List Nat) :=
  faceOrder.map fun f => (netFacelets.zipIdx.filter fun (p, _) => decide (f.layer p)).map (·.2)

/-- The outward normal of each face: the axis it turns about. -/
def faceAxes : List (List Int) := faceOrder.map fun f => vecList f.normal

/-- A move as the face that turns, by its index in {name}`faceOrder`, and the angle in quarter
turns anticlockwise about that face's normal. A clockwise turn is {lean}`-1`. -/
def moveTurn (m : Move) : List Int :=
  [faceOrder.idxOf m.face, match m.turn with | .cw => -1 | .half => -2 | .ccw => 1]

/-- The moves of a sequence, how each one turns, and the colours of every state along it, from
solved onwards. -/
def cubeFrames (s : String) : Option (List String × List (List Int) × List String) := do
  let ms ← parseAlg? s
  pure (ms.map Move.toToken, ms.map moveTurn,
    (List.range (ms.length + 1)).map fun k => netString (alg (ms.take k)))

-- A cube state, or sequence of states, drawn as an unfolded net or in 3D, with controls to step
-- through.
block_extension Block.cube (moves : List String) (turns : List (List Int)) (frames : List String) where
  data := Json.mkObj [("moves", toJson moves), ("turns", toJson turns), ("frames", toJson frames),
    ("geometry", toJson netGeometry), ("layers", toJson netLayers), ("axes", toJson faceAxes)]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ data _ => do
    pure {{<div class="tyj-cube" "data-cube"={{data.compress}}></div>}}
  extraCss := [r##"
.tyj-cube { margin: 1rem 0; display: flex; flex-direction: column; align-items: center; gap: 0.5rem; }
.tyj-cube svg { max-width: 100%; height: auto; }
.tyj-cube canvas { width: min(300px, 100%); aspect-ratio: 1; touch-action: none; cursor: grab; }
.tyj-cube canvas:active { cursor: grabbing; }
.tyj-cube [hidden] { display: none; }
.tyj-cube .tyj-moves { font-family: var(--verso-code-font-family, monospace); display: flex; flex-wrap: wrap; gap: 0.35rem; justify-content: center; }
.tyj-cube .tyj-moves span { padding: 0 0.2rem; border-radius: 3px; }
.tyj-cube .tyj-moves span.done { opacity: 0.45; }
.tyj-cube .tyj-moves span.next { outline: 2px solid currentColor; }
.tyj-cube .tyj-controls { display: flex; gap: 0.4rem; }
.tyj-cube button { font: inherit; padding: 0.15rem 0.6rem; cursor: pointer; border: 1px solid currentColor; background: transparent; color: inherit; border-radius: 4px; }
.tyj-cube button:disabled { opacity: 0.35; cursor: default; }
"##]
  extraJs := [r##"
(function () {
  const colours = { U: "#ffffff", R: "#c41e3a", F: "#009e60", D: "#ffd500", L: "#ff5800", B: "#0051ba" };
  // Where each face sits in the cross-shaped net, in units of one face.
  const place = { U: [1, 0], L: [0, 1], F: [1, 1], R: [2, 1], B: [3, 1], D: [1, 2] };
  const order = ["U", "R", "F", "D", "L", "B"];
  const cell = 18, gap = 4, face = 3 * cell + gap;
  function drawNet(svg, frame) {
    svg.textContent = "";
    order.forEach((f, fi) => {
      const [fx, fy] = place[f];
      for (let i = 0; i < 9; i++) {
        const r = document.createElementNS("http://www.w3.org/2000/svg", "rect");
        r.setAttribute("x", fx * face + (i % 3) * cell + 1);
        r.setAttribute("y", fy * face + Math.floor(i / 3) * cell + 1);
        r.setAttribute("width", cell - 2); r.setAttribute("height", cell - 2);
        r.setAttribute("rx", 2);
        r.setAttribute("fill", colours[frame[fi * 9 + i]]);
        r.setAttribute("stroke", "#222"); r.setAttribute("stroke-width", 1);
        svg.appendChild(r);
      }
    });
  }

  // ---- 3D view. Positions, layers and turn angles all come from the page data; this code only
  // rotates and projects them.
  const rgb = Object.fromEntries(Object.entries(colours).map(([k, h]) =>
    [k, [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16) / 255)]));
  const body = [0.08, 0.08, 0.09];
  const shader = `
struct U { viewProj : mat4x4f, light : vec4f };
@group(0) @binding(0) var<uniform> u : U;
struct V { @builtin(position) pos : vec4f, @location(0) n : vec3f, @location(1) c : vec3f };
@vertex fn vs(@location(0) p : vec3f, @location(1) n : vec3f, @location(2) c : vec3f) -> V {
  var o : V; o.pos = u.viewProj * vec4f(p, 1.0); o.n = n; o.c = c; return o;
}
@fragment fn fs(i : V) -> @location(0) vec4f {
  let k = 0.55 + 0.45 * max(dot(normalize(i.n), u.light.xyz), 0.0);
  return vec4f(i.c * k, 1.0);
}`;
  let gpu = null;
  function getGpu() {
    if (gpu) return gpu;
    gpu = (async () => {
      if (!navigator.gpu) return null;
      const adapter = await navigator.gpu.requestAdapter();
      if (!adapter) return null;
      const device = await adapter.requestDevice();
      const format = navigator.gpu.getPreferredCanvasFormat();
      const module = device.createShaderModule({ code: shader });
      const pipeline = device.createRenderPipeline({
        layout: "auto",
        vertex: { module, entryPoint: "vs", buffers: [{ arrayStride: 36, attributes: [
          { shaderLocation: 0, offset: 0, format: "float32x3" },
          { shaderLocation: 1, offset: 12, format: "float32x3" },
          { shaderLocation: 2, offset: 24, format: "float32x3" }] }] },
        fragment: { module, entryPoint: "fs", targets: [{ format }] },
        primitive: { topology: "triangle-list", cullMode: "back" },
        depthStencil: { format: "depth24plus", depthWriteEnabled: true, depthCompare: "less" },
        multisample: { count: 4 },
      });
      const g = { device, format, pipeline, lost: [] };
      device.lost.then(() => { gpu = null; g.lost.forEach(f => f()); });
      return g;
    })().catch(() => null);
    return gpu;
  }

  const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const norm = a => { const l = Math.hypot(...a); return [a[0] / l, a[1] / l, a[2] / l]; };
  // Rotation by `angle` radians about the unit axis `n`, right-handed.
  function rotation(n, angle) {
    const c = Math.cos(angle), s = Math.sin(angle);
    return v => { const d = dot(n, v), x = cross(n, v);
      return [0, 1, 2].map(i => v[i] * c + x[i] * s + n[i] * d * (1 - c)); };
  }
  function mat4mul(a, b) {
    const o = new Float32Array(16);
    for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) {
      let s = 0; for (let k = 0; k < 4; k++) s += a[k * 4 + r] * b[c * 4 + k]; o[c * 4 + r] = s;
    }
    return o;
  }
  function viewProj(yaw, pitch, aspect) {
    const d = 12, eye = [d * Math.cos(pitch) * Math.sin(yaw), d * Math.sin(pitch), d * Math.cos(pitch) * Math.cos(yaw)];
    const z = norm(eye), x = norm(cross([0, 1, 0], z)), y = cross(z, x);
    const view = [x[0], y[0], z[0], 0, x[1], y[1], z[1], 0, x[2], y[2], z[2], 0, -dot(x, eye), -dot(y, eye), -dot(z, eye), 1];
    const f = 1 / Math.tan(0.5 / 2), near = 4, far = 20;
    const proj = [f / aspect, 0, 0, 0, 0, f, 0, 0, 0, 0, far / (near - far), -1, 0, 0, near * far / (near - far), 0];
    return { m: mat4mul(proj, view), eye: z };
  }
  // The two unit directions spanning the plane perpendicular to an axis-aligned normal.
  function tangents(n) {
    const a = n[0] !== 0 ? [0, 1, 0] : [1, 0, 0];
    return [a, cross(n, a)];
  }
  function pushQuad(out, centre, n, half, colour, rot) {
    const [s, t] = tangents(n);
    const corner = (i, j) => [0, 1, 2].map(k => centre[k] + (s[k] * i + t[k] * j) * half);
    let q = [corner(-1, -1), corner(1, -1), corner(1, 1), corner(-1, 1)];
    if (dot(cross(sub(q[1], q[0]), sub(q[2], q[0])), n) < 0) q.reverse();
    let nn = n;
    if (rot) { q = q.map(rot); nn = rot(n); }
    for (const i of [0, 1, 2, 0, 2, 3]) out.push(...q[i], ...nn, ...colour);
  }
  const axesOf = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]];
  const cubies = [];
  for (let x = -1; x <= 1; x++) for (let y = -1; y <= 1; y++) for (let z = -1; z <= 1; z++)
    if (x || y || z) cubies.push([x, y, z]);

  // Build the triangles for one frame; while a layer turns, its stickers (from the page's layer
  // table) and the cubies on it are rotated by `rot` about `axis`.
  function buildMesh(data, frame, turning) {
    const out = [];
    const inLayer = new Set(turning ? data.layers[turning.face] : []);
    for (const c of cubies) {
      const rot = turning && dot(c, turning.axis) === 1 ? turning.rot : null;
      for (const n of axesOf) pushQuad(out, c.map((v, i) => v + n[i] * 0.48), n, 0.48, body, rot);
    }
    data.geometry.forEach((g, i) => {
      const c = g.slice(0, 3), n = g.slice(3, 6);
      const centre = c.map((v, k) => v + n[k] * 0.49);
      pushQuad(out, centre, n, 0.4, rgb[frame[i]], inLayer.has(i) ? turning.rot : null);
    });
    return new Float32Array(out);
  }

  function makeView3d(g, canvas, data) {
    const { device, format, pipeline } = g;
    const ctx = canvas.getContext("webgpu");
    ctx.configure({ device, format, alphaMode: "premultiplied" });
    const uniform = device.createBuffer({ size: 80, usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST });
    const bind = device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries: [{ binding: 0, resource: { buffer: uniform } }] });
    let vbuf = null, msaa = null, depth = null;
    let yaw = 0.6, pitch = 0.5;
    const view = { frame: null, turning: null };
    function render() {
      const dpr = window.devicePixelRatio || 1;
      const w = Math.max(1, Math.round(canvas.clientWidth * dpr)), h = Math.max(1, Math.round(canvas.clientHeight * dpr));
      if (canvas.width !== w || canvas.height !== h || !msaa) {
        canvas.width = w; canvas.height = h;
        msaa?.destroy(); depth?.destroy();
        msaa = device.createTexture({ size: [w, h], sampleCount: 4, format, usage: GPUTextureUsage.RENDER_ATTACHMENT });
        depth = device.createTexture({ size: [w, h], sampleCount: 4, format: "depth24plus", usage: GPUTextureUsage.RENDER_ATTACHMENT });
      }
      const mesh = buildMesh(data, view.frame, view.turning);
      if (!vbuf || vbuf.size < mesh.byteLength) {
        vbuf?.destroy();
        vbuf = device.createBuffer({ size: mesh.byteLength, usage: GPUBufferUsage.VERTEX | GPUBufferUsage.COPY_DST });
      }
      device.queue.writeBuffer(vbuf, 0, mesh);
      const vp = viewProj(yaw, pitch, w / h);
      const light = norm([vp.eye[0] + 0.3, vp.eye[1] + 0.8, vp.eye[2]]);
      const u = new Float32Array(20); u.set(vp.m); u.set(light, 16);
      device.queue.writeBuffer(uniform, 0, u);
      const enc = device.createCommandEncoder();
      const pass = enc.beginRenderPass({
        colorAttachments: [{ view: msaa.createView(), resolveTarget: ctx.getCurrentTexture().createView(),
          clearValue: [0, 0, 0, 0], loadOp: "clear", storeOp: "discard" }],
        depthStencilAttachment: { view: depth.createView(), depthClearValue: 1, depthLoadOp: "clear", depthStoreOp: "discard" },
      });
      pass.setPipeline(pipeline); pass.setBindGroup(0, bind); pass.setVertexBuffer(0, vbuf);
      pass.draw(mesh.length / 9); pass.end();
      device.queue.submit([enc.finish()]);
    }
    let queued = false;
    const request = () => { if (!queued) { queued = true; requestAnimationFrame(() => { queued = false; render(); }); } };
    let drag = null;
    canvas.addEventListener("pointerdown", e => { drag = [e.clientX, e.clientY]; canvas.setPointerCapture(e.pointerId); });
    canvas.addEventListener("pointermove", e => {
      if (!drag) return;
      yaw -= (e.clientX - drag[0]) * 0.01;
      pitch = Math.max(-1.4, Math.min(1.4, pitch + (e.clientY - drag[1]) * 0.01));
      drag = [e.clientX, e.clientY]; request();
    });
    const end = () => { drag = null; };
    canvas.addEventListener("pointerup", end); canvas.addEventListener("pointercancel", end);
    new ResizeObserver(request).observe(canvas);
    let anim = null;
    function finish() { if (anim) { cancelAnimationFrame(anim.raf); view.frame = anim.target; view.turning = null; anim = null; } }
    return {
      show(frame) { finish(); view.frame = frame; view.turning = null; request(); },
      // Turn layer `face` by `quarters` (anticlockwise about its normal) starting from `from`,
      // then rest on `target`.
      animate(from, face, quarters, target) {
        finish();
        const axis = data.axes[face], total = quarters * Math.PI / 2, ms = 180 + 90 * Math.abs(quarters);
        const t0 = performance.now();
        anim = { target };
        const step = now => {
          const t = Math.min(1, (now - t0) / ms), e = t < 0.5 ? 2 * t * t : 1 - 2 * (1 - t) * (1 - t);
          if (t >= 1) { finish(); render(); return; }
          view.frame = from; view.turning = { face, axis, rot: rotation(axis, total * e) };
          render(); anim.raf = requestAnimationFrame(step);
        };
        anim.raf = requestAnimationFrame(step);
      },
      resize: request,
    };
  }

  const reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
  function setup(el) {
    const data = JSON.parse(el.dataset.cube);
    const { moves, turns, frames } = data;
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("viewBox", `0 0 ${4 * face} ${3 * face}`);
    svg.setAttribute("width", 4 * face * 1.4);
    svg.setAttribute("role", "img");
    el.appendChild(svg);
    const canvas = document.createElement("canvas");
    canvas.setAttribute("role", "img"); canvas.hidden = true;
    el.appendChild(canvas);
    let step = frames.length - 1;
    const list = document.createElement("div"); list.className = "tyj-moves";
    const spans = moves.map(m => { const s = document.createElement("span"); s.textContent = m; list.appendChild(s); return s; });
    const controls = document.createElement("div"); controls.className = "tyj-controls";
    const mk = (label, title, fn) => { const b = document.createElement("button"); b.textContent = label; b.title = title; b.onclick = fn; controls.appendChild(b); return b; };
    let first, back, fwd, last;
    if (moves.length > 0) {
      first = mk("⏮", "Start", () => go(0)); back = mk("◀", "Back one move", () => go(step - 1));
      fwd = mk("▶", "Forward one move", () => go(step + 1)); last = mk("⏭", "End", () => go(frames.length - 1));
      el.appendChild(list);
    }
    const toggle = mk("3D", "Switch view", () => setMode(mode === "3d" ? "net" : "3d"));
    toggle.hidden = true;
    el.appendChild(controls);
    let mode = "net", view3d = null;
    function setMode(m) {
      mode = m;
      svg.toggleAttribute("hidden", m !== "net"); canvas.hidden = m !== "3d";
      toggle.textContent = m === "3d" ? "Net" : "3D";
      if (m === "3d") view3d.show(frames[step]);
    }
    function label() {
      return moves.length === 0 ? "solved cube"
        : `cube after ${step} of ${moves.length} moves: ${moves.slice(0, step).join(" ")}`;
    }
    function go(k) {
      const prev = step;
      step = Math.max(0, Math.min(frames.length - 1, k));
      drawNet(svg, frames[step]);
      if (view3d && mode === "3d") {
        if (Math.abs(step - prev) === 1 && !reduceMotion.matches) {
          const i = Math.min(step, prev), [f, q] = turns[i];
          view3d.animate(frames[prev], f, step > prev ? q : -q, frames[step]);
        } else view3d.show(frames[step]);
      }
      spans.forEach((s, i) => { s.className = i < step ? "done" : (i === step ? "next" : ""); });
      if (first) {
        first.disabled = back.disabled = step === 0;
        fwd.disabled = last.disabled = step === frames.length - 1;
      }
      svg.setAttribute("aria-label", label()); canvas.setAttribute("aria-label", label());
    }
    go(step);
    if (!navigator.gpu) return;
    svg.style.visibility = "hidden";
    getGpu().then(g => {
      svg.style.visibility = "";
      if (!g) return;
      view3d = makeView3d(g, canvas, data);
      g.lost.push(() => { view3d = null; toggle.hidden = true; setMode("net"); });
      toggle.hidden = false;
      setMode("3d");
    });
  }
  function init() { document.querySelectorAll(".tyj-cube").forEach(setup); }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init); else init();
})();
"##]

/-- Draw the state a Singmaster sequence produces, with controls to step through it. -/
@[code_block]
def cube : CodeBlockExpanderOf Unit
  | (), code => do
    let src := code.getString.trimAscii.copy
    let some (moves, turns, frames) ← unsafe Term.evalTerm
        (Option (List String × List (List Int) × List String))
        (← Term.elabType (← `(Option (List String × List (List Int) × List String))))
        (← `(CubingSite.cubeFrames $(quote src)))
      | throwErrorAt code "not a sequence of Singmaster moves: {src}"
    ``(Verso.Doc.Block.other (CubingSite.Block.cube $(quote moves) $(quote turns) $(quote frames)) #[])

end CubingSite
