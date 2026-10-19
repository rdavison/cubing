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
-/

open Lean Elab
open Verso Doc Elab Output Html
open Verso.Genre Manual
open Cubing.Cube3x3

namespace CubingSite

/-- One letter per colour, named by the face whose centre has it. -/
def faceLetter : Face → String
  | .U => "U" | .D => "D" | .F => "F" | .B => "B" | .L => "L" | .R => "R"

/-- The 54 colours of a state, face by face in the order U R F D L B, each face row by row. -/
def netString (g : Cube) : String :=
  String.join <| [Face.U, .R, .F, .D, .L, .B].flatMap fun f =>
    (List.finRange 9).map fun i => faceLetter (colors g (netFacelet f i))

/-- The moves of a sequence and the colours of every state along it, from solved onwards. -/
def cubeFrames (s : String) : Option (List String × List String) := do
  let ms ← parseAlg? s
  pure (ms.map Move.toToken, (List.range (ms.length + 1)).map fun k => netString (alg (ms.take k)))

-- A cube state, or sequence of states, drawn as an unfolded net with controls to step through.
block_extension Block.cube (moves : List String) (frames : List String) where
  data := Json.mkObj [("moves", toJson moves), ("frames", toJson frames)]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ data _ => do
    pure {{<div class="tyj-cube" "data-cube"={{data.compress}}></div>}}
  extraCss := [r##"
.tyj-cube { margin: 1rem 0; display: flex; flex-direction: column; align-items: center; gap: 0.5rem; }
.tyj-cube svg { max-width: 100%; height: auto; }
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
  function draw(svg, frame) {
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
  function setup(el) {
    const { moves, frames } = JSON.parse(el.dataset.cube);
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("viewBox", `0 0 ${4 * face} ${3 * face}`);
    svg.setAttribute("width", 4 * face * 1.4);
    svg.setAttribute("role", "img");
    el.appendChild(svg);
    let step = frames.length - 1;
    if (moves.length === 0) { draw(svg, frames[0]); svg.setAttribute("aria-label", "solved cube"); return; }
    const list = document.createElement("div"); list.className = "tyj-moves";
    const spans = moves.map(m => { const s = document.createElement("span"); s.textContent = m; list.appendChild(s); return s; });
    const controls = document.createElement("div"); controls.className = "tyj-controls";
    const mk = (label, title, fn) => { const b = document.createElement("button"); b.textContent = label; b.title = title; b.onclick = fn; controls.appendChild(b); return b; };
    const first = mk("⏮", "Start", () => go(0)), back = mk("◀", "Back one move", () => go(step - 1));
    const fwd = mk("▶", "Forward one move", () => go(step + 1)), last = mk("⏭", "End", () => go(frames.length - 1));
    function go(k) {
      step = Math.max(0, Math.min(frames.length - 1, k));
      draw(svg, frames[step]);
      spans.forEach((s, i) => { s.className = i < step ? "done" : (i === step ? "next" : ""); });
      first.disabled = back.disabled = step === 0;
      fwd.disabled = last.disabled = step === frames.length - 1;
      svg.setAttribute("aria-label", `cube after ${step} of ${moves.length} moves: ${moves.slice(0, step).join(" ")}`);
    }
    el.appendChild(list); el.appendChild(controls);
    go(step);
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
    let some (moves, frames) ← unsafe Term.evalTerm (Option (List String × List String))
        (← Term.elabType (← `(Option (List String × List String))))
        (← `(CubingSite.cubeFrames $(quote src)))
      | throwErrorAt code "not a sequence of Singmaster moves: {src}"
    ``(Verso.Doc.Block.other (CubingSite.Block.cube $(quote moves) $(quote frames)) #[])

end CubingSite
