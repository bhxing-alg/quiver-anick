    "use strict";

    const $ = (id) => document.getElementById(id);
    let lastComputation = null;
    let lastHHResult = null;
    let hhWorker = null;
    let hhRequestSeq = 0;
    const hhPendingRequests = new Map();
    let hhDegreeCache = { key: "", cohomology: new Map(), homology: new Map() };
    let FIELD_CHAR = 0n;

    function absBig(n) {
      return n < 0n ? -n : n;
    }

    function modBig(n, p) {
      const r = n % p;
      return r < 0n ? r + p : r;
    }

    function modInverseBig(a, p) {
      let t = 0n;
      let nextT = 1n;
      let r = p;
      let nextR = modBig(a, p);
      while (nextR !== 0n) {
        const q = r / nextR;
        [t, nextT] = [nextT, t - q * nextT];
        [r, nextR] = [nextR, r - q * nextR];
      }
      if (r !== 1n) throw new Error("Coefficient denominator is not invertible in characteristic " + p.toString());
      return modBig(t, p);
    }

    function setFieldCharacteristic(p) {
      FIELD_CHAR = BigInt(p || 0);
    }

    function gcdBig(a, b) {
      a = absBig(a);
      b = absBig(b);
      while (b !== 0n) {
        const t = a % b;
        a = b;
        b = t;
      }
      return a === 0n ? 1n : a;
    }

    class Rat {
      constructor(n, d = 1n) {
        if (d === 0n) throw new Error("Denominator cannot be zero");
        if (d < 0n) {
          n = -n;
          d = -d;
        }
        if (FIELD_CHAR > 0n) {
          const den = modBig(d, FIELD_CHAR);
          if (den === 0n) throw new Error("Coefficient denominator is divisible by char k = " + FIELD_CHAR.toString());
          this.n = modBig(modBig(n, FIELD_CHAR) * modInverseBig(den, FIELD_CHAR), FIELD_CHAR);
          this.d = 1n;
          return;
        }
        const g = gcdBig(n, d);
        this.n = n / g;
        this.d = d / g;
      }

      static zero() { return new Rat(0n, 1n); }
      static one() { return new Rat(1n, 1n); }
      static minusOne() { return new Rat(-1n, 1n); }

      static fromDecimal(raw) {
        let s = raw.trim();
        let sign = 1n;
        if (s.startsWith("+")) s = s.slice(1);
        if (s.startsWith("-")) {
          sign = -1n;
          s = s.slice(1);
        }
        if (!s.includes(".")) return new Rat(sign * BigInt(s || "0"), 1n);
        const [whole, frac] = s.split(".");
        const scale = 10n ** BigInt(frac.length);
        const num = BigInt(whole || "0") * scale + BigInt(frac || "0");
        return new Rat(sign * num, scale);
      }

      static parse(raw) {
        const s = raw.trim();
        if (!s) throw new Error("Empty coefficient");
        const parts = s.split("/");
        if (parts.length === 1) return Rat.fromDecimal(parts[0]);
        if (parts.length === 2) return Rat.fromDecimal(parts[0]).div(Rat.fromDecimal(parts[1]));
        throw new Error("Cannot parse coefficient: " + raw);
      }

      add(x) { return new Rat(this.n * x.d + x.n * this.d, this.d * x.d); }
      sub(x) { return new Rat(this.n * x.d - x.n * this.d, this.d * x.d); }
      mul(x) { return new Rat(this.n * x.n, this.d * x.d); }
      div(x) {
        if (x.n === 0n) throw new Error("Division by zero");
        return new Rat(this.n * x.d, this.d * x.n);
      }
      neg() { return new Rat(-this.n, this.d); }
      isZero() { return this.n === 0n; }
      isOne() { return this.n === this.d; }
      isMinusOne() { return this.n === -this.d; }
      abs() { return this.n < 0n ? this.neg() : this; }
      eq(x) { return this.n === x.n && this.d === x.d; }
      sign() { return this.n < 0n ? -1 : this.n > 0n ? 1 : 0; }
      toString() {
        if (this.d === 1n) return this.n.toString();
        return this.n.toString() + "/" + this.d.toString();
      }
    }

    function keyOf(path) {
      return path.join(" ");
    }

    function pathOf(key) {
      return key ? key.split(" ") : [];
    }

    function samePath(a, b) {
      if (a.length !== b.length) return false;
      for (let i = 0; i < a.length; i++) {
        if (a[i] !== b[i]) return false;
      }
      return true;
    }

    function formatPath(path) {
      return path.length ? path.join(" ") : "e";
    }

    function pathForDisplay(path, ctx) {
      return path.slice();
    }

    function pathFromInputTokens(tokens, ctx) {
      return tokens.slice();
    }

    function displayPath(path, ctx) {
      return formatPath(pathForDisplay(path, ctx));
    }

    function comparePaths(a, b, ctx) {
      const da = pathForDisplay(a, ctx);
      const db = pathForDisplay(b, ctx);
      if (da.length !== db.length) return da.length > db.length ? 1 : -1;
      for (let i = 0; i < da.length; i++) {
        if (da[i] === db[i]) continue;
        const ra = ctx.rank.get(da[i]);
        const rb = ctx.rank.get(db[i]);
        if (ra == null || rb == null) throw new Error("Arrow is missing from the order on Q1: " + (ra == null ? da[i] : db[i]));
        if (ctx.earlierLarge) return ra < rb ? 1 : -1;
        return ra > rb ? 1 : -1;
      }
      return 0;
    }

    function findOccurrences(path, sub) {
      const out = [];
      if (!sub.length || sub.length > path.length) return out;
      for (let i = 0; i <= path.length - sub.length; i++) {
        let ok = true;
        for (let j = 0; j < sub.length; j++) {
          if (path[i + j] !== sub[j]) {
            ok = false;
            break;
          }
        }
        if (ok) out.push(i);
      }
      return out;
    }

    function containsFactor(path, factor) {
      return findOccurrences(path, factor).length > 0;
    }

    function pathSource(path, ctx) {
      if (!path.length) return null;
      const arrow = ctx.arrows.get(path[0]);
      return arrow ? arrow.source : null;
    }

    function pathTarget(path, ctx) {
      if (!path.length) return null;
      const arrow = ctx.arrows.get(path[path.length - 1]);
      return arrow ? arrow.target : null;
    }

    function isComposable(path, ctx) {
      for (let i = 0; i < path.length - 1; i++) {
        const left = ctx.arrows.get(path[i]);
        const right = ctx.arrows.get(path[i + 1]);
        if (!left || !right) return false;
        if (left.target !== right.source) return false;
      }
      return true;
    }

    function canConcat(a, b, ctx) {
      if (!a.length || !b.length) return true;
      return pathTarget(a, ctx) === pathSource(b, ctx);
    }

    class Poly {
      constructor(terms) {
        this.terms = new Map(terms || []);
        this.clean();
      }

      static zero() {
        return new Poly();
      }

      clone() {
        return new Poly(this.terms);
      }

      clean() {
        for (const [k, c] of [...this.terms.entries()]) {
          if (c.isZero()) this.terms.delete(k);
        }
        return this;
      }

      addTerm(path, coeff) {
        if (coeff.isZero()) return this;
        const k = keyOf(path);
        const old = this.terms.get(k) || Rat.zero();
        const next = old.add(coeff);
        if (next.isZero()) this.terms.delete(k);
        else this.terms.set(k, next);
        return this;
      }

      add(other, scale = Rat.one()) {
        const out = this.clone();
        for (const [k, c] of other.terms.entries()) {
          out.addTerm(pathOf(k), c.mul(scale));
        }
        return out.clean();
      }

      sub(other) {
        return this.add(other, Rat.minusOne());
      }

      scale(c) {
        const out = Poly.zero();
        if (c.isZero()) return out;
        for (const [k, v] of this.terms.entries()) {
          out.terms.set(k, v.mul(c));
        }
        return out.clean();
      }

      isZero() {
        return this.terms.size === 0;
      }

      leading(ctx) {
        let bestKey = null;
        for (const k of this.terms.keys()) {
          if (bestKey == null || comparePaths(pathOf(k), pathOf(bestKey), ctx) > 0) {
            bestKey = k;
          }
        }
        if (bestKey == null) return null;
        return { key: bestKey, path: pathOf(bestKey), coeff: this.terms.get(bestKey) };
      }

      monic(ctx) {
        const lt = this.leading(ctx);
        if (!lt) return this.clone();
        return this.scale(Rat.one().div(lt.coeff));
      }

      signature(ctx) {
        return [...this.terms.entries()]
          .sort((a, b) => -comparePaths(pathOf(a[0]), pathOf(b[0]), ctx))
          .map(([k, c]) => c.toString() + "*" + k)
          .join("|");
      }
    }

    function multiplyPoly(poly, prefix, suffix) {
      const out = Poly.zero();
      for (const [k, coeff] of poly.terms.entries()) {
        out.addTerm(prefix.concat(pathOf(k), suffix), coeff);
      }
      return out;
    }

    function formatPoly(poly, ctx) {
      if (poly.isZero()) return "0";
      const entries = [...poly.terms.entries()]
        .sort((a, b) => -comparePaths(pathOf(a[0]), pathOf(b[0]), ctx));
      let s = "";
      entries.forEach(([k, coeff], index) => {
        const sign = coeff.sign();
        const abs = coeff.abs();
        const path = pathOf(k);
        let body = displayPath(path, ctx);
        if (!abs.isOne()) body = abs.toString() + " " + body;
        if (index === 0) s += sign < 0 ? "- " + body : body;
        else s += sign < 0 ? " - " + body : " + " + body;
      });
      return s;
    }

    function normalizeMath(raw) {
      return raw
        .replace(/\u2212|\u2013|\u2014/g, "-")
        .replace(/\u00b7|\u22c5/g, "*")
        .replace(/\r/g, "");
    }

    function splitNames(text) {
      return normalizeMath(text)
        .split(/[,\s]+/)
        .map((x) => x.trim())
        .filter(Boolean);
    }

    function stripComment(line) {
      return line.replace(/#.*/, "").trim();
    }

    function parseVertices(text) {
      const vertices = splitNames(text);
      if (!vertices.length) throw new Error("Please enter the vertex set Q0");
      return vertices;
    }

    function parseArrows(text, vertices) {
      const vset = new Set(vertices);
      const arrows = new Map();
      const lines = normalizeMath(text).split("\n").map(stripComment).filter(Boolean);
      if (!lines.length) throw new Error("Please enter the arrow set Q1");
      for (const line of lines) {
        let m = line.match(/^(\S+)\s*:\s*(\S+)\s*->\s*(\S+)$/);
        if (!m) m = line.match(/^(\S+)\s+(\S+)\s+(\S+)$/);
        if (!m) throw new Error("Cannot parse arrow: " + line);
        const name = m[1];
        const source = m[2];
        const target = m[3];
        if (arrows.has(name)) throw new Error("Duplicate arrow: " + name);
        if (!vset.has(source) || !vset.has(target)) {
          throw new Error("Arrow endpoints must belong to Q0: " + line);
        }
        arrows.set(name, { name, source, target });
      }
      return arrows;
    }

    function stripLatexComment(line) {
      let out = "";
      for (let i = 0; i < line.length; i++) {
        if (line[i] === "%" && line[i - 1] !== "\\") break;
        out += line[i];
      }
      return out.trim();
    }

    function extractTikzcdBody(text) {
      const raw = normalizeMath(text);
      const m = raw.match(/\\begin\{tikzcd\}(?:\[[^\]]*\])?([\s\S]*?)\\end\{tikzcd\}/);
      return m ? m[1] : raw;
    }

    function splitTikzRows(text) {
      const rows = [];
      let buf = "";
      for (let i = 0; i < text.length; i++) {
        if (text[i] === "\\" && text[i + 1] === "\\") {
          if (buf.trim()) rows.push(buf.trim());
          buf = "";
          i += 1;
        } else {
          buf += text[i];
        }
      }
      if (buf.trim()) rows.push(buf.trim());
      return rows;
    }

    function splitTikzCells(row) {
      const cells = [];
      let buf = "";
      let depth = 0;
      let quoted = false;
      for (let i = 0; i < row.length; i++) {
        const ch = row[i];
        if (ch === '"' && row[i - 1] !== "\\") quoted = !quoted;
        if (!quoted && ch === "{") depth += 1;
        if (!quoted && ch === "}") depth = Math.max(0, depth - 1);
        if (ch === "&" && row[i - 1] !== "\\" && depth === 0 && !quoted) {
          cells.push(buf.trim());
          buf = "";
        } else {
          buf += ch;
        }
      }
      cells.push(buf.trim());
      return cells;
    }

    function extractArrowCommands(text) {
      const commands = [];
      const re = /\\arrow\s*(?:\[([^\]]*)\])?/g;
      let m;
      while ((m = re.exec(text)) !== null) {
        commands.push({ command: m[0], options: m[1] || "" });
      }
      return commands;
    }

    function removeArrowCommands(text) {
      return text.replace(/\\arrow\s*(?:\[[^\]]*\])?/g, " ");
    }

    function splitTikzOptions(text) {
      const options = [];
      let buf = "";
      let depth = 0;
      let quoted = false;
      for (let i = 0; i < text.length; i++) {
        const ch = text[i];
        if (ch === '"' && text[i - 1] !== "\\") quoted = !quoted;
        if (!quoted && ch === "{") depth += 1;
        if (!quoted && ch === "}") depth = Math.max(0, depth - 1);
        if (ch === "," && !quoted && depth === 0) {
          if (buf.trim()) options.push(buf.trim());
          buf = "";
        } else {
          buf += ch;
        }
      }
      if (buf.trim()) options.push(buf.trim());
      return options;
    }

    function stripOuterBraces(s) {
      let out = s.trim();
      while (out.startsWith("{") && out.endsWith("}")) {
        let depth = 0;
        let wraps = true;
        for (let i = 0; i < out.length; i++) {
          if (out[i] === "{") depth += 1;
          if (out[i] === "}") depth -= 1;
          if (depth === 0 && i < out.length - 1) {
            wraps = false;
            break;
          }
        }
        if (!wraps) break;
        out = out.slice(1, -1).trim();
      }
      return out;
    }

    function cleanTikzText(text) {
      let s = stripOuterBraces(String(text).trim());
      s = s.replace(/^\$|\$$/g, "");
      s = s.replace(/\\text\{([^{}]*)\}/g, "$1");
      s = s.replace(/\\mathrm\{([^{}]*)\}/g, "$1");
      s = s.replace(/_\{([^{}]+)\}/g, "_$1");
      s = s.replace(/\\,/g, " ");
      s = s.replace(/\\&/g, "&");
      s = s.replace(/\\_/g, "_");
      s = s.replace(/\\([A-Za-z]+)/g, "$1");
      s = stripOuterBraces(s);
      return s.replace(/\s+/g, " ").trim();
    }

    function arrowLabelFromOptions(options) {
      for (const opt of options) {
        const m = opt.match(/"([^"]+)"/);
        if (m) return cleanTikzText(m[1]);
      }
      for (const opt of options) {
        const trimmed = opt.trim();
        if (/^(from|to)\s*=/.test(trimmed)) continue;
        if (/^(r+|l+|u+|d+|[ud]+[rl]+|[rl]+[ud]+)$/.test(trimmed)) continue;
        if (/^(bend|loop|swap|near|pos|description|tail|head|hook|two heads|dashed|phantom)/.test(trimmed)) continue;
        if (trimmed.startsWith("'")) continue;
        const cleaned = cleanTikzText(trimmed.replace(/^'|'$/g, ""));
        if (cleaned && !/^[a-z]+(=|$)/i.test(cleaned)) return cleaned;
      }
      return "";
    }

    function parseTikzCoord(raw) {
      const m = String(raw).trim().match(/^(\d+)\s*-\s*(\d+)$/);
      if (!m) throw new Error("Cannot parse tikzcd coordinate: " + raw);
      return { row: Number(m[1]), col: Number(m[2]) };
    }

    function cellKey(row, col) {
      return row + "-" + col;
    }

    function directionDelta(options) {
      for (const opt of options) {
        const token = opt.trim().replace(/'.*$/, "");
        if (!/^(r+|l+|u+|d+|[ud]+[rl]+|[rl]+[ud]+)$/.test(token)) continue;
        let row = 0;
        let col = 0;
        for (const ch of token) {
          if (ch === "r") col += 1;
          if (ch === "l") col -= 1;
          if (ch === "d") row += 1;
          if (ch === "u") row -= 1;
        }
        return { row, col };
      }
      return null;
    }

    function hasTikzLoopOption(options) {
      return options.some((opt) => /^loop\b/.test(opt.trim()));
    }

    function parseTikzcdQuiver(text) {
      const body = extractTikzcdBody(text);
      const rawLines = body.split("\n").map(stripLatexComment).filter(Boolean);
      if (!rawLines.length) throw new Error("Please enter a tikzcd diagram for Q");

      const matrixLines = [];
      const explicitArrowLines = [];
      for (const line of rawLines) {
        if (/^\\arrow\b/.test(line)) explicitArrowLines.push(line);
        else matrixLines.push(line);
      }

      const cellToVertex = new Map();
      const vertices = [];
      const vertexSet = new Set();
      const inlineCommands = [];
      const rows = splitTikzRows(matrixLines.join("\n"));
      rows.forEach((rowText, rowIndex) => {
        const row = rowIndex + 1;
        const cells = splitTikzCells(rowText);
        cells.forEach((cell, colIndex) => {
          const col = colIndex + 1;
          for (const cmd of extractArrowCommands(cell)) inlineCommands.push({ ...cmd, row, col });
          const label = cleanTikzText(removeArrowCommands(cell));
          if (!label) return;
          if (vertexSet.has(label)) throw new Error("Duplicate vertex label in tikzcd: " + label);
          vertexSet.add(label);
          vertices.push(label);
          cellToVertex.set(cellKey(row, col), label);
        });
      });
      if (!vertices.length) throw new Error("No vertices were found in the tikzcd diagram");

      const arrows = new Map();
      const addArrow = (cmd, context) => {
        const options = splitTikzOptions(cmd.options);
        const label = arrowLabelFromOptions(options);
        if (!label) throw new Error("Every tikzcd arrow must have a label: " + cmd.command);
        let fromCoord = null;
        let toCoord = null;
        for (const opt of options) {
          const fromMatch = opt.match(/^from\s*=\s*(.+)$/);
          const toMatch = opt.match(/^to\s*=\s*(.+)$/);
          if (fromMatch) fromCoord = parseTikzCoord(fromMatch[1]);
          if (toMatch) toCoord = parseTikzCoord(toMatch[1]);
        }
        if (!fromCoord || !toCoord) {
          if (!context) throw new Error("tikzcd arrow needs from=... and to=..., or it must appear inside a node cell: " + cmd.command);
          if (hasTikzLoopOption(options)) {
            fromCoord = { row: context.row, col: context.col };
            toCoord = { row: context.row, col: context.col };
          } else {
            const delta = directionDelta(options);
            if (!delta) throw new Error("Cannot determine tikzcd arrow direction: " + cmd.command);
            fromCoord = { row: context.row, col: context.col };
            toCoord = { row: context.row + delta.row, col: context.col + delta.col };
          }
        }
        const source = cellToVertex.get(cellKey(fromCoord.row, fromCoord.col));
        const target = cellToVertex.get(cellKey(toCoord.row, toCoord.col));
        if (!source || !target) throw new Error("tikzcd arrow endpoint does not point to a labelled vertex: " + cmd.command);
        if (arrows.has(label)) throw new Error("Duplicate arrow label in tikzcd: " + label);
        arrows.set(label, { name: label, source, target });
      };

      for (const cmd of inlineCommands) addArrow(cmd, { row: cmd.row, col: cmd.col });
      for (const line of explicitArrowLines) {
        for (const cmd of extractArrowCommands(line)) addArrow(cmd, null);
      }
      if (!arrows.size) throw new Error("No labelled arrows were found in the tikzcd diagram");
      return { vertices, arrows };
    }

    function parseOrder(text, arrows) {
      const given = splitNames(text);
      const names = [...arrows.keys()];
      const seen = new Set();
      const order = [];
      for (const name of given) {
        if (!arrows.has(name)) throw new Error("Unknown arrow in the order on Q1: " + name);
        if (!seen.has(name)) {
          seen.add(name);
          order.push(name);
        }
      }
      for (const name of names) {
        if (!seen.has(name)) order.push(name);
      }
      const rank = new Map();
      order.forEach((name, index) => rank.set(name, index));
      return { order, rank };
    }

    function splitSignedTerms(expr) {
      const s = normalizeMath(expr).trim();
      if (!s) return [];
      const out = [];
      let sign = 1;
      let buf = "";
      for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if ((ch === "+" || ch === "-") && (i === 0 || s[i - 1] !== "/")) {
          if (buf.trim()) out.push({ sign, body: buf.trim() });
          sign = ch === "-" ? -1 : 1;
          buf = "";
        } else {
          buf += ch;
        }
      }
      if (buf.trim()) out.push({ sign, body: buf.trim() });
      return out;
    }

    function parseCompactPath(raw, ctx) {
      let s = raw.trim();
      if (!s) throw new Error("Empty path");
      const names = [...ctx.arrows.keys()].sort((a, b) => b.length - a.length || a.localeCompare(b));
      const path = [];
      while (s.length) {
        let hit = null;
        for (const name of names) {
          if (s.startsWith(name)) {
            hit = name;
            break;
          }
        }
        if (!hit) throw new Error("Cannot split path into arrows: " + raw);
        path.push(hit);
        s = s.slice(hit.length);
      }
      return path;
    }

    function parsePath(raw, ctx) {
      const body = raw.trim();
      if (!body || body === "0") return null;
      let tokens;
      if (/[\s*]/.test(body)) {
        tokens = body.split(/[\s*]+/).map((x) => x.trim()).filter(Boolean);
      } else {
        tokens = parseCompactPath(body, ctx);
      }
      if (!tokens.length) return null;
      for (const t of tokens) {
        if (!ctx.arrows.has(t)) throw new Error("Unknown arrow: " + t + " in " + raw);
      }
      const path = pathFromInputTokens(tokens, ctx);
      if (!isComposable(path, ctx)) throw new Error("Path is not composable in Q from left to right: " + raw);
      return path;
    }

    function parseTerm(body, sign, ctx) {
      let s = body.replace(/^\*/, "").trim();
      if (s === "0") return null;
      let coeff = sign < 0 ? Rat.minusOne() : Rat.one();
      let pathPart = s;
      const m = s.match(/^([+-]?(?:\d+(?:\.\d+)?|\.\d+)(?:\/[+-]?(?:\d+(?:\.\d+)?|\.\d+))?)\s*(?:\*|\s+)?\s*(.*)$/);
      if (m && m[2].trim()) {
        coeff = coeff.mul(Rat.parse(m[1]));
        pathPart = m[2].trim();
      } else if (/^[+-]?(?:\d+(?:\.\d+)?|\.\d+)(?:\/[+-]?(?:\d+(?:\.\d+)?|\.\d+))?$/.test(s)) {
        throw new Error("A relation contains a scalar term without a path: " + s);
      }
      const path = parsePath(pathPart, ctx);
      if (!path) return null;
      return { path, coeff };
    }

    function parseExpression(expr, ctx) {
      const poly = Poly.zero();
      for (const part of splitSignedTerms(expr)) {
        const term = parseTerm(part.body, part.sign, ctx);
        if (term) poly.addTerm(term.path, term.coeff);
      }
      return poly;
    }

    function parseRelation(line, ctx) {
      const clean = stripComment(normalizeMath(line));
      if (!clean) return null;
      const eq = clean.indexOf("=");
      let poly;
      if (eq >= 0) {
        const left = clean.slice(0, eq);
        const right = clean.slice(eq + 1);
        poly = parseExpression(left, ctx).sub(parseExpression(right, ctx));
      } else {
        poly = parseExpression(clean, ctx);
      }
      if (poly.isZero()) return null;
      const endpoints = new Set();
      for (const k of poly.terms.keys()) {
        const p = pathOf(k);
        endpoints.add(pathSource(p, ctx) + "->" + pathTarget(p, ctx));
      }
      if (endpoints.size > 1) {
        throw new Error("Each relation must be a linear combination of parallel paths: " + line);
      }
      return poly;
    }

    function quiverInputMode() {
      const active = document.querySelector("[data-quiver-mode].active");
      return active ? active.dataset.quiverMode : "structured";
    }

    function setQuiverMode(mode) {
      document.querySelectorAll("[data-quiver-mode]").forEach((btn) => {
        btn.classList.toggle("active", btn.dataset.quiverMode === mode);
      });
      $("structuredQuiverInput").hidden = mode !== "structured";
      $("tikzcdQuiverInput").hidden = mode !== "tikzcd";
    }

    function parseQuiverInput() {
      if (quiverInputMode() === "tikzcd") return parseTikzcdQuiver($("tikzcdInput").value);
      const vertices = parseVertices($("verticesInput").value);
      const arrows = parseArrows($("arrowsInput").value, vertices);
      return { vertices, arrows };
    }

    function parseInput() {
      const characteristic = readCharacteristic();
      setFieldCharacteristic(characteristic);
      const { vertices, arrows } = parseQuiverInput();
      const orderInfo = parseOrder($("orderInput").value, arrows);
      const ctx = {
        vertices,
        arrows,
        order: orderInfo.order,
        rank: orderInfo.rank,
        earlierLarge: $("earlierLargeInput").checked,
        characteristic,
        compositionDirection: readCompositionDirection(),
        maxReductionSteps: 30000
      };
      const relations = normalizeMath($("relationsInput").value)
        .split("\n")
        .map((line) => parseRelation(line, ctx))
        .filter(Boolean);
      if (!relations.length) throw new Error("Please enter at least one nonzero relation");
      const opts = {
        maxDegree: readInt("maxDegreeInput", 14),
        maxBasis: readInt("maxBasisInput", 250),
        maxPairs: readInt("maxPairsInput", 12000),
        maxChains: readInt("maxChainsInput", 2000),
        n: readInt("nInput", 0),
        hhDegree: readInt("hhDegreeInput", 3),
        hhDimCap: readInt("hhDimCapInput", 100),
        characteristic,
        compositionDirection: ctx.compositionDirection
      };
      return { ctx, relations, opts };
    }

    function collectInputValues() {
      return {
        quiverMode: quiverInputMode(),
        vertices: $("verticesInput").value,
        arrows: $("arrowsInput").value,
        tikzcd: $("tikzcdInput").value,
        order: $("orderInput").value,
        earlierLarge: $("earlierLargeInput").checked,
        characteristic: readCharacteristic(),
        relations: $("relationsInput").value,
        n: readInt("nInput", 0),
        maxDegree: readInt("maxDegreeInput", 14),
        maxBasis: readInt("maxBasisInput", 250),
        maxPairs: readInt("maxPairsInput", 12000),
        maxChains: readInt("maxChainsInput", 2000),
        hhDegree: readInt("hhDegreeInput", 3),
        hhDimCap: readInt("hhDimCapInput", 100)
      };
    }

    function parseInputValues(values) {
      const characteristic = Number(values.characteristic) || 0;
      setFieldCharacteristic(characteristic);
      const quiver = values.quiverMode === "tikzcd"
        ? parseTikzcdQuiver(values.tikzcd || "")
        : {
          vertices: parseVertices(values.vertices || ""),
          arrows: parseArrows(values.arrows || "", parseVertices(values.vertices || ""))
        };
      const orderInfo = parseOrder(values.order || "", quiver.arrows);
      const ctx = {
        vertices: quiver.vertices,
        arrows: quiver.arrows,
        order: orderInfo.order,
        rank: orderInfo.rank,
        earlierLarge: values.earlierLarge !== false,
        characteristic,
        compositionDirection: "ltr",
        maxReductionSteps: 30000
      };
      const relations = normalizeMath(values.relations || "")
        .split("\n")
        .map((line) => parseRelation(line, ctx))
        .filter(Boolean);
      if (!relations.length) throw new Error("Please enter at least one nonzero relation");
      const opts = {
        maxDegree: Math.max(2, Number(values.maxDegree) || 14),
        maxBasis: Math.max(1, Number(values.maxBasis) || 250),
        maxPairs: Math.max(1, Number(values.maxPairs) || 12000),
        maxChains: Math.max(1, Number(values.maxChains) || 2000),
        n: Number.isFinite(Number(values.n)) ? Number(values.n) : 0,
        hhDegree: Math.max(0, Number(values.hhDegree) || 0),
        hhDimCap: Math.max(1, Number(values.hhDimCap) || 100),
        characteristic,
        compositionDirection: "ltr"
      };
      return { ctx, relations, opts };
    }

    function computeBaseFromInputValues(values) {
      const { ctx, relations, opts } = parseInputValues(values);
      const completed = completeBasis(relations, ctx, opts);
      const basis = completed.basis;
      const W = basis.map((g) => g.leading(ctx).path);
      const graph = buildUfnarovski(ctx, W);
      return {
        ctx,
        basis,
        W,
        graph,
        opts,
        stats: completed.stats,
        warnings: completed.warnings,
        monomialFast: isMonomialGroebnerBasis(basis)
      };
    }

    function readInt(id, fallback) {
      const v = Number.parseInt($(id).value, 10);
      return Number.isFinite(v) ? v : fallback;
    }

    function isPrimeInt(n) {
      if (n < 2) return false;
      if (n === 2) return true;
      if (n % 2 === 0) return false;
      for (let d = 3; d * d <= n; d += 2) {
        if (n % d === 0) return false;
      }
      return true;
    }

    const ALLOWED_CHARACTERISTICS = [0, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
    let lastCharacteristicValue = 0;
    let characteristicTyping = false;

    function snapCharacteristicValue(value, direction = 0) {
      if (!Number.isFinite(value)) return lastCharacteristicValue || 0;
      const exactIndex = ALLOWED_CHARACTERISTICS.indexOf(value);
      if (exactIndex >= 0) return value;
      if (direction > 0) {
        return ALLOWED_CHARACTERISTICS.find((p) => p > lastCharacteristicValue) || ALLOWED_CHARACTERISTICS[ALLOWED_CHARACTERISTICS.length - 1];
      }
      if (direction < 0) {
        for (let i = ALLOWED_CHARACTERISTICS.length - 1; i >= 0; i--) {
          if (ALLOWED_CHARACTERISTICS[i] < lastCharacteristicValue) return ALLOWED_CHARACTERISTICS[i];
        }
        return 0;
      }
      if (value <= 0) return 0;
      return ALLOWED_CHARACTERISTICS.find((p) => p >= value) || ALLOWED_CHARACTERISTICS[ALLOWED_CHARACTERISTICS.length - 1];
    }

    function setCharacteristicInput(value) {
      const snapped = snapCharacteristicValue(value, 0);
      $("charInput").value = String(snapped);
      lastCharacteristicValue = snapped;
      return snapped;
    }

    function normalizeCharacteristicInput(direction = 0) {
      const input = $("charInput");
      const raw = input.value.trim();
      if (!raw) return setCharacteristicInput(0);
      const value = Number.parseInt(raw, 10);
      const snapped = snapCharacteristicValue(value, direction);
      input.value = String(snapped);
      lastCharacteristicValue = snapped;
      return snapped;
    }

    function stepCharacteristic(direction) {
      const current = normalizeCharacteristicInput(0);
      const index = Math.max(0, ALLOWED_CHARACTERISTICS.indexOf(current));
      const nextIndex = clamp(index + direction, 0, ALLOWED_CHARACTERISTICS.length - 1);
      return setCharacteristicInput(ALLOWED_CHARACTERISTICS[nextIndex]);
    }

    function setupCharacteristicInput() {
      const input = $("charInput");
      input.addEventListener("keydown", (event) => {
        if (event.key === "ArrowUp") {
          event.preventDefault();
          stepCharacteristic(1);
          return;
        }
        if (event.key === "ArrowDown") {
          event.preventDefault();
          stepCharacteristic(-1);
          return;
        }
        if (/^\d$/.test(event.key) || event.key === "Backspace" || event.key === "Delete") {
          characteristicTyping = true;
        }
      });
      input.addEventListener("paste", () => {
        characteristicTyping = true;
      });
      input.addEventListener("input", () => {
        if (characteristicTyping) {
          const value = Number.parseInt(input.value.trim(), 10);
          if (ALLOWED_CHARACTERISTICS.includes(value) && String(value) === input.value.trim()) {
            lastCharacteristicValue = value;
          }
          characteristicTyping = false;
          return;
        }
        const raw = input.value.trim();
        const value = Number.parseInt(raw, 10);
        const direction = Number.isFinite(value) ? Math.sign(value - lastCharacteristicValue) : 0;
        normalizeCharacteristicInput(direction);
      });
      input.addEventListener("change", () => normalizeCharacteristicInput(0));
      input.addEventListener("blur", () => normalizeCharacteristicInput(0));
      setCharacteristicInput(Number.parseInt(input.value, 10) || 0);
    }

    function readCharacteristic() {
      normalizeCharacteristicInput(0);
      const raw = $("charInput").value.trim();
      if (!raw) return 0;
      const value = Number.parseInt(raw, 10);
      if (!Number.isFinite(value) || value < 0 || String(value) !== raw) {
        throw new Error("Characteristic of k must be 0 or a prime integer p <= 100");
      }
      if (!ALLOWED_CHARACTERISTICS.includes(value)) {
        throw new Error("Characteristic of k must be 0 or a prime integer p <= 100");
      }
      return value;
    }

    function readCompositionDirection() {
      return "ltr";
    }

    function normalForm(poly, basis, ctx, skip = new Set()) {
      let p = poly.clone();
      const result = Poly.zero();
      let steps = 0;
      while (!p.isZero()) {
        steps += 1;
        if (steps > ctx.maxReductionSteps) throw new Error("Reduction exceeded the step limit");
        const lt = p.leading(ctx);
        let reduction = null;
        for (let i = 0; i < basis.length; i++) {
          if (skip.has(i)) continue;
          const glt = basis[i].leading(ctx);
          if (!glt) continue;
          const positions = findOccurrences(lt.path, glt.path);
          if (positions.length) {
            reduction = { index: i, pos: positions[0], glt };
            break;
          }
        }
        if (reduction) {
          const prefix = lt.path.slice(0, reduction.pos);
          const suffix = lt.path.slice(reduction.pos + reduction.glt.path.length);
          const factor = lt.coeff.div(reduction.glt.coeff);
          p = p.sub(multiplyPoly(basis[reduction.index], prefix, suffix).scale(factor));
        } else {
          result.addTerm(lt.path, lt.coeff);
          p.addTerm(lt.path, lt.coeff.neg());
        }
      }
      return result.clean();
    }

    function overlapLength(a, b, len) {
      for (let i = 0; i < len; i++) {
        if (a[a.length - len + i] !== b[i]) return false;
      }
      return true;
    }

    function criticalCompositions(g, h, ctx, sameBasisElement) {
      const glt = g.leading(ctx);
      const hlt = h.leading(ctx);
      if (!glt || !hlt) return [];
      const p = glt.path;
      const q = hlt.path;
      const comps = [];
      const add = (poly, label) => {
        if (!poly.isZero()) comps.push({ poly, label });
      };

      for (const pos of findOccurrences(p, q)) {
        if (!(sameBasisElement && pos === 0 && p.length === q.length)) {
          const prefix = p.slice(0, pos);
          const suffix = p.slice(pos + q.length);
          add(g.sub(multiplyPoly(h, prefix, suffix)), "inclusion");
        }
      }

      for (const pos of findOccurrences(q, p)) {
        if (!(sameBasisElement && pos === 0 && p.length === q.length)) {
          const prefix = q.slice(0, pos);
          const suffix = q.slice(pos + p.length);
          add(multiplyPoly(g, prefix, suffix).sub(h), "inclusion");
        }
      }

      const maxOverlap = Math.min(p.length, q.length) - 1;
      for (let len = 1; len <= maxOverlap; len++) {
        if (overlapLength(p, q, len)) {
          add(multiplyPoly(g, [], q.slice(len)).sub(multiplyPoly(h, p.slice(0, p.length - len), [])), "overlap");
        }
        if (overlapLength(q, p, len)) {
          add(multiplyPoly(h, [], p.slice(len)).sub(multiplyPoly(g, q.slice(0, q.length - len), [])), "overlap");
        }
      }
      return comps;
    }

    function completeBasis(relations, ctx, opts) {
      const basis = [];
      const queue = [];
      const warnings = [];
      const stats = {
        inputRelations: relations.length,
        added: 0,
        compositionsQueued: 0,
        compositionsProcessed: 0,
        reductionsToZero: 0,
        completed: true
      };

      const enqueueFor = (i) => {
        for (let j = 0; j <= i; j++) {
          const comps = criticalCompositions(basis[i], basis[j], ctx, i === j);
          queue.push(...comps);
          stats.compositionsQueued += comps.length;
        }
      };

      for (const rel of relations) {
        const nf = normalForm(rel, basis, ctx);
        if (nf.isZero()) continue;
        const monic = nf.monic(ctx);
        const lt = monic.leading(ctx);
        if (lt.path.length > opts.maxDegree) {
          warnings.push("An initial relation has Tip length above the limit: " + displayPath(lt.path, ctx));
          stats.completed = false;
          continue;
        }
        basis.push(monic);
        stats.added += 1;
        enqueueFor(basis.length - 1);
      }

      while (queue.length) {
        if (stats.compositionsProcessed >= opts.maxPairs) {
          warnings.push("The composition limit was reached; G may be partial");
          stats.completed = false;
          break;
        }
        if (basis.length >= opts.maxBasis) {
          warnings.push("The basis-size limit was reached; G may be partial");
          stats.completed = false;
          break;
        }
        const item = queue.shift();
        stats.compositionsProcessed += 1;
        const nf = normalForm(item.poly, basis, ctx);
        if (nf.isZero()) {
          stats.reductionsToZero += 1;
          continue;
        }
        const monic = nf.monic(ctx);
        const lt = monic.leading(ctx);
        if (lt.path.length > opts.maxDegree) {
          warnings.push("A new Tip has length above the limit: " + displayPath(lt.path, ctx));
          stats.completed = false;
          break;
        }
        basis.push(monic);
        stats.added += 1;
        enqueueFor(basis.length - 1);
      }

      const reduced = reduceBasis(basis, ctx);
      return { basis: reduced, warnings, stats };
    }

    function reduceBasis(basis, ctx) {
      let current = basis.map((g) => g.monic(ctx));
      for (let pass = 0; pass < 30; pass++) {
        const next = [];
        for (let i = 0; i < current.length; i++) {
          const nf = normalForm(current[i], current, ctx, new Set([i]));
          if (!nf.isZero()) next.push(nf.monic(ctx));
        }
        const unique = new Map();
        for (const g of next) {
          const lt = g.leading(ctx);
          if (!lt) continue;
          if (!unique.has(lt.key)) unique.set(lt.key, g);
          else {
            const combined = unique.get(lt.key).sub(g);
            if (!combined.isZero()) unique.set(lt.key, combined.monic(ctx));
          }
        }
        current = [...unique.values()].sort((a, b) => {
          return -comparePaths(a.leading(ctx).path, b.leading(ctx).path, ctx);
        });
        const sig = current.map((g) => g.signature(ctx)).join("\n");
        const nextSig = next.map((g) => g.signature(ctx)).sort().join("\n");
        if (sig && sig === nextSig) break;
      }
      return current.sort((a, b) => -comparePaths(a.leading(ctx).path, b.leading(ctx).path, ctx));
    }

    function inMonomialIdeal(path, W) {
      return W.some((w) => containsFactor(path, w));
    }

    function properPrefixesClean(path, W) {
      for (let len = 1; len < path.length; len++) {
        if (inMonomialIdeal(path.slice(0, len), W)) return false;
      }
      return true;
    }

    function addPathVertex(map, path, type) {
      const key = keyOf(path);
      if (!map.has(key)) map.set(key, { key, path, type });
    }

    function buildUfnarovski(ctx, W) {
      const vertices = new Map();
      for (const v of ctx.vertices) {
        vertices.set("@" + v, { key: "@" + v, path: [], type: "vertex", label: v });
      }
      for (const name of ctx.arrows.keys()) addPathVertex(vertices, [name], "path");
      for (const w of W) {
        for (let i = 1; i < w.length; i++) addPathVertex(vertices, w.slice(i), "path");
      }

      const positive = [...vertices.values()].filter((v) => v.path.length);
      const adjacency = new Map();
      for (const v of positive) adjacency.set(v.key, []);
      for (const u of positive) {
        for (const v of positive) {
          const product = u.path.concat(v.path);
          if (inMonomialIdeal(product, W) && properPrefixesClean(product, W)) {
            adjacency.get(u.key).push(v.key);
          }
        }
      }
      for (const [k, arr] of adjacency.entries()) {
        arr.sort((a, b) => comparePaths(vertices.get(a).path, vertices.get(b).path, ctx));
      }
      return { vertices, positive, adjacency };
    }

    function qWNodeLabel(node, ctx) {
      return node.type === "vertex" ? "e_" + node.label : displayPath(node.path, ctx);
    }

    function qWEdges(ctx, graph) {
      const edges = [];
      for (const arrow of ctx.arrows.values()) {
        const from = "@" + arrow.source;
        const to = keyOf([arrow.name]);
        if (graph.vertices.has(from) && graph.vertices.has(to)) edges.push({ from, to, label: "" });
      }
      for (const [from, tos] of graph.adjacency.entries()) {
        for (const to of tos) edges.push({ from, to, label: "" });
      }
      return edges;
    }

    function quiverDiagramData(ctx) {
      const nodes = ctx.vertices.map((v, index) => ({
        key: v,
        label: v,
        layer: 0,
        order: index
      }));
      const edges = [...ctx.arrows.values()].map((a) => ({
        from: a.source,
        to: a.target,
        label: a.name
      }));
      return { nodes, edges };
    }

    function qWDiagramData(ctx, graph) {
      const nodes = [...graph.vertices.values()].map((node) => ({
        key: node.key,
        label: qWNodeLabel(node, ctx),
        path: node.path,
        layer: node.type === "vertex" ? 0 : node.path.length,
        order: node.type === "vertex" ? ctx.vertices.indexOf(node.label) : pathSortIndex(node.path, ctx)
      }));
      return { nodes, edges: qWEdges(ctx, graph) };
    }

    function pathSortIndex(path, ctx) {
      const display = pathForDisplay(path, ctx);
      let value = display.length * 10000;
      for (let i = 0; i < display.length; i++) {
        value += (ctx.rank.get(display[i]) || 0) * (100 ** Math.max(0, display.length - i - 1));
      }
      return value;
    }

    function nodeBoxSize(node) {
      const labelLen = node.label.length;
      return {
        w: Math.max(46, Math.min(120, labelLen * 8 + 24)),
        h: 34
      };
    }

    function shouldUseCircularLayout(nodes) {
      if (nodes.length < 3) return false;
      const layers = new Set(nodes.map((node) => node.layer));
      return layers.size === 1;
    }

    function layoutCircularDiagram(nodes) {
      const sorted = nodes.slice().sort((a, b) => a.order - b.order || a.label.localeCompare(b.label));
      const placed = new Map();
      const radius = Math.max(96, Math.min(190, 34 * sorted.length));
      const centerX = radius + 92;
      const centerY = radius + 76;
      const minX = centerX - radius;
      const minY = centerY - radius;
      const xGap = 132;
      const yGap = 96;
      const occupied = new Set();
      sorted.forEach((node, index) => {
        const angle = -Math.PI / 2 + (2 * Math.PI * index) / sorted.length;
        const x = centerX + Math.cos(angle) * radius;
        const y = centerY + Math.sin(angle) * radius;
        const size = nodeBoxSize(node);
        let row = Math.max(1, Math.round((y - minY) / yGap) + 1);
        let col = Math.max(1, Math.round((x - minX) / xGap) + 1);
        while (occupied.has(row + ":" + col)) col += 1;
        occupied.add(row + ":" + col);
        placed.set(node.key, {
          ...node,
          row,
          col,
          x,
          y,
          w: size.w,
          h: size.h
        });
      });
      return placed;
    }

    function layoutDiagram(nodes, edges = []) {
      if (shouldUseCircularLayout(nodes, edges)) return layoutCircularDiagram(nodes);
      const groups = new Map();
      for (const node of nodes) {
        if (!groups.has(node.layer)) groups.set(node.layer, []);
        groups.get(node.layer).push(node);
      }
      const layers = [...groups.keys()].sort((a, b) => a - b);
      let maxCount = 1;
      for (const layer of layers) {
        const row = groups.get(layer).sort((a, b) => a.order - b.order || a.label.localeCompare(b.label));
        maxCount = Math.max(maxCount, row.length);
      }
      const xGap = 148;
      const yGap = 108;
      const marginX = 70;
      const marginY = 58;
      const placed = new Map();
      layers.forEach((layer, rowIndex) => {
        const row = groups.get(layer);
        const offset = Math.floor((maxCount - row.length) / 2);
        row.forEach((node, i) => {
          const size = nodeBoxSize(node);
          const col = offset + i + 1;
          placed.set(node.key, {
            ...node,
            row: rowIndex + 1,
            col,
            x: marginX + (col - 1) * xGap,
            y: marginY + rowIndex * yGap,
            w: size.w,
            h: size.h
          });
        });
      });
      return placed;
    }

    function edgeGroupKey(edge) {
      return [edge.from, edge.to].sort().join("||");
    }

    function directedEdgeKey(edge) {
      return edge.from + "||" + edge.to;
    }

    function edgeGroupMap(edges) {
      const groups = new Map();
      for (const edge of edges) {
        const key = edgeGroupKey(edge);
        if (!groups.has(key)) groups.set(key, []);
        groups.get(key).push(edge);
      }
      return groups;
    }

    function directedEdgeGroupMap(edges) {
      const groups = new Map();
      for (const edge of edges) {
        const key = directedEdgeKey(edge);
        if (!groups.has(key)) groups.set(key, []);
        groups.get(key).push(edge);
      }
      return groups;
    }

    function edgeRouteOffset(edge, directedGroups) {
      const same = directedGroups.get(directedEdgeKey(edge)) || [edge];
      const opposite = directedGroups.get(edge.to + "||" + edge.from) || [];
      const index = Math.max(0, same.indexOf(edge));
      if (opposite.length) {
        return 36 + (index - (same.length - 1) / 2) * 20;
      }
      if (same.length > 1) return (index - (same.length - 1) / 2) * 34;
      return 0;
    }

    function clamp(value, min, max) {
      return Math.max(min, Math.min(max, value));
    }

    function renderSvgDiagram(containerId, nodes, edges) {
      const layout = layoutDiagram(nodes, edges);
      const validEdges = edges.filter((e) => layout.has(e.from) && layout.has(e.to));
      const groups = edgeGroupMap(validEdges);
      const directedGroups = directedEdgeGroupMap(validEdges);
      const nodeList = [...layout.values()];
      const width = Math.max(640, ...nodeList.map((n) => n.x + n.w + 220));
      const height = Math.max(340, ...nodeList.map((n) => n.y + n.h + 190));
      const markerId = containerId + "-arrow";
      const edgeSvg = validEdges.map((edge, index) => svgEdge(edge, layout, groups, directedGroups, markerId, index)).join("");
      const nodeSvg = nodeList.map((node) => {
        const label = escapeHtml(node.label);
        return `<g class="diagram-node" data-node="${escapeHtml(node.key)}" transform="translate(${node.x} ${node.y})"><rect x="${-node.w / 2}" y="${-node.h / 2}" width="${node.w}" height="${node.h}" rx="5" fill="#ffffff" stroke="#9fb0ac"/><text x="0" y="4" text-anchor="middle" font-size="13" fill="#18201f">${label}</text></g>`;
      }).join("");
      $(containerId).innerHTML = `<svg viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-label="draggable quiver diagram"><defs><marker id="${markerId}" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,6 L8,3 z" fill="#006d77"/></marker></defs><g fill="none" stroke="#006d77" stroke-width="1.6">${edgeSvg}</g><g>${nodeSvg}</g></svg>`;
      makeDiagramDraggable(containerId, layout, validEdges, groups, directedGroups, width, height);
      return layout;
    }

    function edgeGeometry(edge, layout, groups, directedGroups) {
      const from = layout.get(edge.from);
      const to = layout.get(edge.to);
      if (edge.from === edge.to) {
        const group = groups.get(edgeGroupKey(edge)) || [edge];
        const index = Math.max(0, group.indexOf(edge));
        const variant = loopSvgVariant(from, index);
        return {
          path: variant.path,
          labelX: variant.labelX,
          labelY: variant.labelY
        };
      }
      const dx = to.x - from.x;
      const dy = to.y - from.y;
      const len = Math.max(1, Math.hypot(dx, dy));
      const ux = dx / len;
      const uy = dy / len;
      const nx = -uy;
      const ny = ux;
      const offset = edgeRouteOffset(edge, directedGroups);
      const endpointShift = clamp(offset * 0.34, -18, 18);
      const sx = from.x + ux * (from.w / 2 + 3) + nx * endpointShift;
      const sy = from.y + uy * (from.h / 2 + 3) + ny * endpointShift;
      const tx = to.x - ux * (to.w / 2 + 8) + nx * endpointShift;
      const ty = to.y - uy * (to.h / 2 + 8) + ny * endpointShift;
      const mx = (sx + tx) / 2;
      const my = (sy + ty) / 2;
      const cx = mx + nx * offset;
      const cy = my + ny * offset;
      const path = Math.abs(offset) < 0.1 ? `M ${sx} ${sy} L ${tx} ${ty}` : `M ${sx} ${sy} Q ${cx} ${cy} ${tx} ${ty}`;
      return {
        path,
        labelX: cx,
        labelY: cy - 8
      };
    }

    function svgEdge(edge, layout, groups, directedGroups, markerId, index) {
      const label = edge.label ? escapeHtml(edge.label) : "";
      const geometry = edgeGeometry(edge, layout, groups, directedGroups);
      const text = label ? `<text class="diagram-edge-label" x="${geometry.labelX}" y="${geometry.labelY}" text-anchor="middle" font-size="12" fill="#273532">${label}</text>` : "";
      return `<g class="diagram-edge" data-edge-index="${index}"><path class="diagram-edge-path" d="${geometry.path}" marker-end="url(#${markerId})"/>${text}</g>`;
    }

    function updateSvgEdges(svg, layout, edges, groups, directedGroups) {
      const edgeEls = svg.querySelectorAll(".diagram-edge");
      edges.forEach((edge, index) => {
        const edgeEl = edgeEls[index];
        if (!edgeEl) return;
        const geometry = edgeGeometry(edge, layout, groups, directedGroups);
        const pathEl = edgeEl.querySelector(".diagram-edge-path");
        if (pathEl) pathEl.setAttribute("d", geometry.path);
        const textEl = edgeEl.querySelector(".diagram-edge-label");
        if (textEl) {
          textEl.setAttribute("x", geometry.labelX);
          textEl.setAttribute("y", geometry.labelY);
        }
      });
    }

    function svgEventPoint(svg, event) {
      const matrix = svg.getScreenCTM();
      if (!matrix) return { x: event.offsetX || 0, y: event.offsetY || 0 };
      return new DOMPoint(event.clientX, event.clientY).matrixTransform(matrix.inverse());
    }

    function makeDiagramDraggable(containerId, layout, edges, groups, directedGroups, width, height) {
      const svg = $(containerId).querySelector("svg");
      if (!svg) return;
      const nodeEls = new Map();
      svg.querySelectorAll(".diagram-node").forEach((nodeEl) => {
        nodeEls.set(nodeEl.dataset.node, nodeEl);
      });
      let drag = null;

      svg.addEventListener("pointerdown", (event) => {
        const nodeEl = event.target.closest ? event.target.closest(".diagram-node") : null;
        if (!nodeEl || !svg.contains(nodeEl)) return;
        if (event.button !== undefined && event.button !== 0) return;
        const node = layout.get(nodeEl.dataset.node);
        if (!node) return;
        const point = svgEventPoint(svg, event);
        drag = {
          key: node.key,
          dx: point.x - node.x,
          dy: point.y - node.y,
          pointerId: event.pointerId
        };
        nodeEl.classList.add("dragging");
        svg.setPointerCapture(event.pointerId);
        event.preventDefault();
      });

      svg.addEventListener("pointermove", (event) => {
        if (!drag) return;
        const node = layout.get(drag.key);
        const nodeEl = nodeEls.get(drag.key);
        if (!node || !nodeEl) return;
        const point = svgEventPoint(svg, event);
        const minX = node.w / 2 + 24;
        const maxX = width - node.w / 2 - 24;
        const minY = node.h / 2 + 24;
        const maxY = height - node.h / 2 - 24;
        node.x = clamp(point.x - drag.dx, minX, maxX);
        node.y = clamp(point.y - drag.dy, minY, maxY);
        nodeEl.setAttribute("transform", `translate(${node.x} ${node.y})`);
        updateSvgEdges(svg, layout, edges, groups, directedGroups);
        event.preventDefault();
      });

      function finishDrag(event) {
        if (!drag) return;
        const nodeEl = nodeEls.get(drag.key);
        if (nodeEl) nodeEl.classList.remove("dragging");
        if (svg.hasPointerCapture && svg.hasPointerCapture(drag.pointerId)) {
          svg.releasePointerCapture(drag.pointerId);
        }
        drag = null;
        if (event) event.preventDefault();
      }

      svg.addEventListener("pointerup", finishDrag);
      svg.addEventListener("pointercancel", finishDrag);
    }

    function loopSvgVariant(node, index) {
      const cycle = index % 4;
      const ring = Math.floor(index / 4);
      const r = 28 + ring * 15;
      const x = node.x;
      const y = node.y;
      const top = y - node.h / 2;
      const bottom = y + node.h / 2;
      const left = x - node.w / 2;
      const right = x + node.w / 2;
      if (cycle === 0) {
        return {
          path: `M ${right - 8} ${top} C ${x + r} ${top - r} ${x - r} ${top - r} ${left + 8} ${top}`,
          labelX: x,
          labelY: top - r - 6
        };
      }
      if (cycle === 1) {
        return {
          path: `M ${right} ${top + 8} C ${right + r} ${y - r} ${right + r} ${y + r} ${right} ${bottom - 8}`,
          labelX: right + r + 14,
          labelY: y + 4
        };
      }
      if (cycle === 2) {
        return {
          path: `M ${left + 8} ${bottom} C ${x - r} ${bottom + r} ${x + r} ${bottom + r} ${right - 8} ${bottom}`,
          labelX: x,
          labelY: bottom + r + 16
        };
      }
      return {
        path: `M ${left} ${bottom - 8} C ${left - r} ${y + r} ${left - r} ${y - r} ${left} ${top + 8}`,
        labelX: left - r - 14,
        labelY: y + 4
      };
    }

    function tikzToken(s) {
      return String(s).replace(/([{}&%$#])/g, "\\$1");
    }

    function tikzPathLabel(path) {
      return path.map(tikzToken).join("\\,");
    }

    function tikzNodeLabel(node) {
      if (node.key && node.key.startsWith("@")) return "e_{" + tikzToken(node.label.replace(/^e_/, "")) + "}";
      if (node.path) return tikzToken(node.label).replace(/\s+/g, "\\,");
      return tikzToken(node.label);
    }

    function tikzDiagram(nodes, edges, layout, title) {
      const nodeByKey = new Map(nodes.map((n) => [n.key, n]));
      const rows = Math.max(1, ...[...layout.values()].map((n) => n.row));
      const cols = Math.max(1, ...[...layout.values()].map((n) => n.col));
      const cells = Array.from({ length: rows }, () => Array.from({ length: cols }, () => ""));
      for (const placed of layout.values()) {
        const original = nodeByKey.get(placed.key) || placed;
        cells[placed.row - 1][placed.col - 1] = tikzNodeLabel(original);
      }
      const lines = [
        "% " + title,
        "\\[",
        "\\begin{tikzcd}[column sep=large, row sep=large]"
      ];
      cells.forEach((row, index) => {
        lines.push(row.join(" & ") + (index < cells.length - 1 ? " \\\\" : ""));
      });
      const groups = edgeGroupMap(edges);
      const directedGroups = directedEdgeGroupMap(edges);
      for (const edge of edges) {
        const from = layout.get(edge.from);
        const to = layout.get(edge.to);
        if (!from || !to) continue;
        const options = [`from=${from.row}-${from.col}`, `to=${to.row}-${to.col}`];
        if (edge.label) options.push(`"{${tikzToken(edge.label)}}"`);
        if (edge.from === edge.to) {
          const group = groups.get(edgeGroupKey(edge)) || [];
          options.push(tikzLoopOption(Math.max(0, group.indexOf(edge))));
        }
        else {
          const same = directedGroups.get(directedEdgeKey(edge)) || [];
          const opposite = directedGroups.get(edge.to + "||" + edge.from) || [];
          if (opposite.length) {
            const idx = Math.max(0, same.indexOf(edge));
            options.push(`bend left=${18 + idx * 10}`);
          }
          else if (same.length > 1) {
            const idx = Math.max(0, same.indexOf(edge));
            const angle = 14 + Math.floor(idx / 2) * 10;
            options.push(idx % 2 === 0 ? `bend left=${angle}` : `bend right=${angle}`);
          }
        }
        lines.push("\\arrow[" + options.join(", ") + "]");
      }
      lines.push("\\end{tikzcd}");
      lines.push("\\]");
      return lines.join("\n");
    }

    function tikzLoopOption(index) {
      const directions = ["loop above", "loop right", "loop below", "loop left"];
      return directions[index % directions.length];
    }

    function renderDiagrams(ctx, graph) {
      const q = quiverDiagramData(ctx);
      const qLayout = renderSvgDiagram("quiverDiagram", q.nodes, q.edges);
      $("quiverTikz").textContent = tikzDiagram(q.nodes, q.edges, qLayout, "Input quiver Q");

      const qw = qWDiagramData(ctx, graph);
      const qwLayout = renderSvgDiagram("qwDiagram", qw.nodes, qw.edges);
      $("qwTikz").textContent = tikzDiagram(qw.nodes, qw.edges, qwLayout, "Ufnarovski graph Q_W");
    }

    function countChains(ctx, graph, n) {
      if (n < 0) return BigInt(ctx.vertices.length);
      let counts = new Map();
      for (const name of ctx.arrows.keys()) {
        const key = keyOf([name]);
        counts.set(key, (counts.get(key) || 0n) + 1n);
      }
      for (let step = 1; step <= n; step++) {
        const next = new Map();
        for (const [last, count] of counts.entries()) {
          for (const dest of graph.adjacency.get(last) || []) {
            next.set(dest, (next.get(dest) || 0n) + count);
          }
        }
        counts = next;
      }
      let total = 0n;
      for (const c of counts.values()) total += c;
      return total;
    }

    function listChains(ctx, graph, n, maxChains) {
      const truncated = { value: false };
      if (n < 0) {
        return {
          chains: ctx.vertices.slice(0, maxChains).map((v) => ({ parts: ["e_" + v], word: [] })),
          truncated: ctx.vertices.length > maxChains
        };
      }
      const chains = [];
      const stack = [];
      const arrowNames = [...ctx.arrows.keys()].reverse();
      for (const name of arrowNames) {
        stack.push({ parts: [keyOf([name])], last: keyOf([name]) });
      }
      while (stack.length) {
        const item = stack.pop();
        if (item.parts.length === n + 1) {
          chains.push({
            parts: item.parts,
            word: item.parts.flatMap((k) => pathOf(k))
          });
          if (chains.length >= maxChains) {
            truncated.value = true;
            break;
          }
          continue;
        }
        const next = [...(graph.adjacency.get(item.last) || [])].reverse();
        for (const dest of next) {
          stack.push({ parts: item.parts.concat(dest), last: dest });
        }
      }
      return { chains, truncated: truncated.value };
    }

    function isChainTuple(tuple, graph, ctx) {
      if (!tuple.length) return false;
      const first = pathOf(tuple[0]);
      if (first.length !== 1 || !ctx.arrows.has(first[0])) return false;
      for (let i = 0; i < tuple.length - 1; i++) {
        const next = graph.adjacency.get(tuple[i]) || [];
        if (!next.includes(tuple[i + 1])) return false;
      }
      return true;
    }

    function chainPrefixIndex(tuple, graph, ctx) {
      let best = -1;
      for (let len = 1; len <= tuple.length; len++) {
        if (isChainTuple(tuple.slice(0, len), graph, ctx)) best = len - 1;
        else break;
      }
      return best;
    }

    function isCriticalTuple(tuple, graph, ctx) {
      return tuple.length > 0 && chainPrefixIndex(tuple, graph, ctx) === tuple.length - 1;
    }

    function tupleWord(tuple) {
      return tuple.filter((k) => !k.startsWith("@")).flatMap((k) => pathOf(k));
    }

    function formatTuple(tuple) {
      if (!tuple.length) return "()";
      if (tuple.length === 1 && tuple[0].startsWith("@")) return "e_" + tuple[0].slice(1);
      return "(" + tuple.map((k) => k.startsWith("@") ? "e_" + k.slice(1) : formatPath(pathOf(k))).join(", ") + ")";
    }

    function formatTupleForCtx(tuple, ctx) {
      if (!tuple.length) return "()";
      if (tuple.length === 1 && tuple[0].startsWith("@")) return "e_" + tuple[0].slice(1);
      return "(" + tuple.map((k) => k.startsWith("@") ? "e_" + k.slice(1) : formatPath(pathOf(k))).join(", ") + ")";
    }

    function normalFormProduct(leftKey, rightKey, basis, ctx) {
      const product = pathOf(leftKey).concat(pathOf(rightKey));
      const poly = Poly.zero().addTerm(product, Rat.one());
      const nf = normalForm(poly, basis, ctx);
      return [...nf.terms.entries()]
        .map(([k, coeff]) => ({ key: k, path: pathOf(k), coeff }))
        .filter((term) => term.path.length > 0);
    }

    function isMatchingMerge(sourceTuple, targetTuple, pairIndex, graph, ctx) {
      return chainPrefixIndex(sourceTuple, graph, ctx) === pairIndex &&
        chainPrefixIndex(targetTuple, graph, ctx) === pairIndex - 1;
    }

    function ratSign(power) {
      return power % 2 === 0 ? Rat.one() : Rat.minusOne();
    }

    function makeWeight(scalar, left = [], right = []) {
      return { scalar, left, right };
    }

    function multiplyWeights(a, b) {
      return {
        scalar: a.scalar.mul(b.scalar),
        left: a.left.concat(b.left),
        right: b.right.concat(a.right)
      };
    }

    function formatAeWeight(weight) {
      const scalar = weight.scalar.toString();
      const left = weight.left.length ? formatPath(weight.left) : "1";
      const right = weight.right.length ? formatPath(weight.right) : "1";
      if (scalar === "1" && left === "1" && right === "1") return "1";
      if (scalar === "1") return left + " ⊗ " + right;
      return scalar + " · " + left + " ⊗ " + right;
    }

    function formatAeWeightForCtx(weight, ctx) {
      const scalar = weight.scalar.toString();
      const left = weight.left.length ? displayPath(weight.left, ctx) : "1";
      const right = weight.right.length ? displayPath(weight.right, ctx) : "1";
      if (scalar === "1" && left === "1" && right === "1") return "1";
      if (scalar === "1") return left + " ⊗ " + right;
      return scalar + " · " + left + " ⊗ " + right;
    }

    function formatAeWeight(weight) {
      const scalar = weight.scalar.toString();
      const left = weight.left.length ? formatPath(weight.left) : "1";
      const right = weight.right.length ? formatPath(weight.right) : "1";
      if (scalar === "1" && left === "1" && right === "1") return "1";
      if (scalar === "1") return left + " ⊗ " + right;
      return scalar + " · " + left + " ⊗ " + right;
    }

    function sameTuple(a, b) {
      return a.length === b.length && a.every((x, i) => x === b[i]);
    }

    function targetIsLowerCritical(tuple, targetLength, graph, ctx) {
      if (targetLength === 0) return tuple.length === 1 && tuple[0].startsWith("@");
      return tuple.length === targetLength && isCriticalTuple(tuple, graph, ctx);
    }

    function thickBarEdges(tuple, basis, graph, ctx) {
      const edges = [];
      if (tuple.length === 0 || tuple[0].startsWith("@")) return edges;
      const L = tuple.length;
      const first = pathOf(tuple[0]);
      const last = pathOf(tuple[L - 1]);
      const d0Target = L === 1 ? ["@" + pathTarget(first, ctx)] : tuple.slice(1);
      edges.push({
        kind: "thick",
        label: "d0_" + L,
        target: d0Target,
        weight: makeWeight(Rat.one(), first, [])
      });

      for (let j = 0; j < L - 1; j++) {
        const terms = normalFormProduct(tuple[j], tuple[j + 1], basis, ctx);
        const productKey = keyOf(pathOf(tuple[j]).concat(pathOf(tuple[j + 1])));
        const sign = ratSign(j + 1);
        for (const term of terms) {
          const target = tuple.slice(0, j).concat(term.key, tuple.slice(j + 2));
          if (term.key === productKey && term.coeff.isOne() && isMatchingMerge(tuple, target, j, graph, ctx)) continue;
          edges.push({
            kind: "thick",
            label: "d" + (j + 1) + "_" + L,
            target,
            weight: makeWeight(sign.mul(term.coeff), [], [])
          });
        }
      }

      const dLastTarget = L === 1 ? ["@" + pathSource(last, ctx)] : tuple.slice(0, L - 1);
      edges.push({
        kind: "thick",
        label: "d" + L + "_" + L,
        target: dLastTarget,
        weight: makeWeight(ratSign(L), [], last)
      });
      return edges;
    }

    function reversedMatchingEdges(tuple, graph, ctx) {
      const edges = [];
      if (!tuple.length || tuple[0].startsWith("@")) return edges;
      for (let j = 0; j < tuple.length; j++) {
        const path = pathOf(tuple[j]);
        for (let cut = 1; cut < path.length; cut++) {
          const left = path.slice(0, cut);
          const right = path.slice(cut);
          const splitTuple = tuple.slice(0, j).concat(keyOf(left), keyOf(right), tuple.slice(j + 1));
          if (!isMatchingMerge(splitTuple, tuple, j, graph, ctx)) continue;
          edges.push({
            kind: "dotted",
            label: "d^-" + (j + 1) + "_" + (tuple.length + 1),
            target: splitTuple,
            weight: makeWeight(ratSign(j + 2), [], [])
          });
        }
      }
      return edges;
    }

    function outgoingMorseEdges(tuple, basis, graph, ctx) {
      return thickBarEdges(tuple, basis, graph, ctx).concat(reversedMatchingEdges(tuple, graph, ctx));
    }

    function computeMorseZigzags(startTuple, computation) {
      const { basis, graph, ctx } = computation;
      const targetLength = startTuple.length - 1;
      const wordLength = tupleWord(startTuple).length;
      const maxDepth = Math.max(8, wordLength * 3 + startTuple.length + 4);
      const maxPaths = 2000;
      const stack = [{
        tuple: startTuple,
        steps: [],
        weight: makeWeight(Rat.one(), [], [])
      }];
      const paths = [];
      let truncated = false;
      while (stack.length) {
        const state = stack.pop();
        if (targetIsLowerCritical(state.tuple, targetLength, graph, ctx)) {
          paths.push(state);
          if (paths.length >= maxPaths) {
            truncated = true;
            break;
          }
          continue;
        }
        if (state.steps.length >= maxDepth) {
          truncated = true;
          continue;
        }
        const edges = outgoingMorseEdges(state.tuple, basis, graph, ctx);
        for (let i = edges.length - 1; i >= 0; i--) {
          const edge = edges[i];
          if (state.steps.some((step) => sameTuple(step.from, edge.target) && step.label === edge.label)) continue;
          stack.push({
            tuple: edge.target,
            steps: state.steps.concat({
              label: edge.label,
              kind: edge.kind,
              from: state.tuple,
              to: edge.target,
              weight: edge.weight
            }),
            weight: multiplyWeights(state.weight, edge.weight)
          });
        }
      }
      return { paths, truncated, maxDepth, maxPaths };
    }

    function summarizeZigzags(paths) {
      const grouped = new Map();
      for (const path of paths) {
        const target = formatTupleForCtx(path.tuple, lastComputation ? lastComputation.ctx : null);
        const left = keyOf(path.weight.left);
        const right = keyOf(path.weight.right);
        const key = target + "|" + left + "|" + right;
        const old = grouped.get(key) || { target, left: path.weight.left, right: path.weight.right, scalar: Rat.zero(), count: 0 };
        old.scalar = old.scalar.add(path.weight.scalar);
        old.count += 1;
        grouped.set(key, old);
      }
      return [...grouped.values()].filter((x) => !x.scalar.isZero());
    }

    function renderMorseDifferential(chainIndex) {
      if (!lastComputation) return;
      setFieldFromComputation(lastComputation);
      const chain = lastComputation.chains[chainIndex];
      if (!chain) return;
      const startTuple = chain.parts;
      const diff = computeMorseZigzags(startTuple, lastComputation);
      const summary = summarizeZigzags(diff.paths);
      const selected = "Selected " + formatTupleForCtx(startTuple, lastComputation.ctx);
      const warnings = [];
      if (diff.truncated) warnings.push("truncated at " + diff.paths.length + " paths or depth " + diff.maxDepth);
      $("diffCount").textContent = diff.paths.length + " zigzag paths";
      $("diffSummary").textContent = [
        selected,
        "Target component: W(" + (startTuple.length - 2) + ")",
        ...(warnings.length ? ["Warning: " + warnings.join("; ")] : []),
        "",
        "Image of differential:",
        summary.length ? summary.map((term) => {
          const weight = formatAeWeightForCtx({ scalar: term.scalar, left: term.left, right: term.right }, lastComputation.ctx);
          return weight + " · " + term.target + "   [" + term.count + " path" + (term.count === 1 ? "" : "s") + "]";
        }).join("\n") : "0"
      ].join("\n");
      fillList("diffPaths", diff.paths, (path) => {
        const steps = path.steps.map((step) => {
          const kind = step.kind === "dotted" ? "<span class=\"zigzag-kind dotted\">(dotted)</span>" : "<span class=\"zigzag-kind thick\">(thick)</span>";
          return escapeHtml(formatTupleForCtx(step.from, lastComputation.ctx)) + " --" + escapeHtml(step.label) + " " + escapeHtml(formatAeWeightForCtx(step.weight, lastComputation.ctx)) + " " + kind + "--> " + escapeHtml(formatTupleForCtx(step.to, lastComputation.ctx));
        }).join("\n");
        return "<pre>" + steps + "\n=> " + escapeHtml(formatAeWeightForCtx(path.weight, lastComputation.ctx)) + " · " + escapeHtml(formatTupleForCtx(path.tuple, lastComputation.ctx)) + "</pre>";
      });
    }

    function renderMorseDifferential(chainIndex) {
      if (!lastComputation) return;
      setFieldFromComputation(lastComputation);
      const chain = lastComputation.chains[chainIndex];
      if (!chain) return;
      const startTuple = chain.parts;
      const diff = computeMorseZigzags(startTuple, lastComputation);
      const summary = summarizeZigzags(diff.paths);
      const selected = "Selected " + formatTupleForCtx(startTuple, lastComputation.ctx);
      const warnings = [];
      if (diff.truncated) warnings.push("truncated at " + diff.paths.length + " paths or depth " + diff.maxDepth);
      $("diffCount").textContent = diff.paths.length + " zigzag paths";
      const summaryLines = [
        selected,
        "Target component: W(" + (startTuple.length - 2) + ")",
        ...(warnings.length ? ["Warning: " + warnings.join("; ")] : []),
        "",
        "Image of differential:",
        summary.length ? summary.map((term) => {
          const weight = formatAeWeightForCtx({ scalar: term.scalar, left: term.left, right: term.right }, lastComputation.ctx);
          return weight + " · " + term.target;
        }).join("\n") : "0"
      ];
      $("diffSummary").textContent = summaryLines.join("\n");
      fillList("diffPaths", diff.paths, (path) => {
        const steps = path.steps.map((step) => {
          const kind = step.kind === "dotted" ? "<span class=\"zigzag-kind dotted\">(dotted)</span>" : "<span class=\"zigzag-kind thick\">(thick)</span>";
          return escapeHtml(formatTupleForCtx(step.from, lastComputation.ctx)) + " --" + escapeHtml(step.label) + " " + escapeHtml(formatAeWeightForCtx(step.weight, lastComputation.ctx)) + " " + kind + "--> " + escapeHtml(formatTupleForCtx(step.to, lastComputation.ctx));
        }).join("\n");
        return "<pre>" + steps + "\n=> " + escapeHtml(formatAeWeightForCtx(path.weight, lastComputation.ctx)) + " · " + escapeHtml(formatTupleForCtx(path.tuple, lastComputation.ctx)) + "</pre>";
      });
    }

    function renderMorseDifferential(chainIndex) {
      if (!lastComputation) return;
      setFieldFromComputation(lastComputation);
      const chain = lastComputation.chains[chainIndex];
      if (!chain) return;
      const startTuple = chain.parts;
      const diff = computeMorseZigzags(startTuple, lastComputation);
      const summary = summarizeZigzags(diff.paths);
      const selected = "Selected " + formatTupleForCtx(startTuple, lastComputation.ctx);
      const warnings = [];
      if (diff.truncated) warnings.push("truncated at " + diff.paths.length + " paths or depth " + diff.maxDepth);
      $("diffCount").textContent = diff.paths.length + " zigzag paths";
      const summaryLines = [
        selected,
        "Target component: W(" + (startTuple.length - 2) + ")",
        ...(warnings.length ? ["Warning: " + warnings.join("; ")] : []),
        "",
        "Image of differential:",
        summary.length ? summary.map((term) => {
          const weight = formatAeWeightForCtx({ scalar: term.scalar, left: term.left, right: term.right }, lastComputation.ctx);
          return weight + " · " + term.target;
        }).join("\n") : "0"
      ];
      $("diffSummary").textContent = summaryLines.join("\n");
      fillList("diffPaths", diff.paths, (path) => {
        const steps = path.steps.map((step) => {
          const kind = step.kind === "dotted" ? "<span class=\"zigzag-kind dotted\">(dotted)</span>" : "<span class=\"zigzag-kind thick\">(thick)</span>";
          return escapeHtml(formatTupleForCtx(step.from, lastComputation.ctx)) + " --" + escapeHtml(step.label) + " " + escapeHtml(formatAeWeightForCtx(step.weight, lastComputation.ctx)) + " " + kind + "--> " + escapeHtml(formatTupleForCtx(step.to, lastComputation.ctx));
        }).join("\n");
        return "<pre>" + steps + "\n=> " + escapeHtml(formatAeWeightForCtx(path.weight, lastComputation.ctx)) + " · " + escapeHtml(formatTupleForCtx(path.tuple, lastComputation.ctx)) + "</pre>";
      });
    }

    function pathKeySource(key, ctx) {
      if (key.startsWith("@")) return key.slice(1);
      return pathSource(pathOf(key), ctx);
    }

    function pathKeyTarget(key, ctx) {
      if (key.startsWith("@")) return key.slice(1);
      return pathTarget(pathOf(key), ctx);
    }

    function pathKeyArray(key) {
      return key.startsWith("@") ? [] : pathOf(key);
    }

    function generateAlgebraBasis(ctx, W, cap) {
      const basis = [];
      const seen = new Set();
      const add = (key) => {
        if (seen.has(key)) return;
        seen.add(key);
        basis.push(key);
        if (basis.length > cap) throw new Error("dim_k A exceeded the cap " + cap);
      };
      for (const v of ctx.vertices) add("@" + v);
      const queue = [];
      for (const arrow of ctx.arrows.keys()) {
        const path = [arrow];
        if (!inMonomialIdeal(path, W)) {
          const key = keyOf(path);
          add(key);
          queue.push(path);
        }
      }
      let cursor = 0;
      while (cursor < queue.length) {
        const path = queue[cursor++];
        for (const arrow of ctx.arrows.values()) {
          const next = path.concat(arrow.name);
          if (!isComposable(next, ctx)) continue;
          if (inMonomialIdeal(next, W)) continue;
          const key = keyOf(next);
          if (!seen.has(key)) {
            add(key);
            queue.push(next);
          }
        }
      }
      return basis.sort((a, b) => {
        if (a.startsWith("@") && !b.startsWith("@")) return -1;
        if (!a.startsWith("@") && b.startsWith("@")) return 1;
        if (a.startsWith("@") && b.startsWith("@")) return a.localeCompare(b);
        return comparePaths(pathOf(a), pathOf(b), ctx);
      });
    }

    function isMonomialGroebnerBasis(basis) {
      return basis.every((g) => g.terms.size === 1);
    }

    function multiplyBasisKeys(leftKey, rightKey, computation) {
      const { ctx, basis } = computation;
      if (leftKey.startsWith("@") && rightKey.startsWith("@")) {
        return leftKey === rightKey ? new Map([[leftKey, Rat.one()]]) : new Map();
      }
      if (leftKey.startsWith("@")) {
        return leftKey.slice(1) === pathKeySource(rightKey, ctx) ? new Map([[rightKey, Rat.one()]]) : new Map();
      }
      if (rightKey.startsWith("@")) {
        return pathKeyTarget(leftKey, ctx) === rightKey.slice(1) ? new Map([[leftKey, Rat.one()]]) : new Map();
      }
      const product = pathOf(leftKey).concat(pathOf(rightKey));
      if (!isComposable(product, ctx)) return new Map();
      if (computation.monomialFast) {
        return inMonomialIdeal(product, computation.W) ? new Map() : new Map([[keyOf(product), Rat.one()]]);
      }
      const poly = Poly.zero().addTerm(product, Rat.one());
      const nf = normalForm(poly, basis, ctx);
      const out = new Map();
      for (const [k, c] of nf.terms.entries()) out.set(k, c);
      return out;
    }

    function multiplyWeightByAlgebraPath(weight, middleKey, computation) {
      let terms = new Map([[middleKey, weight.scalar]]);
      if (weight.left.length) {
        const leftKey = keyOf(weight.left);
        terms = multiplySparseByKey(leftKey, terms, computation, true);
      }
      if (weight.right.length) {
        const rightKey = keyOf(weight.right);
        terms = multiplySparseByKey(rightKey, terms, computation, false);
      }
      return terms;
    }

    function multiplySparseByKey(key, terms, computation, leftSide) {
      const out = new Map();
      for (const [termKey, coeff] of terms.entries()) {
        const product = leftSide ? multiplyBasisKeys(key, termKey, computation) : multiplyBasisKeys(termKey, key, computation);
        for (const [k, c] of product.entries()) {
          const next = (out.get(k) || Rat.zero()).add(coeff.mul(c));
          if (next.isZero()) out.delete(k);
          else out.set(k, next);
        }
      }
      return out;
    }

    function chainEndpoints(tuple, ctx) {
      if (tuple.length === 1 && tuple[0].startsWith("@")) {
        const v = tuple[0].slice(1);
        return { source: v, target: v };
      }
      const word = tupleWord(tuple);
      return { source: pathSource(word, ctx), target: pathTarget(word, ctx) };
    }

    function tupleId(tuple) {
      return tuple.join("||");
    }

    function chainsForHHDegree(degree, chainCache, ctx) {
      if (degree === 0) return ctx.vertices.map((v) => ({ parts: ["@" + v], word: [] }));
      return chainCache[degree - 1] || [];
    }

    function buildHHChains(maxDegree, computation) {
      const { ctx, graph, opts } = computation;
      const chainCache = [];
      const cap = Math.max(opts.maxChains || 2000, 5000);
      for (let n = 0; n <= maxDegree; n++) {
        const result = listChains(ctx, graph, n, cap);
        if (result.truncated) throw new Error("W(" + n + ") exceeded the chain cap " + cap);
        chainCache[n] = result.chains;
      }
      return chainCache;
    }

    function cochainBasisForDegree(degree, algebraBasis, chainCache, computation) {
      const { ctx } = computation;
      const chains = chainsForHHDegree(degree, chainCache, ctx);
      const basis = [];
      for (const chain of chains) {
        const endpoints = chainEndpoints(chain.parts, ctx);
        for (const aKey of algebraBasis) {
          if (pathKeySource(aKey, ctx) === endpoints.source && pathKeyTarget(aKey, ctx) === endpoints.target) {
            basis.push({ chain: chain.parts, chainId: tupleId(chain.parts), aKey });
          }
        }
      }
      return basis;
    }

    function homologyBasisForDegree(degree, algebraBasis, chainCache, computation) {
      const { ctx } = computation;
      const chains = chainsForHHDegree(degree, chainCache, ctx);
      const basis = [];
      for (const chain of chains) {
        const endpoints = chainEndpoints(chain.parts, ctx);
        for (const aKey of algebraBasis) {
          if (pathKeySource(aKey, ctx) === endpoints.target && pathKeyTarget(aKey, ctx) === endpoints.source) {
            basis.push({ chain: chain.parts, chainId: tupleId(chain.parts), aKey });
          }
        }
      }
      return basis;
    }

    function addMatrixEntry(matrix, row, col, coeff) {
      if (coeff.isZero()) return;
      if (!matrix.has(row)) matrix.set(row, new Map());
      const rowMap = matrix.get(row);
      const next = (rowMap.get(col) || Rat.zero()).add(coeff);
      if (next.isZero()) rowMap.delete(col);
      else rowMap.set(col, next);
      if (rowMap.size === 0) matrix.delete(row);
    }

    function differentialMatrixCochain(degree, spaces, chainCache, computation) {
      const domain = spaces[degree];
      const codomain = spaces[degree + 1];
      const rowIndex = new Map(codomain.map((b, i) => [b.chainId + "|" + b.aKey, i]));
      const lowByChain = new Map();
      domain.forEach((b, col) => {
        if (!lowByChain.has(b.chainId)) lowByChain.set(b.chainId, []);
        lowByChain.get(b.chainId).push({ ...b, col });
      });
      const matrix = new Map();
      const highChains = chainsForHHDegree(degree + 1, chainCache, computation.ctx);
      for (const high of highChains) {
        const zigzags = computeMorseZigzags(high.parts, computation);
        for (const path of zigzags.paths) {
          const lowId = tupleId(path.tuple);
          const columns = lowByChain.get(lowId) || [];
          for (const colData of columns) {
            const product = multiplyWeightByAlgebraPath(path.weight, colData.aKey, computation);
            for (const [resultKey, coeff] of product.entries()) {
              const row = rowIndex.get(tupleId(high.parts) + "|" + resultKey);
              if (row != null) addMatrixEntry(matrix, row, colData.col, coeff);
            }
          }
        }
      }
      return { matrix, rows: codomain.length, cols: domain.length };
    }

    function multiplyHomologyWeightByAlgebraPath(weight, middleKey, computation) {
      let terms = new Map([[middleKey, weight.scalar]]);
      if (weight.right.length) {
        const rightKey = keyOf(weight.right);
        terms = multiplySparseByKey(rightKey, terms, computation, true);
      }
      if (weight.left.length) {
        const leftKey = keyOf(weight.left);
        terms = multiplySparseByKey(leftKey, terms, computation, false);
      }
      return terms;
    }

    function differentialMatrixHomology(degree, spaces, chainCache, computation) {
      const domain = spaces[degree];
      if (degree === 0) return { matrix: new Map(), rows: 0, cols: domain.length };
      const codomain = spaces[degree - 1];
      const rowIndex = new Map(codomain.map((b, i) => [b.chainId + "|" + b.aKey, i]));
      const highByChain = new Map();
      domain.forEach((b, col) => {
        if (!highByChain.has(b.chainId)) highByChain.set(b.chainId, []);
        highByChain.get(b.chainId).push({ ...b, col });
      });
      const matrix = new Map();
      const highChains = chainsForHHDegree(degree, chainCache, computation.ctx);
      for (const high of highChains) {
        const zigzags = computeMorseZigzags(high.parts, computation);
        const columns = highByChain.get(tupleId(high.parts)) || [];
        for (const colData of columns) {
          for (const path of zigzags.paths) {
            const product = multiplyHomologyWeightByAlgebraPath(path.weight, colData.aKey, computation);
            for (const [resultKey, coeff] of product.entries()) {
              const row = rowIndex.get(tupleId(path.tuple) + "|" + resultKey);
              if (row != null) addMatrixEntry(matrix, row, colData.col, coeff);
            }
          }
        }
      }
      return { matrix, rows: codomain.length, cols: domain.length };
    }

    function rankSparseMatrix(data) {
      const rows = [...data.matrix.values()].map((row) => new Map(row));
      let rank = 0;
      for (let col = 0; col < data.cols; col++) {
        let pivot = -1;
        for (let r = rank; r < rows.length; r++) {
          const value = rows[r].get(col);
          if (value && !value.isZero()) {
            pivot = r;
            break;
          }
        }
        if (pivot < 0) continue;
        const tmp = rows[rank];
        rows[rank] = rows[pivot];
        rows[pivot] = tmp;
        const pivotValue = rows[rank].get(col);
        for (const [k, v] of [...rows[rank].entries()]) rows[rank].set(k, v.div(pivotValue));
        for (let r = 0; r < rows.length; r++) {
          if (r === rank) continue;
          const factor = rows[r].get(col);
          if (!factor || factor.isZero()) continue;
          for (const [k, v] of rows[rank].entries()) {
            const next = (rows[r].get(k) || Rat.zero()).sub(factor.mul(v));
            if (next.isZero()) rows[r].delete(k);
            else rows[r].set(k, next);
          }
        }
        rank += 1;
        if (rank === rows.length) break;
      }
      return rank;
    }

    function cleanVector(vector) {
      const out = new Map();
      for (const [k, v] of vector.entries()) {
        if (!v.isZero()) out.set(Number(k), v);
      }
      return out;
    }

    function rrefVectors(vectors, dimension) {
      const rows = vectors.map((v) => cleanVector(v)).filter((v) => v.size > 0);
      const pivots = [];
      let rank = 0;
      for (let col = 0; col < dimension; col++) {
        let pivot = -1;
        for (let r = rank; r < rows.length; r++) {
          const value = rows[r].get(col);
          if (value && !value.isZero()) {
            pivot = r;
            break;
          }
        }
        if (pivot < 0) continue;
        const tmp = rows[rank];
        rows[rank] = rows[pivot];
        rows[pivot] = tmp;
        const pivotValue = rows[rank].get(col);
        for (const [k, v] of [...rows[rank].entries()]) rows[rank].set(k, v.div(pivotValue));
        for (let r = 0; r < rows.length; r++) {
          if (r === rank) continue;
          const factor = rows[r].get(col);
          if (!factor || factor.isZero()) continue;
          for (const [k, v] of rows[rank].entries()) {
            const next = (rows[r].get(k) || Rat.zero()).sub(factor.mul(v));
            if (next.isZero()) rows[r].delete(k);
            else rows[r].set(k, next);
          }
        }
        pivots.push(col);
        rank += 1;
        if (rank === rows.length) break;
      }
      return { rows: rows.slice(0, rank), pivots, rank };
    }

    function rankOfVectors(vectors, dimension) {
      return rrefVectors(vectors, dimension).rank;
    }

    function columnVectors(data) {
      const cols = Array.from({ length: data.cols }, () => new Map());
      for (const [row, rowMap] of data.matrix.entries()) {
        for (const [col, coeff] of rowMap.entries()) {
          if (!coeff.isZero()) cols[col].set(row, coeff);
        }
      }
      return cols.filter((v) => v.size > 0);
    }

    function independentBasis(vectors, dimension) {
      const selected = [];
      let rank = 0;
      for (const vector of vectors) {
        const cleaned = cleanVector(vector);
        if (!cleaned.size) continue;
        const nextRank = rankOfVectors(selected.concat(cleaned), dimension);
        if (nextRank > rank) {
          selected.push(cleaned);
          rank = nextRank;
        }
      }
      return selected;
    }

    function kernelBasis(data) {
      const equationRows = [...data.matrix.values()].map((row) => new Map(row));
      const rref = rrefVectors(equationRows, data.cols);
      const pivotSet = new Set(rref.pivots);
      const basis = [];
      for (let free = 0; free < data.cols; free++) {
        if (pivotSet.has(free)) continue;
        const vector = new Map([[free, Rat.one()]]);
        rref.pivots.forEach((pivotCol, rowIndex) => {
          const coeff = rref.rows[rowIndex].get(free) || Rat.zero();
          if (!coeff.isZero()) vector.set(pivotCol, coeff.neg());
        });
        basis.push(cleanVector(vector));
      }
      return basis;
    }

    function quotientRepresentatives(kernelVectors, imageVectors, dimension) {
      const imageBasis = independentBasis(imageVectors, dimension);
      const reps = [];
      let rank = rankOfVectors(imageBasis, dimension);
      for (const vector of kernelVectors) {
        const nextRank = rankOfVectors(imageBasis.concat(reps, vector), dimension);
        if (nextRank > rank) {
          reps.push(cleanVector(vector));
          rank = nextRank;
        }
      }
      return reps;
    }

    function formatPathKeyForHH(key) {
      if (key.startsWith("@")) return "e_" + key.slice(1);
      return formatPath(pathOf(key));
    }

    function pathLabelHtml(path, ctx) {
      const display = pathForDisplay(path, ctx);
      return display.length ? display.map((arrow) => escapeHtml(arrow)).join(" ") : "e";
    }

    function formatPathKeyForHHHtml(key, ctx) {
      if (key.startsWith("@")) return "e<sub>" + escapeHtml(key.slice(1)) + "</sub>";
      return pathLabelHtml(pathOf(key), ctx);
    }

    function formatTupleHtml(tuple, ctx) {
      if (!tuple.length) return "()";
      if (tuple.length === 1 && tuple[0].startsWith("@")) return "e<sub>" + escapeHtml(tuple[0].slice(1)) + "</sub>";
      return "(" + tuple.map((k) => k.startsWith("@") ? "e<sub>" + escapeHtml(k.slice(1)) + "</sub>" : pathLabelHtml(pathOf(k), null)).join(", ") + ")";
    }

    function ratHtml(value) {
      const text = value.toString();
      if (!text.includes("/")) return escapeHtml(text);
      const [num, den] = text.split("/");
      return "<span class=\"math-frac\"><sup>" + escapeHtml(num) + "</sup>&frasl;<sub>" + escapeHtml(den) + "</sub></span>";
    }

    function formatSignedMathVector(vector, space, termHtml) {
      const entries = [...vector.entries()].sort((a, b) => a[0] - b[0]);
      if (!entries.length) return "0";
      let out = "";
      entries.forEach(([index, coeff], termIndex) => {
        const sign = coeff.sign();
        const abs = coeff.abs();
        let body = termHtml(space[index]);
        if (!abs.isOne()) body = ratHtml(abs) + " " + body;
        if (termIndex === 0) out += sign < 0 ? "&minus; " + body : body;
        else out += sign < 0 ? " &minus; " + body : " + " + body;
      });
      return out;
    }

    function formatCochainVectorHtml(vector, space, ctx) {
      return formatSignedMathVector(vector, space, (data) => {
        return "[" + formatTupleHtml(data.chain, ctx) + " <span class=\"math-arrow\">&mapsto;</span> " + formatPathKeyForHHHtml(data.aKey, ctx) + "]";
      });
    }

    function formatHomologyVector(vector, space) {
      const entries = [...vector.entries()].sort((a, b) => a[0] - b[0]);
      if (!entries.length) return "0";
      let out = "";
      entries.forEach(([index, coeff], termIndex) => {
        const data = space[index];
        const sign = coeff.sign();
        const abs = coeff.abs();
        let body = formatPathKeyForHH(data.aKey) + " ⊗ " + formatTuple(data.chain);
        if (!abs.isOne()) body = abs.toString() + " " + body;
        if (termIndex === 0) out += sign < 0 ? "- " + body : body;
        else out += sign < 0 ? " - " + body : " + " + body;
      });
      return out;
    }

    function formatHomologyVectorHtml(vector, space, ctx) {
      return formatSignedMathVector(vector, space, (data) => {
        return formatPathKeyForHHHtml(data.aKey, ctx) + " <span class=\"math-tensor\">&otimes;</span> " + formatTupleHtml(data.chain, ctx);
      });
    }

    function activeOutputTab() {
      const active = document.querySelector("[data-tab].active");
      return active ? active.dataset.tab : "basic";
    }

    function setFieldFromComputation(computation) {
      setFieldCharacteristic((computation && computation.opts && computation.opts.characteristic) || (computation && computation.ctx && computation.ctx.characteristic) || 0);
    }

    function setHHLogsHtml(html) {
      $("hhCohomologyLog").innerHTML = html;
      $("hhHomologyLog").innerHTML = html;
    }

    function hhPlaceholderHtml() {
      return "<div class=\"math-muted\">Click Show degrees, then choose a degree to compute Hochschild cohomology or homology.</div>";
    }

    function renderHHLogLine(line) {
      if (!line) return "";
      if (line.startsWith("Cohomology:")) {
        return "<strong>Cohomology.</strong> <span class=\"math\">C<sup>n</sup> = Hom<sub>A<sup>e</sup></sub>(P<sub>n</sub>, A)</span>.";
      }
      if (line.startsWith("Homology:")) {
        return "<strong>Homology.</strong> <span class=\"math\">C<sub>n</sub> = A <span class=\"math-tensor\">&otimes;<sub>A<sup>e</sup></sub></span> P<sub>n</sub></span>.";
      }
      let html = escapeHtml(line);
      html = html
        .replace(/dim_k A/g, "dim<sub>k</sub> A")
        .replace(/&lt;=/g, "&le;")
        .replace(/HH\^(\d+)/g, "HH<sup>$1</sup>")
        .replace(/HH_(\d+)/g, "HH<sub>$1</sub>");
      return html;
    }

    function renderHHLogs(log) {
      const lines = log.filter((line) => line !== "").map((line) => "<div>" + renderHHLogLine(line) + "</div>");
      setHHLogsHtml(lines.length ? lines.join("") : "<div class=\"math-muted\">No HH log messages.</div>");
    }

    function mathListHtml(items) {
      if (!items.length) return "<div class=\"math-muted\">0</div>";
      return "<ol class=\"math-list\">" + items.map((item, index) => {
        return "<li><span class=\"math-index\">" + (index + 1) + ".</span> <span class=\"math\">" + item + "</span></li>";
      }).join("") + "</ol>";
    }

    function mathSectionHtml(headingHtml, items) {
      return "<div class=\"math-section\"><div class=\"math-heading\">" + headingHtml + "</div>" + mathListHtml(items) + "</div>";
    }

    function hhInputKey(values) {
      return JSON.stringify({
        quiverMode: values.quiverMode,
        vertices: values.vertices,
        arrows: values.arrows,
        tikzcd: values.tikzcd,
        order: values.order,
        earlierLarge: values.earlierLarge,
        characteristic: values.characteristic,
        relations: values.relations,
        maxDegree: values.maxDegree,
        maxBasis: values.maxBasis,
        maxPairs: values.maxPairs,
        maxChains: values.maxChains,
        hhDimCap: values.hhDimCap
      });
    }

    function hhDegreeButtonsHtml(kind, maxDegree) {
      const isCohomology = kind === "cohomology";
      return Array.from({ length: maxDegree + 1 }, (_, degree) => {
        const attr = isCohomology ? "data-hh-degree" : "data-hh-homology-degree";
        const label = isCohomology ? "HH<sup>" + degree + "</sup>" : "HH<sub>" + degree + "</sub>";
        return "<button class=\"tab\" type=\"button\" " + attr + "=\"" + degree + "\">" + label + "</button>";
      }).join("");
    }

    function emptyHHTableHtml(kind) {
      if (kind === "cohomology") {
        return "<tr><th>n</th><th>dim C<sup>n</sup></th><th>rank d<sup>n</sup></th><th>rank d<sup>n-1</sup></th><th>dim HH<sup>n</sup></th></tr>";
      }
      return "<tr><th>n</th><th>dim C<sub>n</sub></th><th>rank d<sub>n</sub></th><th>rank d<sub>n+1</sub></th><th>dim HH<sub>n</sub></th></tr>";
    }

    function hhRowHtml(kind, row) {
      if (kind === "cohomology") {
        return "<tr><td>" + row.degree + "</td><td>" + row.dimCn + "</td><td>" + row.rankDn + "</td><td>" + row.rankPrev + "</td><td>" + row.hh + "</td></tr>";
      }
      return "<tr><td>" + row.degree + "</td><td>" + row.dimCn + "</td><td>" + row.rankDn + "</td><td>" + row.rankNext + "</td><td>" + row.hh + "</td></tr>";
    }

    function renderHHDegreeTable(kind) {
      const cache = kind === "cohomology" ? hhDegreeCache.cohomology : hhDegreeCache.homology;
      const rows = [...cache.values()].sort((a, b) => a.degree - b.degree);
      const table = kind === "cohomology" ? $("hhTable") : $("hhHomologyTable");
      table.innerHTML = emptyHHTableHtml(kind) + rows.map((item) => hhRowHtml(kind, item.row)).join("");
    }

    function hhModeLogLine(computation) {
      return computation.monomialFast ? "Bardzell fast mode for monomial algebra." : "Morse-Anick mode for non-monomial algebra.";
    }

    function computeHHDegreeResult(values, kind, degree) {
      const computation = computeBaseFromInputValues(values);
      const dimCap = Math.max(1, Number(values.hhDimCap) || computation.opts.hhDimCap || 100);
      const algebraBasis = generateAlgebraBasis(computation.ctx, computation.W, dimCap);
      const chainCache = buildHHChains(degree + 1, computation);
      const log = [
        "Restriction: finite-dimensional algebra with dim_k A <= " + dimCap + ".",
        "Characteristic of k: " + (computation.opts.characteristic ? computation.opts.characteristic : "0") + ".",
        "Basis of A: " + algebraBasis.length + " NonTip paths.",
        hhModeLogLine(computation),
        kind === "cohomology" ? "Cohomology: chain complex." : "Homology: chain complex."
      ];
      if (kind === "cohomology") return computeCohomologyDegreeResult(degree, computation, algebraBasis, chainCache, log);
      return computeHomologyDegreeResult(degree, computation, algebraBasis, chainCache, log);
    }

    function computeCohomologyDegreeResult(degree, computation, algebraBasis, chainCache, log) {
      const spaces = [];
      for (let i = 0; i <= degree + 1; i++) spaces[i] = cochainBasisForDegree(i, algebraBasis, chainCache, computation);
      const differential = differentialMatrixCochain(degree, spaces, chainCache, computation);
      const previous = degree === 0 ? { matrix: new Map(), rows: spaces[0].length, cols: 0 } : differentialMatrixCochain(degree - 1, spaces, chainCache, computation);
      const rankDn = rankSparseMatrix(differential);
      const rankPrev = degree === 0 ? 0 : rankSparseMatrix(previous);
      const dimCn = spaces[degree].length;
      const kernelVectors = kernelBasis(differential);
      const imageVectors = degree === 0 ? [] : columnVectors(previous);
      const imageBasis = independentBasis(imageVectors, dimCn);
      const representatives = quotientRepresentatives(kernelVectors, imageVectors, dimCn);
      const row = {
        degree,
        dimCn,
        rankDn,
        rankPrev,
        hh: dimCn - rankDn - rankPrev
      };
      const kernelBasisHtml = kernelVectors.map((vector) => formatCochainVectorHtml(vector, spaces[degree], computation.ctx));
      const imageBasisHtml = imageBasis.map((vector) => formatCochainVectorHtml(vector, spaces[degree], computation.ctx));
      const hhBasisHtml = representatives.map((vector) => formatCochainVectorHtml(vector, spaces[degree], computation.ctx));
      const warning = representatives.length === row.hh ? "" : "Representative count is " + representatives.length + ", expected " + row.hh + ".";
      const detailHtml = [
        "<div class=\"math-section\"><div class=\"math math-heading\">Degree <span class=\"math\">n = " + degree + "</span></div></div>",
        warning ? "<div class=\"math-section\"><div class=\"math-muted\">" + escapeHtml(warning) + "</div></div>" : "",
        mathSectionHtml("Basis for <span class=\"math\">ker d<sup>" + degree + "</sup></span> (dimension " + (dimCn - rankDn) + ")", kernelBasisHtml),
        mathSectionHtml("Basis for <span class=\"math\">im d<sup>" + (degree - 1) + "</sup> &subset; C<sup>" + degree + "</sup></span> (dimension " + rankPrev + ")", imageBasisHtml),
        mathSectionHtml("Representatives for <span class=\"math\">HH<sup>" + degree + "</sup>(A) = ker d<sup>" + degree + "</sup> / im d<sup>" + (degree - 1) + "</sup></span> (dimension " + row.hh + ")", hhBasisHtml)
      ].join("");
      return { kind: "cohomology", degree, row, detailHtml, log };
    }

    function computeHomologyDegreeResult(degree, computation, algebraBasis, chainCache, log) {
      const spaces = [];
      for (let i = 0; i <= degree + 1; i++) spaces[i] = homologyBasisForDegree(i, algebraBasis, chainCache, computation);
      const differential = differentialMatrixHomology(degree, spaces, chainCache, computation);
      const next = differentialMatrixHomology(degree + 1, spaces, chainCache, computation);
      const rankDn = rankSparseMatrix(differential);
      const rankNext = rankSparseMatrix(next);
      const dimCn = spaces[degree].length;
      const kernelVectors = kernelBasis(differential);
      const imageVectors = columnVectors(next);
      const imageBasis = independentBasis(imageVectors, dimCn);
      const representatives = quotientRepresentatives(kernelVectors, imageVectors, dimCn);
      const row = {
        degree,
        dimCn,
        rankDn,
        rankNext,
        hh: dimCn - rankDn - rankNext
      };
      const kernelBasisHtml = kernelVectors.map((vector) => formatHomologyVectorHtml(vector, spaces[degree], computation.ctx));
      const imageBasisHtml = imageBasis.map((vector) => formatHomologyVectorHtml(vector, spaces[degree], computation.ctx));
      const hhBasisHtml = representatives.map((vector) => formatHomologyVectorHtml(vector, spaces[degree], computation.ctx));
      const warning = representatives.length === row.hh ? "" : "Representative count is " + representatives.length + ", expected " + row.hh + ".";
      const detailHtml = [
        "<div class=\"math-section\"><div class=\"math math-heading\">Degree <span class=\"math\">n = " + degree + "</span></div></div>",
        warning ? "<div class=\"math-section\"><div class=\"math-muted\">" + escapeHtml(warning) + "</div></div>" : "",
        mathSectionHtml("Basis for <span class=\"math\">ker d<sub>" + degree + "</sub></span> (dimension " + (dimCn - rankDn) + ")", kernelBasisHtml),
        mathSectionHtml("Basis for <span class=\"math\">im d<sub>" + (degree + 1) + "</sub> &subset; C<sub>" + degree + "</sub></span> (dimension " + rankNext + ")", imageBasisHtml),
        mathSectionHtml("Representatives for <span class=\"math\">HH<sub>" + degree + "</sub>(A) = ker d<sub>" + degree + "</sub> / im d<sub>" + (degree + 1) + "</sub></span> (dimension " + row.hh + ")", hhBasisHtml)
      ].join("");
      return { kind: "homology", degree, row, detailHtml, log };
    }

    function computeHochschildCohomology() {
      let inputCharacteristic = 0;
      let inputComposition = "ltr";
      try {
        inputCharacteristic = readCharacteristic();
        inputComposition = readCompositionDirection();
      } catch (err) {
        setStatus([{ text: "computation failed", kind: "bad" }]);
        setError(err && err.message ? err.message : String(err));
        return;
      }
      if (!lastComputation || (lastComputation.opts && lastComputation.opts.characteristic) !== inputCharacteristic || (lastComputation.opts && lastComputation.opts.compositionDirection) !== inputComposition) compute();
      if (!lastComputation) return;
      if ((lastComputation.opts && lastComputation.opts.characteristic) !== inputCharacteristic || (lastComputation.opts && lastComputation.opts.compositionDirection) !== inputComposition) return;
      const previousTab = activeOutputTab();
      try {
        $("hhStatus").textContent = "computing...";
        $("hhHomologyStatus").textContent = "computing...";
        $("hhTable").innerHTML = "";
        $("hhHomologyTable").innerHTML = "";
        $("hhDegreeTabs").innerHTML = "";
        $("hhDetailOutput").innerHTML = "";
        $("hhHomologyDegreeTabs").innerHTML = "";
        $("hhHomologyDetailOutput").innerHTML = "";
        lastHHResult = null;
        setHHLogsHtml("<div>Computing HH with the current <span class=\"math\">G</span>, <span class=\"math\">W = Tip(G)</span>, and Morse zigzag differential...</div>");
        const computation = lastComputation;
        setFieldFromComputation(computation);
        const maxDegree = Math.max(0, readInt("hhDegreeInput", computation.opts.hhDegree || 0));
        const dimCap = Math.max(1, readInt("hhDimCapInput", computation.opts.hhDimCap || 100));
        const algebraBasis = generateAlgebraBasis(computation.ctx, computation.W, dimCap);
        const chainCache = buildHHChains(maxDegree + 1, computation);
        const spaces = [];
        const homologySpaces = [];
        for (let degree = 0; degree <= maxDegree + 1; degree++) {
          spaces[degree] = cochainBasisForDegree(degree, algebraBasis, chainCache, computation);
          homologySpaces[degree] = homologyBasisForDegree(degree, algebraBasis, chainCache, computation);
        }
        const differentials = [];
        const ranks = [];
        for (let degree = 0; degree <= maxDegree; degree++) {
          differentials[degree] = differentialMatrixCochain(degree, spaces, chainCache, computation);
          ranks[degree] = rankSparseMatrix(differentials[degree]);
        }
        const homologyDifferentials = [];
        const homologyRanks = [];
        for (let degree = 0; degree <= maxDegree + 1; degree++) {
          homologyDifferentials[degree] = differentialMatrixHomology(degree, homologySpaces, chainCache, computation);
          homologyRanks[degree] = rankSparseMatrix(homologyDifferentials[degree]);
        }
        const rows = [];
        const homologyRows = [];
        const log = [
          "Restriction: finite-dimensional algebra with dim_k A <= " + dimCap + ".",
          "Characteristic of k: " + (computation.opts.characteristic ? computation.opts.characteristic : "0") + ".",
          "Basis of A: " + algebraBasis.length + " NonTip paths.",
          "Basis data is computed on demand after the dimension tables are ready.",
          "Cohomology: chain complex.",
          "Homology: chain complex.",
          ""
        ];
        for (let degree = 0; degree <= maxDegree; degree++) {
          const dimCn = spaces[degree].length;
          const rankDn = ranks[degree] || 0;
          const rankPrev = degree === 0 ? 0 : (ranks[degree - 1] || 0);
          const ker = dimCn - rankDn;
          const hh = ker - rankPrev;
          rows.push({
            degree,
            dimCn,
            rankDn,
            rankPrev,
            hh,
            basisComputed: false,
            kernelBasis: [],
            imageBasis: [],
            hhBasis: []
          });

          const dimHnChain = homologySpaces[degree].length;
          const rankDnHomology = homologyRanks[degree] || 0;
          const rankNextHomology = homologyRanks[degree + 1] || 0;
          const homologyKernel = dimHnChain - rankDnHomology;
          const homologyDim = homologyKernel - rankNextHomology;
          homologyRows.push({
            degree,
            dimCn: dimHnChain,
            rankDn: rankDnHomology,
            rankNext: rankNextHomology,
            hh: homologyDim,
            basisComputed: false,
            kernelBasis: [],
            imageBasis: [],
            hhBasis: []
          });
        }
        renderHHResult(rows, homologyRows, log, { spaces, differentials, homologySpaces, homologyDifferentials });
        activateTab(previousTab === "homology" ? "homology" : "cohomology");
      } catch (err) {
      $("hhStatus").textContent = "failed";
      $("hhHomologyStatus").textContent = "failed";
      $("hhTable").innerHTML = "";
      $("hhHomologyTable").innerHTML = "";
      $("hhDegreeTabs").innerHTML = "";
      $("hhDetailOutput").innerHTML = "";
      $("hhHomologyDegreeTabs").innerHTML = "";
      $("hhHomologyDetailOutput").innerHTML = "";
      lastHHResult = null;
      setHHLogsHtml("<div class=\"math-muted\">" + escapeHtml(err && err.message ? err.message : String(err)) + "</div>");
      activateTab(previousTab === "homology" ? "homology" : "cohomology");
      }
    }

    function hhBasisPromptHtml(kind) {
      return "<div class=\"math-muted\">Dimension table is ready. Click a degree button above to compute " + kind + " basis data for that degree.</div>";
    }

    function ensureHHCohomologyBasis(row) {
      if (row.basisComputed) return;
      setFieldCharacteristic(lastHHResult.characteristic || 0);
      const degree = row.degree;
      const dimension = row.dimCn;
      const space = lastHHResult.spaces[degree];
      const imageVectors = degree === 0 ? [] : columnVectors(lastHHResult.differentials[degree - 1]);
      const imageBasis = independentBasis(imageVectors, dimension);
      const kernelVectors = kernelBasis(lastHHResult.differentials[degree]);
      const representatives = quotientRepresentatives(kernelVectors, imageVectors, dimension);
      row.kernelBasis = kernelVectors.map((vector) => formatCochainVectorHtml(vector, space, lastHHResult.ctx));
      row.imageBasis = imageBasis.map((vector) => formatCochainVectorHtml(vector, space, lastHHResult.ctx));
      row.hhBasis = representatives.map((vector) => formatCochainVectorHtml(vector, space, lastHHResult.ctx));
      row.basisWarning = representatives.length === row.hh ? "" : "Representative count is " + representatives.length + ", expected " + row.hh + ".";
      row.basisComputed = true;
    }

    function ensureHHHomologyBasis(row) {
      if (row.basisComputed) return;
      setFieldCharacteristic(lastHHResult.characteristic || 0);
      const degree = row.degree;
      const dimension = row.dimCn;
      const space = lastHHResult.homologySpaces[degree];
      const kernelVectors = kernelBasis(lastHHResult.homologyDifferentials[degree]);
      const imageVectors = columnVectors(lastHHResult.homologyDifferentials[degree + 1]);
      const imageBasis = independentBasis(imageVectors, dimension);
      const representatives = quotientRepresentatives(kernelVectors, imageVectors, dimension);
      row.kernelBasis = kernelVectors.map((vector) => formatHomologyVectorHtml(vector, space, lastHHResult.ctx));
      row.imageBasis = imageBasis.map((vector) => formatHomologyVectorHtml(vector, space, lastHHResult.ctx));
      row.hhBasis = representatives.map((vector) => formatHomologyVectorHtml(vector, space, lastHHResult.ctx));
      row.basisWarning = representatives.length === row.hh ? "" : "Representative count is " + representatives.length + ", expected " + row.hh + ".";
      row.basisComputed = true;
    }

    function renderHHResult(rows, homologyRows, log, cache) {
      lastHHResult = { cohomologyRows: rows, homologyRows, log, characteristic: lastComputation && lastComputation.opts ? lastComputation.opts.characteristic : 0, ctx: lastComputation ? lastComputation.ctx : null, ...cache };
      $("hhStatus").textContent = rows.length ? "dimensions through degree " + rows[rows.length - 1].degree : "";
      $("hhHomologyStatus").textContent = homologyRows.length ? "dimensions through degree " + homologyRows[homologyRows.length - 1].degree : "";
      $("hhTable").innerHTML = [
        "<tr><th>n</th><th>dim C<sup>n</sup></th><th>rank d<sup>n</sup></th><th>rank d<sup>n-1</sup></th><th>dim HH<sup>n</sup></th></tr>",
        ...rows.map((row) => "<tr><td>" + row.degree + "</td><td>" + row.dimCn + "</td><td>" + row.rankDn + "</td><td>" + row.rankPrev + "</td><td>" + row.hh + "</td></tr>")
      ].join("");
      $("hhHomologyTable").innerHTML = [
        "<tr><th>n</th><th>dim C<sub>n</sub></th><th>rank d<sub>n</sub></th><th>rank d<sub>n+1</sub></th><th>dim HH<sub>n</sub></th></tr>",
        ...homologyRows.map((row) => "<tr><td>" + row.degree + "</td><td>" + row.dimCn + "</td><td>" + row.rankDn + "</td><td>" + row.rankNext + "</td><td>" + row.hh + "</td></tr>")
      ].join("");
      $("hhDegreeTabs").innerHTML = rows.map((row, index) => {
        return "<button class=\"tab\" type=\"button\" data-hh-degree=\"" + row.degree + "\">Basis for HH<sup>" + row.degree + "</sup></button>";
      }).join("");
      $("hhHomologyDegreeTabs").innerHTML = homologyRows.map((row, index) => {
        return "<button class=\"tab\" type=\"button\" data-hh-homology-degree=\"" + row.degree + "\">Basis for HH<sub>" + row.degree + "</sub></button>";
      }).join("");
      $("hhDetailOutput").innerHTML = rows.length ? hhBasisPromptHtml("cohomology") : "";
      $("hhHomologyDetailOutput").innerHTML = homologyRows.length ? hhBasisPromptHtml("homology") : "";
      renderHHLogs(log);
    }

    function renderHHDegreeDetail(degree) {
      if (!lastHHResult) return;
      const row = lastHHResult.cohomologyRows.find((item) => item.degree === degree);
      if (!row) return;
      document.querySelectorAll("[data-hh-degree]").forEach((btn) => {
        btn.classList.toggle("active", Number(btn.dataset.hhDegree) === degree);
      });
      $("hhDetailOutput").innerHTML = "<div class=\"math-muted\">Computing basis for <span class=\"math\">HH<sup>" + row.degree + "</sup>(A)</span>...</div>";
      ensureHHCohomologyBasis(row);
      $("hhDetailOutput").innerHTML = [
        "<div class=\"math-section\"><div class=\"math math-heading\">Degree <span class=\"math\">n = " + row.degree + "</span></div></div>",
        row.basisWarning ? "<div class=\"math-section\"><div class=\"math-muted\">" + escapeHtml(row.basisWarning) + "</div></div>" : "",
        mathSectionHtml("Basis for <span class=\"math\">ker d<sup>" + row.degree + "</sup></span> (dimension " + (row.dimCn - row.rankDn) + ")", row.kernelBasis),
        mathSectionHtml("Basis for <span class=\"math\">im d<sup>" + (row.degree - 1) + "</sup> &subset; C<sup>" + row.degree + "</sup></span> (dimension " + row.rankPrev + ")", row.imageBasis),
        mathSectionHtml("Representatives for <span class=\"math\">HH<sup>" + row.degree + "</sup>(A) = ker d<sup>" + row.degree + "</sup> / im d<sup>" + (row.degree - 1) + "</sup></span> (dimension " + row.hh + ")", row.hhBasis)
      ].join("");
    }

    function renderHHHomologyDegreeDetail(degree) {
      if (!lastHHResult) return;
      const row = lastHHResult.homologyRows.find((item) => item.degree === degree);
      if (!row) return;
      document.querySelectorAll("[data-hh-homology-degree]").forEach((btn) => {
        btn.classList.toggle("active", Number(btn.dataset.hhHomologyDegree) === degree);
      });
      $("hhHomologyDetailOutput").innerHTML = "<div class=\"math-muted\">Computing basis for <span class=\"math\">HH<sub>" + row.degree + "</sub>(A)</span>...</div>";
      ensureHHHomologyBasis(row);
      $("hhHomologyDetailOutput").innerHTML = [
        "<div class=\"math-section\"><div class=\"math math-heading\">Degree <span class=\"math\">n = " + row.degree + "</span></div></div>",
        row.basisWarning ? "<div class=\"math-section\"><div class=\"math-muted\">" + escapeHtml(row.basisWarning) + "</div></div>" : "",
        mathSectionHtml("Basis for <span class=\"math\">ker d<sub>" + row.degree + "</sub></span> (dimension " + (row.dimCn - row.rankDn) + ")", row.kernelBasis),
        mathSectionHtml("Basis for <span class=\"math\">im d<sub>" + (row.degree + 1) + "</sub> &subset; C<sub>" + row.degree + "</sub></span> (dimension " + row.rankNext + ")", row.imageBasis),
        mathSectionHtml("Representatives for <span class=\"math\">HH<sub>" + row.degree + "</sub>(A) = ker d<sub>" + row.degree + "</sub> / im d<sub>" + (row.degree + 1) + "</sub></span> (dimension " + row.hh + ")", row.hhBasis)
      ].join("");
    }

    function resetHHDegreeUi(values, key) {
      const maxDegree = Math.max(0, Number(values.hhDegree) || 0);
      hhDegreeCache = { key, values, cohomology: new Map(), homology: new Map() };
      lastHHResult = null;
      $("hhStatus").textContent = "choose a degree";
      $("hhHomologyStatus").textContent = "choose a degree";
      $("hhTable").innerHTML = emptyHHTableHtml("cohomology");
      $("hhHomologyTable").innerHTML = emptyHHTableHtml("homology");
      $("hhDegreeTabs").innerHTML = hhDegreeButtonsHtml("cohomology", maxDegree);
      $("hhHomologyDegreeTabs").innerHTML = hhDegreeButtonsHtml("homology", maxDegree);
      $("hhDetailOutput").innerHTML = "<div class=\"math-muted\">Click a degree button to compute that cohomology group.</div>";
      $("hhHomologyDetailOutput").innerHTML = "<div class=\"math-muted\">Click a degree button to compute that homology group.</div>";
      setHHLogsHtml("<div>Ready. Each degree is computed on demand in a Web Worker.</div>");
    }

    function prepareHHDegreeComputation() {
      try {
        const values = collectInputValues();
        resetHHDegreeUi(values, hhInputKey(values));
      } catch (err) {
        setStatus([{ text: "computation failed", kind: "bad" }]);
        setError(err && err.message ? err.message : String(err));
      }
    }

    function getPreparedHHValues() {
      const values = collectInputValues();
      const key = hhInputKey(values);
      if (hhDegreeCache.key !== key) resetHHDegreeUi(values, key);
      return { values, key };
    }

    function getHHWorker() {
      if (typeof Worker === "undefined") return null;
      if (hhWorker) return hhWorker;
      try {
        hhWorker = new Worker("app.js");
        hhWorker.onmessage = (event) => {
          const { id, ok, result, error } = event.data || {};
          const pending = hhPendingRequests.get(id);
          if (!pending) return;
          hhPendingRequests.delete(id);
          if (ok) pending.resolve(result);
          else pending.reject(new Error(error || "Worker failed"));
        };
        hhWorker.onerror = (event) => {
          const error = new Error(event.message || "Worker failed");
          for (const pending of hhPendingRequests.values()) pending.reject(error);
          hhPendingRequests.clear();
          hhWorker = null;
        };
        return hhWorker;
      } catch (err) {
        hhWorker = null;
        return null;
      }
    }

    function runHHDegreeTask(values, kind, degree) {
      const worker = getHHWorker();
      if (!worker) return Promise.resolve().then(() => computeHHDegreeResult(values, kind, degree));
      const id = ++hhRequestSeq;
      return new Promise((resolve, reject) => {
        hhPendingRequests.set(id, { resolve, reject });
        worker.postMessage({ type: "hh-degree", id, values, kind, degree });
      });
    }

    function setHHActiveButton(kind, degree) {
      const selector = kind === "cohomology" ? "[data-hh-degree]" : "[data-hh-homology-degree]";
      document.querySelectorAll(selector).forEach((btn) => {
        const value = kind === "cohomology" ? Number(btn.dataset.hhDegree) : Number(btn.dataset.hhHomologyDegree);
        btn.classList.toggle("active", value === degree);
      });
    }

    function applyHHDegreeResult(result) {
      const kind = result.kind;
      const cache = kind === "cohomology" ? hhDegreeCache.cohomology : hhDegreeCache.homology;
      cache.set(result.degree, result);
      renderHHDegreeTable(kind);
      renderHHLogs(result.log || []);
      setHHActiveButton(kind, result.degree);
      if (kind === "cohomology") {
        $("hhStatus").textContent = "degree " + result.degree + " computed";
        $("hhDetailOutput").innerHTML = result.detailHtml;
      } else {
        $("hhHomologyStatus").textContent = "degree " + result.degree + " computed";
        $("hhHomologyDetailOutput").innerHTML = result.detailHtml;
      }
    }

    async function computeHHDegreeOnDemand(kind, degree) {
      let prepared;
      try {
        prepared = getPreparedHHValues();
      } catch (err) {
        setStatus([{ text: "computation failed", kind: "bad" }]);
        setError(err && err.message ? err.message : String(err));
        return;
      }
      const cache = kind === "cohomology" ? hhDegreeCache.cohomology : hhDegreeCache.homology;
      if (cache.has(degree)) {
        applyHHDegreeResult(cache.get(degree));
        return;
      }
      setHHActiveButton(kind, degree);
      if (kind === "cohomology") {
        $("hhStatus").textContent = "computing degree " + degree + "...";
        $("hhDetailOutput").innerHTML = "<div class=\"math-muted\">Computing <span class=\"math\">HH<sup>" + degree + "</sup>(A)</span> in a Web Worker...</div>";
      } else {
        $("hhHomologyStatus").textContent = "computing degree " + degree + "...";
        $("hhHomologyDetailOutput").innerHTML = "<div class=\"math-muted\">Computing <span class=\"math\">HH<sub>" + degree + "</sub>(A)</span> in a Web Worker...</div>";
      }
      setHHLogsHtml("<div>Computing degree " + degree + "...</div>");
      try {
        const result = await runHHDegreeTask(prepared.values, kind, degree);
        if (hhDegreeCache.key !== prepared.key) return;
        applyHHDegreeResult(result);
      } catch (err) {
        const message = err && err.message ? err.message : String(err);
        if (kind === "cohomology") {
          $("hhStatus").textContent = "failed";
          $("hhDetailOutput").innerHTML = "<div class=\"math-muted\">" + escapeHtml(message) + "</div>";
        } else {
          $("hhHomologyStatus").textContent = "failed";
          $("hhHomologyDetailOutput").innerHTML = "<div class=\"math-muted\">" + escapeHtml(message) + "</div>";
        }
        setHHLogsHtml("<div class=\"math-muted\">" + escapeHtml(message) + "</div>");
      }
    }

    function setStatus(items) {
      const box = $("statusPills");
      box.innerHTML = "";
      for (const item of items) {
        const span = document.createElement("span");
        span.className = "pill " + (item.kind || "");
        span.textContent = item.text;
        box.appendChild(span);
      }
    }

    function setError(message) {
      const box = $("errorBox");
      box.innerHTML = "";
      if (!message) return;
      const div = document.createElement("div");
      div.className = "error-box";
      div.textContent = message;
      box.appendChild(div);
    }

    function fillList(id, items, formatter) {
      const list = $(id);
      list.innerHTML = "";
      if (!items.length) {
        const li = document.createElement("li");
        li.className = "empty";
        li.textContent = "empty";
        list.appendChild(li);
        return;
      }
      items.forEach((item, index) => {
        const li = document.createElement("li");
        li.innerHTML = formatter(item, index);
        list.appendChild(li);
      });
    }

    function escapeHtml(s) {
      return String(s)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;");
    }

    function renderAll(result) {
      const { ctx, basis, W, graph, chains, chainTotal, chainTruncated, warnings, stats, opts } = result;
      const monomialFast = isMonomialGroebnerBasis(basis);
      lastComputation = { ctx, basis, W, graph, chains, opts, monomialFast };
      const status = [
        { text: stats.completed ? "completion finished" : "partial G", kind: stats.completed ? "good" : "warn" },
        { text: "|G| = " + basis.length },
        { text: "|W| = " + W.length },
        { text: "|W(" + opts.n + ")| = " + chainTotal.toString(), kind: chainTruncated ? "warn" : "" },
        monomialFast ? { text: "Bardzell fast mode", kind: "good" } : null
      ].filter(Boolean);
      setStatus(status);
      setError("");

      $("basisCount").textContent = basis.length + " elements";
      fillList("basisList", basis, (g) => {
        const lt = g.leading(ctx);
        return "<code>Tip = " + escapeHtml(displayPath(lt.path, ctx)) + "</code> &nbsp; " + escapeHtml(formatPoly(g, ctx));
      });

      $("wCount").textContent = "W has " + W.length + " paths";

      const edgeGroups = new Map();
      for (const edge of qWEdges(ctx, graph)) {
        const fromNode = graph.vertices.get(edge.from);
        const toNode = graph.vertices.get(edge.to);
        if (!fromNode || !toNode) continue;
        const fromLabel = qWNodeLabel(fromNode);
        const toLabel = qWNodeLabel(toNode);
        if (!edgeGroups.has(fromLabel)) edgeGroups.set(fromLabel, []);
        edgeGroups.get(fromLabel).push(toLabel);
      }
      const totalQwEdges = [...edgeGroups.values()].reduce((sum, tos) => sum + tos.length, 0);
      $("graphCount").textContent = graph.vertices.size + " vertices, " + totalQwEdges + " edges";
      renderDiagrams(ctx, graph);

      $("chainCount").textContent = "n = " + opts.n + ", total = " + chainTotal.toString() + (chainTruncated ? ", shown = " + chains.length : "");
      fillList("chainList", chains, (c, index) => {
        const parts = c.parts.map((k) => "<code>" + escapeHtml(k.startsWith("e_") ? k : formatPath(pathOf(k))) + "</code>").join(" , ");
        const word = c.word && c.word.length ? " &nbsp; word: <code>" + escapeHtml(formatPath(c.word)) + "</code>" : "";
        return "<button class=\"chain-pick\" type=\"button\" data-chain-index=\"" + index + "\">(" + parts + ")" + word + "</button>";
      });
      $("diffCount").textContent = "";
      $("diffSummary").textContent = "Select a listed chain in W(n).";
      $("diffPaths").innerHTML = "";
      $("hhStatus").textContent = "";
      $("hhTable").innerHTML = "";
      $("hhHomologyStatus").textContent = "";
      $("hhHomologyTable").innerHTML = "";
      $("hhDegreeTabs").innerHTML = "";
      $("hhDetailOutput").innerHTML = "";
      $("hhHomologyDegreeTabs").innerHTML = "";
      $("hhHomologyDetailOutput").innerHTML = "";
      lastHHResult = null;
      setHHLogsHtml(hhPlaceholderHtml());

      const rows = [
        ["Characteristic of k", opts.characteristic ? String(opts.characteristic) : "0"],
        ["Path composition", "left to right"],
        ["Q0", ctx.vertices.join(", ")],
        ["Order on Q1", ctx.order.join(" > ")],
        ["Input relations", String(stats.inputRelations)],
        ["Elements added to G", String(stats.added)],
        ["queued compositions", String(stats.compositionsQueued)],
        ["processed compositions", String(stats.compositionsProcessed)],
        ["zero reductions", String(stats.reductionsToZero)],
        ["completion", stats.completed ? "finished" : "stopped by limits"]
      ];
      $("metricTable").innerHTML = rows.map(([a, b]) => "<tr><th>" + escapeHtml(a) + "</th><td>" + escapeHtml(b) + "</td></tr>").join("");
      $("logOutput").textContent = warnings.length ? warnings.join("\n") : "No warnings";
    }

    function compute() {
      try {
        setError("");
        const { ctx, relations, opts } = parseInput();
        const completed = completeBasis(relations, ctx, opts);
        const basis = completed.basis;
        const W = basis.map((g) => g.leading(ctx).path);
        const graph = buildUfnarovski(ctx, W);
        const chainTotal = countChains(ctx, graph, opts.n);
        const chainResult = listChains(ctx, graph, opts.n, opts.maxChains);
        renderAll({
          ctx,
          basis,
          W,
          graph,
          chains: chainResult.chains,
          chainTotal,
          chainTruncated: chainResult.truncated,
          warnings: completed.warnings,
          stats: completed.stats,
          opts
        });
      } catch (err) {
        setStatus([{ text: "computation failed", kind: "bad" }]);
        setError(err && err.message ? err.message : String(err));
      }
    }

    function loadSample(index = null) {
      const examples = [
        {
          vertices: "1, 2, 3",
          arrows: ["a: 1 -> 2", "a': 2 -> 1", "b: 2 -> 3", "b': 3 -> 2"],
          tikzcd: [
            "\\begin{tikzcd}",
            "1 \\arrow[r, \"a\", bend left] & 2 \\arrow[l, \"a'\", bend left] \\arrow[r, \"b\", bend left] & 3 \\arrow[l, \"b'\", bend left]",
            "\\end{tikzcd}"
          ],
          order: "a, b, b', a'",
          relations: ["a b = 0", "b' a' = 0", "a' a - b b' = 0"]
        },
        {
          vertices: "1",
          arrows: ["x: 1 -> 1"],
          tikzcd: [
            "\\begin{tikzcd}",
            "1 \\arrow[\"x\"', loop, distance=2em, in=305, out=235]",
            "\\end{tikzcd}"
          ],
          order: "x",
          relations: ["x x = 0"]
        },
        {
          vertices: "1",
          arrows: ["x: 1 -> 1", "y: 1 -> 1"],
          tikzcd: [
            "\\begin{tikzcd}",
            "1 \\arrow[\"x\"', loop, distance=2em, in=305, out=235] \\arrow[\"y\", loop, distance=2em, in=55, out=125]",
            "\\end{tikzcd}"
          ],
          order: "x, y",
          relations: ["x y - y x = 0", "x x = 0", "y y = 0"]
        },
        {
          vertices: "1",
          arrows: ["x: 1 -> 1", "y: 1 -> 1"],
          tikzcd: [
            "\\begin{tikzcd}",
            "1 \\arrow[\"x\"', loop, distance=2em, in=305, out=235] \\arrow[\"y\", loop, distance=2em, in=55, out=125]",
            "\\end{tikzcd}"
          ],
          order: "x, y",
          relations: ["x x - y y = 0", "x y = 0", "y x = 0"]
        },
        {
          mode: "tikzcd",
          vertices: "1, 2, 3",
          arrows: ["x: 1 -> 2", "y: 2 -> 3", "z: 3 -> 1"],
          tikzcd: [
            "\\begin{tikzcd}",
            " & 1 \\\\",
            " &  \\\\",
            "3 & 2",
            "\\arrow[from=1-2, to=3-2, \"{x}\"]",
            "\\arrow[from=3-2, to=3-1, \"{y}\"]",
            "\\arrow[from=3-1, to=1-2, \"{z}\"]",
            "\\end{tikzcd}"
          ],
          order: "x, y, z",
          relations: ["x y = 0", "y z = 0", "z x = 0"]
        }
      ];
      const chosenIndex = Number.isInteger(index) ? ((index % examples.length) + examples.length) % examples.length : Math.floor(Math.random() * examples.length);
      const chosen = examples[chosenIndex];
      $("verticesInput").value = chosen.vertices;
      $("arrowsInput").value = chosen.arrows.join("\n");
      $("tikzcdInput").value = chosen.tikzcd.join("\n");
      setQuiverMode(chosen.mode || "structured");
      $("orderInput").value = chosen.order;
      $("earlierLargeInput").checked = true;
      setCharacteristicInput(0);
      $("relationsInput").value = chosen.relations.join("\n");
      $("nInput").value = "2";
      $("maxDegreeInput").value = "14";
      $("maxBasisInput").value = "250";
      $("maxPairsInput").value = "12000";
      $("maxChainsInput").value = "2000";
      $("hhDegreeInput").value = "3";
      $("hhDimCapInput").value = "100";
      compute();
    }

    function clearOutput() {
      lastComputation = null;
      setStatus([]);
      setError("");
      $("basisCount").textContent = "";
      $("wCount").textContent = "";
      $("graphCount").textContent = "";
      $("chainCount").textContent = "";
      $("diffCount").textContent = "";
      $("basisList").innerHTML = "";
      $("chainList").innerHTML = "";
      $("diffSummary").textContent = "";
      $("diffPaths").innerHTML = "";
      $("hhStatus").textContent = "";
      $("hhTable").innerHTML = "";
      $("hhHomologyStatus").textContent = "";
      $("hhHomologyTable").innerHTML = "";
      $("hhDegreeTabs").innerHTML = "";
      $("hhDetailOutput").innerHTML = "";
      $("hhHomologyDegreeTabs").innerHTML = "";
      $("hhHomologyDetailOutput").innerHTML = "";
      lastHHResult = null;
      setHHLogsHtml(hhPlaceholderHtml());
      $("quiverDiagram").innerHTML = "";
      $("qwDiagram").innerHTML = "";
      $("quiverTikz").textContent = "";
      $("qwTikz").textContent = "";
      $("metricTable").innerHTML = "";
      $("logOutput").textContent = "";
    }

    function activateTab(name) {
      document.querySelectorAll("[data-tab]").forEach((btn) => {
        btn.classList.toggle("active", btn.dataset.tab === name);
      });
      document.querySelectorAll(".section").forEach((section) => section.classList.remove("active"));
      $(name + "Section").classList.add("active");
    }

  if (typeof document !== "undefined") {
    document.querySelectorAll(".tab").forEach((btn) => {
      btn.addEventListener("click", () => {
        activateTab(btn.dataset.tab);
        if ((btn.dataset.tab === "cohomology" || btn.dataset.tab === "homology") && !$("hhDegreeTabs").innerHTML.trim() && $("hhStatus").textContent !== "computing...") {
          prepareHHDegreeComputation();
        }
      });
    });
    document.querySelectorAll("[data-quiver-mode]").forEach((btn) => {
      btn.addEventListener("click", () => setQuiverMode(btn.dataset.quiverMode));
    });
    $("chainList").addEventListener("click", (event) => {
      const btn = event.target.closest("[data-chain-index]");
      if (!btn) return;
      renderMorseDifferential(Number(btn.dataset.chainIndex));
    });
    $("hhDegreeTabs").addEventListener("click", (event) => {
      const btn = event.target.closest("[data-hh-degree]");
      if (!btn) return;
      computeHHDegreeOnDemand("cohomology", Number(btn.dataset.hhDegree));
    });
    $("hhHomologyDegreeTabs").addEventListener("click", (event) => {
      const btn = event.target.closest("[data-hh-homology-degree]");
      if (!btn) return;
      computeHHDegreeOnDemand("homology", Number(btn.dataset.hhHomologyDegree));
    });
    document.querySelectorAll("[data-copy]").forEach((btn) => {
      btn.addEventListener("click", async () => {
        const target = $(btn.dataset.copy);
        const text = target ? target.textContent : "";
        if (!text) return;
        const original = btn.textContent;
        try {
          if (navigator.clipboard && navigator.clipboard.writeText) await navigator.clipboard.writeText(text);
          else window.prompt("Copy tikzcd source", text);
          btn.textContent = "Copied";
        } catch (err) {
          window.prompt("Copy tikzcd source", text);
          btn.textContent = "Copy";
        }
        window.setTimeout(() => { btn.textContent = original; }, 1200);
      });
    });
    $("sampleBtn").addEventListener("click", loadSample);
    $("basisBtn").addEventListener("click", compute);
    $("hhPanelBtn").addEventListener("click", prepareHHDegreeComputation);
    $("hhHomologyPanelBtn").addEventListener("click", prepareHHDegreeComputation);
    $("clearBtn").addEventListener("click", clearOutput);
    setupCharacteristicInput();
    window.addEventListener("DOMContentLoaded", loadSample);
  } else if (typeof self !== "undefined") {
    self.onmessage = (event) => {
      const { type, id, values, kind, degree } = event.data || {};
      if (type !== "hh-degree") return;
      try {
        const result = computeHHDegreeResult(values, kind, degree);
        self.postMessage({ id, ok: true, result });
      } catch (err) {
        self.postMessage({ id, ok: false, error: err && err.message ? err.message : String(err) });
      }
    };
  }
