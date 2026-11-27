// solve.js — a faster drop-in for makefun-diff 1.0.0.
//
// Same patch for every pair of texts, byte for byte: the common prefix, then
// the common suffix, then Myers's greedy search with make.fun's
// deletion-on-tie rule, then the makefun-diff/1 patch. What changes is how
// the search runs: lines are hash-consed to integer ids once, the search
// keeps only the furthest x reached on each diagonal (one Int32Array row per
// edit depth, in a buffer reused across cases), and the script is rebuilt by
// walking those rows backwards, replaying the same tie-break at each step.
// No path objects, no string comparisons inside the search, no per-case
// allocation of the search table. Node 22, standard library only: no WASM,
// no native code, no network, no reads outside the repository.

const KEEP = '=', DELETE = '-', INSERT = '+';
const CONTEXT = 3;

/** Reused search table: row d starts at d*d and holds 2d+1 furthest-x values (-1: no path). */
let vBuf = new Int32Array(1 << 24);

function ensureV(need) {
  if (vBuf.length >= need) return;
  let size = vBuf.length;
  while (size < need) size *= 2;
  const next = new Int32Array(size);
  next.set(vBuf);
  vBuf = next;
}

/** A text's lines, each with its "\n" (the last one without, when the text does not end in one). */
function tokenize(text) {
  const parts = text.split('\n');
  const last = parts.length - 1;
  const lines = new Array(parts.length);
  for (let i = 0; i < last; i++) lines[i] = parts[i] + '\n';
  if (parts[last] !== '') lines[last] = parts[last]; else lines.length = last;
  return lines;
}

/** Lines as integer ids; equal lines share one id (one map serves both texts). */
function toIds(lines, map) {
  const ids = new Int32Array(lines.length);
  for (let i = 0; i < lines.length; i++) {
    const s = lines[i];
    let id = map.get(s);
    if (id === undefined) { id = map.size; map.set(s, id); }
    ids[i] = id;
  }
  return ids;
}

/**
 * The middle region's edit runs, exactly as makefun-diff finds them.
 * Forward: for each depth d the furthest x on every diagonal, snapped after
 * its snake; the first (d, k) in k order to reach both ends wins. Backward:
 * from that (D, k), each step replays the same deletion-on-tie choice from
 * the row below, so the script is the reference's own. Runs come back in
 * order, neighbours of one kind merged.
 */
function myersRuns(a, b) {
  const n = a.length, m = b.length;
  let x = 0, y = 0; // depth 0: the snake from (0, 0)
  while (x < n && y < m && a[x] === b[y]) { x++; y++; }
  ensureV(1);
  vBuf[0] = x;
  let D = 0, kEnd = 0;
  if (x < n || y < m) {
    search: for (let d = 1; d <= n + m; d++) {
      ensureV((d + 1) * (d + 1));
      const base = d * d, prev = (d - 1) * (d - 1);
      for (let j = 0; j <= 2 * d; j += 2) {
        const k = j - d;
        const xDown = j >= 2 ? vBuf[prev + j - 2] : -1;
        const xRight = j <= 2 * d - 2 ? vBuf[prev + j] : -1;
        const canRemove = xDown !== -1 && xDown < n;
        const canAdd = xRight !== -1 && xRight - 1 - k < m;
        const xd = canRemove ? xDown + 1 : -1;
        const xi = canAdd ? xRight : -1;
        if (xd === -1 && xi === -1) { vBuf[base + j] = -1; continue; }
        let xx = xd >= xi ? xd : xi, yy = xx - k;
        while (xx < n && yy < m && a[xx] === b[yy]) { xx++; yy++; }
        vBuf[base + j] = xx;
        if (xx >= n && yy >= m) { D = d; kEnd = k; break search; }
      }
    }
  }
  const rev = []; // the script, last step first
  let k = kEnd;
  x = n; y = m;
  for (let d = D; d >= 1; d--) {
    const prev = (d - 1) * (d - 1), j = k + d;
    const xDown = j >= 2 ? vBuf[prev + j - 2] : -1;
    const xRight = j <= 2 * d - 2 ? vBuf[prev + j] : -1;
    const canRemove = xDown !== -1 && xDown < n;
    const canAdd = xRight !== -1 && xRight - 1 - k < m;
    const xd = canRemove ? xDown + 1 : -1;
    const xi = canAdd ? xRight : -1;
    const del = xd >= xi, x0 = del ? xd : xi;
    if (x > x0) rev.push({ kind: KEEP, count: x - x0 });
    rev.push({ kind: del ? DELETE : INSERT, count: 1 });
    if (del) { x = xDown; k -= 1; } else { x = xRight; k += 1; }
    y = x - k;
  }
  if (x > 0) rev.push({ kind: KEEP, count: x });
  rev.reverse();
  const runs = [];
  for (const r of rev) {
    const last = runs[runs.length - 1];
    if (last !== undefined && last.kind === r.kind) last.count += r.count;
    else runs.push({ kind: r.kind, count: r.count });
  }
  return runs;
}

/** A line as the patch writes it: its op, the line, a newline, and "%" on a line of its own when it had none. */
function written(op, line) {
  return line.endsWith('\n') ? `${op}${line}` : `${op}${line}\n%\n`;
}

/** make.fun's own patch of input.old into input.new, as one string. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const aLines = tokenize(input.old), bLines = tokenize(input.new);
  const map = new Map();
  const a = toIds(aLines, map), b = toIds(bLines, map);
  const n = a.length, m = b.length;
  let prefix = 0;
  while (prefix < n && prefix < m && a[prefix] === b[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && a[n - 1 - suffix] === b[m - 1 - suffix]) suffix++;
  const runs = [];
  if (prefix > 0) runs.push({ kind: KEEP, count: prefix });
  runs.push(...myersRuns(a.subarray(prefix, n - suffix), b.subarray(prefix, m - suffix)));
  if (suffix > 0) runs.push({ kind: KEEP, count: suffix });
  // Change runs: each a stretch of deletions and insertions between two kept lines.
  const changes = [];
  let o = 0, p = 0, deleted = 0, inserted = 0;
  for (const r of runs) {
    if (r.kind === KEEP) { o += r.count; p += r.count; continue; }
    let c = changes[changes.length - 1];
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === DELETE) { c.dels += r.count; o += r.count; deleted += r.count; }
    else { c.ins += r.count; p += r.count; inserted += r.count; }
  }
  // Hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks[hunks.length - 1];
    const prev = h === undefined ? undefined : h[h.length - 1];
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }
  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0], last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after, newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push(written(KEEP, aLines[at]));
      for (let i = 0; i < c.dels; i++) out.push(written(DELETE, aLines[c.o + i]));
      for (let i = 0; i < c.ins; i++) out.push(written(INSERT, bLines[c.p + i]));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written(KEEP, aLines[at]));
  }
  return out.join('');
}
