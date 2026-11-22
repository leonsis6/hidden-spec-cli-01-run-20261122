// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { old: string; nw: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** A file's text as lines, with its own line break and whether it ends with one (SPEC.md section 3). */
interface FileState { lines: string[]; br: string; final: boolean; }

function splitFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

const stripTrail = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => /^[ \t]*/.exec(s)?.[0] ?? '';

/** Line equality at one matching tier (SPEC.md section 5). */
function tierEq(tier: number, a: string, b: string): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}

/** Positions where O occurs in lines at tier, at or after `from` (occurrences may overlap). */
function occurrencesAt(O: string[], lines: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  for (let i = from; i + O.length <= lines.length; i++) {
    let ok = true;
    for (let k = 0; k < O.length; k++) {
      if (!tierEq(tier, O[k]!, lines[i + k]!)) { ok = false; break; }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs at or after `from`, with its positions, or null. */
function findTier(O: string[], lines: string[], strict: boolean, from: number): { tier: number; pos: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const pos = occurrencesAt(O, lines, t, from);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** One line of N: its text, and for a context line the index of its line in O. */
interface NLine { text: string; ctx: number | null; }

/** Build the lines that replace a match: a context line is the file's own matched line; at tier 2 every other
 * line of N is re-indented from O's first line's leading whitespace to the file's (SPEC.md section 5). */
function buildReplacement(N: NLine[], O: string[], fileLines: string[], pos: number, tier: number): string[] {
  const out: string[] = [];
  const P = tier === 2 && O.length > 0 ? leadWs(O[0]!) : '';
  const F = tier === 2 && O.length > 0 ? leadWs(fileLines[pos]!) : '';
  for (const nl of N) {
    if (nl.ctx !== null) {
      out.push(fileLines[pos + nl.ctx]!);
      continue;
    }
    const t = nl.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(P)) out.push(F + t.slice(P.length));
    else out.push(t);
  }
  return out;
}

/** One body line of a unified hunk or a V4A chunk, with the patch line it came from. */
interface BodyEntry { kind: 'ctx' | 'old' | 'new' | 'bs'; text: string; raw: string; }

interface Hunk {
  a: number;
  o: string[];
  n: NLine[];
  noEol: boolean; // a `\` line follows the hunk's last context or `+` line
  plusNoEol: boolean; // a `\` line follows the hunk's last `+` line
}

/** A hunk's parsed body: O is its context and `-` lines, N its context and `+` lines (SPEC.md section 6). */
function buildHunk(a: number, entries: BodyEntry[]): Hunk {
  const es = [...entries];
  // Empty lines at the end of a body are not part of it; a `\` line that followed one of them goes with it.
  while (es.length > 0) {
    const last = es[es.length - 1]!;
    if (last.kind === 'ctx' && last.raw === '') { es.pop(); continue; }
    if (last.kind === 'bs' && es.length >= 2) {
      const prev = es[es.length - 2]!;
      if (prev.kind === 'ctx' && prev.raw === '') { es.pop(); continue; }
    }
    break;
  }
  const o: string[] = [];
  const n: NLine[] = [];
  for (const e of es) {
    if (e.kind === 'ctx') { n.push({ text: e.text, ctx: o.length }); o.push(e.text); }
    else if (e.kind === 'old') o.push(e.text);
    else if (e.kind === 'new') n.push({ text: e.text, ctx: null });
  }
  let noEol = false;
  let plusNoEol = false;
  for (let j = es.length - 1; j >= 0; j--) {
    if (es[j]!.kind === 'ctx' || es[j]!.kind === 'new') {
      noEol = es[j + 1]?.kind === 'bs';
      break;
    }
  }
  for (let j = es.length - 1; j >= 0; j--) {
    if (es[j]!.kind === 'new') {
      plusNoEol = es[j + 1]?.kind === 'bs';
      break;
    }
  }
  return { a, o, n, noEol, plusNoEol };
}

/** Apply a section's hunks in order to a file's lines (SPEC.md section 6). */
function applyHunks(f: FileState, hunks: Hunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const h of hunks) {
    if (h.o.length === 0) {
      const insertPos = Math.max(0, Math.min(h.a + d, f.lines.length));
      const added = buildReplacement(h.n, h.o, f.lines, insertPos, 0);
      const atEnd = insertPos === f.lines.length;
      f.lines.splice(insertPos, 0, ...added);
      if (atEnd && added.length > 0) f.final = !h.noEol;
    } else {
      const found = findTier(h.o, f.lines, strict, 0);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.pos[0]!;
      let bestDist = Math.abs(best - target);
      for (const p of found.pos) {
        const dist = Math.abs(p - target);
        if (dist < bestDist) { best = p; bestDist = dist; }
      }
      const toEnd = best + h.o.length === f.lines.length;
      const added = buildReplacement(h.n, h.o, f.lines, best, found.tier);
      f.lines.splice(best, h.o.length, ...added);
      if (toEnd) f.final = !h.noEol;
    }
    d += h.n.length - h.o.length;
  }
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

interface USection {
  oldP: string | undefined; // undefined = unnamed; null = /dev/null
  newP: string | undefined;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

/** One section of a unified diff as one edit (SPEC.md section 6). */
function unifiedSectionEdit(s: USection, strict: boolean): Edit {
  const oldP = s.oldP ?? '';
  const newP = s.newP ?? '';
  const kind = (s.oldP === null || s.create) ? 'create' : (s.newP === null || s.del) ? 'delete' : oldP !== newP ? 'move' : 'change';
  return (tree) => {
    if (kind === 'create') {
      if (!safe(newP)) throw new Fail('unsafe', newP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const plus: string[] = [];
      for (const h of s.hunks) for (const nl of h.n) if (nl.ctx === null) plus.push(nl.text);
      let finalBreak = true;
      for (let hi = s.hunks.length - 1; hi >= 0; hi--) {
        const h = s.hunks[hi]!;
        if (h.n.some((nl) => nl.ctx === null)) { finalBreak = !h.plusNoEol; break; }
      }
      tree.now.set(newP, plus.length === 0 ? '' : plus.join('\n') + (finalBreak ? '\n' : ''));
      return;
    }
    if (kind === 'delete') {
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (kind === 'move') {
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (!safe(newP)) throw new Fail('unsafe', newP);
      const before = tree.get(oldP);
      if (before === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const f = splitFile(before);
      applyHunks(f, s.hunks, strict, oldP);
      tree.now.set(newP, joinFile(f));
      tree.now.set(oldP, null);
      tree.moves.push({ old: oldP, nw: newP });
      return;
    }
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    const f = splitFile(before);
    applyHunks(f, s.hunks, strict, oldP);
    tree.now.set(oldP, joinFile(f));
  };
}

/** Read a patch in the unified format (SPEC.md section 6). */
function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let pairOld: string | null | undefined;
  let pairNew: string | null | undefined;
  let renOld: string | undefined;
  let renNew: string | undefined;
  let gitOld: string | undefined;
  let gitNew: string | undefined;
  let hunk: { a: number; entries: BodyEntry[] } | null = null;
  let inBody = false;
  let seenHunk = false;

  const hunkHeader = (l: string): number | null => {
    const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(l);
    return m ? parseInt(m[1]!, 10) : null;
  };
  const diffGit = (l: string): [string, string] | null => {
    const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(l);
    return m ? [m[1]!, m[2]!] : null;
  };
  const headPath = (l: string): string => {
    let t = l.slice(4);
    const tab = t.indexOf('\t');
    if (tab >= 0) t = t.slice(0, tab);
    return t.trim();
  };
  const stripAB = (p: string): string => (p.startsWith('a/') || p.startsWith('b/')) ? p.slice(2) : p;
  const normPath = (p: string): string | null => (p === '/dev/null' ? null : stripAB(p));
  const finishHunk = (): void => {
    if (cur !== null && hunk !== null) cur.hunks.push(buildHunk(hunk.a, hunk.entries));
    hunk = null;
    inBody = false;
  };
  const finishSection = (): void => {
    if (cur === null) return;
    cur.oldP = pairOld !== undefined ? pairOld : renOld !== undefined ? renOld : gitOld;
    cur.newP = pairNew !== undefined ? pairNew : renNew !== undefined ? renNew : gitNew;
    cur = null;
  };
  const startSection = (gOld: string | undefined, gNew: string | undefined): void => {
    finishHunk();
    finishSection();
    cur = { oldP: undefined, newP: undefined, create: false, del: false, hunks: [] };
    pairOld = undefined; pairNew = undefined; renOld = undefined; renNew = undefined;
    gitOld = gOld; gitNew = gNew;
    seenHunk = false;
    sections.push(cur);
  };
  const bodyEntry = (l: string): BodyEntry => (
    l === '' ? { kind: 'ctx', text: '', raw: l }
      : l.startsWith(' ') ? { kind: 'ctx', text: l.slice(1), raw: l }
      : l.startsWith('-') ? { kind: 'old', text: l.slice(1), raw: l }
      : l.startsWith('+') ? { kind: 'new', text: l.slice(1), raw: l }
      : { kind: 'bs', text: l.slice(1), raw: l }
  );

  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!;
    if (inBody) {
      if (l.startsWith('diff --git ')) {
        const g = diffGit(l);
        if (g === null) throw new Exit2(`error: parse ${i + 1}`);
        startSection(g[0], g[1]);
        continue;
      }
      if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        startSection(undefined, undefined);
        pairOld = normPath(headPath(l));
        pairNew = normPath(headPath(lines[i + 1]!));
        i++;
        continue;
      }
      if (l.startsWith('@@')) {
        const a = hunkHeader(l);
        if (a === null) throw new Exit2(`error: parse ${i + 1}`);
        finishHunk();
        hunk = { a, entries: [] };
        inBody = true;
        seenHunk = true;
        continue;
      }
      if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
        hunk!.entries.push(bodyEntry(l));
        continue;
      }
      finishHunk();
    }
    if (cur === null) {
      if (l.startsWith('diff --git ')) {
        const g = diffGit(l);
        if (g === null) throw new Exit2(`error: parse ${i + 1}`);
        startSection(g[0], g[1]);
        continue;
      }
      if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        startSection(undefined, undefined);
        pairOld = normPath(headPath(l));
        pairNew = normPath(headPath(lines[i + 1]!));
        i++;
        continue;
      }
      if (l.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
      continue;
    }
    if (l.startsWith('diff --git ')) {
      const g = diffGit(l);
      if (g === null) throw new Exit2(`error: parse ${i + 1}`);
      startSection(g[0], g[1]);
      continue;
    }
    if (l.startsWith('--- ')) {
      if ((lines[i + 1] ?? '').startsWith('+++ ')) {
        if (pairOld === undefined && pairNew === undefined && !seenHunk) {
          pairOld = normPath(headPath(l));
          pairNew = normPath(headPath(lines[i + 1]!));
          i++;
          continue;
        }
        startSection(undefined, undefined);
        pairOld = normPath(headPath(l));
        pairNew = normPath(headPath(lines[i + 1]!));
        i++;
        continue;
      }
      if (!seenHunk) throw new Exit2(`error: parse ${i + 2}`);
      continue;
    }
    if (l.startsWith('@@')) {
      const a = hunkHeader(l);
      if (a === null) throw new Exit2(`error: parse ${i + 1}`);
      hunk = { a, entries: [] };
      inBody = true;
      seenHunk = true;
      continue;
    }
    if (!seenHunk) {
      if (l.startsWith('rename from ')) { renOld = l.slice('rename from '.length).trim(); continue; }
      if (l.startsWith('rename to ')) { renNew = l.slice('rename to '.length).trim(); continue; }
      if (l.startsWith('new file mode')) { cur.create = true; continue; }
      if (l.startsWith('deleted file mode')) { cur.del = true; continue; }
    }
  }
  finishHunk();
  finishSection();
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

/** Read a patch in the SEARCH/REPLACE format (SPEC.md section 7). */
function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  interface Block { path: string; oldLines: string[]; newLines: string[]; }
  const blocks: Block[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') { i++; continue; }
    const searchIdx = i;
    let path: string | null = null;
    for (let j = searchIdx - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    let sep = -1;
    for (let j = searchIdx + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') { sep = j; break; }
      if (t === '>>>>>>> REPLACE') break;
    }
    if (sep < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    let end = -1;
    for (let j = sep + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') { end = j; break; }
    }
    if (end < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    blocks.push({ path, oldLines: lines.slice(searchIdx + 1, sep), newLines: lines.slice(sep + 1, end) });
    prevPath = path;
    prevEnd = end;
    i = end + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const f = splitFile(before);
    const found = findTier(b.oldLines, f.lines, strict, 0);
    if (found === null) throw new Fail('no-match', b.path);
    if (found.pos.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.pos[0]!;
    const added = buildReplacement(b.newLines.map((t) => ({ text: t, ctx: null })), b.oldLines, f.lines, pos, found.tier);
    f.lines.splice(pos, b.oldLines.length, ...added);
    tree.now.set(b.path, joinFile(f));
  });
}

interface VChunk {
  anchor: string | null;
  eof: boolean;
  o: string[];
  n: NLine[];
}

/** Read a patch in the V4A format (SPEC.md section 8). */
function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);

  const sectionStart = (l: string): 'add' | 'delete' | 'update' | null => (
    l.startsWith('*** Add File: ') ? 'add'
      : l.startsWith('*** Delete File: ') ? 'delete'
      : l.startsWith('*** Update File: ') ? 'update' : null
  );
  const sectionPath = (l: string, kind: 'add' | 'delete' | 'update'): string => (
    l.slice(`*** ${kind === 'add' ? 'Add' : kind === 'delete' ? 'Delete' : 'Update'} File: `.length).trim()
  );

  const edits: Edit[] = [];
  let j = first + 1;
  while (j < last) {
    const l = lines[j]!;
    if (blank(l)) { j++; continue; }
    const kind = sectionStart(l);
    if (kind === null) throw new Exit2(`error: parse ${j + 1}`);
    const path = sectionPath(l, kind);
    const headLine = j + 1;
    j++;
    // Collect this section's raw lines (until the next section start or *** End Patch).
    const raw: string[] = [];
    while (j < last) {
      const x = lines[j]!;
      if (sectionStart(x) !== null) break;
      raw.push(x);
      j++;
    }
    if (kind === 'add') {
      const body = [...raw];
      while (body.length > 0 && blank(body[body.length - 1]!)) body.pop();
      const addLines: string[] = [];
      for (let k = 0; k < body.length; k++) {
        const x = body[k]!;
        if (x.startsWith('+')) addLines.push(x.slice(1));
        else if (x === '') addLines.push('');
        else throw new Exit2(`error: parse ${headLine + 1 + k}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, addLines.length === 0 ? '' : addLines.join('\n') + '\n');
      });
      continue;
    }
    if (kind === 'delete') {
      for (let k = 0; k < raw.length; k++) {
        if (!blank(raw[k]!)) throw new Exit2(`error: parse ${headLine + 1 + k}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
      continue;
    }
    // Update File section.
    let moveTo: string | null = null;
    let k = 0;
    if (k < raw.length && raw[k]!.startsWith('*** Move to: ')) {
      moveTo = raw[k]!.slice('*** Move to: '.length).trim();
      k++;
    }
    const chunks: VChunk[] = [];
    let cur: { anchor: string | null; eof: boolean; entries: BodyEntry[] } | null = null;
    let seenChunk = false;
    const closeChunk = (dropTrailing: boolean): void => {
      if (cur === null) return;
      const es = [...cur.entries];
      // Blank lines at the end of a section are not part of it; blanks before an
      // `*** End of File` line or a new `@@` chunk belong to the chunk.
      if (dropTrailing) while (es.length > 0 && blank(es[es.length - 1]!.raw)) es.pop();
      const o: string[] = [];
      const n: NLine[] = [];
      for (const e of es) {
        if (e.kind === 'ctx') { n.push({ text: e.text, ctx: o.length }); o.push(e.text); }
        else if (e.kind === 'old') o.push(e.text);
        else if (e.kind === 'new') n.push({ text: e.text, ctx: null });
      }
      chunks.push({ anchor: cur.anchor, eof: cur.eof, o, n });
      cur = null;
    };
    while (k < raw.length) {
      const x = raw[k]!;
      const lineNo = headLine + 1 + k;
      if (x.trim() === '*** End of File') {
        if (cur === null) throw new Exit2(`error: parse ${lineNo}`);
        cur.eof = true;
        closeChunk(false);
        k++;
        continue;
      }
      if (x.startsWith('@@')) {
        closeChunk(false);
        const anchor = x.slice(2).trim();
        cur = { anchor: anchor === '' ? null : anchor, eof: false, entries: [] };
        seenChunk = true;
        k++;
        continue;
      }
      if (x.startsWith('*** ')) throw new Exit2(`error: parse ${lineNo}`);
      if (blank(x)) {
        if (cur !== null) cur.entries.push({ kind: 'ctx', text: x === '' ? '' : x.slice(1), raw: x });
        else if (!seenChunk) {
          cur = { anchor: null, eof: false, entries: [{ kind: 'ctx', text: x === '' ? '' : x.slice(1), raw: x }] };
          seenChunk = true;
        }
        k++;
        continue;
      }
      if (x.startsWith(' ') || x.startsWith('-') || x.startsWith('+')) {
        if (cur === null) {
          if (seenChunk) throw new Exit2(`error: parse ${lineNo}`);
          cur = { anchor: null, eof: false, entries: [] };
          seenChunk = true;
        }
        cur.entries.push(
          x.startsWith(' ') ? { kind: 'ctx', text: x.slice(1), raw: x }
            : x.startsWith('-') ? { kind: 'old', text: x.slice(1), raw: x }
            : { kind: 'new', text: x.slice(1), raw: x },
        );
        k++;
        continue;
      }
      throw new Exit2(`error: parse ${lineNo}`);
    }
    closeChunk(true);
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${headLine}`);
    edits.push((tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
      const before = tree.get(path);
      if (before === null) throw new Fail('missing', path);
      if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
      const f = splitFile(before);
      let cursor = 0;
      for (const chunk of chunks) {
        if (chunk.anchor !== null) {
          let foundIdx = -1;
          const tiers = strict ? [0] : [0, 1, 2];
          for (const t of tiers) {
            for (let q = cursor; q < f.lines.length; q++) {
              if (tierEq(t, chunk.anchor, f.lines[q]!)) { foundIdx = q; break; }
            }
            if (foundIdx >= 0) break;
          }
          if (foundIdx < 0) throw new Fail('no-match', path);
          cursor = foundIdx + 1;
        }
        if (chunk.o.length === 0) {
          const insertPos = chunk.eof ? f.lines.length : cursor;
          const added = buildReplacement(chunk.n, chunk.o, f.lines, insertPos, 0);
          f.lines.splice(insertPos, 0, ...added);
          cursor = insertPos + added.length;
          continue;
        }
        if (chunk.eof) {
          const want = f.lines.length - chunk.o.length;
          if (want < cursor) throw new Fail('no-match', path);
          let tier = -1;
          const tiers = strict ? [0] : [0, 1, 2];
          for (const t of tiers) {
            let ok = true;
            for (let m = 0; m < chunk.o.length; m++) {
              if (!tierEq(t, chunk.o[m]!, f.lines[want + m]!)) { ok = false; break; }
            }
            if (ok) { tier = t; break; }
          }
          if (tier < 0) throw new Fail('no-match', path);
          const added = buildReplacement(chunk.n, chunk.o, f.lines, want, tier);
          f.lines.splice(want, chunk.o.length, ...added);
          cursor = want + added.length;
          continue;
        }
        const found = findTier(chunk.o, f.lines, strict, cursor);
        if (found === null) throw new Fail('no-match', path);
        const pos = found.pos[0]!;
        const added = buildReplacement(chunk.n, chunk.o, f.lines, pos, found.tier);
        f.lines.splice(pos, chunk.o.length, ...added);
        cursor = pos + added.length;
      }
      const out = joinFile(f);
      if (moveTo !== null) {
        tree.now.set(moveTo, out);
        tree.now.set(path, null);
        tree.moves.push({ old: path, nw: moveTo });
      } else {
        tree.now.set(path, out);
      }
    });
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = kind === 'json' ? jsonEdits(text, lines)
      : kind === 'unified' ? unifiedEdits(lines, strict)
      : kind === 'search-replace' ? searchReplaceEdits(lines, strict)
      : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  interface Row { key: string; text: string; }
  const rows: Row[] = [];
  const moved = new Set<string>();
  for (const m of tree.moves) {
    const wasOld = tree.original(m.old);
    const nowOld = tree.get(m.old);
    const wasNew = tree.original(m.nw);
    const nowNew = tree.get(m.nw);
    if (wasOld !== null && nowOld === null && wasNew === null && nowNew !== null) {
      rows.push({ key: m.nw, text: `R ${m.old} -> ${m.nw}` });
      moved.add(m.old);
      moved.add(m.nw);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (moved.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const now = tree.now.get(p)!;
      if (tree.original(p) === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  const out = rows.map((r) => r.text);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
