import { log } from './config';
import { Expl, Impl, Mode } from './mode';
import { Name } from './names';
import { Abs, App, IndSigma, Let, Pair, PFst, Pi, PIndex, PName, Proj, ProjType, PSnd, show, Sigma, Surface, Type, Var } from './surface';
import { many, Usage, usages } from './usage';
import { serr } from './utils/utils';

type BracketO = '(' | '{'
type Bracket = BracketO | ')' | '}';
const matchingBracket = (c: Bracket): Bracket => {
  if(c === '(') return ')';
  if(c === ')') return '(';
  if(c === '{') return '}';
  if(c === '}') return '{';
  return serr(`invalid bracket: ${c}`);
};

type Token
  = { tag: 'Name', name: string }
  | { tag: 'Num', num: string }
  | { tag: 'List', list: Token[], bracket: BracketO }
  | { tag: 'Str', str: string };
const TName = (name: string): Token => ({ tag: 'Name', name });
const TNum = (num: string): Token => ({ tag: 'Num', num });
const TList = (list: Token[], bracket: BracketO): Token => ({ tag: 'List', list, bracket });
const TStr = (str: string): Token => ({ tag: 'Str', str });

const SYM1: string[] = ['\\', ':', '=', ';', '*', ','];
const SYM2: string[] = ['->', '**'];

const START = 0;
const NAME = 1;
const COMMENT = 2;
const NUMBER = 3;
const STRING = 4;
const tokenize = (sc: string): Token[] => {
  let state = START;
  let r: Token[] = [];
  let t = '';
  let esc = false;
  let p: Token[][] = [], b: BracketO[] = [];
  for (let i = 0, l = sc.length; i <= l; i++) {
    const c = sc[i] || ' ';
    const next = sc[i + 1] || '';
    if (state === START) {
      if (SYM2.indexOf(c + next) >= 0) r.push(TName(c + next)), i++;
      else if (SYM1.indexOf(c) >= 0) r.push(TName(c));
      else if (c === '"') state = STRING;
      else if (c === '.' && !/[\.\%\_a-z]/i.test(next)) r.push(TName('.'));
      else if (c + next === '--') i++, state = COMMENT;
      else if (/[\-\.\?\@\#\%\_a-z]/i.test(c)) t += c, state = NAME;
      else if (/[0-9]/.test(c)) t += c, state = NUMBER;
      else if(c === '(' || c === '{') b.push(c), p.push(r), r = [];
      else if(c === ')' || c === '}') {
        if(b.length === 0) return serr(`unmatched bracket: ${c}`);
        const br = b.pop() as BracketO;
        if(matchingBracket(br) !== c) return serr(`unmatched bracket: ${br} and ${c}`);
        const a: Token[] = p.pop() as Token[];
        a.push(TList(r, br));
        r = a;
      }
      else if (/\s/.test(c)) continue;
      else return serr(`invalid char ${c} in tokenize`);
    } else if (state === NAME) {
      if (!(/[a-z0-9\-\_\/]/i.test(c) || (c === '.' && /[a-z0-9\_]/i.test(next)))) {
        r.push(TName(t));
        t = '', i--, state = START;
      } else t += c;
    } else if (state === NUMBER) {
      if (!/[0-9a-z\+\-]/i.test(c)) {
        r.push(TNum(t));
        t = '', i--, state = START;
      } else t += c;
    } else if (state === COMMENT) {
      if (c === '\n') state = START;
    } else if (state === STRING) {
      if (c === '\\') esc = true;
      else if (esc) t += c, esc = false;
      else if (c === '"') {
        r.push(TStr(t));
        t = '', state = START;
      } else t += c;
    }
  }
  if (b.length > 0) return serr(`unclosed brackets: ${b.join(' ')}`);
  if (state !== START && state !== COMMENT)
    return serr('invalid tokenize end state');
  if (esc) return serr(`escape is true after tokenize`);
  return r;
};

const isName = (t: Token, x: Name): boolean =>
  t.tag === 'Name' && t.name === x;
const isNames = (t: Token[]): Name[] =>
  t.map(x => {
    if (x.tag !== 'Name') return serr(`expected name`);
    return x.name;
  });

const splitTokens = (a: Token[], fn: (t: Token) => boolean, keepSymbol: boolean = false): Token[][] => {
  const r: Token[][] = [];
  let t: Token[] = [];
  for (let i = 0, l = a.length; i < l; i++) {
    const c = a[i];
    if (fn(c)) {
      r.push(t);
      t = keepSymbol ? [c] : [];
    } else t.push(c);
  }
  r.push(t);
  return r;
};

const usage = (t: Token): Usage | null => {
  if (t.tag === 'Name' && usages.includes(t.name)) return t.name as Usage;
  if (t.tag === 'Num' && usages.includes(t.num)) return t.num as Usage;
  return null;
};

const lambdaParams = (t: Token, fromRepl: boolean): [Usage, Name, Mode, Surface | null][] => {
  if (t.tag === 'Name') return [[many, t.name, Expl, null]];
  if (t.tag === 'List') {
    const impl = t.bracket === '{' ? Impl : Expl;
    const a = t.list;
    if (a.length === 0) return [[many, '_', impl, Var('UnitType')]];
    const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
    if (i === -1) return isNames(a).map(x => [many, x, impl, null]);
    let start = 0;
    const n = a[0];
    const pu = usage(n);
    let u: Usage = many;
    if (pu !== null) { u = pu; start = 1 }
    const ns = a.slice(start, i);
    const rest = a.slice(i + 1);
    const ty = exprs(rest, '(', fromRepl);
    return isNames(ns).map(x => [u, x, impl, ty]);
  }
  return serr(`invalid lambda param`);
};
const piParams = (t: Token, fromRepl: boolean): [Usage, Name, Mode, Surface][] => {
  if (t.tag === 'Name') return [[many, '_', Expl, expr(t, fromRepl)[0]]];
  if (t.tag === 'List') {
    const impl = t.bracket === '{' ? Impl : Expl;
    const a = t.list;
    if (a.length === 0) return [[many, '_', impl, Var('UnitType')]];
    const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
    if (i === -1) return [[many, '_', impl, expr(t, fromRepl)[0]]];
    let start = 0;
    const n = a[0];
    const pu = usage(n);
    let u: Usage = many;
    if (pu !== null) { u = pu; start = 1 }
    const ns = a.slice(start, i);
    const rest = a.slice(i + 1);
    const ty = exprs(rest, '(', fromRepl);
    return isNames(ns).map(x => [u, x, impl, ty]);
  }
  return serr(`invalid pi param`);
};

const codepoints = (s: string): number[] => {
  const chars: number[] = [];
  for (let i = 0; i < s.length; i++) {
    const c1 = s.charCodeAt(i);
    if (c1 >= 0xD800 && c1 < 0xDC00 && i + 1 < s.length) {
      const c2 = s.charCodeAt(i + 1);
      if (c2 >= 0xDC00 && c2 < 0xE000) {
        chars.push(0x10000 + ((c1 - 0xD800) << 10) + (c2 - 0xDC00));
        i++;
        continue;
      }
    }
    chars.push(c1);
  }
  return chars;
};

const numToNat = (n: number, orig: string): Surface => {
  if (isNaN(n)) return serr(`invalid nat number: ${orig}`);
  const s = Var('S');
  let c: Surface = Var('Z');
  for (let i = 0; i < n; i++) c = App(s, Expl, c);
  return c;
};

const proj = (p: string): ProjType => {
  if (p === '_1') return PFst;
  if (p === '_2') return PSnd;
  const i = +p;
  if (!isNaN(i)) {
    if (i < 0 || Math.floor(i) !== i) return serr(`invalid projection: ${p}`);
    return PIndex(i);
  }
  if (/[a-z]/i.test(p[0])) return PName(p);
  return serr(`invalid projection: ${p}`);
};
const projs = (ps: string): ProjType[] => {
  const parts = ps.split('.');
  return parts.map(proj);
};

const expr = (t: Token, fromRepl: boolean): [Surface, boolean] => {
  if (t.tag === 'List')
    return [exprs(t.list, '(', fromRepl), t.bracket === '{'];
  if (t.tag === 'Str') {
    const s = codepoints(t.str).reverse();
    const Cons = Var('Cons');
    const Nil = Var('Nil');
    return [s.reduce((t, n) => App(App(Cons, Expl, numToNat(n, `codepoint: ${n}`)), Expl, t), Nil as Surface), false];
  }
  if (t.tag === 'Name') {
    const x = t.name;
    if (x === 'Type') return [Type, false];
    if (x === '*') return [Var('Unit'), false];
    if (/[a-z]/i.test(x[0])) {
      if (x.indexOf('.') >= 0) {
        const parts = x.split('.');
        const first = parts[0];
        const ps = projs(parts.slice(1).join('.'));
        return [ps.reduce((t, p) => Proj(t, p), Var(first) as Surface), false];
      } else return [Var(x), false];
    }
    return serr(`invalid name: ${x}`);
  }
  if (t.tag === 'Num') {
    if (t.num.endsWith('b')) {
      const n = +t.num.slice(0, -1);
      if (isNaN(n)) return serr(`invalid number: ${t.num}`);
      const s0 = Var('B0');
      const s1 = Var('B1');
      let c: Surface = Var('BE');
      const s = n.toString(2);
      for (let i = 0; i < s.length; i++) c = App(s[i] === '0' ? s0 : s1, Expl, c);
      return [c, false];
    } else if (t.num.endsWith('f')) {
      const n = +t.num.slice(0, -1);
      if (isNaN(n)) return serr(`invalid number: ${t.num}`);
      const s = Var('FS');
      let c: Surface = Var('FZ');
      for (let i = 0; i < n; i++) c = App(s, Expl, c);
      return [c, false];
    } else if (t.num.endsWith('n')) {
      return [numToNat(+t.num.slice(0, -1), t.num), false];
    } else {
      return [numToNat(+t.num, t.num), false];
    }
  }
  return t;
};

const exprs = (ts: Token[], br: BracketO, fromRepl: boolean): Surface => {
  if (br === '{') return serr(`{} cannot be used here`);
  if (ts.length === 0) return Var('UnitType');
  if (ts.length === 1) return expr(ts[0], fromRepl)[0];
  if (isName(ts[0], 'let')) {
    let x = ts[1];
    let j = 2;
    const pu = usage(x);
    let u: Usage = many;
    if (pu !== null) { u = pu; x = ts[2]; j = 3 }
    let name = 'ERROR';
    if (x.tag === 'Name') {
      name = x.name;
    } else if (x.tag === 'List' && x.bracket === '{') {
      const a = x.list;
      if (a.length !== 1) return serr(`invalid name for let`);
      const h = a[0];
      if (h.tag !== 'Name') return serr(`invalid name for let`);
      name = h.name;
    } else return serr(`invalid name for let`);
    let ty: Surface | null = null;
    if (isName(ts[j], ':')) {
      const tyts: Token[] = [];
      j++;
      for (; j < ts.length; j++) {
        const v = ts[j];
        if (v.tag === 'Name' && v.name === '=')
          break;
        else tyts.push(v);
      }
      ty = exprs(tyts, '(', fromRepl);
    }
    if (!isName(ts[j], '=')) return serr(`no = after name in let`);
    const vals: Token[] = [];
    let found = false;
    let i = j + 1;
    for (; i < ts.length; i++) {
      const c = ts[i];
      if (c.tag === 'Name' && c.name === ';') {
        found = true;
        break;
      }
      vals.push(c);
    }
    if (vals.length === 0) return serr(`empty val in let`);
    const val = exprs(vals, '(', fromRepl);
    if (!found) {
      if (!fromRepl) return serr(`no ; after let`);
      return Let(u, name, ty || null, val, null as any);
    }
    const body = exprs(ts.slice(i + 1), '(', fromRepl);
    return Let(u, name, ty || null, val, body);
  }
  const i = ts.findIndex(x => isName(x, ':'));
  if (i >= 0) {
    const a = ts.slice(0, i);
    const b = ts.slice(i + 1);
    return Let(many, 'x', exprs(b, '(', fromRepl), exprs(a, '(', fromRepl), Var('x'));
  }
  if (isName(ts[0], '\\')) {
    const args: [Usage, Name, Mode, Surface | null][] = [];
    let found = false;
    let i = 1;
    for (; i < ts.length; i++) {
      const c = ts[i];
      if (isName(c, '.')) {
        found = true;
        break;
      }
      lambdaParams(c, fromRepl).forEach(x => args.push(x));
    }
    if (!found) return serr(`. not found after \\ or there was no whitespace after .`);
    const body = exprs(ts.slice(i + 1), '(', fromRepl);
    return args.reduceRight((x, [u, name, mode , ty]) => Abs(u, mode, name, ty, x), body);
  }
  if (isName(ts[0], 'indSigma')) {
    let j = 1;
    let u = usage(ts[1]);
    if (u) { j = 2 } else { u = many }
    let motive: Surface | null = null;
    let scrut: Surface;
    const [maybemotive, impl] = expr(ts[j], fromRepl);
    if (impl) {
      motive = maybemotive;
      const [scrut2, impl2] = expr(ts[j + 1], fromRepl);
      if (impl2) return serr(`indSigma scrutinee cannot be implicit`);
      scrut = scrut2;
      j++;
    } else {
      scrut = maybemotive;
    }
    const cas = exprs(ts.slice(j + 1), '(', fromRepl);
    return IndSigma(u, motive, scrut, cas);
  }
  const j = ts.findIndex(x => isName(x, '->'));
  if (j >= 0) {
    const s = splitTokens(ts, x => isName(x, '->'));
    if (s.length < 2) return serr(`parsing failed with ->`);
    const args: [Usage, Name, Mode, Surface][] = s.slice(0, -1)
      .map(p => p.length === 1 ? piParams(p[0], fromRepl) : [[many, '_', Expl, exprs(p, '(', fromRepl)] as [Usage, Name, Mode, Surface]])
      .reduce((x, y) => x.concat(y), []);
    const body = exprs(s[s.length - 1], '(', fromRepl);
    return args.reduceRight((x, [u, name, impl, ty]) => Pi(u, impl, name, ty, x), body);
  }
  const jp = ts.findIndex(x => isName(x, ','));
  if (jp >= 0) {
    const s = splitTokens(ts, x => isName(x, ','));
    if (s.length < 2) return serr(`parsing failed with ,`);
    const args: [Surface, boolean][] = s.map(x => {
      if (x.length === 1) {
        const h = x[0];
        if (h.tag === 'List' && h.bracket === '{')
          return expr(h, fromRepl)
      }
      return [exprs(x, '(', fromRepl), false];
    });
    if (args.length === 0) return serr(`empty pair`);
    if (args.length === 1) return serr(`singleton pair`);
    const last1 = args[args.length - 1];
    const last2 = args[args.length - 2];
    const lastitem = Pair(last2[0], last1[0]);
    return args.slice(0, -2).reduceRight((x, [y, _p]) => Pair(y, x), lastitem);
  }
  const js = ts.findIndex(x => isName(x, '**'));
  if (js >= 0) {
    const s = splitTokens(ts, x => isName(x, '**'));
    if (s.length < 2) return serr(`parsing failed with **`);
    const args: [Usage, Name, Mode, Surface][] = s.slice(0, -1)
      .map(p => p.length === 1 ? piParams(p[0], fromRepl) : [[many, '_', Expl, exprs(p, '(', fromRepl)] as [Usage, Name, Mode, Surface]])
      .reduce((x, y) => x.concat(y), []);
    const body = exprs(s[s.length - 1], '(', fromRepl);
    return args.reduceRight((x, [u, name, mode, ty]) => {
      if (mode.tag !== 'Expl') return serr(`sigma cannot be implicit`);
      return Sigma(u, name, ty, x)
    }, body);
  }
  const l = ts.findIndex(x => isName(x, '\\'));
  let all: AppPart[] = [];
  if (l >= 0) {
    const first = ts.slice(0, l).map(t => appPart(t, fromRepl));
    const rest = exprs(ts.slice(l), '(', fromRepl);
    all = first.concat([{ tag: 'Expr', expr: rest, impl: false }]);
  } else {
    all = ts.map(t => appPart(t, fromRepl));
  }
  if (all.length === 0) return serr(`empty application`);
  const hd = all[0];
  if (hd.tag === 'Expr' && hd.impl) return serr(`in application function cannot be between {}`);
  if (hd.tag === 'Proj') return serr(`in application function cannot be a projection`);
  return all.slice(1).reduce((x, a) => {
    if (a.tag === 'Proj') return a.proj.reduce((t, p) => Proj(t, p), x as Surface);
    return App(x, a.impl ? Impl : Expl, a.expr)
  }, hd.expr);
};

type AppPart = { tag: 'Expr', expr: Surface, impl: boolean } | { tag: 'Proj', proj: ProjType[] };
const appPart = (t: Token, fromRepl: boolean): AppPart => {
  if (t.tag === 'Name' && t.name[0] === '.') return { tag: 'Proj', proj: projs(t.name.slice(1)) };
  const [ex, impl] = expr(t, fromRepl);
  return { tag: 'Expr', expr: ex, impl };
};

export const parse = (s: string, fromRepl: boolean = false): Surface => {
  log(() => `parse ${s}`);
  const ts = tokenize(s);
  const ex = exprs(ts, '(', fromRepl);
  if (!fromRepl) log(() => `parsed ${show(ex)}`);
  return ex;
};
