import { log } from './config';
import { Expl, Impl, Mode } from './mode';
import { Name } from './names';
import { Abs, App, Import, ElimSigma, Let, ModEntry, Module, Pair, PFst, Pi, PIndex, PName, Proj, ProjType, PropEq, PSnd, Refl, show, SigEntry, Sigma, Signature, Surface, Type, Var, ElimPropEq, Hole, Nat, NatS, NatLit, ElimNat, Fin, FinS, ElimFin, ElimFinN } from './surface';
import { many, Usage, usages, zero } from './usage';
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
const SYM2: string[] = ['->', '**', '!='];

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
  t && t.tag === 'Name' && t.name === x;
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
  if (!t) return null;
  if (t.tag === 'Name' && usages.includes(t.name)) return t.name as Usage;
  if (t.tag === 'Num' && usages.includes(t.num)) return t.num as Usage;
  return null;
};

const lambdaParams = (t: Token): [Usage, Name, Mode, Surface | null][] => {
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
    const ty = exprs(rest, '(');
    return isNames(ns).map(x => [u, x, impl, ty]);
  }
  return serr(`invalid lambda param`);
};
const piParams = (t: Token): [Usage, Name, Mode, Surface][] => {
  if (t.tag === 'Name') return [[many, '_', Expl, expr(t)[0]]];
  if (t.tag === 'List') {
    const impl = t.bracket === '{' ? Impl : Expl;
    const a = t.list;
    if (a.length === 0) return [[many, '_', impl, Var('UnitType')]];
    const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
    if (i === -1) return [[many, '_', impl, expr(t)[0]]];
    let start = 0;
    const n = a[0];
    const pu = usage(n);
    let u: Usage = many;
    if (pu !== null) { u = pu; start = 1 }
    const ns = a.slice(start, i);
    const rest = a.slice(i + 1);
    const ty = exprs(rest, '(');
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

const natSPrim = Abs(many, Expl, 'n', Nat, NatS(Var('n')));
const finSPrim = Abs(zero, Impl, 'n', Nat, Abs(many, Expl, 'f', Fin(Var('n')), FinS(Var('f'))));

const expr = (t: Token): [Surface, boolean] => {
  if (t.tag === 'List')
    return [exprs(t.list, '('), t.bracket === '{'];
  if (t.tag === 'Str') {
    const s = codepoints(t.str).reverse();
    const Cons = Var('Cons');
    const Nil = Var('Nil');
    return [s.reduce((t, n) => App(App(Cons, Expl, NatLit(BigInt(n))), Expl, t), Nil as Surface), false];
  }
  if (t.tag === 'Name') {
    const x = t.name;
    if (x === 'Type') return [Type, false];
    if (x === 'Nat') return [Nat, false];
    if (x === 'Fin') return [Abs(many, Expl, 'n', Nat, Fin(Var('n'))), false];
    if (x === 'S') return [natSPrim, false];
    if (x === 'FS') return [finSPrim, false];
    if (x === 'Refl') return [Refl(null, null), false];
    if (x === '*') return [Var('Unit'), false];
    if (x[0] === '_') return [Hole(x.slice(1)), false];
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
      const n = BigInt(t.num);
      if (n < 0) return serr(`Nat cannot be negative: ${t.num}`);
      return [NatLit(n), false];
    }
  }
  return t;
};

const exprs = (ts: Token[], br: BracketO, fromRepl: boolean = false): Surface => {
  if (br === '{') return serr(`{} cannot be used here`);
  if (ts.length === 0) return Var('UnitType');
  if (ts.length === 1) return expr(ts[0])[0];
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
      ty = exprs(tyts, '(');
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
    const val = exprs(vals, '(');
    if (!found) {
      if (!fromRepl) return serr(`no ; after let`);
      if (ts.slice(i + 1).length > 0) return serr(`no ; after let`);
      return Let(u, name, ty || null, val, null as any);
    }
    const body = exprs(ts.slice(i + 1), '(');
    return Let(u, name, ty || null, val, body);
  }
  if (isName(ts[0], 'import')) {
    if (!ts[1]) return serr(`import needs a term`);
    const [term, i] = expr(ts[1]);
    if (i) return serr(`import term cannot be implicit`);
    let j = 3;
    let imports: string[] | null = null;
    if (!isName(ts[2], ';')) {
      if (!ts[2] || ts[2].tag !== 'List' || ts[2].bracket !== '(') {
        if(!fromRepl)
          return serr(`import needs a list or ;`);
        if (ts.slice(j).length > 0)
          return serr(`expected ; after import list`);
        return Import(term, null, null as any);
      }
      imports = splitTokens(ts[2].list, t => isName(t, ',')).map(ts => {
        if (ts.length === 0) return null;
        if (ts.length > 1) return serr(`import list must only contain variables`);
        if (ts[0].tag !== 'Name') return serr(`import list must only contain variables`);
        return ts[0].name;
      }).filter(Boolean) as string[];
      if (!isName(ts[3], ';')) {
        if(!fromRepl)
          return serr(`expected ; after import list`);
        if (ts.slice(j).length > 0)
          return serr(`expected ; after import list`);
        return Import(term, imports, null as any);
      }
      j++;
    }
    const body = exprs(ts.slice(j), '(');
    return Import(term, imports, body);
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
      lambdaParams(c).forEach(x => args.push(x));
    }
    if (!found) return serr(`. not found after \\ or there was no whitespace after .`);
    const body = exprs(ts.slice(i + 1), '(');
    return args.reduceRight((x, [u, name, mode , ty]) => Abs(u, mode, name, ty, x), body);
  }
  if (isName(ts[0], 'elimSigma')) {
    let j = 1;
    let u = usage(ts[1]);
    if (u) { j = 2 } else { u = many }
    if (!ts[j]) return serr(`elimSigma: not enough arguments`);
    const [motive, impl] = expr(ts[j]);
    if (impl) return serr(`elimSigma motive cannot be implicit`); 
    if (!ts[j + 1]) return serr(`elimSigma: not enough arguments`);
    const [scrut, impl2] = expr(ts[j + 1]);
    if (impl2) return serr(`elimSigma scrutinee cannot be implicit`);
    const cas = exprs(ts.slice(j + 2), '(');
    return ElimSigma(u, motive, scrut, cas);
  }
  if (isName(ts[0], 'elimPropEq')) {
    let j = 1;
    let u = usage(ts[1]);
    if (u) { j = 2 } else { u = many }
    if (!ts[j]) return serr(`elimPropEq: not enough arguments`);
    const [motive, impl] = expr(ts[j]);
    if (impl) return serr(`elimPropEq motive cannot be implicit`); 
    if (!ts[j + 1]) return serr(`elimPropEq: not enough arguments`);
    const [scrut, impl2] = expr(ts[j + 1]);
    if (impl2) return serr(`elimPropEq scrutinee cannot be implicit`);
    const cas = exprs(ts.slice(j + 2), '(');
    return ElimPropEq(u, motive, scrut, cas);
  }
  if (isName(ts[0], 'elimNat')) {
    let j = 1;
    let u = usage(ts[1]);
    if (u) { j = 2 } else { u = many }
    if (!ts[j]) return serr(`elimNat: not enough arguments`);
    const [motive, impl] = expr(ts[j]);
    if (impl) return serr(`elimNat motive cannot be implicit`); 
    if (!ts[j + 1]) return serr(`elimNat: not enough arguments`);
    const [scrut, impl2] = expr(ts[j + 1]);
    if (impl2) return serr(`elimNat scrutinee cannot be implicit`);
    if (!ts[j + 2]) return serr(`elimNat: not enough arguments`);
    const [z, impl3] = expr(ts[j + 2]);
    if (impl3) return serr(`elimNat case Z cannot be implicit`);
    const s = exprs(ts.slice(j + 3), '(');
    return ElimNat(u, motive, scrut, z, s);
  }
  if (isName(ts[0], 'elimFin')) {
    let j = 1;
    let u = usage(ts[1]);
    if (u) { j = 2 } else { u = many }
    if (!ts[j]) return serr(`elimFin: not enough arguments`);
    const [motive, impl] = expr(ts[j]);
    if (impl) return serr(`elimFin motive cannot be implicit`); 
    if (!ts[j + 1]) return serr(`elimFin: not enough arguments`);
    const [scrut, impl2] = expr(ts[j + 1]);
    if (impl2) return serr(`elimFin scrutinee cannot be implicit`);
    if (!ts[j + 2]) return serr(`elimFin: not enough arguments`);
    const [z, impl3] = expr(ts[j + 2]);
    if (impl3) return serr(`elimFin case Z cannot be implicit`);
    const s = exprs(ts.slice(j + 3), '(');
    return ElimFin(u, motive, scrut, z, s);
  }
  if (isName(ts[0], 'elimFinN')) {
    let j = 1;
    let u = usage(ts[1]);
    if (u) { j = 2 } else { u = many }
    if (!ts[j]) return serr(`elimFinN: not enough arguments`);
    const [motive, impl] = expr(ts[j]);
    if (impl) return serr(`elimFinN motive cannot be implicit`); 
    if (!ts[j + 1]) return serr(`elimFinN: not enough arguments`);
    const [scrut, impl2] = expr(ts[j + 1]);
    if (impl2) return serr(`elimFinN scrutinee cannot be implicit`);
    const cs = ts.slice(j + 2).map(x => {
      const [c, impl] = expr(x);
      if (impl) return serr(`elimFinN case cannot be implicit`);
      return c;
    });
    return ElimFinN(u, motive, scrut, cs);
  }
  if (isName(ts[0], 'Fin')) {
    if (ts.length !== 2) return serr(`Fin: needs exactly one argument`);
    const [index, impl] = expr(ts[1]);
    if (impl) return serr(`Fin index cannot be implicit`);
    return Fin(index);
  }
  const i = ts.findIndex(x => isName(x, ':'));
  if (i >= 0) {
    const a = ts.slice(0, i);
    const b = ts.slice(i + 1);
    return Let(many, 'x', exprs(b, '('), exprs(a, '('), Var('x'));
  }
  const j = ts.findIndex(x => isName(x, '->'));
  if (j >= 0) {
    const s = splitTokens(ts, x => isName(x, '->'));
    if (s.length < 2) return serr(`parsing failed with ->`);
    const args: [Usage, Name, Mode, Surface][] = s.slice(0, -1)
      .map(p => p.length === 1 ? piParams(p[0]) : [[many, '_', Expl, exprs(p, '(')] as [Usage, Name, Mode, Surface]])
      .reduce((x, y) => x.concat(y), []);
    const body = exprs(s[s.length - 1], '(');
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
          return expr(h)
      }
      return [exprs(x, '('), false];
    });
    if (args.length === 0) return serr(`empty pair`);
    if (args.length === 1) return serr(`singleton pair`);
    const last1 = args[args.length - 1];
    const last2 = args[args.length - 2];
    const lastitem = Pair(last2[0], last1[0]);
    return args.slice(0, -2).reduceRight((x, [y, _p]) => Pair(y, x), lastitem);
  }
  if (isName(ts[0], 'Refl')) {
    if (ts.length === 1) return Refl(null, null);
    if (ts.length === 2) {
      if (ts[1].tag !== 'List' || ts[1].bracket !== '{') return serr(`invalid Refl`);
      const type = exprs(ts[1].list, '(');
      return Refl(type, null);
    }
    if (ts.length === 3) {
      if (ts[1].tag !== 'List' || ts[1].bracket !== '{') return serr(`invalid Refl`);
      if (ts[2].tag !== 'List' || ts[2].bracket !== '{') return serr(`invalid Refl`);
      const type = exprs(ts[1].list, '(');
      const val = exprs(ts[2].list, '(');
      return Refl(type, val);
    }
    return serr(`invalid Refl`);
  }
  if (isName(ts[0], 'S')) {
    if (ts.length === 1) return natSPrim;
    if (ts.length > 2) return serr(`too many arguments for S`);
    const [term, impl] = expr(ts[1]);
    if (impl) return serr(`arguments for S cannot be implicit`);
    return NatS(term);
  }
  if (isName(ts[0], 'FS')) {
    if (ts.length === 1) return finSPrim;
    if (ts.length === 2) {
      const [term, impl] = expr(ts[1]);
      if (impl) return App(finSPrim, Impl, term);
      return FinS(term);
    }
    if (ts.length === 3) {
      const [n, impl] = expr(ts[1]);
      if (!impl) return serr(`FS index must be implicit`);
      const [term, impl2] = expr(ts[2]);
      if (impl2) return serr(`FS argument cannot be implicit`);
      return App(App(finSPrim, Impl, n), Expl, term);
    }
    return serr(`invalid FS: too many arguments`);
  }
  const js = ts.findIndex(x => isName(x, '**'));
  if (js >= 0) {
    const s = splitTokens(ts, x => isName(x, '**'));
    if (s.length < 2) return serr(`parsing failed with **`);
    const args: [Usage, Name, Mode, Surface][] = s.slice(0, -1)
      .map(p => p.length === 1 ? piParams(p[0]) : [[many, '_', Expl, exprs(p, '(')] as [Usage, Name, Mode, Surface]])
      .reduce((x, y) => x.concat(y), []);
    const body = exprs(s[s.length - 1], '(');
    return args.reduceRight((x, [u, name, mode, ty]) => {
      if (mode.tag !== 'Expl') return serr(`sigma cannot be implicit`);
      return Sigma(u, name, ty, x)
    }, body);
  }
  const jq = ts.findIndex(x => isName(x, '='));
  if (jq >= 0) {
    if (ts.length < 3) return serr(`invalid equality`);
    let rest = ts;
    let type: Surface | null = null;
    if (ts[0].tag === 'List' && ts[0].bracket === '{') {
      rest = ts.slice(1);
      type = exprs(ts[0].list, '(');
    }
    const spl = splitTokens(rest, t => isName(t, '='));
    if (spl.length !== 2) return serr(`invalid equality`);
    const left = exprs(spl[0], '(');
    const right = exprs(spl[1], '(');
    return PropEq(type, left, right);
  }
  const jnq = ts.findIndex(x => isName(x, '!='));
  if (jnq >= 0) {
    if (ts.length < 3) return serr(`invalid inequality`);
    let rest = ts;
    let type: Surface | null = null;
    if (ts[0].tag === 'List' && ts[0].bracket === '{') {
      rest = ts.slice(1);
      type = exprs(ts[0].list, '(');
    }
    const spl = splitTokens(rest, t => isName(t, '!='));
    if (spl.length !== 2) return serr(`invalid inequality`);
    const left = exprs(spl[0], '(');
    const right = exprs(spl[1], '(');
    return Pi(many, Expl, '_', PropEq(type, left, right), Var('Void'));
  }
  if (isName(ts[0], 'sig')) {
    if (ts.length !== 2) return serr(`invalid signature (1)`);
    const b = ts[1];
    if (b.tag !== 'List' || b.bracket !== '{') return serr(`invalid signature (2)`);
    const bs = b.list;
    const spl = splitTokens(bs, t => t.tag === 'Name' && t.name === 'def', true);
    const entries: SigEntry[] = [];
    for (let i = 0; i < spl.length; i++) {
      const c = spl[i];
      if (c.length === 0) continue;
      if (c[0].tag !== 'Name') return serr(`invalid signature, definition does not start with def`);
      if (c[0].name !== 'def') return serr(`invalid signature, definition does not start with def`);
      let x = c[1];
      let j = 2;
      const pu = usage(x);
      let u: Usage = many;
      if (pu !== null) { u = pu; x = c[2]; j = 3 }
      let name = '';
      if (x.tag === 'Name') {
        name = x.name;
      } else return serr(`invalid name for signature def: ${x.tag}`);
      if (name.length === 0) return serr(`signature definition with empty name`);
      const sym = c[j];
      if (!sym) {
        entries.push(SigEntry(u, name, null));
        continue;
      }
      if (sym.tag !== 'Name') return serr(`signature def: after name should be :`);
      if (sym.name === ':') {
        const type = exprs(c.slice(j + 1), '(');
        entries.push(SigEntry(u, name, type));
        continue;
      } else return serr(`def: : or = expected but got ${sym.name}`);
    }
    return Signature(entries);
  }
  if (isName(ts[0], 'mod')) {
    if (ts.length !== 2) return serr(`invalid module (1)`);
    const b = ts[1];
    if (b.tag !== 'List' || b.bracket !== '{') return serr(`invalid module (2)`);
    const bs = b.list;
    const spl = splitTokens(bs, t => t.tag === 'Name' && ['def', 'private'].includes(t.name), true);
    const entries: ModEntry[] = [];
    let private_flag = false;
    for (let i = 0; i < spl.length; i++) {
      const c = spl[i];
      if (c.length === 0) continue;
      if (c[0].tag !== 'Name') return serr(`invalid module, definition does not start with def or private`);
      if (c[0].name !== 'def' && c[0].name !== 'private') return serr(`invalid module, definition does not start with def or private`);
      if (c[0].name === 'private') {
        if (c.length > 1) return serr(`something went wrong in parsing module private definition`);
        private_flag = true;
        continue;
      }
      let private_ = false;
      if (c[0].name === 'def' && private_flag) {
        private_flag = false;
        private_ = true;
      }
      let x = c[1];
      let j = 2;
      const pu = usage(x);
      let u: Usage = many;
      if (pu !== null) { u = pu; x = c[2]; j = 3 }
      let name = '';
      if (x.tag === 'Name') {
        name = x.name;
      } else return serr(`invalid name for module def`);
      if (name.length === 0) return serr(`module definition with empty name`);
      const sym = c[j];
      if (sym.tag !== 'Name') return serr(`module def: after name should be : or =`);
      if (sym.name === '=') {
        const val = exprs(c.slice(j + 1), '(');
        entries.push(ModEntry(private_, u, name, null, val));
        continue;
      } else if (sym.name === ':') {
        const tyts: Token[] = [];
        j++;
        for (; j < c.length; j++) {
          const v = c[j];
          if (v.tag === 'Name' && v.name === '=')
            break;
          else tyts.push(v);
        }
        const type = exprs(tyts, '(');
        const val = exprs(c.slice(j + 1), '(');
        entries.push(ModEntry(private_, u, name, type , val));
        continue;
      } else return serr(`def: : or = expected but got ${sym.name}`);
    }
    return Module(entries);
  }
  const l = ts.findIndex(x => isName(x, '\\'));
  let all: AppPart[] = [];
  if (l >= 0) {
    const first = ts.slice(0, l).map(t => appPart(t));
    const rest = exprs(ts.slice(l), '(');
    all = first.concat([{ tag: 'Expr', expr: rest, impl: false }]);
  } else {
    all = ts.map(t => appPart(t));
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
const appPart = (t: Token): AppPart => {
  if (t.tag === 'Name' && t.name[0] === '.') return { tag: 'Proj', proj: projs(t.name.slice(1)) };
  const [ex, impl] = expr(t);
  return { tag: 'Expr', expr: ex, impl };
};

export const parse = (s: string, fromRepl: boolean = false): Surface => {
  log(() => `parse ${s}`);
  const ts = tokenize(s);
  const ex = exprs(ts, '(', fromRepl);
  if (!fromRepl) log(() => `parsed ${show(ex)}`);
  return ex;
};
