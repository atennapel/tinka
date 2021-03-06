import { log } from './config';
import { Erasure, Expl, Impl, Mode } from './mode';
import { Name } from './names';
import { Abs, App, Let, Pair, PFst, Pi, PIndex, PName, Proj, ProjType, PSnd, show, Sigma, Surface, Var, Hole, Ann, Type, Import, Rigid, SymbolLit, Global } from './surface';
import { serr } from './utils/utils';

type BracketO = '(' | '{' | '['
type Bracket = BracketO | ')' | '}' | ']';
const matchingBracket = (c: Bracket): Bracket => {
  if(c === '(') return ')';
  if(c === ')') return '(';
  if(c === '{') return '}';
  if(c === '}') return '{';
  if(c === '[') return ']';
  if(c === ']') return '[';
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

const SYM1: string[] = ['\\', ':', '=', ';', '*', ',', '#', '&', '%', 'λ', '×', '→', '★', '~'];
const SYM2: string[] = ['->', '**'];

const createTName = (x: string): Token => {
  if (x === 'λ') return TName('\\');
  if (x === '×') return TName('**');
  if (x === '→') return TName('->');
  if (x === '★') return TName('*');
  return TName(x);
};

const START = 0;
const NAME = 1;
const COMMENT = 2;
const NUMBER = 3;
const STRING = 4;
const BLOCKCOMMENT = 5;
const tokenize = (sc: string): Token[] => {
  let state = START;
  let r: Token[] = [];
  let t = '';
  let esc = false;
  let commentlevel = 0;
  let p: Token[][] = [], b: BracketO[] = [];
  for (let i = 0, l = sc.length; i <= l; i++) {
    const c = sc[i] || ' ';
    const next = sc[i + 1] || '';
    const next2 = sc[i + 2] || '';
    if (state === START) {
      if (c + next === '--') i++, state = COMMENT;
      else if (c + next + next2 === '{--') i += 2, commentlevel++, state = BLOCKCOMMENT;
      else if (SYM2.indexOf(c + next) >= 0) r.push(createTName(c + next)), i++;
      else if (SYM1.indexOf(c) >= 0) r.push(createTName(c));
      else if (c === '"') state = STRING;
      else if (c === '.' && !/[\.\%\_a-z]/i.test(next)) r.push(TName('.'));
      else if (/[\'\-\.\?\@\#\%\_\@a-z\/]/i.test(c)) t += c, state = NAME;
      else if (/[0-9]/.test(c)) t += c, state = NUMBER;
      else if(c === '(' || c === '{' || c === '[') b.push(c), p.push(r), r = [];
      else if(c === ')' || c === '}' || c === ']') {
        if(b.length === 0) return serr(`unmatched bracket: ${c} (char ${i})`);
        const br = b.pop() as BracketO;
        if(matchingBracket(br) !== c) return serr(`unmatched bracket: ${br} and ${c}`);
        const a: Token[] = p.pop() as Token[];
        a.push(TList(r, br));
        r = a;
      }
      else if (/\s/.test(c)) continue;
      else return serr(`invalid char ${c} in tokenize`);
    } else if (state === NAME) {
      if (!(/[a-z0-9\-\_\/]/i.test(c) || (c === '.' && /[a-z0-9\_\/]/i.test(next)))) {
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
    } else if (state === BLOCKCOMMENT) {
      if (c + next + next2 === '{--') i += 2, commentlevel++;
      else if (c + next + next2 === '--}') {
        i += 2; commentlevel--;
        if (commentlevel === 0) state = START;
      }
    }
  }
  if (b.length > 0) return serr(`unclosed brackets: ${b.join(' ')}`);
  if (state !== START && state !== COMMENT)
    return serr('invalid tokenize end state');
  if (esc) return serr(`escape is true after tokenize`);
  if (commentlevel !== 0) return serr(`unclosed block comment`);
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

const UnitType = Var('()');

const erasedName = (x: Name): [Name, Erasure] => x[0] === '-' ? [x.slice(1), true] : [x, false];

const lambdaParams = (t: Token): [Erasure, Name, Mode, Surface | null][] => {
  if (t.tag === 'Name') {
    const [x, er] = erasedName(t.name);
    return [[er, x, Expl, null]];
  }
  if (t.tag === 'List') {
    const impl = t.bracket === '{' ? Impl : Expl;
    const a = t.list;
    if (a.length === 0) return [[false, '_', impl, UnitType]];
    const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
    if (i === -1) return isNames(a).map(x => {
      const [y, er] = erasedName(x);
      return [er, y, impl, null]
    });
    const ns = a.slice(0, i);
    const rest = a.slice(i + 1);
    const ty = exprs(rest, '(');
    return isNames(ns).map(x => {
      const [y, er] = erasedName(x);
      return [er, y, impl, ty]
    });
  }
  return serr(`invalid lambda param`);
};
const piParams = (t: Token): [Erasure, Name, Mode, Surface][] => {
  if (t.tag === 'Name') return [[false, '_', Expl, expr(t)[0]]];
  if (t.tag === 'List') {
    const impl = t.bracket === '{' ? Impl : Expl;
    const a = t.list;
    if (a.length === 0) return [[false, '_', impl, UnitType]];
    const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
    if (i === -1) return [[false, '_', impl, expr(t)[0]]];
    const ns = a.slice(0, i);
    const rest = a.slice(i + 1);
    const ty = exprs(rest, '(');
    return isNames(ns).map(x => {
      const [y, er] = erasedName(x);
      return [er, y, impl, ty]
    });
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

const mkVar = (x: string) => x[0] === '@' ? Rigid(Var(x.slice(1))) : Var(x);

const expr = (t: Token): [Surface, boolean] => {
  if (t.tag === 'List')
    return t.bracket === '[' ? [exprs(t.list, '['), false] : [exprs(t.list, '('), t.bracket === '{'];
  if (t.tag === 'Str') {
    const s = codepoints(t.str).reverse();
    const Cons = Var('Cons');
    const Nil = Var('Nil');
    return [s.reduce((t, n) => App(App(Cons, Expl, numToNat(n, `${n}`)), Expl, t), Nil as Surface), false];
  }
  if (t.tag === 'Name') {
    const x = t.name;
    if (x === '*') return [Type, false];
    if (x.includes('/')) return [Global(x), false];
    if (x[0] === "'") return [SymbolLit(x.slice(1)), false];
    if (x[0] === '_') {
      const y = x.slice(1);
      return [Hole(y.length > 0 ? y : null), false];
    }
    if (/[a-z\@]/i.test(x[0])) {
      if (x.indexOf('.') >= 0) {
        const parts = x.split('.');
        const first = parts[0];
        const ps = projs(parts.slice(1).join('.'));
        return [ps.reduce((t, p) => Proj(t, p), mkVar(first) as Surface), false];
      } else return [mkVar(x), false];
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

const Unit = Var('[]');
const Nil = Var('Nil');
const Cons = Var('Cons');
const VNil = Var('VNil');
const VCons = Var('VCons');
const exprs = (ts: Token[], br: BracketO, fromRepl: boolean = false): Surface => {
  if (br === '{') return serr(`{} cannot be used here`);
  if (br === '[') {
    if (ts.length === 0) return Unit;
    let type = 0;
    if (isName(ts[0], '#')) {
      ts = ts.slice(1);
      type = 1;
    } else if (isName(ts[0], '&')) {
      ts = ts.slice(1);
      type = 2;
    } else if (isName(ts[0], '%')) {
      ts = ts.slice(1);
      type = 3;
    } else if (isName(ts[0], '~')) {
      ts = ts.slice(1);
      type = 4;
    }
    if (ts.length === 0) {
      if (type === 1) return Pair(numToNat(0, '0'), Unit);
      if (type === 2) return Nil;
      if (type === 3) return VNil;
      return Unit;
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
      if (args.length === 0) {
        if (type === 1) return Pair(numToNat(0, '0'), Unit);
        if (type === 2) return Nil;
        if (type === 3) return VNil;
        return Unit;
      }
      if (type === 2) return args.reduceRight((x, [y, i]) => {
        if (i) return serr(`list element cannot be implicit`);
        return App(App(Cons, Expl, y), Expl, x);
      }, Nil as Surface);
      if (type === 3) return args.reduceRight((x, [y, i]) => {
        if (i) return serr(`vec element cannot be implicit`);
        return App(App(VCons, Expl, y), Expl, x);
      }, VNil as Surface);
      if (type === 4) return args.reduce((x, [y, i]) => {
        if (i) return serr(`tuple element cannot be implicit`);
        return Pair(x, y);
      }, Unit as Surface);
      const p = args.reduceRight((x, [y, i]) => {
        if (i) return serr(`pair element cannot be implicit`);
        return Pair(y, x);
      }, Unit as Surface);
      if (type === 1) Pair(numToNat(args.length, `${args.length}`), p);
      return p;
    } else {
      const expr = exprs(ts, '(');
      if (type === 1) return Pair(numToNat(1, `1`), Pair(expr, Unit));
      if (type === 2) return App(App(Cons, Expl, expr), Expl, Nil);
      if (type === 3) return App(App(VCons, Expl, expr), Expl, VNil);
      if (type === 4) return Pair(Unit, expr);
      return Pair(expr, Unit);
    }
  }
  if (ts.length === 0) return UnitType;
  if (ts.length === 1) return expr(ts[0])[0];
  if (isName(ts[0], 'let')) {
    let x = ts[1];
    let j = 2;
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
      const [y, er] = erasedName(name);
      return Let(er, y, ty || null, val, null as any);
    }
    const body = exprs(ts.slice(i + 1), '(');
    const [y, er] = erasedName(name);
    return Let(er, y, ty || null, val, body);
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
  const i = ts.findIndex(x => isName(x, ':'));
  if (i >= 0) {
    const a = ts.slice(0, i);
    const b = ts.slice(i + 1);
    return Ann(exprs(a, '('), exprs(b, '('));
  }
  if (isName(ts[0], '@')) {
    const term = exprs(ts.slice(1), '(');
    return Rigid(term);
  }
  if (isName(ts[0], '\\')) {
    const args: [Erasure, Name, Mode, Surface | null][] = [];
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
  const j = ts.findIndex(x => isName(x, '->'));
  if (j >= 0) {
    const s = splitTokens(ts, x => isName(x, '->'));
    if (s.length < 2) return serr(`parsing failed with ->`);
    const args: [Erasure, Name, Mode, Surface][] = s.slice(0, -1)
      .map(p => p.length === 1 ? piParams(p[0]) : [[false, '_', Expl, exprs(p, '(')] as [Erasure, Name, Mode, Surface]])
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
  const js = ts.findIndex(x => isName(x, '**'));
  if (js >= 0) {
    const s = splitTokens(ts, x => isName(x, '**'));
    if (s.length < 2) return serr(`parsing failed with **`);
    const args: [Erasure, Name, Mode, Surface][] = s.slice(0, -1)
      .map(p => p.length === 1 ? piParams(p[0]) : [[false, '_', Expl, exprs(p, '(')] as [Erasure, Name, Mode, Surface]])
      .reduce((x, y) => x.concat(y), []);
    const body = exprs(s[s.length - 1], '(');
    return args.reduceRight((x, [u, name, mode, ty]) => {
      if (mode.tag !== 'Expl') return serr(`sigma cannot be implicit`);
      return Sigma(u, name, ty, x)
    }, body);
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
