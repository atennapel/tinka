import { Ix } from '../names';
import { Term as TTerm } from '../core/syntax';
import { impossible } from '../utils/util';
import { globalGet } from '../globalenv';

export type Term = Var | App | Abs | Num | Inc | Pair;

export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type App = { tag: 'App', left: Term, right: Term };
export const App = (left: Term, right: Term): App => ({ tag: 'App', left, right });
export type Abs = { tag: 'Abs', body: Term };
export const Abs = (body: Term): Abs => ({ tag: 'Abs', body });

export type Num = { tag: 'Num', value: number };
export const Num = (value: number): Num => ({ tag: 'Num', value });
export type Inc = { tag: 'Inc', term: Term };
export const Inc = (term: Term): Inc => ({ tag: 'Inc', term });
export type Pair = { tag: 'Pair', fst: Term, snd: Term };
export const Pair = (fst: Term, snd: Term): Pair => ({ tag: 'Pair', fst, snd });

export const idTerm = Abs(Var(0));

export const showTermS = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'App') return `(${showTermS(t.left)} ${showTermS(t.right)})`;
  if (t.tag === 'Abs') return `(\\${showTermS(t.body)})`;
  if (t.tag === 'Num') return `#${t.value}`;
  if (t.tag === 'Inc') return `(inc ${showTermS(t.term)})`;
  if (t.tag === 'Pair') return `(${showTermS(t.fst)}, ${showTermS(t.snd)})`;
  return t;
};

export const flattenApp = (t: Term): [Term, Term[]] => {
  const r: Term[] = [];
  while (t.tag === 'App') {
    r.push(t.right);
    t = t.left;
  }
  return [t, r.reverse()];
};

export const showTermP = (b: boolean, t: Term): string =>
  b ? `(${showTerm(t)})` : showTerm(t);
export const showTerm = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'App') {
    const [f, as] = flattenApp(t);
    return `${showTermP(f.tag === 'Abs' || f.tag === 'App', f)} ${
      as.map((t, i) =>
          `${showTermP(t.tag === 'App' || (t.tag === 'Abs' && i < as.length - 1) || t.tag === 'Inc', t)}`).join(' ')}`;
  }
  if (t.tag === 'Abs') return `\\${showTerm(t.body)}`;
  if (t.tag === 'Num') return `#${t.value}`;
  if (t.tag === 'Inc') return `inc ${showTermP(t.term.tag === 'App', t.term)}`;
  if (t.tag === 'Pair') return `(${showTerm(t.fst)}, ${showTerm(t.snd)})`;
  return t;
};

export const shift = (d: Ix, c: Ix, t: Term): Term => {
  if (t.tag === 'Var') return t.index < c ? t : Var(t.index + d);
  if (t.tag === 'Abs') return Abs(shift(d, c + 1, t.body));
  if (t.tag === 'App') return App(shift(d, c, t.left), shift(d, c, t.right));
  if (t.tag === 'Inc') return Inc(shift(d, c, t.term));
  if (t.tag === 'Pair') return Pair(shift(d, c, t.fst), shift(d, c, t.snd));
  return t;
};

export const erase = (t: TTerm): Term => {
  if (t.tag === 'Global') {
    const res = globalGet(t.name);
    if (!res) return impossible(`erase: global not in map: ${t.name}`);
    return res.pure;
  }
  if (t.tag === 'Var') return Var(t.index);
  if (t.tag === 'App') return t.plicity ? erase(t.left) : App(erase(t.left), erase(t.right));
  if (t.tag === 'Abs') return t.plicity ? shift(-1, 0, erase(t.body)) : Abs(erase(t.body));
  if (t.tag === 'Let') return t.plicity ? shift(-1, 0, erase(t.body)) : App(Abs(erase(t.body)), erase(t.val));
  if (t.tag === 'Roll') return erase(t.term);
  if (t.tag === 'Unroll') return erase(t.term);
  if (t.tag === 'Pi') return idTerm;
  if (t.tag === 'Fix') return idTerm;
  if (t.tag === 'Type') return idTerm;
  if (t.tag === 'Data') return idTerm;
  if (t.tag === 'Con') {
    // scott-encoding
    // cons {T} i n args... = \a1..a_n. a_i args...
    const args = t.args.filter(([_, p]) => !p).map(([x, _]) => shift(t.total, 0, erase(x)));
    let c = args.reduce((a, b) => App(a, b), Var(t.total - t.index - 1));
    for (let i = 0; i < t.total; i++) c = Abs(c);
    return c;
  }
  return t;
};
