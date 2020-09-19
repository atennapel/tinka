import { Name, Ix, nextName } from './names';
import { List, index, Cons, contains, take, toArray, Nil } from './utils/list';
import * as S from './surface';

export type Term = Var | Global | App | Abs | Pair | Proj | Let;

export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type Global = { tag: 'Global', name: Name };
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export type App = { tag: 'App', left: Term, right: Term };
export const App = (left: Term, right: Term): App => ({ tag: 'App', left, right });
export type Abs = { tag: 'Abs', name: Name, body: Term };
export const Abs = (name: Name, body: Term): Abs => ({ tag: 'Abs', name, body });
export type Pair = { tag: 'Pair', fst: Term, snd: Term };
export const Pair = (fst: Term, snd: Term): Pair => ({ tag: 'Pair', fst, snd });
export type Proj = { tag: 'Proj', proj: 'fst' | 'snd', term: Term };
export const Proj = (proj: 'fst' | 'snd', term: Term): Proj => ({ tag: 'Proj', proj, term });
export type Let = { tag: 'Let', name: Name, val: Term, body: Term };
export const Let = (name: Name, val: Term, body: Term): Let => ({ tag: 'Let', name, val, body });

export const showTermS = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'App') return `(${showTermS(t.left)} ${showTermS(t.right)})`;
  if (t.tag === 'Abs') return `(\\${t.name}. ${showTermS(t.body)})`;
  if (t.tag === 'Pair') return `(${showTermS(t.fst)}, ${showTermS(t.snd)})`;
  if (t.tag === 'Let') return `(let ${t.name} = ${showTermS(t.val)} in ${showTermS(t.body)})`;
  if (t.tag === 'Proj') return `(${t.proj} ${showTermS(t.term)})`;
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
export const flattenAbs = (t: Term): [Name[], Term] => {
  const r: Name[] = [];
  while (t.tag === 'Abs') {
    r.push(t.name);
    t = t.body;
  }
  return [r, t];
};
export const flattenPair = (t: Term): Term[] => {
  const r: Term[] = [];
  while (t.tag === 'Pair') {
    r.push(t.fst);
    t = t.snd;
  }
  r.push(t);
  return r;
};

const showTermP = (b: boolean, t: Term, ns: List<Name>) => b ? `(${showTerm(t, ns)})` : showTerm(t, ns);
const isSimple = (t: Term) => t.tag === 'Var' || t.tag === 'Global' || t.tag === 'Pair';
const chooseName = (x: Name, ns: List<Name>): Name =>
  contains(ns, x) ? chooseName(nextName(x), ns) : x;
export const showTerm = (t: Term, ns: List<Name> = Nil): string => {
  if (t.tag === 'Var') return index(ns, t.index) || `$${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'App') {
    const [f, as] = flattenApp(t);
    return `${showTermP(!isSimple(f) && f.tag !== 'Proj', f, ns)} ${as.map((t, i) => showTermP(!isSimple(t) && !(t.tag === 'Abs' && i === as.length - 1), t, ns)).join(' ')}`;
  }
  if (t.tag === 'Abs') {
    const [xs, b] = flattenAbs(t);
    const newns = xs.reduce((ys, x) => Cons(chooseName(x, ys), ys), ns);
    const ys = toArray(take(newns, xs.length), x => x).reverse();
    return `\\${ys.join(' ')}. ${showTerm(b, newns)}`;
  }
  if (t.tag === 'Pair') {
    const ps = flattenPair(t);
    return `(${ps.map(t => showTerm(t, ns)).join(', ')})`;
  }
  if (t.tag === 'Let')
    return `let ${t.name} = ${showTermP(t.val.tag === 'Let', t.val, ns)} in ${showTerm(t.body, Cons(chooseName(t.name, ns), ns))}`;
  if (t.tag === 'Proj') return `.${t.proj} ${showTermP(!isSimple(t.term), t.term, ns)}`;
  return t;
};

export const idTerm = Abs('x', Var(0));

export const erasePrim = (prim: S.PrimName): Term => {
  if (prim === 'UnitType') return idTerm;
  if (prim === 'Bool') return idTerm;
  if (prim === 'IFix') return idTerm;
  if (prim === 'HEq') return idTerm;
  if (prim === 'unsafeElimHEq') return idTerm;

  if (prim === 'Unit') return idTerm;
  if (prim === 'True') return Abs('x', Abs('y', Var(1)));
  if (prim === 'False') return Abs('x', Abs('y', Var(0)));
  if (prim === 'indBool') return Abs('t', Abs('f', Abs('b', App(App(Var(0), Var(2)), Var(1))))); // \t f b. b t f
  if (prim === 'ReflHEq') return idTerm;
  if (prim === 'IIn') return Abs('x', Abs('f', App(App(Var(0), Abs('y', App(Var(0), Var(1)))), Var(1)))); // \x f. f (\x. x f) x
  if (prim === 'elimHEq') return Abs('x', Abs('y', App(Var(0), Var(1)))); // \x p. p x
  if (prim === 'genindIFix') return Abs('x', Abs('y', App(Var(0), Var(1)))); // \f x. x f

  return prim;
};
