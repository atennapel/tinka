import { Name, Ix } from './names';

export type Plicity = boolean;

export type ProjType = PName | PIndex | PCore;
export type PName = { tag: 'PName', name: Name };
export const PName = (name: Name): PName => ({ tag: 'PName', name });
export type PIndex = { tag: 'PIndex', index: Ix };
export const PIndex = (index: Ix): PIndex => ({ tag: 'PIndex', index });
export type PCore = { tag: 'PCore', proj: 'fst' | 'snd' };
export const PCore = (proj: 'fst' | 'snd'): PCore => ({ tag: 'PCore', proj });

export type Term = Var | App | Abs | Pair | Proj | Let | Pi | Sigma | Type | Data | TCon | Con | Ann | Hole | Meta | Prim;

export type Var = { tag: 'Var', name: Name };
export const Var = (name: Name): Var => ({ tag: 'Var', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, name: Name, type: Term | null, body: Term };
export const Abs = (plicity: Plicity, name: Name, type: Term | null, body: Term): Abs => ({ tag: 'Abs', plicity, name, type, body });
export type Pair = { tag: 'Pair', plicity: Plicity, plicity2: Plicity, fst: Term, snd: Term };
export const Pair = (plicity: Plicity, plicity2: Plicity, fst: Term, snd: Term): Pair => ({ tag: 'Pair', plicity, plicity2, fst, snd });
export type Proj = { tag: 'Proj', proj: ProjType, term: Term };
export const Proj = (proj: ProjType, term: Term): Proj => ({ tag: 'Proj', proj, term });
export type Let = { tag: 'Let', plicity: Plicity, name: Name, type: Term | null, val: Term, body: Term };
export const Let = (plicity: Plicity, name: Name, type: Term | null, val: Term, body: Term): Let => ({ tag: 'Let', plicity, name, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, name, type, body });
export type Sigma = { tag: 'Sigma', plicity: Plicity, plicity2: Plicity, name: Name, type: Term, body: Term };
export const Sigma = (plicity: Plicity, plicity2: Plicity, name: Name, type: Term, body: Term): Sigma => ({ tag: 'Sigma', plicity, plicity2, name, type, body });
export type Type = { tag: 'Type' };
export const Type: Type = { tag: 'Type' };
export type Data = { tag: 'Data', kind: Term, cons: Term[] };
export const Data = (kind: Term, cons: Term[]): Data => ({ tag: 'Data', kind, cons });
export type TCon = { tag: 'TCon', data: Term, args: Term[] };
export const TCon = (data: Term, args: Term[]): TCon => ({ tag: 'TCon', data, args });
export type Con = { tag: 'Con', ix: Ix, data: Term, args: Term[] };
export const Con = (ix: Ix, data: Term, args: Term[]): Con => ({ tag: 'Con', ix, data, args });
export type Ann = { tag: 'Ann', term: Term, type: Term };
export const Ann = (term: Term, type: Term): Ann => ({ tag: 'Ann', term, type });
export type Hole = { tag: 'Hole', name: Name | null };
export const Hole = (name: Name | null = null): Hole => ({ tag: 'Hole', name });
export type Meta = { tag: 'Meta', index: Ix };
export const Meta = (index: Ix): Meta => ({ tag: 'Meta', index });

export type PrimName =
  'Data' |
  'drec' | 'dreci' |
  'HEq' | 'ReflHEq' | 'elimHEq' |
  'Nat' | 'Z' | 'S' | 'elimNat' |
  'Fin' | 'FZ' | 'FS' | 'elimFin' | 'elimFin0' |
  'IFix' | 'IIn' | 'elimIFix';
export const primNames = [
  'Data',
  'drec', 'dreci',
  'HEq', 'ReflHEq', 'elimHEq',
  'Nat', 'Z', 'S', 'elimNat',
  'Fin', 'FZ', 'FS', 'elimFin', 'elimFin0',
  'IFix', 'IIn', 'elimIFix',
];
export const isPrimName = (x: string): x is PrimName => primNames.includes(x);
export type Prim = { tag: 'Prim', name: PrimName };
export const Prim = (name: PrimName): Prim => ({ tag: 'Prim', name });

export const showTermS = (t: Term): string => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Prim') return `%${t.name}`;
  if (t.tag === 'Type') return '*';
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'App') return `(${showTermS(t.left)} ${t.plicity ? '-' : ''}${showTermS(t.right)})`;
  if (t.tag === 'Abs')
    return t.type ? `(\\(${t.plicity ? '-' : ''}${t.name} : ${showTermS(t.type)}). ${showTermS(t.body)})` : `(\\${t.plicity ? '-' : ''}${t.name}. ${showTermS(t.body)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${t.name}${t.type ? ` : ${showTermS(t.type)}` : ''} = ${showTermS(t.val)} in ${showTermS(t.body)})`;
  if (t.tag === 'Pi') return `(/(${t.plicity ? '-' : ''}${t.name} : ${showTermS(t.type)}). ${showTermS(t.body)})`;
  if (t.tag === 'Sigma') return `(${t.plicity ? '{' : '('}${t.name} : ${showTermS(t.type)}${t.plicity ? '}' : ')'} ** ${t.plicity ? '{' : '('}${showTermS(t.body)}${t.plicity ? '}' : ')'})`;
  if (t.tag === 'Ann') return `(${showTermS(t.term)} : ${showTermS(t.type)})`;
  if (t.tag === 'Hole') return `_${t.name || ''}`;
  if (t.tag === 'Pair') return `(${t.plicity ? '{' : ''}${showTermS(t.fst)}${t.plicity ? '}' : ''}, ${t.plicity ? '{' : ''}${showTermS(t.snd)}${t.plicity ? '}' : ''})`;
  if (t.tag === 'Proj') return `(.${t.proj.tag === 'PName' ? t.proj.name : t.proj.tag === 'PIndex' ? t.proj.index : t.proj.proj} ${showTermS(t.term)})`;
  if (t.tag === 'Data') return `(data ${showTermS(t.kind)}${t.cons.length > 0 ? ` ${t.cons.map(showTermS).join(' ')}` : ''})`;
  if (t.tag === 'TCon') return `(tcon ${showTermS(t.data)}${t.args.length > 0 ? ` ${t.args.map(showTermS).join(' ')}` : ''})`;
  if (t.tag === 'Con') return `(con ${t.ix} ${showTermS(t.data)}${t.args.length > 0 ? ` ${t.args.map(showTermS).join(' ')}` : ''})`;
  return t;
};

export const flattenApp = (t: Term): [Term, [Plicity, Term][]] => {
  const r: [Plicity, Term][] = [];
  while (t.tag === 'App') {
    r.push([t.plicity, t.right]);
    t = t.left;
  }
  return [t, r.reverse()];
};
export const flattenAbs = (t: Term): [[Name, Plicity, Term | null][], Term] => {
  const r: [Name, Plicity, Term | null][] = [];
  while (t.tag === 'Abs') {
    r.push([t.name, t.plicity, t.type]);
    t = t.body;
  }
  return [r, t];
};
export const flattenPi = (t: Term): [[Name, Plicity, Term][], Term] => {
  const r: [Name, Plicity, Term][] = [];
  while (t.tag === 'Pi') {
    r.push([t.name, t.plicity, t.type]);
    t = t.body;
  }
  return [r, t];
};
export const flattenSigma = (t: Term): [[Name, Plicity, Term][], Term, boolean] => {
  const r: [Name, Plicity, Term][] = [];
  let right = false;
  while (t.tag === 'Sigma') {
    r.push([t.name, t.plicity, t.type]);
    if (t.plicity2) {
      right = true;
      t = t.body;
      break;
    }
    t = t.body;
  }
  return [r, t, right];
};
export const flattenPair = (t: Term): [Plicity, Term][] => {
  const r: [Plicity, Term][] = [];
  let right = false;
  while (t.tag === 'Pair') {
    r.push([t.plicity, t.fst]);
    if (t.plicity2) {
      right = true;
      t = t.snd;
      break;
    }
    t = t.snd;
  }
  r.push([right, t]);
  return r;
};

export const showTermP = (b: boolean, t: Term): string =>
  b ? `(${showTerm(t)})` : showTerm(t);
export const showTerm = (t: Term): string => {
  if (t.tag === 'Prim') return `%${t.name}`;
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'Type') return '*';
  if (t.tag === 'App') {
    const [f, as] = flattenApp(t);
    return `${showTermP(f.tag === 'Abs' || f.tag === 'Pi' || f.tag === 'Sigma' || f.tag === 'App' || f.tag === 'Let' || f.tag === 'Ann' || f.tag === 'Proj' || f.tag === 'Data' || f.tag === 'TCon' || f.tag === 'Con', f)} ${
      as.map(([im, t], i) =>
        im ? `{${showTerm(t)}}` :
          `${showTermP(t.tag === 'App' || t.tag === 'Ann' ||t.tag === 'Let' || (t.tag === 'Abs' && i < as.length - 1) || t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Proj' || t.tag === 'Data' || t.tag === 'TCon' || t.tag === 'Con', t)}`).join(' ')}`;
  }
  if (t.tag === 'Abs') {
    const [as, b] = flattenAbs(t);
    return `\\${as.map(([x, im, t]) => im ? `{${x}${t ? ` : ${showTermP(t.tag === 'Ann', t)}` : ''}}` : !t ? x : `(${x} : ${showTermP(t.tag === 'Ann', t)})`).join(' ')}. ${showTermP(b.tag === 'Ann', b)}`;
  }
  if (t.tag === 'Pi') {
    const [as, b] = flattenPi(t);
    return `${as.map(([x, im, t]) => x === '_' ? (im ? `${im ? '{' : ''}${showTerm(t)}${im ? '}' : ''}` : showTermP(t.tag === 'Ann' || t.tag === 'Abs' || t.tag === 'Let' || t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Proj' || t.tag === 'Data' || t.tag === 'TCon' || t.tag === 'Con', t)) : `${im ? '{' : '('}${x} : ${showTermP(t.tag === 'Ann', t)}${im ? '}' : ')'}`).join(' -> ')} -> ${showTermP(b.tag === 'Ann', b)}`;
  }
  if (t.tag === 'Sigma') {
    const [as, b, p] = flattenSigma(t);
    return `${as.map(([x, im, t]) => x === '_' ? (im ? `${im ? '{' : ''}${showTerm(t)}${im ? '}' : ''}` :showTermP(t.tag === 'Ann' || t.tag === 'Abs' || t.tag === 'Let' || t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Proj' || t.tag === 'Data' || t.tag === 'TCon' || t.tag === 'Con', t)) : `${im ? '{' : '('}${x} : ${showTermP(t.tag === 'Ann', t)}${im ? '}' : ')'}`).join(' ** ')} ** ${p ? `{${showTerm(b)}}` : showTermP(b.tag === 'Ann', b)}`
  }
  if (t.tag === 'Pair') {
    const ps = flattenPair(t);
    return `(${ps.map(([p, t]) => p ? `{${showTerm(t)}}` : showTerm(t)).join(', ')})`;
  }
  if (t.tag === 'Let')
    return `let ${t.plicity ? `{${t.name}}` : t.name}${t.type ? ` : ${showTermP(t.type.tag === 'Let' || t.type.tag === 'Ann', t.type)}` : ''} = ${showTermP(t.val.tag === 'Let', t.val)} in ${showTermP(t.body.tag === 'Ann', t.body)}`;
  if (t.tag === 'Ann')
    return `${showTermP(t.term.tag === 'Ann', t.term)} : ${showTermP(t.term.tag === 'Ann', t.type)}`;
  if (t.tag === 'Hole') return `_${t.name || ''}`;
  if (t.tag === 'Proj') return `.${t.proj.tag === 'PName' ? t.proj.name : t.proj.tag === 'PIndex' ? t.proj.index : t.proj.proj} ${showTermP(t.term.tag !== 'Var' && t.term.tag !== 'Meta' && t.term.tag !== 'Prim' && t.term.tag !== 'Type', t.term)}`;
  if (t.tag === 'Data') return `data ${showTermP(t.kind.tag !== 'Var' && t.kind.tag !== 'Meta' && t.kind.tag !== 'Prim' && t.kind.tag !== 'Type', t.kind)}${t.cons.length > 0 ? ` ${t.cons.map(x => showTermP(x.tag !== 'Var' && x.tag !== 'Meta' && x.tag !== 'Prim' && x.tag !== 'Type', x)).join(' ')}` : ''}`;
  if (t.tag === 'TCon') return `tcon ${showTermP(t.data.tag !== 'Var' && t.data.tag !== 'Meta' && t.data.tag !== 'Prim' && t.data.tag !== 'Type', t.data)}${t.args.length > 0 ? ` ${t.args.map(x => showTermP(x.tag !== 'Var' && x.tag !== 'Meta' && x.tag !== 'Prim' && x.tag !== 'Type', x)).join(' ')}` : ''}`;
  if (t.tag === 'Con') return `con ${t.ix} ${showTermP(t.data.tag !== 'Var' && t.data.tag !== 'Meta' && t.data.tag !== 'Prim' && t.data.tag !== 'Type', t.data)}${t.args.length > 0 ? ` ${t.args.map(x => showTermP(x.tag !== 'Var' && x.tag !== 'Meta' && x.tag !== 'Prim' && x.tag !== 'Type', x)).join(' ')}` : ''}`;
  return t;
};

export const erase = (t: Term): Term => {
  if (t.tag === 'Hole') return t;
  if (t.tag === 'Meta') return t;
  if (t.tag === 'Var') return t;
  if (t.tag === 'Prim') return t;
  if (t.tag === 'Ann') return erase(t.term);
  if (t.tag === 'Abs') return t.plicity ? erase(t.body) : Abs(false, t.name, null, erase(t.body));
  if (t.tag === 'Pair') {
    if (t.plicity && t.plicity2) return t;
    if (t.plicity) return erase(t.snd);
    if (t.plicity2) return erase(t.fst);
    return Pair(false, false, erase(t.fst), erase(t.snd));
  }
  if (t.tag === 'App')
    return t.plicity ? erase(t.left) : App(erase(t.left), false, erase(t.right));
  if (t.tag === 'Pi') return Pi(t.plicity, t.name, erase(t.type), erase(t.body));
  if (t.tag === 'Sigma') return Sigma(t.plicity, t.plicity2, t.name, erase(t.type), erase(t.body));
  if (t.tag === 'Let') return t.plicity ? erase(t.body) : Let(false, t.name, null, erase(t.val), erase(t.body));
  if (t.tag === 'Proj') return Proj(t.proj, erase(t.term));
  if (t.tag === 'Data') return Data(erase(t.kind), t.cons.map(erase));
  if (t.tag === 'TCon') return TCon(erase(t.data), t.args.map(erase));
  if (t.tag === 'Con') return Con(t.ix, erase(t.data), t.args.map(erase));
  return t;
};

export type Def = DDef;

export type DDef = { tag: 'DDef', name: Name, value: Term, plicity: Plicity };
export const DDef = (name: Name, value: Term, plicity: Plicity): DDef => ({ tag: 'DDef', name, value, plicity });

export const showDef = (d: Def): string => {
  if (d.tag === 'DDef') return `def ${d.plicity ? '{' : ''}${d.name}${d.plicity ? '}' : ''} = ${showTerm(d.value)}`;
  return d.tag;
};
export const showDefs = (ds: Def[]): string => ds.map(showDef).join('\n');
