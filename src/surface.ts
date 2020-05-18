import { Name, Ix } from './names';

export type Plicity = boolean;

export type Sorts = '*' | '**';
export type Term = Var | App | Abs | Let | Pi | Sort | Ann | Hole | Meta | UnsafeCast;

export type Var = { tag: 'Var', name: Name };
export const Var = (name: Name): Var => ({ tag: 'Var', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, name: Name, type: Term | null, body: Term };
export const Abs = (plicity: Plicity, name: Name, type: Term | null, body: Term): Abs => ({ tag: 'Abs', plicity, name, type, body });
export type Let = { tag: 'Let', plicity: Plicity, name: Name, type: Term | null, val: Term, body: Term };
export const Let = (plicity: Plicity, name: Name, type: Term | null, val: Term, body: Term): Let => ({ tag: 'Let', plicity, name, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, name, type, body });
export type Sort = { tag: 'Sort', sort: Sorts };
export const Sort = (sort: Sorts): Sort => ({ tag: 'Sort', sort });
export type Ann = { tag: 'Ann', term: Term, type: Term };
export const Ann = (term: Term, type: Term): Ann => ({ tag: 'Ann', term, type });
export type Hole = { tag: 'Hole', name: Name | null };
export const Hole = (name: Name | null = null): Hole => ({ tag: 'Hole', name });
export type Meta = { tag: 'Meta', index: Ix };
export const Meta = (index: Ix): Meta => ({ tag: 'Meta', index });
export type UnsafeCast = { tag: 'UnsafeCast', type: Term | null, val: Term }
export const UnsafeCast = (type: Term | null, val: Term): UnsafeCast => ({ tag: 'UnsafeCast', type, val });

export const Type: Sort = Sort('*');

export const showTermS = (t: Term): string => {
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'App') return `(${showTermS(t.left)} ${t.plicity ? '-' : ''}${showTermS(t.right)})`;
  if (t.tag === 'Abs')
    return t.type ? `(\\(${t.plicity ? '-' : ''}${t.name} : ${showTermS(t.type)}). ${showTermS(t.body)})` : `(\\${t.plicity ? '-' : ''}${t.name}. ${showTermS(t.body)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${t.name}${t.type ? ` : ${showTermS(t.type)}` : ''} = ${showTermS(t.val)} in ${showTermS(t.body)})`;
  if (t.tag === 'Pi') return `(/(${t.plicity ? '-' : ''}${t.name} : ${showTermS(t.type)}). ${showTermS(t.body)})`;
  if (t.tag === 'Sort') return t.sort;
  if (t.tag === 'Ann') return `(${showTermS(t.term)} : ${showTermS(t.type)})`;
  if (t.tag === 'Hole') return `_${t.name || ''}`;
  if (t.tag === 'UnsafeCast') return `(unsafeCast ${t.type ? `{${showTermS(t.type)}} ` : ''}${showTermS(t.val)})`;
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

export const showTermP = (b: boolean, t: Term): string =>
  b ? `(${showTerm(t)})` : showTerm(t);
export const showTerm = (t: Term): string => {
  if (t.tag === 'Sort') return t.sort;
  if (t.tag === 'Var') return t.name;
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'App') {
    const [f, as] = flattenApp(t);
    return `${showTermP(f.tag === 'Abs' || f.tag === 'Pi' || f.tag === 'App' || f.tag === 'Let' || f.tag === 'Ann', f)} ${
      as.map(([im, t], i) =>
        im ? `{${showTerm(t)}}` :
          `${showTermP(t.tag === 'App' || t.tag === 'Ann' || t.tag === 'Let' || (t.tag === 'Abs' && i < as.length - 1) || t.tag === 'Pi', t)}`).join(' ')}`;
  }
  if (t.tag === 'Abs') {
    const [as, b] = flattenAbs(t);
    return `\\${as.map(([x, im, t]) => im ? `{${x}${t ? ` : ${showTermP(t.tag === 'Ann', t)}` : ''}}` : !t ? x : `(${x} : ${showTermP(t.tag === 'Ann', t)})`).join(' ')}. ${showTermP(b.tag === 'Ann', b)}`;
  }
  if (t.tag === 'Pi') {
    const [as, b] = flattenPi(t);
    return `${as.map(([x, im, t]) => x === '_' ? (im ? `${im ? '{' : ''}${showTerm(t)}${im ? '}' : ''}` : `${showTermP(t.tag === 'Ann' || t.tag === 'Abs' || t.tag === 'Let' || t.tag === 'Pi', t)}`) : `${im ? '{' : '('}${x} : ${showTermP(t.tag === 'Ann', t)}${im ? '}' : ')'}`).join(' -> ')} -> ${showTermP(b.tag === 'Ann', b)}`;
  }
  if (t.tag === 'Let')
    return `let ${t.plicity ? `{${t.name}}` : t.name}${t.type ? ` : ${showTermP(t.type.tag === 'Let' || t.type.tag === 'Ann', t.type)}` : ''} = ${showTermP(t.val.tag === 'Let', t.val)} in ${showTermP(t.body.tag === 'Ann', t.body)}`;
  if (t.tag === 'Ann')
    return `${showTermP(t.term.tag === 'Ann', t.term)} : ${showTermP(t.term.tag === 'Ann', t.type)}`;
  if (t.tag === 'Hole') return `_${t.name || ''}`;
  if (t.tag === 'UnsafeCast') return `unsafeCast ${t.type ? `{${showTermS(t.type)}} ` : ''}${showTermP(t.val.tag !== 'Var' && t.val.tag !== 'Meta' && t.val.tag !== 'Sort', t.val)}`;
  return t;
};

export const erase = (t: Term): Term => {
  if (t.tag === 'Hole') return t;
  if (t.tag === 'Meta') return t;
  if (t.tag === 'Var') return t;
  if (t.tag === 'Sort') return t;
  if (t.tag === 'Ann') return erase(t.term);
  if (t.tag === 'Abs') return t.plicity ? erase(t.body) : Abs(false, t.name, null, erase(t.body));
  if (t.tag === 'App') return t.plicity ? erase(t.left) : App(erase(t.left), false, erase(t.right));
  if (t.tag === 'Pi') return Pi(t.plicity, t.name, erase(t.type), erase(t.body));
  if (t.tag === 'Let') return t.plicity ? erase(t.body) : Let(false, t.name, null, erase(t.val), erase(t.body));
  if (t.tag === 'UnsafeCast') return erase(t.val);
  return t;
};

export type Def = DDef;

export type DDef = { tag: 'DDef', name: Name, value: Term };
export const DDef = (name: Name, value: Term): DDef => ({ tag: 'DDef', name, value });

export const showDef = (d: Def): string => {
  if (d.tag === 'DDef') return `def ${d.name} = ${showTerm(d.value)}`;
  return d.tag;
};
export const showDefs = (ds: Def[]): string => ds.map(showDef).join('\n');
