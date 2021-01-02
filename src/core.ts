import { Mode } from './mode';
import { Ix, Name } from './names';
import { many, Usage } from './usage';

export type Core =
  Var | Global | Let |
  Type |
  Pi | Abs | App;

export interface Var { readonly tag: 'Var'; readonly index: Ix }
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export interface Global { readonly tag: 'Global'; readonly name: Name }
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export interface Let { readonly tag: 'Let'; readonly usage: Usage; readonly name: Name; readonly type: Core; readonly val: Core; readonly body: Core }
export const Let = (usage: Usage, name: Name, type: Core, val: Core, body: Core): Let => ({ tag: 'Let', usage, name, type, val, body });
export interface Type { readonly tag: 'Type' }
export const Type: Type = { tag: 'Type' };
export interface Pi { readonly tag: 'Pi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Pi = (usage: Usage, mode: Mode, name: Name, type: Core, body: Core): Pi =>
  ({ tag: 'Pi', usage, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Abs = (usage: Usage, mode: Mode, name: Name, type: Core, body: Core): Abs =>
  ({ tag: 'Abs', usage, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Core; readonly mode: Mode; readonly arg: Core }
export const App = (fn: Core, mode: Mode, arg: Core): App => ({ tag: 'App', fn, mode, arg });

export const flattenPi = (t: Core): [[Usage, Mode, Name, Core][], Core] => {
  const params: [Usage, Mode, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Pi') {
    params.push([c.usage, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenAbs = (t: Core): [[Usage, Mode, Name, Core][], Core] => {
  const params: [Usage, Mode, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Abs') {
    params.push([c.usage, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenApp = (t: Core): [Core, [Mode, Core][]] => {
  const args: [Mode, Core][] = [];
  let c = t;  
  while (c.tag === 'App') {
    args.push([c.mode, c.arg]);
    c = c.fn;
  }
  return [c, args.reverse()];
};

const showP = (b: boolean, t: Core) => b ? `(${show(t)})` : show(t);
const isSimple = (t: Core) => t.tag === 'Type' || t.tag === 'Var' || t.tag === 'Global';
const showS = (t: Core) => showP(!isSimple(t), t);
export const show = (t: Core): string => {
  if (t.tag === 'Type') return 'Type';
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Global') return `${t.name}`;
  if (t.tag === 'Pi') {
    const [params, ret] = flattenPi(t);
    return `${params.map(([u, m, x, t]) => u === many && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${u === many ? '' : `${u} `}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' -> ')} -> ${show(ret)}`;
  }
  if (t.tag === 'Abs') {
    const [params, body] = flattenAbs(t);
    return `\\${params.map(([u, m, x, t]) => `${m.tag === 'Expl' ? '(' : '{'}${u === many ? '' : `${u} `}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' ')}. ${show(body)}`;
  }
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${show(a)}}`).join(' ')}`;
  }
  if (t.tag === 'Let')
    return `let ${t.usage === many ? '' : `${t.usage} `}${t.name} : ${showP(t.type.tag === 'Let', t.type)} = ${showP(t.val.tag === 'Let', t.val)}; ${show(t.body)}`;
  return t;
};
