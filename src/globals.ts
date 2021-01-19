import { elaborate } from './elaboration';
import { Local } from './local';
import { parse } from './parser';
import { freeVars, Surface } from './surface';
import { typecheck } from './typecheck';
import { nil } from './utils/List';
import { impossible, loadFile, loadFileSync, removeAll } from './utils/utils';
import { evaluate, Val } from './values';
import * as EV from './erasedvalues';

export interface EntryG {
  val: Val,
  type: Val,
  erval: EV.Val,
}

type Globals = { [key: string]: EntryG };

let globals: Globals = {};

export const globalReset = () => {
  globals = {};
};

export const globalGet = (x: string): EntryG | null => globals[x] || null;
export const globalSet = (x: string, val: Val, type: Val, erval: EV.Val): void => {
  globals[x] = { val, type, erval };
};

export const globalLoad = (x: string): EntryG | null => {
  if (globals[x]) return globals[x];
  const sc = loadFileSync(`lib/${x}`);
  if (sc instanceof Error) return null;
  const e = parse(sc);
  const [tm, ty] = elaborate(e);
  const [, er] = typecheck(tm);
  globalSet(x, evaluate(tm, nil), evaluate(ty, nil), EV.evaluate(er, nil));
  return globalGet(x);
};

export const preload = (t: Surface, local: Local = Local.empty()): Promise<EntryG[]> => {
  const vs = freeVars(t);
  const localVars = local.nsSurface.toArray();
  removeAll(vs, localVars);
  return Promise.all(vs.map(async v => {
    const sc = await loadFile(`lib/${v}`);
    const e = parse(sc);
    const [tm, ty] = elaborate(e);
    const [, er] = typecheck(tm);
    globalSet(v, evaluate(tm, nil), evaluate(ty, nil), EV.evaluate(er, nil));
    return globalGet(v) || impossible(`preload failed, unable to get ${v}`);
  }));
};
