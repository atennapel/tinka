import { Val } from './domain';
import { Term } from './syntax';
import { Name } from './names';
import * as E from './erased';
import { Plicity } from './surface';

export type EnvGEntry = {
  term: Term,
  val: Val,
  type: Val,
  plicity: Plicity,
  erased: E.Term,
};
export type EnvG = { [key: string]: EnvGEntry };

let env: EnvG = {};

export const globalReset = () => {
  env = {};
};
export const globalMap = (): EnvG => env;
export const globalGet = (name: Name): EnvGEntry | null =>
  env[name] || null;
export const globalSet = (name: Name, term: Term, val: Val, type: Val, plicity: Plicity, erased: E.Term): void => {
  env[name] = { term, val, type, plicity, erased };
};
export const globalDelete = (name: Name): void => {
  delete env[name];
};
