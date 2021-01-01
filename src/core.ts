import { Mode } from './mode';
import { Name } from './names';
import { Usage } from './usage';

export type Core = Pi | Abs | App;

export interface Pi { readonly tag: 'Pi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Pi = (usage: Usage, mode: Mode, name: Name, type: Core, body: Core): Pi =>
  ({ tag: 'Pi', usage, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Abs = (usage: Usage, mode: Mode, name: Name, type: Core, body: Core): Abs =>
  ({ tag: 'Abs', usage, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Core; readonly mode: Mode; readonly arg: Core }
export const App = (fn: Core, mode: Mode, arg: Core): App => ({ tag: 'App', fn, mode, arg });
