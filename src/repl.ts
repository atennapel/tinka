import { config, log, setConfig } from './config';
import { parse } from './parser';
import { Let, show, showCore, Surface, Var } from './surface';
import { many, Usage, zero } from './usage';
import { Name } from './names';
import { Local } from './local';
import { elaborate } from './elaboration';
import * as C from './core';
import { typecheck } from './typecheck';
import { evaluate, normalize } from './values';

const help = `
COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showStackTrace] show stack trace of error
[:type or :t] do not normalize
[:defs] show definitions
[:clear] clear definitions
[:undoDef] undo last def
`.trim();

let showStackTrace = false;
let defs: [Usage, Name, Surface | null, Surface][] = [];
let local: Local = Local.empty();

export const initREPL = () => {
  showStackTrace = false;
  defs = [];
  local = Local.empty();
};

export const runREPL = (s_: string, cb: (msg: string, err?: boolean) => void) => {
  try {
    let s = s_.trim();
    if (s === ':help' || s === ':h')
      return cb(help);
    if (s === ':d' || s === ':debug') {
      const d = !config.debug;
      setConfig({ debug: d });
      return cb(`debug: ${d}`);
    }
    if (s === ':showStackTrace') {
      showStackTrace = !showStackTrace;
      return cb(`showStackTrace: ${showStackTrace}`);
    }
    if (s === ':defs')
      return cb(defs.map(([u, x, t, v]) => `let ${u === '*' ? '' : `${u} `}${x}${t ? ` : ${show(t)}` : ''} = ${show(v)}`).join('\n'));
    if (s === ':clear') {
      defs = [];
      local = Local.empty();
      return cb(`cleared definitions`);
    }
    if (s === ':undoDef') {
      if (defs.length > 0) {
        const [u, x, t, v] = (defs.pop() as any);
        local = local.unsafeUndo();
        return cb(`undid let ${u === '*' ? '' : `${u} `}${x}${t ? ` : ${show(t)}` : ''} = ${show(v)}`);
      }
      cb(`no def to undo`);
    }
    let typeOnly = false;    
    if (s.startsWith(':type') || s.startsWith(':t')) {
      typeOnly = true;
      s = s.startsWith(':type') ? s.slice(5) : s.slice(2);
    }
    if (s.startsWith(':')) throw new Error(`invalid command: ${s}`);

    log(() => 'PARSE');
    let term = parse(s, true);
    let isDef = false;
    let usage = many;
    if (term.tag === 'Let' && term.body === null) {
      isDef = true;
      usage = term.usage;
      term = Let(term.usage === zero ? many : term.usage, term.name, term.type, term.val, Var(term.name));
    }
    log(() => show(term));

    log(() => 'ELABORATE');
    const [eterm, etype] = elaborate(term, local);
    log(() => C.show(eterm));
    log(() => showCore(eterm));
    log(() => C.show(etype));
    log(() => showCore(etype));

    log(() => 'VERIFICATION');
    typecheck(eterm, local);

    let normstr = '';
    if (!typeOnly) {
      log(() => 'NORMALIZE');
      const norm = normalize(eterm, local.vs);
      log(() => C.show(norm));
      log(() => showCore(norm));
      normstr = `\nnorm: ${showCore(norm)}`;
    }

    const etermstr = showCore(eterm, local.ns);

    if (isDef && term.tag === 'Let') {
      defs.push([usage, term.name, term.type, term.val]);
      const value = evaluate(eterm, local.vs);
      local = local.define(usage, term.name, evaluate(etype, local.vs), value);
    }

    return cb(`term: ${show(term)}\ntype: ${showCore(etype)}\netrm: ${etermstr}${normstr}`);
  } catch (err) {
    if (showStackTrace) console.error(err);
    return cb(`${err}`, true);
  }
};
