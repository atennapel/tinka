import { config, log, setConfig } from './config';
import { parse } from './parser';
import { Let, show, showCore, Var } from './surface';
import { Name } from './names';
import { EntryT, Local } from './local';
import { elaborate } from './elaboration';
import * as C from './core';
import { verify } from './verification';
import { evaluate, normalize, quote, Val } from './values';
import { loadFile } from './utils/utils';
import { setGlobal } from './globals';
import { Cons, nil } from './utils/List';

const help = `
COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showStackTrace] show stack trace of error
[:type or :t] do not normalize
[:defs] show definitions
[:clear] clear definitions
[:undoDef] undo last def
[:load name] load a global
`.trim();

let showStackTrace = false;
let doPreload = true;
let showFullNorm = false;
let showErasure = true;
let local: Local = Local.empty();

export const initREPL = () => {
  showStackTrace = false;
  showFullNorm = false;
  doPreload = true;
  showErasure = true;
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
    if (s === ':showFullNorm') {
      showFullNorm = !showFullNorm;
      return cb(`showFullNorm: ${showFullNorm}`);
    }
    if (s === ':showErasure') {
      showErasure = !showErasure;
      return cb(`showErasure: ${showErasure}`);
    }
    if (s === ':preload') {
      doPreload = !doPreload;
      return cb(`preload: ${doPreload}`);
    }
    if (s === ':defs') {
      const defs: string[] = [];
      for (let i = local.level - 1; i >= 0; i--) {
        const x = local.ns.index(i) as Name;
        const entry = local.ts.index(i) as EntryT;
        const u = entry.erased;
        const t = quote(entry.type, local.level);
        const v = quote(local.vs.index(i) as Val, local.level);
        defs.push(`${u ? '-' : ``}${x} : ${showCore(t, local.ns)} = ${showCore(v, local.ns)}`);
      }
      return cb(defs.join('\n'));
    }
    if (s === ':clear') {
      local = Local.empty();
      return cb(`cleared definitions`);
    }
    if (s === ':undoDef') {
      if (local.level > 0) {
        const name = (local.ns as Cons<Name>).head;
        local = local.undo();
        return cb(`removed definition ${name}`);
      }
      cb(`no def to undo`);
    }
    if (s.startsWith(':load') || s.startsWith(':eload')) {
      const erased = s.startsWith(':eload');
      const name = `lib/${s.slice(s.startsWith(':load') ? 5 : 6).trim()}`;
      loadFile(name)
        .then(sc => parse(sc))
        .then(e => {
          const [tm, ty] = elaborate(e);
          verify(tm);
          setGlobal(name, evaluate(ty, nil), evaluate(tm, nil), ty, tm, erased);
          cb(`loaded ${name}`);
        })
        .catch(err => cb('' + err, true));
      return;
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
    let erased = false;
    if (term.tag === 'Let' && term.body === null) {
      isDef = true;
      erased = term.erased;
      term = Let(erased, term.name, term.type, term.val, Var(term.name));
    }
    log(() => show(term));

    let prom = Promise.resolve();
    prom.then(() => {
      log(() => 'ELABORATE');
      const [eterm, etype] = elaborate(term, erased ? local.inType() : local);
      log(() => C.show(eterm));
      log(() => showCore(eterm, local.ns));
      log(() => C.show(etype));
      log(() => showCore(etype, local.ns));

      log(() => 'VERIFICATION');
      verify(eterm, erased ? local.inType() : local);

      let normstr = '';
      if (!typeOnly) {
        log(() => 'NORMALIZE');
        if (showFullNorm) {
          const norm = normalize(eterm, local.level, local.vs, true);
          log(() => C.show(norm));
          log(() => showCore(norm, local.ns));
          normstr += `\nnorm: ${showCore(norm, local.ns)}`;
        }
      }

      const etermstr = showCore(eterm, local.ns);

      if (isDef) {
        if (term.tag === 'Let') {
          const value = evaluate(eterm, local.vs);
          local = local.define(erased, term.name, evaluate(etype, local.vs), value);
        } else throw new Error(`invalid definition: ${term.tag}`);
      }

      return cb(`term: ${show(term)}\ntype: ${showCore(etype, local.ns)}\netrm: ${etermstr}${normstr}`);
    }).catch(err => {
      if (showStackTrace) console.error(err);
      return cb(`${err}`, true);
    });
  } catch (err) {
    if (showStackTrace) console.error(err);
    return cb(`${err}`, true);
  }
};
