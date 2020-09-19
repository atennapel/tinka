import { log, setConfig, config } from './config';
import { showTerm } from './surface';
import { parse, ImportMap, parseDefs } from './parser';
import { globalMap, globalDelete, globalGet } from './globalenv';
import { loadFile } from './utils/utils';
import { showTermSZ, quoteZ, normalize } from './domain';
import { showSurfaceZ, showTerm as showTermI, Term, toSurface } from './syntax';
import { Nil } from './utils/list';
import { typecheckDefs, typecheck } from './typecheck';
import { verify } from './verify';
import * as E from './erased';
import * as ED from './domainErased';
import * as S from './surface';

const help = `
COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showEnvs or :showenvs] toggle showing environments in debug log messages
[:showNorm or :shownorm] toggle showing normalization
[:def definitions] define names
[:defs] show all defs
[:del name] delete a name
[:import files] import a file
[:view files] view a file
[:gtype name] view the fully normalized type of a name
[:gelab name] view the elaborated term of a name
[:gterm name] view the term of a name
[:gnorm name] view the fully normalized term of a name
[:geras name] view erased term of a name
[:genor name] view normalized erased term of a name
[:t term] or [:type term] show the type of an expressions
[:verify term] verify elaborated output
`.trim();

let importMap: ImportMap = {};

export const initREPL = () => {
  importMap = {};
};

export const runREPL = (_s: string, _cb: (msg: string, err?: boolean) => void) => {
  try {
    _s = _s.trim();
    if (_s === ':help' || _s === ':h')
      return _cb(help);
    if (_s === ':debug' || _s === ':d') {
      setConfig({ debug: !config.debug });
      return _cb(`debug: ${config.debug}`);
    }
    if (_s.toLowerCase() === ':showenvs') {
      setConfig({ showEnvs: !config.showEnvs });
      return _cb(`showEnvs: ${config.showEnvs}`);
    }
    if (_s.toLowerCase() === ':shownorm') {
      setConfig({ showNormalization: !config.showNormalization });
      return _cb(`showNormalization: ${config.showNormalization}`);
    }
    if (_s === ':defs') {
      const e = globalMap();
      const msg = Object.keys(e).map(k => `def ${k} : ${showTermSZ(e[k].type)} = ${showSurfaceZ(e[k].term)}`).join('\n');
      return _cb(msg || 'no definitions');
    }
    if (_s.startsWith(':del')) {
      const name = _s.slice(4).trim();
      globalDelete(name);
      return _cb(`deleted ${name}`);
    }
    if (_s.startsWith(':def') || _s.startsWith(':import')) {
      const rest = _s.slice(1);
      parseDefs(rest, importMap).then(ds => {
        const xs = typecheckDefs(ds, true);
        return _cb(`defined ${xs.join(' ')}`);
      }).catch(err => _cb(''+err, true));
      return;
    }
    if (_s.startsWith(':view')) {
      const files = _s.slice(5).trim().split(/\s+/g);
      Promise.all(files.map(loadFile)).then(ds => {
        return _cb(ds.join('\n\n'));
      }).catch(err => _cb(''+err, true));
      return;
    }
    if (_s.startsWith(':gtype')) {
      const name = _s.slice(6).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(showTermSZ(res.type, Nil, Nil, 0, true));
    }
    if (_s.startsWith(':gelab')) {
      const name = _s.slice(6).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      log(() => showTermI(res.term));
      return _cb(showSurfaceZ(res.term));
    }
    if (_s.startsWith(':gterm')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(showTermSZ(res.val));
    }
    if (_s.startsWith(':gnorm')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(showTermSZ(res.val, Nil, Nil, 0, true));
    }
    if (_s.startsWith(':geras')) {
      const name = _s.slice(6).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      log(() => E.showTerm(res.erased));
      return _cb(E.showTerm(res.erased));
    }
    if (_s.startsWith(':genor')) {
      const name = _s.slice(6).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      const nor = ED.normalize(res.erased);
      log(() => E.showTerm(nor));
      return _cb(E.showTerm(nor));
    }
    let typeOnly = false;
    if (_s.startsWith(':t')) {
      _s = _s.slice(_s.startsWith(':type') ? 5 : 2);
      typeOnly = true;
    }
    if (_s.startsWith(':')) return _cb('invalid command', true);
    let msg = '';
    let tm_: Term;
    let ty_: Term;
    let er_: E.Term;
    try {
      const t = parse(_s);
      log(() => showTerm(t));
      const [ztm, vty] = typecheck(t);
      tm_ = ztm;
      ty_ = quoteZ(vty);
      log(() => showTermSZ(vty));
      log(() => showSurfaceZ(tm_));
      log(() => S.showTerm(S.erase(toSurface(normalize(tm_, Nil, 0, true)))));
      msg += `type: ${showTermSZ(vty)}\nterm: ${showSurfaceZ(tm_)}`;
      er_ = verify(ztm)[1];
      msg += `\neras: ${E.showTerm(er_)}`;
      if (typeOnly) return _cb(msg);
    } catch (err) {
      log(() => ''+err);
      return _cb(''+err, true);
    }
    try {
      const n = ED.normalize(er_);
      log(() => E.showTermS(n));
      log(() => E.showTerm(n));
      let norm: string = '';
      if (ty_.tag === 'Global' && ty_.name === 'Showable') {
        throw new Error('unimplemented Showable');
        /*
        let c = n;
        const r: number[] = [];
        while (c.tag === 'App' && c.left.tag === 'Prim' && c.left.name === 'IIn') {
          const p = c.right as E.Pair;
          if (p.fst.tag === 'Prim' && p.fst.name === 'True') break;
          const d = p.snd as E.Pair;
          let m = d.fst;
          let i = 0;
          while(m.tag === 'App' && m.left.tag === 'Prim' && m.left.name === 'IIn') {
            const inner = m.right as E.Pair;
            if (inner.fst.tag === 'Prim' && inner.fst.name === 'True') break;
            i++;
            m = inner.snd;
          }
          r.push(i);
          c = d.snd;
        }
        norm = String.fromCodePoint.apply(null, r);*/
      } else norm = E.showTerm(n);
      return _cb(`${msg}${config.showNormalization ? `\nnorm: ${norm}` : ''}`);
    } catch (err) {
      log(() => ''+err);
      msg += '\n'+err;
      return _cb(msg, true);
    }
  } catch (err) {
    log(() => ''+err);
    return _cb(err, true);
  }
};
