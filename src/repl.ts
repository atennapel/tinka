import { log, setConfig, config } from './config';
import { showTerm } from './surface';
import { parseDefs, parse, ImportMap } from './parser';
import { loadFile } from './utils/util';
import * as C from './core/syntax';
import * as CT from './core/typecheck';
import * as CD from './core/domain';
import { Nil } from './utils/list';
import { globalDelete, globalMap, globalGet } from './globalenv';
import { showTermSZ, normalize } from './domain';
import { showTerm as showTermI, showSurfaceZ, Term } from './syntax';
import { typecheck, typecheckDefs } from './typecheck';
import * as P from './pure/syntax';
import * as PD from './pure/domain';

const help = `
EXAMPLES
identity = \\{t : *} (x : t). x
zero = \\{t} z s. z : {t : *} -> t -> (t -> t) -> t

COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showEnvs or :showenvs] toggle showing environments in debug log messages
[:checkCore or :checkcore] toggle rechecking of core terms
[:quoteLevel n] how much to normalize
[:alwaysUnfold x y z] always unfold names
[:def definitions] define names
[:defs] show all defs
[:del name] delete a name
[:import files] import a file
[:view files] view a file
[:gtypec name] view the core type of a name
[:gtypenormc name] view the fully normalized core type of a name
[:gelabc name] view the core elaborated term of a name
[:gtermc name] view the core term of a name
[:gnormc name] view the fully normalized core term of a name
[:gtype name] view the fully normalized type of a name
[:gelab name] view the elaborated term of a name
[:gterm name] view the term of a name
[:gnorm name] view the fully normalized term of a name
[:t term] or [:type term] show the type of an expressions
[:core term] also typecheck core term
`.trim();

let importMap: ImportMap = {};

export const initREPL = () => {
  importMap = {};
  setConfig({ quoteLevel: Infinity });
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
    if (_s.toLowerCase() === ':checkcore') {
      setConfig({ checkCore: !config.checkCore });
      return _cb(`checkCore: ${config.checkCore}`);
    }
    if (_s.toLowerCase().startsWith(':quotelevel')) {
      const n = _s.slice(11);
      const m = +n;
      if (isNaN(m)) return _cb(`invalid quoteLevel: ${n}`, true);
      setConfig({ quoteLevel: m });
      return _cb(`quoteLevel: ${config.quoteLevel}`);
    }
    if (_s.toLowerCase().startsWith(':alwaysunfold')) {
      let rest = _s.slice(13).trim();
      let add = false;
      if (rest[0] === '+') {
        add = true;
        rest = rest.slice(1);
      }
      const names = rest.split(/\s+/g);
      setConfig({ alwaysUnfold: add ? config.alwaysUnfold.concat(names) : names });
      return _cb(`alwaysUnfold: ${config.alwaysUnfold.join(' ')}`);
    }
    if (_s === ':defs') {
      const e = globalMap();
      const msg = Object.keys(e).map(k => `def ${k} : ${showTermSZ(e[k].type)} = ${showSurfaceZ(e[k].term)} ~> ${P.showTerm(e[k].pure)}`).join('\n');
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
    if (_s.startsWith(':gtypenormc')) {
      const name = _s.slice(11).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(C.showTerm(CD.quote(res.coretype, 0, true)));
    }
    if (_s.startsWith(':gtypec')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(C.showTerm(CD.quote(res.coretype, 0, false)));
    }
    if (_s.startsWith(':gtype')) {
      const name = _s.slice(6).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(showTermSZ(res.type, Nil, Nil, 0, Infinity));
    }
    if (_s.startsWith(':gelabc')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(C.showTerm(res.coreterm));
    }
    if (_s.startsWith(':gelab')) {
      const name = _s.slice(6).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      log(() => showTermI(res.term));
      return _cb(showSurfaceZ(res.term));
    }
    if (_s.startsWith(':gtermc')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(C.showTerm(CD.quote(res.coreval, 0, false)));
    }
    if (_s.startsWith(':gterm')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(showTermSZ(res.val));
    }
    if (_s.startsWith(':gnormc')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(C.showTerm(CD.quote(res.coreval, 0, true)));
    }
    if (_s.startsWith(':gnorm')) {
      const name = _s.slice(7).trim();
      const res = globalGet(name);
      if (!res) return _cb(`undefined global: ${name}`, true);
      return _cb(showTermSZ(res.val, Nil, Nil, 0, Infinity));
    }
    let typeOnly = false;
    let core = false;
    if (_s.startsWith(':t')) {
      _s = _s.slice(_s.startsWith(':type') ? 5 : 2);
      typeOnly = true;
    }
    if (_s.startsWith(':core')) {
      _s = _s.slice(5);
      core = true;
    }
    if (_s.startsWith(':')) return _cb('invalid command', true);
    let msg = '';
    let tm_: Term;
    let tmc_: C.Term | null = null;
    let cty_: C.Term | null = null;
    try {
      const t = parse(_s);
      log(() => showTerm(t));
      const [ztm, vty] = typecheck(t);
      tm_ = ztm;
      log(() => showTermSZ(vty));
      log(() => showSurfaceZ(tm_));
      msg += `type: ${showTermSZ(vty)}\nterm: ${showSurfaceZ(tm_)}`;
      if (core) {
        const ctm = C.toCore(ztm);
        tmc_ = ctm;
        log(() => C.showTerm(ctm));
        const cty = CT.typecheck(ctm);
        const ctyq = CD.quote(cty, 0, false);
        cty_ = ctyq;
        log(() => C.showTerm(ctyq));
        msg += `\nctyp: ${C.showTerm(ctyq)}\ncter: ${C.showTerm(tmc_)}`;
      }
      if (typeOnly) return _cb(msg);
    } catch (err) {
      log(() => ''+err);
      return _cb(''+err, true);
    }
    try {
      const n = normalize(tm_, Nil, 0, config.quoteLevel);
      log(() => showSurfaceZ(n));
      let pnor = '';
      let pdsp = '';
      if (core && tmc_) {
        const p = PD.normalize(P.erase(tmc_));
        pnor = `\npnor: ${P.showTerm(p)}`;
        if (cty_ && cty_.tag === 'Global') {
          // const fty = CD.normalize(cty_, Nil, 0, true);
          // TODO: check type
          if (cty_.name === 'PrimNat') {
            const g = PD.normalize(P.App(P.App(p, P.Num(0)), P.Abs(P.Inc(P.Var(0)))));
            if (g.tag === 'Num') pdsp = `\npdsp: ${g.value}`;
          } else if (cty_.name === 'PrimChar') {
            const g = PD.normalize(P.App(P.App(p, P.Num(0)), P.Abs(P.Inc(P.Var(0)))));
            if (g.tag === 'Num') pdsp = `\npdsp: ${JSON.stringify(String.fromCodePoint(g.value))}`;
          } else if (cty_.name === 'PrimStr') {
            const g = PD.normalize(P.App(P.App(p, P.Num(0)), P.Abs(P.Pair(P.App(P.App(P.Var(1), P.Num(0)), P.Abs(P.Inc(P.Var(0)))), P.Var(0)))));
            const cp: number[] = [];
            let c = g;
            while (c.tag === 'Pair') {
              if (c.fst.tag === 'Num') cp.push(c.fst.value);
              c = c.snd;
            }
            pdsp = `\npdsp: ${JSON.stringify(String.fromCodePoint(...cp))}`;
          }
        }
      }
      return _cb(`${msg}\nnorm: ${showSurfaceZ(n)}${core && tmc_ ? `\ncnor: ${C.showTerm(CD.normalize(tmc_, Nil, 0, true))}${pnor}${pdsp}` : ''}`);
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
