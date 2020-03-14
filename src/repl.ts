import { log, setConfig, config } from './config';
import { showTerm, showDefs } from './surface';
import { parseDefs, parse, ImportMap } from './parser';
import { loadFile } from './utils/util';
import * as C from './core/syntax';
import * as CT from './core/typecheck';
import * as CD from './core/domain';
import { Nil } from './utils/list';

const help = `
EXAMPLES
identity = \\{t : *} (x : t). x
zero = \\{t} z s. z : {t : *} -> t -> (t -> t) -> t

COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showEnvs or :showenvs] toggle showing environments in debug log messages
[:def definitions] define names
[:import files] import a file
[:view files] view a file
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
    if (_s.startsWith(':def') || _s.startsWith(':import')) {
      const rest = _s.slice(1);
      parseDefs(rest, importMap).then(ds => {
        return _cb(showDefs(ds));
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
    if (_s.startsWith(':')) return _cb('invalid command', true);
    const t = parse(_s);
    const tstr = showTerm(t);
    log(() => tstr);
    const core = C.fromSurface(t);
    const corestr = C.showTerm(core);
    log(() => corestr);
    const type = CT.typecheck(core);
    const typestr = CD.showTermQ(type);
    log(() => typestr);
    const typn = CD.quote(type, 0, true);
    const typnstr = C.showTerm(typn);
    log(() => typnstr);
    const norm = CD.normalize(core, Nil, 0, false);
    const normstr = C.showTerm(norm);
    log(() => normstr);
    const norf = CD.normalize(core, Nil, 0, true);
    const norfstr = C.showTerm(norf);
    log(() => norfstr);
    return _cb(`term: ${tstr}\ncore: ${corestr}\ntype: ${typestr}\ntypn: ${typnstr}\nnorm: ${normstr}\nnorf: ${norfstr}`);
  } catch (err) {
    log(() => ''+err);
    return _cb(err, true);
  }
};
