import { initREPL, runREPL } from './repl';
import { setConfig } from './config';
import { show, showCore } from './surface';
import { parse } from './parser';
import { elaborate } from './elaboration';
import { typecheck } from './typecheck';
import { normalize } from './values';
import { nil } from './utils/List';
import { show as showCoreSimple } from './core';
import { Erased, show as showE } from './erased';
import * as EV from './erasedvalues';

if (process.argv[2]) {
  const option = process.argv[3] || '';
  let typeOnly = false;
  let showCore_ = false;
  let verify = true;
  if (option.includes('d')) setConfig({ debug: true });
  if (option.includes('e')) setConfig({ showEnvs: true });
  if (option.includes('t')) typeOnly = true;
  if (option.includes('c')) showCore_ = true;
  if (option.includes('l')) verify = false;
  try {
    const sc = require('fs').readFileSync(process.argv[2], 'utf8');
    const e = parse(sc);
    console.log(show(e));
    const [tm, ty] = elaborate(e);
    if (showCore_) {
      console.log(showCoreSimple(tm));
      console.log(showCoreSimple(ty));
    }
    console.log(showCore(tm));
    console.log(showCore(ty));
    let er: Erased | null = null;
    if (verify) {
      [, er] = typecheck(tm);
      console.log(showE(er));
    }
    if (!typeOnly) {
      console.log(showCore(normalize(tm, 0, nil, true)));
      if (verify && er) {
        const ernorm = EV.normalize(er);
        console.log(showE(ernorm));
      }
    }
  } catch(err) {
    console.error(err);
    process.exit();
  }
} else {
  const _readline = require('readline').createInterface(process.stdin, process.stdout);
  console.log('tinka repl');
  process.stdin.setEncoding('utf8');
  function _input() {
    _readline.question('> ', function(_i: string) {
      runREPL(_i, (s: string, _e?: boolean) => {
        console.log(s);
        setImmediate(_input, 0);
      });
    });
  };
  initREPL();
  _input();
}
