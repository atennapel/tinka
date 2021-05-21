import { initREPL, runREPL } from './repl';
import { log, setConfig } from './config';
import { show, showCore } from './surface';
import { parse } from './parser';
import { elaborate } from './elaboration';
import { verify } from './verification';
import { normalize } from './values';
import { nil } from './utils/List';
import { show as showCoreSimple } from './core';

if (process.argv[2]) {
  const option = process.argv[3] || '';
  let typeOnly = false;
  let showCore_ = false;
  let doVerify = true;
  if (option.includes('d')) setConfig({ debug: true });
  if (option.includes('e')) setConfig({ showEnvs: true });
  if (option.includes('g')) setConfig({ localGlue: false });
  if (option.includes('u')) setConfig({ unicode: false });
  if (option.includes('i')) setConfig({ hideImplicits: false });
  if (option.includes('m')) setConfig({ verifyMetaSolutions: false });
  if (option.includes('p')) setConfig({ postpone: false });
  if (option.includes('t')) typeOnly = true;
  if (option.includes('c')) showCore_ = true;
  if (option.includes('l')) doVerify = false;
  try {
    const sc = require('fs').readFileSync(process.argv[2], 'utf8');
    log(() => `PARSE`);
    const e = parse(sc);
    console.log(show(e));
    log(() => `ELABORATE`);
    const [tm, ty] = elaborate(e);
    if (showCore_) {
      console.log(showCoreSimple(tm));
      console.log(showCoreSimple(ty));
    }
    console.log(showCore(tm));
    console.log(showCore(ty));
    if (doVerify) {
      log(() => `VERIFY`);
      const ty = verify(tm);
      log(() => `verified type: ${showCore(ty)}`);
    }
    if (!typeOnly) {
      console.log(showCore(normalize(tm, 0, nil, true)));
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
  initREPL(false);
  _input();
}
