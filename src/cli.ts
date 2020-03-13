import { parseDefs } from './parser';
import { initREPL, runREPL } from './repl';
import { setConfig } from './config';
import { showDefs } from './surface';

if (process.argv[2]) {
  const option = process.argv[3];
  if (option === '-d') setConfig({ debug: true, showEnvs: true });
  try {
    const sc = require('fs').readFileSync(process.argv[2], 'utf8');
    parseDefs(sc, {}).then(ds => {
      console.log(showDefs(ds));
      process.exit();
    }).catch(err => {
      console.error(err);
      process.exit();
    });
  } catch(err) {
    console.error(err);
    process.exit();
  };
} else {
  const _readline = require('readline').createInterface(process.stdin, process.stdout);
  console.log('tinka repl');
  process.stdin.setEncoding('utf8');
  function _input() {
    _readline.question('> ', function(_i: string) {
      runREPL(_i, (s: string, e?: boolean) => {
        console.log(s);
        setImmediate(_input, 0);
      });
    });
  };
  initREPL();
  _input();
}
