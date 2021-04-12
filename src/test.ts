import { elaborate } from './elaboration';
import { parse } from './parser';

let total = 0;
let failed = 0;

const mustGiveTypeError = (s: string): void => {
  total++;
  try {
    const e = parse(s);
    elaborate(e);
  } catch (err) {
    if (err instanceof TypeError) return;
    failed++;
    console.log(`expected type error for (${s}), but got ${err}`);
    return;
  }
  console.log(`expected type error for (${s}), but got no error`);
  failed++;
};

// meta solving should not put erased var in non-erased position
mustGiveTypeError(`\\(-A : *) (x : A). (\\{B : *} (y : B). B) x`);

console.log(`${total} tests done, ${failed} failed`);
