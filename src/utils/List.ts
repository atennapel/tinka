export abstract class List<T> {

  private static _Nil: List<never>;
  static Nil(): List<never> {
    if (List._Nil === undefined)
      List._Nil = new Nil();
    return List._Nil;
  }
  static Cons<T>(head: T, tail: List<T>): List<T> { return new Cons(head, tail) }

  static from<T>(values: T[]): List<T> {
    let l: List<T> = List.Nil();
    for (let i = values.length - 1; i >= 0; i--)
      l = List.Cons(values[i], l);
    return l;
  }
  static of<T>(...values: T[]): List<T> { return List.from(values) }

  static range(n: number): List<number> {
    let l: List<number> = List._Nil;
    for (let i = 0; i < n; i++) l = List.Cons(i, l);
    return l;
  }

  abstract isNil(): this is Nil;
  abstract isCons(): this is Cons<T>;

  toString(fn: (val: T) => string = val => `${val}`): string {
    return `[${this.toMappedArray(fn).join(', ')}]`;
  }

  abstract toMappedArray<R>(fn: (val: T) => R): R[];
  abstract toArray(): T[];
  abstract map<R>(fn: (val: T) => R): List<R>;
  abstract each(fn: (val: T) => void): void;
  abstract index(ix: number): T | null;

  abstract findIndex(fn: (val: T) => boolean): number;
  abstract find(fn: (val: T) => boolean): T | null;

  abstract indexOf(val: T): number;
  contains(val: T): boolean { return this.indexOf(val) >= 0 }

  abstract reverse(): List<T>;

  abstract zip<R>(o: List<R>): List<[T, R]>;
  abstract zipWith<R, U>(o: List<R>, fn: (a: T, b: R) => U): List<U>;
  abstract zipWith_<R>(o: List<R>, fn: (a: T, b: R) => void): void;

}

export class Nil extends List<never> {

  isNil(): this is Nil { return true }
  isCons(): this is Cons<never> { return false }

  toString(): string { return '[]' }
  toMappedArray(): never[] { return [] }
  toArray(): never[] { return [] }
  map(): List<never> { return this }
  each(): void {}
  index(): null { return null }

  findIndex(): number { return -1 }
  find(): null { return null }

  indexOf(): number { return -1 }
  contains(): boolean { return false }

  reverse(): List<never> { return this }

  zip<R>(): List<[never, R]> { return this }
  zipWith<U>(): List<U> { return this }
  zipWith_(): void {}

}

export class Cons<T> extends List<T> {

  readonly head: T;
  readonly tail: List<T>;

  constructor(head: T, tail: List<T>) {
    super();
    this.head = head;
    this.tail = tail;
  }

  isNil(): this is Nil { return false }
  isCons(): this is Cons<T> { return true }

  toMappedArray<R>(fn: (val: T) => R): R[] {
    const r: R[] = [];
    let c: List<T> = this;
    while (c.isCons()) {
      r.push(fn(c.head));
      c = c.tail;
    }
    return r;
  }
  toArray(): T[] {
    const r: T[] = [];
    let c: List<T> = this;
    while (c.isCons()) {
      r.push(c.head);
      c = c.tail;
    }
    return r;
  }

  map<R>(fn: (val: T) => R): List<R> {
    return new Cons(fn(this.head), this.tail.map(fn));
  }
  each(fn: (val: T) => void): void {
    let c: List<T> = this;
    while (c.isCons()) {
      fn(c.head);
      c = c.tail;
    }
  }

  index(ix: number): T | null {
    if (ix <= 0) return this.head;
    let i = ix;
    let c: List<T> = this;
    while (c.isCons()) {
      if (i <= 0) return c.head;
      c = c.tail;
      i--;
    }
    return null;
  }

  findIndex(fn: (val: T) => boolean): number {
    let i = 0;
    let c: List<T> = this;
    while (c.isCons()) {
      if (fn(c.head)) return i;
      c = c.tail;
      i++;
    }
    return -1;
  }
  find(fn: (val: T) => boolean): T | null {
    let c: List<T> = this;
    while (c.isCons()) {
      if (fn(c.head)) return c.head;
      c = c.tail;
    }
    return null;
  }

  indexOf(val: T): number {
    let i = 0;
    let c: List<T> = this;
    while (c.isCons()) {
      if (c.head === val) return i;
      c = c.tail;
      i++;
    }
    return -1;
  }

  reverse(): List<T> {
    let c: List<T> = this;
    let r: List<T> = List.Nil();
    while (c.isCons()) {
      r = new Cons(c.head, r);
      c = c.tail;
    }
    return r;
  }

  zip<R>(o: List<R>): List<[T, R]> {
    let a: List<T> = this;
    let b: List<R> = o;
    let r: List<[T, R]> = List.Nil();
    while (a.isCons() && b.isCons()) {
      r = new Cons([a.head, b.head], r);
      a = a.tail;
      b = b.tail;
    }
    return r;
  }
  zipWith<R, U>(o: List<R>, fn: (a: T, b: R) => U): List<U> {
    let a: List<T> = this;
    let b: List<R> = o;
    let r: List<U> = List.Nil();
    while (a.isCons() && b.isCons()) {
      r = new Cons(fn(a.head, b.head), r);
      a = a.tail;
      b = b.tail;
    }
    return r;
  }
  zipWith_<R>(o: List<R>, fn: (a: T, b: R) => void): void {
    let a: List<T> = this;
    let b: List<R> = o;
    while (a.isCons() && b.isCons()) {
      fn(a.head, b.head);
      a = a.tail;
      b = b.tail;
    }
  }

}
