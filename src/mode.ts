export type Erasure = boolean;

export type Mode = Expl | Impl;

export interface Expl { readonly tag: 'Expl' };
export const Expl: Mode = { tag: 'Expl' };
export interface Impl { readonly tag: 'Impl' };
export const Impl: Mode = { tag: 'Impl' };

export const eqMode = (a: Mode, b: Mode): boolean => a.tag === b.tag;
