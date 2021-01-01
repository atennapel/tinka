export type Mode = Expl | Impl;

export interface Expl { readonly tag: 'Expl' };
export const Expl: Expl = { tag: 'Expl' };
export interface Impl { readonly tag: 'Impl' };
export const Impl: Impl = { tag: 'Impl' };
