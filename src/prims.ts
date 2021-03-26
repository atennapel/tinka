export type PrimConName = '*';
export type PrimElimName = never;
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = ['*'];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const isPrimErased = (name: PrimName): boolean => true;
