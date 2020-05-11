import { Name } from './names';

export interface Config {
  debug: boolean;
  showEnvs: boolean;
  quoteLevel: number;
  alwaysUnfold: Name[];
  showNormalization: boolean;
}
export const config: Config = {
  debug: false,
  showEnvs: false,
  quoteLevel: 0,
  alwaysUnfold: [],
  showNormalization: false,
};
export const setConfig = (c: Partial<Config>) => {
  for (let k in c) (config as any)[k] = (c as any)[k];
};

export const log = (msg: () => any) => {
  if (config.debug) console.log(msg());
};
