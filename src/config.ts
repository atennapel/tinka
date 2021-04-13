export interface Config {
  debug: boolean;
  showEnvs: boolean;
  localGlue: boolean;
  unicode: boolean;
  hideImplicits: boolean;
  verifyMetaSolutions: boolean;
}
export const config: Config = {
  debug: false,
  showEnvs: false,
  localGlue: true,
  unicode: true,
  hideImplicits: true,
  verifyMetaSolutions: true,
};
export const setConfig = (c: Partial<Config>) => {
  for (let k in c) (config as any)[k] = (c as any)[k];
};

export const log = (msg: () => any) => {
  if (config.debug) console.log(msg());
};
