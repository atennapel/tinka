(function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.log = exports.setConfig = exports.config = void 0;
exports.config = {
    debug: false,
    showEnvs: false,
    localGlue: true,
    unicode: true,
    hideImplicits: true,
    verifyMetaSolutions: true,
    postpone: true,
};
const setConfig = (c) => {
    for (let k in c)
        exports.config[k] = c[k];
};
exports.setConfig = setConfig;
const log = (msg) => {
    if (exports.config.debug)
        console.log(msg());
};
exports.log = log;

},{}],2:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.subst = exports.substVar = exports.shift = exports.show = exports.showProjType = exports.flattenProj = exports.flattenPair = exports.flattenApp = exports.flattenAbs = exports.flattenSigma = exports.flattenPi = exports.Unit = exports.Type = exports.PIndex = exports.PSnd = exports.PFst = exports.PProj = exports.InsertedMeta = exports.Meta = exports.Proj = exports.Pair = exports.Sigma = exports.App = exports.Abs = exports.Pi = exports.Let = exports.SymbolLit = exports.Prim = exports.Global = exports.Var = void 0;
const config_1 = require("./config");
const utils_1 = require("./utils/utils");
const Var = (index) => ({ tag: 'Var', index });
exports.Var = Var;
const Global = (name) => ({ tag: 'Global', name });
exports.Global = Global;
const Prim = (name) => ({ tag: 'Prim', name });
exports.Prim = Prim;
const SymbolLit = (name) => ({ tag: 'SymbolLit', name });
exports.SymbolLit = SymbolLit;
const Let = (erased, name, type, val, body) => ({ tag: 'Let', erased, name, type, val, body });
exports.Let = Let;
const Pi = (erased, mode, name, type, body) => ({ tag: 'Pi', erased, mode, name, type, body });
exports.Pi = Pi;
const Abs = (erased, mode, name, type, body) => ({ tag: 'Abs', erased, mode, name, type, body });
exports.Abs = Abs;
const App = (fn, mode, arg) => ({ tag: 'App', fn, mode, arg });
exports.App = App;
const Sigma = (erased, name, type, body) => ({ tag: 'Sigma', erased, name, type, body });
exports.Sigma = Sigma;
const Pair = (fst, snd, type) => ({ tag: 'Pair', fst, snd, type });
exports.Pair = Pair;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const Meta = (id) => ({ tag: 'Meta', id });
exports.Meta = Meta;
const InsertedMeta = (id, spine) => ({ tag: 'InsertedMeta', id, spine });
exports.InsertedMeta = InsertedMeta;
const PProj = (proj) => ({ tag: 'PProj', proj });
exports.PProj = PProj;
exports.PFst = exports.PProj('fst');
exports.PSnd = exports.PProj('snd');
const PIndex = (name, index) => ({ tag: 'PIndex', name, index });
exports.PIndex = PIndex;
exports.Type = exports.Prim('*');
exports.Unit = exports.Prim('[]');
const flattenPi = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Pi') {
        params.push([c.erased, c.mode, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenPi = flattenPi;
const flattenSigma = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Sigma') {
        params.push([c.erased, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenSigma = flattenSigma;
const flattenAbs = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Abs') {
        params.push([c.erased, c.mode, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenAbs = flattenAbs;
const flattenApp = (t) => {
    const args = [];
    let c = t;
    while (c.tag === 'App') {
        args.push([c.mode, c.arg]);
        c = c.fn;
    }
    return [c, args.reverse()];
};
exports.flattenApp = flattenApp;
const flattenPair = (t) => {
    const ps = [];
    let c = t;
    while (c.tag === 'Pair') {
        ps.push(c.fst);
        c = c.snd;
    }
    return [ps, c];
};
exports.flattenPair = flattenPair;
const flattenProj = (t) => {
    const r = [];
    while (t.tag === 'Proj') {
        r.push(t.proj);
        t = t.term;
    }
    return [t, r.reverse()];
};
exports.flattenProj = flattenProj;
const showP = (b, t) => b ? `(${exports.show(t)})` : exports.show(t);
const isSimple = (t) => t.tag === 'Var' || t.tag === 'SymbolLit' || t.tag === 'Global' || t.tag === 'Prim' || t.tag === 'Meta' || t.tag === 'InsertedMeta' || t.tag === 'Pair' || t.tag === 'Proj';
const showS = (t) => showP(!isSimple(t), t);
const showProjType = (p) => {
    if (p.tag === 'PProj')
        return p.proj === 'fst' ? '_1' : '_2';
    if (p.tag === 'PIndex')
        return p.name ? `${p.name}/${p.index}` : `${p.index}`;
    return p;
};
exports.showProjType = showProjType;
const show = (t) => {
    if (t.tag === 'Var')
        return `'${t.index}`;
    if (t.tag === 'Global')
        return `${t.name}`;
    if (t.tag === 'Prim')
        return t.name === '*' && config_1.config.unicode ? '★' : `${t.name}`;
    if (t.tag === 'SymbolLit')
        return `'${t.name}`;
    if (t.tag === 'Meta')
        return `?${t.id}`;
    if (t.tag === 'InsertedMeta')
        return `?*${t.id}${t.spine.reverse().toString(([m, b]) => `${m.tag === 'Expl' ? '' : '{'}${b ? 'b' : 'd'}${m.tag === 'Expl' ? '' : '}'}`)}`;
    if (t.tag === 'Pi') {
        const [params, ret] = exports.flattenPi(t);
        const arr = config_1.config.unicode ? '→' : '->';
        return `${params.map(([e, m, x, t]) => !e && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${e ? '-' : ''}${x} : ${exports.show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(` ${arr} `)} ${arr} ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
    }
    if (t.tag === 'Abs') {
        const [params, body] = exports.flattenAbs(t);
        return `${config_1.config.unicode ? 'λ' : '\\'}${params.map(([e, m, x, t]) => `${m.tag === 'Impl' ? '{' : '('}${e ? '-' : ''}${x} : ${exports.show(t)}${m.tag === 'Impl' ? '}' : ')'}`).join(' ')}. ${exports.show(body)}`;
    }
    if (t.tag === 'App') {
        const [fn, args] = exports.flattenApp(t);
        return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${exports.show(a)}}`).join(' ')}`;
    }
    if (t.tag === 'Sigma') {
        const [params, ret] = exports.flattenSigma(t);
        const prod = config_1.config.unicode ? '×' : '**';
        return `${params.map(([e, x, t]) => !e && x === '_' ? showP(t.tag === 'Sigma' || t.tag === 'Pi' || t.tag === 'Let', t) : `(${e ? '-' : ''}${x} : ${exports.show(t)})`).join(` ${prod} `)} ${prod} ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
    }
    if (t.tag === 'Pair') {
        const [ps, ret] = exports.flattenPair(t);
        if (ret.tag === 'Prim' && ret.name === '[]')
            return `[${ps.map(exports.show).join(', ')}] : ${exports.show(t.type)}`;
        return `(${ps.map(exports.show).join(', ')}, ${exports.show(ret)}) : ${exports.show(t.type)}`;
    }
    if (t.tag === 'Let')
        return `let ${t.erased ? '-' : ''}${t.name} : ${showP(t.type.tag === 'Let', t.type)} = ${showP(t.val.tag === 'Let', t.val)}; ${exports.show(t.body)}`;
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(exports.showProjType).join('.')}`;
    }
    return t;
};
exports.show = show;
const shift = (d, c, t) => {
    if (t.tag === 'Var')
        return t.index < c ? t : exports.Var(t.index + d);
    if (t.tag === 'App')
        return exports.App(exports.shift(d, c, t.fn), t.mode, exports.shift(d, c, t.arg));
    if (t.tag === 'Abs')
        return exports.Abs(t.erased, t.mode, t.name, exports.shift(d, c, t.type), exports.shift(d, c + 1, t.body));
    if (t.tag === 'Pair')
        return exports.Pair(exports.shift(d, c, t.fst), exports.shift(d, c, t.snd), exports.shift(d, c, t.type));
    if (t.tag === 'Proj')
        return exports.Proj(exports.shift(d, c, t.term), t.proj);
    if (t.tag === 'Let')
        return exports.Let(t.erased, t.name, exports.shift(d, c, t.type), exports.shift(d, c, t.val), exports.shift(d, c + 1, t.body));
    if (t.tag === 'Pi')
        return exports.Pi(t.erased, t.mode, t.name, exports.shift(d, c, t.type), exports.shift(d, c + 1, t.body));
    if (t.tag === 'Sigma')
        return exports.Sigma(t.erased, t.name, exports.shift(d, c, t.type), exports.shift(d, c + 1, t.body));
    if (t.tag === 'InsertedMeta')
        return utils_1.impossible(`InsertedMeta in shift`);
    return t;
};
exports.shift = shift;
const substVar = (j, s, t) => {
    if (t.tag === 'Var')
        return t.index === j ? s : t;
    if (t.tag === 'App')
        return exports.App(exports.substVar(j, s, t.fn), t.mode, exports.substVar(j, s, t.arg));
    if (t.tag === 'Abs')
        return exports.Abs(t.erased, t.mode, t.name, exports.substVar(j, s, t.type), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'Pair')
        return exports.Pair(exports.substVar(j, s, t.fst), exports.substVar(j, s, t.snd), exports.substVar(j, s, t.type));
    if (t.tag === 'Proj')
        return exports.Proj(exports.substVar(j, s, t.term), t.proj);
    if (t.tag === 'Let')
        return exports.Let(t.erased, t.name, exports.substVar(j, s, t.type), exports.substVar(j, s, t.val), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'Pi')
        return exports.Pi(t.erased, t.mode, t.name, exports.substVar(j, s, t.type), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'Sigma')
        return exports.Sigma(t.erased, t.name, exports.substVar(j, s, t.type), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'InsertedMeta')
        return utils_1.impossible(`InsertedMeta in substVar`);
    return t;
};
exports.substVar = substVar;
const subst = (t, u) => exports.shift(-1, 0, exports.substVar(0, exports.shift(1, 0, u), t));
exports.subst = subst;

},{"./config":1,"./utils/utils":16}],3:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.elaborate = void 0;
const core_1 = require("./core");
const local_1 = require("./local");
const metas_1 = require("./metas");
const surface_1 = require("./surface");
const List_1 = require("./utils/List");
const values_1 = require("./values");
const S = require("./surface");
const C = require("./core");
const config_1 = require("./config");
const utils_1 = require("./utils/utils");
const unification_1 = require("./unification");
const globals_1 = require("./globals");
const mode_1 = require("./mode");
const prims_1 = require("./prims");
const showV = (local, val) => S.showVal(val, local.level, false, local.ns);
const closeTy = (path, ty) => path.foldl((rest, [e, m, x, ty, val]) => val ? core_1.Let(e, x, ty, val, rest) : core_1.Pi(e, m, x, ty, rest), ty);
const newMeta = (local, ty, erased = false) => {
    if (values_1.isVUnitType(values_1.force(ty))) {
        config_1.log(() => `short circuit meta with unit type`);
        return C.Unit;
    }
    const qtype = closeTy(local.path, values_1.quote(ty, local.level));
    const type = values_1.evaluate(qtype, List_1.nil);
    const id = metas_1.freshMeta(type, erased || local.erased); // is this erasure correct?
    config_1.log(() => `newMeta ?${id} : ${showV(local_1.Local.empty(), type)}`);
    const bds = local.ts.map(e => [e.mode, e.bound]);
    const meta = core_1.InsertedMeta(id, bds);
    return meta;
};
const inst = (local, ty_) => {
    const ty = values_1.force(ty_);
    if (ty.tag === 'VPi' && ty.mode.tag === 'Impl') {
        const m = newMeta(local, ty.type, ty.erased);
        const vm = values_1.evaluate(m, local.vs);
        const [res, args] = inst(local, values_1.vinst(ty, vm));
        return [res, List_1.cons(m, args)];
    }
    return [ty_, List_1.nil];
};
let postponed = [];
const postpone = (m, local, tm, ty, res) => {
    config_1.log(() => `postpone for ?${m}`);
    const problem = [m, local, tm, ty, res];
    postponed.push(problem);
    metas_1.registerMetaCallback(m, () => {
        config_1.log(() => `try postponed problem for ?${m}`);
        const p = check(local, tm, ty);
        unification_1.unify(local.level, res, values_1.evaluate(p, local.vs));
        const i = postponed.findIndex(x => x === problem);
        if (i >= 0)
            postponed.splice(i, 1);
    });
};
const tryAllPostponed = () => {
    config_1.log(() => `try all postponed problems`);
    for (let i = 0, l = postponed.length; i < l; i++) {
        const [m, local, tm, ty, res] = postponed[i];
        config_1.log(() => `try postponed problem for ?${m}`);
        const p = check(local, tm, ty);
        unification_1.unify(local.level, res, values_1.evaluate(p, local.vs));
        const j = postponed.findIndex(x => x === postponed[i]);
        if (j >= 0)
            postponed.splice(j, 1);
    }
    config_1.setConfig({ postpone: false });
    for (let i = 0, l = postponed.length; i < l; i++) {
        const [m, local, tm, ty, res] = postponed[i];
        config_1.log(() => `try remaining postponed problem for ?${m}`);
        const p = check(local, tm, ty);
        unification_1.unify(local.level, res, values_1.evaluate(p, local.vs));
        const j = postponed.findIndex(x => x === postponed[i]);
        if (j >= 0)
            postponed.splice(j, 1);
    }
    config_1.setConfig({ postpone: true });
};
const check = (local, tm, ty) => {
    config_1.log(() => `check ${surface_1.show(tm)} : ${showV(local, ty)}${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
    if (tm.tag === 'Hole') {
        const x = newMeta(local, ty);
        if (tm.name) {
            if (holes[tm.name])
                return utils_1.terr(`duplicate hole ${tm.name}`);
            holes[tm.name] = [values_1.evaluate(x, local.vs), ty, local];
        }
        return x;
    }
    const fty = values_1.force(ty);
    config_1.log(() => `check(full) ${surface_1.show(tm)} : ${showV(local, fty)}`);
    if (tm.tag === 'Abs' && !tm.type && fty.tag === 'VPi' && mode_1.eqMode(tm.mode, fty.mode)) {
        const v = values_1.VVar(local.level);
        const x = tm.name;
        const body = check(local.bind(fty.erased, fty.mode, x, fty.type), tm.body, values_1.vinst(fty, v));
        return core_1.Abs(fty.erased, fty.mode, x, values_1.quote(fty.type, local.level), body);
    }
    if (fty.tag === 'VPi' && fty.mode.tag === 'Impl' && tm.tag !== 'Rigid') {
        const v = values_1.VVar(local.level);
        const term = check(local.insert(true, fty.mode, fty.name, fty.type), tm, values_1.vinst(fty, v));
        return core_1.Abs(fty.erased, fty.mode, fty.name, values_1.quote(fty.type, local.level), term);
    }
    if (tm.tag === 'Pair' && fty.tag === 'VSigma') {
        const fst = check(fty.erased ? local.inType() : local, tm.fst, fty.type);
        const snd = check(local, tm.snd, values_1.vinst(fty, values_1.evaluate(fst, local.vs)));
        const qty = values_1.quote(ty, local.level);
        config_1.log(() => `quoted sigma type (${surface_1.show(tm)}): ${C.show(qty)}`);
        return core_1.Pair(fst, snd, qty);
    }
    if (config_1.config.postpone && tm.tag === 'Pair' && fty.tag === 'VFlex') {
        const m = newMeta(local, ty, local.erased);
        postpone(fty.head, local, tm, ty, values_1.evaluate(m, local.vs));
        return m;
    }
    if (tm.tag === 'Let') {
        let vtype;
        let vty;
        let val;
        if (tm.type) {
            vtype = check(local.inType(), tm.type, values_1.VType);
            vty = values_1.evaluate(vtype, local.vs);
            val = check(tm.erased ? local.inType() : local, tm.val, ty);
        }
        else {
            [val, vty] = synth(tm.erased ? local.inType() : local, tm.val);
            vtype = values_1.quote(vty, local.level);
        }
        const v = values_1.evaluate(val, local.vs);
        const body = check(local.define(tm.erased, tm.name, vty, v, vtype, val), tm.body, ty);
        return core_1.Let(tm.erased, tm.name, vtype, val, body);
    }
    const [term, ty2] = synth(local, tm.tag === 'Rigid' ? tm.term : tm);
    const [ty2inst, ms] = tm.tag === 'Rigid' ? [ty2, List_1.nil] : inst(local, ty2);
    return utils_1.tryT(() => {
        config_1.log(() => `unify ${showV(local, ty2inst)} ~ ${showV(local, ty)}`);
        config_1.log(() => `for check ${surface_1.show(tm)} : ${showV(local, ty)}`);
        unification_1.unify(local.level, ty2inst, ty);
        return ms.foldl((a, m) => core_1.App(a, mode_1.Impl, m), term);
    }, e => utils_1.terr(`check failed (${surface_1.show(tm)}): ${showV(local, ty2)} ~ ${showV(local, ty)}: ${e}`));
};
const freshPi = (local, erased, mode, x) => {
    const a = newMeta(local, values_1.VType, true);
    const va = values_1.evaluate(a, local.vs);
    const b = newMeta(local.bind(erased, mode, '_', va), values_1.VType, true);
    return values_1.evaluate(core_1.Pi(erased, mode, x, a, b), local.vs);
};
/*
const freshSigma = (local: Local, erased: Erasure, x: Name): Val => {
  const a = newMeta(local, VType, true);
  const va = evaluate(a, local.vs);
  const b = newMeta(local.bind(erased, Expl, '_', va), VType, true);
  const sigma = Sigma(erased, x, a, b);
  return evaluate(sigma, local.vs);
};
*/
const synth = (local, tm) => {
    config_1.log(() => `synth ${surface_1.show(tm)}${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
    if (tm.tag === 'SymbolLit')
        return [C.SymbolLit(tm.name), values_1.VSymbol];
    if (tm.tag === 'Var') {
        const i = local.nsSurface.indexOf(tm.name);
        if (i < 0) {
            if (prims_1.isPrimName(tm.name)) {
                if (prims_1.isPrimErased(tm.name) && !local.erased)
                    return utils_1.terr(`erased prim used: ${surface_1.show(tm)}`);
                return [core_1.Prim(tm.name), prims_1.primType(tm.name)];
            }
            else
                utils_1.terr(`undefined variable of primitive: ${surface_1.show(tm)}`);
            utils_1.terr(`undefined variable of primitive: ${surface_1.show(tm)}`);
        }
        else {
            const [entry, j] = local_1.indexEnvT(local.ts, i) || utils_1.terr(`var out of scope ${surface_1.show(tm)}`);
            config_1.log(() => `local: ${i} ~> ${j}`);
            if (entry.erased && !local.erased)
                return utils_1.terr(`erased var used: ${surface_1.show(tm)}`);
            return [core_1.Var(j), entry.type];
        }
    }
    if (tm.tag === 'Global') {
        const entry = globals_1.loadGlobal(tm.name);
        if (!entry)
            return utils_1.terr(`global ${tm.name} not found`);
        if (entry.erased && !local.erased)
            return utils_1.terr(`erased global used: ${surface_1.show(tm)}`);
        return [core_1.Global(tm.name), entry.type];
    }
    if (tm.tag === 'App') {
        const [fn, fnty] = synth(local, tm.fn);
        const [arg, rty, ms] = synthapp(local, fnty, tm.mode, tm.arg, tm);
        return [core_1.App(ms.foldl((a, m) => core_1.App(a, mode_1.Impl, m), fn), tm.mode, arg), rty];
    }
    if (tm.tag === 'Abs') {
        if (tm.type) {
            const type = check(local.inType(), tm.type, values_1.VType);
            const ty = values_1.evaluate(type, local.vs);
            const [body, rty] = synth(local.bind(tm.erased, tm.mode, tm.name, ty), tm.body);
            const qpi = core_1.Pi(tm.erased, tm.mode, tm.name, type, values_1.quote(rty, local.level + 1));
            const pi = values_1.evaluate(qpi, local.vs);
            return [core_1.Abs(tm.erased, tm.mode, tm.name, type, body), pi];
        }
        else {
            // TODO: maybe synth here?
            const pi = freshPi(local, tm.erased, tm.mode, tm.name);
            const term = check(local, tm, pi);
            return [term, pi];
        }
    }
    if (tm.tag === 'Pi') {
        if (!local.erased)
            return utils_1.terr(`pi type in non-type context: ${surface_1.show(tm)}`);
        const type = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(type, local.vs);
        const body = check(local.inType().bind(tm.erased, tm.mode, tm.name, ty), tm.body, values_1.VType);
        const pi = core_1.Pi(tm.erased, tm.mode, tm.name, type, body);
        return [pi, values_1.VType];
    }
    if (tm.tag === 'Sigma') {
        if (!local.erased)
            return utils_1.terr(`sigma type in non-type context: ${surface_1.show(tm)}`);
        const type = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(type, local.vs);
        const body = check(local.inType().bind(tm.erased, mode_1.Expl, tm.name, ty), tm.body, values_1.VType);
        return [core_1.Sigma(tm.erased, tm.name, type, body), values_1.VType];
    }
    if (tm.tag === 'Proj') {
        const [term, sigma_] = synth(local, tm.term);
        if (tm.proj.tag === 'PProj') {
            const sigma = values_1.force(sigma_);
            if (sigma.tag !== 'VSigma')
                return utils_1.terr(`not a sigma type in ${surface_1.show(tm)}: ${showV(local, sigma_)}`);
            if (sigma.erased && tm.proj.proj === 'fst' && !local.erased)
                return utils_1.terr(`cannot project erased ${surface_1.show(tm)}: ${showV(local, sigma_)}`);
            const fst = sigma.name !== '_' ? core_1.PIndex(sigma.name, 0) : core_1.PFst; // TODO: is this nice?
            return [core_1.Proj(term, tm.proj), tm.proj.proj === 'fst' ? sigma.type : values_1.vinst(sigma, values_1.vproj(values_1.evaluate(term, local.vs), fst))];
        }
        else if (tm.proj.tag === 'PName') {
            const orig = values_1.evaluate(term, local.vs);
            const [ty, ix] = projectName(local, tm, orig, orig, sigma_, tm.proj.name, 0);
            return [core_1.Proj(term, core_1.PIndex(tm.proj.name, ix)), ty];
        }
        else
            return [core_1.Proj(term, core_1.PIndex(null, tm.proj.index)), projectIndex(local, tm, values_1.evaluate(term, local.vs), sigma_, tm.proj.index)];
    }
    if (tm.tag === 'Let') {
        let type;
        let ty;
        let val;
        if (tm.type) {
            type = check(local.inType(), tm.type, values_1.VType);
            ty = values_1.evaluate(type, local.vs);
            val = check(tm.erased ? local.inType() : local, tm.val, ty);
        }
        else {
            [val, ty] = synth(tm.erased ? local.inType() : local, tm.val);
            type = values_1.quote(ty, local.level);
        }
        const v = values_1.evaluate(val, local.vs);
        const [body, rty] = synth(local.define(tm.erased, tm.name, ty, v, type, val), tm.body);
        return [core_1.Let(tm.erased, tm.name, type, val, body), rty];
    }
    if (tm.tag === 'Hole') {
        const vt = values_1.evaluate(newMeta(local, values_1.VType, true), local.vs);
        const t = newMeta(local, vt);
        if (tm.name) {
            if (holes[tm.name])
                return utils_1.terr(`duplicate hole ${tm.name}`);
            holes[tm.name] = [values_1.evaluate(t, local.vs), vt, local];
        }
        return [t, vt];
    }
    if (tm.tag === 'Pair') {
        let erased = false;
        if (tm.fst.tag === 'Var') {
            const i = local.nsSurface.indexOf(tm.fst.name);
            if (i >= 0) {
                const res = local_1.indexEnvT(local.ts, i);
                if (res) {
                    erased = res[0].erased;
                }
            }
            else if (prims_1.isPrimName(tm.fst.name)) {
                erased = prims_1.isPrimErased(tm.fst.name);
            }
        } // TODO: remove this ugliness
        const x = tm.fst.tag === 'Var' ? tm.fst.name : '_';
        const [fst, fstty] = synth(erased ? local.inType() : local, tm.fst);
        const [snd, sndty] = synth(local, tm.snd);
        const ty = core_1.Sigma(erased, x, values_1.quote(fstty, local.level), values_1.quote(sndty, local.level + 1));
        return [core_1.Pair(fst, snd, ty), values_1.evaluate(ty, local.vs)];
    }
    if (tm.tag === 'Ann') {
        const type = check(local.inType(), tm.type, values_1.VType);
        config_1.log(() => `eval type in Ann`);
        const vtype = values_1.evaluate(type, local.vs);
        const term = check(local, tm.term, vtype);
        return [core_1.Let(false, 'x', type, term, core_1.Var(0)), vtype];
    }
    if (tm.tag === 'Import') {
        const [term, sigma_] = synth(local, tm.term);
        const vterm = values_1.evaluate(term, local.vs);
        return createImportTerm(local, term, vterm, sigma_, tm.imports, tm.body);
    }
    if (tm.tag === 'Rigid')
        return utils_1.terr(`can only use rigid in checking position: ${surface_1.show(tm)}`);
    return utils_1.terr(`unable to synth ${surface_1.show(tm)}`);
};
const createImportTerm = (local, term, vterm, sigma_, imports, body, i = 0) => {
    config_1.log(() => `createImportTerm (${local.level}) ${S.showCore(term, local.ns)} ${showV(local, sigma_)}`);
    const sigma = values_1.force(sigma_);
    if (sigma.tag === 'VSigma') {
        let name = sigma.name;
        let nextimports = imports;
        let found = false;
        if (imports) {
            const nameix = imports.indexOf(sigma.name);
            if (nameix < 0) {
                name = '_';
            }
            else {
                nextimports = imports.slice(0);
                nextimports.splice(nameix, 1);
                found = true;
            }
        }
        else {
            found = true;
        }
        if (found) {
            const val = values_1.vproj(vterm, core_1.PIndex(sigma.name, i));
            const qtype = values_1.quote(sigma.type, local.level);
            const newlocal = local.define(sigma.erased, name, sigma.type, val, qtype, values_1.quote(val, local.level));
            const val2 = values_1.evaluate(core_1.Var(0), newlocal.vs);
            const [rest, ty] = createImportTerm(newlocal, term, vterm, values_1.vinst(sigma, val2), nextimports, body, i + 1);
            return [core_1.Let(sigma.erased, name, qtype, core_1.Proj(term, core_1.PIndex(sigma.name, i)), rest), ty];
        }
        else {
            return createImportTerm(local, term, vterm, values_1.vinst(sigma, values_1.vproj(vterm, core_1.PIndex(sigma.name, i))), nextimports, body, i + 1);
        }
    }
    if (imports && imports.length > 0)
        return utils_1.terr(`failed to import, names not in module: ${imports.join(' ')}`);
    config_1.log(() => `names in import body scope: ${local.ns}`);
    return synth(local, body);
};
const projectIndex = (local, full, tm, ty_, index) => {
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (ty.erased && index === 0 && !local.erased)
            return utils_1.terr(`cannot project erased ${surface_1.show(full)}: ${showV(local, ty)}`);
        if (index === 0)
            return ty.type;
        const fst = ty.name !== '_' ? core_1.PIndex(ty.name, 0) : core_1.PFst; // TODO: is this nice?
        return projectIndex(local, full, values_1.vproj(tm, core_1.PSnd), values_1.vinst(ty, values_1.vproj(tm, fst)), index - 1);
    }
    return utils_1.terr(`failed to project, ${surface_1.show(full)}: ${showV(local, ty_)}`);
};
const projectName = (local, full, orig, tm, ty_, x, ix, ns = List_1.nil) => {
    config_1.log(() => `projectName (${showV(local, tm)}) (${showV(local, ty_)}) ${x} ${ix} ${ns.toString()}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (ty.erased && ty.name === x && !local.erased)
            return utils_1.terr(`cannot project erased ${surface_1.show(full)}: ${showV(local, ty)}`);
        if (ty.name === x)
            return [ty.type, ix];
        const fst = ty.name !== '_' ? core_1.PIndex(ty.name, 0) : core_1.PFst; // TODO: is this nice?
        const vfst = ty.name !== '_' ? (!ns.contains(ty.name) ? values_1.vproj(orig, core_1.PIndex(ty.name, ix)) : values_1.vproj(tm, core_1.PIndex(ty.name, 0))) : values_1.vproj(tm, fst);
        config_1.log(() => showV(local, vfst));
        return projectName(local, full, orig, values_1.vproj(tm, core_1.PSnd), values_1.vinst(ty, vfst), x, ix + 1, List_1.cons(ty.name, ns));
    }
    return utils_1.terr(`failed to project, ${surface_1.show(full)}: ${showV(local, ty_)}`);
};
const synthapp = (local, ty_, mode, tm, tmall) => {
    config_1.log(() => `synthapp ${showV(local, ty_)} @ ${mode.tag === 'Expl' ? '' : '{'}${surface_1.show(tm)}${mode.tag === 'Expl' ? '' : '}'}${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VPi' && ty.mode.tag === 'Impl' && mode.tag === 'Expl') {
        const m = newMeta(local, ty.type, ty.erased);
        const vm = values_1.evaluate(m, local.vs);
        const [rest, rt, l] = synthapp(local, values_1.vinst(ty, vm), mode, tm, tmall);
        return [rest, rt, List_1.cons(m, l)];
    }
    if (ty.tag === 'VPi' && mode_1.eqMode(ty.mode, mode)) {
        const right = check(ty.erased ? local.inType() : local, tm, ty.type);
        const rt = values_1.vinst(ty, values_1.evaluate(right, local.vs));
        return [right, rt, List_1.nil];
    }
    if (ty.tag === 'VFlex') {
        const vpi = freshPi(local, false, mode, 'x');
        unification_1.unify(local.level, ty, vpi);
        return synthapp(local, ty, mode, tm, tmall);
    }
    return utils_1.terr(`invalid type or plicity mismatch in synthapp in ${surface_1.show(tmall)}: ${showV(local, ty)} @ ${mode.tag === 'Expl' ? '' : '{'}${surface_1.show(tm)}${mode.tag === 'Expl' ? '' : '}'}`);
};
let holes = {};
const showValSZ = (local, v) => S.showCore(values_1.zonk(values_1.quote(v, local.level, false), local.vs, local.level, false), local.ns);
const showHoles = (tm, ty, toplocal) => {
    const holeprops = Object.entries(holes);
    if (holeprops.length === 0)
        return;
    const strtype = S.showCore(ty, toplocal.ns);
    const strterm = S.showCore(tm, toplocal.ns);
    const str = holeprops.map(([x, [t, v, local]]) => {
        const fst = local.ns.zipWith(local.vs, (x, v) => [x, v]);
        const all = fst.zipWith(local.ts, ([x, v], { bound: def, type: ty, inserted, erased, mode }) => [x, v, def, ty, inserted, erased, mode]);
        const allstr = all.toMappedArray(([x, v, b, t, i, p, m]) => {
            const y = p ? `-${x}` : x;
            const name = `${mode_1.eqMode(m, mode_1.Impl) ? `{${y}}` : y}`;
            return `${i ? 'i ' : ''}${name} : ${showValSZ(local, t)}${b ? '' : ` = ${showValSZ(local, v)}`}`;
        }).join('\n');
        return `\n_${x} : ${showValSZ(local, v)} = ${showValSZ(local, t)}\nlocal:\n${allstr}\n`;
    }).join('\n');
    return utils_1.terr(`unsolved holes\ntype: ${strtype}\nterm: ${strterm}\n${str}`);
};
const showUnsolvedMetas = (local) => metas_1.getUnsolvedMetas().map(m => `${m.erased ? '-' : ''}?${m.id} : ${showV(local, m.type)}`).join('\n');
const elaborate = (t, local = local_1.Local.empty()) => {
    holes = {};
    postponed = [];
    metas_1.resetMetas();
    const [tm, ty] = synth(local, t);
    tryAllPostponed();
    if (postponed.length > 0)
        return utils_1.terr(`there are postponed problems left: ${postponed.map(x => `?${x[0]}`).join(' ')}`);
    const qty = values_1.quote(ty, local.level);
    config_1.log(() => C.show(qty));
    config_1.log(() => C.show(tm));
    config_1.log(() => S.showCore(qty, local.ns));
    config_1.log(() => S.showCore(tm, local.ns));
    const zty = values_1.zonk(qty, local.vs, local.level);
    config_1.log(() => S.showCore(zty, local.ns));
    const ztm = values_1.zonk(tm, local.vs, local.level);
    config_1.log(() => S.showCore(ztm, local.ns));
    showHoles(ztm, zty, local);
    if (!metas_1.allMetasSolved())
        return utils_1.terr(`not all metas are solved: ${S.showCore(ztm, local.ns)} : ${S.showCore(zty, local.ns)}\n\n${showUnsolvedMetas(local)}`);
    return [ztm, zty];
};
exports.elaborate = elaborate;

},{"./config":1,"./core":2,"./globals":4,"./local":5,"./metas":6,"./mode":7,"./prims":10,"./surface":12,"./unification":13,"./utils/List":15,"./utils/utils":16,"./values":17}],4:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.preload = exports.loadGlobal = exports.deleteGlobal = exports.setGlobal = exports.getGlobals = exports.getGlobal = exports.resetGlobals = void 0;
const elaboration_1 = require("./elaboration");
const local_1 = require("./local");
const parser_1 = require("./parser");
const surface_1 = require("./surface");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const verification_1 = require("./verification");
let globals = {};
const resetGlobals = () => { globals = {}; };
exports.resetGlobals = resetGlobals;
const getGlobal = (name) => {
    const entry = globals[name];
    if (!entry)
        return utils_1.impossible(`undefined global in getGlobal: ${name}`);
    return entry;
};
exports.getGlobal = getGlobal;
const getGlobals = () => globals;
exports.getGlobals = getGlobals;
const setGlobal = (name, type, value, etype, term, erased) => {
    globals[name] = { type, value, etype, term, erased };
};
exports.setGlobal = setGlobal;
const deleteGlobal = (name) => {
    delete globals[name];
};
exports.deleteGlobal = deleteGlobal;
const loadGlobal = (x, erased = false) => {
    if (globals[x])
        return globals[x];
    const sc = utils_1.loadFileSync(`${x}`);
    if (sc instanceof Error)
        return null;
    const e = parser_1.parse(sc);
    const [tm, ty] = elaboration_1.elaborate(e);
    verification_1.verify(tm);
    exports.setGlobal(x, values_1.evaluate(ty, List_1.nil), values_1.evaluate(tm, List_1.nil), ty, tm, erased);
    return exports.getGlobal(x);
};
exports.loadGlobal = loadGlobal;
const preload = (t, local = local_1.Local.empty()) => {
    const vs = surface_1.globalsInSurface(t);
    const localVars = local.nsSurface.toArray();
    utils_1.removeAll(vs, localVars);
    return Promise.all(vs.map(async (v) => {
        const sc = await utils_1.loadFile(`${v}`);
        const e = parser_1.parse(sc);
        const [tm, ty] = elaboration_1.elaborate(e);
        verification_1.verify(tm);
        exports.setGlobal(v, values_1.evaluate(ty, List_1.nil), values_1.evaluate(tm, List_1.nil), ty, tm, local.erased);
        return exports.getGlobal(v) || utils_1.impossible(`preload failed, unable to get ${v}`);
    }));
};
exports.preload = preload;

},{"./elaboration":3,"./local":5,"./parser":9,"./surface":12,"./utils/List":15,"./utils/utils":16,"./values":17,"./verification":18}],5:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.showValCore = exports.showV = exports.Local = exports.indexEnvT = exports.EntryT = void 0;
const mode_1 = require("./mode");
const List_1 = require("./utils/List");
const values_1 = require("./values");
const S = require("./surface");
const EntryT = (type, erased, mode, bound, inserted) => ({ type, bound, mode, erased, inserted });
exports.EntryT = EntryT;
const indexEnvT = (ts, ix) => {
    let l = ts;
    let i = 0;
    let erased = 0;
    while (l.isCons()) {
        if (l.head.inserted) {
            l = l.tail;
            i++;
            continue;
        }
        if (ix === 0)
            return [l.head, i, erased];
        if (l.head.erased)
            erased++;
        i++;
        ix--;
        l = l.tail;
    }
    return null;
};
exports.indexEnvT = indexEnvT;
class Local {
    constructor(erased, level, ns, nsSurface, ts, vs, path) {
        this.erased = erased;
        this.level = level;
        this.ns = ns;
        this.nsSurface = nsSurface;
        this.ts = ts;
        this.vs = vs;
        this.path = path;
    }
    static empty() {
        if (Local._empty === undefined)
            Local._empty = new Local(false, 0, List_1.nil, List_1.nil, List_1.nil, List_1.nil, List_1.nil);
        return Local._empty;
    }
    bind(erased, mode, name, ty) {
        return new Local(this.erased, this.level + 1, List_1.cons(name, this.ns), List_1.cons(name, this.nsSurface), List_1.cons(exports.EntryT(ty, erased, mode, true, false), this.ts), List_1.cons(values_1.VVar(this.level), this.vs), List_1.cons([erased, mode, name, values_1.quote(ty, this.level), null], this.path));
    }
    insert(erased, mode, name, ty) {
        return new Local(this.erased, this.level + 1, List_1.cons(name, this.ns), this.nsSurface, List_1.cons(exports.EntryT(ty, erased, mode, true, true), this.ts), List_1.cons(values_1.VVar(this.level), this.vs), List_1.cons([erased, mode, name, values_1.quote(ty, this.level), null], this.path));
    }
    define(erased, name, ty, val, qty, qval) {
        return new Local(this.erased, this.level + 1, List_1.cons(name, this.ns), List_1.cons(name, this.nsSurface), List_1.cons(exports.EntryT(ty, erased, mode_1.Expl, false, false), this.ts), List_1.cons(val, this.vs), List_1.cons([erased, mode_1.Expl, name, qty, qval], this.path));
    }
    undo() {
        if (this.level === 0)
            return this;
        return new Local(this.erased, this.level - 1, this.ns.tail, this.nsSurface.tail, this.ts.tail, this.vs.tail, this.path.tail);
    }
    inType() {
        return new Local(true, this.level, this.ns, this.nsSurface, this.ts, this.vs, this.path);
    }
    toString() {
        return this.ts.toString(e => `${e.bound ? '' : 'd '}${exports.showV(this, e.type)}`);
    }
}
exports.Local = Local;
const showV = (local, val) => S.showVal(val, local.level, false, local.ns);
exports.showV = showV;
const showValCore = (local, val) => values_1.show(val, local.level);
exports.showValCore = showValCore;

},{"./mode":7,"./surface":12,"./utils/List":15,"./values":17}],6:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.getUnsolvedMetas = exports.allMetasSolved = exports.setMeta = exports.getMeta = exports.freshMeta = exports.registerMetaCallback = exports.resetMetas = exports.Solved = exports.Unsolved = void 0;
const utils_1 = require("./utils/utils");
const Unsolved = (id, type, erased) => ({ tag: 'Unsolved', id, type, erased });
exports.Unsolved = Unsolved;
const Solved = (id, solution, type) => ({ tag: 'Solved', id, solution, type });
exports.Solved = Solved;
let metas = [];
let callbacks = {};
const resetMetas = () => { metas = []; callbacks = {}; };
exports.resetMetas = resetMetas;
const registerMetaCallback = (m, fn) => {
    if (!callbacks[m])
        callbacks[m] = [];
    callbacks[m].push(fn);
};
exports.registerMetaCallback = registerMetaCallback;
const freshMeta = (type, erased) => {
    const id = metas.length;
    metas.push(exports.Unsolved(id, type, erased));
    return id;
};
exports.freshMeta = freshMeta;
const getMeta = (id) => {
    const entry = metas[id];
    if (!entry)
        return utils_1.impossible(`getMeta with undefined meta ${id}`);
    return entry;
};
exports.getMeta = getMeta;
const setMeta = (id, solution) => {
    const entry = metas[id];
    if (!entry)
        return utils_1.impossible(`setMeta with undefined meta ${id}`);
    if (entry.tag === 'Solved')
        return utils_1.impossible(`setMeta with solved meta ${id}`);
    metas[id] = exports.Solved(id, solution, entry.type);
    const cbs = callbacks[id];
    if (cbs)
        for (let i = 0, l = cbs.length; i < l; i++)
            cbs[i]();
    delete callbacks[id];
};
exports.setMeta = setMeta;
const allMetasSolved = () => metas.every(x => x.tag === 'Solved');
exports.allMetasSolved = allMetasSolved;
const getUnsolvedMetas = () => metas.filter(x => x.tag === 'Unsolved');
exports.getUnsolvedMetas = getUnsolvedMetas;

},{"./utils/utils":16}],7:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.eqMode = exports.Impl = exports.Expl = void 0;
;
exports.Expl = { tag: 'Expl' };
;
exports.Impl = { tag: 'Impl' };
const eqMode = (a, b) => a.tag === b.tag;
exports.eqMode = eqMode;

},{}],8:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.chooseName = exports.nextName = void 0;
const nextName = (x) => {
    if (x === '_')
        return x;
    const s = x.split('$');
    if (s.length === 2)
        return `${s[0]}\$${+s[1] + 1}`;
    return `${x}\$0`;
};
exports.nextName = nextName;
const chooseName = (x, ns) => x === '_' ? x : ns.contains(x) ? exports.chooseName(exports.nextName(x), ns) : x;
exports.chooseName = chooseName;

},{}],9:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parse = void 0;
const config_1 = require("./config");
const mode_1 = require("./mode");
const surface_1 = require("./surface");
const utils_1 = require("./utils/utils");
const matchingBracket = (c) => {
    if (c === '(')
        return ')';
    if (c === ')')
        return '(';
    if (c === '{')
        return '}';
    if (c === '}')
        return '{';
    if (c === '[')
        return ']';
    if (c === ']')
        return '[';
    return utils_1.serr(`invalid bracket: ${c}`);
};
const TName = (name) => ({ tag: 'Name', name });
const TNum = (num) => ({ tag: 'Num', num });
const TList = (list, bracket) => ({ tag: 'List', list, bracket });
const TStr = (str) => ({ tag: 'Str', str });
const SYM1 = ['\\', ':', '=', ';', '*', ',', '#', '&', '%', 'λ', '×', '→', '★', '~'];
const SYM2 = ['->', '**'];
const createTName = (x) => {
    if (x === 'λ')
        return TName('\\');
    if (x === '×')
        return TName('**');
    if (x === '→')
        return TName('->');
    if (x === '★')
        return TName('*');
    return TName(x);
};
const START = 0;
const NAME = 1;
const COMMENT = 2;
const NUMBER = 3;
const STRING = 4;
const BLOCKCOMMENT = 5;
const tokenize = (sc) => {
    let state = START;
    let r = [];
    let t = '';
    let esc = false;
    let commentlevel = 0;
    let p = [], b = [];
    for (let i = 0, l = sc.length; i <= l; i++) {
        const c = sc[i] || ' ';
        const next = sc[i + 1] || '';
        const next2 = sc[i + 2] || '';
        if (state === START) {
            if (c + next === '--')
                i++, state = COMMENT;
            else if (c + next + next2 === '{--')
                i += 2, commentlevel++, state = BLOCKCOMMENT;
            else if (SYM2.indexOf(c + next) >= 0)
                r.push(createTName(c + next)), i++;
            else if (SYM1.indexOf(c) >= 0)
                r.push(createTName(c));
            else if (c === '"')
                state = STRING;
            else if (c === '.' && !/[\.\%\_a-z]/i.test(next))
                r.push(TName('.'));
            else if (/[\'\-\.\?\@\#\%\_\@a-z\/]/i.test(c))
                t += c, state = NAME;
            else if (/[0-9]/.test(c))
                t += c, state = NUMBER;
            else if (c === '(' || c === '{' || c === '[')
                b.push(c), p.push(r), r = [];
            else if (c === ')' || c === '}' || c === ']') {
                if (b.length === 0)
                    return utils_1.serr(`unmatched bracket: ${c} (char ${i})`);
                const br = b.pop();
                if (matchingBracket(br) !== c)
                    return utils_1.serr(`unmatched bracket: ${br} and ${c}`);
                const a = p.pop();
                a.push(TList(r, br));
                r = a;
            }
            else if (/\s/.test(c))
                continue;
            else
                return utils_1.serr(`invalid char ${c} in tokenize`);
        }
        else if (state === NAME) {
            if (!(/[a-z0-9\-\_\/]/i.test(c) || (c === '.' && /[a-z0-9\_\/]/i.test(next)))) {
                r.push(TName(t));
                t = '', i--, state = START;
            }
            else
                t += c;
        }
        else if (state === NUMBER) {
            if (!/[0-9a-z\+\-]/i.test(c)) {
                r.push(TNum(t));
                t = '', i--, state = START;
            }
            else
                t += c;
        }
        else if (state === COMMENT) {
            if (c === '\n')
                state = START;
        }
        else if (state === STRING) {
            if (c === '\\')
                esc = true;
            else if (esc)
                t += c, esc = false;
            else if (c === '"') {
                r.push(TStr(t));
                t = '', state = START;
            }
            else
                t += c;
        }
        else if (state === BLOCKCOMMENT) {
            if (c + next + next2 === '{--')
                i += 2, commentlevel++;
            else if (c + next + next2 === '--}') {
                i += 2;
                commentlevel--;
                if (commentlevel === 0)
                    state = START;
            }
        }
    }
    if (b.length > 0)
        return utils_1.serr(`unclosed brackets: ${b.join(' ')}`);
    if (state !== START && state !== COMMENT)
        return utils_1.serr('invalid tokenize end state');
    if (esc)
        return utils_1.serr(`escape is true after tokenize`);
    if (commentlevel !== 0)
        return utils_1.serr(`unclosed block comment`);
    return r;
};
const isName = (t, x) => t && t.tag === 'Name' && t.name === x;
const isNames = (t) => t.map(x => {
    if (x.tag !== 'Name')
        return utils_1.serr(`expected name`);
    return x.name;
});
const splitTokens = (a, fn, keepSymbol = false) => {
    const r = [];
    let t = [];
    for (let i = 0, l = a.length; i < l; i++) {
        const c = a[i];
        if (fn(c)) {
            r.push(t);
            t = keepSymbol ? [c] : [];
        }
        else
            t.push(c);
    }
    r.push(t);
    return r;
};
const UnitType = surface_1.Var('()');
const erasedName = (x) => x[0] === '-' ? [x.slice(1), true] : [x, false];
const lambdaParams = (t) => {
    if (t.tag === 'Name') {
        const [x, er] = erasedName(t.name);
        return [[er, x, mode_1.Expl, null]];
    }
    if (t.tag === 'List') {
        const impl = t.bracket === '{' ? mode_1.Impl : mode_1.Expl;
        const a = t.list;
        if (a.length === 0)
            return [[false, '_', impl, UnitType]];
        const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
        if (i === -1)
            return isNames(a).map(x => {
                const [y, er] = erasedName(x);
                return [er, y, impl, null];
            });
        const ns = a.slice(0, i);
        const rest = a.slice(i + 1);
        const ty = exprs(rest, '(');
        return isNames(ns).map(x => {
            const [y, er] = erasedName(x);
            return [er, y, impl, ty];
        });
    }
    return utils_1.serr(`invalid lambda param`);
};
const piParams = (t) => {
    if (t.tag === 'Name')
        return [[false, '_', mode_1.Expl, expr(t)[0]]];
    if (t.tag === 'List') {
        const impl = t.bracket === '{' ? mode_1.Impl : mode_1.Expl;
        const a = t.list;
        if (a.length === 0)
            return [[false, '_', impl, UnitType]];
        const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
        if (i === -1)
            return [[false, '_', impl, expr(t)[0]]];
        const ns = a.slice(0, i);
        const rest = a.slice(i + 1);
        const ty = exprs(rest, '(');
        return isNames(ns).map(x => {
            const [y, er] = erasedName(x);
            return [er, y, impl, ty];
        });
    }
    return utils_1.serr(`invalid pi param`);
};
const codepoints = (s) => {
    const chars = [];
    for (let i = 0; i < s.length; i++) {
        const c1 = s.charCodeAt(i);
        if (c1 >= 0xD800 && c1 < 0xDC00 && i + 1 < s.length) {
            const c2 = s.charCodeAt(i + 1);
            if (c2 >= 0xDC00 && c2 < 0xE000) {
                chars.push(0x10000 + ((c1 - 0xD800) << 10) + (c2 - 0xDC00));
                i++;
                continue;
            }
        }
        chars.push(c1);
    }
    return chars;
};
const numToNat = (n, orig) => {
    if (isNaN(n))
        return utils_1.serr(`invalid nat number: ${orig}`);
    const s = surface_1.Var('S');
    let c = surface_1.Var('Z');
    for (let i = 0; i < n; i++)
        c = surface_1.App(s, mode_1.Expl, c);
    return c;
};
const proj = (p) => {
    if (p === '_1')
        return surface_1.PFst;
    if (p === '_2')
        return surface_1.PSnd;
    const i = +p;
    if (!isNaN(i)) {
        if (i < 0 || Math.floor(i) !== i)
            return utils_1.serr(`invalid projection: ${p}`);
        return surface_1.PIndex(i);
    }
    if (/[a-z]/i.test(p[0]))
        return surface_1.PName(p);
    return utils_1.serr(`invalid projection: ${p}`);
};
const projs = (ps) => {
    const parts = ps.split('.');
    return parts.map(proj);
};
const mkVar = (x) => x[0] === '@' ? surface_1.Rigid(surface_1.Var(x.slice(1))) : surface_1.Var(x);
const expr = (t) => {
    if (t.tag === 'List')
        return t.bracket === '[' ? [exprs(t.list, '['), false] : [exprs(t.list, '('), t.bracket === '{'];
    if (t.tag === 'Str') {
        const s = codepoints(t.str).reverse();
        const Cons = surface_1.Var('Cons');
        const Nil = surface_1.Var('Nil');
        return [s.reduce((t, n) => surface_1.App(surface_1.App(Cons, mode_1.Expl, numToNat(n, `${n}`)), mode_1.Expl, t), Nil), false];
    }
    if (t.tag === 'Name') {
        const x = t.name;
        if (x === '*')
            return [surface_1.Type, false];
        if (x.includes('/'))
            return [surface_1.Global(x), false];
        if (x[0] === "'")
            return [surface_1.SymbolLit(x.slice(1)), false];
        if (x[0] === '_') {
            const y = x.slice(1);
            return [surface_1.Hole(y.length > 0 ? y : null), false];
        }
        if (/[a-z\@]/i.test(x[0])) {
            if (x.indexOf('.') >= 0) {
                const parts = x.split('.');
                const first = parts[0];
                const ps = projs(parts.slice(1).join('.'));
                return [ps.reduce((t, p) => surface_1.Proj(t, p), mkVar(first)), false];
            }
            else
                return [mkVar(x), false];
        }
        return utils_1.serr(`invalid name: ${x}`);
    }
    if (t.tag === 'Num') {
        if (t.num.endsWith('b')) {
            const n = +t.num.slice(0, -1);
            if (isNaN(n))
                return utils_1.serr(`invalid number: ${t.num}`);
            const s0 = surface_1.Var('B0');
            const s1 = surface_1.Var('B1');
            let c = surface_1.Var('BE');
            const s = n.toString(2);
            for (let i = 0; i < s.length; i++)
                c = surface_1.App(s[i] === '0' ? s0 : s1, mode_1.Expl, c);
            return [c, false];
        }
        else if (t.num.endsWith('f')) {
            const n = +t.num.slice(0, -1);
            if (isNaN(n))
                return utils_1.serr(`invalid number: ${t.num}`);
            const s = surface_1.Var('FS');
            let c = surface_1.Var('FZ');
            for (let i = 0; i < n; i++)
                c = surface_1.App(s, mode_1.Expl, c);
            return [c, false];
        }
        else if (t.num.endsWith('n')) {
            return [numToNat(+t.num.slice(0, -1), t.num), false];
        }
        else {
            return [numToNat(+t.num, t.num), false];
        }
    }
    return t;
};
const Unit = surface_1.Var('[]');
const Nil = surface_1.Var('Nil');
const Cons = surface_1.Var('Cons');
const VNil = surface_1.Var('VNil');
const VCons = surface_1.Var('VCons');
const exprs = (ts, br, fromRepl = false) => {
    if (br === '{')
        return utils_1.serr(`{} cannot be used here`);
    if (br === '[') {
        if (ts.length === 0)
            return Unit;
        let type = 0;
        if (isName(ts[0], '#')) {
            ts = ts.slice(1);
            type = 1;
        }
        else if (isName(ts[0], '&')) {
            ts = ts.slice(1);
            type = 2;
        }
        else if (isName(ts[0], '%')) {
            ts = ts.slice(1);
            type = 3;
        }
        else if (isName(ts[0], '~')) {
            ts = ts.slice(1);
            type = 4;
        }
        if (ts.length === 0) {
            if (type === 1)
                return surface_1.Pair(numToNat(0, '0'), Unit);
            if (type === 2)
                return Nil;
            if (type === 3)
                return VNil;
            return Unit;
        }
        const jp = ts.findIndex(x => isName(x, ','));
        if (jp >= 0) {
            const s = splitTokens(ts, x => isName(x, ','));
            if (s.length < 2)
                return utils_1.serr(`parsing failed with ,`);
            const args = s.map(x => {
                if (x.length === 1) {
                    const h = x[0];
                    if (h.tag === 'List' && h.bracket === '{')
                        return expr(h);
                }
                return [exprs(x, '('), false];
            });
            if (args.length === 0) {
                if (type === 1)
                    return surface_1.Pair(numToNat(0, '0'), Unit);
                if (type === 2)
                    return Nil;
                if (type === 3)
                    return VNil;
                return Unit;
            }
            if (type === 2)
                return args.reduceRight((x, [y, i]) => {
                    if (i)
                        return utils_1.serr(`list element cannot be implicit`);
                    return surface_1.App(surface_1.App(Cons, mode_1.Expl, y), mode_1.Expl, x);
                }, Nil);
            if (type === 3)
                return args.reduceRight((x, [y, i]) => {
                    if (i)
                        return utils_1.serr(`vec element cannot be implicit`);
                    return surface_1.App(surface_1.App(VCons, mode_1.Expl, y), mode_1.Expl, x);
                }, VNil);
            if (type === 4)
                return args.reduce((x, [y, i]) => {
                    if (i)
                        return utils_1.serr(`tuple element cannot be implicit`);
                    return surface_1.Pair(x, y);
                }, Unit);
            const p = args.reduceRight((x, [y, i]) => {
                if (i)
                    return utils_1.serr(`pair element cannot be implicit`);
                return surface_1.Pair(y, x);
            }, Unit);
            if (type === 1)
                surface_1.Pair(numToNat(args.length, `${args.length}`), p);
            return p;
        }
        else {
            const expr = exprs(ts, '(');
            if (type === 1)
                return surface_1.Pair(numToNat(1, `1`), surface_1.Pair(expr, Unit));
            if (type === 2)
                return surface_1.App(surface_1.App(Cons, mode_1.Expl, expr), mode_1.Expl, Nil);
            if (type === 3)
                return surface_1.App(surface_1.App(VCons, mode_1.Expl, expr), mode_1.Expl, VNil);
            if (type === 4)
                return surface_1.Pair(Unit, expr);
            return surface_1.Pair(expr, Unit);
        }
    }
    if (ts.length === 0)
        return UnitType;
    if (ts.length === 1)
        return expr(ts[0])[0];
    if (isName(ts[0], 'let')) {
        let x = ts[1];
        let j = 2;
        let name = 'ERROR';
        if (x.tag === 'Name') {
            name = x.name;
        }
        else if (x.tag === 'List' && x.bracket === '{') {
            const a = x.list;
            if (a.length !== 1)
                return utils_1.serr(`invalid name for let`);
            const h = a[0];
            if (h.tag !== 'Name')
                return utils_1.serr(`invalid name for let`);
            name = h.name;
        }
        else
            return utils_1.serr(`invalid name for let`);
        let ty = null;
        if (isName(ts[j], ':')) {
            const tyts = [];
            j++;
            for (; j < ts.length; j++) {
                const v = ts[j];
                if (v.tag === 'Name' && v.name === '=')
                    break;
                else
                    tyts.push(v);
            }
            ty = exprs(tyts, '(');
        }
        if (!isName(ts[j], '='))
            return utils_1.serr(`no = after name in let`);
        const vals = [];
        let found = false;
        let i = j + 1;
        for (; i < ts.length; i++) {
            const c = ts[i];
            if (c.tag === 'Name' && c.name === ';') {
                found = true;
                break;
            }
            vals.push(c);
        }
        if (vals.length === 0)
            return utils_1.serr(`empty val in let`);
        const val = exprs(vals, '(');
        if (!found) {
            if (!fromRepl)
                return utils_1.serr(`no ; after let`);
            if (ts.slice(i + 1).length > 0)
                return utils_1.serr(`no ; after let`);
            const [y, er] = erasedName(name);
            return surface_1.Let(er, y, ty || null, val, null);
        }
        const body = exprs(ts.slice(i + 1), '(');
        const [y, er] = erasedName(name);
        return surface_1.Let(er, y, ty || null, val, body);
    }
    if (isName(ts[0], 'import')) {
        if (!ts[1])
            return utils_1.serr(`import needs a term`);
        const [term, i] = expr(ts[1]);
        if (i)
            return utils_1.serr(`import term cannot be implicit`);
        let j = 3;
        let imports = null;
        if (!isName(ts[2], ';')) {
            if (!ts[2] || ts[2].tag !== 'List' || ts[2].bracket !== '(') {
                if (!fromRepl)
                    return utils_1.serr(`import needs a list or ;`);
                if (ts.slice(j).length > 0)
                    return utils_1.serr(`expected ; after import list`);
                return surface_1.Import(term, null, null);
            }
            imports = splitTokens(ts[2].list, t => isName(t, ',')).map(ts => {
                if (ts.length === 0)
                    return null;
                if (ts.length > 1)
                    return utils_1.serr(`import list must only contain variables`);
                if (ts[0].tag !== 'Name')
                    return utils_1.serr(`import list must only contain variables`);
                return ts[0].name;
            }).filter(Boolean);
            if (!isName(ts[3], ';')) {
                if (!fromRepl)
                    return utils_1.serr(`expected ; after import list`);
                if (ts.slice(j).length > 0)
                    return utils_1.serr(`expected ; after import list`);
                return surface_1.Import(term, imports, null);
            }
            j++;
        }
        const body = exprs(ts.slice(j), '(');
        return surface_1.Import(term, imports, body);
    }
    const i = ts.findIndex(x => isName(x, ':'));
    if (i >= 0) {
        const a = ts.slice(0, i);
        const b = ts.slice(i + 1);
        return surface_1.Ann(exprs(a, '('), exprs(b, '('));
    }
    if (isName(ts[0], '@')) {
        const term = exprs(ts.slice(1), '(');
        return surface_1.Rigid(term);
    }
    if (isName(ts[0], '\\')) {
        const args = [];
        let found = false;
        let i = 1;
        for (; i < ts.length; i++) {
            const c = ts[i];
            if (isName(c, '.')) {
                found = true;
                break;
            }
            lambdaParams(c).forEach(x => args.push(x));
        }
        if (!found)
            return utils_1.serr(`. not found after \\ or there was no whitespace after .`);
        const body = exprs(ts.slice(i + 1), '(');
        return args.reduceRight((x, [u, name, mode, ty]) => surface_1.Abs(u, mode, name, ty, x), body);
    }
    const j = ts.findIndex(x => isName(x, '->'));
    if (j >= 0) {
        const s = splitTokens(ts, x => isName(x, '->'));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with ->`);
        const args = s.slice(0, -1)
            .map(p => p.length === 1 ? piParams(p[0]) : [[false, '_', mode_1.Expl, exprs(p, '(')]])
            .reduce((x, y) => x.concat(y), []);
        const body = exprs(s[s.length - 1], '(');
        return args.reduceRight((x, [u, name, impl, ty]) => surface_1.Pi(u, impl, name, ty, x), body);
    }
    const jp = ts.findIndex(x => isName(x, ','));
    if (jp >= 0) {
        const s = splitTokens(ts, x => isName(x, ','));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with ,`);
        const args = s.map(x => {
            if (x.length === 1) {
                const h = x[0];
                if (h.tag === 'List' && h.bracket === '{')
                    return expr(h);
            }
            return [exprs(x, '('), false];
        });
        if (args.length === 0)
            return utils_1.serr(`empty pair`);
        if (args.length === 1)
            return utils_1.serr(`singleton pair`);
        const last1 = args[args.length - 1];
        const last2 = args[args.length - 2];
        const lastitem = surface_1.Pair(last2[0], last1[0]);
        return args.slice(0, -2).reduceRight((x, [y, _p]) => surface_1.Pair(y, x), lastitem);
    }
    const js = ts.findIndex(x => isName(x, '**'));
    if (js >= 0) {
        const s = splitTokens(ts, x => isName(x, '**'));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with **`);
        const args = s.slice(0, -1)
            .map(p => p.length === 1 ? piParams(p[0]) : [[false, '_', mode_1.Expl, exprs(p, '(')]])
            .reduce((x, y) => x.concat(y), []);
        const body = exprs(s[s.length - 1], '(');
        return args.reduceRight((x, [u, name, mode, ty]) => {
            if (mode.tag !== 'Expl')
                return utils_1.serr(`sigma cannot be implicit`);
            return surface_1.Sigma(u, name, ty, x);
        }, body);
    }
    const l = ts.findIndex(x => isName(x, '\\'));
    let all = [];
    if (l >= 0) {
        const first = ts.slice(0, l).map(t => appPart(t));
        const rest = exprs(ts.slice(l), '(');
        all = first.concat([{ tag: 'Expr', expr: rest, impl: false }]);
    }
    else {
        all = ts.map(t => appPart(t));
    }
    if (all.length === 0)
        return utils_1.serr(`empty application`);
    const hd = all[0];
    if (hd.tag === 'Expr' && hd.impl)
        return utils_1.serr(`in application function cannot be between {}`);
    if (hd.tag === 'Proj')
        return utils_1.serr(`in application function cannot be a projection`);
    return all.slice(1).reduce((x, a) => {
        if (a.tag === 'Proj')
            return a.proj.reduce((t, p) => surface_1.Proj(t, p), x);
        return surface_1.App(x, a.impl ? mode_1.Impl : mode_1.Expl, a.expr);
    }, hd.expr);
};
const appPart = (t) => {
    if (t.tag === 'Name' && t.name[0] === '.')
        return { tag: 'Proj', proj: projs(t.name.slice(1)) };
    const [ex, impl] = expr(t);
    return { tag: 'Expr', expr: ex, impl };
};
const parse = (s, fromRepl = false) => {
    config_1.log(() => `parse ${s}`);
    const ts = tokenize(s);
    const ex = exprs(ts, '(', fromRepl);
    if (!fromRepl)
        config_1.log(() => `parsed ${surface_1.show(ex)}`);
    return ex;
};
exports.parse = parse;

},{"./config":1,"./mode":7,"./surface":12,"./utils/utils":16}],10:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.primType = exports.isPrimName = exports.PrimNames = exports.isPrimErased = exports.ErasedPrims = void 0;
const mode_1 = require("./mode");
const values_1 = require("./values");
exports.ErasedPrims = ['*', 'HEq', '()', 'Bool', 'IIRData', 'Symbol'];
const isPrimErased = (name) => exports.ErasedPrims.includes(name);
exports.isPrimErased = isPrimErased;
exports.PrimNames = [
    '*',
    'HEq', 'HRefl', 'elimHEq',
    '()', '[]',
    'Bool', 'True', 'False', 'elimBool',
    'IIRData', 'IIRCon', 'elimIIRData', 'funIIRData',
    'Symbol', 'eqSymbol',
    'unsafeGuardedCoerce',
];
const isPrimName = (x) => exports.PrimNames.includes(x);
exports.isPrimName = isPrimName;
const primType = (name) => {
    if (name === '*')
        return values_1.VType;
    // HEq : {A B : *} -> A -> B -> *
    if (name === 'HEq')
        return values_1.VPi(false, mode_1.Impl, 'A', values_1.VType, A => values_1.VPi(false, mode_1.Impl, 'B', values_1.VType, B => values_1.VPi(false, mode_1.Expl, '_', A, _ => values_1.VPi(false, mode_1.Expl, '_', B, _ => values_1.VType))));
    // HRefl : {-A : *} -> {-x : A} -> HEq {A} {A} x x
    if (name === 'HRefl')
        return values_1.VPi(true, mode_1.Impl, 'A', values_1.VType, A => values_1.VPi(true, mode_1.Impl, 'x', A, x => values_1.VEq(A, x, x)));
    /*
      elimHEq : {-A : *}
        -> {-a : A}
        -> (-P : {b : A} -> HEq {A} {A} a b -> *)
        -> P {a} (HRefl {A} {a})
        -> {-b : A}
        -> (p : HEq {A} {A} a b)
        -> P {b} p
    */
    if (name === 'elimHEq')
        return values_1.VPi(true, mode_1.Impl, 'A', values_1.VType, A => values_1.VPi(true, mode_1.Impl, 'a', A, a => values_1.VPi(true, mode_1.Expl, 'P', values_1.VPi(false, mode_1.Impl, 'b', A, b => values_1.VPi(false, mode_1.Expl, '', values_1.VEq(A, a, b), _ => values_1.VType)), P => values_1.VPi(false, mode_1.Expl, '_', values_1.vapp2(P, mode_1.Impl, a, mode_1.Expl, values_1.VHRefl(A, a)), _ => values_1.VPi(true, mode_1.Impl, 'b', A, b => values_1.VPi(false, mode_1.Expl, 'p', values_1.VEq(A, a, b), p => values_1.vapp2(P, mode_1.Impl, b, mode_1.Expl, p)))))));
    if (name === '()')
        return values_1.VType;
    if (name === 'Bool')
        return values_1.VType;
    if (name === 'Symbol')
        return values_1.VType;
    if (name === '[]')
        return values_1.VUnitType;
    if (name === 'True')
        return values_1.VBool;
    if (name === 'False')
        return values_1.VBool;
    // (-P : Bool -> *) -> P True -> P False -> (b : Bool) -> P b
    if (name === 'elimBool')
        return values_1.VPi(true, mode_1.Expl, 'P', values_1.VPi(false, mode_1.Expl, '_', values_1.VBool, _ => values_1.VType), P => values_1.VPi(false, mode_1.Expl, '_', values_1.vapp(P, mode_1.Expl, values_1.VTrue), _ => values_1.VPi(false, mode_1.Expl, '_', values_1.vapp(P, mode_1.Expl, values_1.VFalse), _ => values_1.VPi(false, mode_1.Expl, 'b', values_1.VBool, b => values_1.vapp(P, mode_1.Expl, b)))));
    /*
      {I : *} ->
      {R : I -> *} ->
      (F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *) ->
      ({-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i) ->
      I ->
      *
    */
    if (name === 'IIRData')
        return values_1.VPi(false, mode_1.Impl, 'I', values_1.VType, I => values_1.VPi(false, mode_1.Impl, 'R', values_1.VPi(false, mode_1.Expl, '_', I, _ => values_1.VType), R => values_1.VPi(false, mode_1.Expl, 'F', values_1.viirF(I, R), F => values_1.VPi(false, mode_1.Expl, '_', values_1.viirG(I, R, F), _ => values_1.VPi(false, mode_1.Expl, '_', I, _ => values_1.VType)))));
    /*
      {-I : *} ->
      {-R : I -> *} ->
      {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
      {-G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
      {-i : I} ->
      F (Data {I} {R} F G) (funData {I} {R} {F} {G}) i ->
      Data {I} {R} F G i
    */
    if (name === 'IIRCon')
        return values_1.VPi(true, mode_1.Impl, 'I', values_1.VType, I => values_1.VPi(true, mode_1.Impl, 'R', values_1.VPi(false, mode_1.Expl, '_', I, _ => values_1.VType), R => values_1.VPi(true, mode_1.Impl, 'F', values_1.viirF(I, R), F => values_1.VPi(true, mode_1.Impl, 'G', values_1.viirG(I, R, F), G => values_1.VPi(true, mode_1.Impl, 'i', I, i => values_1.VPi(false, mode_1.Expl, '_', values_1.vapp3(F, mode_1.Expl, values_1.VIIRDataPartial(I, R, F, G), mode_1.Expl, values_1.vfunIIRDataPartial(I, R, F, G), mode_1.Expl, i), _ => values_1.VIIRData(I, R, F, G, i)))))));
    /*
      {-I : *} ->
      {-R : I -> *} ->
      {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
      {-G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
      (-P : {i : I} -> Data {I} {R} F G i -> *) ->
      (
        ({-j : I} -> (z : Data {I} {R} F G j) -> P {j} z) ->
        {-i : I} ->
        (y : F (Data {I} {R} F G) (funData {I} {R} {F} {G}) i) ->
        P {i} (Con {I} {R} {F} {G} {i} y)
      ) ->
      {-i : I} ->
      (x : Data {I} {R} F G i) ->
      P {i} x
    */
    if (name === 'elimIIRData')
        return values_1.VPi(true, mode_1.Impl, 'I', values_1.VType, I => values_1.VPi(true, mode_1.Impl, 'R', values_1.VPi(false, mode_1.Expl, '_', I, _ => values_1.VType), R => values_1.VPi(true, mode_1.Impl, 'F', values_1.viirF(I, R), F => values_1.VPi(true, mode_1.Impl, 'G', values_1.viirG(I, R, F), G => values_1.VPi(true, mode_1.Expl, 'P', values_1.VPi(false, mode_1.Impl, 'i', I, i => values_1.VPi(false, mode_1.Expl, '_', values_1.VIIRData(I, R, F, G, i), _ => values_1.VType)), P => values_1.VPi(false, mode_1.Expl, '_', values_1.VPi(false, mode_1.Expl, '_', values_1.VPi(true, mode_1.Impl, 'j', I, j => values_1.VPi(false, mode_1.Expl, 'z', values_1.VIIRData(I, R, F, G, j), z => values_1.vapp2(P, mode_1.Impl, j, mode_1.Expl, z))), _ => values_1.VPi(true, mode_1.Impl, 'i', I, i => values_1.VPi(false, mode_1.Expl, 'y', values_1.vapp3(F, mode_1.Expl, values_1.VIIRDataPartial(I, R, F, G), mode_1.Expl, values_1.vfunIIRDataPartial(I, R, F, G), mode_1.Expl, i), y => values_1.vapp2(P, mode_1.Impl, i, mode_1.Expl, values_1.VIIRCon(I, R, F, G, i, y))))), _ => values_1.VPi(true, mode_1.Impl, 'i', I, i => values_1.VPi(false, mode_1.Expl, 'x', values_1.VIIRData(I, R, F, G, i), x => values_1.vapp2(P, mode_1.Impl, i, mode_1.Expl, x)))))))));
    /*
      {-I : *} ->
      {-R : I -> *} ->
      {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
      {G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
      {-i : I} ->
      Data {I} {R} F G i ->
      R i
    */
    if (name === 'funIIRData')
        return values_1.VPi(true, mode_1.Impl, 'I', values_1.VType, I => values_1.VPi(true, mode_1.Impl, 'R', values_1.VPi(false, mode_1.Expl, '_', I, _ => values_1.VType), R => values_1.VPi(true, mode_1.Impl, 'F', values_1.viirF(I, R), F => values_1.VPi(false, mode_1.Impl, 'G', values_1.viirG(I, R, F), G => values_1.VPi(true, mode_1.Impl, 'i', I, i => values_1.VPi(false, mode_1.Expl, '_', values_1.VIIRData(I, R, F, G, i), _ => values_1.vapp(R, mode_1.Expl, i)))))));
    // eqSymbol : Symbol -> Symbol -> Bool
    if (name === 'eqSymbol')
        return values_1.VPi(false, mode_1.Expl, '_', values_1.VSymbol, _ => values_1.VPi(false, mode_1.Expl, '_', values_1.VSymbol, _ => values_1.VBool));
    // unsafeGuardedCoerce : {-A -B -C : *} -> A -> (-guard : B) -> C
    if (name === 'unsafeGuardedCoerce')
        return values_1.VPi(true, mode_1.Impl, 'A', values_1.VType, A => values_1.VPi(true, mode_1.Impl, 'B', values_1.VType, B => values_1.VPi(true, mode_1.Impl, 'C', values_1.VType, C => values_1.VPi(false, mode_1.Expl, '_', A, _ => values_1.VPi(true, mode_1.Expl, 'guard', B, _ => C)))));
    return name;
};
exports.primType = primType;

},{"./mode":7,"./values":17}],11:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.runREPL = exports.initREPL = void 0;
const config_1 = require("./config");
const parser_1 = require("./parser");
const surface_1 = require("./surface");
const local_1 = require("./local");
const elaboration_1 = require("./elaboration");
const C = require("./core");
const verification_1 = require("./verification");
const values_1 = require("./values");
const utils_1 = require("./utils/utils");
const globals_1 = require("./globals");
const List_1 = require("./utils/List");
const help = `
COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showStackTrace] show stack trace of error
[:localGlue] enable/disable local glueing
[:unicode] show unicode
[:hideImplicits] hide implicits
[:showEnvs] show environments in debug logs
[:type or :t] do not normalize
[:defs] show definitions
[:clear] clear definitions
[:undoDef] undo last def
[:load name] load a global
`.trim();
let showStackTrace = false;
let doPreload = true;
let showFullNorm = false;
let showErasure = true;
let doVerify = true;
let local = local_1.Local.empty();
const initREPL = (web) => {
    showStackTrace = false;
    showFullNorm = false;
    doPreload = web;
    showErasure = true;
    local = local_1.Local.empty();
};
exports.initREPL = initREPL;
const runREPL = (s_, cb) => {
    try {
        let s = s_.trim();
        if (s === ':help' || s === ':h')
            return cb(help);
        if (s === ':d' || s === ':debug') {
            const d = !config_1.config.debug;
            config_1.setConfig({ debug: d });
            return cb(`debug: ${d}`);
        }
        if (s === ':localGlue') {
            const d = !config_1.config.localGlue;
            config_1.setConfig({ localGlue: d });
            return cb(`localGlue: ${d}`);
        }
        if (s === ':unicode') {
            const d = !config_1.config.unicode;
            config_1.setConfig({ unicode: d });
            return cb(`unicode: ${d}`);
        }
        if (s === ':showEnvs') {
            const d = !config_1.config.showEnvs;
            config_1.setConfig({ showEnvs: d });
            return cb(`showEnvs: ${d}`);
        }
        if (s === ':hideImplicits') {
            const d = !config_1.config.hideImplicits;
            config_1.setConfig({ hideImplicits: d });
            return cb(`hideImplicits: ${d}`);
        }
        if (s === ':postpone') {
            const d = !config_1.config.postpone;
            config_1.setConfig({ postpone: d });
            return cb(`postpone: ${d}`);
        }
        if (s === ':showStackTrace') {
            showStackTrace = !showStackTrace;
            return cb(`showStackTrace: ${showStackTrace}`);
        }
        if (s === ':showFullNorm') {
            showFullNorm = !showFullNorm;
            return cb(`showFullNorm: ${showFullNorm}`);
        }
        if (s === ':showErasure') {
            showErasure = !showErasure;
            return cb(`showErasure: ${showErasure}`);
        }
        if (s === ':preload') {
            doPreload = !doPreload;
            return cb(`preload: ${doPreload}`);
        }
        if (s === ':verify') {
            doVerify = !doVerify;
            return cb(`verify: ${doVerify}`);
        }
        if (s === ':defs') {
            const defs = [];
            for (let i = local.level - 1; i >= 0; i--) {
                const x = local.ns.index(i);
                const entry = local.ts.index(i);
                const u = entry.erased;
                const t = values_1.quote(entry.type, local.level);
                const v = values_1.quote(local.vs.index(i), local.level);
                defs.push(`${u ? '-' : ``}${x} : ${surface_1.showCore(t, local.ns)} = ${surface_1.showCore(v, local.ns)}`);
            }
            return cb(defs.join('\n'));
        }
        if (s === ':clear') {
            local = local_1.Local.empty();
            return cb(`cleared definitions`);
        }
        if (s === ':undoDef') {
            if (local.level > 0) {
                const name = local.ns.head;
                local = local.undo();
                return cb(`removed definition ${name}`);
            }
            cb(`no def to undo`);
        }
        if (s.startsWith(':load') || s.startsWith(':eload')) {
            const erased = s.startsWith(':eload');
            const name = `${s.slice(s.startsWith(':load') ? 5 : 6).trim()}`;
            utils_1.loadFile(name)
                .then(sc => parser_1.parse(sc))
                .then(e => doPreload ? globals_1.preload(e, local).then(() => e) : e)
                .then(e => {
                const [tm, ty] = elaboration_1.elaborate(e);
                verification_1.verify(tm);
                globals_1.setGlobal(name.slice(4), values_1.evaluate(ty, List_1.nil), values_1.evaluate(tm, List_1.nil), ty, tm, erased);
                cb(`loaded ${name}`);
            })
                .catch(err => cb('' + err, true));
            return;
        }
        let typeOnly = false;
        if (s.startsWith(':type') || s.startsWith(':t')) {
            typeOnly = true;
            s = s.startsWith(':type') ? s.slice(5) : s.slice(2);
        }
        if (s.startsWith(':'))
            throw new Error(`invalid command: ${s}`);
        config_1.log(() => 'PARSE');
        let term = parser_1.parse(s, true);
        let isDef = false;
        let erased = false;
        if (term.tag === 'Let' && term.body === null) {
            isDef = true;
            erased = term.erased;
            term = surface_1.Let(erased, term.name, term.type, term.val, surface_1.Var(term.name));
        }
        else if (term.tag === 'Import' && term.body === null) {
            isDef = true;
            term = surface_1.Import(term.term, term.imports, term.term);
        }
        config_1.log(() => surface_1.show(term));
        let prom = Promise.resolve();
        if (doPreload) {
            config_1.log(() => 'PRELOAD');
            prom = globals_1.preload(term, local).then(() => { });
        }
        prom.then(() => {
            config_1.log(() => 'ELABORATE');
            const [eterm, etype] = elaboration_1.elaborate(term, erased || typeOnly ? local.inType() : local);
            config_1.log(() => C.show(eterm));
            config_1.log(() => surface_1.showCore(eterm, local.ns));
            config_1.log(() => C.show(etype));
            config_1.log(() => surface_1.showCore(etype, local.ns));
            config_1.log(() => 'VERIFICATION');
            if (doVerify) {
                const verty = verification_1.verify(eterm, erased || typeOnly ? local.inType() : local);
                config_1.log(() => `verified type: ${surface_1.showCore(verty, local.ns)}`);
            }
            let normstr = '';
            if (showFullNorm) {
                config_1.log(() => 'NORMALIZE');
                const norm = values_1.normalize(eterm, local.level, local.vs, true);
                config_1.log(() => C.show(norm));
                config_1.log(() => surface_1.showCore(norm, local.ns));
                normstr += `\nnorm: ${surface_1.showCore(norm, local.ns)}`;
            }
            const etypestr = surface_1.showCore(etype, local.ns);
            const etermstr = surface_1.showCore(eterm, local.ns);
            if (isDef) {
                if (term.tag === 'Let') {
                    const value = values_1.evaluate(eterm, local.vs);
                    local = local.define(erased, term.name, values_1.evaluate(etype, local.vs), value, etype, eterm);
                }
                else if (term.tag === 'Import') {
                    let c = eterm;
                    while (c && c.tag === 'Let') {
                        local = local.define(c.erased, c.name, values_1.evaluate(c.type, local.vs), values_1.evaluate(c.val, local.vs), c.type, c.val);
                        c = c.body;
                    }
                }
                else
                    throw new Error(`invalid definition: ${term.tag}`);
            }
            return cb(`term: ${surface_1.show(term)}\ntype: ${etypestr}\netrm: ${etermstr}${normstr}`);
        }).catch(err => {
            if (showStackTrace)
                console.error(err);
            return cb(`${err}`, true);
        });
    }
    catch (err) {
        if (showStackTrace)
            console.error(err);
        return cb(`${err}`, true);
    }
};
exports.runREPL = runREPL;

},{"./config":1,"./core":2,"./elaboration":3,"./globals":4,"./local":5,"./parser":9,"./surface":12,"./utils/List":15,"./utils/utils":16,"./values":17,"./verification":18}],12:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.globalsInSurface = exports.freeVars = exports.freeVarsAll = exports.showVal = exports.showCore = exports.fromCore = exports.show = exports.flattenProj = exports.flattenPair = exports.flattenApp = exports.flattenAbs = exports.flattenSigma = exports.flattenPi = exports.Type = exports.PIndex = exports.PName = exports.PSnd = exports.PFst = exports.PProj = exports.Rigid = exports.Hole = exports.Meta = exports.Import = exports.Proj = exports.Pair = exports.Sigma = exports.App = exports.Abs = exports.Pi = exports.Ann = exports.Let = exports.SymbolLit = exports.Global = exports.Var = void 0;
const names_1 = require("./names");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const config_1 = require("./config");
const prims_1 = require("./prims");
const Var = (name) => ({ tag: 'Var', name });
exports.Var = Var;
const Global = (name) => ({ tag: 'Global', name });
exports.Global = Global;
const SymbolLit = (name) => ({ tag: 'SymbolLit', name });
exports.SymbolLit = SymbolLit;
const Let = (erased, name, type, val, body) => ({ tag: 'Let', erased, name, type, val, body });
exports.Let = Let;
const Ann = (term, type) => ({ tag: 'Ann', term, type });
exports.Ann = Ann;
const Pi = (erased, mode, name, type, body) => ({ tag: 'Pi', erased, mode, name, type, body });
exports.Pi = Pi;
const Abs = (erased, mode, name, type, body) => ({ tag: 'Abs', erased, mode, name, type, body });
exports.Abs = Abs;
const App = (fn, mode, arg) => ({ tag: 'App', fn, mode, arg });
exports.App = App;
const Sigma = (erased, name, type, body) => ({ tag: 'Sigma', erased, name, type, body });
exports.Sigma = Sigma;
const Pair = (fst, snd) => ({ tag: 'Pair', fst, snd });
exports.Pair = Pair;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const Import = (term, imports, body) => ({ tag: 'Import', term, imports, body });
exports.Import = Import;
const Meta = (id) => ({ tag: 'Meta', id });
exports.Meta = Meta;
const Hole = (name) => ({ tag: 'Hole', name });
exports.Hole = Hole;
const Rigid = (term) => ({ tag: 'Rigid', term });
exports.Rigid = Rigid;
const PProj = (proj) => ({ tag: 'PProj', proj });
exports.PProj = PProj;
exports.PFst = exports.PProj('fst');
exports.PSnd = exports.PProj('snd');
const PName = (name) => ({ tag: 'PName', name });
exports.PName = PName;
const PIndex = (index) => ({ tag: 'PIndex', index });
exports.PIndex = PIndex;
exports.Type = exports.Var('*');
const flattenPi = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Pi') {
        params.push([c.erased, c.mode, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenPi = flattenPi;
const flattenSigma = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Sigma') {
        params.push([c.erased, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenSigma = flattenSigma;
const flattenAbs = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Abs') {
        params.push([c.erased, c.mode, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenAbs = flattenAbs;
const flattenApp = (t) => {
    const args = [];
    let c = t;
    while (c.tag === 'App') {
        args.push([c.mode, c.arg]);
        c = c.fn;
    }
    return [c, args.reverse()];
};
exports.flattenApp = flattenApp;
const flattenPair = (t) => {
    const ps = [];
    let c = t;
    while (c.tag === 'Pair') {
        ps.push(c.fst);
        c = c.snd;
    }
    return [ps, c];
};
exports.flattenPair = flattenPair;
const flattenProj = (t) => {
    const r = [];
    while (t.tag === 'Proj') {
        r.push(t.proj);
        t = t.term;
    }
    return [t, r.reverse()];
};
exports.flattenProj = flattenProj;
const showP = (b, t) => b ? `(${exports.show(t)})` : exports.show(t);
const appIsSimple = (t) => {
    if (!config_1.config.hideImplicits)
        return false;
    if (t.tag !== 'App')
        return false;
    const [fn, args] = exports.flattenApp(t);
    return !args.some(([m]) => m.tag === 'Expl') && isSimple(fn);
};
const absIsSimple = (t) => {
    if (!config_1.config.hideImplicits)
        return false;
    if (t.tag !== 'Abs')
        return false;
    const [params, body] = exports.flattenAbs(t);
    return !params.some(([_, m]) => m.tag === 'Expl') && isSimple(body);
};
const isSimple = (t) => t.tag === 'Var' || t.tag === 'Global' || t.tag === 'SymbolLit' || t.tag === 'Hole' || t.tag === 'Meta' || t.tag === 'Pair' || t.tag === 'Proj' || appIsSimple(t) || absIsSimple(t);
const showS = (t) => showP(!isSimple(t), t);
const showProjType = (p) => {
    if (p.tag === 'PProj')
        return p.proj === 'fst' ? '_1' : '_2';
    if (p.tag === 'PName')
        return `${p.name}`;
    if (p.tag === 'PIndex')
        return `${p.index}`;
    return p;
};
const show = (t) => {
    if (t.tag === 'Global')
        return `${t.name}`;
    if (t.tag === 'Var')
        return t.name === '*' && config_1.config.unicode ? '★' : `${t.name}`;
    if (t.tag === 'SymbolLit')
        return `'${t.name}`;
    if (t.tag === 'Hole')
        return `_${t.name === null ? '' : t.name}`;
    if (t.tag === 'Meta')
        return `?${t.id}`;
    if (t.tag === 'Pi') {
        const [params, ret] = exports.flattenPi(t);
        const arr = config_1.config.unicode ? '→' : '->';
        return `${params.map(([e, m, x, t]) => !e && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${e ? '-' : ''}${x} : ${exports.show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(` ${arr} `)} ${arr} ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
    }
    if (t.tag === 'Abs') {
        const [params1, body] = exports.flattenAbs(t);
        const params = config_1.config.hideImplicits ? params1.filter(([_, m]) => m.tag === 'Expl') : params1;
        if (params.length === 0)
            return exports.show(t.body);
        return `${config_1.config.unicode ? 'λ' : '\\'}${params.map(([e, m, x, t]) => `${m.tag === 'Impl' ? '{' : t ? '(' : ''}${e ? '-' : ''}${x}${t ? ` : ${exports.show(t)}` : ''}${m.tag === 'Impl' ? '}' : t ? ')' : ''}`).join(' ')}. ${exports.show(body)}`;
    }
    if (t.tag === 'App') {
        const [fn, args1] = exports.flattenApp(t);
        const args = config_1.config.hideImplicits ? args1.filter(([m]) => m.tag === 'Expl') : args1;
        return `${showS(fn)}${args.length > 0 ? ' ' : ''}${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${exports.show(a)}}`).join(' ')}`;
    }
    if (t.tag === 'Sigma') {
        const [params, ret] = exports.flattenSigma(t);
        const prod = config_1.config.unicode ? '×' : '**';
        return `${params.map(([e, x, t]) => !e && x === '_' ? showP(t.tag === 'Sigma' || t.tag === 'Pi' || t.tag === 'Let', t) : `(${e ? '-' : ''}${x} : ${exports.show(t)})`).join(` ${prod} `)} ${prod} ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
    }
    if (t.tag === 'Pair') {
        const [ps, ret] = exports.flattenPair(t);
        if (ret.tag === 'Var' && ret.name === '[]')
            return `[${ps.map(exports.show).join(', ')}]`;
        return `(${ps.map(exports.show).join(', ')}, ${exports.show(ret)})`;
    }
    if (t.tag === 'Let')
        return `let ${t.erased ? '-' : ''}${t.name}${t.type ? ` : ${showP(t.type.tag === 'Let', t.type)}` : ''} = ${showP(t.val.tag === 'Let', t.val)}; ${exports.show(t.body)}`;
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
    }
    if (t.tag === 'Ann')
        return `${exports.show(t.term)} : ${exports.show(t.type)}`;
    if (t.tag === 'Import')
        return `import ${showS(t.term)}${t.imports ? ` (${t.imports.join(', ')})` : ''}; ${exports.show(t.body)}`;
    if (t.tag === 'Rigid')
        return `@${showS(t.term)}`;
    return t;
};
exports.show = show;
const fromCore = (t, ns = List_1.nil) => {
    if (t.tag === 'Var')
        return exports.Var(ns.index(t.index) || utils_1.impossible(`var out of scope in fromCore: ${t.index}`));
    if (t.tag === 'SymbolLit')
        return exports.SymbolLit(t.name);
    if (t.tag === 'Global')
        return exports.Global(t.name);
    if (t.tag === 'Prim')
        return exports.Var(t.name);
    if (t.tag === 'App')
        return exports.App(exports.fromCore(t.fn, ns), t.mode, exports.fromCore(t.arg, ns));
    if (t.tag === 'Pi') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Pi(t.erased, t.mode, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Abs') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Abs(t.erased, t.mode, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Let') {
        // de-elaborate annotations
        if (t.body.tag === 'Var' && t.body.index === 0)
            return exports.Ann(exports.fromCore(t.val, ns), exports.fromCore(t.type, ns));
        const x = names_1.chooseName(t.name, ns);
        return exports.Let(t.erased, x, exports.fromCore(t.type, ns), exports.fromCore(t.val, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Sigma') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Sigma(t.erased, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Pair')
        return exports.Pair(exports.fromCore(t.fst, ns), exports.fromCore(t.snd, ns));
    if (t.tag === 'Proj')
        return exports.Proj(exports.fromCore(t.term, ns), t.proj.tag === 'PProj' ? t.proj : t.proj.name ? exports.PName(t.proj.name) : exports.PIndex(t.proj.index));
    if (t.tag === 'Meta' || t.tag === 'InsertedMeta')
        return exports.Meta(t.id);
    return t;
};
exports.fromCore = fromCore;
const showCore = (t, ns = List_1.nil) => exports.show(exports.fromCore(t, ns));
exports.showCore = showCore;
const showVal = (v, k = 0, full = false, ns = List_1.nil) => exports.show(exports.fromCore(values_1.quote(v, k, full), ns));
exports.showVal = showVal;
const freeVarsAll = (t, a = []) => {
    if (t.tag === 'Var')
        return utils_1.pushUniq(a, t.name);
    if (t.tag === 'Hole')
        return a;
    if (t.tag === 'Pi') {
        exports.freeVarsAll(t.body, a);
        utils_1.remove(a, t.name);
        return exports.freeVarsAll(t.type, a);
    }
    if (t.tag === 'Abs') {
        exports.freeVarsAll(t.body, a);
        utils_1.remove(a, t.name);
        return t.type ? exports.freeVarsAll(t.type, a) : a;
    }
    if (t.tag === 'App') {
        exports.freeVarsAll(t.fn, a);
        return exports.freeVarsAll(t.arg, a);
    }
    if (t.tag === 'Let') {
        exports.freeVarsAll(t.body, a);
        utils_1.remove(a, t.name);
        exports.freeVarsAll(t.val, a);
        return t.type ? exports.freeVarsAll(t.type, a) : a;
    }
    if (t.tag === 'Import')
        return exports.freeVarsAll(t.term, a);
    if (t.tag === 'Sigma') {
        exports.freeVarsAll(t.body, a);
        utils_1.remove(a, t.name);
        return exports.freeVarsAll(t.type, a);
    }
    if (t.tag === 'Pair') {
        exports.freeVarsAll(t.fst, a);
        return exports.freeVarsAll(t.snd, a);
    }
    if (t.tag === 'Proj')
        return exports.freeVarsAll(t.term, a);
    if (t.tag === 'Ann') {
        exports.freeVarsAll(t.term, a);
        return exports.freeVarsAll(t.type, a);
    }
    if (t.tag === 'Rigid')
        return exports.freeVarsAll(t.term, a);
    return a;
};
exports.freeVarsAll = freeVarsAll;
const freeVars = (t) => {
    const vs = exports.freeVarsAll(t);
    utils_1.remove(vs, '_');
    utils_1.removeAll(vs, prims_1.PrimNames);
    return vs;
};
exports.freeVars = freeVars;
const globalsInSurface = (t, a = []) => {
    if (t.tag === 'Global')
        return utils_1.pushUniq(a, t.name);
    if (t.tag === 'Pi') {
        exports.globalsInSurface(t.body, a);
        return exports.globalsInSurface(t.type, a);
    }
    if (t.tag === 'Abs') {
        exports.globalsInSurface(t.body, a);
        return t.type ? exports.globalsInSurface(t.type, a) : a;
    }
    if (t.tag === 'App') {
        exports.globalsInSurface(t.fn, a);
        return exports.globalsInSurface(t.arg, a);
    }
    if (t.tag === 'Let') {
        exports.globalsInSurface(t.body, a);
        exports.globalsInSurface(t.val, a);
        return t.type ? exports.globalsInSurface(t.type, a) : a;
    }
    if (t.tag === 'Import')
        return exports.globalsInSurface(t.term, a);
    if (t.tag === 'Sigma') {
        exports.globalsInSurface(t.body, a);
        return exports.globalsInSurface(t.type, a);
    }
    if (t.tag === 'Pair') {
        exports.globalsInSurface(t.fst, a);
        return exports.globalsInSurface(t.snd, a);
    }
    if (t.tag === 'Proj')
        return exports.globalsInSurface(t.term, a);
    if (t.tag === 'Ann') {
        exports.globalsInSurface(t.term, a);
        return exports.globalsInSurface(t.type, a);
    }
    if (t.tag === 'Rigid')
        return exports.globalsInSurface(t.term, a);
    return a;
};
exports.globalsInSurface = globalsInSurface;

},{"./config":1,"./names":8,"./prims":10,"./utils/List":15,"./utils/utils":16,"./values":17}],13:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.unify = exports.eqHead = void 0;
const config_1 = require("./config");
const core_1 = require("./core");
const metas_1 = require("./metas");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const C = require("./core");
const mode_1 = require("./mode");
const verification_1 = require("./verification");
const local_1 = require("./local");
const insert = (map, key, value) => ({ ...map, [key]: value });
const deleteKey = (map, key) => {
    const n = {};
    for (let k in map) {
        if (+k !== key)
            n[k] = map[k];
    }
    return n;
};
const PRen = (occ, dom, cod, ren) => ({ occ, dom, cod, ren });
const lift = (pren) => PRen(pren.occ, pren.dom + 1, pren.cod + 1, insert(pren.ren, pren.cod, pren.dom));
const skip = (pren) => PRen(pren.occ, pren.dom, pren.cod + 1, pren.ren);
const invertSpine = (sp) => sp.foldr((app, [dom, ren, pr, isLinear]) => {
    if (app.tag !== 'EApp')
        return utils_1.terr(`not a variable in the spine: ${app.tag === 'EPrim' ? app.name : app.tag}`);
    const v = values_1.force(app.arg);
    if (!values_1.isVVar(v))
        return utils_1.terr(`not a variable in the spine`);
    const x = v.head.level;
    return typeof ren[x] === 'number' ?
        [dom + 1, deleteKey(ren, x), List_1.cons([app.mode, false], pr), false] :
        [dom + 1, insert(ren, x, dom), List_1.cons([app.mode, true], pr), isLinear];
}, [0, {}, List_1.nil, true]);
const invert = (gamma, sp) => {
    const [dom, ren, pr, isLinear] = invertSpine(sp);
    return [PRen(-1, dom, gamma, ren), isLinear ? pr : null];
};
const pruneTy = (pr, a_, pren = PRen(-1, 0, 0, {})) => {
    const a = values_1.force(a_);
    if (pr.isNil())
        return rename(pren, a);
    if (pr.isCons() && a.tag === 'VPi') {
        if (pr.head[1])
            return core_1.Pi(a.erased, a.mode, a.name, rename(pren, a.type), pruneTy(pr.tail, values_1.vinst(a, values_1.VVar(pren.cod)), lift(pren)));
        else
            return pruneTy(pr.tail, values_1.vinst(a, values_1.VVar(pren.cod)), skip(pren));
    }
    return utils_1.impossible(`pruneTy, not a pi: ${a.tag}`);
};
const pruneMeta = (pr, m) => {
    const entry = metas_1.getMeta(m);
    if (entry.tag === 'Solved')
        return utils_1.impossible(`pruneMeta, meta is solved: ?${m}`);
    const mty = entry.type;
    const prunedTy = values_1.evaluate(pruneTy(pr.reverse(), mty), List_1.nil);
    const m2 = metas_1.freshMeta(prunedTy, entry.erased);
    const solution = lams(pr.length(), mty, C.InsertedMeta(m2, pr));
    const vsolution = values_1.evaluate(solution, List_1.nil);
    metas_1.setMeta(m, vsolution);
    return [m2, prunedTy];
};
const pruneVFlexSpine = (pren, spine) => spine.foldr((app, [sp, status]) => {
    if (app.tag !== 'EApp')
        return utils_1.terr(`not a variable in the spine: ${app.tag === 'EPrim' ? app.name : app.tag}`);
    const v = values_1.force(app.arg);
    if (values_1.isVVar(v)) {
        const y = pren.ren[v.head.level];
        const contained = typeof y === 'number';
        if (contained)
            return [List_1.cons([core_1.Var(pren.dom - (y + 1)), app.mode], sp), status];
        if (status === 'OKNonRenaming')
            return utils_1.terr(`pruneVFlexSpine: failed to prune spine (1)`);
        return [List_1.cons([null, app.mode], sp), 'NeedsPruning'];
    }
    else {
        if (status === 'NeedsPruning')
            return utils_1.terr(`pruneVFlexSpine: failed to prune spine (2)`);
        const t = rename(pren, v);
        return [List_1.cons([t, app.mode], sp), 'OKNonRenaming'];
    }
}, [List_1.nil, 'OKRenaming']);
const pruneVFlex = (pren, m, sp_) => {
    const [sp, status] = pruneVFlexSpine(pren, sp_);
    let m2, mty;
    if (status === 'NeedsPruning')
        [m2, mty] = pruneMeta(sp.map(([t, i]) => [i, t !== null]), m);
    else {
        const entry = metas_1.getMeta(m);
        if (entry.tag === 'Solved')
            return utils_1.impossible(`pruneVFlex, solved meta: ?${m}`);
        [m2, mty] = [m, entry.type];
    }
    const t = sp.foldr(([mu, i], t) => mu ? core_1.App(t, i, mu) : t, core_1.Meta(m2));
    return [t, m2, mty];
};
const renameElim = (pren, t, e) => {
    if (e.tag === 'EApp')
        return core_1.App(t, e.mode, rename(pren, e.arg));
    if (e.tag === 'EProj')
        return C.Proj(t, e.proj);
    if (e.tag === 'EPrim')
        return core_1.App(e.args.reduce((x, [m, v]) => core_1.App(x, m, rename(pren, v)), core_1.Prim(e.name)), mode_1.Expl, t);
    return e;
};
const renameSpine = (pren, t, sp) => sp.foldr((app, fn) => renameElim(pren, fn, app), t);
const rename = (pren, v_) => {
    const v = values_1.force(v_, false);
    if (v.tag === 'VSymbolLit')
        return C.SymbolLit(v.name);
    if (v.tag === 'VRigid') {
        if (v.head.tag === 'HPrim')
            return renameSpine(pren, core_1.Prim(v.head.name), v.spine);
        const x = pren.ren[v.head.level];
        if (typeof x !== 'number')
            return utils_1.terr(`escaping variable '${v.head.level}`);
        return renameSpine(pren, core_1.Var(pren.dom - x - 1), v.spine);
    }
    if (v.tag === 'VGlobal') {
        if (v.head.tag === 'HLVar')
            return rename(pren, v.val.get());
        return renameSpine(pren, core_1.Global(v.head.name), v.spine); // TODO: should global be forced?
    }
    if (v.tag === 'VAbs')
        return core_1.Abs(v.erased, v.mode, v.name, rename(pren, v.type), rename(lift(pren), values_1.vinst(v, values_1.VVar(pren.cod))));
    if (v.tag === 'VPi')
        return core_1.Pi(v.erased, v.mode, v.name, rename(pren, v.type), rename(lift(pren), values_1.vinst(v, values_1.VVar(pren.cod))));
    if (v.tag === 'VSigma')
        return core_1.Sigma(v.erased, v.name, rename(pren, v.type), rename(lift(pren), values_1.vinst(v, values_1.VVar(pren.cod))));
    if (v.tag === 'VPair')
        return core_1.Pair(rename(pren, v.fst), rename(pren, v.snd), rename(pren, v.type));
    if (v.tag === 'VFlex') {
        const [m2, sp] = [v.head, v.spine];
        if (pren.occ === -1 || pren.occ !== m2) {
            const [t] = pruneVFlex(pren, m2, sp);
            return t;
        }
        return utils_1.terr(`occurs check failed: ${m2}`);
    }
    return v;
};
const lams = (lvl, a_, t, k = 0) => {
    if (lvl === k)
        return t;
    const a = values_1.force(a_);
    if (a.tag !== 'VPi')
        return utils_1.impossible(`lams, not a pi type: ${a.tag}`);
    const x = a.name === '_' ? `x${k}` : a.name;
    return core_1.Abs(a.erased, a.mode, x, values_1.quote(a.type, k), lams(lvl, values_1.vinst(a, values_1.VVar(k)), t, k + 1));
};
const solve = (gamma, m, sp, rhs_) => {
    config_1.log(() => `solve ?${m}${sp.reverse().toString(v => v.tag === 'EApp' ? `${v.mode.tag === 'Expl' ? '' : '{'}${values_1.show(v.arg, gamma)}${v.mode.tag === 'Expl' ? '' : '}'}` : v.tag === 'EPrim' ? v.name : v.tag)} := ${values_1.show(rhs_, gamma)}`);
    const pren = invert(gamma, sp);
    return solveWithPRen(gamma, m, pren, rhs_);
};
const solveWithPRen = (gamma, m, [pren, pruneNonlinear], rhs_) => {
    config_1.log(() => `solveWithPRen ?${m} ${pruneNonlinear ? '(pruneNonlinear)' : ''}`);
    const entry = metas_1.getMeta(m);
    if (entry.tag === 'Solved')
        return utils_1.impossible(`solveWithPRen, solved meta: ?${m}`);
    const mty = entry.type;
    config_1.log(() => `meta type: ${values_1.show(mty, gamma)}`);
    if (pruneNonlinear)
        pruneTy(pruneNonlinear.reverse(), mty);
    const rhs = rename(PRen(m, pren.dom, pren.cod, pren.ren), rhs_);
    const solutionq = lams(pren.dom, mty, rhs);
    config_1.log(() => `solution: ${C.show(solutionq)}`);
    if (config_1.config.verifyMetaSolutions) {
        const mtype = verification_1.verify(solutionq, entry.erased ? local_1.Local.empty().inType() : local_1.Local.empty());
        config_1.log(() => `meta verified: ${C.show(mtype)}`);
    }
    const solution = values_1.evaluate(solutionq, List_1.nil);
    metas_1.setMeta(m, solution);
};
const unifyPIndex = (k, va, vb, sa, sb, index) => {
    if (index === 0)
        return unifySpines(k, va, vb, sa, sb);
    if (sa.isCons() && sa.head.tag === 'EProj' && sa.head.proj.tag === 'PProj' && sa.head.proj.proj === 'snd')
        return unifyPIndex(k, va, vb, sa.tail, sb, index - 1);
    return utils_1.terr(`unify failed (${k}): ${values_1.show(va, k)} ~ ${values_1.show(vb, k)}`);
};
const unifySpines = (l, va, vb, sa, sb) => {
    config_1.log(() => `unifySpines: ${values_1.show(va, l)} (${sa.length()}) ~ ${values_1.show(vb, l)} (${sb.length()})`);
    if (sa.isNil() && sb.isNil())
        return;
    if (sa.isCons() && sb.isCons()) {
        const a = sa.head;
        const b = sb.head;
        if (a === b)
            return unifySpines(l, va, vb, sa.tail, sb.tail);
        if (a.tag === 'EApp' && b.tag === 'EApp' && mode_1.eqMode(a.mode, b.mode)) {
            exports.unify(l, a.arg, b.arg);
            return unifySpines(l, va, vb, sa.tail, sb.tail);
        }
        if (a.tag === 'EPrim' && b.tag === 'EPrim' && a.name === b.name && a.args.length === b.args.length) {
            for (let i = 0, l = a.args.length; i < l; i++) {
                if (!mode_1.eqMode(a.args[i][0], b.args[i][0]))
                    return utils_1.terr(`plicity mismatch in prim elim: ${values_1.show(va, l)} ~ ${values_1.show(vb, l)}`);
                exports.unify(l, a.args[i][1], b.args[i][1]);
            }
            return unifySpines(l, va, vb, sa.tail, sb.tail);
        }
        if (a.tag === 'EProj' && b.tag === 'EProj') {
            if (a.proj === b.proj)
                return unifySpines(l, va, vb, sa.tail, sb.tail);
            if (a.proj.tag === 'PProj' && b.proj.tag === 'PProj' && a.proj.proj === b.proj.proj)
                return unifySpines(l, va, vb, sa.tail, sb.tail);
            if (a.proj.tag === 'PIndex' && b.proj.tag === 'PIndex' && a.proj.index === b.proj.index)
                return unifySpines(l, va, vb, sa.tail, sb.tail);
            if (a.proj.tag === 'PProj' && a.proj.proj === 'fst' && b.proj.tag === 'PIndex')
                return unifyPIndex(l, va, vb, sa.tail, sb.tail, b.proj.index);
            if (b.proj.tag === 'PProj' && b.proj.proj === 'fst' && a.proj.tag === 'PIndex')
                return unifyPIndex(l, va, vb, sb.tail, sa.tail, a.proj.index);
            if (a.proj.tag === 'PIndex' && b.proj.tag === 'PIndex' && a.proj.index > b.proj.index)
                return unifySpines(l, va, vb, List_1.cons(values_1.EProj(core_1.PIndex(a.proj.name, a.proj.index - 1)), List_1.cons(values_1.EProj(core_1.PSnd), sa.tail)), sb);
            if (a.proj.tag === 'PIndex' && b.proj.tag === 'PIndex' && b.proj.index > a.proj.index)
                return unifySpines(l, va, vb, sa, List_1.cons(values_1.EProj(core_1.PIndex(b.proj.name, b.proj.index - 1)), List_1.cons(values_1.EProj(core_1.PSnd), sb.tail)));
        }
    }
    return utils_1.terr(`failed to unify: ${values_1.show(va, l)} ~ ${values_1.show(vb, l)}`);
};
const flexFlex = (l, m, sp, m2, sp2) => {
    if (sp.length() < sp2.length())
        return flexFlex(l, m2, sp2, m, sp);
    const res = utils_1.tryTE(() => invert(l, sp));
    if (res instanceof TypeError) {
        const pren = invert(l, sp2);
        return solveWithPRen(l, m2, pren, values_1.VFlex(m, sp));
    }
    else
        return solveWithPRen(l, m, res, values_1.VFlex(m2, sp2));
};
const intersectPruning = (sp, sp2) => {
    if (sp.isNil() && sp2.isNil())
        return List_1.nil;
    if (sp.isCons() && sp2.isCons()) {
        const app = sp.head;
        const app2 = sp2.head;
        if (app.tag !== 'EApp' || app2.tag !== 'EApp' || !mode_1.eqMode(app.mode, app2.mode))
            return null;
        const v = values_1.force(app.arg);
        const v2 = values_1.force(app2.arg);
        if (values_1.isVVar(v) && values_1.isVVar(v2)) {
            const prev = intersectPruning(sp.tail, sp2.tail);
            return prev && List_1.cons([app.mode, v.head.level === v2.head.level], prev);
        }
        return null;
    }
    return utils_1.impossible(`intersectPruning`);
};
const intersect = (l, m, sp, sp2, va, vb) => {
    const pr = intersectPruning(sp, sp2);
    if (pr)
        pruneMeta(pr, m);
    else
        unifySpines(l, va, vb, sp, sp2);
};
const eqHead = (a, b) => {
    if (a === b)
        return true;
    if (a.tag === 'HVar')
        return b.tag === 'HVar' && a.level === b.level;
    if (a.tag === 'HLVar')
        return b.tag === 'HLVar' && a.level === b.level;
    if (a.tag === 'HPrim')
        return b.tag === 'HPrim' && a.name === b.name;
    if (a.tag === 'HGlobal')
        return b.tag === 'HGlobal' && a.name === b.name;
    return a;
};
exports.eqHead = eqHead;
const unify = (l, a_, b_) => {
    const a = values_1.force(a_, false);
    const b = values_1.force(b_, false);
    config_1.log(() => `unify ${values_1.show(a, l)} ~ ${values_1.show(b, l)}`);
    if (a === b)
        return;
    if (a.tag === 'VSymbolLit' && b.tag === 'VSymbolLit' && a.name === b.name)
        return;
    if (a.tag === 'VAbs' && b.tag === 'VAbs') {
        const v = values_1.VVar(l);
        return exports.unify(l + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VAbs') {
        const v = values_1.VVar(l);
        return exports.unify(l + 1, values_1.vinst(a, v), values_1.vapp(b, a.mode, v));
    }
    if (b.tag === 'VAbs') {
        const v = values_1.VVar(l);
        return exports.unify(l + 1, values_1.vapp(a, b.mode, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VPi' && b.tag === 'VPi' && a.erased === b.erased && mode_1.eqMode(a.mode, b.mode)) {
        exports.unify(l, a.type, b.type);
        const v = values_1.VVar(l);
        return exports.unify(l + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.erased === b.erased) {
        exports.unify(l, a.type, b.type);
        const v = values_1.VVar(l);
        return exports.unify(l + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VPair' && b.tag === 'VPair') {
        exports.unify(l, a.fst, b.fst);
        exports.unify(l, a.snd, b.snd);
        return;
    }
    if (a.tag === 'VPair' && b.tag !== 'VFlex') {
        exports.unify(l, a.fst, values_1.vproj(b, core_1.PFst));
        exports.unify(l, a.snd, values_1.vproj(b, core_1.PSnd));
        return;
    }
    if (b.tag === 'VPair' && a.tag !== 'VFlex') {
        exports.unify(l, values_1.vproj(a, core_1.PFst), b.fst);
        exports.unify(l, values_1.vproj(a, core_1.PSnd), b.snd);
        return;
    }
    if (primEta(a) || primEta(b))
        return;
    if (a.tag === 'VRigid' && b.tag === 'VRigid' && exports.eqHead(a.head, b.head))
        return utils_1.tryT(() => unifySpines(l, a, b, a.spine, b.spine), e => utils_1.terr(`failed to unify: ${values_1.show(a, l)} ~ ${values_1.show(b, l)}: ${e}`));
    if (a.tag === 'VFlex' && b.tag === 'VFlex')
        return a.head === b.head ?
            utils_1.tryT(() => intersect(l, a.head, a.spine, b.spine, a, b), e => utils_1.terr(`failed to unify: ${values_1.show(a, l)} ~ ${values_1.show(b, l)}: ${e}`)) :
            utils_1.tryT(() => flexFlex(l, a.head, a.spine, b.head, b.spine), e => utils_1.terr(`failed to unify: ${values_1.show(a, l)} ~ ${values_1.show(b, l)}: ${e}`));
    if (a.tag === 'VFlex')
        return solve(l, a.head, a.spine, b);
    if (b.tag === 'VFlex')
        return solve(l, b.head, b.spine, a);
    if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && exports.eqHead(a.head, b.head) && (config_1.config.localGlue || a.head.tag !== 'HLVar'))
        return utils_1.tryT(() => unifySpines(l, a, b, a.spine, b.spine), () => exports.unify(l, a.val.get(), b.val.get()));
    if (a.tag === 'VGlobal')
        return exports.unify(l, a.val.get(), b);
    if (b.tag === 'VGlobal')
        return exports.unify(l, a, b.val.get());
    return utils_1.terr(`failed to unify: ${values_1.show(a, l)} ~ ${values_1.show(b, l)}`);
};
exports.unify = unify;
const primEta = (a) => {
    const pa = values_1.getVPrim(a);
    if (pa) {
        const [x] = pa;
        if (x === '[]')
            return true;
    }
    return false;
};

},{"./config":1,"./core":2,"./local":5,"./metas":6,"./mode":7,"./utils/List":15,"./utils/utils":16,"./values":17,"./verification":18}],14:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Lazy = void 0;
class Lazy {
    constructor(fn) {
        this.forced = false;
        this.value = null;
        this.fn = fn;
    }
    static from(fn) {
        return new Lazy(fn);
    }
    static of(val) {
        return Lazy.from(() => val);
    }
    static value(val) {
        const l = new Lazy(() => val);
        l.forced = true;
        l.value = val;
        return l;
    }
    get() {
        if (!this.forced) {
            this.value = this.fn();
            this.forced = true;
        }
        return this.value;
    }
    map(fn) {
        return new Lazy(() => fn(this.get()));
    }
}
exports.Lazy = Lazy;

},{}],15:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.cons = exports.nil = exports.Cons = exports.Nil = exports.List = void 0;
const utils_1 = require("./utils");
class List {
    static Nil() {
        if (List._Nil === undefined)
            List._Nil = new Nil();
        return List._Nil;
    }
    static Cons(head, tail) { return new Cons(head, tail); }
    static from(values) {
        let l = List.Nil();
        for (let i = values.length - 1; i >= 0; i--)
            l = List.Cons(values[i], l);
        return l;
    }
    static of(...values) { return List.from(values); }
    static range(n) {
        let l = List.Nil();
        for (let i = 0; i < n; i++)
            l = List.Cons(i, l);
        return l;
    }
    toString(fn = val => `${val}`) {
        return `[${this.toMappedArray(fn).join(', ')}]`;
    }
    contains(val) { return this.indexOf(val) >= 0; }
}
exports.List = List;
class Nil extends List {
    isNil() { return true; }
    isCons() { return false; }
    case(nil, _cons) { return nil(); }
    caseFull(nil, _cons) { return nil(this); }
    toString() { return '[]'; }
    toMappedArray() { return []; }
    toArray() { return []; }
    map() { return this; }
    each() { }
    index() { return null; }
    updateAt() { return this; }
    findIndex() { return -1; }
    find() { return null; }
    indexOf() { return -1; }
    contains() { return false; }
    reverse() { return this; }
    zip() { return this; }
    zipWith() { return this; }
    zipWith_() { }
    zipWithR_() { }
    foldr(_cons, nil) { return nil; }
    foldl(_cons, nil) { return nil; }
    length() { return 0; }
    uncons() { return utils_1.impossible('uncons called on Nil'); }
    append(o) { return o; }
}
exports.Nil = Nil;
class Cons extends List {
    constructor(head, tail) {
        super();
        this.head = head;
        this.tail = tail;
    }
    isNil() { return false; }
    isCons() { return true; }
    case(_nil, cons) { return cons(this.head, this.tail); }
    caseFull(_nil, cons) { return cons(this); }
    toMappedArray(fn) {
        const r = [];
        let c = this;
        while (c.isCons()) {
            r.push(fn(c.head));
            c = c.tail;
        }
        return r;
    }
    toArray() {
        const r = [];
        let c = this;
        while (c.isCons()) {
            r.push(c.head);
            c = c.tail;
        }
        return r;
    }
    map(fn) {
        return new Cons(fn(this.head), this.tail.map(fn));
    }
    each(fn) {
        let c = this;
        while (c.isCons()) {
            fn(c.head);
            c = c.tail;
        }
    }
    index(ix) {
        if (ix < 0)
            return utils_1.impossible(`index with negative index: ${ix}`);
        if (ix === 0)
            return this.head;
        let i = ix;
        let c = this;
        while (c.isCons()) {
            if (i <= 0)
                return c.head;
            c = c.tail;
            i--;
        }
        return null;
    }
    updateAt(ix, fn) {
        if (ix < 0)
            return utils_1.impossible(`updateAt with negative index: ${ix}`);
        if (ix === 0)
            return new Cons(fn(this.head), this.tail);
        return new Cons(this.head, this.tail.updateAt(ix - 1, fn));
    }
    findIndex(fn) {
        let i = 0;
        let c = this;
        while (c.isCons()) {
            if (fn(c.head))
                return i;
            c = c.tail;
            i++;
        }
        return -1;
    }
    find(fn) {
        let c = this;
        while (c.isCons()) {
            if (fn(c.head))
                return c.head;
            c = c.tail;
        }
        return null;
    }
    indexOf(val) {
        let i = 0;
        let c = this;
        while (c.isCons()) {
            if (c.head === val)
                return i;
            c = c.tail;
            i++;
        }
        return -1;
    }
    reverse() {
        let c = this;
        let r = List.Nil();
        while (c.isCons()) {
            r = new Cons(c.head, r);
            c = c.tail;
        }
        return r;
    }
    zip(b) {
        if (b.isCons())
            return new Cons([this.head, b.head], this.tail.zip(b.tail));
        return List.Nil();
    }
    zipWith(b, fn) {
        if (b.isCons())
            return new Cons(fn(this.head, b.head), this.tail.zipWith(b.tail, fn));
        return List.Nil();
    }
    zipWith_(o, fn) {
        let a = this;
        let b = o;
        while (a.isCons() && b.isCons()) {
            fn(a.head, b.head);
            a = a.tail;
            b = b.tail;
        }
    }
    zipWithR_(o, fn) {
        if (o.isCons()) {
            this.tail.zipWithR_(o.tail, fn);
            fn(this.head, o.head);
        }
    }
    foldr(cons, nil) {
        return cons(this.head, this.tail.foldr(cons, nil));
    }
    foldl(cons, nil) {
        return this.tail.foldl(cons, cons(nil, this.head));
    }
    length() {
        let i = 0;
        let c = this;
        while (c.isCons()) {
            c = c.tail;
            i++;
        }
        return i;
    }
    uncons() {
        return [this.head, this.tail];
    }
    append(o) { return exports.cons(this.head, this.tail.append(o)); }
}
exports.Cons = Cons;
exports.nil = new Nil();
const cons = (head, tail) => new Cons(head, tail);
exports.cons = cons;

},{"./utils":16}],16:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.iterate = exports.removeAll = exports.remove = exports.pushUniq = exports.eqArr = exports.mapObj = exports.tryTE = exports.tryT = exports.hasDuplicates = exports.range = exports.loadFileSync = exports.loadFile = exports.serr = exports.terr = exports.impossible = void 0;
const impossible = (msg) => {
    throw new Error(`impossible: ${msg}`);
};
exports.impossible = impossible;
const terr = (msg) => {
    throw new TypeError(msg);
};
exports.terr = terr;
const serr = (msg) => {
    throw new SyntaxError(msg);
};
exports.serr = serr;
const loadFile = (fn) => {
    if (typeof window === 'undefined') {
        return new Promise((resolve, reject) => {
            require('fs').readFile(fn, 'utf8', (err, data) => {
                if (err)
                    return reject(err);
                return resolve(data);
            });
        });
    }
    else {
        return fetch(fn).then(r => r.text());
    }
};
exports.loadFile = loadFile;
const loadFileSync = (fn) => {
    if (typeof window === 'undefined') {
        try {
            return require('fs').readFileSync(fn, 'utf8');
        }
        catch (err) {
            return err;
        }
    }
    else {
        return new Error(`cannot synchronously retrieve file in browser: ${fn}`);
    }
};
exports.loadFileSync = loadFileSync;
const range = (n) => {
    const a = Array(n);
    for (let i = 0; i < n; i++)
        a[i] = i;
    return a;
};
exports.range = range;
const hasDuplicates = (x) => {
    const m = {};
    for (let i = 0; i < x.length; i++) {
        const y = `${x[i]}`;
        if (m[y])
            return true;
        m[y] = true;
    }
    return false;
};
exports.hasDuplicates = hasDuplicates;
const tryT = (v, e, throwErr = false) => {
    try {
        return v();
    }
    catch (err) {
        if (!(err instanceof TypeError))
            throw err;
        const r = e(err);
        if (throwErr)
            throw err;
        return r;
    }
};
exports.tryT = tryT;
const tryTE = (v) => exports.tryT(v, err => err);
exports.tryTE = tryTE;
const mapObj = (o, fn) => {
    const n = {};
    for (const k in o)
        n[k] = fn(o[k]);
    return n;
};
exports.mapObj = mapObj;
const eqArr = (a, b, eq = (x, y) => x === y) => {
    const l = a.length;
    if (b.length !== l)
        return false;
    for (let i = 0; i < l; i++)
        if (!eq(a[i], b[i]))
            return false;
    return true;
};
exports.eqArr = eqArr;
const pushUniq = (a, x) => a.includes(x) ? a : (a.push(x), a);
exports.pushUniq = pushUniq;
const remove = (a, x) => {
    const i = a.indexOf(x);
    return i >= 0 ? a.splice(i, 1) : a;
};
exports.remove = remove;
const removeAll = (a, xs) => {
    xs.forEach(x => exports.remove(a, x));
    return a;
};
exports.removeAll = removeAll;
const iterate = (n, x, f) => {
    for (let i = 0; i < n; i++)
        x = f(x);
    return x;
};
exports.iterate = iterate;

},{"fs":20}],17:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.velimBD = exports.vfunIIRDataPartial = exports.vprimelim = exports.vproj = exports.vapp4 = exports.vapp3 = exports.vapp2 = exports.vapp = exports.velimSpine = exports.velim = exports.force = exports.isVUnit = exports.isVUnitType = exports.isVNilary = exports.getVPrim = exports.isVVar = exports.viirG = exports.viirF = exports.VIIRCon = exports.VIIRData = exports.VIIRDataPartial = exports.VEq = exports.VHRefl = exports.VHEq = exports.VSymbol = exports.VFalse = exports.VTrue = exports.VBool = exports.VUnitType = exports.VType = exports.vprim = exports.VPrim = exports.VMeta = exports.VVar = exports.vinst = exports.VSymbolLit = exports.VPair = exports.VSigma = exports.VPi = exports.VAbs = exports.VGlobal = exports.VFlex = exports.VRigid = exports.EPrim = exports.EProj = exports.EApp = exports.HLVar = exports.HGlobal = exports.HPrim = exports.HVar = void 0;
exports.zonk = exports.show = exports.normalize = exports.quote = exports.evaluate = void 0;
const core_1 = require("./core");
const metas_1 = require("./metas");
const Lazy_1 = require("./utils/Lazy");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const globals_1 = require("./globals");
const mode_1 = require("./mode");
const config_1 = require("./config");
const HVar = (level) => ({ tag: 'HVar', level });
exports.HVar = HVar;
const HPrim = (name) => ({ tag: 'HPrim', name });
exports.HPrim = HPrim;
const HGlobal = (name) => ({ tag: 'HGlobal', name });
exports.HGlobal = HGlobal;
const HLVar = (level) => ({ tag: 'HLVar', level });
exports.HLVar = HLVar;
const EApp = (mode, arg) => ({ tag: 'EApp', mode, arg });
exports.EApp = EApp;
const EProj = (proj) => ({ tag: 'EProj', proj });
exports.EProj = EProj;
const EPrim = (name, args) => ({ tag: 'EPrim', name, args });
exports.EPrim = EPrim;
const VRigid = (head, spine) => ({ tag: 'VRigid', head, spine });
exports.VRigid = VRigid;
const VFlex = (head, spine) => ({ tag: 'VFlex', head, spine });
exports.VFlex = VFlex;
;
const VGlobal = (head, spine, val) => ({ tag: 'VGlobal', head, spine, val });
exports.VGlobal = VGlobal;
const VAbs = (erased, mode, name, type, clos) => ({ tag: 'VAbs', erased, mode, name, type, clos });
exports.VAbs = VAbs;
const VPi = (erased, mode, name, type, clos) => ({ tag: 'VPi', erased, mode, name, type, clos });
exports.VPi = VPi;
const VSigma = (erased, name, type, clos) => ({ tag: 'VSigma', erased, name, type, clos });
exports.VSigma = VSigma;
const VPair = (fst, snd, type) => ({ tag: 'VPair', fst, snd, type });
exports.VPair = VPair;
const VSymbolLit = (name) => ({ tag: 'VSymbolLit', name });
exports.VSymbolLit = VSymbolLit;
const vinst = (val, arg) => val.clos(arg);
exports.vinst = vinst;
const VVar = (level, spine = List_1.nil) => exports.VRigid(exports.HVar(level), spine);
exports.VVar = VVar;
const VMeta = (meta, spine = List_1.nil) => exports.VFlex(meta, spine);
exports.VMeta = VMeta;
const VPrim = (name, spine = List_1.nil) => exports.VRigid(exports.HPrim(name), spine);
exports.VPrim = VPrim;
const vprim = (name, spine = []) => exports.VPrim(name, List_1.List.from(spine.slice().reverse()));
exports.vprim = vprim;
exports.VType = exports.VPrim('*');
exports.VUnitType = exports.VPrim('()');
exports.VBool = exports.VPrim('Bool');
exports.VTrue = exports.VPrim('True');
exports.VFalse = exports.VPrim('False');
exports.VSymbol = exports.VPrim('Symbol');
const VHEq = (A, B, x, y) => exports.VPrim('HEq', List_1.List.of(exports.EApp(mode_1.Expl, y), exports.EApp(mode_1.Expl, x), exports.EApp(mode_1.Impl, B), exports.EApp(mode_1.Impl, A)));
exports.VHEq = VHEq;
const VHRefl = (A, x) => exports.VPrim('HRefl', List_1.List.of(exports.EApp(mode_1.Impl, x), exports.EApp(mode_1.Impl, A)));
exports.VHRefl = VHRefl;
const VEq = (A, x, y) => exports.VHEq(A, A, x, y);
exports.VEq = VEq;
// IIRData {I} {R} F G
const VIIRDataPartial = (I, R, F, G) => exports.vprim('IIRData', [exports.EApp(mode_1.Impl, I), exports.EApp(mode_1.Impl, R), exports.EApp(mode_1.Expl, F), exports.EApp(mode_1.Expl, G)]);
exports.VIIRDataPartial = VIIRDataPartial;
// IIRData {I} {R} F G i
const VIIRData = (I, R, F, G, i) => exports.vprim('IIRData', [exports.EApp(mode_1.Impl, I), exports.EApp(mode_1.Impl, R), exports.EApp(mode_1.Expl, F), exports.EApp(mode_1.Expl, G), exports.EApp(mode_1.Expl, i)]);
exports.VIIRData = VIIRData;
// IIRCon {I} {R} {F} {G} {i} x
const VIIRCon = (I, R, F, G, i, x) => exports.vprim('IIRCon', [exports.EApp(mode_1.Impl, I), exports.EApp(mode_1.Impl, R), exports.EApp(mode_1.Impl, F), exports.EApp(mode_1.Impl, G), exports.EApp(mode_1.Impl, i), exports.EApp(mode_1.Expl, x)]);
exports.VIIRCon = VIIRCon;
// (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *
const viirF = (I, R) => exports.VPi(false, mode_1.Expl, 'S', exports.VPi(false, mode_1.Expl, '_', I, _ => exports.VType), S => exports.VPi(false, mode_1.Expl, '_', exports.VPi(true, mode_1.Impl, 'i', I, i => exports.VPi(false, mode_1.Expl, '_', exports.vapp(S, mode_1.Expl, i), _ => exports.vapp(R, mode_1.Expl, i))), _ => exports.VPi(false, mode_1.Expl, '_', I, _ => exports.VType)));
exports.viirF = viirF;
// {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i
const viirG = (I, R, F) => exports.VPi(true, mode_1.Impl, 'S', exports.VPi(false, mode_1.Expl, '_', I, _ => exports.VType), S => exports.VPi(false, mode_1.Expl, 'T', exports.VPi(true, mode_1.Impl, 'i', I, i => exports.VPi(false, mode_1.Expl, '_', exports.vapp(S, mode_1.Expl, i), _ => exports.vapp(R, mode_1.Expl, i))), T => exports.VPi(true, mode_1.Impl, 'i', I, i => exports.VPi(false, mode_1.Expl, '_', exports.vapp3(F, mode_1.Expl, S, mode_1.Expl, T, mode_1.Expl, i), _ => exports.vapp(R, mode_1.Expl, i)))));
exports.viirG = viirG;
const isVVar = (v) => v.tag === 'VRigid' && v.head.tag === 'HVar' && v.spine.isNil();
exports.isVVar = isVVar;
const getVPrim = (v) => {
    if (v.tag === 'VRigid' && v.head.tag === 'HPrim') {
        const x = v.head.name;
        const args = [];
        let allApps = true;
        v.spine.each(e => {
            if (e.tag !== 'EApp') {
                allApps = false;
                return;
            }
            args.push(e.arg);
        });
        if (!allApps)
            return null;
        return [x, args.reverse()];
    }
    return null;
};
exports.getVPrim = getVPrim;
const isVNilary = (v, x) => {
    const res = exports.getVPrim(v);
    if (!res)
        return false;
    const [name, args] = res;
    return name === x && args.length === 0;
};
exports.isVNilary = isVNilary;
const isVUnitType = (v) => exports.isVNilary(v, '()');
exports.isVUnitType = isVUnitType;
const isVUnit = (v) => exports.isVNilary(v, '[]');
exports.isVUnit = isVUnit;
const force = (v, forceGlobal = true) => {
    if (v.tag === 'VGlobal' && forceGlobal)
        return exports.force(v.val.get(), forceGlobal);
    if (v.tag === 'VFlex') {
        const e = metas_1.getMeta(v.head);
        return e.tag === 'Solved' ? exports.force(exports.velimSpine(e.solution, v.spine), forceGlobal) : v;
    }
    return v;
};
exports.force = force;
const velim = (e, t) => {
    if (e.tag === 'EApp')
        return exports.vapp(t, e.mode, e.arg);
    if (e.tag === 'EProj')
        return exports.vproj(t, e.proj);
    if (e.tag === 'EPrim')
        return exports.vprimelim(e.name, t, e.args);
    return e;
};
exports.velim = velim;
const velimSpine = (t, sp) => sp.foldr(exports.velim, t);
exports.velimSpine = velimSpine;
const vapp = (left, mode, right) => {
    if (left.tag === 'VAbs')
        return exports.vinst(left, right); // TODO: erasure check?
    if (left.tag === 'VRigid')
        return exports.VRigid(left.head, List_1.cons(exports.EApp(mode, right), left.spine));
    if (left.tag === 'VFlex')
        return exports.VFlex(left.head, List_1.cons(exports.EApp(mode, right), left.spine));
    if (left.tag === 'VGlobal')
        return exports.VGlobal(left.head, List_1.cons(exports.EApp(mode, right), left.spine), left.val.map(v => exports.vapp(v, mode, right)));
    return utils_1.impossible(`vapp: ${left.tag}`);
};
exports.vapp = vapp;
const vapp2 = (f, m1, a, m2, b) => exports.vapp(exports.vapp(f, m1, a), m2, b);
exports.vapp2 = vapp2;
const vapp3 = (f, m1, a, m2, b, m3, c) => exports.vapp(exports.vapp(exports.vapp(f, m1, a), m2, b), m3, c);
exports.vapp3 = vapp3;
const vapp4 = (f, m1, a, m2, b, m3, c, m4, d) => exports.vapp(exports.vapp(exports.vapp(exports.vapp(f, m1, a), m2, b), m3, c), m4, d);
exports.vapp4 = vapp4;
const vproj = (scrut, proj) => {
    if (scrut.tag === 'VPair') {
        if (proj.tag === 'PProj')
            return proj.proj === 'fst' ? scrut.fst : scrut.snd;
        if (proj.tag === 'PIndex') {
            if (proj.index === 0)
                return scrut.fst;
            return exports.vproj(scrut.snd, core_1.PIndex(proj.name, proj.index - 1));
        }
        return proj;
    }
    if (scrut.tag === 'VRigid')
        return exports.VRigid(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine));
    if (scrut.tag === 'VFlex')
        return exports.VFlex(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine));
    if (scrut.tag === 'VGlobal')
        return exports.VGlobal(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine), scrut.val.map(v => exports.vproj(v, proj)));
    return utils_1.impossible(`vproj: ${scrut.tag}`);
};
exports.vproj = vproj;
const isNeutral = (v) => v.tag === 'VFlex' || v.tag === 'VRigid' || (v.tag === 'VGlobal' && isNeutral(v.val.get()));
const vprimelim = (name, scrut, args) => {
    if (name === 'eqSymbol' && scrut.tag === 'VSymbolLit' && args[0][1].tag === 'VSymbolLit')
        return scrut.name === args[0][1].name ? exports.VTrue : exports.VFalse;
    const res = exports.getVPrim(scrut);
    if (res) {
        const [x, spine] = res;
        // elimHEq {A} {a} P h {b} (HRefl {A} {a}) ~> h
        if (name === 'elimHEq' && x === 'HRefl')
            return args[3][1];
        if (name === 'elimBool') {
            if (x === 'True')
                return args[1][1];
            if (x === 'False')
                return args[2][1];
        }
        /*
        elimData {I} {R} {F} {G} P alg {i} (Con {I} {R} {F} {G} {i} x)
        ~>
        alg (\{j} z. elimData {I} {R} {F} {G} P alg {j} z) {i} x
        */
        if (name === 'elimIIRData' && x === 'IIRCon') {
            const x = spine[5];
            const I = args[0][1];
            const R = args[1][1];
            const F = args[2][1];
            const G = args[3][1];
            const P = args[4][1];
            const alg = args[5][1];
            const i = args[6][1];
            const rec = exports.VAbs(true, mode_1.Impl, 'i', I, i => exports.VAbs(false, mode_1.Expl, 'z', exports.VIIRData(I, R, F, G, i), z => exports.vprimelim('elimIIRData', z, [[mode_1.Impl, I], [mode_1.Impl, R], [mode_1.Impl, F], [mode_1.Impl, G], [mode_1.Expl, P], [mode_1.Expl, alg], [mode_1.Impl, i]])));
            return exports.vapp3(alg, mode_1.Expl, rec, mode_1.Impl, i, mode_1.Expl, x);
        }
        /*
        funData {I} {R} {F} {G} {i} (Con {I} {R} {F} {G} {i} x)
        ~>
        G {Data {I} {R} F G} (funData {I} {R} {F} {G}) {i} x
        */
        if (name === 'funIIRData' && x === 'IIRCon') {
            const x = spine[5];
            const I = args[0][1];
            const R = args[1][1];
            const F = args[2][1];
            const G = args[3][1];
            const i = args[4][1];
            return exports.vapp4(G, mode_1.Impl, exports.VIIRDataPartial(I, R, F, G), mode_1.Expl, exports.vfunIIRDataPartial(I, R, F, G), mode_1.Impl, i, mode_1.Expl, x);
        }
    }
    if (name === 'unsafeGuardedCoerce' && !isNeutral(scrut))
        return args[3][1];
    if (scrut.tag === 'VRigid')
        return exports.VRigid(scrut.head, List_1.cons(exports.EPrim(name, args), scrut.spine));
    if (scrut.tag === 'VFlex')
        return exports.VFlex(scrut.head, List_1.cons(exports.EPrim(name, args), scrut.spine));
    if (scrut.tag === 'VGlobal')
        return exports.VGlobal(scrut.head, List_1.cons(exports.EPrim(name, args), scrut.spine), scrut.val.map(v => exports.vprimelim(name, v, args)));
    return utils_1.impossible(`vprimelim ${name}: ${scrut.tag}`);
};
exports.vprimelim = vprimelim;
// \{-i : I} (x : IIRData {I} {R} F G i). funData {I} {R} {F} {G} {i} x
const vfunIIRDataPartial = (I, R, F, G) => exports.VAbs(true, mode_1.Impl, 'i', I, i => exports.VAbs(false, mode_1.Expl, 'x', exports.VIIRData(I, R, F, G, i), x => exports.vprimelim('funIIRData', x, [[mode_1.Impl, I], [mode_1.Impl, R], [mode_1.Impl, F], [mode_1.Impl, G], [mode_1.Impl, i]])));
exports.vfunIIRDataPartial = vfunIIRDataPartial;
const velimBD = (env, v, s) => {
    if (env.isNil() && s.isNil())
        return v;
    if (env.isCons() && s.isCons())
        return s.head[1] ? exports.vapp(exports.velimBD(env.tail, v, s.tail), s.head[0], env.head) : exports.velimBD(env.tail, v, s.tail);
    return utils_1.impossible('velimBD');
};
exports.velimBD = velimBD;
const evaluate = (t, vs, glueBefore = vs.length()) => {
    if (t.tag === 'Abs')
        return exports.VAbs(t.erased, t.mode, t.name, exports.evaluate(t.type, vs, glueBefore), v => exports.evaluate(t.body, List_1.cons(v, vs), glueBefore));
    if (t.tag === 'Pi')
        return exports.VPi(t.erased, t.mode, t.name, exports.evaluate(t.type, vs, glueBefore), v => exports.evaluate(t.body, List_1.cons(v, vs), glueBefore));
    if (t.tag === 'Sigma')
        return exports.VSigma(t.erased, t.name, exports.evaluate(t.type, vs, glueBefore), v => exports.evaluate(t.body, List_1.cons(v, vs), glueBefore));
    if (t.tag === 'Meta')
        return exports.VMeta(t.id);
    if (t.tag === 'InsertedMeta')
        return exports.velimBD(vs, exports.VMeta(t.id), t.spine);
    if (t.tag === 'App')
        return exports.vapp(exports.evaluate(t.fn, vs, glueBefore), t.mode, exports.evaluate(t.arg, vs, glueBefore));
    if (t.tag === 'Pair')
        return exports.VPair(exports.evaluate(t.fst, vs, glueBefore), exports.evaluate(t.snd, vs, glueBefore), exports.evaluate(t.type, vs, glueBefore));
    if (t.tag === 'Let')
        return exports.evaluate(t.body, List_1.cons(exports.evaluate(t.val, vs, glueBefore), vs), glueBefore);
    if (t.tag === 'Proj')
        return exports.vproj(exports.evaluate(t.term, vs, glueBefore), t.proj);
    if (t.tag === 'Var') {
        const v = vs.index(t.index) || utils_1.impossible(`evaluate: var ${t.index} has no value`);
        const l = vs.length();
        const i = t.index;
        if (i >= l - glueBefore)
            return exports.VGlobal(exports.HLVar(l - i - 1), List_1.nil, Lazy_1.Lazy.value(v));
        return v;
    }
    if (t.tag === 'SymbolLit')
        return exports.VSymbolLit(t.name);
    if (t.tag === 'Global')
        return exports.VGlobal(exports.HGlobal(t.name), List_1.nil, Lazy_1.Lazy.from(() => {
            const e = globals_1.getGlobal(t.name);
            if (!e)
                return utils_1.impossible(`failed to load global ${t.name}`);
            return e.value;
        }));
    if (t.tag === 'Prim') {
        if (t.name === 'elimHEq')
            return exports.VAbs(true, mode_1.Impl, 'A', exports.VType, A => exports.VAbs(true, mode_1.Impl, 'a', A, a => exports.VAbs(true, mode_1.Expl, 'P', exports.VPi(false, mode_1.Impl, 'b', A, b => exports.VPi(false, mode_1.Expl, '', exports.VEq(A, a, b), _ => exports.VType)), P => exports.VAbs(false, mode_1.Expl, 'h', exports.vapp2(P, mode_1.Impl, a, mode_1.Expl, exports.VHRefl(A, a)), h => exports.VAbs(true, mode_1.Impl, 'b', A, b => exports.VAbs(false, mode_1.Expl, 'p', exports.VEq(A, a, b), p => exports.vprimelim('elimHEq', p, [[mode_1.Impl, A], [mode_1.Impl, a], [mode_1.Expl, P], [mode_1.Expl, h], [mode_1.Impl, b]])))))));
        if (t.name === 'elimBool')
            return exports.VAbs(true, mode_1.Expl, 'P', exports.VPi(false, mode_1.Expl, '_', exports.VBool, _ => exports.VType), P => exports.VAbs(false, mode_1.Expl, 't', exports.vapp(P, mode_1.Expl, exports.VTrue), t => exports.VAbs(false, mode_1.Expl, 'f', exports.vapp(P, mode_1.Expl, exports.VFalse), f => exports.VAbs(false, mode_1.Expl, 'b', exports.VBool, b => exports.vprimelim('elimBool', b, [[mode_1.Expl, P], [mode_1.Expl, t], [mode_1.Expl, f]])))));
        if (t.name === 'eqSymbol')
            return exports.VAbs(false, mode_1.Expl, 'a', exports.VSymbol, a => exports.VAbs(false, mode_1.Expl, 'b', exports.VSymbol, b => exports.vprimelim('eqSymbol', b, [[mode_1.Expl, a]])));
        if (t.name === 'elimIIRData')
            return exports.VAbs(true, mode_1.Impl, 'I', exports.VType, I => exports.VAbs(true, mode_1.Impl, 'R', exports.VPi(false, mode_1.Expl, '_', I, _ => exports.VType), R => exports.VAbs(true, mode_1.Impl, 'F', exports.viirF(I, R), F => exports.VAbs(false, mode_1.Impl, 'G', exports.viirG(I, R, F), G => exports.VAbs(true, mode_1.Expl, 'P', exports.VPi(false, mode_1.Impl, 'i', I, i => exports.VPi(false, mode_1.Expl, '_', exports.VIIRData(I, R, F, G, i), _ => exports.VType)), P => exports.VAbs(false, mode_1.Expl, 'alg', exports.VPi(false, mode_1.Expl, '_', exports.VPi(true, mode_1.Impl, 'j', I, j => exports.VPi(false, mode_1.Expl, 'z', exports.VIIRData(I, R, F, G, j), z => exports.vapp2(P, mode_1.Impl, j, mode_1.Expl, z))), _ => exports.VPi(true, mode_1.Impl, 'i', I, i => exports.VPi(false, mode_1.Expl, 'y', exports.vapp3(F, mode_1.Expl, exports.VIIRDataPartial(I, R, F, G), mode_1.Expl, exports.vfunIIRDataPartial(I, R, F, G), mode_1.Expl, i), y => exports.vapp2(P, mode_1.Impl, i, mode_1.Expl, exports.VIIRCon(I, R, F, G, i, y))))), alg => exports.VAbs(true, mode_1.Impl, 'i', I, i => exports.VAbs(false, mode_1.Expl, 'x', exports.VIIRData(I, R, F, G, i), x => exports.vprimelim('elimIIRData', x, [[mode_1.Impl, I], [mode_1.Impl, R], [mode_1.Impl, F], [mode_1.Impl, G], [mode_1.Expl, P], [mode_1.Expl, alg], [mode_1.Impl, i]])))))))));
        if (t.name === 'funIIRData')
            return exports.VAbs(true, mode_1.Impl, 'I', exports.VType, I => exports.VAbs(true, mode_1.Impl, 'R', exports.VPi(false, mode_1.Expl, '_', I, _ => exports.VType), R => exports.VAbs(true, mode_1.Impl, 'F', exports.viirF(I, R), F => exports.VAbs(false, mode_1.Impl, 'G', exports.viirG(I, R, F), G => exports.VAbs(true, mode_1.Impl, 'i', I, i => exports.VAbs(false, mode_1.Expl, 'x', exports.VIIRData(I, R, F, G, i), x => exports.vprimelim('funIIRData', x, [[mode_1.Impl, I], [mode_1.Impl, R], [mode_1.Impl, F], [mode_1.Impl, G], [mode_1.Impl, i]])))))));
        if (t.name === 'unsafeGuardedCoerce')
            return exports.VAbs(true, mode_1.Impl, 'A', exports.VType, A => exports.VAbs(true, mode_1.Impl, 'B', exports.VType, B => exports.VAbs(true, mode_1.Impl, 'C', exports.VType, C => exports.VAbs(false, mode_1.Expl, 'value', A, value => exports.VAbs(true, mode_1.Expl, 'guard', B, guard => exports.vprimelim('unsafeGuardedCoerce', guard, [[mode_1.Impl, A], [mode_1.Impl, B], [mode_1.Impl, C], [mode_1.Expl, value]]))))));
        return exports.VPrim(t.name);
    }
    return t;
};
exports.evaluate = evaluate;
const localGlueEscaped = (k, kBefore, v) => {
    const h = v.head;
    if (h.tag !== 'HLVar')
        return false;
    if (!config_1.config.localGlue)
        return true;
    return h.level >= kBefore;
};
const quoteHead = (h, k) => {
    if (h.tag === 'HVar')
        return core_1.Var(k - (h.level + 1));
    if (h.tag === 'HLVar')
        return core_1.Var(k - (h.level + 1));
    if (h.tag === 'HPrim')
        return core_1.Prim(h.name);
    if (h.tag === 'HGlobal')
        return core_1.Global(h.name);
    return h;
};
const quoteElim = (t, e, k, full, kBefore) => {
    if (e.tag === 'EApp')
        return core_1.App(t, e.mode, exports.quote(e.arg, k, full, kBefore));
    if (e.tag === 'EProj')
        return core_1.Proj(t, e.proj);
    if (e.tag === 'EPrim')
        return core_1.App(e.args.reduce((x, [m, v]) => core_1.App(x, m, exports.quote(v, k, full, kBefore)), core_1.Prim(e.name)), mode_1.Expl, t);
    return e;
};
const quote = (v_, k, full = false, kBefore = k) => {
    const v = exports.force(v_, false);
    if (v.tag === 'VSymbolLit')
        return core_1.SymbolLit(v.name);
    if (v.tag === 'VRigid')
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full, kBefore), quoteHead(v.head, k));
    if (v.tag === 'VFlex')
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full, kBefore), core_1.Meta(v.head));
    if (v.tag === 'VGlobal') {
        if (full || localGlueEscaped(k, kBefore, v))
            return exports.quote(v.val.get(), k, full, kBefore);
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full, kBefore), quoteHead(v.head, k));
    }
    if (v.tag === 'VAbs')
        return core_1.Abs(v.erased, v.mode, v.name, exports.quote(v.type, k, full, kBefore), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full, kBefore));
    if (v.tag === 'VPi')
        return core_1.Pi(v.erased, v.mode, v.name, exports.quote(v.type, k, full, kBefore), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full, kBefore));
    if (v.tag === 'VSigma')
        return core_1.Sigma(v.erased, v.name, exports.quote(v.type, k, full, kBefore), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full, kBefore));
    if (v.tag === 'VPair')
        return core_1.Pair(exports.quote(v.fst, k, full, kBefore), exports.quote(v.snd, k, full, kBefore), exports.quote(v.type, k, full, kBefore));
    return v;
};
exports.quote = quote;
const normalize = (t, k = 0, vs = List_1.nil, full = false) => exports.quote(exports.evaluate(t, vs), k, full);
exports.normalize = normalize;
const show = (v, k = 0, full = false) => core_1.show(exports.quote(v, k, full));
exports.show = show;
const zonkSpine = (tm, vs, k, full) => {
    if (tm.tag === 'Meta') {
        const s = metas_1.getMeta(tm.id);
        if (s.tag === 'Unsolved')
            return [true, exports.zonk(tm, vs, k, full)];
        return [false, s.solution];
    }
    if (tm.tag === 'App') {
        const spine = zonkSpine(tm.fn, vs, k, full);
        return spine[0] ?
            [true, core_1.App(spine[1], tm.mode, exports.zonk(tm.arg, vs, k, full))] :
            [false, exports.vapp(spine[1], tm.mode, exports.evaluate(tm.arg, vs))];
    }
    return [true, exports.zonk(tm, vs, k, full)];
};
const vzonkBD = (env, v, s) => {
    if (env.isNil() && s.isNil())
        return v;
    if (env.isCons() && s.isCons())
        return s.head[1] ? exports.vapp(vzonkBD(env.tail, v, s.tail), s.head[0], env.head) : vzonkBD(env.tail, v, s.tail);
    return utils_1.impossible('vzonkBD');
};
const zonk = (tm, vs = List_1.nil, k = 0, full = false) => {
    if (tm.tag === 'Meta') {
        const s = metas_1.getMeta(tm.id);
        if (s.tag === 'Unsolved')
            return tm;
        return exports.quote(s.solution, k, full);
    }
    if (tm.tag === 'InsertedMeta') {
        const s = metas_1.getMeta(tm.id);
        if (s.tag === 'Unsolved')
            return tm;
        return exports.quote(vzonkBD(vs, s.solution, tm.spine), k, full);
    }
    if (tm.tag === 'Pi')
        return core_1.Pi(tm.erased, tm.mode, tm.name, exports.zonk(tm.type, vs, k, full), exports.zonk(tm.body, List_1.cons(exports.VVar(k), vs), k + 1, full));
    if (tm.tag === 'Sigma')
        return core_1.Sigma(tm.erased, tm.name, exports.zonk(tm.type, vs, k, full), exports.zonk(tm.body, List_1.cons(exports.VVar(k), vs), k + 1, full));
    if (tm.tag === 'Let')
        return core_1.Let(tm.erased, tm.name, exports.zonk(tm.type, vs, k, full), exports.zonk(tm.val, vs, k, full), exports.zonk(tm.body, List_1.cons(exports.VVar(k), vs), k + 1, full));
    if (tm.tag === 'Abs')
        return core_1.Abs(tm.erased, tm.mode, tm.name, exports.zonk(tm.type, vs, k, full), exports.zonk(tm.body, List_1.cons(exports.VVar(k), vs), k + 1, full));
    if (tm.tag === 'App') {
        const spine = zonkSpine(tm.fn, vs, k, full);
        return spine[0] ?
            core_1.App(spine[1], tm.mode, exports.zonk(tm.arg, vs, k, full)) :
            exports.quote(exports.vapp(spine[1], tm.mode, exports.evaluate(tm.arg, vs)), k, full);
    }
    if (tm.tag === 'Pair')
        return core_1.Pair(exports.zonk(tm.fst, vs, k, full), exports.zonk(tm.snd, vs, k, full), exports.zonk(tm.type, vs, k, full));
    if (tm.tag === 'Proj')
        return core_1.Proj(exports.zonk(tm.term, vs, k, full), tm.proj);
    return tm;
};
exports.zonk = zonk;

},{"./config":1,"./core":2,"./globals":4,"./metas":6,"./mode":7,"./utils/Lazy":14,"./utils/List":15,"./utils/utils":16}],18:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.verify = void 0;
const config_1 = require("./config");
const core_1 = require("./core");
const globals_1 = require("./globals");
const local_1 = require("./local");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const V = require("./values");
const unification_1 = require("./unification");
const mode_1 = require("./mode");
const prims_1 = require("./prims");
const metas_1 = require("./metas");
const showV = (local, v) => V.show(v, local.level);
const check = (local, tm, ty) => {
    config_1.log(() => `check ${core_1.show(tm)} : ${showV(local, ty)}${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
    const ty2 = synth(local, tm);
    return utils_1.tryT(() => {
        config_1.log(() => `unify ${showV(local, ty2)} ~ ${showV(local, ty)}`);
        unification_1.unify(local.level, ty2, ty);
        return;
    }, e => utils_1.terr(`check failed (${core_1.show(tm)}): ${showV(local, ty2)} ~ ${showV(local, ty)}: ${e}`));
};
const synth = (local, tm) => {
    config_1.log(() => `synth ${core_1.show(tm)}${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
    if (tm.tag === 'SymbolLit')
        return V.VSymbol;
    if (tm.tag === 'Meta' || tm.tag === 'InsertedMeta') {
        const sol = metas_1.getMeta(tm.id);
        return sol.type;
    }
    if (tm.tag === 'Var') {
        const [entry] = local_1.indexEnvT(local.ts, tm.index) || utils_1.terr(`var out of scope ${core_1.show(tm)}`);
        if (entry.erased && !local.erased)
            return utils_1.terr(`erased var used: ${core_1.show(tm)}`);
        return entry.type;
    }
    if (tm.tag === 'Prim') {
        if (prims_1.isPrimErased(tm.name) && !local.erased)
            return utils_1.terr(`erased prim used: ${core_1.show(tm)}`);
        return prims_1.primType(tm.name);
    }
    if (tm.tag === 'Global') {
        const e = globals_1.loadGlobal(tm.name);
        if (!e)
            return utils_1.terr(`undefined global ${core_1.show(tm)}`);
        if (e.erased && !local.erased)
            return utils_1.terr(`erased global used: ${core_1.show(tm)}`);
        return e.type;
    }
    if (tm.tag === 'App') {
        const fnty = synth(local, tm.fn);
        const rty = synthapp(local, fnty, tm.mode, tm.arg);
        return rty;
    }
    if (tm.tag === 'Abs') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const rty = synth(local.bind(tm.erased, tm.mode, tm.name, ty), tm.body);
        const qpi = core_1.Pi(tm.erased, tm.mode, tm.name, tm.type, values_1.quote(rty, local.level + 1));
        const pi = values_1.evaluate(qpi, local.vs);
        return pi;
    }
    if (tm.tag === 'Pair') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const fty = values_1.force(ty);
        if (fty.tag !== 'VSigma')
            return utils_1.terr(`not a sigma type in pair (${core_1.show(tm)}): ${showV(local, ty)}`);
        check(fty.erased ? local.inType() : local, tm.fst, fty.type);
        check(local, tm.snd, values_1.vinst(fty, values_1.evaluate(tm.fst, local.vs)));
        return ty;
    }
    if (tm.tag === 'Pi') {
        if (!local.erased)
            return utils_1.terr(`pi type in non-type context: ${core_1.show(tm)}`);
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        check(local.inType().bind(tm.erased, tm.mode, tm.name, ty), tm.body, values_1.VType);
        return values_1.VType;
    }
    if (tm.tag === 'Sigma') {
        if (!local.erased)
            return utils_1.terr(`sigma type in non-type context: ${core_1.show(tm)}`);
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        check(local.inType().bind(tm.erased, mode_1.Expl, tm.name, ty), tm.body, values_1.VType);
        return values_1.VType;
    }
    if (tm.tag === 'Let') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        check(tm.erased ? local.inType() : local, tm.val, ty);
        const v = values_1.evaluate(tm.val, local.vs);
        const rty = synth(local.define(tm.erased, tm.name, ty, v, tm.type, tm.val), tm.body);
        config_1.log(() => `let type: ${core_1.show(values_1.quote(rty, local.level))} in (${local.level}) ${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
        return rty;
    }
    if (tm.tag === 'Proj') {
        const sigma_ = synth(local, tm.term);
        if (tm.proj.tag === 'PProj') {
            const sigma = values_1.force(sigma_);
            if (sigma.tag !== 'VSigma')
                return utils_1.terr(`not a sigma type in ${core_1.show(tm)}: ${showV(local, sigma_)}`);
            if (sigma.erased && tm.proj.proj === 'fst' && !local.erased)
                return utils_1.terr(`cannot project erased ${core_1.show(tm)}: ${showV(local, sigma_)}`);
            const fst = sigma.name !== '_' ? core_1.PIndex(sigma.name, 0) : core_1.PFst; // TODO: is this nice?
            return tm.proj.proj === 'fst' ? sigma.type : values_1.vinst(sigma, V.vproj(values_1.evaluate(tm.term, local.vs), fst));
        }
        else
            return project(local, tm, values_1.evaluate(tm.term, local.vs), sigma_, tm.proj.index);
    }
    return tm;
};
const project = (local, full, tm, ty_, index) => {
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (ty.erased && index === 0 && !local.erased)
            return utils_1.terr(`cannot project erased sigma (${core_1.show(full)}): ${showV(local, ty_)}`);
        if (index === 0)
            return ty.type;
        const fst = ty.name !== '_' ? core_1.PIndex(ty.name, 0) : core_1.PFst; // TODO: is this nice?
        return project(local, full, V.vproj(tm, core_1.PSnd), values_1.vinst(ty, V.vproj(tm, fst)), index - 1);
    }
    return utils_1.terr(`failed to project, ${core_1.show(full)}: ${showV(local, ty_)}`);
};
const synthapp = (local, ty_, mode, arg) => {
    config_1.log(() => `synthapp ${showV(local, ty_)} @ ${mode.tag === 'Expl' ? '' : '{'}${core_1.show(arg)}${mode.tag === 'Expl' ? '' : '}'}${config_1.config.showEnvs ? ` in ${local.toString()}` : ''}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VPi' && mode_1.eqMode(ty.mode, mode)) {
        check(ty.erased ? local.inType() : local, arg, ty.type);
        const v = values_1.evaluate(arg, local.vs);
        return values_1.vinst(ty, v);
    }
    return utils_1.terr(`not a correct pi type or mode mismatch in synthapp: ${showV(local, ty)} @ ${mode.tag === 'Expl' ? '' : '{'}${core_1.show(arg)}${mode.tag === 'Expl' ? '' : '}'}`);
};
const verify = (t, local = local_1.Local.empty()) => {
    const vty = synth(local, t);
    const ty = values_1.quote(vty, local.level);
    return ty;
};
exports.verify = verify;

},{"./config":1,"./core":2,"./globals":4,"./local":5,"./metas":6,"./mode":7,"./prims":10,"./unification":13,"./utils/utils":16,"./values":17}],19:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const repl_1 = require("./repl");
var hist = [], index = -1;
var input = document.getElementById('input');
var content = document.getElementById('content');
function onresize() {
    content.style.height = window.innerHeight;
}
window.addEventListener('resize', onresize);
onresize();
addResult('tinka repl');
repl_1.initREPL(true);
input.focus();
input.onkeydown = function (keyEvent) {
    var val = input.value;
    var txt = (val || '').trim();
    if (keyEvent.keyCode === 13) {
        keyEvent.preventDefault();
        if (txt) {
            hist.push(val);
            index = hist.length;
            input.value = '';
            var div = document.createElement('div');
            div.innerHTML = val;
            div.className = 'line input';
            content.insertBefore(div, input);
            repl_1.runREPL(txt, addResult);
        }
    }
    else if (keyEvent.keyCode === 38 && index > 0) {
        keyEvent.preventDefault();
        input.value = hist[--index];
    }
    else if (keyEvent.keyCode === 40 && index < hist.length - 1) {
        keyEvent.preventDefault();
        input.value = hist[++index];
    }
    else if (keyEvent.keyCode === 40 && keyEvent.ctrlKey && index >= hist.length - 1) {
        index = hist.length;
        input.value = '';
    }
};
function addResult(msg, err) {
    var divout = document.createElement('pre');
    divout.className = 'line output';
    if (err)
        divout.className += ' error';
    divout.innerHTML = '' + msg;
    content.insertBefore(divout, input);
    input.focus();
    content.scrollTop = content.scrollHeight;
    return divout;
}

},{"./repl":11}],20:[function(require,module,exports){

},{}]},{},[19]);
