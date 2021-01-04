(function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.log = exports.setConfig = exports.config = void 0;
exports.config = {
    debug: false,
    showEnvs: false,
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
exports.conv = exports.eqHead = void 0;
const config_1 = require("./config");
const mode_1 = require("./mode");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const eqHead = (a, b) => {
    if (a === b)
        return true;
    if (a.tag === 'HVar')
        return b.tag === 'HVar' && a.level === b.level;
    return a.tag;
};
exports.eqHead = eqHead;
const convElim = (k, a, b, x, y) => {
    if (a === b)
        return;
    if (a.tag === 'EApp' && b.tag === 'EApp' && mode_1.eqMode(a.mode, b.mode))
        return exports.conv(k, a.arg, b.arg);
    if (a.tag === 'EIndSigma' && b.tag === 'EIndSigma' && a.usage === b.usage) {
        exports.conv(k, a.motive, b.motive);
        return exports.conv(k, a.cas, b.cas);
    }
    if (a.tag === 'EProj' && b.tag === 'EProj' && a.proj === b.proj)
        return;
    return utils_1.terr(`conv failed (${k}): ${values_1.show(x, k)} ~ ${values_1.show(y, k)}`);
};
const conv = (k, a, b) => {
    config_1.log(() => `conv(${k}): ${values_1.show(a, k)} ~ ${values_1.show(b, k)}`);
    if (a === b)
        return;
    if (a.tag === 'VPi' && b.tag === 'VPi' && a.usage === b.usage && mode_1.eqMode(a.mode, b.mode)) {
        exports.conv(k, a.type, b.type);
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.usage === b.usage) {
        exports.conv(k, a.type, b.type);
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VAbs' && b.tag === 'VAbs') {
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VPair' && b.tag === 'VPair') {
        exports.conv(k, a.fst, b.fst);
        return exports.conv(k, a.snd, b.snd);
    }
    if (a.tag === 'VAbs') {
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vinst(a, v), values_1.vapp(b, a.mode, v));
    }
    if (b.tag === 'VAbs') {
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vapp(a, b.mode, v), values_1.vinst(b, v));
    }
    // TODO: is this correct for linear/erased sigmas?
    if (a.tag === 'VPair') {
        exports.conv(k, a.fst, values_1.vproj(b, 'fst'));
        exports.conv(k, a.snd, values_1.vproj(b, 'snd'));
        return;
    }
    if (b.tag === 'VPair') {
        exports.conv(k, values_1.vproj(a, 'fst'), b.fst);
        exports.conv(k, values_1.vproj(a, 'snd'), b.snd);
        return;
    }
    if (a.tag === 'VNe' && b.tag === 'VNe' && exports.eqHead(a.head, b.head))
        return a.spine.zipWithR_(b.spine, (x, y) => convElim(k, x, y, a, b));
    if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && a.head === b.head) {
        return utils_1.tryT(() => a.spine.zipWithR_(b.spine, (x, y) => convElim(k, x, y, a, b)), () => exports.conv(k, a.val.get(), b.val.get()));
    }
    if (a.tag === 'VGlobal')
        return exports.conv(k, a.val.get(), b);
    if (b.tag === 'VGlobal')
        return exports.conv(k, a, b.val.get());
    return utils_1.terr(`conv failed (${k}): ${values_1.show(a, k)} ~ ${values_1.show(b, k)}`);
};
exports.conv = conv;

},{"./config":1,"./mode":7,"./utils/utils":16,"./values":17}],3:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.show = exports.showProjType = exports.flattenProj = exports.flattenPair = exports.flattenSigma = exports.flattenApp = exports.flattenAbs = exports.flattenPi = exports.PSnd = exports.PFst = exports.PProj = exports.Proj = exports.IndSigma = exports.Pair = exports.Sigma = exports.App = exports.Abs = exports.Pi = exports.Type = exports.Let = exports.Global = exports.Var = void 0;
const usage_1 = require("./usage");
const Var = (index) => ({ tag: 'Var', index });
exports.Var = Var;
const Global = (name) => ({ tag: 'Global', name });
exports.Global = Global;
const Let = (usage, name, type, val, body) => ({ tag: 'Let', usage, name, type, val, body });
exports.Let = Let;
exports.Type = { tag: 'Type' };
const Pi = (usage, mode, name, type, body) => ({ tag: 'Pi', usage, mode, name, type, body });
exports.Pi = Pi;
const Abs = (usage, mode, name, type, body) => ({ tag: 'Abs', usage, mode, name, type, body });
exports.Abs = Abs;
const App = (fn, mode, arg) => ({ tag: 'App', fn, mode, arg });
exports.App = App;
const Sigma = (usage, name, type, body) => ({ tag: 'Sigma', usage, name, type, body });
exports.Sigma = Sigma;
const Pair = (fst, snd, type) => ({ tag: 'Pair', fst, snd, type });
exports.Pair = Pair;
const IndSigma = (usage, motive, scrut, cas) => ({ tag: 'IndSigma', usage, motive, scrut, cas });
exports.IndSigma = IndSigma;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const PProj = (proj) => ({ tag: 'PProj', proj });
exports.PProj = PProj;
exports.PFst = exports.PProj('fst');
exports.PSnd = exports.PProj('snd');
const flattenPi = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Pi') {
        params.push([c.usage, c.mode, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenPi = flattenPi;
const flattenAbs = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Abs') {
        params.push([c.usage, c.mode, c.name, c.type]);
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
const flattenSigma = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Sigma') {
        params.push([c.usage, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenSigma = flattenSigma;
const flattenPair = (t) => {
    const r = [];
    while (t.tag === 'Pair') {
        r.push(t.fst);
        t = t.snd;
    }
    r.push(t);
    return r;
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
const isSimple = (t) => t.tag === 'Type' || t.tag === 'Var' || t.tag === 'Global';
const showS = (t) => showP(!isSimple(t), t);
const showProjType = (p) => {
    if (p.tag === 'PProj')
        return p.proj === 'fst' ? '_1' : '_2';
    return p.tag;
};
exports.showProjType = showProjType;
const show = (t) => {
    if (t.tag === 'Type')
        return 'Type';
    if (t.tag === 'Var')
        return `${t.index}`;
    if (t.tag === 'Global')
        return `${t.name}`;
    if (t.tag === 'Pi') {
        const [params, ret] = exports.flattenPi(t);
        return `${params.map(([u, m, x, t]) => u === usage_1.many && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' -> ')} -> ${exports.show(ret)}`;
    }
    if (t.tag === 'Abs') {
        const [params, body] = exports.flattenAbs(t);
        return `\\${params.map(([u, m, x, t]) => `${m.tag === 'Expl' ? '(' : '{'}${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' ')}. ${exports.show(body)}`;
    }
    if (t.tag === 'App') {
        const [fn, args] = exports.flattenApp(t);
        return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${exports.show(a)}}`).join(' ')}`;
    }
    if (t.tag === 'Let')
        return `let ${t.usage === usage_1.many ? '' : `${t.usage} `}${t.name} : ${showP(t.type.tag === 'Let', t.type)} = ${showP(t.val.tag === 'Let', t.val)}; ${exports.show(t.body)}`;
    if (t.tag === 'Sigma') {
        const [params, ret] = exports.flattenSigma(t);
        return `${params.map(([u, x, t]) => u === usage_1.many && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `(${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(t)})`).join(' ** ')} ** ${exports.show(ret)}`;
    }
    if (t.tag === 'Pair') {
        const ps = exports.flattenPair(t);
        return `(${ps.map(t => exports.show(t)).join(', ')} : ${exports.show(t.type)})`;
    }
    if (t.tag === 'IndSigma')
        return `indSigma ${t.usage === usage_1.many ? '' : `${t.usage} `}${showS(t.motive)} ${showS(t.scrut)} ${showS(t.cas)}`;
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(exports.showProjType).join('.')}`;
    }
    return t;
};
exports.show = show;

},{"./usage":13}],4:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.elaborate = void 0;
const config_1 = require("./config");
const core_1 = require("./core");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const surface_1 = require("./surface");
const conversion_1 = require("./conversion");
const usage_1 = require("./usage");
const local_1 = require("./local");
const mode_1 = require("./mode");
const globals_1 = require("./globals");
const check = (local, tm, ty_) => {
    config_1.log(() => `check (${local.level}) ${surface_1.show(tm)} : ${local_1.showVal(local, ty_)}`);
    const ty = values_1.force(ty_);
    if (tm.tag === 'Type' && ty.tag === 'VType')
        return [core_1.Type, usage_1.noUses(local.level)];
    if (tm.tag === 'Abs' && !tm.type && ty.tag === 'VPi' && mode_1.eqMode(tm.mode, ty.mode)) {
        const v = values_1.VVar(local.level);
        const x = tm.name;
        const [body, u] = check(local.bind(ty.usage, ty.mode, x, ty.type), tm.body, values_1.vinst(ty, v));
        const [ux, urest] = u.uncons();
        if (!usage_1.sub(ux, ty.usage))
            return utils_1.terr(`usage error in ${surface_1.show(tm)}: expected ${ty.usage} for ${x} but actual ${ux}`);
        return [core_1.Abs(ty.usage, ty.mode, x, values_1.quote(ty.type, local.level), body), urest];
    }
    /*
    if (ty.tag === 'VPi' && ty.mode.tag === 'Impl' && !(tm.tag === 'Abs' && tm.mode.tag === 'Impl')) {
      const v = VVar(local.level);
      const x = ty.name;
      const [term, u] = check(local.insert(ty.usage, ty.mode, x, ty.type), tm, vinst(ty, v));
      const [ux, urest] = u.uncons();
      if (!sub(ux, ty.usage))
        return terr(`usage error in ${show(tm)}: expected ${ty.usage} for ${x} but actual ${ux}`);
      return [Abs(ty.usage, ty.mode, x, quote(ty.type, local.level), term), urest];
    }
    */
    if (tm.tag === 'Pair' && ty.tag === 'VSigma') {
        const [fst, u1] = check(local, tm.fst, ty.type);
        const [snd, u2] = check(local, tm.snd, values_1.vinst(ty, values_1.evaluate(fst, local.vs)));
        return [core_1.Pair(fst, snd, values_1.quote(ty, local.level)), usage_1.addUses(usage_1.multiplyUses(ty.usage, u1), u2)];
    }
    if (tm.tag === 'Let') {
        let vtype;
        let vty;
        let val;
        let uv;
        if (tm.type) {
            [vtype] = check(local.inType(), tm.type, values_1.VType);
            vty = values_1.evaluate(vtype, local.vs);
            [val, uv] = check(local, tm.val, ty);
        }
        else {
            [val, vty, uv] = synth(local, tm.val);
            vtype = values_1.quote(vty, local.level);
        }
        const v = values_1.evaluate(val, local.vs);
        const [body, ub] = check(local.define(tm.usage, tm.name, vty, v), tm.body, ty_);
        const [ux, urest] = ub.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${surface_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [core_1.Let(tm.usage, tm.name, vtype, val, body), usage_1.addUses(usage_1.multiplyUses(ux, uv), urest)];
    }
    const [Core, ty2, uses] = synth(local, tm);
    return utils_1.tryT(() => {
        config_1.log(() => `unify ${local_1.showVal(local, ty2)} ~ ${local_1.showVal(local, ty_)}`);
        conversion_1.conv(local.level, ty2, ty_);
        return [Core, uses];
    }, e => utils_1.terr(`check failed (${surface_1.show(tm)}): ${local_1.showVal(local, ty2)} ~ ${local_1.showVal(local, ty_)}: ${e}`));
};
const synth = (local, tm) => {
    config_1.log(() => `synth (${local.level}) ${surface_1.show(tm)}`);
    if (tm.tag === 'Type')
        return [core_1.Type, values_1.VType, usage_1.noUses(local.level)];
    if (tm.tag === 'Var') {
        const i = local.nsSurface.indexOf(tm.name);
        if (i < 0) {
            const e = globals_1.globalLoad(tm.name);
            if (!e)
                return utils_1.terr(`undefined variable or failed to load global ${tm.name}`);
            return [core_1.Global(tm.name), e.type, usage_1.noUses(local.level)];
        }
        else {
            const [entry, j] = local_1.indexEnvT(local.ts, i) || utils_1.terr(`var out of scope ${surface_1.show(tm)}`);
            const uses = usage_1.noUses(local.level).updateAt(j, _ => local.usage);
            return [core_1.Var(j), entry.type, uses];
        }
    }
    if (tm.tag === 'App') {
        const [fntm, fnty, fnu] = synth(local, tm.fn);
        const [argtm, rty, fnarg] = synthapp(local, fnty, tm.mode, tm.arg);
        return [core_1.App(fntm, tm.mode, argtm), rty, usage_1.addUses(fnu, fnarg)];
    }
    if (tm.tag === 'Abs') {
        if (tm.type) {
            const [type] = check(local.inType(), tm.type, values_1.VType);
            const ty = values_1.evaluate(type, local.vs);
            const [body, rty, u] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
            const pi = values_1.evaluate(core_1.Pi(tm.usage, tm.mode, tm.name, type, values_1.quote(rty, local.level + 1)), local.vs);
            const [ux, urest] = u.uncons();
            if (!usage_1.sub(ux, tm.usage))
                return utils_1.terr(`usage error in ${surface_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
            return [core_1.Abs(tm.usage, tm.mode, tm.name, type, body), pi, urest];
        }
        else
            utils_1.terr(`cannot synth unannotated lambda: ${surface_1.show(tm)}`);
    }
    if (tm.tag === 'Pi') {
        const [type, u1] = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(type, local.vs);
        const [body, u2] = check(local.bind(usage_1.many, tm.mode, tm.name, ty), tm.body, values_1.VType);
        const [, urest] = u2.uncons();
        return [core_1.Pi(tm.usage, tm.mode, tm.name, type, body), values_1.VType, usage_1.addUses(u1, urest)];
    }
    if (tm.tag === 'Let') {
        let type;
        let ty;
        let val;
        let uv;
        if (tm.type) {
            [type] = check(local.inType(), tm.type, values_1.VType);
            ty = values_1.evaluate(type, local.vs);
            [val, uv] = check(local, tm.val, ty);
        }
        else {
            [val, ty, uv] = synth(local, tm.val);
            type = values_1.quote(ty, local.level);
        }
        const v = values_1.evaluate(val, local.vs);
        const [body, rty, ub] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
        const [ux, urest] = ub.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${surface_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [core_1.Let(tm.usage, tm.name, type, val, body), rty, usage_1.addUses(usage_1.multiplyUses(ux, uv), urest)];
    }
    if (tm.tag === 'Sigma') {
        const [type, u1] = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(type, local.vs);
        const [body, u2] = check(local.bind(usage_1.many, mode_1.Expl, tm.name, ty), tm.body, values_1.VType);
        const [, urest] = u2.uncons();
        return [core_1.Sigma(tm.usage, tm.name, type, body), values_1.VType, usage_1.addUses(u1, urest)];
    }
    if (tm.tag === 'Pair') {
        const [fst, ty1, u1] = synth(local, tm.fst);
        const [snd, ty2, u2] = synth(local, tm.snd);
        const ty = values_1.VSigma(usage_1.many, '_', ty1, _ => ty2);
        return [core_1.Pair(fst, snd, values_1.quote(ty, local.level)), ty, usage_1.addUses(usage_1.multiplyUses(ty.usage, u1), u2)];
    }
    if (tm.tag === 'IndSigma' && tm.motive) {
        if (!usage_1.sub(usage_1.one, tm.usage))
            return utils_1.terr(`usage must be 1 <= q in sigma induction ${surface_1.show(tm)}: ${tm.usage}`);
        const [scrut, sigma_, u1] = synth(local, tm.scrut);
        const sigma = values_1.force(sigma_);
        if (sigma.tag !== 'VSigma')
            return utils_1.terr(`not a sigma type in ${surface_1.show(tm)}: ${local_1.showVal(local, sigma_)}`);
        const [motive] = check(local.inType(), tm.motive, values_1.VPi(usage_1.many, mode_1.Expl, '_', sigma_, _ => values_1.VType));
        const vmotive = values_1.evaluate(motive, local.vs);
        const [cas, u2] = check(local, tm.cas, values_1.VPi(usage_1.multiply(tm.usage, sigma.usage), mode_1.Expl, 'x', sigma.type, x => values_1.VPi(tm.usage, mode_1.Expl, 'y', values_1.vinst(sigma, x), y => values_1.vapp(vmotive, mode_1.Expl, values_1.VPair(x, y, sigma_)))));
        return [core_1.IndSigma(tm.usage, motive, scrut, cas), values_1.vapp(vmotive, mode_1.Expl, values_1.evaluate(scrut, local.vs)), usage_1.multiplyUses(tm.usage, usage_1.addUses(u1, u2))];
    }
    if (tm.tag === 'Proj') {
        const [term, sigma_, u1] = synth(local, tm.term);
        const sigma = values_1.force(sigma_);
        if (sigma.tag !== 'VSigma')
            return utils_1.terr(`not a sigma type in ${surface_1.show(tm)}: ${local_1.showVal(local, sigma_)}`);
        if (local.usage === '1' && (sigma.usage === '1' || (sigma.usage === '0' && tm.proj.proj === 'fst')))
            return utils_1.terr(`cannot project ${surface_1.show(tm)}, usage must be *: ${local_1.showVal(local, sigma_)}`);
        return [core_1.Proj(term, tm.proj), tm.proj.proj === 'fst' ? sigma.type : values_1.vinst(sigma, values_1.vproj(values_1.evaluate(term, local.vs), 'fst')), u1];
    }
    return utils_1.terr(`unable to synth ${surface_1.show(tm)}`);
};
const synthapp = (local, ty_, mode, arg) => {
    config_1.log(() => `synthapp (${local.level}) ${local_1.showVal(local, ty_)} @ ${surface_1.show(arg)}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VPi' && mode_1.eqMode(ty.mode, mode)) {
        const cty = ty.type;
        const [Core, uses] = check(local, arg, cty);
        const v = values_1.evaluate(Core, local.vs);
        return [Core, values_1.vinst(ty, v), usage_1.multiplyUses(ty.usage, uses)];
    }
    return utils_1.terr(`not a correct pi type in synthapp: ${local_1.showVal(local, ty)} @ ${surface_1.show(arg)}`);
};
const elaborate = (t, local = local_1.Local.empty()) => {
    const [tm, vty] = synth(local, t);
    const ty = values_1.quote(vty, 0);
    return [tm, ty];
};
exports.elaborate = elaborate;

},{"./config":1,"./conversion":2,"./core":3,"./globals":5,"./local":6,"./mode":7,"./surface":11,"./usage":13,"./utils/utils":16,"./values":17}],5:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.globalLoad = exports.globalSet = exports.globalGet = exports.globalReset = void 0;
const elaboration_1 = require("./elaboration");
const parser_1 = require("./parser");
const typecheck_1 = require("./typecheck");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
let globals = {};
const globalReset = () => {
    globals = {};
};
exports.globalReset = globalReset;
const globalGet = (x) => globals[x] || null;
exports.globalGet = globalGet;
const globalSet = (x, val, type) => {
    globals[x] = { val, type };
};
exports.globalSet = globalSet;
const globalLoad = (x) => {
    if (globals[x])
        return globals[x];
    const sc = utils_1.loadFileSync(`lib/${x}`);
    if (sc instanceof Error)
        return null;
    const e = parser_1.parse(sc);
    const [tm, ty] = elaboration_1.elaborate(e);
    typecheck_1.typecheck(tm);
    exports.globalSet(x, values_1.evaluate(tm, List_1.nil), values_1.evaluate(ty, List_1.nil));
    return exports.globalGet(x);
};
exports.globalLoad = globalLoad;

},{"./elaboration":4,"./parser":9,"./typecheck":12,"./utils/List":15,"./utils/utils":16,"./values":17}],6:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.showVal = exports.showValCore = exports.Local = exports.indexEnvT = exports.EntryT = void 0;
const mode_1 = require("./mode");
const List_1 = require("./utils/List");
const values_1 = require("./values");
const S = require("./surface");
const EntryT = (type, usage, mode, bound, inserted) => ({ type, bound, mode, usage, inserted });
exports.EntryT = EntryT;
const indexEnvT = (ts, ix) => {
    let l = ts;
    let i = 0;
    while (l.isCons()) {
        if (l.head.inserted) {
            l = l.tail;
            i++;
            continue;
        }
        if (ix === 0)
            return [l.head, i];
        i++;
        ix--;
        l = l.tail;
    }
    return null;
};
exports.indexEnvT = indexEnvT;
class Local {
    constructor(usage, level, ns, nsSurface, ts, vs) {
        this.usage = usage;
        this.level = level;
        this.ns = ns;
        this.nsSurface = nsSurface;
        this.ts = ts;
        this.vs = vs;
    }
    static empty() {
        if (Local._empty === undefined)
            Local._empty = new Local('1', 0, List_1.nil, List_1.nil, List_1.nil, List_1.nil);
        return Local._empty;
    }
    bind(usage, mode, name, ty) {
        return new Local(this.usage, this.level + 1, List_1.cons(name, this.ns), List_1.cons(name, this.nsSurface), List_1.cons(exports.EntryT(ty, usage, mode, true, false), this.ts), List_1.cons(values_1.VVar(this.level), this.vs));
    }
    insert(usage, mode, name, ty) {
        return new Local(this.usage, this.level + 1, List_1.cons(name, this.ns), this.nsSurface, List_1.cons(exports.EntryT(ty, usage, mode, true, true), this.ts), List_1.cons(values_1.VVar(this.level), this.vs));
    }
    define(usage, name, ty, val) {
        return new Local(this.usage, this.level + 1, List_1.cons(name, this.ns), List_1.cons(name, this.nsSurface), List_1.cons(exports.EntryT(ty, usage, mode_1.Expl, false, false), this.ts), List_1.cons(val, this.vs));
    }
    unsafeUndo() {
        return new Local(this.usage, this.level - 1, this.ns.tail, this.nsSurface.tail, this.ts.tail, this.vs.tail);
    }
    inType() {
        return new Local('0', this.level, this.ns, this.nsSurface, this.ts, this.vs);
    }
}
exports.Local = Local;
const showValCore = (local, val) => values_1.show(val, local.level);
exports.showValCore = showValCore;
const showVal = (local, val) => S.showVal(val, local.level, local.ns);
exports.showVal = showVal;

},{"./mode":7,"./surface":11,"./utils/List":15,"./values":17}],7:[function(require,module,exports){
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
const core_1 = require("./core");
const mode_1 = require("./mode");
const surface_1 = require("./surface");
const usage_1 = require("./usage");
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
    return utils_1.serr(`invalid bracket: ${c}`);
};
const TName = (name) => ({ tag: 'Name', name });
const TNum = (num) => ({ tag: 'Num', num });
const TList = (list, bracket) => ({ tag: 'List', list, bracket });
const TStr = (str) => ({ tag: 'Str', str });
const SYM1 = ['\\', ':', '=', ';', '*', ','];
const SYM2 = ['->', '**'];
const START = 0;
const NAME = 1;
const COMMENT = 2;
const NUMBER = 3;
const STRING = 4;
const tokenize = (sc) => {
    let state = START;
    let r = [];
    let t = '';
    let esc = false;
    let p = [], b = [];
    for (let i = 0, l = sc.length; i <= l; i++) {
        const c = sc[i] || ' ';
        const next = sc[i + 1] || '';
        if (state === START) {
            if (SYM2.indexOf(c + next) >= 0)
                r.push(TName(c + next)), i++;
            else if (SYM1.indexOf(c) >= 0)
                r.push(TName(c));
            else if (c === '"')
                state = STRING;
            else if (c === '.' && !/[\.\%\_a-z]/i.test(next))
                r.push(TName('.'));
            else if (c + next === '--')
                i++, state = COMMENT;
            else if (/[\-\.\?\@\#\%\_a-z]/i.test(c))
                t += c, state = NAME;
            else if (/[0-9]/.test(c))
                t += c, state = NUMBER;
            else if (c === '(' || c === '{')
                b.push(c), p.push(r), r = [];
            else if (c === ')' || c === '}') {
                if (b.length === 0)
                    return utils_1.serr(`unmatched bracket: ${c}`);
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
            if (!(/[a-z0-9\-\_\/]/i.test(c) || (c === '.' && /[a-z0-9\_]/i.test(next)))) {
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
    }
    if (b.length > 0)
        return utils_1.serr(`unclosed brackets: ${b.join(' ')}`);
    if (state !== START && state !== COMMENT)
        return utils_1.serr('invalid tokenize end state');
    if (esc)
        return utils_1.serr(`escape is true after tokenize`);
    return r;
};
const isName = (t, x) => t.tag === 'Name' && t.name === x;
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
const usage = (t) => {
    if (t.tag === 'Name' && usage_1.usages.includes(t.name))
        return t.name;
    if (t.tag === 'Num' && usage_1.usages.includes(t.num))
        return t.num;
    return null;
};
const lambdaParams = (t, fromRepl) => {
    if (t.tag === 'Name')
        return [[usage_1.many, t.name, mode_1.Expl, null]];
    if (t.tag === 'List') {
        const impl = t.bracket === '{' ? mode_1.Impl : mode_1.Expl;
        const a = t.list;
        if (a.length === 0)
            return [[usage_1.many, '_', impl, surface_1.Var('UnitType')]];
        const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
        if (i === -1)
            return isNames(a).map(x => [usage_1.many, x, impl, null]);
        let start = 0;
        const n = a[0];
        const pu = usage(n);
        let u = usage_1.many;
        if (pu !== null) {
            u = pu;
            start = 1;
        }
        const ns = a.slice(start, i);
        const rest = a.slice(i + 1);
        const ty = exprs(rest, '(', fromRepl);
        return isNames(ns).map(x => [u, x, impl, ty]);
    }
    return utils_1.serr(`invalid lambda param`);
};
const piParams = (t, fromRepl) => {
    if (t.tag === 'Name')
        return [[usage_1.many, '_', mode_1.Expl, expr(t, fromRepl)[0]]];
    if (t.tag === 'List') {
        const impl = t.bracket === '{' ? mode_1.Impl : mode_1.Expl;
        const a = t.list;
        if (a.length === 0)
            return [[usage_1.many, '_', impl, surface_1.Var('UnitType')]];
        const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
        if (i === -1)
            return [[usage_1.many, '_', impl, expr(t, fromRepl)[0]]];
        let start = 0;
        const n = a[0];
        const pu = usage(n);
        let u = usage_1.many;
        if (pu !== null) {
            u = pu;
            start = 1;
        }
        const ns = a.slice(start, i);
        const rest = a.slice(i + 1);
        const ty = exprs(rest, '(', fromRepl);
        return isNames(ns).map(x => [u, x, impl, ty]);
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
        return core_1.PFst;
    if (p === '_2')
        return core_1.PSnd;
    return utils_1.serr(`invalid projection: ${p}`);
};
const expr = (t, fromRepl) => {
    if (t.tag === 'List')
        return [exprs(t.list, '(', fromRepl), t.bracket === '{'];
    if (t.tag === 'Str') {
        const s = codepoints(t.str).reverse();
        const Cons = surface_1.Var('Cons');
        const Nil = surface_1.Var('Nil');
        return [s.reduce((t, n) => surface_1.App(surface_1.App(Cons, mode_1.Expl, numToNat(n, `codepoint: ${n}`)), mode_1.Expl, t), Nil), false];
    }
    if (t.tag === 'Name') {
        const x = t.name;
        if (x === 'Type')
            return [surface_1.Type, false];
        if (x === '*')
            return [surface_1.Var('Unit'), false];
        if (/[a-z]/i.test(x[0])) {
            const parts = x.split('.');
            return [parts.slice(1).reduce((t, p) => surface_1.Proj(t, proj(p)), surface_1.Var(parts[0])), false];
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
const exprs = (ts, br, fromRepl) => {
    if (br === '{')
        return utils_1.serr(`{} cannot be used here`);
    if (ts.length === 0)
        return surface_1.Var('UnitType');
    if (ts.length === 1)
        return expr(ts[0], fromRepl)[0];
    if (isName(ts[0], 'let')) {
        let x = ts[1];
        let j = 2;
        const pu = usage(x);
        let u = usage_1.many;
        if (pu !== null) {
            u = pu;
            x = ts[2];
            j = 3;
        }
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
            ty = exprs(tyts, '(', fromRepl);
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
        const val = exprs(vals, '(', fromRepl);
        if (!found) {
            if (!fromRepl)
                return utils_1.serr(`no ; after let`);
            return surface_1.Let(u, name, ty || null, val, null);
        }
        const body = exprs(ts.slice(i + 1), '(', fromRepl);
        return surface_1.Let(u, name, ty || null, val, body);
    }
    const i = ts.findIndex(x => isName(x, ':'));
    if (i >= 0) {
        const a = ts.slice(0, i);
        const b = ts.slice(i + 1);
        return surface_1.Let(usage_1.many, 'x', exprs(b, '(', fromRepl), exprs(a, '(', fromRepl), surface_1.Var('x'));
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
            lambdaParams(c, fromRepl).forEach(x => args.push(x));
        }
        if (!found)
            return utils_1.serr(`. not found after \\ or there was no whitespace after .`);
        const body = exprs(ts.slice(i + 1), '(', fromRepl);
        return args.reduceRight((x, [u, name, mode, ty]) => surface_1.Abs(u, mode, name, ty, x), body);
    }
    if (isName(ts[0], 'indSigma')) {
        let j = 1;
        let u = usage(ts[1]);
        if (u) {
            j = 2;
        }
        else {
            u = usage_1.many;
        }
        let motive = null;
        let scrut;
        const [maybemotive, impl] = expr(ts[j], fromRepl);
        if (impl) {
            motive = maybemotive;
            const [scrut2, impl2] = expr(ts[j + 1], fromRepl);
            if (impl2)
                return utils_1.serr(`indSigma scrutinee cannot be implicit`);
            scrut = scrut2;
            j++;
        }
        else {
            scrut = maybemotive;
        }
        const cas = exprs(ts.slice(j + 1), '(', fromRepl);
        return surface_1.IndSigma(u, motive, scrut, cas);
    }
    const j = ts.findIndex(x => isName(x, '->'));
    if (j >= 0) {
        const s = splitTokens(ts, x => isName(x, '->'));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with ->`);
        const args = s.slice(0, -1)
            .map(p => p.length === 1 ? piParams(p[0], fromRepl) : [[usage_1.many, '_', mode_1.Expl, exprs(p, '(', fromRepl)]])
            .reduce((x, y) => x.concat(y), []);
        const body = exprs(s[s.length - 1], '(', fromRepl);
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
                    return expr(h, fromRepl);
            }
            return [exprs(x, '(', fromRepl), false];
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
            .map(p => p.length === 1 ? piParams(p[0], fromRepl) : [[usage_1.many, '_', mode_1.Expl, exprs(p, '(', fromRepl)]])
            .reduce((x, y) => x.concat(y), []);
        const body = exprs(s[s.length - 1], '(', fromRepl);
        return args.reduceRight((x, [u, name, mode, ty]) => {
            if (mode.tag !== 'Expl')
                return utils_1.serr(`sigma cannot be implicit`);
            return surface_1.Sigma(u, name, ty, x);
        }, body);
    }
    const l = ts.findIndex(x => isName(x, '\\'));
    let all = [];
    if (l >= 0) {
        const first = ts.slice(0, l).map(t => expr(t, fromRepl));
        const rest = exprs(ts.slice(l), '(', fromRepl);
        all = first.concat([[rest, false]]);
    }
    else {
        all = ts.map(t => expr(t, fromRepl));
    }
    if (all.length === 0)
        return utils_1.serr(`empty application`);
    if (all[0] && all[0][1])
        return utils_1.serr(`in application function cannot be between {}`);
    return all.slice(1).reduce((x, [y, impl]) => surface_1.App(x, impl ? mode_1.Impl : mode_1.Expl, y), all[0][0]);
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

},{"./config":1,"./core":3,"./mode":7,"./surface":11,"./usage":13,"./utils/utils":16}],10:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.runREPL = exports.initREPL = void 0;
const config_1 = require("./config");
const parser_1 = require("./parser");
const surface_1 = require("./surface");
const usage_1 = require("./usage");
const local_1 = require("./local");
const elaboration_1 = require("./elaboration");
const C = require("./core");
const typecheck_1 = require("./typecheck");
const values_1 = require("./values");
const utils_1 = require("./utils/utils");
const globals_1 = require("./globals");
const List_1 = require("./utils/List");
const help = `
COMMANDS
[:help or :h] this help message
[:debug or :d] toggle debug log messages
[:showStackTrace] show stack trace of error
[:type or :t] do not normalize
[:defs] show definitions
[:clear] clear definitions
[:undoDef] undo last def
[:load name] load a global
`.trim();
let showStackTrace = false;
let defs = [];
let local = local_1.Local.empty();
const initREPL = () => {
    showStackTrace = false;
    defs = [];
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
        if (s === ':showStackTrace') {
            showStackTrace = !showStackTrace;
            return cb(`showStackTrace: ${showStackTrace}`);
        }
        if (s === ':defs')
            return cb(defs.map(([u, x, t, v]) => `let ${u === '*' ? '' : `${u} `}${x}${t ? ` : ${surface_1.show(t)}` : ''} = ${surface_1.show(v)}`).join('\n'));
        if (s === ':clear') {
            defs = [];
            local = local_1.Local.empty();
            return cb(`cleared definitions`);
        }
        if (s === ':undoDef') {
            if (defs.length > 0) {
                const [u, x, t, v] = defs.pop();
                local = local.unsafeUndo();
                return cb(`undid let ${u === '*' ? '' : `${u} `}${x}${t ? ` : ${surface_1.show(t)}` : ''} = ${surface_1.show(v)}`);
            }
            cb(`no def to undo`);
        }
        if (s.startsWith(':load')) {
            const name = `lib/${s.slice(5).trim()}`;
            utils_1.loadFile(name)
                .then(sc => {
                const e = parser_1.parse(sc);
                const [tm, ty] = elaboration_1.elaborate(e);
                typecheck_1.typecheck(tm);
                globals_1.globalSet(name, values_1.evaluate(tm, List_1.nil), values_1.evaluate(ty, List_1.nil));
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
        let usage = usage_1.many;
        if (term.tag === 'Let' && term.body === null) {
            isDef = true;
            usage = term.usage;
            term = surface_1.Let(term.usage === usage_1.zero ? usage_1.many : term.usage, term.name, term.type, term.val, surface_1.Var(term.name));
        }
        config_1.log(() => surface_1.show(term));
        config_1.log(() => 'ELABORATE');
        const [eterm, etype] = elaboration_1.elaborate(term, local);
        config_1.log(() => C.show(eterm));
        config_1.log(() => surface_1.showCore(eterm));
        config_1.log(() => C.show(etype));
        config_1.log(() => surface_1.showCore(etype));
        config_1.log(() => 'VERIFICATION');
        typecheck_1.typecheck(eterm, local);
        let normstr = '';
        if (!typeOnly) {
            config_1.log(() => 'NORMALIZE');
            const norm = values_1.normalize(eterm, local.vs, true);
            config_1.log(() => C.show(norm));
            config_1.log(() => surface_1.showCore(norm));
            normstr = `\nnorm: ${surface_1.showCore(norm)}`;
        }
        const etermstr = surface_1.showCore(eterm, local.ns);
        if (isDef && term.tag === 'Let') {
            defs.push([usage, term.name, term.type, term.val]);
            const value = values_1.evaluate(eterm, local.vs);
            local = local.define(usage, term.name, values_1.evaluate(etype, local.vs), value);
        }
        return cb(`term: ${surface_1.show(term)}\ntype: ${surface_1.showCore(etype)}\netrm: ${etermstr}${normstr}`);
    }
    catch (err) {
        if (showStackTrace)
            console.error(err);
        return cb(`${err}`, true);
    }
};
exports.runREPL = runREPL;

},{"./config":1,"./core":3,"./elaboration":4,"./globals":5,"./local":6,"./parser":9,"./surface":11,"./typecheck":12,"./usage":13,"./utils/List":15,"./utils/utils":16,"./values":17}],11:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.showVal = exports.showCore = exports.fromCore = exports.show = exports.flattenProj = exports.flattenPair = exports.flattenSigma = exports.flattenApp = exports.flattenAbs = exports.flattenPi = exports.Proj = exports.IndSigma = exports.Pair = exports.Sigma = exports.App = exports.Abs = exports.Pi = exports.Type = exports.Let = exports.Var = void 0;
const core_1 = require("./core");
const names_1 = require("./names");
const usage_1 = require("./usage");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const Var = (name) => ({ tag: 'Var', name });
exports.Var = Var;
const Let = (usage, name, type, val, body) => ({ tag: 'Let', usage, name, type, val, body });
exports.Let = Let;
exports.Type = { tag: 'Type' };
const Pi = (usage, mode, name, type, body) => ({ tag: 'Pi', usage, mode, name, type, body });
exports.Pi = Pi;
const Abs = (usage, mode, name, type, body) => ({ tag: 'Abs', usage, mode, name, type, body });
exports.Abs = Abs;
const App = (fn, mode, arg) => ({ tag: 'App', fn, mode, arg });
exports.App = App;
const Sigma = (usage, name, type, body) => ({ tag: 'Sigma', usage, name, type, body });
exports.Sigma = Sigma;
const Pair = (fst, snd) => ({ tag: 'Pair', fst, snd });
exports.Pair = Pair;
const IndSigma = (usage, motive, scrut, cas) => ({ tag: 'IndSigma', usage, motive, scrut, cas });
exports.IndSigma = IndSigma;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const flattenPi = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Pi') {
        params.push([c.usage, c.mode, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenPi = flattenPi;
const flattenAbs = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Abs') {
        params.push([c.usage, c.mode, c.name, c.type]);
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
const flattenSigma = (t) => {
    const params = [];
    let c = t;
    while (c.tag === 'Sigma') {
        params.push([c.usage, c.name, c.type]);
        c = c.body;
    }
    return [params, c];
};
exports.flattenSigma = flattenSigma;
const flattenPair = (t) => {
    const r = [];
    while (t.tag === 'Pair') {
        r.push(t.fst);
        t = t.snd;
    }
    r.push(t);
    return r;
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
const isSimple = (t) => t.tag === 'Type' || t.tag === 'Var';
const showS = (t) => showP(!isSimple(t), t);
const show = (t) => {
    if (t.tag === 'Type')
        return 'Type';
    if (t.tag === 'Var')
        return `${t.name}`;
    if (t.tag === 'Pi') {
        const [params, ret] = exports.flattenPi(t);
        return `${params.map(([u, m, x, t]) => u === usage_1.many && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' -> ')} -> ${exports.show(ret)}`;
    }
    if (t.tag === 'Abs') {
        const [params, body] = exports.flattenAbs(t);
        return `\\${params.map(([u, m, x, t]) => u === usage_1.many && m.tag === 'Expl' && !t ? x : `${m.tag === 'Expl' ? '(' : '{'}${u === usage_1.many ? '' : `${u} `}${x}${t ? ` : ${exports.show(t)}` : ''}${m.tag === 'Expl' ? ')' : '}'}`).join(' ')}. ${exports.show(body)}`;
    }
    if (t.tag === 'App') {
        const [fn, args] = exports.flattenApp(t);
        return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${exports.show(a)}}`).join(' ')}`;
    }
    if (t.tag === 'Let')
        return `let ${t.usage === usage_1.many ? '' : `${t.usage} `}${t.name}${t.type ? ` : ${showP(t.type.tag === 'Let', t.type)}` : ''} = ${showP(t.val.tag === 'Let', t.val)}; ${exports.show(t.body)}`;
    if (t.tag === 'Sigma') {
        const [params, ret] = exports.flattenSigma(t);
        return `${params.map(([u, x, t]) => u === usage_1.many && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `(${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(t)})`).join(' ** ')} ** ${exports.show(ret)}`;
    }
    if (t.tag === 'Pair') {
        const ps = exports.flattenPair(t);
        return `(${ps.map(exports.show).join(', ')})`;
    }
    if (t.tag === 'IndSigma')
        return `indSigma ${t.usage === usage_1.many ? '' : `${t.usage} `}${t.motive ? `{${exports.show(t.motive)}} ` : ''}${showS(t.scrut)} ${showS(t.cas)}`;
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(core_1.showProjType).join('.')}`;
    }
    return t;
};
exports.show = show;
const fromCore = (t, ns = List_1.nil) => {
    if (t.tag === 'Type')
        return exports.Type;
    if (t.tag === 'Var')
        return exports.Var(ns.index(t.index) || utils_1.impossible(`var out of scope in fromCore: ${t.index}`));
    if (t.tag === 'Global')
        return exports.Var(t.name);
    if (t.tag === 'App')
        return exports.App(exports.fromCore(t.fn, ns), t.mode, exports.fromCore(t.arg, ns));
    if (t.tag === 'Pi') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Pi(t.usage, t.mode, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Abs') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Abs(t.usage, t.mode, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Let') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Let(t.usage, x, exports.fromCore(t.type, ns), exports.fromCore(t.val, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Sigma') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Sigma(t.usage, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Pair')
        return exports.Pair(exports.fromCore(t.fst, ns), exports.fromCore(t.snd, ns));
    if (t.tag === 'IndSigma')
        return exports.IndSigma(t.usage, exports.fromCore(t.motive, ns), exports.fromCore(t.scrut, ns), exports.fromCore(t.cas, ns));
    if (t.tag === 'Proj')
        return exports.Proj(exports.fromCore(t.term, ns), t.proj);
    return t;
};
exports.fromCore = fromCore;
const showCore = (t, ns = List_1.nil) => exports.show(exports.fromCore(t, ns));
exports.showCore = showCore;
const showVal = (v, k = 0, ns = List_1.nil) => exports.show(exports.fromCore(values_1.quote(v, k), ns));
exports.showVal = showVal;

},{"./core":3,"./names":8,"./usage":13,"./utils/List":15,"./utils/utils":16,"./values":17}],12:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.typecheck = void 0;
const config_1 = require("./config");
const conversion_1 = require("./conversion");
const core_1 = require("./core");
const globals_1 = require("./globals");
const local_1 = require("./local");
const mode_1 = require("./mode");
const usage_1 = require("./usage");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const check = (local, tm, ty) => {
    config_1.log(() => `check ${core_1.show(tm)} : ${local_1.showValCore(local, ty)}`);
    const [ty2, u] = synth(local, tm);
    return utils_1.tryT(() => {
        config_1.log(() => `unify ${local_1.showValCore(local, ty2)} ~ ${local_1.showValCore(local, ty)}`);
        conversion_1.conv(local.level, ty2, ty);
        return u;
    }, e => utils_1.terr(`check failed (${core_1.show(tm)}): ${local_1.showValCore(local, ty2)} ~ ${local_1.showValCore(local, ty)}: ${e}`));
};
const synth = (local, tm) => {
    config_1.log(() => `synth ${core_1.show(tm)}`);
    if (tm.tag === 'Type')
        return [values_1.VType, usage_1.noUses(local.level)];
    if (tm.tag === 'Var') {
        const [entry, j] = local_1.indexEnvT(local.ts, tm.index) || utils_1.terr(`var out of scope ${core_1.show(tm)}`);
        const uses = usage_1.noUses(local.level).updateAt(j, _ => local.usage);
        return [entry.type, uses];
    }
    if (tm.tag === 'Global') {
        const e = globals_1.globalLoad(tm.name);
        if (!e)
            return utils_1.terr(`undefined global or failed to load global ${tm.name}`);
        return [e.type, usage_1.noUses(local.level)];
    }
    if (tm.tag === 'App') {
        const [fnty, fnu] = synth(local, tm.fn);
        const [rty, argu] = synthapp(local, fnty, tm.mode, tm.arg);
        return [rty, usage_1.addUses(fnu, argu)];
    }
    if (tm.tag === 'Abs') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const [rty, u] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
        const pi = values_1.evaluate(core_1.Pi(tm.usage, tm.mode, tm.name, tm.type, values_1.quote(rty, local.level + 1)), local.vs);
        const [ux, urest] = u.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${core_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [pi, urest];
    }
    if (tm.tag === 'Pi') {
        const u1 = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const u2 = check(local.bind(usage_1.many, tm.mode, tm.name, ty), tm.body, values_1.VType);
        const [, urest] = u2.uncons();
        return [values_1.VType, usage_1.addUses(u1, urest)];
    }
    if (tm.tag === 'Let') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const uv = check(local, tm.val, ty);
        const v = values_1.evaluate(tm.val, local.vs);
        const [rty, ub] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
        const [ux, urest] = ub.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${core_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [rty, usage_1.addUses(usage_1.multiplyUses(ux, uv), urest)];
    }
    if (tm.tag === 'Sigma') {
        const u1 = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const u2 = check(local.bind(usage_1.many, mode_1.Expl, tm.name, ty), tm.body, values_1.VType);
        const [, urest] = u2.uncons();
        return [values_1.VType, usage_1.addUses(u1, urest)];
    }
    if (tm.tag === 'Pair') {
        check(local.inType(), tm.type, values_1.VType);
        const vsigma_ = values_1.evaluate(tm.type, local.vs);
        const vsigma = values_1.force(vsigma_);
        if (vsigma.tag !== 'VSigma')
            return utils_1.terr(`pair without sigma type: ${core_1.show(tm)}`);
        const u1 = check(local, tm.fst, vsigma.type);
        const u2 = check(local, tm.snd, values_1.vinst(vsigma, values_1.evaluate(tm.fst, local.vs)));
        return [vsigma_, usage_1.addUses(usage_1.multiplyUses(vsigma.usage, u1), u2)];
    }
    if (tm.tag === 'IndSigma') {
        /*
          1 <= q
          G |- p : (u x : A) ** B
          G |- P : ((u x : A) ** B x) -> Type
          G |- k : (q * u x : A) -> (q y : B x) -> P (x, y)
          ---------------------------------------------
          q * G |- indSigma q P p k : P p
        */
        if (!usage_1.sub(usage_1.one, tm.usage))
            return utils_1.terr(`usage must be 1 <= q in sigma induction ${core_1.show(tm)}: ${tm.usage}`);
        const [sigma_, u1] = synth(local, tm.scrut);
        const sigma = values_1.force(sigma_);
        if (sigma.tag !== 'VSigma')
            return utils_1.terr(`not a sigma type in ${core_1.show(tm)}: ${local_1.showVal(local, sigma_)}`);
        check(local.inType(), tm.motive, values_1.VPi(usage_1.many, mode_1.Expl, '_', sigma_, _ => values_1.VType));
        const motive = values_1.evaluate(tm.motive, local.vs);
        const u2 = check(local, tm.cas, values_1.VPi(usage_1.multiply(tm.usage, sigma.usage), mode_1.Expl, 'x', sigma.type, x => values_1.VPi(tm.usage, mode_1.Expl, 'y', values_1.vinst(sigma, x), y => values_1.vapp(motive, mode_1.Expl, values_1.VPair(x, y, sigma_)))));
        return [values_1.vapp(motive, mode_1.Expl, values_1.evaluate(tm.scrut, local.vs)), usage_1.multiplyUses(tm.usage, usage_1.addUses(u1, u2))];
    }
    if (tm.tag === 'Proj') {
        const [sigma_, u1] = synth(local, tm.term);
        const sigma = values_1.force(sigma_);
        if (sigma.tag !== 'VSigma')
            return utils_1.terr(`not a sigma type in ${core_1.show(tm)}: ${local_1.showVal(local, sigma_)}`);
        if (local.usage === '1' && (sigma.usage === '1' || (sigma.usage === '0' && tm.proj.proj === 'fst')))
            return utils_1.terr(`cannot project ${core_1.show(tm)}, usage must be *: ${local_1.showVal(local, sigma_)}`);
        return [tm.proj.proj === 'fst' ? sigma.type : values_1.vinst(sigma, values_1.vproj(values_1.evaluate(tm.term, local.vs), 'fst')), u1];
    }
    return tm;
};
const synthapp = (local, ty_, mode, arg) => {
    config_1.log(() => `synthapp ${local_1.showValCore(local, ty_)} @ ${core_1.show(arg)}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VPi' && mode_1.eqMode(ty.mode, mode)) {
        const cty = ty.type;
        const uses = check(local, arg, cty);
        const v = values_1.evaluate(arg, local.vs);
        return [values_1.vinst(ty, v), usage_1.multiplyUses(ty.usage, uses)];
    }
    return utils_1.terr(`not a correct pi type in synthapp: ${local_1.showValCore(local, ty)} @ ${core_1.show(arg)}`);
};
const typecheck = (t, local = local_1.Local.empty()) => {
    const [vty] = synth(local, t);
    const ty = values_1.quote(vty, 0);
    return ty;
};
exports.typecheck = typecheck;

},{"./config":1,"./conversion":2,"./core":3,"./globals":5,"./local":6,"./mode":7,"./usage":13,"./utils/utils":16,"./values":17}],13:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.lubUses = exports.multiplyUses = exports.addUses = exports.noUses = exports.lub = exports.sub = exports.multiply = exports.add = exports.many = exports.one = exports.zero = exports.usages = void 0;
const List_1 = require("./utils/List");
exports.usages = ['0', '1', '*'];
exports.zero = '0';
exports.one = '1';
exports.many = '*';
const add = (a, b) => {
    if (a === '*' || b === '*')
        return '*';
    if (a === '1')
        return b === '1' ? '*' : '1';
    return b;
};
exports.add = add;
const multiply = (a, b) => {
    if (a === '0' || b === '0')
        return '0';
    if (a === '1')
        return b;
    if (b === '1')
        return a;
    return '*';
};
exports.multiply = multiply;
const sub = (a, b) => (a === b) || ((a === '0' || a === '1') && b === '*');
exports.sub = sub;
const lub = (a, b) => a === b ? a : '*';
exports.lub = lub;
const noUses = (size) => List_1.List.range(size).map(() => exports.zero);
exports.noUses = noUses;
const addUses = (a, b) => a.zipWith(b, exports.add);
exports.addUses = addUses;
const multiplyUses = (a, b) => b.map(x => exports.multiply(a, x));
exports.multiplyUses = multiplyUses;
const lubUses = (a, b) => a.zipWith(b, exports.lub);
exports.lubUses = lubUses;

},{"./utils/List":15}],14:[function(require,module,exports){
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
    length() { return 0; }
    uncons() { return utils_1.impossible('uncons called on Nil'); }
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
}
exports.Cons = Cons;
exports.nil = new Nil();
const cons = (head, tail) => new Cons(head, tail);
exports.cons = cons;

},{"./utils":16}],16:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.eqArr = exports.mapObj = exports.tryTE = exports.tryT = exports.hasDuplicates = exports.range = exports.loadFileSync = exports.loadFile = exports.serr = exports.terr = exports.impossible = void 0;
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

},{"fs":19}],17:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.show = exports.normalize = exports.quote = exports.evaluate = exports.vproj = exports.vindsigma = exports.vapp = exports.force = exports.vinst = exports.VVar = exports.VPair = exports.VSigma = exports.VPi = exports.VAbs = exports.VGlobal = exports.VNe = exports.VType = exports.EProj = exports.EIndSigma = exports.EApp = exports.HVar = void 0;
const core_1 = require("./core");
const globals_1 = require("./globals");
const mode_1 = require("./mode");
const Lazy_1 = require("./utils/Lazy");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const HVar = (level) => ({ tag: 'HVar', level });
exports.HVar = HVar;
const EApp = (mode, arg) => ({ tag: 'EApp', mode, arg });
exports.EApp = EApp;
const EIndSigma = (usage, motive, cas) => ({ tag: 'EIndSigma', usage, motive, cas });
exports.EIndSigma = EIndSigma;
const EProj = (proj) => ({ tag: 'EProj', proj });
exports.EProj = EProj;
exports.VType = { tag: 'VType' };
const VNe = (head, spine) => ({ tag: 'VNe', head, spine });
exports.VNe = VNe;
;
const VGlobal = (head, spine, val) => ({ tag: 'VGlobal', head, spine, val });
exports.VGlobal = VGlobal;
const VAbs = (usage, mode, name, type, clos) => ({ tag: 'VAbs', usage, mode, name, type, clos });
exports.VAbs = VAbs;
const VPi = (usage, mode, name, type, clos) => ({ tag: 'VPi', usage, mode, name, type, clos });
exports.VPi = VPi;
const VSigma = (usage, name, type, clos) => ({ tag: 'VSigma', usage, name, type, clos });
exports.VSigma = VSigma;
const VPair = (fst, snd, type) => ({ tag: 'VPair', fst, snd, type });
exports.VPair = VPair;
const VVar = (level, spine = List_1.nil) => exports.VNe(exports.HVar(level), spine);
exports.VVar = VVar;
const vinst = (val, arg) => val.clos(arg);
exports.vinst = vinst;
const force = (v) => {
    if (v.tag === 'VGlobal')
        return exports.force(v.val.get());
    return v;
};
exports.force = force;
const vapp = (left, mode, right) => {
    if (left.tag === 'VAbs')
        return exports.vinst(left, right);
    if (left.tag === 'VNe')
        return exports.VNe(left.head, List_1.cons(exports.EApp(mode, right), left.spine));
    if (left.tag === 'VGlobal')
        return exports.VGlobal(left.head, List_1.cons(exports.EApp(mode, right), left.spine), left.val.map(v => exports.vapp(v, mode, right)));
    return utils_1.impossible(`vapp: ${left.tag}`);
};
exports.vapp = vapp;
const vindsigma = (usage, motive, scrut, cas) => {
    if (scrut.tag === 'VPair')
        return exports.vapp(exports.vapp(cas, mode_1.Expl, scrut.fst), mode_1.Expl, scrut.snd);
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EIndSigma(usage, motive, cas), scrut.spine));
    if (scrut.tag === 'VGlobal')
        return exports.VGlobal(scrut.head, List_1.cons(exports.EIndSigma(usage, motive, cas), scrut.spine), scrut.val.map(v => exports.vindsigma(usage, motive, v, cas)));
    return utils_1.impossible(`vindsigma: ${scrut.tag}`);
};
exports.vindsigma = vindsigma;
const vproj = (scrut, proj) => {
    if (scrut.tag === 'VPair')
        return proj === 'fst' ? scrut.fst : scrut.snd;
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine));
    if (scrut.tag === 'VGlobal')
        return exports.VGlobal(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine), scrut.val.map(v => exports.vproj(v, proj)));
    return utils_1.impossible(`vindsigma: ${scrut.tag}`);
};
exports.vproj = vproj;
const evaluate = (t, vs) => {
    if (t.tag === 'Type')
        return exports.VType;
    if (t.tag === 'Abs')
        return exports.VAbs(t.usage, t.mode, t.name, exports.evaluate(t.type, vs), v => exports.evaluate(t.body, List_1.cons(v, vs)));
    if (t.tag === 'Pi')
        return exports.VPi(t.usage, t.mode, t.name, exports.evaluate(t.type, vs), v => exports.evaluate(t.body, List_1.cons(v, vs)));
    if (t.tag === 'Var')
        return vs.index(t.index) || utils_1.impossible(`evaluate: var ${t.index} has no value`);
    if (t.tag === 'Global')
        return exports.VGlobal(t.name, List_1.nil, Lazy_1.Lazy.from(() => {
            const e = globals_1.globalLoad(t.name);
            if (!e)
                return utils_1.terr(`failed to load global ${t.name}`);
            return e.val;
        }));
    if (t.tag === 'App')
        return exports.vapp(exports.evaluate(t.fn, vs), t.mode, exports.evaluate(t.arg, vs));
    if (t.tag === 'Let')
        return exports.evaluate(t.body, List_1.cons(exports.evaluate(t.val, vs), vs));
    if (t.tag === 'Sigma')
        return exports.VSigma(t.usage, t.name, exports.evaluate(t.type, vs), v => exports.evaluate(t.body, List_1.cons(v, vs)));
    if (t.tag === 'Pair')
        return exports.VPair(exports.evaluate(t.fst, vs), exports.evaluate(t.snd, vs), exports.evaluate(t.type, vs));
    if (t.tag === 'IndSigma')
        return exports.vindsigma(t.usage, exports.evaluate(t.motive, vs), exports.evaluate(t.scrut, vs), exports.evaluate(t.cas, vs));
    if (t.tag === 'Proj')
        return exports.vproj(exports.evaluate(t.term, vs), t.proj.proj);
    return t;
};
exports.evaluate = evaluate;
const quoteHead = (h, k) => {
    if (h.tag === 'HVar')
        return core_1.Var(k - (h.level + 1));
    return h.tag;
};
const quoteElim = (t, e, k, full) => {
    if (e.tag === 'EApp')
        return core_1.App(t, e.mode, exports.quote(e.arg, k, full));
    if (e.tag === 'EIndSigma')
        return core_1.IndSigma(e.usage, exports.quote(e.motive, k), t, exports.quote(e.cas, k));
    if (e.tag === 'EProj')
        return core_1.Proj(t, e.proj === 'fst' ? core_1.PFst : core_1.PSnd);
    return e;
};
const quote = (v, k, full = false) => {
    if (v.tag === 'VType')
        return core_1.Type;
    if (v.tag === 'VNe')
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full), quoteHead(v.head, k));
    if (v.tag === 'VGlobal') {
        if (full)
            return exports.quote(v.val.get(), k, full);
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full), core_1.Global(v.head));
    }
    if (v.tag === 'VAbs')
        return core_1.Abs(v.usage, v.mode, v.name, exports.quote(v.type, k, full), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full));
    if (v.tag === 'VPi')
        return core_1.Pi(v.usage, v.mode, v.name, exports.quote(v.type, k, full), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full));
    if (v.tag === 'VSigma')
        return core_1.Sigma(v.usage, v.name, exports.quote(v.type, k), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1));
    if (v.tag === 'VPair')
        return core_1.Pair(exports.quote(v.fst, k), exports.quote(v.snd, k), exports.quote(v.type, k));
    return v;
};
exports.quote = quote;
const normalize = (t, vs = List_1.nil, full = false) => exports.quote(exports.evaluate(t, vs), 0, full);
exports.normalize = normalize;
const show = (v, k = 0, full = false) => core_1.show(exports.quote(v, k, full));
exports.show = show;

},{"./core":3,"./globals":5,"./mode":7,"./utils/Lazy":14,"./utils/List":15,"./utils/utils":16}],18:[function(require,module,exports){
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
repl_1.initREPL();
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

},{"./repl":10}],19:[function(require,module,exports){

},{}]},{},[18]);
