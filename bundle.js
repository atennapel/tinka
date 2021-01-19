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
const core_1 = require("./core");
const mode_1 = require("./mode");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const eqHead = (a, b) => {
    if (a === b)
        return true;
    if (a.tag === 'HVar')
        return b.tag === 'HVar' && a.level === b.level;
    if (a.tag === 'HPrim')
        return b.tag === 'HPrim' && a.name === b.name;
    if (a.tag === 'HGlobal')
        return b.tag === 'HGlobal' && a.name === b.name;
    return a;
};
exports.eqHead = eqHead;
const convPIndex = (k, va, vb, sa, sb, index) => {
    if (index === 0)
        return convSpines(k, va, vb, sa, sb);
    if (sa.isCons() && sa.head.tag === 'EProj' && sa.head.proj.tag === 'PProj' && sa.head.proj.proj === 'snd')
        return convPIndex(k, va, vb, sa.tail, sb, index - 1);
    return utils_1.terr(`conv failed (${k}): ${values_1.show(va, k)} ~ ${values_1.show(vb, k)}`);
};
const convSpines = (k, va, vb, sa, sb) => {
    if (sa.isNil() && sb.isNil())
        return;
    if (sa.isCons() && sb.isCons()) {
        const a = sa.head;
        const b = sb.head;
        if (a === b)
            return convSpines(k, va, vb, sa.tail, sb.tail);
        if (a.tag === 'EApp' && b.tag === 'EApp' && mode_1.eqMode(a.mode, b.mode)) {
            exports.conv(k, a.arg, b.arg);
            return convSpines(k, va, vb, sa.tail, sb.tail);
        }
        if (a.tag === 'EPrimElim' && b.tag === 'EPrimElim' && a.usage === b.usage && a.cases.length === b.cases.length) {
            exports.conv(k, a.motive, b.motive);
            for (let i = 0, l = a.cases.length; i < l; i++)
                exports.conv(k, a.cases[i], b.cases[i]);
            return convSpines(k, va, vb, sa.tail, sb.tail);
        }
        if (a.tag === 'EProj' && b.tag === 'EProj') {
            if (a.proj === b.proj)
                return convSpines(k, va, vb, sa.tail, sb.tail);
            if (a.proj.tag === 'PProj' && b.proj.tag === 'PProj' && a.proj.proj === b.proj.proj)
                return convSpines(k, va, vb, sa.tail, sb.tail);
            if (a.proj.tag === 'PIndex' && b.proj.tag === 'PIndex' && a.proj.index === b.proj.index)
                return convSpines(k, va, vb, sa.tail, sb.tail);
            if (a.proj.tag === 'PProj' && a.proj.proj === 'fst' && b.proj.tag === 'PIndex')
                return convPIndex(k, va, vb, sa.tail, sb.tail, b.proj.index);
            if (b.proj.tag === 'PProj' && b.proj.proj === 'fst' && a.proj.tag === 'PIndex')
                return convPIndex(k, va, vb, sb.tail, sa.tail, a.proj.index);
        }
    }
    return utils_1.terr(`conv failed (${k}): ${values_1.show(va, k)} ~ ${values_1.show(vb, k)}`);
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
    if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.usage === b.usage && a.exclusive === b.exclusive) {
        exports.conv(k, a.type, b.type);
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VPropEq' && b.tag === 'VPropEq') {
        exports.conv(k, a.type, b.type);
        exports.conv(k, a.left, b.left);
        return exports.conv(k, a.right, b.right);
    }
    if (a.tag === 'VAbs' && b.tag === 'VAbs') {
        const v = values_1.VVar(k);
        return exports.conv(k + 1, values_1.vinst(a, v), values_1.vinst(b, v));
    }
    if (a.tag === 'VPair' && b.tag === 'VPair') {
        exports.conv(k, a.fst, b.fst);
        return exports.conv(k, a.snd, b.snd);
    }
    if (a.tag === 'VRefl' && b.tag === 'VRefl') {
        exports.conv(k, a.type, b.type);
        return exports.conv(k, a.val, b.val);
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
        exports.conv(k, a.fst, values_1.vproj(b, core_1.PFst));
        exports.conv(k, a.snd, values_1.vproj(b, core_1.PSnd));
        return;
    }
    if (b.tag === 'VPair') {
        exports.conv(k, values_1.vproj(a, core_1.PFst), b.fst);
        exports.conv(k, values_1.vproj(a, core_1.PSnd), b.snd);
        return;
    }
    if (values_1.isVUnit(a))
        return;
    if (values_1.isVUnit(b))
        return;
    if (a.tag === 'VNe' && b.tag === 'VNe' && exports.eqHead(a.head, b.head))
        return convSpines(k, a, b, a.spine, b.spine);
    if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && exports.eqHead(a.head, b.head))
        return utils_1.tryT(() => convSpines(k, a, b, a.spine, b.spine), () => exports.conv(k, a.val.get(), b.val.get()));
    if (a.tag === 'VGlobal')
        return exports.conv(k, a.val.get(), b);
    if (b.tag === 'VGlobal')
        return exports.conv(k, a, b.val.get());
    return utils_1.terr(`conv failed (${k}): ${values_1.show(a, k)} ~ ${values_1.show(b, k)}`);
};
exports.conv = conv;

},{"./config":1,"./core":3,"./mode":9,"./utils/utils":19,"./values":20}],3:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.subst = exports.substVar = exports.shift = exports.show = exports.flattenProj = exports.flattenPair = exports.flattenSigma = exports.flattenApp = exports.flattenAbs = exports.flattenPi = exports.PIndex = exports.PSnd = exports.PFst = exports.PProj = exports.Unit = exports.UnitType = exports.PrimElim = exports.Refl = exports.PropEq = exports.Proj = exports.Pair = exports.Sigma = exports.App = exports.Abs = exports.Pi = exports.Let = exports.Prim = exports.Global = exports.Var = void 0;
const usage_1 = require("./usage");
const Var = (index) => ({ tag: 'Var', index });
exports.Var = Var;
const Global = (name) => ({ tag: 'Global', name });
exports.Global = Global;
const Prim = (name) => ({ tag: 'Prim', name });
exports.Prim = Prim;
const Let = (usage, name, type, val, body) => ({ tag: 'Let', usage, name, type, val, body });
exports.Let = Let;
const Pi = (usage, mode, name, type, body) => ({ tag: 'Pi', usage, mode, name, type, body });
exports.Pi = Pi;
const Abs = (usage, mode, name, type, body) => ({ tag: 'Abs', usage, mode, name, type, body });
exports.Abs = Abs;
const App = (fn, mode, arg) => ({ tag: 'App', fn, mode, arg });
exports.App = App;
const Sigma = (usage, exclusive, name, type, body) => ({ tag: 'Sigma', usage, exclusive, name, type, body });
exports.Sigma = Sigma;
const Pair = (fst, snd, type) => ({ tag: 'Pair', fst, snd, type });
exports.Pair = Pair;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const PropEq = (type, left, right) => ({ tag: 'PropEq', type, left, right });
exports.PropEq = PropEq;
;
const Refl = (type, val) => ({ tag: 'Refl', type, val });
exports.Refl = Refl;
const PrimElim = (name, usage, motive, scrut, cases) => ({ tag: 'PrimElim', name, usage, motive, scrut, cases });
exports.PrimElim = PrimElim;
exports.UnitType = exports.Prim('()');
exports.Unit = exports.Prim('*');
const PProj = (proj) => ({ tag: 'PProj', proj });
exports.PProj = PProj;
exports.PFst = exports.PProj('fst');
exports.PSnd = exports.PProj('snd');
const PIndex = (name, index) => ({ tag: 'PIndex', name, index });
exports.PIndex = PIndex;
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
        params.push([c.usage, c.exclusive, c.name, c.type]);
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
const isSimple = (t) => t.tag === 'Var' || t.tag === 'Global' || t.tag === 'Prim' || t.tag === 'Proj';
const showS = (t) => showP(!isSimple(t), t);
const showProjType = (p) => {
    if (p.tag === 'PProj')
        return p.proj === 'fst' ? '_1' : '_2';
    if (p.tag === 'PIndex')
        return p.name ? `${p.name}` : `${p.index}`;
    return p;
};
const show = (t) => {
    if (t.tag === 'Var')
        return `'${t.index}`;
    if (t.tag === 'Global')
        return `${t.name}`;
    if (t.tag === 'Prim')
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
        const ps = params.map(([u, e, x, ty]) => {
            const param = u === usage_1.many && x === '_' ? showP(ty.tag === 'Pi' || ty.tag === 'Sigma' || ty.tag === 'Let', ty) : `(${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(ty)})`;
            return `${param} ${e ? '||' : '**'} `;
        }).join('');
        return `${ps}${exports.show(ret)}`;
    }
    if (t.tag === 'Pair') {
        const ps = exports.flattenPair(t);
        return `(${ps.map(t => exports.show(t)).join(', ')} : ${exports.show(t.type)})`;
    }
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
    }
    if (t.tag === 'PropEq')
        return `{${exports.show(t.type)}} ${exports.show(t.left)} = ${exports.show(t.right)}`;
    if (t.tag === 'Refl')
        return `Refl {${exports.show(t.type)}} {${exports.show(t.val)}}`;
    if (t.tag === 'PrimElim')
        return `${t.name} ${t.usage === usage_1.many ? '' : `${t.usage} `}${showS(t.motive)} ${showS(t.scrut)}${t.cases.map(c => ` ${showS(c)}`).join('')}`;
    return t;
};
exports.show = show;
const shift = (d, c, t) => {
    if (t.tag === 'Var')
        return t.index < c ? t : exports.Var(t.index + d);
    if (t.tag === 'App')
        return exports.App(exports.shift(d, c, t.fn), t.mode, exports.shift(d, c, t.arg));
    if (t.tag === 'Abs')
        return exports.Abs(t.usage, t.mode, t.name, exports.shift(d, c, t.type), exports.shift(d, c + 1, t.body));
    if (t.tag === 'Pair')
        return exports.Pair(exports.shift(d, c, t.fst), exports.shift(d, c, t.snd), exports.shift(d, c, t.type));
    if (t.tag === 'Proj')
        return exports.Proj(exports.shift(d, c, t.term), t.proj);
    if (t.tag === 'Let')
        return exports.Let(t.usage, t.name, exports.shift(d, c, t.type), exports.shift(d, c, t.val), exports.shift(d, c + 1, t.body));
    if (t.tag === 'Pi')
        return exports.Pi(t.usage, t.mode, t.name, exports.shift(d, c, t.type), exports.shift(d, c + 1, t.body));
    if (t.tag === 'Sigma')
        return exports.Sigma(t.usage, t.exclusive, t.name, exports.shift(d, c, t.type), exports.shift(d, c + 1, t.body));
    if (t.tag === 'PropEq')
        return exports.PropEq(exports.shift(d, c, t.type), exports.shift(d, c, t.left), exports.shift(d, c, t.right));
    if (t.tag === 'Refl')
        return exports.Refl(exports.shift(d, c, t.type), exports.shift(d, c, t.val));
    if (t.tag === 'PrimElim')
        return exports.PrimElim(t.name, t.usage, exports.shift(d, c, t.motive), exports.shift(d, c, t.scrut), t.cases.map(x => exports.shift(d, c, x)));
    return t;
};
exports.shift = shift;
const substVar = (j, s, t) => {
    if (t.tag === 'Var')
        return t.index === j ? s : t;
    if (t.tag === 'App')
        return exports.App(exports.substVar(j, s, t.fn), t.mode, exports.substVar(j, s, t.arg));
    if (t.tag === 'Abs')
        return exports.Abs(t.usage, t.mode, t.name, exports.substVar(j, s, t.type), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'Pair')
        return exports.Pair(exports.substVar(j, s, t.fst), exports.substVar(j, s, t.snd), exports.substVar(j, s, t.type));
    if (t.tag === 'Proj')
        return exports.Proj(exports.substVar(j, s, t.term), t.proj);
    if (t.tag === 'Let')
        return exports.Let(t.usage, t.name, exports.substVar(j, s, t.type), exports.substVar(j, s, t.val), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'Pi')
        return exports.Pi(t.usage, t.mode, t.name, exports.substVar(j, s, t.type), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'Sigma')
        return exports.Sigma(t.usage, t.exclusive, t.name, exports.substVar(j, s, t.type), exports.substVar(j + 1, exports.shift(1, 0, s), t.body));
    if (t.tag === 'PropEq')
        return exports.PropEq(exports.substVar(j, s, t.type), exports.substVar(j, s, t.left), exports.substVar(j, s, t.right));
    if (t.tag === 'Refl')
        return exports.Refl(exports.substVar(j, s, t.type), exports.substVar(j, s, t.val));
    if (t.tag === 'PrimElim')
        return exports.PrimElim(t.name, t.usage, exports.substVar(j, s, t.motive), exports.substVar(j, s, t.scrut), t.cases.map(x => exports.substVar(j, s, x)));
    return t;
};
exports.substVar = substVar;
const subst = (t, u) => exports.shift(-1, 0, exports.substVar(0, exports.shift(1, 0, u), t));
exports.subst = subst;

},{"./usage":16}],4:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.elaborate = void 0;
const config_1 = require("./config");
const core_1 = require("./core");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const surface_1 = require("./surface");
const S = require("./surface");
const conversion_1 = require("./conversion");
const usage_1 = require("./usage");
const local_1 = require("./local");
const mode_1 = require("./mode");
const globals_1 = require("./globals");
const List_1 = require("./utils/List");
const prims_1 = require("./prims");
const check = (local, tm, ty_) => {
    config_1.log(() => `check (${local.level}) ${surface_1.show(tm)} : ${local_1.showVal(local, ty_)}`);
    const ty = values_1.force(ty_);
    if (tm.tag === 'Abs' && !tm.type && ty.tag === 'VPi' && mode_1.eqMode(tm.mode, ty.mode) && (tm.usage === usage_1.many || tm.usage === ty.usage)) {
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
        if (ty.exclusive)
            return [core_1.Pair(fst, snd, values_1.quote(ty, local.level)), usage_1.lubUses(u1, u2)]; // TODO
        return [core_1.Pair(fst, snd, values_1.quote(ty, local.level)), usage_1.addUses(usage_1.multiplyUses(ty.usage, u1), u2)];
    }
    if (tm.tag === 'Refl' && !tm.type && !tm.val && ty.tag === 'VPropEq') {
        utils_1.tryT(() => conversion_1.conv(local.level, ty.left, ty.right), e => utils_1.terr(`check failed (${surface_1.show(tm)}): ${local_1.showVal(local, ty_)}: ${e}`));
        return [core_1.Refl(values_1.quote(ty.type, local.level), values_1.quote(ty.left, local.level)), usage_1.noUses(local.level)];
    }
    if (tm.tag === 'Let') {
        let vtype;
        let vty;
        let val;
        let uv;
        if (tm.type) {
            [vtype] = check(local.inType(), tm.type, values_1.VType);
            vty = values_1.evaluate(vtype, local.vs);
            [val, uv] = check(tm.usage === usage_1.zero ? local.inType() : local, tm.val, ty);
        }
        else {
            [val, vty, uv] = synth(tm.usage === usage_1.zero ? local.inType() : local, tm.val);
            vtype = values_1.quote(vty, local.level);
        }
        const v = values_1.evaluate(val, local.vs);
        const [body, ub] = check(local.define(tm.usage, tm.name, vty, v), tm.body, ty_);
        const [ux, urest] = ub.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${surface_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [core_1.Let(tm.usage, tm.name, vtype, val, body), usage_1.addUses(usage_1.multiplyUses(ux, uv), urest)];
    }
    if (tm.tag === 'Hole') {
        const n = local.level;
        const ts = local.ts;
        const ns = local.ns;
        const vs = local.vs;
        const usage = local.usage;
        const r = [];
        for (let i = 0; i < n; i++) {
            const t = ts.index(i);
            const v = vs.index(i);
            const x = ns.index(i);
            if (!t || !v || !x)
                continue;
            const type = local_1.showVal(local, t.type);
            r.push(`${t.inserted ? 'inserted ' : ''}${t.usage === usage_1.many ? '' : `${t.usage} `}${mode_1.eqMode(t.mode, mode_1.Impl) ? '{' : ''}${x}${mode_1.eqMode(t.mode, mode_1.Impl) ? '}' : ''} : ${type}${t.bound ? '' : ` = ${local_1.showVal(local, v)}`}`);
        }
        return utils_1.terr(`hole: ${surface_1.show(tm)}, expected type: ${local_1.showVal(local, ty_)}\nlocal (${usage}):\n${r.join('\n')}`);
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
    if (tm.tag === 'Var') {
        if (prims_1.isPrimName(tm.name))
            return [core_1.Prim(tm.name), prims_1.synthPrim(tm.name), usage_1.noUses(local.level)];
        else {
            const i = local.nsSurface.indexOf(tm.name);
            if (i < 0) {
                const e = globals_1.globalLoad(tm.name);
                if (e)
                    return [core_1.Global(tm.name), e.type, usage_1.noUses(local.level)];
                return utils_1.terr(`undefined global ${tm.name}`);
            }
            else {
                const [entry, j] = local_1.indexEnvT(local.ts, i) || utils_1.terr(`undefined variable ${surface_1.show(tm)}`);
                const uses = usage_1.noUses(local.level).updateAt(j, _ => local.usage);
                return [core_1.Var(j), entry.type, uses];
            }
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
            [val, uv] = check(tm.usage === usage_1.zero ? local.inType() : local, tm.val, ty);
        }
        else {
            [val, ty, uv] = synth(tm.usage === usage_1.zero ? local.inType() : local, tm.val);
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
        return [core_1.Sigma(tm.usage, tm.exclusive, tm.name, type, body), values_1.VType, usage_1.addUses(u1, urest)];
    }
    if (tm.tag === 'Pair') {
        const [fst, ty1, u1] = synth(local, tm.fst);
        const [snd, ty2, u2] = synth(local, tm.snd);
        const ty = values_1.VSigma(usage_1.many, false, '_', ty1, _ => ty2);
        return [core_1.Pair(fst, snd, values_1.quote(ty, local.level)), ty, usage_1.addUses(usage_1.multiplyUses(ty.usage, u1), u2)];
    }
    if (tm.tag === 'PrimElim') {
        if (!usage_1.sub(usage_1.one, tm.usage))
            return utils_1.terr(`usage must be 1 <= q in ${surface_1.show(tm)} but got ${tm.usage}`);
        const [scrut, ty_, u1] = synth(local, tm.scrut);
        const [amount, cont] = prims_1.synthPrimElim(tm.name);
        if (tm.cases.length !== amount)
            return utils_1.terr(`invalid case amount, expected ${amount} but got ${tm.cases.length} in ${surface_1.show(tm)}`);
        try {
            const [tmotive, contcases] = cont(ty_, tm.usage);
            const [motive] = check(local.inType(), tm.motive, tmotive);
            const vmotive = values_1.evaluate(motive, local.vs);
            const vscrut = values_1.evaluate(scrut, local.vs);
            const [tycases, rty] = contcases(vmotive, vscrut);
            if (tycases.length !== amount)
                return utils_1.terr(`invalid ${tm.name}: amount does not match`);
            const rescases = tycases.map((ty, i) => check(local, tm.cases[i], ty));
            const uses = rescases.map(([, us]) => us);
            const scrutu = usage_1.multiplyUses(tm.usage, u1);
            const finaluses = uses.length === 0 ? scrutu : usage_1.addUses(scrutu, usage_1.lubUsesAll(uses));
            return [core_1.PrimElim(tm.name, tm.usage, motive, scrut, rescases.map(([t]) => t)), rty, finaluses];
        }
        catch (err) {
            if (!(err instanceof TypeError))
                throw err;
            return utils_1.terr(`synth ${surface_1.show(tm)} failed: ${err}`);
        }
    }
    if (tm.tag === 'Proj') {
        const [term, sigma_, u] = synth(local, tm.term);
        if (tm.proj.tag === 'PProj') {
            const sigma = values_1.force(sigma_);
            if (sigma.tag !== 'VSigma')
                return utils_1.terr(`not a sigma type in ${surface_1.show(tm)}: ${local_1.showVal(local, sigma_)}`);
            if (local.usage === usage_1.one && (sigma.usage === usage_1.one || (sigma.usage === usage_1.zero && tm.proj.proj === 'fst')))
                return utils_1.terr(`cannot project ${surface_1.show(tm)}, usage must be * or 0 with a second projection: ${local_1.showVal(local, sigma_)}`);
            const fst = sigma.name !== '_' ? core_1.PIndex(sigma.name, 0) : core_1.PFst; // TODO: is this nice?
            return [core_1.Proj(term, tm.proj), tm.proj.proj === 'fst' ? sigma.type : values_1.vinst(sigma, values_1.vproj(values_1.evaluate(term, local.vs), fst)), u];
        }
        else if (tm.proj.tag === 'PName') {
            const orig = values_1.evaluate(term, local.vs);
            const [ty, ix] = projectName(local, tm, orig, orig, sigma_, tm.proj.name, 0);
            return [core_1.Proj(term, core_1.PIndex(tm.proj.name, ix)), ty, u];
        }
        else
            return [core_1.Proj(term, core_1.PIndex(null, tm.proj.index)), projectIndex(local, tm, values_1.evaluate(term, local.vs), sigma_, tm.proj.index), u];
    }
    if (tm.tag === 'Import') {
        const [term, sigma_,] = synth(local, tm.term);
        const vterm = values_1.evaluate(term, local.vs);
        return createImportTerm(local, term, vterm, sigma_, tm.imports, tm.body);
    }
    if (tm.tag === 'Signature') {
        let clocal = local;
        const edefs = [];
        for (let i = 0, l = tm.defs.length; i < l; i++) {
            const e = tm.defs[i];
            let type;
            if (e.type) {
                [type] = check(clocal.inType(), e.type, values_1.VType);
            }
            else {
                // type = newMeta(clocal, e.erased, VType);
                return utils_1.terr(`signature definition must have a type: ${surface_1.show(tm)}`);
            }
            edefs.push([e, type]);
            const ty = values_1.evaluate(type, clocal.vs);
            clocal = clocal.bind(e.usage, mode_1.Expl, e.name, ty);
        }
        const stype = edefs.reduceRight((t, [e, type]) => core_1.Sigma(e.usage, false, e.name, type, t), core_1.UnitType);
        return [stype, values_1.VType, usage_1.noUses(local.level)];
    }
    if (tm.tag === 'Module') {
        const defs = List_1.List.from(tm.defs);
        const [term, type, u] = createModuleTerm(local, defs, tm);
        return [term, values_1.evaluate(type, local.vs), u];
    }
    if (tm.tag === 'PropEq') {
        if (tm.type) {
            const [type] = check(local.inType(), tm.type, values_1.VType);
            const ty = values_1.evaluate(type, local.vs);
            const [left, u1] = check(local, tm.left, ty);
            const [right, u2] = check(local, tm.right, ty);
            return [core_1.PropEq(type, left, right), values_1.VType, usage_1.addUses(u1, u2)];
        }
        else {
            const [left, ty, u1] = synth(local, tm.left);
            const [right, u2] = check(local, tm.right, ty);
            return [core_1.PropEq(values_1.quote(ty, local.level), left, right), values_1.VType, usage_1.addUses(u1, u2)];
        }
    }
    if (tm.tag === 'Refl' && tm.type && tm.val) {
        const [type] = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(type, local.vs);
        const [val] = check(local.inType(), tm.val, ty);
        const x = values_1.evaluate(val, local.vs);
        return [core_1.Refl(type, val), values_1.VPropEq(ty, x, x), usage_1.noUses(local.level)];
    }
    if (tm.tag === 'Ann') {
        const [type] = check(local.inType(), tm.type, values_1.VType);
        const vtype = values_1.evaluate(type, local.vs);
        const [term, u] = check(local, tm.term, vtype);
        return [core_1.Let(usage_1.one, 'x', type, term, core_1.Var(0)), vtype, u];
    }
    return utils_1.terr(`unable to synth ${surface_1.show(tm)}`);
};
const createModuleTerm = (local, entries, full) => {
    config_1.log(() => `createModuleTerm (${local.level}) ${entries.toString(v => `ModEntry(${v.name}, ${v.priv}, ${v.usage}, ${!v.type ? '' : surface_1.show(v.type)}, ${surface_1.show(v.val)})`)}`);
    if (entries.isCons()) {
        const e = entries.head;
        const rest = entries.tail;
        let type;
        let ty;
        let val;
        let u;
        if (e.type) {
            [type] = check(local.inType(), e.type, values_1.VType);
            ty = values_1.evaluate(type, local.vs);
            [val, u] = check(e.usage === usage_1.zero ? local.inType() : local, e.val, ty);
        }
        else {
            [val, ty, u] = synth(e.usage === usage_1.zero ? local.inType() : local, e.val);
            type = values_1.quote(ty, local.level);
        }
        const v = values_1.evaluate(val, local.vs);
        const nextlocal = local.define(e.usage, e.name, ty, v);
        const [nextterm, nexttype, u2] = createModuleTerm(nextlocal, rest, full);
        const [ux, urest] = u2.uncons();
        if (!usage_1.sub(ux, e.usage))
            return utils_1.terr(`usage error in ${surface_1.show(full)}: expected ${e.usage} for ${e.name} but actual ${ux}`);
        const nextuses = usage_1.addUses(usage_1.multiplyUses(e.usage, u), urest);
        if (e.priv) {
            return [core_1.Let(e.usage, e.name, type, val, nextterm), core_1.subst(nexttype, val), nextuses];
        }
        else {
            const sigma = core_1.Sigma(e.usage, false, e.name, type, nexttype);
            return [core_1.Let(e.usage, e.name, type, val, core_1.Pair(core_1.Var(0), nextterm, core_1.shift(1, 0, sigma))), sigma, nextuses];
        }
    }
    return [core_1.Unit, core_1.UnitType, usage_1.noUses(local.level)];
};
const createImportTerm = (local, term, vterm, sigma_, imports, body, i = 0) => {
    config_1.log(() => `createImportTerm (${local.level}) ${S.showCore(term, local.ns)} ${local_1.showVal(local, sigma_)}`);
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
            const newlocal = local.define(sigma.usage, name, sigma.type, val);
            const val2 = values_1.evaluate(core_1.Var(0), newlocal.vs);
            const [rest, ty, u2] = createImportTerm(newlocal, term, vterm, values_1.vinst(sigma, val2), nextimports, body, i + 1);
            const [ux, urest] = u2.uncons();
            if (!usage_1.sub(ux, sigma.usage))
                return utils_1.terr(`usage error in importing ${S.showCore(term, local.ns)}: expected ${sigma.usage} for ${sigma.name} but actual ${ux}`);
            return [core_1.Let(sigma.usage, name, values_1.quote(sigma.type, local.level), core_1.Proj(term, core_1.PIndex(sigma.name, i)), rest), ty, urest];
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
const getAllNamesFromSigma = (k, ty_, ns, a = [], all = []) => {
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (!ns || ns.includes(ty.name))
            a.push([ty.name, ty.usage]);
        all.push(ty.name);
        return getAllNamesFromSigma(k + 1, values_1.vinst(ty, values_1.VVar(k)), ns, a, all);
    }
    return [a, all];
};
const projectIndex = (local, full, tm, ty_, index) => {
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (local.usage === usage_1.one && (ty.usage === usage_1.one || (ty.usage === usage_1.zero && index === 0)))
            return utils_1.terr(`cannot project ${surface_1.show(full)}, usage must be * or 0 with a second projection: ${local_1.showVal(local, ty_)}`);
        if (index === 0)
            return ty.type;
        const fst = ty.name !== '_' ? core_1.PIndex(ty.name, 0) : core_1.PFst; // TODO: is this nice?
        return projectIndex(local, full, values_1.vproj(tm, core_1.PSnd), values_1.vinst(ty, values_1.vproj(tm, fst)), index - 1);
    }
    return utils_1.terr(`failed to project, ${surface_1.show(full)}: ${local_1.showVal(local, ty_)}`);
};
const projectName = (local, full, orig, tm, ty_, x, ix, ns = List_1.nil) => {
    config_1.log(() => `projectName (${local_1.showVal(local, tm)}) (${local_1.showVal(local, ty_)}) ${x} ${ix} ${ns.toString()}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (local.usage === usage_1.one && (ty.usage === usage_1.one || (ty.usage === usage_1.zero && ty.name === x)))
            return utils_1.terr(`cannot project ${surface_1.show(full)}, usage must be * or 0 with a second projection: ${local_1.showVal(local, ty_)}`);
        if (ty.name === x)
            return [ty.type, ix];
        const fst = ty.name !== '_' ? core_1.PIndex(ty.name, 0) : core_1.PFst; // TODO: is this nice?
        const vfst = ty.name !== '_' ? (!ns.contains(ty.name) ? values_1.vproj(orig, core_1.PIndex(ty.name, ix)) : values_1.vproj(tm, core_1.PIndex(ty.name, 0))) : values_1.vproj(tm, fst);
        config_1.log(() => local_1.showVal(local, vfst));
        return projectName(local, full, orig, values_1.vproj(tm, core_1.PSnd), values_1.vinst(ty, vfst), x, ix + 1, List_1.cons(ty.name, ns));
    }
    return utils_1.terr(`failed to project, ${surface_1.show(full)}: ${local_1.showVal(local, ty_)}`);
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
    const ty = values_1.quote(vty, local.level);
    return [tm, ty];
};
exports.elaborate = elaborate;

},{"./config":1,"./conversion":2,"./core":3,"./globals":7,"./local":8,"./mode":9,"./prims":12,"./surface":14,"./usage":16,"./utils/List":18,"./utils/utils":19,"./values":20}],5:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.erasePrimElim = exports.erasePrim = exports.show = exports.flattenProj = exports.flattenPair = exports.flattenApp = exports.TODO = exports.Type = exports.PIndex = exports.PSnd = exports.PFst = exports.PProj = exports.False = exports.True = exports.ElimFix = exports.ElimBool = exports.Bool = exports.Proj = exports.Pair = exports.App = exports.Abs = exports.Let = exports.Global = exports.Var = void 0;
const Var = (index) => ({ tag: 'Var', index });
exports.Var = Var;
const Global = (name) => ({ tag: 'Global', name });
exports.Global = Global;
const Let = (val, body) => ({ tag: 'Let', val, body });
exports.Let = Let;
const Abs = (body) => ({ tag: 'Abs', body });
exports.Abs = Abs;
const App = (fn, arg) => ({ tag: 'App', fn, arg });
exports.App = App;
const Pair = (fst, snd) => ({ tag: 'Pair', fst, snd });
exports.Pair = Pair;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const Bool = (value) => ({ tag: 'Bool', value });
exports.Bool = Bool;
const ElimBool = (term, ifTrue, ifFalse) => ({ tag: 'ElimBool', term, ifTrue, ifFalse });
exports.ElimBool = ElimBool;
const ElimFix = (term, cas) => ({ tag: 'ElimFix', term, cas });
exports.ElimFix = ElimFix;
exports.True = exports.Bool(true);
exports.False = exports.Bool(false);
const PProj = (proj) => ({ tag: 'PProj', proj });
exports.PProj = PProj;
exports.PFst = exports.PProj('fst');
exports.PSnd = exports.PProj('snd');
const PIndex = (index) => ({ tag: 'PIndex', index });
exports.PIndex = PIndex;
exports.Type = exports.False;
exports.TODO = exports.Global('TODO');
const flattenApp = (t) => {
    const args = [];
    let c = t;
    while (c.tag === 'App') {
        args.push(c.arg);
        c = c.fn;
    }
    return [c, args.reverse()];
};
exports.flattenApp = flattenApp;
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
const isSimple = (t) => t.tag === 'Var' || t.tag === 'Global' || t.tag === 'Proj' || t.tag === 'Bool';
const showS = (t) => showP(!isSimple(t), t);
const showProjType = (p) => {
    if (p.tag === 'PProj')
        return p.proj === 'fst' ? '_1' : '_2';
    if (p.tag === 'PIndex')
        return `${p.index}`;
    return p;
};
const show = (t) => {
    if (t.tag === 'Var')
        return `'${t.index}`;
    if (t.tag === 'Global')
        return `${t.name}`;
    if (t.tag === 'Bool')
        return t.value ? '1' : '0';
    if (t.tag === 'Abs')
        return `\\${exports.show(t.body)}`;
    if (t.tag === 'App') {
        const [fn, args] = exports.flattenApp(t);
        return `${showS(fn)} ${args.map(a => showS(a)).join(' ')}`;
    }
    if (t.tag === 'Let')
        return `let ${showP(t.val.tag === 'Let', t.val)}; ${exports.show(t.body)}`;
    if (t.tag === 'Pair') {
        const ps = exports.flattenPair(t);
        return `(${ps.map(t => exports.show(t)).join(', ')})`;
    }
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
    }
    if (t.tag === 'ElimBool')
        return `if ${showS(t.term)} ${showS(t.ifTrue)} ${showS(t.ifFalse)}`;
    if (t.tag === 'ElimFix')
        return `rec ${showS(t.term)} ${showS(t.cas)}`;
    return t;
};
exports.show = show;
const idTerm = exports.Abs(exports.Var(0));
const erasePrim = (x) => {
    if (x === '*')
        return exports.False;
    if (x === 'False')
        return exports.False;
    if (x === 'True')
        return exports.True;
    if (x === 'ICon')
        return idTerm;
    return exports.Type;
};
exports.erasePrim = erasePrim;
const erasePrimElim = (x, scrut, cases) => {
    if (x === 'elimUnit')
        return cases[0];
    if (x === 'elimVoid')
        return scrut;
    if (x === 'elimPropEq')
        return cases[0];
    if (x === 'elimSigma') {
        if (scrut.tag === 'Pair')
            return exports.App(exports.App(cases[0], scrut.fst), scrut.snd);
        if (scrut.tag === 'Var' || scrut.tag === 'Global')
            return exports.App(exports.App(cases[0], exports.Proj(scrut, exports.PFst)), exports.Proj(scrut, exports.PSnd));
        return exports.Let(scrut, exports.App(exports.App(cases[0], exports.Proj(exports.Var(0), exports.PFst)), exports.Proj(exports.Var(0), exports.PSnd)));
    }
    if (x === 'elimBool') {
        if (scrut.tag === 'Bool')
            return scrut.value ? cases[0] : cases[1];
        return exports.ElimBool(scrut, cases[0], cases[1]);
    }
    if (x === 'elimIFix')
        return exports.ElimFix(scrut, cases[0]);
    return x;
};
exports.erasePrimElim = erasePrimElim;

},{}],6:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.show = exports.normalize = exports.quote = exports.evaluate = exports.velimfix = exports.velimbool = exports.vproj = exports.vapp = exports.vinst = exports.VVar = exports.VBool = exports.VPair = exports.VAbs = exports.VNe = exports.EElimFix = exports.EElimBool = exports.EProj = exports.EApp = void 0;
const erased_1 = require("./erased");
const globals_1 = require("./globals");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const EApp = (arg) => ({ tag: 'EApp', arg });
exports.EApp = EApp;
const EProj = (proj) => ({ tag: 'EProj', proj });
exports.EProj = EProj;
const EElimBool = (ifTrue, ifFalse) => ({ tag: 'EElimBool', ifTrue, ifFalse });
exports.EElimBool = EElimBool;
const EElimFix = (cas) => ({ tag: 'EElimFix', cas });
exports.EElimFix = EElimFix;
const VNe = (head, spine) => ({ tag: 'VNe', head, spine });
exports.VNe = VNe;
const VAbs = (clos) => ({ tag: 'VAbs', clos });
exports.VAbs = VAbs;
const VPair = (fst, snd) => ({ tag: 'VPair', fst, snd });
exports.VPair = VPair;
const VBool = (value) => ({ tag: 'VBool', value });
exports.VBool = VBool;
const VVar = (level, spine = List_1.nil) => exports.VNe(level, spine);
exports.VVar = VVar;
const vinst = (val, arg) => val.clos(arg);
exports.vinst = vinst;
const vapp = (left, right) => {
    if (left.tag === 'VAbs')
        return exports.vinst(left, right);
    if (left.tag === 'VNe')
        return exports.VNe(left.head, List_1.cons(exports.EApp(right), left.spine));
    return utils_1.impossible(`vapp: ${left.tag}`);
};
exports.vapp = vapp;
const vproj = (scrut, proj) => {
    if (scrut.tag === 'VPair') {
        if (proj.tag === 'PProj')
            return proj.proj === 'fst' ? scrut.fst : scrut.snd;
        if (proj.tag === 'PIndex') {
            if (proj.index === 0)
                return scrut.fst;
            return exports.vproj(scrut.snd, erased_1.PIndex(proj.index - 1));
        }
        return proj;
    }
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine));
    return utils_1.impossible(`vproj: ${scrut.tag}`);
};
exports.vproj = vproj;
const velimbool = (scrut, ifTrue, ifFalse) => {
    if (scrut.tag === 'VBool')
        return scrut.value ? ifTrue : ifFalse;
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EElimBool(ifTrue, ifFalse), scrut.spine));
    return utils_1.impossible(`velimbool: ${scrut.tag}`);
};
exports.velimbool = velimbool;
const velimfix = (scrut, cas) => {
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EElimFix(cas), scrut.spine));
    return exports.vapp(exports.vapp(cas, exports.VAbs(v => exports.velimfix(v, cas))), scrut);
};
exports.velimfix = velimfix;
const evaluate = (t, vs) => {
    if (t.tag === 'Abs')
        return exports.VAbs(v => exports.evaluate(t.body, List_1.cons(v, vs)));
    if (t.tag === 'Var') {
        const v = vs.index(t.index) || utils_1.impossible(`evaluate: var ${t.index} has no value`);
        return v;
    }
    if (t.tag === 'Global') {
        const e = globals_1.globalLoad(t.name);
        if (!e)
            return utils_1.terr(`failed to load global ${t.name}`);
        return e.erval;
    }
    if (t.tag === 'App')
        return exports.vapp(exports.evaluate(t.fn, vs), exports.evaluate(t.arg, vs));
    if (t.tag === 'Let')
        return exports.evaluate(t.body, List_1.cons(exports.evaluate(t.val, vs), vs));
    if (t.tag === 'Pair')
        return exports.VPair(exports.evaluate(t.fst, vs), exports.evaluate(t.snd, vs));
    if (t.tag === 'Proj')
        return exports.vproj(exports.evaluate(t.term, vs), t.proj);
    if (t.tag === 'Bool')
        return exports.VBool(t.value);
    if (t.tag === 'ElimBool')
        return exports.velimbool(exports.evaluate(t.term, vs), exports.evaluate(t.ifTrue, vs), exports.evaluate(t.ifFalse, vs));
    if (t.tag === 'ElimFix')
        return exports.velimfix(exports.evaluate(t.term, vs), exports.evaluate(t.cas, vs));
    return t;
};
exports.evaluate = evaluate;
const quoteHead = (h, k) => erased_1.Var(k - (h + 1));
const quoteElim = (t, e, k) => {
    if (e.tag === 'EApp')
        return erased_1.App(t, exports.quote(e.arg, k));
    if (e.tag === 'EProj')
        return erased_1.Proj(t, e.proj);
    if (e.tag === 'EElimBool')
        return erased_1.ElimBool(t, exports.quote(e.ifTrue, k), exports.quote(e.ifFalse, k));
    if (e.tag === 'EElimFix')
        return erased_1.ElimFix(t, exports.quote(e.cas, k));
    return e;
};
const quote = (v, k) => {
    if (v.tag === 'VNe')
        return v.spine.foldr((x, y) => quoteElim(y, x, k), quoteHead(v.head, k));
    if (v.tag === 'VAbs')
        return erased_1.Abs(exports.quote(exports.vinst(v, exports.VVar(k)), k + 1));
    if (v.tag === 'VPair')
        return erased_1.Pair(exports.quote(v.fst, k), exports.quote(v.snd, k));
    if (v.tag === 'VBool')
        return erased_1.Bool(v.value);
    return v;
};
exports.quote = quote;
const normalize = (t, k = 0, vs = List_1.nil) => exports.quote(exports.evaluate(t, vs), k);
exports.normalize = normalize;
const show = (v, k = 0) => erased_1.show(exports.quote(v, k));
exports.show = show;

},{"./erased":5,"./globals":7,"./utils/List":18,"./utils/utils":19}],7:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.preload = exports.globalLoad = exports.globalSet = exports.globalGet = exports.globalReset = void 0;
const elaboration_1 = require("./elaboration");
const local_1 = require("./local");
const parser_1 = require("./parser");
const surface_1 = require("./surface");
const typecheck_1 = require("./typecheck");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const EV = require("./erasedvalues");
let globals = {};
const globalReset = () => {
    globals = {};
};
exports.globalReset = globalReset;
const globalGet = (x) => globals[x] || null;
exports.globalGet = globalGet;
const globalSet = (x, val, type, erval) => {
    globals[x] = { val, type, erval };
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
    const [, er] = typecheck_1.typecheck(tm);
    exports.globalSet(x, values_1.evaluate(tm, List_1.nil), values_1.evaluate(ty, List_1.nil), EV.evaluate(er, List_1.nil));
    return exports.globalGet(x);
};
exports.globalLoad = globalLoad;
const preload = (t, local = local_1.Local.empty()) => {
    const vs = surface_1.freeVars(t);
    const localVars = local.nsSurface.toArray();
    utils_1.removeAll(vs, localVars);
    return Promise.all(vs.map(async (v) => {
        const sc = await utils_1.loadFile(`lib/${v}`);
        const e = parser_1.parse(sc);
        const [tm, ty] = elaboration_1.elaborate(e);
        const [, er] = typecheck_1.typecheck(tm);
        exports.globalSet(v, values_1.evaluate(tm, List_1.nil), values_1.evaluate(ty, List_1.nil), EV.evaluate(er, List_1.nil));
        return exports.globalGet(v) || utils_1.impossible(`preload failed, unable to get ${v}`);
    }));
};
exports.preload = preload;

},{"./elaboration":4,"./erasedvalues":6,"./local":8,"./parser":11,"./surface":14,"./typecheck":15,"./utils/List":18,"./utils/utils":19,"./values":20}],8:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.showVal = exports.showValCore = exports.Local = exports.indexEnvT = exports.EntryT = void 0;
const mode_1 = require("./mode");
const usage_1 = require("./usage");
const List_1 = require("./utils/List");
const values_1 = require("./values");
const S = require("./surface");
const EntryT = (type, usage, mode, bound, inserted) => ({ type, bound, mode, usage, inserted });
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
        if (l.head.usage === usage_1.zero)
            erased++;
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
    undo() {
        if (this.level === 0)
            return this;
        return new Local(this.usage, this.level - 1, this.ns.tail, this.nsSurface.tail, this.ts.tail, this.vs.tail);
    }
    inType() {
        return new Local(usage_1.zero, this.level, this.ns, this.nsSurface, this.ts, this.vs);
    }
}
exports.Local = Local;
const showValCore = (local, val) => values_1.show(val, local.level);
exports.showValCore = showValCore;
const showVal = (local, val) => S.showVal(val, local.level, local.ns);
exports.showVal = showVal;

},{"./mode":9,"./surface":14,"./usage":16,"./utils/List":18,"./values":20}],9:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.eqMode = exports.Impl = exports.Expl = void 0;
;
exports.Expl = { tag: 'Expl' };
;
exports.Impl = { tag: 'Impl' };
const eqMode = (a, b) => a.tag === b.tag;
exports.eqMode = eqMode;

},{}],10:[function(require,module,exports){
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

},{}],11:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parse = void 0;
const config_1 = require("./config");
const mode_1 = require("./mode");
const prims_1 = require("./prims");
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
const SYM2 = ['->', '**', '!=', '||'];
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
const usage = (t) => {
    if (!t)
        return null;
    if (t.tag === 'Name' && usage_1.usages.includes(t.name))
        return t.name;
    if (t.tag === 'Num' && usage_1.usages.includes(t.num))
        return t.num;
    return null;
};
const lambdaParams = (t) => {
    if (t.tag === 'Name')
        return [[usage_1.many, t.name, mode_1.Expl, null]];
    if (t.tag === 'List') {
        const impl = t.bracket === '{' ? mode_1.Impl : mode_1.Expl;
        const a = t.list;
        if (a.length === 0)
            return [[usage_1.many, '_', impl, surface_1.UnitType]];
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
        const ty = exprs(rest, '(');
        return isNames(ns).map(x => [u, x, impl, ty]);
    }
    return utils_1.serr(`invalid lambda param`);
};
const piParams = (t) => {
    if (t.tag === 'Name')
        return [[usage_1.many, '_', mode_1.Expl, expr(t)[0]]];
    if (t.tag === 'List') {
        const impl = t.bracket === '{' ? mode_1.Impl : mode_1.Expl;
        const a = t.list;
        if (a.length === 0)
            return [[usage_1.many, '_', impl, surface_1.UnitType]];
        const i = a.findIndex(v => v.tag === 'Name' && v.name === ':');
        if (i === -1)
            return [[usage_1.many, '_', impl, expr(t)[0]]];
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
        const ty = exprs(rest, '(');
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
const expr = (t) => {
    if (t.tag === 'List')
        return [exprs(t.list, '('), t.bracket === '{'];
    if (t.tag === 'Str') {
        const s = codepoints(t.str).reverse();
        const Cons = surface_1.Var('Cons');
        const Nil = surface_1.Var('Nil');
        return [s.reduce((t, n) => surface_1.App(surface_1.App(Cons, mode_1.Expl, numToNat(n, `codepoint: ${n}`)), mode_1.Expl, t), Nil), false];
    }
    if (t.tag === 'Name') {
        const x = t.name;
        if (prims_1.isPrimElimName(x))
            return utils_1.serr(`prim elim ${x} used without arguments`);
        if (x === 'Refl')
            return [surface_1.Refl(null, null), false];
        if (x === '*')
            return [surface_1.Unit, false];
        if (x[0] === '_')
            return [surface_1.Hole(x.slice(1)), false];
        if (/[a-z]/i.test(x[0])) {
            if (x.indexOf('.') >= 0) {
                const parts = x.split('.');
                const first = parts[0];
                const ps = projs(parts.slice(1).join('.'));
                return [ps.reduce((t, p) => surface_1.Proj(t, p), surface_1.Var(first)), false];
            }
            else
                return [surface_1.Var(x), false];
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
const exprs = (ts, br, fromRepl = false) => {
    if (br === '{')
        return utils_1.serr(`{} cannot be used here`);
    if (ts.length === 0)
        return surface_1.UnitType;
    if (ts.length === 1)
        return expr(ts[0])[0];
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
            return surface_1.Let(u, name, ty || null, val, null);
        }
        const body = exprs(ts.slice(i + 1), '(');
        return surface_1.Let(u, name, ty || null, val, body);
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
    if (prims_1.PrimElimNames.some(x => isName(ts[0], x))) {
        const name = ts[0].tag === 'Name' ? ts[0].name : utils_1.serr(`not a name: ${ts[0].tag}`);
        let j = 1;
        let u = usage(ts[1]);
        if (u) {
            j = 2;
        }
        else {
            u = usage_1.many;
        }
        if (!ts[j])
            return utils_1.serr(`${name}: not enough arguments`);
        const [motive, impl] = expr(ts[j]);
        if (impl)
            return utils_1.serr(`${name} motive cannot be implicit`);
        if (!ts[j + 1])
            return utils_1.serr(`${name}: not enough arguments`);
        const [scrut, impl2] = expr(ts[j + 1]);
        if (impl2)
            return utils_1.serr(`${name} scrutinee cannot be implicit`);
        const cases = ts.slice(j + 2).map(t => {
            const [e, impl] = expr(t);
            if (impl)
                return utils_1.serr(`${name} case cannot be implicit`);
            return e;
        });
        return surface_1.PrimElim(name, u, motive, scrut, cases);
    }
    const i = ts.findIndex(x => isName(x, ':'));
    if (i >= 0) {
        const a = ts.slice(0, i);
        const b = ts.slice(i + 1);
        return surface_1.Ann(exprs(a, '('), exprs(b, '('));
    }
    const j = ts.findIndex(x => isName(x, '->'));
    if (j >= 0) {
        const s = splitTokens(ts, x => isName(x, '->'));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with ->`);
        const args = s.slice(0, -1)
            .map(p => p.length === 1 ? piParams(p[0]) : [[usage_1.many, '_', mode_1.Expl, exprs(p, '(')]])
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
    if (isName(ts[0], 'Refl')) {
        if (ts.length === 1)
            return surface_1.Refl(null, null);
        if (ts.length === 2) {
            if (ts[1].tag !== 'List' || ts[1].bracket !== '{')
                return utils_1.serr(`invalid Refl`);
            const type = exprs(ts[1].list, '(');
            return surface_1.Refl(type, null);
        }
        if (ts.length === 3) {
            if (ts[1].tag !== 'List' || ts[1].bracket !== '{')
                return utils_1.serr(`invalid Refl`);
            if (ts[2].tag !== 'List' || ts[2].bracket !== '{')
                return utils_1.serr(`invalid Refl`);
            const type = exprs(ts[1].list, '(');
            const val = exprs(ts[2].list, '(');
            return surface_1.Refl(type, val);
        }
        return utils_1.serr(`invalid Refl`);
    }
    const jse = ts.findIndex(x => isName(x, '||'));
    if (jse >= 0) {
        const s = splitTokens(ts, x => isName(x, '||'));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with ||`);
        const args = s.slice(0, -1)
            .map(p => p.length === 1 ? piParams(p[0]) : [[usage_1.many, '_', mode_1.Expl, exprs(p, '(')]])
            .reduce((x, y) => x.concat(y), []);
        const body = exprs(s[s.length - 1], '(');
        return args.reduceRight((x, [u, name, mode, ty]) => {
            if (mode.tag !== 'Expl')
                return utils_1.serr(`sigma cannot be implicit`);
            return surface_1.Sigma(u, true, name, ty, x);
        }, body);
    }
    const js = ts.findIndex(x => isName(x, '**'));
    if (js >= 0) {
        const s = splitTokens(ts, x => isName(x, '**'));
        if (s.length < 2)
            return utils_1.serr(`parsing failed with **`);
        const args = s.slice(0, -1)
            .map(p => p.length === 1 ? piParams(p[0]) : [[usage_1.many, '_', mode_1.Expl, exprs(p, '(')]])
            .reduce((x, y) => x.concat(y), []);
        const body = exprs(s[s.length - 1], '(');
        return args.reduceRight((x, [u, name, mode, ty]) => {
            if (mode.tag !== 'Expl')
                return utils_1.serr(`sigma cannot be implicit`);
            return surface_1.Sigma(u, false, name, ty, x);
        }, body);
    }
    const jq = ts.findIndex(x => isName(x, '='));
    if (jq >= 0) {
        if (ts.length < 3)
            return utils_1.serr(`invalid equality`);
        let rest = ts;
        let type = null;
        if (ts[0].tag === 'List' && ts[0].bracket === '{') {
            rest = ts.slice(1);
            type = exprs(ts[0].list, '(');
        }
        const spl = splitTokens(rest, t => isName(t, '='));
        if (spl.length !== 2)
            return utils_1.serr(`invalid equality`);
        const left = exprs(spl[0], '(');
        const right = exprs(spl[1], '(');
        return surface_1.PropEq(type, left, right);
    }
    const jnq = ts.findIndex(x => isName(x, '!='));
    if (jnq >= 0) {
        if (ts.length < 3)
            return utils_1.serr(`invalid inequality`);
        let rest = ts;
        let type = null;
        if (ts[0].tag === 'List' && ts[0].bracket === '{') {
            rest = ts.slice(1);
            type = exprs(ts[0].list, '(');
        }
        const spl = splitTokens(rest, t => isName(t, '!='));
        if (spl.length !== 2)
            return utils_1.serr(`invalid inequality`);
        const left = exprs(spl[0], '(');
        const right = exprs(spl[1], '(');
        return surface_1.Pi(usage_1.many, mode_1.Expl, '_', surface_1.PropEq(type, left, right), surface_1.Var('Void'));
    }
    if (isName(ts[0], 'sig')) {
        if (ts.length !== 2)
            return utils_1.serr(`invalid signature (1)`);
        const b = ts[1];
        if (b.tag !== 'List' || b.bracket !== '{')
            return utils_1.serr(`invalid signature (2)`);
        const bs = b.list;
        const spl = splitTokens(bs, t => t.tag === 'Name' && t.name === 'def', true);
        const entries = [];
        for (let i = 0; i < spl.length; i++) {
            const c = spl[i];
            if (c.length === 0)
                continue;
            if (c[0].tag !== 'Name')
                return utils_1.serr(`invalid signature, definition does not start with def`);
            if (c[0].name !== 'def')
                return utils_1.serr(`invalid signature, definition does not start with def`);
            let x = c[1];
            let j = 2;
            const pu = usage(x);
            let u = usage_1.many;
            if (pu !== null) {
                u = pu;
                x = c[2];
                j = 3;
            }
            let name = '';
            if (x.tag === 'Name') {
                name = x.name;
            }
            else
                return utils_1.serr(`invalid name for signature def: ${x.tag}`);
            if (name.length === 0)
                return utils_1.serr(`signature definition with empty name`);
            const sym = c[j];
            if (!sym) {
                entries.push(surface_1.SigEntry(u, name, null));
                continue;
            }
            if (sym.tag !== 'Name')
                return utils_1.serr(`signature def: after name should be :`);
            if (sym.name === ':') {
                const type = exprs(c.slice(j + 1), '(');
                entries.push(surface_1.SigEntry(u, name, type));
                continue;
            }
            else
                return utils_1.serr(`def: : or = expected but got ${sym.name}`);
        }
        return surface_1.Signature(entries);
    }
    if (isName(ts[0], 'mod')) {
        if (ts.length !== 2)
            return utils_1.serr(`invalid module (1)`);
        const b = ts[1];
        if (b.tag !== 'List' || b.bracket !== '{')
            return utils_1.serr(`invalid module (2)`);
        const bs = b.list;
        const spl = splitTokens(bs, t => t.tag === 'Name' && ['def', 'private'].includes(t.name), true);
        const entries = [];
        let private_flag = false;
        for (let i = 0; i < spl.length; i++) {
            const c = spl[i];
            if (c.length === 0)
                continue;
            if (c[0].tag !== 'Name')
                return utils_1.serr(`invalid module, definition does not start with def or private`);
            if (c[0].name !== 'def' && c[0].name !== 'private')
                return utils_1.serr(`invalid module, definition does not start with def or private`);
            if (c[0].name === 'private') {
                if (c.length > 1)
                    return utils_1.serr(`something went wrong in parsing module private definition`);
                private_flag = true;
                continue;
            }
            let private_ = false;
            if (c[0].name === 'def' && private_flag) {
                private_flag = false;
                private_ = true;
            }
            let x = c[1];
            let j = 2;
            const pu = usage(x);
            let u = usage_1.many;
            if (pu !== null) {
                u = pu;
                x = c[2];
                j = 3;
            }
            let name = '';
            if (x.tag === 'Name') {
                name = x.name;
            }
            else
                return utils_1.serr(`invalid name for module def`);
            if (name.length === 0)
                return utils_1.serr(`module definition with empty name`);
            const sym = c[j];
            if (sym.tag !== 'Name')
                return utils_1.serr(`module def: after name should be : or =`);
            if (sym.name === '=') {
                const val = exprs(c.slice(j + 1), '(');
                entries.push(surface_1.ModEntry(private_, u, name, null, val));
                continue;
            }
            else if (sym.name === ':') {
                const tyts = [];
                j++;
                for (; j < c.length; j++) {
                    const v = c[j];
                    if (v.tag === 'Name' && v.name === '=')
                        break;
                    else
                        tyts.push(v);
                }
                const type = exprs(tyts, '(');
                const val = exprs(c.slice(j + 1), '(');
                entries.push(surface_1.ModEntry(private_, u, name, type, val));
                continue;
            }
            else
                return utils_1.serr(`def: : or = expected but got ${sym.name}`);
        }
        return surface_1.Module(entries);
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

},{"./config":1,"./mode":9,"./prims":12,"./surface":14,"./usage":16,"./utils/utils":19}],12:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.synthPrimElim = exports.synthPrim = exports.primElim = exports.isPrimElimName = exports.isPrimName = exports.PrimElimNames = exports.PrimNames = void 0;
const mode_1 = require("./mode");
const usage_1 = require("./usage");
const Lazy_1 = require("./utils/Lazy");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
exports.PrimNames = ['Type', 'Void', '()', '*', 'Bool', 'True', 'False', 'IFix', 'ICon'];
exports.PrimElimNames = ['elimSigma', 'elimPropEq', 'elimVoid', 'elimUnit', 'elimBool', 'elimIFix'];
const isPrimName = (name) => exports.PrimNames.includes(name);
exports.isPrimName = isPrimName;
const isPrimElimName = (name) => exports.PrimElimNames.includes(name);
exports.isPrimElimName = isPrimElimName;
// I -> Type
const ifixType = (I) => values_1.VPi(usage_1.many, mode_1.Expl, '_', I, _ => values_1.VType);
const primTypes = utils_1.mapObj({
    Type: () => values_1.VType,
    Void: () => values_1.VType,
    '()': () => values_1.VType,
    '*': () => values_1.VUnitType,
    Bool: () => values_1.VType,
    True: () => values_1.VBool,
    False: () => values_1.VBool,
    // IFix : (I : Type) -> ((I -> Type) -> (I -> Type)) -> I -> Type
    IFix: () => values_1.VPi(usage_1.many, mode_1.Expl, 'I', values_1.VType, I => values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.VPi(usage_1.many, mode_1.Expl, '_', ifixType(I), _ => ifixType(I)), _ => ifixType(I))),
    // ICon : (0 I : Type) -> (0 F : (I -> Type) -> (I -> Type)) -> (0 i : I) -> F (IFix I F) i -> IFix I F i
    ICon: () => values_1.VPi(usage_1.zero, mode_1.Expl, 'I', values_1.VType, I => values_1.VPi(usage_1.zero, mode_1.Expl, 'F', values_1.VPi(usage_1.many, mode_1.Expl, '_', ifixType(I), _ => ifixType(I)), F => values_1.VPi(usage_1.zero, mode_1.Expl, 'i', I, i => values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.vapp(values_1.vapp(F, mode_1.Expl, values_1.vapp(values_1.vapp(values_1.VIFix, mode_1.Expl, I), mode_1.Expl, F)), mode_1.Expl, i), _ => values_1.vapp(values_1.vapp(values_1.vapp(values_1.VIFix, mode_1.Expl, I), mode_1.Expl, F), mode_1.Expl, i))))),
}, Lazy_1.Lazy.from);
const primElim = (name, usage, motive, scrut, cases) => {
    if (name === 'elimUnit') {
        if (values_1.isVUnit(scrut))
            return cases[0];
    }
    if (name === 'elimBool') {
        if (values_1.isVTrue(scrut))
            return cases[0];
        if (values_1.isVFalse(scrut))
            return cases[1];
    }
    if (name === 'elimSigma') {
        if (scrut.tag === 'VPair')
            return values_1.vapp(values_1.vapp(cases[0], mode_1.Expl, scrut.fst), mode_1.Expl, scrut.snd);
    }
    if (name === 'elimPropEq') {
        if (scrut.tag === 'VRefl')
            return values_1.vapp(cases[0], mode_1.Expl, scrut.val);
    }
    if (name === 'elimIFix') {
        // elimIFix q P (ICon I F i x) c ~> c (\(0 i : I) (v : IFix I F i). elimIFix q P v) i x
        if (values_1.isVICon(scrut) && scrut.spine.length() === 4) {
            const [I, F, i, x] = scrut.spine.toMappedArray(e => e.arg).reverse();
            const rec = values_1.VAbs(usage_1.zero, mode_1.Expl, 'i', I, _ => values_1.VAbs(usage_1.many, mode_1.Expl, 'v', values_1.vapp(values_1.vapp(values_1.vapp(values_1.VIFix, mode_1.Expl, I), mode_1.Expl, F), mode_1.Expl, i), v => values_1.vprimelim(name, usage, motive, v, cases)));
            return values_1.vapp(values_1.vapp(values_1.vapp(cases[0], mode_1.Expl, rec), mode_1.Expl, i), mode_1.Expl, x);
        }
    }
    return null;
};
exports.primElim = primElim;
const primElimTypes = {
    elimVoid: [0, ty_ => {
            const ty = values_1.force(ty_);
            if (ty.tag !== 'VNe' || ty.head.tag !== 'HPrim' || ty.head.name !== 'Void')
                return utils_1.terr(`expected a Void in elimVoid`);
            return [
                values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.VVoid, _ => values_1.VType),
                (vmotive, vscrut) => [[], values_1.vapp(vmotive, mode_1.Expl, vscrut)],
            ];
        }],
    elimUnit: [1, ty_ => {
            const ty = values_1.force(ty_);
            if (ty.tag !== 'VNe' || ty.head.tag !== 'HPrim' || ty.head.name !== '()')
                return utils_1.terr(`expected a () in elimUnit`);
            return [
                values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.VUnitType, _ => values_1.VType),
                (vmotive, vscrut) => [[values_1.vapp(vmotive, mode_1.Expl, values_1.VUnit)], values_1.vapp(vmotive, mode_1.Expl, vscrut)],
            ];
        }],
    elimBool: [2, ty_ => {
            const ty = values_1.force(ty_);
            if (ty.tag !== 'VNe' || ty.head.tag !== 'HPrim' || ty.head.name !== 'Bool')
                return utils_1.terr(`expected a Bool in elimBool`);
            return [
                values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.VBool, _ => values_1.VType),
                (vmotive, vscrut) => [[values_1.vapp(vmotive, mode_1.Expl, values_1.VTrue), values_1.vapp(vmotive, mode_1.Expl, values_1.VFalse)], values_1.vapp(vmotive, mode_1.Expl, vscrut)],
            ];
        }],
    elimSigma: [1, (sigma_, usage) => {
            const sigma = values_1.force(sigma_);
            if (sigma.tag !== 'VSigma')
                return utils_1.terr(`not a sigma type in elimSigma`);
            if (sigma.exclusive)
                return utils_1.terr(`cannot call elimSigma on exclusive sigma`);
            return [
                values_1.VPi(usage_1.many, mode_1.Expl, '_', sigma_, _ => values_1.VType),
                (vmotive, vscrut) => [
                    [values_1.VPi(usage_1.multiply(usage, sigma.usage), mode_1.Expl, 'x', sigma.type, x => values_1.VPi(usage, mode_1.Expl, 'y', values_1.vinst(sigma, x), y => values_1.vapp(vmotive, mode_1.Expl, values_1.VPair(x, y, sigma_))))],
                    values_1.vapp(vmotive, mode_1.Expl, vscrut),
                ],
            ];
        }],
    elimPropEq: [1, eq_ => {
            const eq = values_1.force(eq_);
            if (eq.tag !== 'VPropEq')
                return utils_1.terr(`not a equality type in elimPropEq`);
            const A = eq.type;
            return [
                values_1.VPi(usage_1.many, mode_1.Expl, 'x', A, x => values_1.VPi(usage_1.many, mode_1.Expl, 'y', A, y => values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.VPropEq(A, x, y), _ => values_1.VType))),
                (vmotive, vscrut) => [
                    [values_1.VPi(usage_1.zero, mode_1.Expl, 'x', A, x => values_1.vapp(values_1.vapp(values_1.vapp(vmotive, mode_1.Expl, x), mode_1.Expl, x), mode_1.Expl, values_1.VRefl(A, x)))],
                    values_1.vapp(values_1.vapp(values_1.vapp(vmotive, mode_1.Expl, eq.left), mode_1.Expl, eq.right), mode_1.Expl, vscrut),
                ],
            ];
        }],
    elimIFix: [1, (fix_, usage) => {
            const fix = values_1.force(fix_);
            if (!(fix.tag === 'VNe' && fix.head.tag === 'HPrim' && fix.head.name === 'IFix' && fix.spine.length() === 3))
                return utils_1.terr(`not a IFix type in elimIFix`);
            const [I, F, i] = fix.spine.toMappedArray(e => e.arg).reverse();
            return [
                // (i : I) -> IFix I F i -> Type
                values_1.VPi(usage_1.many, mode_1.Expl, 'i', I, i => values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.vapp(values_1.vapp(values_1.vapp(values_1.VIFix, mode_1.Expl, I), mode_1.Expl, F), mode_1.Expl, i), _ => values_1.VType)),
                (vmotive, vscrut) => [
                    // ((0 i : I) -> (x : IFix I F i) -> P i x) -> (0 i : I) -> (q x : F (IFix I F) i) -> P i (ICon I F i x)
                    [
                        values_1.VPi(usage_1.many, mode_1.Expl, '_', values_1.VPi(usage_1.zero, mode_1.Expl, 'i', I, i => values_1.VPi(usage_1.many, mode_1.Expl, 'x', values_1.vapp(values_1.vapp(values_1.vapp(values_1.VIFix, mode_1.Expl, I), mode_1.Expl, F), mode_1.Expl, i), x => values_1.vapp(values_1.vapp(vmotive, mode_1.Expl, i), mode_1.Expl, x))), _ => values_1.VPi(usage_1.zero, mode_1.Expl, 'i', I, i => values_1.VPi(usage, mode_1.Expl, 'x', values_1.vapp(values_1.vapp(F, mode_1.Expl, values_1.vapp(values_1.vapp(values_1.VIFix, mode_1.Expl, I), mode_1.Expl, F)), mode_1.Expl, i), x => values_1.vapp(values_1.vapp(vmotive, mode_1.Expl, i), mode_1.Expl, values_1.vapp(values_1.vapp(values_1.vapp(values_1.vapp(values_1.VICon, mode_1.Expl, I), mode_1.Expl, F), mode_1.Expl, i), mode_1.Expl, x))))),
                    ],
                    values_1.vapp(values_1.vapp(vmotive, mode_1.Expl, i), mode_1.Expl, vscrut),
                ],
            ];
        }],
};
const synthPrim = (name) => primTypes[name].get();
exports.synthPrim = synthPrim;
const synthPrimElim = (name) => primElimTypes[name];
exports.synthPrimElim = synthPrimElim;

},{"./mode":9,"./usage":16,"./utils/Lazy":17,"./utils/utils":19,"./values":20}],13:[function(require,module,exports){
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
const erased_1 = require("./erased");
const EV = require("./erasedvalues");
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
let doPreload = true;
let showFullNorm = false;
let showErasure = true;
let local = local_1.Local.empty();
let ervs = List_1.nil;
const initREPL = () => {
    showStackTrace = false;
    showFullNorm = false;
    doPreload = true;
    showErasure = true;
    local = local_1.Local.empty();
    ervs = List_1.nil;
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
        if (s === ':defs') {
            const defs = [];
            for (let i = local.level - 1; i >= 0; i--) {
                const x = local.ns.index(i);
                const entry = local.ts.index(i);
                const u = entry.usage;
                const t = values_1.quote(entry.type, local.level);
                const v = values_1.quote(local.vs.index(i), local.level);
                defs.push(`${u === '*' ? '' : `${u} `}${x} : ${surface_1.showCore(t, local.ns)} = ${surface_1.showCore(v, local.ns)}`);
            }
            return cb(defs.join('\n'));
        }
        if (s === ':clear') {
            local = local_1.Local.empty();
            ervs = List_1.nil;
            return cb(`cleared definitions`);
        }
        if (s === ':undoDef') {
            if (local.level > 0) {
                const name = local.ns.head;
                local = local.undo();
                const usage = local.ts.head;
                if (usage.usage !== usage_1.zero)
                    ervs = ervs.tail;
                return cb(`removed definition ${name}`);
            }
            cb(`no def to undo`);
        }
        if (s.startsWith(':load')) {
            const name = `lib/${s.slice(5).trim()}`;
            utils_1.loadFile(name)
                .then(sc => parser_1.parse(sc))
                .then(e => doPreload ? globals_1.preload(e, local).then(() => e) : e)
                .then(e => {
                const [tm, ty] = elaboration_1.elaborate(e);
                const [, er] = typecheck_1.typecheck(tm);
                globals_1.globalSet(name, values_1.evaluate(tm, List_1.nil), values_1.evaluate(ty, List_1.nil), EV.evaluate(er, List_1.nil));
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
            const [eterm, etype] = elaboration_1.elaborate(term, local);
            config_1.log(() => C.show(eterm));
            config_1.log(() => surface_1.showCore(eterm, local.ns));
            config_1.log(() => C.show(etype));
            config_1.log(() => surface_1.showCore(etype, local.ns));
            config_1.log(() => 'VERIFICATION');
            const [, er] = typecheck_1.typecheck(eterm, local);
            let normstr = '';
            if (!typeOnly) {
                config_1.log(() => 'NORMALIZE');
                if (showFullNorm) {
                    const norm = values_1.normalize(eterm, local.level, local.vs, true);
                    config_1.log(() => C.show(norm));
                    config_1.log(() => surface_1.showCore(norm, local.ns));
                    normstr += `\nnorm: ${surface_1.showCore(norm, local.ns)}`;
                }
                if (showErasure) {
                    const ernorm = EV.normalize(er, ervs.length(), ervs);
                    config_1.log(() => erased_1.show(ernorm));
                    normstr += `\neran: ${erased_1.show(ernorm)}`;
                }
            }
            const etermstr = surface_1.showCore(eterm, local.ns);
            if (isDef) {
                if (term.tag === 'Let') {
                    const value = values_1.evaluate(eterm, local.vs);
                    local = local.define(usage, term.name, values_1.evaluate(etype, local.vs), value);
                    if (usage !== usage_1.zero)
                        ervs = List_1.cons(EV.evaluate(er, ervs), ervs);
                }
                else if (term.tag === 'Import') {
                    let c = eterm;
                    while (c && c.tag === 'Let') {
                        local = local.define(c.usage, c.name, values_1.evaluate(c.type, local.vs), values_1.evaluate(c.val, local.vs));
                        if (c.usage !== usage_1.zero) {
                            const [, erval] = typecheck_1.typecheck(c.val, local);
                            ervs = List_1.cons(EV.evaluate(erval, ervs), ervs);
                        }
                        c = c.body;
                    }
                }
                else
                    throw new Error(`invalid definition: ${term.tag}`);
            }
            return cb(`term: ${surface_1.show(term)}\ntype: ${surface_1.showCore(etype, local.ns)}\netrm: ${etermstr}${showErasure ? `\neras: ${erased_1.show(er)}` : ''}${normstr}`);
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

},{"./config":1,"./core":3,"./elaboration":4,"./erased":5,"./erasedvalues":6,"./globals":7,"./local":8,"./parser":11,"./surface":14,"./typecheck":15,"./usage":16,"./utils/List":18,"./utils/utils":19,"./values":20}],14:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.freeVars = exports.freeVarsAll = exports.showVal = exports.showCore = exports.fromCore = exports.show = exports.flattenProj = exports.flattenPair = exports.flattenSigma = exports.flattenApp = exports.flattenAbs = exports.flattenPi = exports.PIndex = exports.PName = exports.PSnd = exports.PFst = exports.PProj = exports.Unit = exports.UnitType = exports.PrimElim = exports.Hole = exports.Refl = exports.PropEq = exports.Module = exports.ModEntry = exports.Signature = exports.SigEntry = exports.Import = exports.Proj = exports.Pair = exports.Sigma = exports.App = exports.Abs = exports.Pi = exports.Ann = exports.Let = exports.Var = void 0;
const names_1 = require("./names");
const prims_1 = require("./prims");
const usage_1 = require("./usage");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const Var = (name) => ({ tag: 'Var', name });
exports.Var = Var;
const Let = (usage, name, type, val, body) => ({ tag: 'Let', usage, name, type, val, body });
exports.Let = Let;
const Ann = (term, type) => ({ tag: 'Ann', term, type });
exports.Ann = Ann;
const Pi = (usage, mode, name, type, body) => ({ tag: 'Pi', usage, mode, name, type, body });
exports.Pi = Pi;
const Abs = (usage, mode, name, type, body) => ({ tag: 'Abs', usage, mode, name, type, body });
exports.Abs = Abs;
const App = (fn, mode, arg) => ({ tag: 'App', fn, mode, arg });
exports.App = App;
const Sigma = (usage, exclusive, name, type, body) => ({ tag: 'Sigma', usage, exclusive, name, type, body });
exports.Sigma = Sigma;
const Pair = (fst, snd) => ({ tag: 'Pair', fst, snd });
exports.Pair = Pair;
const Proj = (term, proj) => ({ tag: 'Proj', term, proj });
exports.Proj = Proj;
const Import = (term, imports, body) => ({ tag: 'Import', term, imports, body });
exports.Import = Import;
const SigEntry = (usage, name, type) => ({ usage, name, type });
exports.SigEntry = SigEntry;
const Signature = (defs) => ({ tag: 'Signature', defs });
exports.Signature = Signature;
const ModEntry = (priv, usage, name, type, val) => ({ priv, usage, name, type, val });
exports.ModEntry = ModEntry;
const Module = (defs) => ({ tag: 'Module', defs });
exports.Module = Module;
const PropEq = (type, left, right) => ({ tag: 'PropEq', type, left, right });
exports.PropEq = PropEq;
;
const Refl = (type, val) => ({ tag: 'Refl', type, val });
exports.Refl = Refl;
const Hole = (name) => ({ tag: 'Hole', name });
exports.Hole = Hole;
const PrimElim = (name, usage, motive, scrut, cases) => ({ tag: 'PrimElim', name, usage, motive, scrut, cases });
exports.PrimElim = PrimElim;
exports.UnitType = exports.Var('()');
exports.Unit = exports.Var('*');
const PProj = (proj) => ({ tag: 'PProj', proj });
exports.PProj = PProj;
exports.PFst = exports.PProj('fst');
exports.PSnd = exports.PProj('snd');
const PName = (name) => ({ tag: 'PName', name });
exports.PName = PName;
const PIndex = (index) => ({ tag: 'PIndex', index });
exports.PIndex = PIndex;
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
        params.push([c.usage, c.exclusive, c.name, c.type]);
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
const isSimple = (t) => t.tag === 'Var' || t.tag === 'Proj' || t.tag === 'Hole';
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
    if (t.tag === 'Var')
        return `${t.name}`;
    if (t.tag === 'Hole')
        return `_${t.name || ''}`;
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
    if (t.tag === 'Import')
        return `import ${showS(t.term)}${t.imports ? ` (${t.imports.join(', ')})` : ''}; ${exports.show(t.body)}`;
    if (t.tag === 'Sigma') {
        const [params, ret] = exports.flattenSigma(t);
        const ps = params.map(([u, e, x, ty]) => {
            const param = u === usage_1.many && x === '_' ? showP(ty.tag === 'Pi' || ty.tag === 'Sigma' || ty.tag === 'Let', ty) : `(${u === usage_1.many ? '' : `${u} `}${x} : ${exports.show(ty)})`;
            return `${param} ${e ? '||' : '**'} `;
        }).join('');
        return `${ps}${exports.show(ret)}`;
    }
    if (t.tag === 'Pair') {
        const ps = exports.flattenPair(t);
        return `(${ps.map(exports.show).join(', ')})`;
    }
    if (t.tag === 'Proj') {
        const [hd, ps] = exports.flattenProj(t);
        return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
    }
    if (t.tag === 'Signature')
        return `sig { ${t.defs.map(({ usage, name, type }) => `def ${usage === usage_1.many ? '' : `${usage} `}${name}${type ? ` : ${exports.show(type)}` : ''}`).join(' ')} }`;
    if (t.tag === 'Module')
        return `mod { ${t.defs.map(({ priv, usage, name, type, val }) => `${priv ? 'private ' : ''}def ${usage === usage_1.many ? '' : `${usage} `}${name}${type ? ` : ${exports.show(type)}` : ''} = ${exports.show(val)}`).join(' ')} }`;
    if (t.tag === 'PropEq')
        return `${t.type ? `{${exports.show(t.type)}} ` : ''}${exports.show(t.left)} = ${exports.show(t.right)}`;
    if (t.tag === 'Refl')
        return `Refl${t.type ? ` {${exports.show(t.type)}}` : ''}${t.val ? ` {${exports.show(t.val)}}` : ''}`;
    if (t.tag === 'PrimElim')
        return `${t.name} ${t.usage === usage_1.many ? '' : `${t.usage} `}${showS(t.motive)} ${showS(t.scrut)}${t.cases.map(c => ` ${showS(c)}`).join('')}`;
    if (t.tag === 'Ann')
        return `${exports.show(t.term)} : ${exports.show(t.type)}`;
    return t;
};
exports.show = show;
const fromCore = (t, ns = List_1.nil) => {
    if (t.tag === 'Var')
        return exports.Var(ns.index(t.index) || utils_1.impossible(`var out of scope in fromCore: ${t.index}`));
    if (t.tag === 'Global')
        return exports.Var(t.name);
    if (t.tag === 'Prim')
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
        // de-elaborate annotations
        if (t.usage === usage_1.one && t.body.tag === 'Var' && t.body.index === 0)
            return exports.Ann(exports.fromCore(t.val, ns), exports.fromCore(t.type, ns));
        const x = names_1.chooseName(t.name, ns);
        return exports.Let(t.usage, x, exports.fromCore(t.type, ns), exports.fromCore(t.val, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Sigma') {
        const x = names_1.chooseName(t.name, ns);
        return exports.Sigma(t.usage, t.exclusive, x, exports.fromCore(t.type, ns), exports.fromCore(t.body, List_1.cons(x, ns)));
    }
    if (t.tag === 'Pair')
        return exports.Pair(exports.fromCore(t.fst, ns), exports.fromCore(t.snd, ns));
    if (t.tag === 'Proj')
        return exports.Proj(exports.fromCore(t.term, ns), t.proj.tag === 'PProj' ? t.proj : t.proj.name ? exports.PName(t.proj.name) : exports.PIndex(t.proj.index));
    if (t.tag === 'PropEq')
        return exports.PropEq(exports.fromCore(t.type, ns), exports.fromCore(t.left, ns), exports.fromCore(t.right, ns));
    if (t.tag === 'Refl')
        return exports.Refl(exports.fromCore(t.type, ns), exports.fromCore(t.val, ns));
    if (t.tag === 'PrimElim')
        return exports.PrimElim(t.name, t.usage, exports.fromCore(t.motive, ns), exports.fromCore(t.scrut, ns), t.cases.map(x => exports.fromCore(x, ns)));
    return t;
};
exports.fromCore = fromCore;
const showCore = (t, ns = List_1.nil) => exports.show(exports.fromCore(t, ns));
exports.showCore = showCore;
const showVal = (v, k = 0, ns = List_1.nil) => exports.show(exports.fromCore(values_1.quote(v, k), ns));
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
    if (t.tag === 'Signature') {
        t.defs.forEach(d => { if (d.type)
            exports.freeVarsAll(d.type, a); });
        return a;
    }
    if (t.tag === 'Module') {
        t.defs.forEach(d => {
            exports.freeVarsAll(d.val, a);
            if (d.type)
                exports.freeVarsAll(d.type, a);
        });
        return a;
    }
    if (t.tag === 'PropEq') {
        exports.freeVarsAll(t.left, a);
        exports.freeVarsAll(t.right, a);
        return t.type ? exports.freeVarsAll(t.type, a) : a;
    }
    if (t.tag === 'Refl') {
        if (t.val)
            exports.freeVarsAll(t.val, a);
        return t.type ? exports.freeVarsAll(t.type, a) : a;
    }
    if (t.tag === 'PrimElim') {
        exports.freeVarsAll(t.motive, a);
        exports.freeVarsAll(t.scrut, a);
        t.cases.forEach(x => exports.freeVarsAll(x, a));
        return a;
    }
    if (t.tag === 'Ann') {
        exports.freeVarsAll(t.term, a);
        return exports.freeVarsAll(t.type, a);
    }
    return t;
};
exports.freeVarsAll = freeVarsAll;
const freeVars = (t) => {
    const vs = exports.freeVarsAll(t);
    utils_1.remove(vs, '_');
    utils_1.removeAll(vs, prims_1.PrimNames);
    utils_1.removeAll(vs, prims_1.PrimElimNames);
    return vs;
};
exports.freeVars = freeVars;

},{"./names":10,"./prims":12,"./usage":16,"./utils/List":18,"./utils/utils":19,"./values":20}],15:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.typecheck = void 0;
const config_1 = require("./config");
const conversion_1 = require("./conversion");
const core_1 = require("./core");
const globals_1 = require("./globals");
const local_1 = require("./local");
const mode_1 = require("./mode");
const prims_1 = require("./prims");
const usage_1 = require("./usage");
const utils_1 = require("./utils/utils");
const values_1 = require("./values");
const E = require("./erased");
const check = (local, tm, ty) => {
    config_1.log(() => `check ${core_1.show(tm)} : ${local_1.showValCore(local, ty)}`);
    const [ty2, u, er] = synth(local, tm);
    return utils_1.tryT(() => {
        config_1.log(() => `unify ${local_1.showValCore(local, ty2)} ~ ${local_1.showValCore(local, ty)}`);
        conversion_1.conv(local.level, ty2, ty);
        return [u, er];
    }, e => utils_1.terr(`check failed (${core_1.show(tm)}): ${local_1.showValCore(local, ty2)} ~ ${local_1.showValCore(local, ty)}: ${e}`));
};
const synth = (local, tm) => {
    config_1.log(() => `synth ${core_1.show(tm)}`);
    if (tm.tag === 'Prim')
        return [prims_1.synthPrim(tm.name), usage_1.noUses(local.level), E.erasePrim(tm.name)];
    if (tm.tag === 'Var') {
        const [entry, j, erasedNo] = local_1.indexEnvT(local.ts, tm.index) || utils_1.terr(`var out of scope ${core_1.show(tm)}`);
        const uses = usage_1.noUses(local.level).updateAt(j, _ => local.usage);
        return [entry.type, uses, E.Var(tm.index - erasedNo)];
    }
    if (tm.tag === 'Global') {
        const e = globals_1.globalLoad(tm.name);
        if (!e)
            return utils_1.terr(`undefined global or failed to load global ${tm.name}`);
        return [e.type, usage_1.noUses(local.level), E.Global(tm.name)];
    }
    if (tm.tag === 'App') {
        const [fnty, fnu, fner] = synth(local, tm.fn);
        const [rty, argu, arger, u] = synthapp(local, fnty, tm.mode, tm.arg);
        return [rty, usage_1.addUses(fnu, argu), u === usage_1.zero ? fner : E.App(fner, arger)];
    }
    if (tm.tag === 'Abs') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const [rty, u, erbody] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
        const pi = values_1.evaluate(core_1.Pi(tm.usage, tm.mode, tm.name, tm.type, values_1.quote(rty, local.level + 1)), local.vs);
        const [ux, urest] = u.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${core_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [pi, urest, tm.usage === usage_1.zero ? erbody : E.Abs(erbody)];
    }
    if (tm.tag === 'Pi') {
        const [u1] = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const [u2] = check(local.bind(usage_1.many, tm.mode, tm.name, ty), tm.body, values_1.VType);
        const [, urest] = u2.uncons();
        return [values_1.VType, usage_1.addUses(u1, urest), E.Type];
    }
    if (tm.tag === 'Let') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const [uv, erval] = check(tm.usage === usage_1.zero ? local.inType() : local, tm.val, ty);
        const v = values_1.evaluate(tm.val, local.vs);
        const [rty, ub, erbody] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
        const [ux, urest] = ub.uncons();
        if (!usage_1.sub(ux, tm.usage))
            return utils_1.terr(`usage error in ${core_1.show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
        return [rty, usage_1.addUses(usage_1.multiplyUses(ux, uv), urest), tm.usage === usage_1.zero ? erbody : E.Let(erval, erbody)];
    }
    if (tm.tag === 'Sigma') {
        const [u1] = check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const [u2] = check(local.bind(usage_1.many, mode_1.Expl, tm.name, ty), tm.body, values_1.VType);
        const [, urest] = u2.uncons();
        return [values_1.VType, usage_1.addUses(u1, urest), E.Type];
    }
    if (tm.tag === 'Pair') {
        check(local.inType(), tm.type, values_1.VType);
        const vsigma_ = values_1.evaluate(tm.type, local.vs);
        const vsigma = values_1.force(vsigma_);
        if (vsigma.tag !== 'VSigma')
            return utils_1.terr(`pair without sigma type: ${core_1.show(tm)}`);
        const [u1, erfst] = check(local, tm.fst, vsigma.type);
        const [u2, ersnd] = check(local, tm.snd, values_1.vinst(vsigma, values_1.evaluate(tm.fst, local.vs)));
        if (vsigma.exclusive)
            return [vsigma_, usage_1.lubUses(u1, u2), E.Pair(erfst, ersnd)]; // TODO: do I need to use the sigma usage?
        return [vsigma_, usage_1.addUses(usage_1.multiplyUses(vsigma.usage, u1), u2), vsigma.usage === usage_1.zero ? ersnd : E.Pair(erfst, ersnd)];
    }
    if (tm.tag === 'PrimElim') {
        if (!usage_1.sub(usage_1.one, tm.usage))
            return utils_1.terr(`usage must be 1 <= q in ${core_1.show(tm)} but got ${tm.usage}`);
        const [ty_, u1, erscrut] = synth(local, tm.scrut);
        const [amount, cont] = prims_1.synthPrimElim(tm.name);
        if (tm.cases.length !== amount)
            return utils_1.terr(`invalid case amount, expected ${amount} but got ${tm.cases.length} in ${core_1.show(tm)}`);
        try {
            const [tmotive, contcases] = cont(ty_, tm.usage);
            check(local.inType(), tm.motive, tmotive);
            const vmotive = values_1.evaluate(tm.motive, local.vs);
            const vscrut = values_1.evaluate(tm.scrut, local.vs);
            const [tycases, rty] = contcases(vmotive, vscrut);
            if (tycases.length !== amount)
                return utils_1.terr(`invalid ${tm.name}: amount does not match`);
            const usesAndEr = tycases.map((ty, i) => check(local, tm.cases[i], ty));
            const uses = usesAndEr.map(x => x[0]);
            const ercases = usesAndEr.map(x => x[1]);
            const scrutu = usage_1.multiplyUses(tm.usage, u1);
            return [rty, uses.length === 0 ? scrutu : usage_1.addUses(scrutu, usage_1.lubUsesAll(uses)), E.erasePrimElim(tm.name, erscrut, ercases)];
        }
        catch (err) {
            if (!(err instanceof TypeError))
                throw err;
            return utils_1.terr(`synth ${core_1.show(tm)} failed: ${err}`);
        }
    }
    if (tm.tag === 'Proj') {
        const [sigma_, u, erterm] = synth(local, tm.term);
        if (tm.proj.tag === 'PProj') {
            const sigma = values_1.force(sigma_);
            if (sigma.tag !== 'VSigma')
                return utils_1.terr(`not a sigma type in ${core_1.show(tm)}: ${local_1.showVal(local, sigma_)}`);
            if (local.usage === usage_1.one && (sigma.usage === usage_1.one || (sigma.usage === usage_1.zero && tm.proj.proj === 'fst')))
                return utils_1.terr(`cannot project ${core_1.show(tm)}, usage must be * or 0 with a second projection: ${local_1.showVal(local, sigma_)}`);
            const fst = sigma.name !== '_' ? core_1.PIndex(sigma.name, 0) : core_1.PFst; // TODO: is this nice?
            return [tm.proj.proj === 'fst' ? sigma.type : values_1.vinst(sigma, values_1.vproj(values_1.evaluate(tm.term, local.vs), fst)), u, sigma.usage === usage_1.zero ? erterm : E.Proj(erterm, tm.proj.proj === 'fst' ? E.PFst : E.PSnd)];
        }
        else {
            const [ty, erindex] = project(local, tm, values_1.evaluate(tm.term, local.vs), sigma_, tm.proj.index, 0);
            return [ty, u, E.Proj(erterm, E.PIndex(erindex))];
        }
    }
    if (tm.tag === 'PropEq') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        const [u1] = check(local, tm.left, ty);
        const [u2] = check(local, tm.right, ty);
        return [values_1.VType, usage_1.addUses(u1, u2), E.Type];
    }
    if (tm.tag === 'Refl') {
        check(local.inType(), tm.type, values_1.VType);
        const ty = values_1.evaluate(tm.type, local.vs);
        check(local.inType(), tm.val, ty);
        const x = values_1.evaluate(tm.val, local.vs);
        return [values_1.VPropEq(ty, x, x), usage_1.noUses(local.level), E.False];
    }
    return tm;
};
const project = (local, full, tm, ty_, index, erindex) => {
    const ty = values_1.force(ty_);
    if (ty.tag === 'VSigma') {
        if (local.usage === usage_1.one && (ty.usage === usage_1.one || (ty.usage === usage_1.zero && index === 0)))
            return utils_1.terr(`cannot project ${core_1.show(full)}, usage must be * or 0 with a second projection: ${local_1.showVal(local, ty_)}`);
        if (index === 0)
            return [ty.type, erindex];
        const fst = ty.name !== '_' ? core_1.PIndex(ty.name, 0) : core_1.PFst; // TODO: is this nice?
        return project(local, full, values_1.vproj(tm, core_1.PSnd), values_1.vinst(ty, values_1.vproj(tm, fst)), index - 1, ty.usage === usage_1.zero ? erindex : erindex + 1);
    }
    return utils_1.terr(`failed to project, ${core_1.show(full)}: ${local_1.showVal(local, ty_)}`);
};
const synthapp = (local, ty_, mode, arg) => {
    config_1.log(() => `synthapp ${local_1.showValCore(local, ty_)} @ ${core_1.show(arg)}`);
    const ty = values_1.force(ty_);
    if (ty.tag === 'VPi' && mode_1.eqMode(ty.mode, mode)) {
        const cty = ty.type;
        const [uses, er] = check(local, arg, cty);
        const v = values_1.evaluate(arg, local.vs);
        return [values_1.vinst(ty, v), usage_1.multiplyUses(ty.usage, uses), er, ty.usage];
    }
    return utils_1.terr(`not a correct pi type in synthapp: ${local_1.showValCore(local, ty)} @ ${core_1.show(arg)}`);
};
const typecheck = (t, local = local_1.Local.empty()) => {
    const [vty, , er] = synth(local, t);
    const ty = values_1.quote(vty, local.level);
    return [ty, er];
};
exports.typecheck = typecheck;

},{"./config":1,"./conversion":2,"./core":3,"./erased":5,"./globals":7,"./local":8,"./mode":9,"./prims":12,"./usage":16,"./utils/utils":19,"./values":20}],16:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.lubUsesAll = exports.lubUses = exports.multiplyUses = exports.addUses = exports.noUses = exports.lub = exports.sub = exports.multiply = exports.add = exports.many = exports.one = exports.zero = exports.usages = void 0;
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
exports.usages = ['0', '1', '*'];
exports.zero = '0';
exports.one = '1';
exports.many = '*';
const add = (a, b) => {
    if (a === exports.many || b === exports.many)
        return exports.many;
    if (a === exports.one)
        return b === exports.one ? exports.many : exports.one;
    return b;
};
exports.add = add;
const multiply = (a, b) => {
    if (a === exports.zero || b === exports.zero)
        return exports.zero;
    if (a === '1')
        return b;
    if (b === '1')
        return a;
    return exports.many;
};
exports.multiply = multiply;
const sub = (a, b) => (a === b) || ((a === exports.zero || a === exports.one) && b === exports.many);
exports.sub = sub;
const lub = (a, b) => a === b ? a : exports.many;
exports.lub = lub;
const noUses = (size) => List_1.List.range(size).map(() => exports.zero);
exports.noUses = noUses;
const guardUsesZip = (a, b) => {
    if (a.length() !== b.length())
        return utils_1.impossible(`trying zip Uses of different length`);
};
const addUses = (a, b) => { guardUsesZip(a, b); return a.zipWith(b, exports.add); };
exports.addUses = addUses;
const multiplyUses = (a, b) => b.map(x => exports.multiply(a, x));
exports.multiplyUses = multiplyUses;
const lubUses = (a, b) => { guardUsesZip(a, b); return a.zipWith(b, exports.lub); };
exports.lubUses = lubUses;
// a must not be empty
const lubUsesAll = (a) => a.reduce(exports.lubUses);
exports.lubUsesAll = lubUsesAll;

},{"./utils/List":18,"./utils/utils":19}],17:[function(require,module,exports){
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

},{}],18:[function(require,module,exports){
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

},{"./utils":19}],19:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.removeAll = exports.remove = exports.pushUniq = exports.eqArr = exports.mapObj = exports.tryTE = exports.tryT = exports.hasDuplicates = exports.range = exports.loadFileSync = exports.loadFile = exports.serr = exports.terr = exports.impossible = void 0;
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

},{"fs":22}],20:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.show = exports.normalize = exports.quote = exports.evaluate = exports.vprimelim = exports.vproj = exports.vapp = exports.force = exports.vinst = exports.isVICon = exports.isVFalse = exports.isVTrue = exports.isVUnit = exports.VICon = exports.VIFix = exports.VFalse = exports.VTrue = exports.VBool = exports.VUnit = exports.VUnitType = exports.VVoid = exports.VType = exports.VPrim = exports.VVar = exports.VRefl = exports.VPropEq = exports.VPair = exports.VSigma = exports.VPi = exports.VAbs = exports.VGlobal = exports.VNe = exports.EPrimElim = exports.EProj = exports.EApp = exports.HGlobal = exports.HPrim = exports.HVar = void 0;
const core_1 = require("./core");
const globals_1 = require("./globals");
const prims_1 = require("./prims");
const Lazy_1 = require("./utils/Lazy");
const List_1 = require("./utils/List");
const utils_1 = require("./utils/utils");
const HVar = (level) => ({ tag: 'HVar', level });
exports.HVar = HVar;
const HPrim = (name) => ({ tag: 'HPrim', name });
exports.HPrim = HPrim;
const HGlobal = (name) => ({ tag: 'HGlobal', name });
exports.HGlobal = HGlobal;
const EApp = (mode, arg) => ({ tag: 'EApp', mode, arg });
exports.EApp = EApp;
const EProj = (proj) => ({ tag: 'EProj', proj });
exports.EProj = EProj;
const EPrimElim = (name, usage, motive, cases) => ({ tag: 'EPrimElim', name, usage, motive, cases });
exports.EPrimElim = EPrimElim;
const VNe = (head, spine) => ({ tag: 'VNe', head, spine });
exports.VNe = VNe;
;
const VGlobal = (head, spine, val) => ({ tag: 'VGlobal', head, spine, val });
exports.VGlobal = VGlobal;
const VAbs = (usage, mode, name, type, clos) => ({ tag: 'VAbs', usage, mode, name, type, clos });
exports.VAbs = VAbs;
const VPi = (usage, mode, name, type, clos) => ({ tag: 'VPi', usage, mode, name, type, clos });
exports.VPi = VPi;
const VSigma = (usage, exclusive, name, type, clos) => ({ tag: 'VSigma', usage, exclusive, name, type, clos });
exports.VSigma = VSigma;
const VPair = (fst, snd, type) => ({ tag: 'VPair', fst, snd, type });
exports.VPair = VPair;
const VPropEq = (type, left, right) => ({ tag: 'VPropEq', type, left, right });
exports.VPropEq = VPropEq;
const VRefl = (type, val) => ({ tag: 'VRefl', type, val });
exports.VRefl = VRefl;
const VVar = (level, spine = List_1.nil) => exports.VNe(exports.HVar(level), spine);
exports.VVar = VVar;
const VPrim = (name, spine = List_1.nil) => exports.VNe(exports.HPrim(name), spine);
exports.VPrim = VPrim;
exports.VType = exports.VPrim('Type');
exports.VVoid = exports.VPrim('Void');
exports.VUnitType = exports.VPrim('()');
exports.VUnit = exports.VPrim('*');
exports.VBool = exports.VPrim('Bool');
exports.VTrue = exports.VPrim('True');
exports.VFalse = exports.VPrim('False');
exports.VIFix = exports.VPrim('IFix');
exports.VICon = exports.VPrim('ICon');
const isVUnit = (v) => v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === '*' && v.spine.isNil();
exports.isVUnit = isVUnit;
const isVTrue = (v) => v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === 'True' && v.spine.isNil();
exports.isVTrue = isVTrue;
const isVFalse = (v) => v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === 'False' && v.spine.isNil();
exports.isVFalse = isVFalse;
const isVICon = (v) => v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === 'ICon';
exports.isVICon = isVICon;
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
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine));
    if (scrut.tag === 'VGlobal')
        return exports.VGlobal(scrut.head, List_1.cons(exports.EProj(proj), scrut.spine), scrut.val.map(v => exports.vproj(v, proj)));
    return utils_1.impossible(`vproj: ${scrut.tag}`);
};
exports.vproj = vproj;
const vprimelim = (name, usage, motive, scrut, cases) => {
    const res = prims_1.primElim(name, usage, motive, scrut, cases);
    if (res)
        return res;
    if (scrut.tag === 'VNe')
        return exports.VNe(scrut.head, List_1.cons(exports.EPrimElim(name, usage, motive, cases), scrut.spine));
    if (scrut.tag === 'VGlobal')
        return exports.VGlobal(scrut.head, List_1.cons(exports.EPrimElim(name, usage, motive, cases), scrut.spine), scrut.val.map(v => exports.vprimelim(name, usage, motive, v, cases)));
    return utils_1.impossible(`velimbool: ${scrut.tag}`);
};
exports.vprimelim = vprimelim;
const evaluate = (t, vs, glueBefore = vs.length()) => {
    if (t.tag === 'Abs')
        return exports.VAbs(t.usage, t.mode, t.name, exports.evaluate(t.type, vs, glueBefore), v => exports.evaluate(t.body, List_1.cons(v, vs), glueBefore));
    if (t.tag === 'Pi')
        return exports.VPi(t.usage, t.mode, t.name, exports.evaluate(t.type, vs, glueBefore), v => exports.evaluate(t.body, List_1.cons(v, vs), glueBefore));
    if (t.tag === 'Var') {
        const v = vs.index(t.index) || utils_1.impossible(`evaluate: var ${t.index} has no value`);
        const l = vs.length();
        if (t.index >= l - glueBefore)
            return exports.VGlobal(exports.HVar(l - t.index - 1), List_1.nil, Lazy_1.Lazy.value(v));
        return v;
    }
    if (t.tag === 'Global')
        return exports.VGlobal(exports.HGlobal(t.name), List_1.nil, Lazy_1.Lazy.from(() => {
            const e = globals_1.globalLoad(t.name);
            if (!e)
                return utils_1.terr(`failed to load global ${t.name}`);
            return e.val;
        }));
    if (t.tag === 'Prim')
        return exports.VPrim(t.name);
    if (t.tag === 'App')
        return exports.vapp(exports.evaluate(t.fn, vs, glueBefore), t.mode, exports.evaluate(t.arg, vs, glueBefore));
    if (t.tag === 'Let')
        return exports.evaluate(t.body, List_1.cons(exports.evaluate(t.val, vs, glueBefore), vs), glueBefore);
    if (t.tag === 'Sigma')
        return exports.VSigma(t.usage, t.exclusive, t.name, exports.evaluate(t.type, vs, glueBefore), v => exports.evaluate(t.body, List_1.cons(v, vs), glueBefore));
    if (t.tag === 'Pair')
        return exports.VPair(exports.evaluate(t.fst, vs, glueBefore), exports.evaluate(t.snd, vs, glueBefore), exports.evaluate(t.type, vs, glueBefore));
    if (t.tag === 'Proj')
        return exports.vproj(exports.evaluate(t.term, vs, glueBefore), t.proj);
    if (t.tag === 'PropEq')
        return exports.VPropEq(exports.evaluate(t.type, vs, glueBefore), exports.evaluate(t.left, vs, glueBefore), exports.evaluate(t.right, vs, glueBefore));
    if (t.tag === 'Refl')
        return exports.VRefl(exports.evaluate(t.type, vs, glueBefore), exports.evaluate(t.val, vs, glueBefore));
    if (t.tag === 'PrimElim')
        return exports.vprimelim(t.name, t.usage, exports.evaluate(t.motive, vs, glueBefore), exports.evaluate(t.scrut, vs, glueBefore), t.cases.map(c => exports.evaluate(c, vs, glueBefore)));
    return t;
};
exports.evaluate = evaluate;
const quoteHead = (h, k) => {
    if (h.tag === 'HVar')
        return core_1.Var(k - (h.level + 1));
    if (h.tag === 'HPrim')
        return core_1.Prim(h.name);
    if (h.tag === 'HGlobal')
        return core_1.Global(h.name);
    return h;
};
const quoteElim = (t, e, k, full) => {
    if (e.tag === 'EApp')
        return core_1.App(t, e.mode, exports.quote(e.arg, k, full));
    if (e.tag === 'EProj')
        return core_1.Proj(t, e.proj);
    if (e.tag === 'EPrimElim')
        return core_1.PrimElim(e.name, e.usage, exports.quote(e.motive, k, full), t, e.cases.map(c => exports.quote(c, k, full)));
    return e;
};
const quote = (v, k, full = false) => {
    if (v.tag === 'VNe')
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full), quoteHead(v.head, k));
    if (v.tag === 'VGlobal') {
        if (full || v.head.tag === 'HVar' && v.head.level >= k)
            return exports.quote(v.val.get(), k, full);
        return v.spine.foldr((x, y) => quoteElim(y, x, k, full), quoteHead(v.head, k));
    }
    if (v.tag === 'VAbs')
        return core_1.Abs(v.usage, v.mode, v.name, exports.quote(v.type, k, full), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full));
    if (v.tag === 'VPi')
        return core_1.Pi(v.usage, v.mode, v.name, exports.quote(v.type, k, full), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full));
    if (v.tag === 'VSigma')
        return core_1.Sigma(v.usage, v.exclusive, v.name, exports.quote(v.type, k, full), exports.quote(exports.vinst(v, exports.VVar(k)), k + 1, full));
    if (v.tag === 'VPair')
        return core_1.Pair(exports.quote(v.fst, k, full), exports.quote(v.snd, k, full), exports.quote(v.type, k, full));
    if (v.tag === 'VPropEq')
        return core_1.PropEq(exports.quote(v.type, k, full), exports.quote(v.left, k, full), exports.quote(v.right, k, full));
    if (v.tag === 'VRefl')
        return core_1.Refl(exports.quote(v.type, k, full), exports.quote(v.val, k, full));
    return v;
};
exports.quote = quote;
const normalize = (t, k = 0, vs = List_1.nil, full = false) => exports.quote(exports.evaluate(t, vs), k, full);
exports.normalize = normalize;
const show = (v, k = 0, full = false) => core_1.show(exports.quote(v, k, full));
exports.show = show;

},{"./core":3,"./globals":7,"./prims":12,"./utils/Lazy":17,"./utils/List":18,"./utils/utils":19}],21:[function(require,module,exports){
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

},{"./repl":13}],22:[function(require,module,exports){

},{}]},{},[21]);
