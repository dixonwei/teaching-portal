/* ============================================================
   内部教学门户 · 账号 / 审批 / 权限（零依赖 Node 版）
   - 学员自助注册 → 管理员审批 → 分权限（查询 / 教学）
   - 密码 scrypt 加盐哈希；HttpOnly 会话
   运行：node server.js   （默认端口 8123）
   ============================================================ */
const http = require("http");
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");

const ROOT = __dirname;
const DATA = path.join(ROOT, "data");
const USERS_FILE = path.join(DATA, "users.json");
const INVITES_FILE = path.join(DATA, "invites.json");
const ADMIN_PW_FILE = path.join(DATA, "初始管理员密码.txt");
const PORT = Number(process.env.PORT || 8123);
const TOOLS_DIR = path.join(ROOT, "..", "mobile");
const SESSION_MS = 1000 * 60 * 60 * 12;   // 12 小时

fs.mkdirSync(DATA, { recursive: true });
const load = (f, d) => { try { return JSON.parse(fs.readFileSync(f, "utf8")); } catch (e) { return d; } };
const save = (f, v) => fs.writeFileSync(f, JSON.stringify(v, null, 2), "utf8");

let users = load(USERS_FILE, []);
let invites = load(INVITES_FILE, []);
const sessions = new Map();
let _usersMtime = 0;
function reloadUsersIfChanged() {
  try {
    const st = fs.statSync(USERS_FILE);
    if (st.mtimeMs !== _usersMtime) { _usersMtime = st.mtimeMs; users = load(USERS_FILE, users); }
  } catch (e) {}
}

/* ---------- 审计日志 ---------- */
const AUDIT_FILE = path.join(DATA, "audit.log");
function audit(actor, action, target, detail, ip) {
  try {
    fs.appendFileSync(AUDIT_FILE, JSON.stringify({ at: nowISO(), actor: actor || "-", action, target: target || "", detail: detail || "", ip: ip || "" }) + "\n", "utf8");
  } catch (e) {}
}
function auditTail(n) {
  try {
    const lines = fs.readFileSync(AUDIT_FILE, "utf8").split("\n").filter(Boolean);
    return lines.slice(-n).reverse().map(l => { try { return JSON.parse(l); } catch (e) { return null; } }).filter(Boolean);
  } catch (e) { return []; }
}

/* ---------- 登录限流（同一 IP+账号：10 分钟内失败 5 次 → 锁 10 分钟）---------- */
const RATE = new Map();
const RATE_MAX = 5, RATE_WINDOW = 10 * 60e3, RATE_BLOCK = 10 * 60e3;
const rk = (ip, name) => ip + "|" + String(name || "").toLowerCase();
function rateCheck(ip, name) {
  const r = RATE.get(rk(ip, name));
  if (r && r.blockUntil && r.blockUntil > Date.now()) return Math.ceil((r.blockUntil - Date.now()) / 60000);
  return 0;
}
function rateFail(ip, name) {
  const k = rk(ip, name), now = Date.now();
  let r = RATE.get(k);
  if (!r || now - r.firstAt > RATE_WINDOW) r = { count: 0, firstAt: now, blockUntil: 0 };
  r.count++;
  if (r.count >= RATE_MAX) { r.blockUntil = now + RATE_BLOCK; r.count = 0; r.firstAt = now; }
  RATE.set(k, r);
  return r.blockUntil;
}
const rateReset = (ip, name) => RATE.delete(rk(ip, name));

/* ---------- 注册频次（同一 IP 每小时最多 5 个）---------- */
const REG = new Map();
function regAllow(ip) {
  const now = Date.now(), r = REG.get(ip);
  if (!r || now - r.firstAt > 60 * 60e3) { REG.set(ip, { count: 1, firstAt: now }); return true; }
  if (r.count >= 5) return false;
  r.count++; return true;
}

/* ---------- CSRF（双提交 Cookie）---------- */
let CURRENT_CSRF = "";
const clientIp = req => ((req.headers["x-forwarded-for"] || "").split(",")[0].trim()) || req.socket.remoteAddress || "";
function ensureCsrf(req, res) {
  const m = /(?:^|;\s*)csrf=([a-f0-9]{32})/.exec(req.headers.cookie || "");
  if (m) return m[1];
  const t = crypto.randomBytes(16).toString("hex");
  const secure = /^https/.test(req.headers["x-forwarded-proto"] || "");
  res.setHeader("set-cookie", "csrf=" + t + "; Path=/; SameSite=Lax; Max-Age=86400" + (secure ? "; Secure" : ""));
  return t;
}
function csrfOk(req, body) {
  const m = /(?:^|;\s*)csrf=([a-f0-9]{32})/.exec(req.headers.cookie || "");
  if (!m || !body || !body.csrf) return false;
  const a = Buffer.from(m[1]), b = Buffer.from(String(body.csrf));
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}

/* ---------- 密码 ---------- */
function hashPassword(pw, salt) {
  salt = salt || crypto.randomBytes(16).toString("hex");
  const hash = crypto.scryptSync(pw, salt, 64).toString("hex");
  return { salt, hash };
}
function verifyPassword(pw, user) {
  const { hash } = hashPassword(pw, user.salt);
  const a = Buffer.from(hash, "hex"), b = Buffer.from(user.hash, "hex");
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
const rid = () => crypto.randomBytes(8).toString("hex");
const nowISO = () => new Date().toISOString().replace("T", " ").slice(0, 16);
function expiryFromValidity(validity){
  const d = new Date();
  if (validity === "month") d.setMonth(d.getMonth() + 1);
  else if (validity === "year") d.setFullYear(d.getFullYear() + 1);
  else return null;
  return d.toISOString();
}
function validityLabel(u){
  if (!u) return "";
  if (u.role === "admin") return "终身有效";
  if (u.status === "expired") return "已到期" + (u.expiresAt ? "（" + u.expiresAt.slice(0,10) + "）" : "");
  if (!u.expiresAt || u.validity === "lifetime") return "终身有效";
  return "有效期至 " + u.expiresAt.slice(0,10);
}
function isExpired(u){ return !!(u && u.status === "active" && u.expiresAt && new Date(u.expiresAt).getTime() <= Date.now()); }
function expireIfNeeded(u){ if(isExpired(u)){ u.status = "expired"; save(USERS_FILE, users); } return u; }

/* ---------- 首次运行：创建管理员 ---------- */
if (!users.length) {
  const pw = "adm-" + crypto.randomBytes(4).toString("hex");
  const { salt, hash } = hashPassword(pw);
  users.push({ id: rid(), username: "admin", salt, hash, role: "admin", status: "active",
    perms: { query: true, teach: true }, createdAt: nowISO(), note: "初始管理员" });
  save(USERS_FILE, users);
  fs.writeFileSync(ADMIN_PW_FILE, "初始管理员账号：admin\n初始密码：" + pw + "\n（首次登录后请到后台重置密码）\n", "utf8");
  console.log("========================================");
  console.log("已创建初始管理员");
  console.log("  账号：admin");
  console.log("  密码：" + pw);
  console.log("（同时写入 data/初始管理员密码.txt）");
  console.log("========================================");
}

/* ---------- 会话 ---------- */
function createSession(userId) {
  const t = crypto.randomBytes(24).toString("hex");
  sessions.set(t, { userId, exp: Date.now() + SESSION_MS });
  return t;
}
function currentUser(req) {
  const m = /(?:^|;\s*)sid=([a-f0-9]+)/.exec(req.headers.cookie || "");
  if (!m) return null;
  const s = sessions.get(m[1]);
  if (!s || s.exp < Date.now()) { sessions.delete(m[1]); return null; }
  return expireIfNeeded(users.find(u => u.id === s.userId) || null);
}
const esc = s => String(s == null ? "" : s).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
/* ============================================================
   页面模板（暖橙 · ②-B 风格）
   ============================================================ */
const CSS = `
:root{--bg:#fffaf3;--card:#fff;--ink:#1b1a17;--muted:#7c7368;--line:#f0e4d2;--brand:#b45309;--brand2:#f59e0b;--ok:#059669;--bad:#dc2626}
*{box-sizing:border-box;margin:0}
body{font-family:system-ui,"Microsoft YaHei",sans-serif;line-height:1.7;color:var(--ink);background:
  radial-gradient(900px 320px at 50% -140px,rgba(245,158,11,.18),transparent 65%),var(--bg);
  min-height:100vh;display:flex;align-items:center;justify-content:center;padding:24px}
.wrap{width:100%;max-width:920px}
.card{background:var(--card);border:1px solid var(--line);border-radius:18px;padding:28px;box-shadow:0 14px 40px rgba(120,80,20,.08)}
h1{font-size:22px;margin-bottom:6px}h2{font-size:16px;margin:22px 0 12px}
.sub{color:var(--muted);font-size:13.5px;margin-bottom:18px}
label{display:block;font-weight:700;font-size:13px;margin:12px 0 6px}
input,select{width:100%;padding:11px 13px;border:1.5px solid #eadfcd;border-radius:10px;font-size:14px;font-family:inherit;background:#fffdf9}
input:focus{outline:none;border-color:var(--brand);box-shadow:0 0 0 4px rgba(180,83,9,.12)}
button,.btn{display:inline-flex;align-items:center;gap:8px;padding:11px 18px;border:0;border-radius:10px;font-weight:800;font-size:14px;cursor:pointer;text-decoration:none;font-family:inherit;margin:8px 8px 0 0}
.primary{background:linear-gradient(135deg,var(--brand),var(--brand2));color:#fff;box-shadow:0 8px 20px rgba(180,83,9,.22)}
.ghost{background:#fff;color:var(--ink);border:1.5px solid var(--line)}
.danger{background:#fff1f0;color:#b91c1c;border:1.5px solid #f7c8c4}
.mini{padding:6px 12px;font-size:12.5px;border-radius:8px;margin:0 6px 6px 0}
.msg{padding:11px 14px;border-radius:10px;font-size:13.5px;margin:12px 0}
.msg.ok{background:#ecfdf5;border:1px solid #a7f3d0;color:#065f46}
.msg.bad{background:#fff1f2;border:1px solid #fecdd3;color:#9f1239}
.msg.info{background:#fff7ea;border:1px solid #fde68a;color:#92400e}
table{width:100%;border-collapse:separate;border-spacing:0;border:1px solid var(--line);border-radius:12px;overflow:hidden;font-size:13.5px}
th{background:#fff7ea;text-align:left;padding:10px 12px;color:#92400e;font-size:12.5px}
td{padding:10px 12px;border-top:1px solid var(--line);vertical-align:middle}
.tag{display:inline-block;padding:2px 9px;border-radius:999px;font-size:11.5px;font-weight:800}
.tag.on{background:#ecfdf5;color:#065f46}.tag.off{background:#f4f4f5;color:#71717a}
.tag.pending{background:#fff7ea;color:#92400e}.tag.admin{background:#fef3c7;color:#92400e}
.row{display:flex;gap:12px;flex-wrap:wrap}
.entry{display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-top:8px}
@media(max-width:700px){.entry{grid-template-columns:1fr}}
.box{border:1px solid var(--line);border-radius:14px;padding:18px;background:#fffdf9}
.mono{font-family:ui-monospace,Consolas,monospace;font-size:12.5px;color:var(--muted)}
.top{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-bottom:6px}
`;

function layout(title, body, user) {
  const nav = user
    ? `<div class="top"><div class="mono">已登录：${esc(user.username)}${user.role === "admin" ? " · 管理员" : ""}</div>
       <div><a class="btn ghost mini" href="/password">修改密码</a>${user.role === "admin" ? '<a class="btn ghost mini" href="/admin">管理后台</a>' : ""}<a class="btn ghost mini" href="/logout">退出登录</a></div></div>`
    : "";
  return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8"/>
<meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>${esc(title)} · 领航体系 · 阿郎的教学网站</title><style>${CSS}</style></head>
<body><div class="wrap"><div class="card">${nav}${body}</div></div></body></html>`;
}

const SITE_LOGO_DATA_URI = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAADgAAAApCAYAAABgDOogAAAFAElEQVR4nO2af4hUVRTHP9MsE8kKhrHLgjGhFAX9NAyXoihcCIKiWCiSYoJiIyEKo1LoF0WSJP0RRVawERhJURSVgWEYyUqRbLRRJC2Fkri4qKw0ODQUF743Dqf7Zt6MM+soHRjmvXnvvnO/95z7PT/eFDbs5bSWMzjNpa/Lz18KrABWAucDi4B+4CgwA/wIfAvsAo6cKgBXAmsFrNzk3lGgBpSAL4BNwOe96qJXA98BX2viEVy9ybiSQK4CtgHfAMt7DeDbwA5NrOhAhXNygIxjVgjkK70AsB/4AbhLk0TWKJpjK/UMi1bdQoTjB+QNJ20PDglcII44ybMM0KqOA3m8IyLZK4BDcsngyks0Lsvt/wCW6XktS6HNODgA/KaJ1TPc8E3gvpzPewF4tMH1WeCc+XLRxVrVUgJcWOXdYeFaABfkMY3Z30DncW2JrgIsAYcMsKLbW88Dw7Qv5ypURKk73XPdBnjc7C3PlGuA5zhxeUQWTbl+TXPoOMn0AwekIBKCVR7Abc4YG+67FrhZmU1N2ctnwFTGmI0C+KL7PRJY8KLzgGOdsuC4QHqar2vFX80YVwEOKkY+JJCjIpXAwJPAZRljg6s+7PTVzJ68tdMsGoL4U6L4kiz6OvBhxv3vaRLezeIiRWsEuQX4OOM51wPrgUuN9Z9sYP2OhIlmsl0Ts+D8norWiEBXK172fLm0TUE8pmx1rfYIMKi9s8ZYsabjcbn0vACcUEXQDrgbXMr2KXAJ8KVKpN+1Z5eZEqkosOH3e9vQOwG8lgdgSLt+UckTGOyTnArKGjdiXC5879H+SskBxT0fbt6QNfPqPaj5jqXGWYBDylBCYRotcBPwp9iuYq7FrH8d8KvStrLbYyG9utKcjyqGHVa4QDQ/YOg+umxF923RHKzeshj5J+kdMPOtiLGTJDOhlYhkYEnBE0Sj85h0FxKLFyUAWugW+293Hidt2TZau2j0kJjrBuAJb8FhUbAHV1WGslCTLihBKIg0NjuwUek+546X61kzAmzv/4v/yhGFhzOd3j7tXxuerP7xCC4rTOxU5oGA/XtzE9mh0GBXfxq4qMGYslw8Mmq0UAjwL+fUOwlcLJCblHg0jYM7peB9Wq/s73QrOiUW9XKjITHbBRgR47YiW7TnH5yPQP8ucHvC3R5XKYVIouKsXRPoUBh3TPraGLOoSYvvDl0fc2OScUpSEls2AhcZtmuZzLOKOYcVOia04im539V1yAVTbYdjcuHQNkzJWhHWnMhon3pAuSSvi3q3syy7UfVbSgLpvJRRMdSVe97dQO8HSthTYSnXXs0LcIkyFdscskqfAZ5uMD4AvELfR0U8uxQ+suQjlVdeX03p322d3IP7lVYdSgRfVEaVFLdS8r0+ecWCi/riYgar39ONPTjrOlveZdY1IRJaiKeBcHCLWZdL5gbXTrk0m8GiEeyYiKgdKctDbB1pPWWPqVS6Wg9WgbOVcqU61QPKK7ertZAH2KQS58WJ59WVQl41353tQVnLgrAJ8CpdL2r1A6n8rN7OUrFgrCqs+BbHVLvgOvH6bNBUIRacn+xyfZpVJV62KnE4qS2LYQV1z6wp8WCywFVFJicErpM9mZDBXyA3TL09ynqr5CW+qFkAvNVrTadp4BoB3SoSiuLb/DannBH9rxZ5he+efoU9bVzrQuA6vQaLLY05JQ5fqbro6v88Cv//jYRTW/4B9RtOqzSg9X0AAAAASUVORK5CYII=";

const LOGIN_CSS = `
*{box-sizing:border-box}body{margin:0;min-height:100vh;background:#fffaf3;color:#231f1a;font-family:Inter,"Microsoft YaHei",sans-serif}
.login-shell{min-height:100vh;display:grid;grid-template-columns:1.12fr .88fr}.login-cover{padding:52px 58px;position:relative;overflow:hidden;background:radial-gradient(720px 520px at 10% 5%,rgba(245,158,11,.2),transparent 65%),linear-gradient(145deg,#fffaf3,#fff3df)}
.login-cover:before{content:"";position:absolute;width:480px;height:480px;border:1px solid rgba(180,83,9,.12);border-radius:50%;right:-130px;top:-110px}.login-cover:after{content:"";position:absolute;width:330px;height:330px;border:1px dashed rgba(180,83,9,.17);border-radius:50%;right:-20px;top:20px}
.login-brand{position:relative;z-index:2;display:flex;align-items:center;gap:14px}.login-brand .login-logo{width:70px;height:58px;object-fit:contain;filter:drop-shadow(0 5px 10px rgba(17,24,39,.14))}.login-brand h1{margin:0;font-size:25px;letter-spacing:.04em}.login-brand p{margin:4px 0 0;color:#9a7b5b;font-size:12px;letter-spacing:.14em}
.login-hero{position:relative;z-index:2;margin-top:76px;max-width:760px}.login-badge{display:inline-flex;padding:7px 13px;border-radius:999px;background:#fef3c7;border:1px solid #fde68a;color:#92400e;font-size:12px;font-weight:800;letter-spacing:.1em}.login-hero h2{font-size:clamp(44px,5.3vw,76px);line-height:1.06;letter-spacing:-.055em;margin:22px 0 18px}.login-hero h2 em{font-style:normal;color:#b45309}.login-hero p{max-width:620px;color:#75695c;line-height:1.9;font-size:16px;margin:0}.login-features{display:grid;grid-template-columns:1fr 1fr;gap:10px;max-width:620px;margin-top:28px}.login-feature{padding:13px 15px;border-radius:14px;background:rgba(255,255,255,.78);border:1px solid #f0e4d2;box-shadow:0 12px 28px rgba(120,80,20,.06)}.login-feature b{display:block;font-size:14px;color:#241f1a}.login-feature span{display:block;color:#9a8d7c;font-size:12px;margin-top:3px}
.login-illustration{position:absolute;right:68px;bottom:48px;width:330px;height:260px;z-index:1}.login-sun{position:absolute;right:10px;top:0;width:150px;height:150px;border-radius:50%;background:linear-gradient(135deg,#fbbf24,#f97316);box-shadow:0 20px 60px rgba(245,158,11,.32)}.login-ship{position:absolute;left:0;right:0;bottom:0;height:120px;background:#b45309;clip-path:polygon(0 70%,100% 70%,86% 100%,14% 100%);border-radius:0 0 24px 24px}.login-mast{position:absolute;left:48%;bottom:100px;width:5px;height:120px;background:#7c2d12}.login-sail{position:absolute;left:49%;bottom:110px;width:90px;height:100px;background:#fff7ed;clip-path:polygon(0 100%,0 0,100% 100%);border-left:2px solid #7c2d12}.login-wave{position:absolute;left:0;right:0;bottom:50px;height:30px;background:repeating-linear-gradient(90deg,#f59e0b 0 18px,transparent 18px 28px);border-radius:50%;opacity:.35}
.login{padding:52px 6vw;display:flex;align-items:center;justify-content:center;background:#fff;border-left:1px solid #f0e4d2}.login-card{width:min(430px,100%)}.login-kicker{color:#b45309;font-size:12px;font-weight:900;letter-spacing:.13em}.login-card h3{font-size:31px;margin:12px 0 0}.login-card .login-sub{color:#8b8175;font-size:14px;line-height:1.75;margin:9px 0 30px}.login-field{margin-bottom:16px}.login-field label{display:block;font-size:13px;color:#76695b;margin-bottom:7px;font-weight:700}.login-field input{width:100%;height:52px;border:1px solid #e8dccb;border-radius:14px;padding:0 16px;background:#fffdf9;outline:none;font-size:14px}.login-field input:focus{border-color:#f59e0b;box-shadow:0 0 0 4px rgba(245,158,11,.12)}
.login-btn{width:100%;height:52px;border:0;border-radius:14px;background:linear-gradient(135deg,#b45309,#f59e0b);color:#fff;font-weight:800;font-size:15px;box-shadow:0 14px 30px rgba(180,83,9,.22);cursor:pointer}.login-ghost{display:block;text-align:center;margin-top:15px;color:#b45309;text-decoration:none;font-size:14px}.login-foot{text-align:center;color:#b8ac9d;font-size:12px;margin-top:26px}.login-msg{padding:11px 14px;border-radius:10px;font-size:13.5px;margin:0 0 16px}.login-msg.bad{background:#fff1f2;border:1px solid #fecdd3;color:#9f1239}.login-msg.info{background:#fffbeb;border:1px solid #fde68a;color:#92400e}
@media(max-width:900px){.login-shell{grid-template-columns:1fr}.login-cover{padding:34px 24px;min-height:46vh}.login-hero{margin-top:50px}.login-hero h2{font-size:42px}.login-illustration{display:none}.login-features{grid-template-columns:1fr}.login{padding:34px 20px}}
`;
function loginLayout(body, title){
  return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8"/><meta name="viewport" content="width=device-width,initial-scale=1"/><title>${esc(title||"领航体系 · 阿郎的教学网站")}</title><style>${LOGIN_CSS}</style></head><body><div class="login-shell"><section class="login-cover"><div class="login-brand"><img class="login-logo" src="${SITE_LOGO_DATA_URI}" alt="领航体系 LOGO" /><div><h1>领航体系</h1><p>阿郎的教学网站</p></div></div><div class="login-hero"><span class="login-badge">系统学习 · 链上实践 · 一起成长</span><h2>跟阿郎老师一起<br>学懂<em>链上世界</em></h2><p>从课程到工具，从查询到实践，把复杂的链上知识拆成一条清楚的学习路线。</p><div class="login-features"><div class="login-feature"><b>资产查询</b><span>ANUBIS / 马蹄链统一查询</span></div><div class="login-feature"><b>收益扫描</b><span>本金、爆块、额外爆块、债券</span></div><div class="login-feature"><b>教学执行</b><span>一站式执行 ANUBIS 和 POLYGON 链上全资产提取</span></div><div class="login-feature"><b>课程工具</b><span>课程资料与内部教学入口</span></div></div></div><div class="login-illustration"><div class="login-sun"></div><div class="login-mast"></div><div class="login-sail"></div><div class="login-ship"></div><div class="login-wave"></div></div></section><section class="login"><div class="login-card">${body}</div></section></div></body></html>`;
}
const pageLogin = (msg, info) => loginLayout(`
  <div class="login-kicker">MEMBERS · LEARNING · PRACTICE</div><h3>登录领航体系</h3><p class="login-sub">进入课程、链上查询与内部教学工具。</p>
  ${msg ? `<div class="login-msg bad">${esc(msg)}</div>` : ""}
  ${info ? `<div class="login-msg info">${esc(info)}</div>` : ""}
  <form method="POST" action="/login"><div class="login-field"><label>账号</label><input name="username" autocomplete="username" required /></div><div class="login-field"><label>密码</label><input name="password" type="password" autocomplete="current-password" required /></div><button class="login-btn" type="submit">登录学习平台</button><a class="login-ghost" href="/register">学员注册 / 申请加入</a></form><div class="login-foot">领航体系 · 阿郎的教学网站</div>`, "领航体系 · 阿郎的教学网站");
const pageRegister = (msg) => layout("注册", `
  <h1>学员注册</h1><div class="sub">注册后账号为「待审核」，管理员批准并授权后才能使用查询/教学功能。</div>
  ${msg ? `<div class="msg bad">${esc(msg)}</div>` : ""}
  <form method="POST" action="/register">
    <label>账号（3-20 位字母数字）</label><input name="username" required />
    <label>密码（至少 6 位）</label><input name="password" type="password" required />
    <label>邀请码（可选）</label><input name="invite" placeholder="有邀请码可直接获得权限" />
    <button class="primary" type="submit">提交注册</button>
    <a class="btn ghost" href="/">返回登录</a>
  </form>`);

const pagePending = (user, msg) => layout("待审核", `
  <h1>等待管理员审核</h1>
  <div class="msg info">账号 <b>${esc(user.username)}</b> 已创建，状态：待审核。管理员批准并授权后即可使用。</div>
  ${msg ? `<div class="msg ok">${esc(msg)}</div>` : ""}
  <p class="sub">如长时间未通过，请联系管理员（阿郎老师）。</p>`);

const pageDashboard = (user, msg) => layout("我的面板", `
  <h1>${esc(user.username)} 的教学面板</h1>
        <div class="sub">你的权限由管理员分配，可分别开通「查询」与「教学」。当前状态：${user.status === "active" ? "已授权" : user.status === "expired" ? "已到期" : "待审核"} · 有效期：${validityLabel(user)}</div>
  ${msg ? `<div class="msg ok">${esc(msg)}</div>` : ""}
  <div class="entry">
    <div class="box"><h2>① 只读查询</h2>
      <p class="sub">查看链上资产（只读，不签名）。</p>
      <div>${user.perms.query ? '<span class="tag on">已授权</span>' : '<span class="tag off">未授权</span>'}</div>
      <div style="margin-top:12px">${user.perms.query
        ? '<a class="btn primary" href="/app/query/anubis">ANUBIS 查询</a><a class="btn primary" href="/app/query/polygon">马蹄链查询</a>'
        : '<span class="mono">如需开通，请联系管理员</span>'}</div>
    </div>
    <div class="box"><h2>② 链上执行（内部教学）</h2>
      <p class="sub">教学用：<b>查询 + 执行同屏</b>（先看数据，再模拟 → 签名发送）。</p>
      <div>${user.perms.teach ? '<span class="tag on">已授权</span>' : '<span class="tag off">未授权</span>'}</div>
      <div style="margin-top:12px">${user.perms.teach
        ? '<a class="btn primary" href="/app/teach/anubis">ANUBIS 教学</a><a class="btn primary" href="/app/teach/polygon">马蹄链教学</a>'
        : '<span class="mono">教学权限需管理员审批后开通</span>'}</div>
    </div>
    <div class="box"><h2>③ AILGNS 教学工具</h2>
      <p class="sub">AiLGNS 涡轮产品：<b>资产查询 + 提取操作</b>（查余额与锁仓、激活涡轮、领取已解锁）。</p>
      <div>${user.perms.teach ? '<span class="tag on">已授权</span>' : '<span class="tag off">未授权</span>'}</div>
      <div style="margin-top:12px">${user.perms.teach
        ? '<a class="btn primary" href="/app/teach/ailgns">AILGNS 教学</a>'
        : '<span class="mono">需管理员审批开通教学权限</span>'}</div>
    </div>
  </div>`, user);

const pagePassword = (user, msg) => layout("修改密码", `
  <h1>修改密码</h1><div class="sub">建议使用 8 位以上、包含字母和数字的密码。</div>
  ${msg ? `<div class="msg ${msg.includes("成功") ? "ok" : "bad"}">${esc(msg)}</div>` : ""}
  <form method="POST" action="/password">
    <label>原密码</label><input name="old" type="password" required />
    <label>新密码（≥8 位，含字母和数字）</label><input name="new" type="password" required />
    <label>确认新密码</label><input name="confirm" type="password" required />
    <button class="primary" type="submit">确认修改</button>
    <a class="btn ghost" href="/">返回面板</a>
  </form>`, user);
function pageAdmin(adminUser, msg) {
  const rows = users.map(u => {
    const selected = u.validity || (u.expiresAt ? "month" : "lifetime");
    const validitySelect = u.role === "admin" ? '<span class="mono">终身有效</span>' : `<select name="validity" style="max-width:130px"><option value="month"${selected === "month" ? " selected" : ""}>1个月</option><option value="year"${selected === "year" ? " selected" : ""}>1年</option><option value="lifetime"${selected === "lifetime" ? " selected" : ""}>终身有效</option></select>`;
    return `<tr>
      <td><b>${esc(u.username)}</b><div class="mono">${esc(u.createdAt || "")}</div></td>
      <td>${u.role === "admin" ? '<span class="tag admin">管理员</span>' : ""}${u.status === "pending" ? '<span class="tag pending">待审核</span>' : u.status === "disabled" ? '<span class="tag off">已禁用</span>' : u.status === "expired" ? '<span class="tag off">已到期</span>' : '<span class="tag on">已启用</span>'}</td>
      <td><div class="mono">${validityLabel(u)}</div></td>
      <td>查询 <span class="tag ${u.perms.query ? "on" : "off"}">${u.perms.query ? "有" : "无"}</span><br/>教学 <span class="tag ${u.perms.teach ? "on" : "off"}">${u.perms.teach ? "有" : "无"}</span></td>
      <td><form method="POST" action="/admin/act" style="display:inline"><input type="hidden" name="id" value="${u.id}"/>${validitySelect}<button class="btn ghost mini" name="op" value="approve">批准+授权查询</button><button class="btn ghost mini" name="op" value="updateValidity">更新有效期</button><button class="btn ghost mini" name="op" value="toggleQuery">切换查询</button><button class="btn ghost mini" name="op" value="toggleTeach">切换教学</button><button class="btn ghost mini" name="op" value="toggleStatus">${u.status === "disabled" ? "启用" : "禁用"}</button><button class="btn ghost mini" name="op" value="resetPw">重置密码</button></form></td></tr>`;
  }).join("");
  const inviteRows = invites.length ? invites.map(i => `<tr><td class="mono">${esc(i.code)}</td><td>查询 ${i.perms.query ? "有" : "无"} / 教学 ${i.perms.teach ? "有" : "无"}</td><td class="mono">${esc(i.createdAt)}</td></tr>`).join("")
    : '<tr><td colspan="3" class="mono">暂无邀请码</td></tr>';

  return layout("管理后台", `
  <h1>管理后台</h1><div class="sub">审批学员、分配「查询 / 教学」权限、生成邀请码。</div>
  ${msg ? `<div class="msg ok">${esc(msg)}</div>` : ""}
  <h2>用户列表（${users.length}）</h2>
  <table><tr><th>账号</th><th>状态 / 角色</th><th>有效期</th><th>权限</th><th>操作</th></tr>${rows}</table>
  <h2>生成邀请码</h2>
  <form method="POST" action="/admin/invite" class="row">
    <select name="perm" style="max-width:280px">
      <option value="query">可直接使用：只读查询</option>
      <option value="teach">可直接使用：查询 + 教学</option>
    </select>
    <button class="primary" type="submit">生成邀请码</button>
  </form>
  <table style="margin-top:12px"><tr><th>邀请码</th><th>权限</th><th>创建时间</th></tr>${inviteRows}</table>
  <h2>最近操作记录（审计日志）</h2>
  <table><tr><th>时间</th><th>操作者</th><th>动作</th><th>对象</th><th>说明</th><th>IP</th></tr>
  ${auditTail(30).map(a => `<tr><td class="mono">${esc(a.at)}</td><td>${esc(a.actor)}</td><td>${esc(a.action)}</td><td>${esc(a.target)}</td><td>${esc(a.detail)}</td><td class="mono">${esc(a.ip)}</td></tr>`).join("") || '<tr><td colspan="6" class="mono">暂无记录</td></tr>'}</table>`, adminUser);
}
/* ============================================================
   路由与权限网关
   ============================================================ */
function readBody(req) {
  return new Promise(resolve => {
    let d = "";
    req.on("data", c => { d += c; if (d.length > 1e6) req.destroy(); });
    req.on("end", () => {
      const o = {};
      new URLSearchParams(d).forEach((v, k) => { o[k] = v; });
      resolve(o);
    });
  });
}
function send(res, code, html, headers) {
  let out = html;
  if (typeof out === "string" && out.indexOf("<form method=\"POST\"") >= 0 && out.indexOf('name="csrf"') < 0) {
    out = out.replace(/(<form method="POST"[^>]*>)/g, '$1<input type="hidden" name="csrf" value="' + CURRENT_CSRF + '">');
  }
  res.writeHead(code, Object.assign({
    "content-type": "text/html; charset=utf-8",
    "cache-control": "no-store",
    "x-content-type-options": "nosniff",
    "x-frame-options": "DENY",
    "referrer-policy": "same-origin"
  }, headers || {}));
  res.end(out);
}
function redirect(res, to, cookie) {
  const h = { location: to };
  if (cookie) h["set-cookie"] = cookie;
  res.writeHead(302, h); res.end();
}
function sidCookie(req, token, maxAgeSec) {
  const secure = /^https/.test(req.headers["x-forwarded-proto"] || "");
  return "sid=" + token + "; HttpOnly; Path=/; SameSite=Lax; Max-Age=" + maxAgeSec + (secure ? "; Secure" : "");
}

/* 受保护的工具页：按权限裁剪「链上执行」标签 */
function serveTool(res, user, chain, allowTeach) {
  const base = chain === "polygon" ? "polygon" : (chain === "ailgns" ? "ailgns" : "anubis");
  const fileName = chain === "ailgns" ? "ailgns-tool-mobile.html" : (allowTeach ? base + "-tool-mobile.html" : base + "-query-only.html");
  const file = path.join(TOOLS_DIR, fileName);
  let html;
  try { html = fs.readFileSync(file, "utf8"); }
  catch (e) { return send(res, 500, "<h1>工具文件缺失</h1>"); }

  const bar = `<div style="position:fixed;left:12px;bottom:12px;z-index:99;background:#fff;border:1px solid #f0e4d2;
    border-radius:999px;padding:8px 14px;font:600 12.5px system-ui;box-shadow:0 8px 22px rgba(120,80,20,.12)">
    ${esc(user.username)} ｜ ${allowTeach ? "查询 + 教学权限" : "仅查询权限"} ｜
    <a href="/" style="color:#b45309;text-decoration:none">返回面板</a></div>`;
  let inject = bar + `<script>document.addEventListener("DOMContentLoaded",function(){var h=document.getElementById("homeLink");if(h){h.href="/";h.textContent="← 返回首页";}});</script>`;
  if (!allowTeach) {
    // 仅查询权限：直接读取纯查询版，页面中不包含执行区与签名代码。
  } else {
    // 教学权限：保持“最初工具模板”的原样结构（移除标签脚本，不重排、不合并）
    const marker = 'function build() {';
    const mi = html.indexOf(marker);
    if (mi > 0) {
      const s = html.lastIndexOf('<script>', mi);
      const e = html.indexOf('</script>', mi);
      if (s >= 0 && e > s) html = html.slice(0, s) + html.slice(e + '</script>'.length);
    }
  }
  if (chain === "ailgns") {
    try {
      const lib = fs.readFileSync(path.join(TOOLS_DIR, "ethers.umd.min.js"), "utf8");
      html = html.replace('<script src="ethers.umd.min.js"></script>', '<script>' + lib + '</' + 'script>');
    } catch (e) {}
    inject += '<style>[data-tab="records"],[data-tab="team"],[data-tab="all"]{display:none !important}</style>'
      + '<script>document.addEventListener("DOMContentLoaded",function(){document.querySelectorAll(".tab").forEach(function(b){if(["records","team","all"].indexOf(b.dataset.tab)>=0){b.style.display="none"}});});</' + 'script>';
  }
  html = html.replace("</body>", inject + "</body>");
  send(res, 200, html);
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, "http://localhost");
  const p = url.pathname;
  reloadUsersIfChanged();
  const user = currentUser(req);
  CURRENT_CSRF = ensureCsrf(req, res);
  const ip = clientIp(req);
  let _bodyCache = null;
  const getBody = async () => { if (_bodyCache === null) _bodyCache = await readBody(req); return _bodyCache; };
  if (user && user.status === "expired" && p !== "/" && p !== "/login" && p !== "/logout" && p !== "/favicon.ico") return send(res, 403, pageLogin("账号已到期，请联系管理员续期"));

  try {
    if (req.method === "POST") {
      const b0 = await getBody();
      if (!csrfOk(req, b0)) {
        audit(user ? user.username : "anonymous", "csrf_block", p, "", ip);
        return send(res, 403, "<h1>403 请求校验失败</h1><p>请返回上一页重新提交。</p>");
      }
    }
    /* ---------- 首页 ---------- */
    if (p === "/" && req.method === "GET") {
      if (!user) return send(res, 200, pageLogin());
      if (user.status === "expired") return send(res, 200, pageLogin("账号已到期，请联系管理员续期"));
      if (user.status === "pending") return send(res, 200, pagePending(user));
      if (user.status === "disabled") return send(res, 200, pageLogin("账号已被禁用，请联系管理员"));
      return send(res, 200, pageDashboard(user));
    }

    /* ---------- favicon ---------- */
    if (p === "/favicon.ico") { res.writeHead(204); return res.end(); }

    /* ---------- 登录 ---------- */
    if (p === "/login" && req.method === "GET") return redirect(res, "/");
    if (p === "/login" && req.method === "POST") {
      const b = await getBody();
      const name = (b.username || "").trim();
      const wait = rateCheck(ip, name);
      if (wait) { audit("anonymous", "login_blocked", name, "限流剩余 " + wait + " 分钟", ip); return send(res, 429, pageLogin("登录尝试过多，请 " + wait + " 分钟后再试")); }
      const u = users.find(x => x.username === name);
      if (!u || !verifyPassword(b.password || "", u)) {
        rateFail(ip, name);
        audit("anonymous", "login_fail", name, "账号或密码错误", ip);
        return send(res, 200, pageLogin("账号或密码错误"));
      }
      if (u.status === "active" && isExpired(u)) { u.status = "expired"; save(USERS_FILE, users); audit("anonymous", "login_expired", name, "账号已到期", ip); return send(res, 200, pageLogin("账号已到期，请联系管理员续期")); }
      if (u.status === "expired") { audit("anonymous", "login_expired", name, "账号已到期", ip); return send(res, 200, pageLogin("账号已到期，请联系管理员续期")); }
      if (u.status === "disabled") { audit("anonymous", "login_disabled", name, "账号被禁用", ip); return send(res, 200, pageLogin("账号已被禁用，请联系管理员")); }
      rateReset(ip, name);
      audit(u.username, "login", "", "登录成功", ip);
      const token = createSession(u.id);
      return redirect(res, "/", sidCookie(req, token, SESSION_MS / 1000));
    }

    /* ---------- 注册 ---------- */
    if (p === "/register" && req.method === "GET") return send(res, 200, pageRegister());
    if (p === "/register" && req.method === "POST") {
      const b = await getBody();
      const name = (b.username || "").trim();
      const pw = b.password || "";
      if (!/^[A-Za-z0-9_]{3,20}$/.test(name)) return send(res, 200, pageRegister("账号需为 3-20 位字母、数字或下划线"));
      if (pw.length < 6) return send(res, 200, pageRegister("密码至少 6 位"));
      if (users.some(u => u.username.toLowerCase() === name.toLowerCase())) return send(res, 200, pageRegister("该账号已存在"));

      if (!regAllow(ip)) { audit("anonymous", "register_blocked", name, "同 IP 注册过多", ip); return send(res, 429, pageRegister("注册过于频繁，请稍后再试")); }
      const code = (b.invite || "").trim();
      const inv = code ? invites.find(i => i.code === code) : null;
      const { salt, hash } = hashPassword(pw);
      const u = { id: rid(), username: name, salt, hash, role: "member",
        status: inv ? "active" : "pending",
        perms: inv ? { query: !!inv.perms.query, teach: !!inv.perms.teach } : { query: false, teach: false },
        createdAt: nowISO(), expiresAt: null, validity: "lifetime", note: inv ? "邀请码注册" : "待审核" };
      users.push(u); save(USERS_FILE, users);
      audit(u.username, "register", "", inv ? "邀请码注册（含权限）" : "待审核", ip);
      if (inv) { invites = invites.filter(i => i.code !== code); save(INVITES_FILE, invites); }
      const token = createSession(u.id);
      return redirect(res, "/", "sid=" + token + "; HttpOnly; Path=/; SameSite=Lax; Max-Age=" + (SESSION_MS / 1000));
    }

    /* ---------- 退出 ---------- */
    if (p === "/logout") { audit(user ? user.username : "anonymous", "logout", "", "", ip); return redirect(res, "/", sidCookie(req, "", 0)); }

    /* ---------- 自助改密码 ---------- */
    if (p === "/password" && req.method === "GET") { if (!user) return redirect(res, "/"); return send(res, 200, pagePassword(user)); }
    if (p === "/password" && req.method === "POST") {
      if (!user) return redirect(res, "/");
      const b = await getBody();
      if (!verifyPassword(b.old || "", user)) { audit(user.username, "pw_change_fail", "", "原密码错误", ip); return send(res, 200, pagePassword(user, "原密码错误")); }
      const np = b.new || "";
      if (np.length < 8) return send(res, 200, pagePassword(user, "新密码至少 8 位"));
      if (!/[A-Za-z]/.test(np) || !/[0-9]/.test(np)) return send(res, 200, pagePassword(user, "新密码需同时包含字母和数字"));
      if (np !== (b.confirm || "")) return send(res, 200, pagePassword(user, "两次输入的新密码不一致"));
      const h = hashPassword(np); user.salt = h.salt; user.hash = h.hash;
      save(USERS_FILE, users);
      audit(user.username, "pw_change", "", "自助修改密码成功", ip);
      return send(res, 200, pageDashboard(user, "密码已修改成功"));
    }
    /* ---------- 管理后台 ---------- */
    if (p === "/admin") {
      if (!user || user.role !== "admin") return send(res, 403, pageLogin("需要管理员权限"));
      return send(res, 200, pageAdmin(user, url.searchParams.get("msg") || ""));
    }
    if (p === "/admin/act" && req.method === "POST") {
      if (!user || user.role !== "admin") return send(res, 403, pageLogin("需要管理员权限"));
      const b = await getBody();
      const u = users.find(x => x.id === b.id);
      if (!u) return redirect(res, "/admin?msg=用户不存在");
      let msg = "";
      if (b.op === "approve") { const validity = ["month", "year", "lifetime"].includes(b.validity) ? b.validity : "lifetime"; u.status = "active"; u.perms.query = true; u.validity = validity; u.expiresAt = expiryFromValidity(validity); u.note = "已批准（含查询权限）"; msg = u.username + " 已批准并开通查询权限，有效期：" + validityLabel(u); }
      if (b.op === "updateValidity") { const validity = ["month", "year", "lifetime"].includes(b.validity) ? b.validity : "lifetime"; u.status = "active"; u.validity = validity; u.expiresAt = expiryFromValidity(validity); msg = u.username + " 有效期已更新为：" + validityLabel(u); }
      if (b.op === "toggleQuery") { u.perms.query = !u.perms.query; msg = u.username + " 查询权限：" + (u.perms.query ? "已开通" : "已关闭"); }
      if (b.op === "toggleTeach") { u.perms.teach = !u.perms.teach; msg = u.username + " 教学权限：" + (u.perms.teach ? "已开通" : "已关闭"); }
      if (b.op === "toggleStatus") { u.status = u.status === "disabled" ? "active" : "disabled"; msg = u.username + " 状态：" + u.status; }
      if (b.op === "resetPw") {
        const np = "tmp-" + crypto.randomBytes(3).toString("hex");
        const h = hashPassword(np); u.salt = h.salt; u.hash = h.hash;
        msg = u.username + " 新临时密码：" + np + "（请转告本人并让其尽快修改）";
      }
      save(USERS_FILE, users);
      audit(user.username, "admin_" + b.op, u.username, msg, ip);
      return redirect(res, "/admin?msg=" + encodeURIComponent(msg));
    }
    if (p === "/admin/invite" && req.method === "POST") {
      if (!user || user.role !== "admin") return send(res, 403, pageLogin("需要管理员权限"));
      const b = await getBody();
      const code = "INV-" + crypto.randomBytes(3).toString("hex").toUpperCase();
      const perm = b.perm === "teach" ? { query: true, teach: true } : { query: true, teach: false };
      invites.push({ code, perms: perm, createdAt: nowISO(), by: user.username });
      save(INVITES_FILE, invites);
      audit(user.username, "admin_invite", code, "权限：" + JSON.stringify(perm), ip);
      return redirect(res, "/admin?msg=" + encodeURIComponent("已生成邀请码：" + code));
    }

    /* ---------- 受保护的工具页 ---------- */
    if (p.startsWith("/app/")) {
      if (!user) return redirect(res, "/");
      if (user.status === "expired") return send(res, 403, pageLogin("账号已到期，请联系管理员续期"));
      if (user.status !== "active") return send(res, 403, pagePending(user));
      const m = /^\/app\/(query|teach)\/(anubis|polygon|ailgns)$/.exec(p);
      if (!m) return send(res, 404, "<h1>404</h1>");
      const kind = m[1], chain = m[2];
      if (kind === "query" && !user.perms.query) return send(res, 403, pageDashboard(user, "你没有查询权限，请联系管理员开通"));
      if (kind === "teach" && !user.perms.teach) return send(res, 403, pageDashboard(user, "你没有教学权限，需管理员审批开通"));
      return serveTool(res, user, chain, kind === "teach");
    }

    /* ---------- 404 ---------- */
    send(res, 404, "<h1>404 Not Found</h1><p><a href='/'>返回首页</a></p>");
  } catch (e) {
    console.error(e);
    send(res, 500, "<h1>服务器错误</h1><pre>" + esc(e.message) + "</pre>");
  }
});

server.listen(PORT, "127.0.0.1", () => {
  console.log("内部教学门户已启动：http://localhost:" + PORT);
  console.log("  管理员后台：http://localhost:" + PORT + "/admin");
  console.log("  数据文件：data/users.json、data/invites.json");
}).on("error", (e) => {
  if (e && e.code === "EADDRINUSE") { console.log("端口 " + PORT + " 已在运行（门户可能已启动）"); process.exit(0); }
  throw e;
});