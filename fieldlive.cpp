// fieldlive: field-level liveness over a lean4export (ndjson, format 3.1) stream.
//
// Usage: zstd -dc --long=30 solution.ndjson.zst | fieldlive PROJECT_INDUCTIVES.txt OUTDIR [ROOT...]
//
// Walks the proof from the root theorems. Arguments of a fully applied constructor of a
// candidate structure (a project inductive with one constructor and no indices, not recursive)
// are held back per field until something reads that field: a `proj`, or the structure's
// recursor (which counts as reading every field). A constructor that is not fully applied also
// counts as reading every field. Field types that mention an earlier field read it. Whatever is
// still held back at the end is a dead field; constants reached only through dead fields drop out.
// A baseline run (every field read) gives the ordinary closure to compare against.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <fstream>
#include <iostream>
#include <algorithm>
using namespace std;
typedef uint32_t u32;
static const u32 NONE = 0xffffffffu;

// ---------- chunked vector (no realloc peaks) ----------
template <class T> struct Chunked {
  static const size_t B = 1u << 24;
  vector<T*> blocks; size_t n = 0;
  void ensure(size_t i) { while (i >= blocks.size() * B) { blocks.push_back((T*)calloc(B, sizeof(T))); if (!blocks.back()) { fprintf(stderr, "OOM\n"); exit(1); } } if (i + 1 > n) n = i + 1; }
  T& operator[](size_t i) { return blocks[i / B][i % B]; }
};

// ---------- minimal JSON (arena, no per-line allocation after warmup) ----------
struct JV { char t; string_view k; string_view s; long long n; int first, next; }; // t: o a s n b z
struct JP {
  vector<JV> v; const char* p; const char* e;
  void ws() { while (p < e && (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t')) ++p; }
  string_view str() { ++p; const char* b = p; while (p < e && *p != '"') { if (*p == '\\') ++p; ++p; } string_view r(b, p - b); ++p; return r; }
  int val(string_view key) {
    ws(); int id = v.size(); v.push_back(JV{0, key, {}, 0, -1, -1});
    char c = *p;
    if (c == '{' || c == '[') {
      v[id].t = c == '{' ? 'o' : 'a'; ++p; int last = -1;
      for (;;) { ws(); if (*p == '}' || *p == ']') { ++p; break; }
        string_view k; if (v[id].t == 'o') { k = str(); ws(); ++p; }
        int ch = val(k); if (last < 0) v[id].first = ch; else v[last].next = ch; last = ch;
        ws(); if (*p == ',') ++p; }
    } else if (c == '"') { v[id].t = 's'; v[id].s = str(); }
    else if (c == 't' || c == 'f') { v[id].t = 'b'; v[id].n = c == 't'; p += c == 't' ? 4 : 5; }
    else if (c == 'n') { v[id].t = 'z'; p += 4; }
    else { v[id].t = 'n'; bool neg = false; if (*p == '-') { neg = true; ++p; } long long x = 0; while (p < e && *p >= '0' && *p <= '9') x = x * 10 + (*p++ - '0');
      if (p < e && (*p == '.' || *p == 'e' || *p == 'E')) { while (p < e && strchr("0123456789.eE+-", *p)) ++p; } v[id].n = neg ? -x : x; }
    return id;
  }
  int parse(const char* b, const char* end) { v.clear(); p = b; e = end; return val({}); }
  int get(int o, const char* k) { for (int c = v[o].first; c >= 0; c = v[c].next) if (v[c].k == k) return c; return -1; }
  long long num(int o, const char* k) { int c = get(o, k); return c < 0 ? -1 : v[c].n; }
};

// ---------- tables ----------
enum K : uint8_t { BVAR = 1, SORT, CONST, APP, LAM, PI, LET, PROJ, LIT, MDATA };
Chunked<uint8_t> ek; Chunked<u32> ea, eb, en;        // kind, a, b
vector<u32> letBody;                                  // LET: a=type, b=value, body in letBody[...] keyed by order
unordered_map<u32, u32> letIdx;                       // expr -> index into letBody
vector<pair<u32, u32>> projInfo;                      // PROJ: a=struct, b=index into projInfo (typeName, idx)
vector<u32> namePre; vector<string> nameStr; vector<long long> nameNum;  // names
vector<char> levelZero;                               // level id -> is literally zero

struct Decl { char kind; u32 type, value; int ind; };   // kind: t d o a q I(type) C(ctor) R(rec)
unordered_map<u32, Decl> decls;                       // name id -> decl
struct Ind { u32 name, type; vector<u32> ctors, all; int nParams, nIdx; bool isRec; };
struct Ctor { u32 name, type, induct; int nParams, nFields; };
struct Rec { u32 name, type; vector<u32> rhs; vector<u32> all; };
vector<Ind> inds; vector<Ctor> ctors; vector<Rec> recs;
unordered_map<u32, int> indOf, ctorOf, recOf;         // name id -> index

string fullName(u32 n) {
  if (n == 0 || n == NONE) return "";
  string pre = fullName(namePre[n]);
  string me = nameNum[n] >= 0 ? to_string(nameNum[n]) : nameStr[n];
  return pre.empty() ? me : pre + "." + me;
}

// ---------- candidate structures ----------
struct Cand { int ind, ctor; int nParams, nFields; bool prop; vector<char> read; vector<vector<u32>> pend; vector<string> fieldNames; };
vector<Cand> cands; unordered_map<u32, int> candOfInd, candOfCtor, candOfRec;

// ---------- liveness ----------
struct Run {
  bool fieldMode; vector<char> live; vector<uint64_t> vis; vector<u32> st; size_t nLive = 0;
  bool seen(u32 e) { uint64_t m = 1ull << (e & 63); if (vis[e >> 6] & m) return true; vis[e >> 6] |= m; return false; }
  void push(u32 e) { if (e != NONE) st.push_back(e); }
  void readField(Cand& c, int k) { if (c.read[k]) return; c.read[k] = 1; for (u32 x : c.pend[k]) push(x); c.pend[k].clear(); c.pend[k].shrink_to_fit(); }
  void readAll(Cand& c) { for (int k = 0; k < c.nFields; ++k) readField(c, k); }
  void reachInd(int i);
  void reach(u32 n) {
    if (n >= live.size() || live[n]) return;
    live[n] = 1; ++nLive;
    auto it = decls.find(n); if (it == decls.end()) return;
    Decl& d = it->second;
    if (d.kind == 'I') { reachInd(d.ind); return; }
    if (d.kind == 'C') { reachInd(indOf[ctors[d.ind].induct]); return; }
    if (d.kind == 'R') { Rec& r = recs[d.ind]; push(r.type); for (u32 x : r.rhs) push(x); for (u32 a : r.all) reach(a);
      auto c = candOfRec.find(n); if (fieldMode && c != candOfRec.end()) readAll(cands[c->second]); return; }
    push(d.type); push(d.value);
  }
  void ctorType(Cand* c, Ctor& ct) {  // push ctor type, holding back field binder types
    u32 e = ct.type; int i = 0;
    while (e != NONE && ek[e] == PI) {
      u32 ty = ea[e];
      if (c && fieldMode && i >= ct.nParams && i - ct.nParams < ct.nFields && !c->read[i - ct.nParams]) c->pend[i - ct.nParams].push_back(ty);
      else push(ty);
      e = eb[e]; ++i;
    }
    push(e);
  }
  void run() {
    while (!st.empty()) {
      u32 e = st.back(); st.pop_back();
      if (seen(e)) continue;
      switch (ek[e]) {
        case CONST: reach(ea[e]);
          if (fieldMode) { auto c = candOfCtor.find(ea[e]); if (c != candOfCtor.end()) readAll(cands[c->second]); }  // bare constructor
          break;
        case APP: {
          static thread_local vector<u32> args; args.clear(); u32 h = e;
          while (ek[h] == APP) { args.push_back(eb[h]); h = ea[h]; }
          reverse(args.begin(), args.end());
          int ci = -1; if (fieldMode && ek[h] == CONST) { auto c = candOfCtor.find(ea[h]); if (c != candOfCtor.end()) ci = c->second; }
          if (ci >= 0 && (int)args.size() == cands[ci].nParams + cands[ci].nFields) {
            Cand& c = cands[ci]; reach(ea[h]);
            for (int k = 0; k < (int)args.size(); ++k) {
              int f = k - c.nParams;
              if (f < 0 || c.read[f]) push(args[k]); else c.pend[f].push_back(args[k]);
            }
          } else { push(h); for (u32 a : args) push(a); }
          break; }
        case LAM: case PI: push(ea[e]); push(eb[e]); break;
        case LET: push(ea[e]); push(eb[e]); push(letBody[letIdx[e]]); break;
        case PROJ: { push(ea[e]); auto& pi = projInfo[eb[e]]; reach(pi.first);
          if (fieldMode) { auto c = candOfInd.find(pi.first); if (c != candOfInd.end() && (int)pi.second < cands[c->second].nFields) readField(cands[c->second], pi.second); }
          break; }
        case MDATA: push(ea[e]); break;
        default: break;
      }
    }
  }
};
void Run::reachInd(int i) {
  Ind& I = inds[i];
  if (!live[I.name]) { live[I.name] = 1; ++nLive; }
  static unordered_set<int> done[2]; if (done[fieldMode].count(i)) return; done[fieldMode].insert(i);
  push(I.type);
  for (u32 a : I.all) if (a != I.name) reach(a);
  for (u32 cn : I.ctors) {
    if (!live[cn]) { live[cn] = 1; ++nLive; }
    Ctor& ct = ctors[ctorOf[cn]];
    auto c = candOfCtor.find(cn);
    ctorType(c != candOfCtor.end() ? &cands[c->second] : nullptr, ct);
  }
}

// loose bvars of an expression (small DAGs only: constructor field types)
void loose(u32 e, int depth, vector<int>& out, int budget, int& used) {
  if (e == NONE || ++used > budget) return;
  switch (ek[e]) {
    case BVAR: if ((int)ea[e] >= depth) out.push_back(ea[e] - depth); break;
    case APP: loose(ea[e], depth, out, budget, used); loose(eb[e], depth, out, budget, used); break;
    case LAM: case PI: loose(ea[e], depth, out, budget, used); loose(eb[e], depth + 1, out, budget, used); break;
    case LET: loose(ea[e], depth, out, budget, used); loose(eb[e], depth, out, budget, used); loose(letBody[letIdx[e]], depth + 1, out, budget, used); break;
    case PROJ: case MDATA: loose(ea[e], depth, out, budget, used); break;
    default: break;
  }
}

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: fieldlive PROJECT_INDUCTIVES OUTDIR [ROOT...]\n"); return 2; }
  unordered_set<string> projInd; { ifstream f(argv[1]); string s; while (getline(f, s)) if (!s.empty()) projInd.insert(s); }
  string outdir = argv[2];
  vector<string> roots; for (int i = 3; i < argc; ++i) roots.push_back(argv[i]);
  if (roots.empty()) roots = {"riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"};
  namePre.push_back(NONE); nameStr.push_back(""); nameNum.push_back(-1); levelZero.push_back(1);
  JP J; string line; line.reserve(1 << 20);
  static char buf[1 << 22]; size_t lines = 0; u32 maxE = 0;
  auto setName = [&](size_t i) { if (namePre.size() <= i) { namePre.resize(i + 1, NONE); nameStr.resize(i + 1); nameNum.resize(i + 1, -1); } };
  while (true) {
    line.clear();
    for (;;) { if (!fgets(buf, sizeof buf, stdin)) break; line.append(buf); if (!line.empty() && line.back() == '\n') break; }
    if (line.empty()) break;
    if (++lines % 100000000 == 0) fprintf(stderr, "%zu lines, %u exprs\n", lines, maxE);
    int r = J.parse(line.data(), line.data() + line.size());
    int c;
    if ((c = J.get(r, "ie")) >= 0) {
      u32 id = J.v[c].n; ek.ensure(id); ea.ensure(id); eb.ensure(id); en.ensure(id); if (id + 1 > maxE) maxE = id + 1;
      ea[id] = NONE; eb[id] = NONE;
      int x;
      if ((x = J.get(r, "app")) >= 0) { ek[id] = APP; ea[id] = J.num(x, "fn"); eb[id] = J.num(x, "arg"); }
      else if ((x = J.get(r, "const")) >= 0) { ek[id] = CONST; ea[id] = J.num(x, "name"); }
      else if ((x = J.get(r, "lam")) >= 0 || (x = J.get(r, "forallE")) >= 0) { ek[id] = J.v[x].k == "lam" ? LAM : PI; ea[id] = J.num(x, "type"); eb[id] = J.num(x, "body"); en[id] = J.num(x, "name"); }
      else if ((x = J.get(r, "bvar")) >= 0) { ek[id] = BVAR; ea[id] = J.v[x].n; }
      else if ((x = J.get(r, "sort")) >= 0) { ek[id] = SORT; ea[id] = J.v[x].n; }
      else if ((x = J.get(r, "letE")) >= 0) { ek[id] = LET; ea[id] = J.num(x, "type"); eb[id] = J.num(x, "value"); letIdx[id] = letBody.size(); letBody.push_back(J.num(x, "body")); }
      else if ((x = J.get(r, "proj")) >= 0) { ek[id] = PROJ; ea[id] = J.num(x, "struct"); eb[id] = projInfo.size(); projInfo.push_back({(u32)J.num(x, "typeName"), (u32)J.num(x, "idx")}); }
      else if ((x = J.get(r, "mdata")) >= 0) { ek[id] = MDATA; ea[id] = J.num(x, "expr"); }
      else ek[id] = LIT;
    } else if ((c = J.get(r, "in")) >= 0) {
      size_t id = J.v[c].n; setName(id); int x;
      if ((x = J.get(r, "str")) >= 0) { namePre[id] = J.num(x, "pre"); nameStr[id] = string(J.v[J.get(x, "str")].s); }
      else if ((x = J.get(r, "num")) >= 0) { namePre[id] = J.num(x, "pre"); nameNum[id] = J.num(x, "i"); }
    } else if ((c = J.get(r, "il")) >= 0) {
      size_t id = J.v[c].n; if (levelZero.size() <= id) levelZero.resize(id + 1, 0); levelZero[id] = 0;
    } else {
      int x;
      const char* simple[] = {"thm", "def", "opaque", "axiom", "quot"}; const char kinds[] = {'t', 'd', 'o', 'a', 'q'};
      bool done = false;
      for (int i = 0; i < 5; ++i) if ((x = J.get(r, simple[i])) >= 0) {
        long long v = J.num(x, "value"); decls[J.num(x, "name")] = Decl{kinds[i], (u32)J.num(x, "type"), v < 0 ? NONE : (u32)v, -1}; done = true; break; }
      if (!done && (x = J.get(r, "inductive")) >= 0) {
        int ts = J.get(x, "types"), cs = J.get(x, "ctors"), rs = J.get(x, "recs");
        vector<u32> all; for (int t = J.v[ts].first; t >= 0; t = J.v[t].next) all.push_back(J.num(t, "name"));
        for (int t = J.v[ts].first; t >= 0; t = J.v[t].next) {
          Ind I; I.name = J.num(t, "name"); I.type = J.num(t, "type"); I.nParams = J.num(t, "numParams"); I.nIdx = J.num(t, "numIndices");
          int ir = J.get(t, "isRec"); I.isRec = ir >= 0 && J.v[ir].n; I.all = all;
          for (int k = J.v[J.get(t, "ctors")].first; k >= 0; k = J.v[k].next) I.ctors.push_back(J.v[k].n);
          indOf[I.name] = inds.size(); decls[I.name] = Decl{'I', I.type, NONE, (int)inds.size()}; inds.push_back(I);
        }
        for (int t = J.v[cs].first; t >= 0; t = J.v[t].next) {
          Ctor C; C.name = J.num(t, "name"); C.type = J.num(t, "type"); C.induct = J.num(t, "induct"); C.nParams = J.num(t, "numParams"); C.nFields = J.num(t, "numFields");
          ctorOf[C.name] = ctors.size(); decls[C.name] = Decl{'C', C.type, NONE, (int)ctors.size()}; ctors.push_back(C);
        }
        for (int t = J.v[rs].first; t >= 0; t = J.v[t].next) {
          Rec R; R.name = J.num(t, "name"); R.type = J.num(t, "type"); R.all = all;
          int ru = J.get(t, "rules"); if (ru >= 0) for (int k = J.v[ru].first; k >= 0; k = J.v[k].next) R.rhs.push_back(J.num(k, "rhs"));
          recOf[R.name] = recs.size(); decls[R.name] = Decl{'R', R.type, NONE, (int)recs.size()}; recs.push_back(R);
        }
      }
    }
  }
  fprintf(stderr, "parsed %zu lines, %u exprs, %zu names, %zu decls, %zu inductives\n", lines, maxE, namePre.size(), decls.size(), inds.size());

  // candidates
  for (size_t i = 0; i < inds.size(); ++i) {
    Ind& I = inds[i];
    if (I.ctors.size() != 1 || I.nIdx != 0 || I.isRec || I.all.size() != 1) continue;
    if (!projInd.count(fullName(I.name))) continue;
    Cand c; c.ind = i; c.ctor = ctorOf[I.ctors[0]]; Ctor& ct = ctors[c.ctor]; c.nParams = ct.nParams; c.nFields = ct.nFields;
    if (c.nFields == 0) continue;
    u32 t = I.type; while (ek[t] == PI) t = eb[t]; c.prop = ek[t] == SORT && ea[t] < levelZero.size() && levelZero[ea[t]];
    c.read.assign(c.nFields, 0); c.pend.assign(c.nFields, {});
    // field names; fields whose later field types mention them count as read
    u32 e = ct.type; int k = 0; vector<u32> ftypes;
    while (ek[e] == PI) { if (k >= c.nParams) { /* binder name not stored; use index */ ftypes.push_back(ea[e]); } e = eb[e]; ++k; }
    for (int f = 0; f < (int)ftypes.size(); ++f) {
      vector<int> lb; int used = 0; loose(ftypes[f], 0, lb, 2000000, used);
      if (used > 2000000) { for (int g = 0; g < f; ++g) c.read[g] = 1; continue; }  // too big: be conservative
      for (int b : lb) { int g = f - 1 - b; if (g >= 0 && g < f) c.read[g] = 1; }
    }
    int ci = cands.size(); candOfInd[I.name] = ci; candOfCtor[ct.name] = ci;
    for (auto& r : recs) if (!r.all.empty() && r.all[0] == I.name) candOfRec[r.name] = ci;
    cands.push_back(move(c));
  }
  fprintf(stderr, "candidate structures: %zu\n", cands.size());
  // field names from projection functions: value = fun params self => self.i
  for (auto& c : cands) { c.fieldNames.assign(c.nFields, "");
    u32 e = ctors[c.ctor].type; int k = 0;
    while (ek[e] == PI) { if (k >= c.nParams && k - c.nParams < c.nFields) c.fieldNames[k - c.nParams] = fullName(en[e]); e = eb[e]; ++k; } }
  for (auto& kv : decls) {
    Decl& d = kv.second; if (d.value == NONE || (d.kind != 'd' && d.kind != 't')) continue;
    u32 v = d.value; while (ek[v] == LAM) v = eb[v];
    if (ek[v] != PROJ || ek[ea[v]] != BVAR || ea[ea[v]] != 0) continue;
    auto& pi = projInfo[eb[v]]; auto c = candOfInd.find(pi.first);
    if (c == candOfInd.end() || (int)pi.second >= cands[c->second].nFields) continue;
    if (namePre[kv.first] == pi.first && nameNum[kv.first] < 0) cands[c->second].fieldNames[pi.second] = nameStr[kv.first];
  }

  // FIELDLIVE_ONLY=file of "Structure<TAB>field" lines: only those fields may be dropped
  if (const char* only = getenv("FIELDLIVE_ONLY")) {
    unordered_set<string> allow; ifstream f(only); string s; while (getline(f, s)) if (!s.empty()) allow.insert(s);
    size_t kept = 0;
    for (auto& c : cands) for (int k = 0; k < c.nFields; ++k) {
      if (allow.count(fullName(inds[c.ind].name) + "\t" + c.fieldNames[k])) ++kept; else c.read[k] = 1; }
    fprintf(stderr, "FIELDLIVE_ONLY: %zu fields may be dropped\n", kept);
  }

  vector<u32> rootIds;
  for (auto& kv : decls) { string s = fullName(kv.first); for (auto& r : roots) if (s == r) rootIds.push_back(kv.first); }
  fprintf(stderr, "roots found: %zu of %zu\n", rootIds.size(), roots.size());

  size_t nNames = namePre.size(); size_t nE = maxE;
  vector<char> liveBase;
  { Run R; R.fieldMode = false; R.live.assign(nNames, 0); R.vis.assign(nE / 64 + 1, 0); for (u32 r : rootIds) R.reach(r); R.run(); liveBase = R.live; fprintf(stderr, "baseline live constants: %zu\n", R.nLive); }
  vector<char> pendingRecorded(cands.size(), 0);
  Run R; R.fieldMode = true; R.live.assign(nNames, 0); R.vis.assign(nE / 64 + 1, 0); for (u32 r : rootIds) R.reach(r); R.run();
  fprintf(stderr, "field-mode live constants: %zu\n", R.nLive);

  // outputs
  FILE* df = fopen((outdir + "/dead-fields.tsv").c_str(), "w");
  fprintf(df, "structure\tfield\tprop\tfield_index\tnum_fields\tconstructor_sites_held\n");
  size_t deadFields = 0, deadStructs = 0;
  for (auto& c : cands) {
    if (!R.live[inds[c.ind].name]) continue;
    bool any = false;
    for (int k = 0; k < c.nFields; ++k) if (!c.read[k]) { ++deadFields; any = true;
      fprintf(df, "%s\t%s\t%d\t%d\t%d\t%zu\n", fullName(inds[c.ind].name).c_str(), c.fieldNames[k].c_str(), c.prop, k, c.nFields, c.pend[k].size()); }
    deadStructs += any;
  }
  fclose(df);
  FILE* dr = fopen((outdir + "/dropped-constants.txt").c_str(), "w"); size_t dropped = 0;
  for (size_t n = 0; n < nNames; ++n) if (liveBase[n] && !R.live[n] && decls.count(n)) { ++dropped; fprintf(dr, "%s\n", fullName(n).c_str()); }
  fclose(dr);
  fprintf(stderr, "dead fields: %zu in %zu live structures; constants dropped: %zu\n", deadFields, deadStructs, dropped);
  // per dead field: the dropped constants reachable from what it holds back
  FILE* fa = fopen((outdir + "/field-reach.tsv").c_str(), "w");
  for (auto& c : cands) {
    if (!R.live[inds[c.ind].name]) continue;
    for (int k = 0; k < c.nFields; ++k) if (!c.read[k]) {
      unordered_set<u32> vis, got; vector<u32> st(c.pend[k].begin(), c.pend[k].end());
      while (!st.empty()) {
        u32 e = st.back(); st.pop_back(); if (e == NONE || !vis.insert(e).second) continue;
        switch (ek[e]) {
          case CONST: { u32 n = ea[e];
            if (n < liveBase.size() && liveBase[n] && !R.live[n] && got.insert(n).second) {
              auto it = decls.find(n);
              if (it != decls.end()) { st.push_back(it->second.type); st.push_back(it->second.value);
                if (it->second.kind == 'I') for (u32 cn : inds[it->second.ind].ctors) st.push_back(ctors[ctorOf[cn]].type); } }
            break; }
          case APP: case LAM: case PI: st.push_back(ea[e]); st.push_back(eb[e]); break;
          case LET: st.push_back(ea[e]); st.push_back(eb[e]); st.push_back(letBody[letIdx[e]]); break;
          case PROJ: case MDATA: st.push_back(ea[e]); break;
          default: break;
        }
      }
      fprintf(fa, "%s\t%s\t%zu\t", fullName(inds[c.ind].name).c_str(), c.fieldNames[k].c_str(), got.size());
      bool first = true; for (u32 n : got) { fprintf(fa, first ? "%s" : ";%s", fullName(n).c_str()); first = false; }
      fprintf(fa, "\n");
    }
  }
  fclose(fa);
  printf("dead_fields\t%zu\ndead_structs\t%zu\ndropped_constants\t%zu\n", deadFields, deadStructs, dropped);
  return 0;
}
