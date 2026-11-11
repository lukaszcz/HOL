#!/usr/bin/env python3
"""A canonical form of a HOL4 theory `.dat` file (TASK32 behavior compare).

A `.dat` file is an s-expression (HOLsexp) holding a theory's name, parents
with their hashes, sharing tables (strings, identifiers, types, terms) and
the theory's exports, new signature and loadable theory data (format of
src/portableML/rawtheory/RawTheoryReader.sml). Two builds of one theory can
serialize it with differently ordered tables. The canonical form resolves
every table index to a structural value, so only the content is compared:

  - types and terms become Merkle digests of their structure (a variable's
    type, a constant's identifier and type, application, abstraction);
  - encoded terms (theorem conclusions and hypotheses, exported terms,
    `tag-tm` theory data) are decoded with the `write_raw` rules of
    src/portableML/rawtheory/RawTermPP.sml and resolved the same way;
  - theorem names, dependencies, tags, class, privacy, locations, the new
    signature and the exports are kept in full and in order;
  - the loadable theory data is kept in full and every ThyDataSexp tag is
    resolved through the tables: both fields of `tag-knm`, `tag-str`,
    `tag-tm`, `tag-ty` and the encoded terms of `tag-th`. Data that this
    module cannot attribute to a tag - any integer or untagged string left
    in it, as written by an unknown or custom writer (grammar ancestry,
    split data, ...) - may be a table index. For such a file the canonical
    form also holds the ordered full string, identifier, type and term
    tables (`fallback`), so an index it cannot resolve can only make two
    equal files differ, never hide a difference.

A parent's hash is the only field that may be masked (`<MASK>`), and only
by the caller, for a parent that itself compared equal. Any parse failure
raises Failure.
"""
import hashlib
import json
import re

MASK = "<MASK>"
CLASSES = {0: "Axm", 1: "Def", 2: "Thm"}


class Failure(ValueError):
    """The file is not a theory this module understands."""


class Sym(str):
    pass


class Dot:
    """`(a b . tail)` with a tail that is not a list."""

    def __init__(self, items, tail):
        self.items, self.tail = items, tail


TOKEN = re.compile(
    r'(?P<ws>\s+|;[^\n]*)|(?P<lp>\()|(?P<rp>\))|(?P<dot>\.)'
    r'|"(?P<str>(?:[^"\\\n]|\\(?:[0-9]{3}|\^.|.))*)"'
    r'|\|(?P<qsym>(?:[^|\\\n]|\\\||\\n)*)\|'
    r'|(?P<atom>[-%+*_A-Za-z0-9]+)')
ESCAPE = re.compile(r'\\([0-9]{3}|\^.|.)')
SIMPLE = {'"': '"', "a": "\a", "b": "\b", "f": "\f", "n": "\n",
          "r": "\r", "t": "\t", "\\": "\\"}


def unescape(text):
    def one(m):
        body = m.group(1)
        if body.isdigit():
            return chr(int(body))
        if body[0] == "^":
            return chr(ord(body[1]) - 64)
        if body in SIMPLE:
            return SIMPLE[body]
        raise Failure("bad escape \\" + body)
    return ESCAPE.sub(one, text)


def parse_sexp(text):
    """Python value of an s-expression: int, str, Sym, list (a proper
    list; the symbol nil is the empty list) or Dot."""
    stack, result, pos = [], None, 0
    # each frame: [items, dotted?, tail]
    done = False

    def put(value):
        nonlocal result, done
        if not stack:
            if done:
                raise Failure("trailing data")
            result, done = value, True
            return
        frame = stack[-1]
        if frame[1]:
            if frame[2] is not None:
                raise Failure("bad dotted list")
            frame[2] = value
        else:
            frame[0].append(value)

    while pos < len(text):
        m = TOKEN.match(text, pos)
        if m is None:
            raise Failure("bad character at %d" % pos)
        pos, kind = m.end(), m.lastgroup
        if kind == "ws":
            continue
        if kind == "lp":
            stack.append([[], False, None])
        elif kind == "rp":
            if not stack:
                raise Failure("unbalanced )")
            items, dotted, tail = stack.pop()
            if dotted:
                if tail is None or not items:
                    raise Failure("bad dotted list")
                value = items if tail == [] else Dot(items, tail)
            else:
                value = items
            put(value)
        elif kind == "dot":
            if not stack or stack[-1][1] or not stack[-1][0]:
                raise Failure("bad dot")
            stack[-1][1] = True
        elif kind == "str":
            put(unescape(m.group("str")))
        elif kind == "qsym":
            put(Sym(m.group("qsym").replace("\\|", "|")
                    .replace("\\n", "\n")))
        else:
            atom = m.group("atom")
            if re.fullmatch(r"[-+]?[0-9]+", atom):
                put(int(atom))
            elif atom == "nil":
                put([])
            else:
                put(Sym(atom))
    if stack or not done:
        raise Failure("unbalanced (")
    return result


# -- decoding helpers, mirroring HOLsexp's pair/tagged decoders ---------

def car_cdr(x):
    if isinstance(x, list) and x:
        return x[0], x[1:]
    if isinstance(x, Dot):
        rest = x.items[1:]
        return x.items[0], (Dot(rest, x.tail) if rest else x.tail)
    raise Failure("expected a pair")


def as_list(x):
    if not isinstance(x, list):
        raise Failure("expected a list")
    return x


def tagged(tag, x):
    car, cdr = car_cdr(x)
    if car != tag or not isinstance(car, Sym):
        raise Failure("expected tag " + tag)
    return cdr


def pair_n(x, n):
    """The n components of (a (b (c ... (z)))), the last one single."""
    out = []
    for _ in range(n - 1):
        car, x = car_cdr(x)
        out.append(car)
    x = as_list(x)
    if len(x) != 1:
        raise Failure("expected a singleton")
    return out + [x[0]]


def integer(x):
    if not isinstance(x, int) or isinstance(x, bool):
        raise Failure("expected an integer")
    return x


def string(x):
    if not isinstance(x, str) or isinstance(x, Sym):
        raise Failure("expected a string")
    return x


def int_pair(x):
    a, b = car_cdr(x)
    return integer(a), b


def node(*parts):
    return hashlib.sha256(json.dumps(
        parts, separators=(",", ":")).encode()).hexdigest()


# -- terms -----------------------------------------------------------

LEX = re.compile(r"\||%(\d+)|\$(\d+)|U(\d+)|u(\d+)|B(\d+)|b(\d+)|@(\d*)")


class Tables:
    def __init__(self, strings, ids, types, terms):
        self.strings = strings
        self.ids = []
        for a, b in ids:
            self.ids.append([self.s(a), self.s(b)])
        self.types = []
        for entry in types:
            self.types.append(self.type_of(entry))
        self.terms = []
        for entry in terms:
            self.terms.append(self.term_of(entry))

    def s(self, i):
        if not 0 <= integer(i) < len(self.strings):
            raise Failure("string index out of range")
        return self.strings[i]

    def ident(self, i):
        if not 0 <= integer(i) < len(self.ids):
            raise Failure("identifier index out of range")
        return self.ids[i]

    def ty(self, i, limit=None):
        limit = len(self.types) if limit is None else limit
        if not 0 <= integer(i) < limit:
            raise Failure("type index out of range")
        return self.types[i]

    def type_of(self, entry):
        if isinstance(entry, str) and not isinstance(entry, Sym):
            return node("tyv", entry)
        args = [integer(i) for i in as_list(entry)]
        if not args:
            raise Failure("empty type entry")
        return node("tyop", self.ident(args[0]),
                    [self.ty(i) for i in args[1:]])

    def tm(self, i):
        if not 0 <= integer(i) < len(self.terms):
            raise Failure("term index out of range")
        return self.terms[i]

    def term_of(self, entry):
        items = as_list(entry)
        if len(items) == 2 and isinstance(items[0], str) and \
                not isinstance(items[0], Sym):
            return node("var", items[0], self.ty(items[1]))
        if len(items) == 2:
            return node("const", self.ident(items[0]), self.ty(items[1]))
        if len(items) == 3 and items[0] in ("ap", "ab"):
            return node(items[0], self.tm(items[1]), self.tm(items[2]))
        raise Failure("bad term entry")

    def decode(self, text):
        """The digest of a write_raw encoded term."""
        stack, pos = [], 0

        def pop(n):
            if len(stack) < n:
                raise Failure("encoded term: stack underflow")
            out = stack[len(stack) - n:]
            del stack[len(stack) - n:]
            return out

        while pos < len(text):
            m = LEX.match(text, pos)
            if m is None:
                raise Failure("encoded term: bad character")
            pos, token = m.end(), m.group(0)
            kind = token[0]
            if kind == "|":
                bv, body = pop(2)
                stack.append(node("abs", bv, body))
            elif kind == "%":
                stack.append(self.tm(int(m.group(1))))
            elif kind == "$":
                stack.append(node("bv", int(m.group(2))))
            elif kind == "U":
                (t,) = pop(1)
                stack.append(node("ap", self.tm(int(m.group(3))), t))
            elif kind == "u":
                (t,) = pop(1)
                stack.append(node("ap", node("bv", int(m.group(4))), t))
            elif kind == "B":
                t1, t2 = pop(2)
                stack.append(node("ap", node("ap", self.tm(
                    int(m.group(5))), t1), t2))
            elif kind == "b":
                t1, t2 = pop(2)
                stack.append(node("ap", node("ap", node(
                    "bv", int(m.group(6))), t1), t2))
            else:
                count = int(m.group(7)) if m.group(7) else 1
                args = pop(count)
                (f,) = pop(1)
                for arg in args:
                    f = node("ap", f, arg)
                stack.append(f)
        if len(stack) != 1:
            raise Failure("encoded term: not exactly one term")
        return stack[0]


def plain(x):
    """A JSON-able copy of an s-expression that resolves nothing."""
    if isinstance(x, list):
        return ["l"] + [plain(i) for i in x]
    if isinstance(x, Dot):
        return ["d", [plain(i) for i in x.items], plain(x.tail)]
    if isinstance(x, Sym):
        return ["s", str(x)]
    return ["i", x] if isinstance(x, int) else ["t", x]


class ThyData:
    """Resolution of the ThyDataSexp tags; `unresolved` is set when an
    integer or untagged string remains that might be a table index."""

    def __init__(self, tables):
        self.tables = tables
        self.unresolved = False

    def value(self, x):
        t = self.tables
        if isinstance(x, Dot):
            head, tail = x.items, x.tail
            tag = head[0] if len(head) == 1 and \
                isinstance(head[0], Sym) else None
            if tag in ("tag-tm", "tag-ty") and isinstance(tail, str) and \
                    not isinstance(tail, Sym):
                return [tag, t.decode(tail)]
            if tag == "tag-str" and isinstance(tail, int):
                return [tag, t.s(tail)]
            if tag == "tag-ch" and isinstance(tail, int):
                return [tag, tail]
            if len(head) == 2 and head[0] == "tag-knm" and \
                    isinstance(head[0], Sym) and \
                    isinstance(head[1], int) and isinstance(tail, int):
                return ["tag-knm", t.s(head[1]), t.s(tail)]
            return ["d", [self.value(i) for i in head], self.value(tail)]
        if isinstance(x, list):
            if len(x) == 5 and x[0] == "tag-th" and isinstance(x[0], Sym) \
                    and isinstance(x[2], list) and isinstance(x[4], int) \
                    and isinstance(x[3], str):
                return ["tag-th", plain(x[1]),
                        [t.decode(string(i)) for i in x[2]], x[3], x[4]]
            return ["l"] + [self.value(i) for i in x]
        if isinstance(x, Sym):
            return ["s", str(x)]
        self.unresolved = True
        return ["i", x] if isinstance(x, int) else ["t", x]

    def entries(self, x):
        out = []
        for entry in as_list(x):
            name, rest = car_cdr(entry)
            out.append([string(name), self.value(rest)])
        return out


def theorem(x, tables):
    i, deptag, info, terms = pair_n(x, 4)
    deps, tags = car_cdr(deptag)
    deps = [(integer(n), [integer(j) for j in as_list(js)])
            for n, js in (car_cdr(d) for d in as_list(deps))]
    if not deps or len(deps[0][1]) != 1:
        raise Failure("bad theorem dependencies")
    info = [integer(j) for j in as_list(info)]
    if len(info) < 2 or info[0] not in CLASSES:
        raise Failure("bad theorem info")
    loc = None if len(info) == 2 else {
        "exact": info[2] != 0 if len(info) > 2 else None,
        "line": info[3] if len(info) > 3 else None,
        "path": [tables.s(j) for j in info[4:]]}
    if len(info) == 3:
        raise Failure("bad theorem location")
    terms = [tables.decode(string(t)) for t in as_list(terms)]
    if not terms:
        raise Failure("theorem without a conclusion")
    return {"name": tables.s(i),
            "me": [tables.s(deps[0][0]), deps[0][1][0]],
            "deps": [[tables.s(n), js] for n, js in deps[1:]],
            "tags": [string(t) for t in as_list(tags)],
            "class": CLASSES[info[0]], "private": info[1] != 0,
            "loc": loc, "concl": terms[0], "hyps": terms[1:]}


def canonical(text):
    """The canonical dict of the text of a `.dat` file."""
    top = tagged("theory", parse_sexp(text))
    parentage, rest = car_cdr(top)
    name, parents = car_cdr(parentage)
    parents = [[string(t), string(h)] for t, h in
               (car_cdr(p) for p in as_list(parents))]
    core, incorporate, loadable = pair_n(rest, 3)
    tables_part, exports_part = car_cdr(tagged("core-data", core))
    st, idt, tyt, tmt = pair_n(tagged("tables", tables_part), 4)
    tables = Tables(
        [string(s) for s in as_list(tagged("string-table", st))],
        [(integer(a), integer(b)) for a, b in
         (car_cdr(p) for p in as_list(tagged("id-table", idt)))],
        as_list(tagged("type-table", tyt)),
        as_list(tagged("term-table", tmt)))
    types, terms, thms = pair_n(tagged("exports", exports_part), 3)
    utys, ntys = car_cdr(types)
    utms, ntms = car_cdr(terms)
    inc_types, inc_consts = car_cdr(tagged("incorporate", incorporate))
    newtypes = [[string(n), integer(a)] for n, a in
                (car_cdr(p) for p in as_list(tagged("incorporate-types",
                                                    inc_types)))]
    newconsts = [[string(n), tables.ty(integer(t))] for n, t in
                 (car_cdr(p) for p in as_list(tagged("incorporate-consts",
                                                     inc_consts)))]
    data = ThyData(tables)
    resolved = data.entries(tagged("loadable-thydata", loadable))
    return {
        "name": string(name), "parents": parents,
        "unnamed_types": [tables.ty(i) for i in as_list(utys)],
        "named_types": [[string(n), tables.ty(integer(t))] for n, t in
                        (car_cdr(p) for p in as_list(ntys))],
        "unnamed_terms": [tables.decode(string(t)) for t in as_list(utms)],
        "named_terms": [[string(n), tables.decode(string(t))] for n, t in
                        (car_cdr(p) for p in as_list(ntms))],
        "thms": [theorem(t, tables) for t in as_list(thms)],
        "newsig": {"types": newtypes, "consts": newconsts},
        "thydata": resolved, "fallback": data.unresolved,
        "tables": {"strings": tables.strings, "ids": tables.ids,
                   "types": tables.types, "terms": tables.terms}
        if data.unresolved else None}


def digest(canon, equal_parents=()):
    """(sha256 of the canonical dict, the parents whose hash was masked):
    the hash of a parent named in `equal_parents` becomes MASK."""
    masked = [t for t, _ in canon["parents"] if t in equal_parents]
    shown = dict(canon, parents=[[t, MASK if t in equal_parents else h]
                                 for t, h in canon["parents"]])
    text = json.dumps(shown, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(text.encode()).hexdigest(), masked
