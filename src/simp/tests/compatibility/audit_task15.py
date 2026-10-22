#!/usr/bin/env python3
"""Bounded, offline TASK_15 fragment representation/construction audit.

Compare SML tokens (not whitespace-stripped text) with pinned develop. Nested
comments and strings are lexed separately. This is a structural gate, not an
SML type checker, execution test, or a claim about TASK_16 simpset storage.
The temporary compiled companions/ordinals are allowed only at installation;
ordinary fragment routes must be baseline code. Extension sources are frozen
at task-start HEAD, independently of the ordinary restoration.
"""
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
SRC = 'src/simp/src/'
BASE = 'cccaa27d7099cbadc886983020cbe745db7793f3'
START = '1cb8802770fb9e291951b8a1bd7d4bd1a529bb80'
FILES = tuple(SRC + name for name in (
    'simpLib.sml', 'simpLib.sig', 'simpExtLib.sml', 'simpExtLib.sig'))
WORD = re.compile(r"[A-Za-z_][A-Za-z_0-9']*|'[A-Za-z_0-9']+")
SYMBOL = re.compile(r'[!%&$#+\-/:<=>?@\\~`^|*]+')
NUMBER = re.compile(r'~?[0-9]+(?:\.[0-9]+)?')


def require(condition, message):
    if not condition:
        raise AssertionError(message)


@lru_cache(maxsize=None)
def git_source(revision, path):
    return subprocess.check_output(
        ['git', '-C', str(ROOT), 'show', revision + ':' + path],
        text=True)


def tokens(text):
    """Small fail-closed SML lexer; retain literals and token boundaries."""
    result = []
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith('(*', i):
            depth = 1
            i += 2
            while depth and i < len(text):
                if text.startswith('(*', i):
                    depth += 1
                    i += 2
                elif text.startswith('*)', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, 'unterminated SML comment')
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\\':
                    i += 1
                    # SML string gaps may contain arbitrary whitespace.
                    if i < len(text) and text[i].isspace():
                        while i < len(text) and text[i].isspace():
                            i += 1
                        require(i < len(text) and text[i] == '\\',
                                'unterminated SML string gap')
                i += 1
            require(i < len(text), 'unterminated SML string')
            i += 1
            result.append(text[start:i])
        else:
            match = WORD.match(text, i) or NUMBER.match(text, i)
            match = match or SYMBOL.match(text, i)
            if match:
                result.append(match.group())
                i = match.end()
            else:
                require(text[i] in '(){}[],;.',
                        'unrecognized SML token: ' + repr(text[i:i+20]))
                result.append(text[i])
                i += 1
    return result


def positions(seq, needle):
    return [i for i in range(len(seq) - len(needle) + 1)
            if seq[i:i+len(needle)] == needle]


def locate(seq, text):
    needle = tokens(text)
    found = positions(seq, needle)
    require(len(found) == 1, 'missing/ambiguous anchor: ' + text)
    return found[0]


def part(seq, start, stop):
    a, b = locate(seq, start), locate(seq, stop)
    require(a < b, 'reversed anchors: ' + start)
    return seq[a:b]


def replace_once(seq, old, new):
    old, new = tokens(old), tokens(new)
    found = positions(seq, old)
    require(len(found) == 1, 'missing/ambiguous replacement: ' + str(old))
    a = found[0]
    return seq[:a] + new + seq[a+len(old):]


def record(seq):
    """Exact top-level record fields, allowing only field-order changes."""
    require(seq[0] == '{' and seq[-1] == '}', 'expected record')
    fields = {}
    start, depth = 1, 0
    for i in range(1, len(seq)):
        t = seq[i]
        if (t == ',' and depth == 0) or i == len(seq)-1:
            field = seq[start:i]
            require(len(field) >= 3 and field[1] == '=',
                    'non-explicit record field')
            require(field[0] not in fields, 'duplicate record field')
            fields[field[0]] = field[2:]
            start = i + 1
        if t in ('{', '(', '['):
            depth += 1
        elif t in ('}', ')', ']'):
            depth -= 1
    return fields


def constructor_apps(seq):
    """Inventory every SSFRAG_CON occurrence, including pattern matches."""
    result = Counter()
    for i, t in enumerate(seq):
        if t != 'SSFRAG_CON':
            continue
        j = i + 1
        require(j < len(seq), 'bare SSFRAG_CON')
        if seq[j] == 'of':       # datatype declaration, checked separately
            continue
        if seq[j] != '{':
            result[tuple(seq[i:j+1])] += 1
            continue
        depth = 1
        k = j + 1
        while depth and k < len(seq):
            depth += (seq[k] == '{') - (seq[k] == '}')
            k += 1
        require(depth == 0, 'unclosed constructor record')
        result[tuple(seq[i:k])] += 1
    return result


def binding_inventory(seq):
    # Includes nested declarations: a new lazy companion/table cannot be
    # smuggled in as an extra local declaration or a shadow public function.
    kinds = {'val', 'fun', 'type', 'datatype', 'exception', 'structure'}
    return Counter((t, seq[i+1]) for i, t in enumerate(seq[:-1])
                   if t in kinds)


def sources():
    return tuple((ROOT / path).read_text() for path in FILES)


def audit(simp=None, sig=None, extension=None, extension_sig=None):
    if simp is None:
        simp, sig, extension, extension_sig = sources()
    require(all(isinstance(s, str) for s in
                (simp, sig, extension, extension_sig)), 'missing sources')
    base = tokens(git_source(BASE, FILES[0]))
    start = tokens(git_source(START, FILES[0]))
    ordinary = tokens(simp)
    signature = tokens(sig)
    base_sig = tokens(git_source(BASE, FILES[1]))

    # Do not normalize the extension: all slots, inventories, actual controls,
    # prepared matchers, and separate type identities must remain untouched.
    for path, text in zip(FILES[2:], (extension, extension_sig)):
        require(text == git_source(START, path),
                'extension changed from task-start HEAD: ' + path)
    require('source_slot' not in ordinary + signature,
            'ordinary source_slot survives')
    require(not {'TravrulesExt', 'threaded_congs'}.intersection(ordinary),
            'ordinary threaded-fragment edge survives')
    removed = ('threaded_cong_ss', 'looper_ss', 'solver_ss', 'safe_solver_ss',
               'rewrite_views', 'rewrite_bundle', 'prepare_rewrite_bundle',
               'combine_rewrite_bundles', 'rewrite_bundle_rules',
               'install_rewrite_bundle', 'split_ss',
               'GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND')
    require(not set(removed).intersection(ordinary + signature),
            'extension-only fragment builder survives in ordinary API/body')

    # Preserve the transitional compiler prefix exactly except for separating
    # compiled data from fragment data and deleting ordinary source slots.
    # This also rules out shadow map/helpers and new global companion stores.
    prefix = part(start, 'structure simpLib :>', 'type relsimpdata =')
    prefix = replace_once(
        prefix, "type 'a source_slot = {item : 'a, token : int} "
        'fun source_slot item = {item=item, token=source_token ()}', '')
    prefix = replace_once(prefix, 'type tagged_convdata =',
                          'type compiled_convdata =')
    prefix = replace_once(prefix, ': tagged_convdata option',
                          ': compiled_convdata option')
    prefix = replace_once(
        prefix, 'type stdconvdata =',
        'type tagged_convdata = {thypart : string option, cd : convdata} '
        'type stdconvdata =')
    require(part(ordinary, 'structure simpLib :>', 'type relsimpdata =') ==
            prefix, 'unreviewed compiler prefix/helper/global state')

    # Exact baseline element/record types, not just the absence of old labels.
    for begin, end in (
            ('type convdata =', ';'),
            ('type stdconvdata =', 'fun appconv'),
            ('type relsimpdata =', 'datatype ssfrag')):
        if begin == 'type convdata =':
            a = locate(base, begin)
            b = base.index(';', a)
            c = locate(ordinary, begin)
            d = ordinary.index(';', c)
            require(ordinary[c:d+1] == base[a:b+1], 'convdata changed')
        elif begin == 'type stdconvdata =':
            require(part(ordinary, begin, 'fun appconvs') ==
                    part(base, begin, end), 'stdconvdata changed')
        else:
            require(part(ordinary, begin, 'type conv_info =') ==
                    part(base, begin, end), 'relsimpdata changed')
    require(part(ordinary, 'type tagged_convdata =', 'type stdconvdata =') ==
            tokens('type tagged_convdata = '
                   '{thypart : string option, cd : convdata}'),
            'tagged_convdata must be exactly baseline {thypart,cd:convdata}')
    require(part(ordinary, 'ssfrag = SSFRAG_CON of', 'datatype looper_kind =') ==
            part(base, 'ssfrag = SSFRAG_CON of', 'fun frag_name'),
            'ssfrag fields/element types differ from pinned develop')

    # Seal the entire fragment section, including the named database and all
    # easy/named/std/merge/filter/update routes. No extra ref, paired runner,
    # helper, lazy cell, promotion call or insertion table fits in this seal.
    expected = part(base, 'fun frag_name', 'type conv_info =')
    expected = replace_once(
        expected, 'fun SSFRAG',
        'fun ordinary_looper (name,apply) = '
        'LooperEntry {kind=OrdinaryLooper,name=name,apply=apply} fun SSFRAG')
    expected = replace_once(
        expected, 'local val ssfragDB_slot',
        'fun ssf_filter_rewrs keep = ssf_upd_rewrs (List.filter keep) '
        'local val ssfragDB_slot')
    fragments = part(ordinary, 'fun frag_name', 'val empty_excluded')
    require(fragments == expected,
            'fragment constructors/updates/registration differ from baseline')

    # Public fragment shapes and complete constructor signatures are baseline.
    for begin, end in (('val SSFRAG :', 'val Cong :'),
                       ('val rewrites :', 'type weakener_data =')):
        expected_sig = part(base_sig, begin, end)
        if begin == 'val rewrites :':
            # The mutually recursive mixed compiler needs this abstract type
            # earlier in the signature; its placement is not a fragment API.
            require(expected_sig[-2:] == tokens('type simpset'),
                    'unexpected pinned signature tail')
            expected_sig = expected_sig[:-2]
        require(part(signature, begin, end) == expected_sig,
                'ordinary fragment signature changed: ' + begin)

    # TypeBase is baseline, with one explicitly allowed factoring of its
    # name/conversion expressions and record field order. No arbitrary helper
    # equivalence, stripping of effectful expressions, or callback rewriting.
    old_tyi = part(base, 'fun tyi_to_ssdata', 'fun type_ssfrag')
    factored_tyi = replace_once(
        old_tyi,
        'in SSFRAG_CON {name = SOME("Datatype "^tyname), '
        'convs = map (fn c => {thypart=SOME thy,cd=c}) convs, '
        'rewrs=rewrs, filter=NONE, dprocs=[], ac=[], congs=[], relsimps=[]}',
        'val name = SOME ("Datatype " ^ tyname) '
        'val convs = map (fn c => {thypart=SOME thy,cd=c}) convs '
        'in SSFRAG_CON {name=name, convs=convs, rewrs=rewrs, ac=[], '
        'filter=NONE, dprocs=[], congs=[], relsimps=[]}')
    tyi = part(ordinary, 'fun tyi_to_ssdata', 'fun type_ssfrag')
    require(tyi in (old_tyi, factored_tyi), 'TypeBase construction changed')
    require(part(ordinary, 'fun type_ssfrag', 'val CONSISTENT') ==
            part(base, 'fun type_ssfrag', 'val CONSISTENT'),
            'TypeBase fetch route changed')
    printer = part(ordinary, 'fun dest_convdata', 'fun pp_simpset')
    expected_printer = part(base, 'fun dest_convdata', 'fun pp_simpset')
    expected_printer = [t if t != 'dest_reducer' else 'reducer_data'
                        for t in expected_printer]
    require(printer == expected_printer, 'fragment printing changed')
    printing_tail = ordinary[locate(ordinary, 'val reducer_data ='):]
    require(part(printing_tail, 'val reducer_data =', 'fun merge_names') ==
            tokens('val reducer_data = Traverse.dest_reducer'),
            'printing must use the shared opaque reducer accessor')
    base_tail = base[locate(base, 'val CONSISTENT'):]
    require(part(printing_tail, 'fun merge_names', 'fun dest_convdata') ==
            part(base_tail, 'fun merge_names', 'fun dest_convdata'),
            'printing name merge changed')
    require(part(ordinary, 'val pp_ssfrag =', 'val pp_simpset =') ==
            part(base, 'val pp_ssfrag =', 'val pp_simpset ='),
            'fragment printer wrapper changed')

    # Marker-generated Cong/AC is also a construction route, not installation
    # metadata. Compare every record value with baseline, not selected labels.
    marker = part(ordinary, 'val cong_ac =', 'val withCongAc =')
    base_marker = part(base, 'val cong_ac =', 'val withCongAc =')
    prefix = tokens('val cong_ac = SSFRAG_CON')
    require(marker[:len(prefix)] == base_marker[:len(prefix)] == prefix,
            'Cong/AC constructor wrapper/allocation')
    require(record(marker[len(prefix):]) ==
            record(base_marker[len(prefix):]), 'Cong/AC payload changed')

    # All remaining constructor occurrences must be these destructors/patterns.
    # This closes unnoticed construction paths elsewhere in the mixed compiler.
    covered = fragments + tyi + printer + marker
    residual = constructor_apps(ordinary) - constructor_apps(covered)
    patterns = (
        'SSFRAG_CON {name=SOME n1,...}',
        'SSFRAG_CON {name=SOME n2,...}',
        'SSFRAG_CON ssf',
        'SSFRAG_CON {name=SOME n,...}',
        'SSFRAG_CON {name=NONE,...}',
        'SSFRAG_CON {name=SOME n,...}',
        'SSFRAG_CON {name=NONE,...}',
        'SSFRAG_CON f',
        'SSFRAG_CON {congs,relsimps,...}',
    )
    require(residual == Counter(tuple(tokens(p)) for p in patterns),
            'unreviewed fragment constructor/destructor route')
    require(part(ordinary, 'fun ssfrags_of', 'fun rewrite_source_handles') ==
            tokens('fun ssfrags_of (SS x) = List.mapPartial '
                   '(fn ADDFRAG (sf,_,_,_) => SOME sf | _ => NONE) '
                   '(#history x)'), 'history must return original fragments')
    require(part(ordinary, 'fun same_frag', 'fun ssfrag_names_of') ==
            part(base, 'fun same_frag', 'fun ssfrag_names_of'),
            'duplicate fragment comparison changed')
    require(part(ordinary, 'fun is_excluded', 'fun numbered') ==
            part(start, 'fun is_excluded', 'fun numbered'),
            'fragment exclusion comparison changed')

    # The remaining mixed compiler is deliberately not a fragment constructor.
    # Exact staging prevents interleaved decode/AC/makers/conversions (and
    # conversion before a later throwing maker). Ordinals allocate no tokens.
    compiler = part(ordinary, 'fun compile_frag_native', 'fun add_frag_native')
    require(compiler == tokens('''
      fun compile_frag_native event mk_rewrs ac rewrs =
        let
          val crewrs = numbered
            (fn (slot,(nm,th)) => (slot,0,(nm,dest_tagged_rewrite th))) rewrs
          val acrewrs = Lib.itlist
            (fn (slot,item) => fn acc =>
              numbered (fn (component,rw) => (slot,component,rw))
                (mk_ac item []) @ acc) (numbered I ac) []
          val named = map (fn (slot,component,rw) =>
            (slot,component,mk_named_rewrs mk_rewrs rw)) (acrewrs @ crewrs)
        in flatten (map (fn (slot,component,rws) =>
             compile_native_named event slot component rws) named) end
    '''), 'installation decode/AC/makers/conversions schedule changed')
    for begin, end, old_end in (
            ('fun mk_ac', 'fun same_frag', 'fun same_frag'),
            ('fun mk_named_rewrs', 'fun is_excluded', 'fun is_excluded'),
            ('fun numbered', 'fun compile_frag_native',
             'fun compile_native_rewrite')):
        require(part(ordinary, begin, end) == part(start, begin, old_end),
                'compiler helper changed: ' + begin)
    install = part(ordinary, 'fun add_frag_native', 'val mk_simpset')
    require(part(install, 'fun add_frag_native', "val mk_rewrs' =") ==
            part(start, 'fun add_frag_native', "val mk_rewrs' ="),
            'installation must reject excluded fragments before compilation')
    require(len(positions(install, tokens(
                'val all_native = case native_override of SOME compiled '
                '=> compiled | NONE => '
                "compile_frag_native event mk_rewrs' ac rewrs"))) == 1,
            'fragment compiler no longer belongs to installation')
    adapter = part(install, 'fun compiled_conv', 'val newconvdata =')
    require(adapter == tokens('''
      fun compiled_conv {thypart,cd} : compiled_convdata =
        {thypart=thypart,cd=lift_convdata cd,legacy= #conv cd,
         source=NONE,bound=NONE}
    '''), 'installation conversion adapter changed')
    require(part(install, 'val newconvdata =', 'fun travrel') ==
            tokens('val newconvdata = map compiled_conv convs @ map #1 native '
                   'val net = net_add_convs initial_net newconvdata'),
            'user conversion adaptation/net installation order changed')
    require(part(install, 'val travrules = merge_travrules',
                 'SS {mk_rewrs = mk_rewrs') == tokens('''
      val travrules = merge_travrules
        (travrules::mk_travrules relations congs::reltravs) in
    '''), 'ordinary congruence merge schedule changed')
    require(locate(install, 'val all_native =') <
            locate(install, 'val newconvdata =') <
            locate(install, 'val context_thms = if null suspended') <
            locate(install, 'val new_dprocs ='),
            'decode/AC/makers/conversions/collector order changed')
    require(ordinary.count('lift_convdata') == 2 and
            ordinary.count('compiled_conv') == 2 and
            ordinary.count('compile_frag_native') == 2,
            'paired conversion/compiler escaped installation')
    require(ordinary.count('source_token') == 2 and
            ordinary.count('source_serial') == 4 and
            tokens('fun op++ args = add_frag false (source_token ()) args') ==
            part(ordinary, 'fun op++', 'val mk_simpset'),
            'source serial/token allocation escaped installation')

    # Fail closed on added bindings or state/table allocation sites anywhere,
    # not only in the obvious constructors. Existing mixed compiled state is
    # TASK_16's scope; the baseline named-registration table is intentionally
    # retained above, rather than falsely banning every global table.
    allowed = binding_inventory(start)
    allowed[('datatype', 'ssfrag')] += 1
    allowed[('type', 'compiled_convdata')] += 1
    allowed[('fun', 'compiled_conv')] += 1
    allowed[('val', '{')] += 1  # baseline ssf_upd_rewrs destructuring above
    require(not (binding_inventory(ordinary) - allowed),
            'new hidden binding/companion/table in ordinary module')
    require(not (binding_inventory(signature) - binding_inventory(
        tokens(git_source(START, FILES[1])))),
        'new unreviewed ordinary API/type')
    allocations = {'ref', 'lazy', 'delay', 'mkDict', 'new', 'empty',
                   'array', 'Array', 'Weak', 'WeakArray'}

    def allocation_sites(seq):
        # Pin neighboring tokens as well as multiplicity: deleting old mixed
        # state must not create an allowance to allocate a new hidden table
        # under an existing binding elsewhere. No task15 route needs a new
        # allocation site of these kinds. Exact route seals remain primary.
        return Counter(tuple(seq[max(0, i-8):i+9])
                       for i, t in enumerate(seq) if t in allocations)

    require(not (allocation_sites(ordinary) - allocation_sites(start)),
            'new hidden allocation/table site')
    return True


if __name__ == '__main__':
    audit()
    print(json.dumps(dict(task=15, structural='pass', baseline=BASE,
                          task_start=START,
                          scope='fragment source contracts; not TASK_16 '
                                'compiled storage or runtime validation')))
