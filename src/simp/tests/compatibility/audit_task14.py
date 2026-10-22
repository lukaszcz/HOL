#!/usr/bin/env python3
"""Small structural complement to the executed tracked compiler contracts.

This is not a general SML parser or whole-plan legacy performance audit.
The bounded checks reject hidden compilation/promotion in public getters,
loss of actual-control binding and re-preparation of cached matcher shapes.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[4]


def part(text, start, end):
    assert text.count(start) == 1, start
    return text.split(start, 1)[1].split(end, 1)[0]


def audit(simp, cond, sig):
    # A tracked getter may allocate shallow data/closures, not identities,
    # counters, matchers, collector contexts or a replay of any kind.
    projection = part(simp, ' fun traversedata_for_ss ss =',
                      ' fun SIMP_QCONV_WITH_XDATA')
    default = part(simp, ' fun default_traversedata_for_ss',
                   ' (* Settings used only')
    setup = part(simp, ' fun rewriter_context_for_ss_prepared',
                 ' fun configured_traversedata_for_ss_prepared')
    inventory = part(simp, 'fun rewrite_sources (SS data)',
                     '\nfun SIMP_CONV ss')
    for getter in (projection, default, inventory):
        for forbidden in ('source_token', 'source_slot', 'ref ',
                          'mk_rewr_convdata', 'mk_rewrs', 'addctxt',
                          'process_tags', 'process_asm_tags',
                          'build_from_history', 'ssfrags_of'):
            assert forbidden not in getter, ('getter', forbidden)
    assert 'legacy_rewriter_for_ss_prepared ss []' in default
    assert 'ParentFirst ss []' in projection
    assert 'prepared_convdata mk_rewrs prepared' in setup
    assert 'initial_net' in setup and 'net_add_convs initial_net' in setup
    assert 'DEST_BOUNDED' in inventory
    assert 'dest_tagged_rewrite' not in inventory
    assert 'raise ERR ("rewrite_sources"' in inventory
    assert 'prepare_rewrite_arguments' in inventory
    assert '(* Inspection only.' in simp

    compiler = part(simp, ' fun compile_frag_native',
                    '\n datatype rewrite_bundle')
    assert (compiler.index('dest_tagged_rewrite') < compiler.index('mk_ac') <
            compiler.index('mk_named_rewrs') <
            compiler.index('compile_native_named'))
    assert 'source_token' not in compiler
    compile_rule = part(simp, 'fun mk_rewr_convdata',
                        '(* Replay rebinds')
    assert compile_rule.count('Cond_rewrExt.prepare') == 1
    assert 'Cond_rewrExt.runners prepared' in compile_rule
    assert 'prepared = SOME prepared' in compile_rule
    replay = part(simp, 'fun freshen_prepared_native',
                  '\nfun suspend_rewrite_sources')
    assert 'mk_rewr_convdata' not in replay
    assert 'rebind_convdata' in replay
    assert 'same_rewrite_source (previous,source)' in replay
    assert 'Portable.pointer_eq (old,counter)' in replay
    bind = part(simp, 'fun rebind_convdata',
                '(*---------------------------------------------------------------------------*)')
    assert 'Cond_rewrExt.rebind' in bind and 'BOUNDED counter' in bind
    assert 'mk_rewr_convdata' not in bind
    assert 'bound=SOME (counter,declared)' in bind
    prepare = part(simp, 'fun prepare_rewrite_arguments ss thl =',
                   '(* Inspection only.')
    assert 'process_tags0 {report=true,preserve=true}' in prepare
    assert 'build_from_history' not in prepare
    assert 'remove_ssfrags_with_controls preserve exclfrags ss' in simp
    assert not re.search(r'\bsimpLib\.[A-Za-z]', simp)
    assert not re.search(r'val\s+(promote|import_simpset)\b', sig)

    shape = part(cond, 'datatype prepared =', '\nend')
    assert 'shape : runners' in shape and 'bound : runners' in shape
    rebind = part(shape, 'fun rebind ', 'fun runners ')
    assert 'bounded = is_bounded control' in rebind
    assert 'bind shape control' in rebind
    assert 'COND_REWR_CONVS' not in rebind and 'ref ' not in rebind
    assert shape.count('Portable.dec r') == 2
    assert shape.count('if !r = 0') == 2
    # Scope over net entries, not just the public source inventory. Views
    # and internal entries do not have handles of their own.
    private = part(simp, 'fun prepare_child_first_with_observer',
                   '    val traversal =')
    assert 'Ho_Net.fold\'' in private and '#initial_net data' in private
    assert 'native_sources' not in private
    assert 'Portable.finally restore run tm' in private
    return True


def sources():
    src = ROOT / 'src/simp/src'
    return tuple((src / name).read_text() for name in
                 ('simpExtLib.sml', 'Cond_rewrExt.sml', 'simpExtLib.sig'))


if __name__ == '__main__':
    audit(*sources())
    print('TASK_14 tracked compiler structural contracts: OK')
