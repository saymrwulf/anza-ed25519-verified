#!/usr/bin/env python3
"""Classify every external the extraction declares.

For each gen/<dir>/<X>_Template.lean, Aeneas states what the extracted Rust
needs from outside. Each such name must be provided by exactly one of:

  MODEL   — declared in the hand-written sibling gen/<dir>/<X>.lean: an
            assumption, which the axiom gate and the per-certificate cones
            then govern;
  PROVEN  — resolved to a real definition in the proven corpus, because a
            module of this repository declares it (namespace-aware). This is
            the valuable case and the one the docs claim for the tier-A/B
            curve calls; nothing has ever checked it.

Anything else is drift: the extraction asks for something this repository does
not provide.
"""
import re, sys, os, glob

DECL = re.compile(
    r'^[ \t]*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe )*'
    r'(axiom|def|abbrev|opaque|structure|inductive)[ \t]+([A-Za-z_][A-Za-z0-9_.\'!?]*)')
NS = re.compile(r'^[ \t]*(namespace|end)[ \t]+([A-Za-z_][A-Za-z0-9_.\']*)')

def declared(path):
    """Fully-qualified names declared in one file, honouring namespaces."""
    names, stack = set(), []
    for line in open(path, encoding='utf-8', errors='replace'):
        m = NS.match(line)
        if m:
            if m.group(1) == 'namespace':
                stack.append(m.group(2))
            elif stack and stack[-1] == m.group(2):
                stack.pop()
            continue
        d = DECL.match(line)
        if d:
            names.add('.'.join(stack + [d.group(2)]) if stack else d.group(2))
    return names

def main(root):
    gen = os.path.join(root, 'gen')
    templates = sorted(glob.glob(os.path.join(gen, '*', '*_Template.lean')))
    # The proven corpus: every generated module that is neither a template nor
    # a hand-written model. These are the files Aeneas produced from Rust.
    models = {t.replace('_Template', '') for t in templates}
    corpus = set()
    for f in sorted(glob.glob(os.path.join(gen, '*', '*.lean'))):
        if f in models or f.endswith('_Template.lean'):
            continue
        corpus |= declared(f)

    rows, unresolved = [], []
    for t in templates:
        model = t.replace('_Template', '')
        rel = os.path.relpath(t, gen).replace('_Template.lean', '')
        tnames = declared(t)
        mnames = declared(model) if os.path.exists(model) else set()
        for n in sorted(tnames):
            if n in mnames:
                rows.append(f'{rel}|{n}|MODEL')
            elif n in corpus:
                rows.append(f'{rel}|{n}|PROVEN')
            else:
                rows.append(f'{rel}|{n}|UNRESOLVED')
                unresolved.append(f'{rel}|{n}')
        for n in sorted(mnames - tnames):
            rows.append(f'{rel}|{n}|EXTRA')
    print('\n'.join(rows))
    print(f'CORRESPONDENCE-COUNT|{len(rows)}')
    return 1 if unresolved else 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
