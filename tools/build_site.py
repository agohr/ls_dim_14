#!/usr/bin/env python3
"""Build the static, offline-capable publication site using only Python 3.10+.

The Lean export supplies the graph; catalogue.json supplies editorial descriptions.
This generator never guesses literature contracts from file names or comments.
"""
from __future__ import annotations
import argparse
import hashlib
import html
import io
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
SITE = ROOT / 'site'
EXPLORER = SITE / 'lean'
PREFIX = 'QuaternionicSymmetry.'

def read_json(path):
    return json.loads((ROOT / path).read_text(encoding='utf-8'))

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify_snapshot(manifest):
    paths = {'QuaternionicSymmetry.lean', 'Audit.lean'} | {
        p.relative_to(LEAN).as_posix() for p in (LEAN / 'QuaternionicSymmetry').rglob('*.lean')}
    recorded = {f['path']: f['sha256'] for f in manifest['source_files']}
    if paths != set(recorded):
        raise ValueError('Source inventory differs from the recorded snapshot. Regenerate the Lean export and deliberately update the provenance manifest.')
    for path, sha in recorded.items():
        if digest((LEAN / path).read_bytes()) != sha:
            raise ValueError(f'Source changed since snapshot: {path}. Regenerate the export and provenance before publishing.')
    if (LEAN / 'lean-toolchain').read_text().strip() != manifest['lean_toolchain']:
        raise ValueError('Toolchain differs from the snapshot.')

def load_data():
    manifest = read_json('site-data/source-manifest.json')
    verify_snapshot(manifest)
    raw = read_json('site-data/kernel.json')
    cat = read_json('site-data/catalogue.json')
    nodes = {n['name']: dict(n) for n in raw['nodes']}
    roots = raw['roots']
    assert raw['sourceFieldCount'] == sum(r['role'] == 'literature' for r in roots) == 15
    assert set(cat['entries']) == {r['key'] for r in roots}, 'Editorial catalogue must match exported roots exactly.'
    assert set(cat.get('definitions', {})) <= nodes.keys(), 'Curated definition is absent from the export.'
    refs = cat['references']
    for e in list(cat['entries'].values()) + list(cat.get('definitions', {}).values()):
        assert set(e['references']) <= refs.keys()
    for n in nodes.values():
        missing = [d for d in n['dependencies'] if (d.startswith(PREFIX) or d.startswith('_private.' + PREFIX)) and d not in nodes]
        assert not missing, (n['name'], missing)
    modules = {}
    for n in nodes.values():
        path = n['module'].replace('.', '/') + '.lean'
        if n['module'] not in modules:
            modules[n['module']] = dict(path='lean/' + path, code=(LEAN / path).read_text(encoding='utf-8'))
        n['roots'] = []
        n['role'] = 'definition'
        n['generated'] = n['location'] is None or n['kind'] == 'constructor'
        n['title'] = n['name'].removeprefix(PREFIX)
        # Field projections and compiler helpers are kept, never silently dropped.
        owner = n
        if n['location'] is None or n['kind'] == 'constructor' or n['location']['startColumn'] > 0:
            parts = n['name'].split('.')[:-1]
            while parts:
                candidate = nodes.get('.'.join(parts))
                if candidate and candidate['location']:
                    owner = candidate
                    break
                parts.pop()
        n['sourceOwner'] = owner['name']
        n['sourceLocation'] = owner['location']
        n['parentDoc'] = owner['doc'] if owner is not n else ''
        if owner['location']:
            loc = owner['location']
            lines = modules[n['module']]['code'].splitlines(keepends=True)
            # Whole source lines deliberately preserve indentation and multiline fields.
            n['code'] = ''.join(lines[loc['startLine'] - 1:loc['endLine']]).rstrip('\n')
        else:
            n['code'] = ''
        if n['name'] in cat.get('definitions', {}):
            n.update(cat['definitions'][n['name']])
            n['curated'] = True
    for r in roots:
        nodes[r['name']].update(cat['entries'][r['key']])
        nodes[r['name']].update(role=r['role'], key=r['key'])
        seen, todo = set(), [r['name']]
        while todo:
            name = todo.pop()
            if name in seen or name not in nodes:
                continue
            seen.add(name)
            nodes[name]['roots'].append(r['key'])
            todo.extend(nodes[name]['dependencies'])
    assert all(n['roots'] for n in nodes.values()), 'Unreachable node in export.'
    visible = [n for n in nodes.values() if not n['generated'] and n['role'] in {'definition', 'boundary'}]
    return dict(config=cat['config'], references=refs, roots=roots,
        nodes=sorted(nodes.values(), key=lambda n: n['name']), modules=modules,
        provenance=dict(sourceCommit=manifest['source_commit'], toolchain=manifest['lean_toolchain'],
            sourceFiles=len(manifest['source_files']), kernelSHA256=digest((ROOT / 'site-data/kernel.json').read_bytes()),
            sourceManifestSHA256=digest((ROOT / 'site-data/source-manifest.json').read_bytes())),
        counts=dict(literature=15, additional=2, targets=4, declarations=len(nodes),
            visibleDefinitions=len(visible), modules=len(modules)))

def e(value):
    return html.escape(str(value), quote=True)

def reference_html(key, ref):
    return f'<li id="ref-{e(key)}"><a href="{e(ref["url"])}">{e(ref["title"])}</a><br>{e(ref["authors"])}. {e(ref["publication"])}<p class="small">{e(ref["version"])}</p></li>'

def printable(data):
    by_name = {n['name']: n for n in data['nodes']}
    cards = []
    for r in data['roots']:
        if r['role'] not in ('literature', 'additional'):
            continue
        n = by_name[r['name']]
        links = ', '.join(f'<a href="{e(data["references"][k]["url"])}">{e(k.upper())}</a>' for k in n['references'])
        cards.append(f'''<details class="node" id="{e(r['key'])}"><summary><span class="badge">{e(r['key'])}</span><strong>{e(n['title'])}</strong></summary>
        <div class="comparison"><section class="code-side"><p class="eyebrow">Exact Lean source</p><pre><code>{e(n['code'])}</code></pre><details><summary>Elaborated type, including implicit parameters</summary><pre><code>{e(n['type'])}</code></pre></details></section>
        <section class="math-side"><p class="eyebrow">{e(n['relation'])}</p><h3>Mathematical statement · paraphrase</h3><p>{e(n['statement'])}</p><h3>Correspondence with Lean</h3><p>{e(n['encoding'])}</p><p class="locator">{e(n['locator'])}</p><p>{links}</p><p class="small">{e(n['note'])}</p></section></div></details>''')
    return '\n'.join(cards)

def make_outputs(data):
    config = data['config']
    replacements = {
        'TITLE': e(config['title']), 'COMMIT': e(data['provenance']['sourceCommit'][:12]),
        'FULL_COMMIT': e(data['provenance']['sourceCommit']),
        'DEFINITIONS': str(data['counts']['visibleDefinitions']), 'DECLARATIONS': str(data['counts']['declarations']),
        'SOURCE_FILES': str(data['provenance']['sourceFiles']),
        'REFERENCES': '\n'.join(reference_html(k, r) for k, r in data['references'].items()),
        'PRINTABLE': printable(data),
        'REPOSITORY_LINK': f'<a class="repo-link" href="{e(config["repository_url"])}">GitHub repository ↗</a>' if config['repository_url'] else '',
    }
    outputs = {}
    templates = ROOT / 'tools/templates'
    for path in sorted(templates.rglob('*.html')):
        template = path.read_text(encoding='utf-8')
        for key, value in replacements.items():
            template = template.replace('{{' + key + '}}', value)
        if re.search(r'\{\{[A-Z_]+\}\}', template):
            raise ValueError(f'Unresolved template token in {path}')
        outputs[SITE / path.relative_to(templates)] = template.encode('utf-8')
    serialized = json.dumps(data, ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')
    outputs[EXPLORER / 'assets/data.js'] = ('/* Generated by tools/build_site.py. */\nwindow.PUBLICATION = ' + serialized + ';\n').encode('utf-8')
    for name in ('kernel.json', 'catalogue.json', 'source-manifest.json'):
        outputs[EXPLORER / 'data' / name] = (ROOT / 'site-data' / name).read_bytes()
    outputs[SITE / 'data/LICENSE.txt'] = (ROOT / 'LICENSE').read_bytes()
    outputs[SITE / '.nojekyll'] = b''
    return outputs

def source_archive(outputs):
    """Deterministic archive: tracked-style allowlist, no caches, history, PDFs or symlinks."""
    top_dirs = {'lean', 'python', 'tools', 'site-data', 'site', '.github', '.vscode'}
    top_files = {'README.md', 'PUBLICATION.md', 'VALIDATION.md', 'LICENSE', '.gitignore'}
    files = {}
    for path in ROOT.rglob('*'):
        rel = path.relative_to(ROOT)
        if not path.is_file() or path.is_symlink() or any(x in {'.lake', '.git', '__pycache__', 'node_modules', 'downloads', 'results'} for x in rel.parts):
            continue
        if (len(rel.parts) == 1 and rel.name in top_files) or rel.parts[0] in top_dirs:
            files[rel.as_posix()] = outputs.get(path, path.read_bytes())
    for path, contents in outputs.items():
        files[path.relative_to(ROOT).as_posix()] = contents
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, contents in sorted(files.items()):
            info = zipfile.ZipInfo('ls_dim14/' + name, (2026, 10, 4, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, contents)
    return stream.getvalue()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Fail if generated outputs or source archive are stale.')
    parser.add_argument('--no-archive', action='store_true', help='Build only the website and data.')
    args = parser.parse_args()
    data = load_data()
    outputs = make_outputs(data)
    if not args.no_archive:
        archive = source_archive(outputs)
        outputs[SITE / 'downloads/ls_dim14-source.zip'] = archive
        outputs[SITE / 'downloads/SHA256SUMS'] = (digest(archive) + '  ls_dim14-source.zip\n').encode()
    stale = []
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_bytes() != content:
                stale.append(path.relative_to(ROOT).as_posix())
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
    if stale:
        raise SystemExit('Stale generated files; run python3 tools/build_site.py:\n' + '\n'.join(stale))
    print(('Checked' if args.check else 'Built') + f' site: 15 shared inputs, 2 additional inputs, {data["counts"]["visibleDefinitions"]} visible supporting declarations, {len(data["nodes"])} total graph nodes.')

if __name__ == '__main__':
    main()
