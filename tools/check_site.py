#!/usr/bin/env python3
"""Check statement coverage, local links, source fidelity and the release archive."""
from __future__ import annotations
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit
import zipfile
from build_site import ROOT, SITE, load_data

class Document(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids = set()
        self.links = []
        self.duplicate_ids = set()
        self.feed(text)
    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            if attrs['id'] in self.ids:
                self.duplicate_ids.add(attrs['id'])
            self.ids.add(attrs['id'])
        for attr in ('href', 'src'):
            if attrs.get(attr):
                self.links.append(attrs[attr])

def check():
    data = load_data()
    by_name = {n['name']: n for n in data['nodes']}
    assert len(by_name) == len(data['nodes'])
    roots = data['roots']
    assert len([r for r in roots if r['role'] == 'literature']) == 15
    assert {r['key'] for r in roots if r['role'] == 'additional'} == {'derdzinski','amann'}
    assert len([r for r in roots if r['role'] == 'target']) == 4
    for r in roots:
        n = by_name[r['name']]
        assert n['code'] and n['statement'] and n['encoding'] and n['sourceLocation']
        if r['role'] in {'literature','additional'}:
            assert n['references'] and n['locator'] and n['relation']
    for n in data['nodes']:
        if n['sourceLocation']:
            loc = n['sourceLocation']
            lines = data['modules'][n['module']]['code'].splitlines(keepends=True)
            expected = ''.join(lines[loc['startLine']-1:loc['endLine']]).rstrip('\n')
            assert n['code'] == expected, n['name']
        assert n['roots'], n['name']
    for ref in data['references'].values():
        assert ref['url'].startswith('https://') and ref['version']
    docs = {p: Document(p.read_text()) for p in SITE.rglob('*.html')}
    assert {p.relative_to(SITE).as_posix() for p in docs} == {
        'index.html', 'lean/index.html', 'lean/source.html'}, 'Unexpected leftover site page'
    checked_links = 0
    for path, doc in docs.items():
        assert not doc.duplicate_ids, (path.name, doc.duplicate_ids)
        for raw in doc.links:
            url = urlsplit(raw)
            if url.scheme or url.netloc:
                assert url.scheme in {'https','http'}, raw
                continue
            assert not url.path.startswith('/'), f'Absolute link breaks GitHub project Pages: {raw}'
            dest = (path.parent / unquote(url.path)).resolve() if url.path else path
            assert dest.is_relative_to(SITE), raw
            assert dest.exists(), (path.name, raw)
            if url.fragment:
                if url.fragment.startswith('node='):
                    assert unquote(url.fragment[5:]) in by_name, raw
                elif dest in docs:
                    assert unquote(url.fragment) in docs[dest].ids, (path.name, raw)
            checked_links += 1
    archive = SITE / 'downloads/ls_dim14-source.zip'
    assert archive.exists()
    checksum = (SITE / 'downloads/SHA256SUMS').read_text().split()[0]
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == checksum
    manifest = json.loads((ROOT / 'site-data/source-manifest.json').read_text())
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        assert len(names) == len(set(names))
        for name in names:
            parts = Path(name).parts
            assert parts[0] == 'ls_dim14' and '..' not in parts
            assert not set(parts) & {'.git','.lake','.elan','__pycache__','node_modules','downloads','results'}
            assert not name.endswith(('.pdf','.olean','.ilean','.pem','.key'))
            assert (z.getinfo(name).external_attr >> 16) & 0o170000 != 0o120000
        for f in manifest['source_files']:
            assert hashlib.sha256(z.read('ls_dim14/lean/' + f['path'])).hexdigest() == f['sha256']
        for required in ['LICENSE','README.md','PUBLICATION.md','lean/lake-manifest.json','lean/lean-toolchain',
                         'lean/README.md','lean/tools/ExportBoundary.lean','tools/build_site.py',
                         'python/README.md','python/check_all.py','python/verify.py','python/verify_h2.py',
                         'python/verify_decompositions.py','python/check_examples.py',
                         'python/data/decompositions_certificate.json',
                         'python/check_printed_identities.py','python/adjacent_density.py','python/orbital_polynomials.py',
                         'python/data/h2_witness_n13.json','python/data/h2_witness_n14.json',
                         'site/lean/index.html','.github/workflows/publish.yml']:
            assert 'ls_dim14/' + required in names, required
        assert z.read('ls_dim14/LICENSE').startswith(b'MIT License')
    # Browser JS source uses textContent for data; no network/CDN dependency is required.
    for name in ['site/lean/assets/data.js','site/lean/assets/explorer.js','site-data/catalogue.json', 'README.md']:
        text = (ROOT / name).read_text()
        assert not re.search(r'/(?:home|Users)/[^/]+/', text), name
    subprocess.run([sys.executable, str(ROOT / 'tools/build_site.py'), '--check'], check=True)
    print(f'PASS: {len(roots)} roots; {len(by_name)} graph declarations; exact source excerpts; {checked_links} local links; {len(manifest["source_files"])} archived Lean source hashes; MIT license; deterministic generated files/archive.')

if __name__ == '__main__':
    check()
