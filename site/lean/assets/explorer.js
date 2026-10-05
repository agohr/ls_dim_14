/* No runtime dependencies. Data is local so the site also works over file://. */
(() => {
  'use strict';
  const data = window.PUBLICATION;
  if (!data) return;
  const nodes = new Map(data.nodes.map(n => [n.name, n]));
  const rootByKey = new Map(data.roots.map(r => [r.key, r]));
  const $ = id => document.getElementById(id);
  function element(tag, className, text) {
    const el = document.createElement(tag);
    if (className) el.className = className;
    if (text !== undefined) el.textContent = text;
    return el;
  }
  function link(text, href, className) {
    const a = element('a', className, text); a.href = href; return a;
  }
  function paragraph(parent, text, className) {
    if (text) parent.append(element('p', className, text));
  }
  function code(text) {
    const pre = element('pre'); pre.append(element('code', '', text)); return pre;
  }
  const nodeURL = name => '#node=' + encodeURIComponent(name);
  function renderSource() {
    const name = new URLSearchParams(location.search).get('module');
    const module = data.modules[name];
    if (!module) {
      $('source-error').textContent = 'Module not found in the exported encoding graph. Use a source link in the explorer, or download the complete project.';
      return;
    }
    $('source-title').textContent = name.replace('QuaternionicSymmetry.', '');
    $('source-path').textContent = module.path + ' · snapshot ' + data.provenance.sourceCommit.slice(0, 12);
    const fragment = document.createDocumentFragment();
    module.code.split('\n').forEach((line, i) => {
      const row = element('span', 'source-line'); row.id = 'L' + (i + 1);
      row.append(link(String(i + 1), '#L' + (i + 1), 'line-number'), document.createTextNode(line || ' '));
      fragment.append(row);
    });
    $('full-source').append(fragment);
    const download = $('source-download');
    download.href = URL.createObjectURL(new Blob([module.code], {type: 'text/plain;charset=utf-8'}));
    download.download = module.path.split('/').pop(); download.hidden = false;
    const scroll = () => {
      const match = /^#L(\d+)$/.exec(location.hash);
      if (match) $('L' + match[1])?.scrollIntoView({block: 'center', behavior: 'instant'});
    };
    window.addEventListener('hashchange', scroll); requestAnimationFrame(scroll);
  }
  if ($('full-source')) { renderSource(); return; }
  if (!$('declarations')) return;

  const allowedViews = new Set(['literature', 'targets', 'definitions', 'all']);
  const query = new URLSearchParams(location.search);
  const state = {
    view: allowedViews.has(query.get('view')) ? query.get('view') : 'literature',
    search: query.get('q') || '', root: query.get('root') || '', generated: false, limit: 50
  };
  if (!rootByKey.has(state.root)) state.root = '';
  const openNames = new Set();
  const rootOrder = new Map(data.roots.map((r, i) => [r.name, i]));
  const ordered = [...data.nodes].sort((a, b) => {
    const x = rootOrder.get(a.name) ?? 100, y = rootOrder.get(b.name) ?? 100;
    return x - y || Number(!!b.curated) - Number(!!a.curated) || a.name.localeCompare(b.name);
  });
  const searchText = new Map(ordered.map(n => [n.name, [n.name, n.title, n.doc, n.parentDoc, n.statement,
    n.encoding, n.locator, n.type, n.code, ...(n.references || []).map(k => {
      const ref = data.references[k]; return `${k} ${ref.authors} ${ref.title}`;
    })].filter(Boolean).join(' ').toLocaleLowerCase()]));
  const shortName = name => name.replace(/^QuaternionicSymmetry\./, '');
  function reference(key) {
    const ref = data.references[key];
    const div = element('div', 'reference');
    div.append(link(ref.title, ref.url));
    paragraph(div, ref.authors + '. ' + ref.publication);
    paragraph(div, ref.version, 'small');
    return div;
  }
  function panel(n) {
    const fragment = document.createDocumentFragment();
    const comparison = element('div', 'comparison');
    const left = element('section', 'code-side');
    paragraph(left, 'Exact Lean source', 'eyebrow');
    const loc = n.sourceLocation;
    const path = data.modules[n.module].path;
    const context = n.sourceOwner !== n.name;
    paragraph(left, path + (loc ? ` · lines ${loc.startLine}–${loc.endLine}` : ''), 'source-label');
    if (context) paragraph(left, 'Containing declaration: ' + shortName(n.sourceOwner), 'small');
    if (n.code) left.append(code(n.code));
    else paragraph(left, 'This compiler-generated declaration has no separate source range. Its exact elaborated type is below; the full module is linked for context.', 'small');
    const actions = element('div', 'code-actions');
    if (n.code) {
      const copy = element('button', 'copy-button', 'Copy Lean'); copy.type = 'button';
      copy.addEventListener('click', async () => {
        try {
          if (!navigator.clipboard?.writeText) throw new Error('Clipboard unavailable');
          await navigator.clipboard.writeText(n.code); copy.textContent = 'Copied';
        } catch {
          const range = document.createRange(); range.selectNodeContents(left.querySelector('pre code'));
          const selection = getSelection(); selection.removeAllRanges(); selection.addRange(range);
          copy.textContent = 'Selected — copy with Ctrl/Cmd+C';
        }
      });
      actions.append(copy);
    }
    actions.append(link('Full module ↗', 'source.html?module=' + encodeURIComponent(n.module) + (loc ? '#L' + loc.startLine : '')),
      link('Link to this declaration', nodeURL(n.name)));
    left.append(actions);
    const elaborated = element('details');
    elaborated.append(element('summary', '', 'Elaborated type · all implicit parameters'), code(n.type));
    if (!n.code) elaborated.open = true;
    left.append(elaborated);
    const right = element('section', 'math-side');
    paragraph(right, n.relation || (n.generated ? 'Compiler helper' : n.kind === 'theorem' ? 'Supporting proved theorem' : 'Project encoding'), 'eyebrow');
    if (n.statement) {
      right.append(element('h3', '', n.role === 'literature' || n.role === 'additional' ? 'Mathematical statement · paraphrase' : 'Mathematical meaning'));
      paragraph(right, n.statement);
      right.append(element('h3', '', 'Correspondence with Lean')); paragraph(right, n.encoding);
      paragraph(right, n.locator, 'locator');
    } else {
      const doc = n.doc || n.parentDoc;
      right.append(element('h3', '', doc ? 'Encoding note · source documentation' : 'Implementation definition'));
      paragraph(right, doc || `This ${n.kind} is part of the implementation of the statements linked below. Its elaborated type gives the exact parameters and result.`);
      if (!n.doc && n.parentDoc) paragraph(right, 'The note describes the containing declaration; this node selects or supports part of it.', 'small');
      paragraph(right, 'This supporting declaration is not a separate literature premise. There is no standalone published theorem asserted for this implementation detail. Follow its related inputs for the mathematical correspondence.', 'small');
    }
    if (n.references?.length) {
      right.append(element('h3', '', 'Sources and locators'));
      n.references.forEach(k => right.append(reference(k)));
    }
    paragraph(right, n.note, 'note');
    comparison.append(left, right); fragment.append(comparison);
    const project = n.dependencies.filter(name => nodes.has(name));
    const external = n.dependencies.filter(name => !nodes.has(name));
    if (project.length) {
      const dep = element('details', 'dependencies'); dep.open = true;
      const visible = project.filter(name => state.generated || !nodes.get(name).generated);
      dep.append(element('summary', '', `Definitions and supporting declarations (${visible.length}${visible.length !== project.length ? ' shown; ' + (project.length - visible.length) + ' compiler helpers hidden' : ''})`));
      const list = element('div', 'dependency-list');
      visible.forEach(name => list.append(link(shortName(name), nodeURL(name))));
      if (!visible.length) paragraph(list, 'Enable compiler helpers to see these dependencies.', 'small');
      dep.append(list); fragment.append(dep);
    }
    if (external.length) {
      const dep = element('details', 'dependencies');
      dep.append(element('summary', '', `Lean and mathlib constants (${external.length}; external leaves)`));
      paragraph(dep, 'These library definitions are outside the project-only traversal. The pinned dependency source is available through Lake and “Go to Definition” in the editor.', 'small');
      paragraph(dep, external.join(' · '), 'external-deps'); fragment.append(dep);
    }
    const related = n.roots.filter(key => rootByKey.get(key).name !== n.name && key !== 'sources');
    if (related.length) {
      const div = element('div', 'related'); paragraph(div, 'Appears in the encoding of:');
      related.forEach(key => div.append(link(key, nodeURL(rootByKey.get(key).name)))); fragment.append(div);
    }
    return fragment;
  }
  function card(n) {
    const details = element('details', 'node'); details.id = n.name;
    const summary = element('summary');
    const badge = n.role === 'definition' ? (n.generated ? 'helper' : n.kind) : (n.key || n.role);
    summary.append(element('span', 'badge' + (n.role === 'additional' ? ' additional' : ''), badge));
    const text = element('span', 'summary-text');
    text.append(element('strong', '', n.title));
    if (n.title !== shortName(n.name)) text.append(element('span', 'summary-name', shortName(n.name)));
    summary.append(text); details.append(summary);
    let populated = false;
    function populate() { if (!populated) { details.append(panel(n)); populated = true; } }
    details.addEventListener('toggle', () => {
      if (details.open) { populate(); openNames.add(n.name); }
      else openNames.delete(n.name);
    });
    if (openNames.has(n.name)) { details.open = true; populate(); }
    return details;
  }
  function matches(n) {
    if (!state.generated && n.generated) return false;
    if (state.view === 'literature' && !['literature', 'additional'].includes(n.role)) return false;
    if (state.view === 'targets' && n.role !== 'target') return false;
    if (state.view === 'definitions' && !['definition', 'boundary'].includes(n.role)) return false;
    if (state.root && !n.roots.includes(state.root)) return false;
    return state.search.trim().toLocaleLowerCase().split(/\s+/).every(term => searchText.get(n.name).includes(term));
  }
  function syncURL(clearHash = false) {
    const url = new URL(location.href);
    url.searchParams.delete('view'); url.searchParams.delete('q'); url.searchParams.delete('root');
    if (state.view !== 'literature') url.searchParams.set('view', state.view);
    if (state.search) url.searchParams.set('q', state.search);
    if (state.root) url.searchParams.set('root', state.root);
    if (clearHash) url.hash = '';
    try { history.replaceState(null, '', url); } catch { /* file:// remains usable */ }
  }
  function render() {
    document.querySelectorAll('[data-view]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.view === state.view)));
    $('search').value = state.search; $('root-filter').value = state.root; $('show-generated').checked = state.generated;
    const titles = {literature:'Literature inputs', targets:'Target theorems', definitions:'Encoding definitions', all:'All declarations'};
    $('view-title').textContent = titles[state.view];
    const filtered = ordered.filter(matches);
    $('result-count').textContent = filtered.length + (filtered.length === 1 ? ' declaration' : ' declarations') + (filtered.length > state.limit ? ` · first ${state.limit} shown` : '');
    const fragment = document.createDocumentFragment();
    filtered.slice(0, state.limit).forEach(n => fragment.append(card(n)));
    if (!filtered.length) fragment.append(element('div', 'empty', 'No matching declarations. Try a shorter search, clear “Relevant to”, or choose another category.'));
    $('declarations').replaceChildren(fragment);
    $('load-more').hidden = filtered.length <= state.limit;
    $('load-more').textContent = `Show next ${Math.min(50, Math.max(0, filtered.length - state.limit))}`;
  }
  function openHash() {
    if (!location.hash.startsWith('#node=')) return;
    let name;
    try { name = decodeURIComponent(location.hash.slice(6)); } catch { return; }
    const n = nodes.get(name);
    if (!n) { $('result-count').textContent = 'Unknown declaration in this link.'; return; }
    if (!matches(n)) {
      state.view = n.role === 'target' ? 'targets' : ['literature','additional'].includes(n.role) ? 'literature' : 'definitions';
      state.search = ''; state.root = ''; state.generated = n.generated;
    }
    const index = ordered.filter(matches).findIndex(item => item.name === name);
    state.limit = Math.max(state.limit, index + 1);
    openNames.add(name); syncURL(); render();
    requestAnimationFrame(() => $(name)?.scrollIntoView({block: 'start', behavior: 'instant'}));
  }
  data.roots.filter(r => r.role !== 'boundary').forEach(r => {
    const option = element('option', '', r.key + ' · ' + nodes.get(r.name).title);
    option.value = r.key; $('root-filter').append(option);
  });
  document.querySelectorAll('[data-view]').forEach(button => button.addEventListener('click', () => {
    state.view = button.dataset.view; state.limit = 50; syncURL(true); render();
  }));
  let timer;
  $('search').addEventListener('input', event => {
    state.search = event.target.value; clearTimeout(timer);
    timer = setTimeout(() => { state.limit = 50; syncURL(true); render(); }, 120);
  });
  $('root-filter').addEventListener('change', event => { state.root = event.target.value; state.limit = 50; syncURL(true); render(); });
  $('show-generated').addEventListener('change', event => { state.generated = event.target.checked; state.limit = 50; render(); });
  $('reset').addEventListener('click', () => {
    Object.assign(state, {view:'literature', search:'', root:'', generated:false, limit:50});
    openNames.clear(); syncURL(true); render();
  });
  $('load-more').addEventListener('click', () => { state.limit += 50; render(); });
  window.addEventListener('hashchange', openHash);
  window.addEventListener('popstate', () => {
    if (location.hash.startsWith('#node=')) return;
    const q = new URLSearchParams(location.search);
    state.view = allowedViews.has(q.get('view')) ? q.get('view') : 'literature';
    state.search = q.get('q') || ''; state.root = q.get('root') || ''; render();
  });
  render(); openHash();
})();
