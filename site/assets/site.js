/* Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
 * Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
 * https://github.com/n-yamaguchi-0729
 */
(() => {
  "use strict";

  const publishedLibraries = [
    { name: "Pro-C Groups", repository: "ProCGroups", slug: "pro-c-groups", description: "The library studies profinite groups through their finite quotients, providing ways to construct maps, determine the ranks of open subgroups, and prove that presented groups are infinite." },
    { name: "Class Field Theory", repository: "ClassFieldTheory", slug: "class-field-theory", description: "This library describes abelian extensions of local fields and number fields through arithmetic in the base field, explaining their Galois groups and how primes and norms behave." },
    { name: "Sawin’s Totally Real Towers", repository: "SawinTotallyRealTowers", slug: "sawin-totally-real-towers", description: "The library constructs totally real number fields of arbitrarily large degree while keeping their root discriminants bounded and the same infinite set of primes completely split." },
    { name: "Étale Fundamental Groups and Cohomology", repository: "EtaleFundamentalGroupsAndCohomology", slug: "etale-fundamental-groups-and-cohomology", description: "This library describes algebraic covering spaces through their geometric fibers and studies the sheaves they carry, relating fundamental groups to Galois actions and explaining selected cohomological obstructions." },
    { name: "Jacobian Varieties", repository: "JacobianVarieties", slug: "jacobian-varieties", description: "This library constructs the Jacobian of a smooth proper curve and shows how its geometry controls torsion points and abelian covers of the curve." },
    { name: "Research Papers", repository: "YamaguchiPapersFormalization", slug: "research-papers", description: "These papers study how abelian Galois data detect automorphisms and how the geometry of a boundary controls finite covers over the integers." },
    { name: "Anabelian Geometry", repository: "AnabelianGeometry", slug: "anabelian-geometry", description: "This library studies how the geometry of a curve constrains its étale fundamental group, proving centralizer rigidity for hyperbolic curves and computing the genus-zero case with two punctures." },
  ];

  const base = new URL("../", document.currentScript.src);
  const app = document.getElementById("main");
  const search = document.getElementById("search");
  const popup = document.getElementById("search-popup");
  const suggestions = document.getElementById("search-suggestions");
  const tree = document.getElementById("file-tree");
  const sidebar = document.getElementById("sidebar");
  const menuToggle = document.getElementById("tree-toggle");
  const backdrop = document.getElementById("sidebar-backdrop");
  const announce = document.getElementById("announcement");
  const moduleCache = new Map();
  const workerRequests = new Map();
  let manifest;
  let libraries = new Map();
  let modules = new Map();
  let navigation = 0;
  let worker;
  let requestId = 0;
  let searchTimer;
  let suggestionIndex = -1;
  let suggestionVersion = 0;
  let mathPromise;
  let currentParams = new URLSearchParams(location.search);

  const escape = (value) => String(value ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const number = (value) => Number(value || 0).toLocaleString("en");
  const count = (value, singular, plural = `${singular}s`) => `${number(value)} ${value === 1 ? singular : plural}`;
  const shortName = (value) => String(value || "").split(".").at(-1);
  const prettyName = (value) => String(value || "").replace(/([a-z])([A-Z])/g, "$1 $2").replace(/([A-Z])([A-Z][a-z])/g, "$1 $2").replace(/(Yamaguchi)26 /, "$1 2026 ");
  const libraryName = (library) => library?.displayName || prettyName(library?.name || library?.id || "Library");
  const doc = (value) => typeof value === "string" ? value : "";
  const libraryOf = (module) => libraries.get(module?.library);

  function href(values = {}) {
    const url = new URL(base);
    for (const [name, value] of Object.entries(values)) if (value !== null && value !== undefined && value !== "") url.searchParams.set(name, value);
    return `${url.pathname}${url.search}`;
  }
  const moduleHref = (name, declaration) => href({ module: name, decl: declaration });
  const libraryHref = (id) => href({ library: id });
  const routeLink = (url, label, attributes = "") => `<a href="${escape(url)}" data-route ${attributes}>${label}</a>`;

  function safeUrl(value, context = base) {
    try {
      const url = new URL(value, context);
      return ["http:", "https:", "mailto:"].includes(url.protocol) ? url.href : "";
    } catch { return ""; }
  }

  function inlineMarkdown(text, context) {
    const token = /`([^`\n]+)`|\[([^\]\n]+)\]\(([^\s)]+)(?:\s+"[^"]*")?\)|\*\*([^*\n]+)\*\*|(?<!\*)\*([^*\n]+)\*(?!\*)|(\$\$[\s\S]*?\$\$|(?<!\\)\$[^$\n]+\$|\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\])/g;
    let html = "", end = 0;
    for (const match of text.matchAll(token)) {
      html += escape(text.slice(end, match.index));
      if (match[1] !== undefined) html += `<code>${escape(match[1])}</code>`;
      else if (match[2] !== undefined) {
        const link = safeUrl(match[3], context);
        html += link ? `<a href="${escape(link)}">${escape(match[2])}</a>` : escape(match[2]);
      } else if (match[4] !== undefined) html += `<strong>${escape(match[4])}</strong>`;
      else if (match[5] !== undefined) html += `<em>${escape(match[5])}</em>`;
      else html += escape(match[6]);
      end = match.index + match[0].length;
    }
    return html + escape(text.slice(end));
  }

  // A deliberately small, safe Markdown renderer. Source HTML is always text.
  function markdown(value, context) {
    const lines = doc(value).trim().split(/\r?\n/);
    let html = "", paragraph = [], list = "", fence = false, code = [], quote = [];
    const flushParagraph = () => { if (paragraph.length) html += `<p>${inlineMarkdown(paragraph.join(" "), context)}</p>`; paragraph = []; };
    const closeList = () => { if (list) html += `</${list}>`; list = ""; };
    const closeQuote = () => { if (quote.length) html += `<blockquote>${inlineMarkdown(quote.join(" "), context)}</blockquote>`; quote = []; };
    for (const line of lines) {
      if (/^\s*```/.test(line)) {
        flushParagraph(); closeList(); closeQuote();
        if (fence) { html += `<pre><code>${escape(code.join("\n"))}</code></pre>`; code = []; }
        fence = !fence; continue;
      }
      if (fence) { code.push(line); continue; }
      if (!line.trim()) { flushParagraph(); closeList(); closeQuote(); continue; }
      const heading = line.match(/^\s{0,3}(#{1,6})\s+(.+)/);
      if (heading) { flushParagraph(); closeList(); closeQuote(); html += `<h${heading[1].length > 2 ? 4 : 3}>${inlineMarkdown(heading[2], context)}</h${heading[1].length > 2 ? 4 : 3}>`; continue; }
      const item = line.match(/^\s*(?:([-*+])|(\d+)\.)\s+(.+)/);
      if (item) {
        flushParagraph(); closeQuote(); const type = item[1] ? "ul" : "ol";
        if (list !== type) { closeList(); html += `<${type}>`; list = type; }
        html += `<li>${inlineMarkdown(item[3], context)}</li>`; continue;
      }
      const quoted = line.match(/^\s*>\s?(.*)/);
      if (quoted) { flushParagraph(); closeList(); quote.push(quoted[1]); continue; }
      closeList(); closeQuote(); paragraph.push(line.trim());
    }
    flushParagraph(); closeList(); closeQuote();
    if (code.length) html += `<pre><code>${escape(code.join("\n"))}</code></pre>`;
    return html;
  }

  function plainExcerpt(value, limit = 240) {
    const text = doc(value).replace(/^\s*#{1,6}\s+.*$/gm, "").replace(/\[([^\]]+)\]\([^)]+\)/g, "$1").replace(/[`*_]/g, "").replace(/\s+/g, " ").trim();
    return text.length > limit ? `${text.slice(0, limit).trimEnd()}…` : text;
  }

  function leanCode(source) {
    const token = /\/\*[\s\S]*?\*\/|\/\-[\s\S]*?\-\/|--[^\n]*|"(?:\\.|[^"\\])*"|\b(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|constant|example|namespace|section|end|variable|variables|include|omit|open|export|attribute|where|extends|deriving|private|protected|noncomputable|unsafe|partial|mutual|by|fun|forall|match|with|if|then|else|let|have|show|from|calc|exact|apply|refine|intro|intros|rw|simp|only|constructor|rfl|sorry|admit|import)\b/g;
    let html = "", end = 0;
    for (const match of String(source || "").matchAll(token)) {
      html += escape(source.slice(end, match.index));
      const value = match[0];
      const cls = value.startsWith("--") || value.startsWith("/-") || value.startsWith("/*") ? "comment" : value.startsWith('"') ? "str" : "kw";
      html += `<span class="${cls}">${escape(value)}</span>`;
      end = match.index + value.length;
    }
    return html + escape(String(source || "").slice(end));
  }

  function sourceUrl(item, line) {
    const explicit = safeUrl(item?.sourceUrl || "");
    if (item?.sourceUrl && explicit) return line ? `${explicit.split("#")[0]}#L${line}` : explicit;
    const source = manifest.source || {};
    if (!source.repo || !source.commit || !item?.path) return "";
    return `${source.repo.replace(/\/$/, "")}/blob/${encodeURIComponent(source.commit)}/${item.path.split("/").map(encodeURIComponent).join("/")}${line ? `#L${line}` : ""}`;
  }

  function sourceAction(url, label = "View source ↗", className = "") {
    return url && safeUrl(url) ? `<a class="${className}" href="${escape(safeUrl(url))}">${escape(label)}</a>` : "";
  }

  async function typesetMath(root) {
    const targets = [...root.querySelectorAll(".documentation, .math-summary")].filter((element) => /\$|\\\(|\\\[/.test(element.textContent));
    if (!targets.length) return;
    if (!mathPromise) {
      mathPromise = new Promise((resolve, reject) => {
        window.MathJax = { loader: { load: ["ui/safe"] }, tex: { inlineMath: [["$", "$"], ["\\(", "\\)"]], displayMath: [["$$", "$$"], ["\\[", "\\]"]], processEscapes: true }, options: { skipHtmlTags: ["script", "noscript", "style", "textarea", "pre", "code"], safeOptions: { allow: { URLs: "safe", classes: "none", cssIDs: "none", styles: "none" }, safeProtocols: { http: true, https: true, file: false, javascript: false, data: false } } }, startup: { typeset: false } };
        const script = document.createElement("script");
        script.src = "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml.js";
        script.async = true;
        script.onload = () => window.MathJax.startup.promise.then(resolve, reject);
        script.onerror = reject;
        document.head.appendChild(script);
      });
    }
    try { await mathPromise; await window.MathJax.typesetPromise(targets.filter((element) => element.isConnected)); } catch { /* The original TeX remains readable if the renderer cannot load. */ }
  }

  async function getModule(name) {
    const summary = modules.get(name);
    if (!summary) throw new Error(`The module “${name}” is not in this source snapshot.`);
    if (!moduleCache.has(name)) {
      const url = new URL(summary.dataUrl || `data/modules/${name}.json`, base);
      const request = fetch(url).then((response) => { if (!response.ok) throw new Error(response.status === 404 ? "This source snapshot is no longer available. Reload the page to open the latest revision." : "The module data could not be loaded. Please try again."); return response.json(); }).catch((error) => { moduleCache.delete(name); throw new Error(error instanceof TypeError ? "The module data could not be loaded. Check your connection and reload the page." : error.message); });
      moduleCache.set(name, request);
    }
    return moduleCache.get(name);
  }

  function renderHome() {
    document.title = "NYLL — Lean 4 libraries for number theory and arithmetic geometry";
    const values = [...libraries.values()];
    app.innerHTML = `<section class="hero"><span class="eyebrow">NYLL · Lean 4</span><h1>NYLL — Lean 4 libraries for<br>number theory and arithmetic geometry</h1><p>Lean 4 libraries for number theory and arithmetic geometry. Explore the published libraries, their mathematical results, and the code behind them. NYLL also hosts ongoing development.</p><nav class="home-links" aria-label="Explore NYLL"><a href="#published-libraries">Published standalone libraries ↓</a><a href="#development-libraries">Browse work in progress ↓</a></nav></section>
      <section id="published-libraries" class="published-catalog" aria-labelledby="published-heading"><div class="catalog-intro"><h2 id="published-heading">Published standalone libraries</h2><span class="count">${count(publishedLibraries.length, "repository", "repositories")}</span></div><p class="catalog-description">Explore each library’s scope and selected theorems and definitions, with mathematical explanations, Lean code, and references.</p><ul class="published-list">${publishedLibraries.map((library) => `<li><h3><a href="${new URL(`libraries/${library.slug}/`, base).pathname}">${escape(library.name)} <span aria-hidden="true">→</span></a></h3><p>${escape(library.description)}</p></li>`).join("")}</ul></section>
      <section id="development-libraries" aria-labelledby="libraries-heading"><div class="catalog-intro"><h2 id="libraries-heading">Browse development libraries</h2><span class="count">${count(values.length, "library", "libraries")} · ${count(modules.size, "module")}</span></div><p class="catalog-description">Explore the full collection in NYLL, including work in progress.</p>
      ${values.map((library, index) => {
        const summary = plainExcerpt(doc(library.summary || library.doc).replace(/Formalization of Naganori Yamaguchi['’]s /g, "Formalization of "));
        return `<article class="library-row"><span class="row-number" aria-hidden="true">${String(index + 1).padStart(2, "0")}</span><div><h3>${routeLink(libraryHref(library.id), escape(libraryName(library)))}</h3>${summary ? `<p class="math-summary">${escape(summary)}</p>` : ""}<div class="row-meta"><span>${count(library.moduleCount, "module")}</span><code>${escape(library.rootModule || `Nyll.${library.id}.All`)}</code></div></div>${routeLink(libraryHref(library.id), "↗", `class="row-arrow" aria-label="Browse ${escape(libraryName(library))}"`)}</article>`;
      }).join("")}</section><section class="module-overview"><h2 class="section-label">Authorship and verification</h2><div class="documentation"><p>NYLL’s original code and documentation are Copyright (c) 2026 Naganori Yamaguchi. All original code developed for NYLL is written by OpenAI Codex. Source-specific credits and licenses are preserved for adapted and external material.</p><p>${sourceAction(`${manifest.source?.repo}/blob/${manifest.source?.commit}/README.md`, "Authorship, verification, and license details ↗")}</p></div></section><p class="page-footer">Browse the documentation alongside its Lean source. ${sourceAction(manifest.source?.repo, "The source repository ↗")} contains the full development collection.</p>`;
    void typesetMath(app);
  }

  function libraryModules(id) { return [...modules.values()].filter((module) => module.library === id); }

  function moduleRows(items, prefix = "") {
    return items.map((module) => {
      const label = prefix && module.name.startsWith(`${prefix}.`) ? module.name.slice(prefix.length + 1) : module.name;
      const summary = plainExcerpt(module.summary || module.doc, 220);
      return `<article class="module-row"><div class="module-row-head">${routeLink(moduleHref(module.name), `${escape(label)}.lean`)}<span class="count">${count(module.declarationCount, "declaration")}</span></div>${summary ? `<p class="math-summary">${escape(summary)}</p>` : ""}</article>`;
    }).join("");
  }

  function groupedModuleRows(items, library, filter = "") {
    const prefix = `Nyll.${library.id}`;
    const filtered = items.filter((item) => item.name.toLowerCase().includes(filter.toLowerCase()));
    if (!filtered.length) return '<p class="empty">No modules match this filter.</p>';
    if (filter || filtered.length < 20) return moduleRows(filtered, prefix);
    const groups = new Map();
    for (const module of filtered) {
      const rest = module.name.startsWith(`${prefix}.`) ? module.name.slice(prefix.length + 1) : module.name;
      const group = rest.includes(".") ? rest.split(".")[0] : "Root modules";
      if (!groups.has(group)) groups.set(group, []);
      groups.get(group).push(module);
    }
    return [...groups.entries()].sort(([left], [right]) => left === "Root modules" ? -1 : right === "Root modules" ? 1 : left.localeCompare(right)).map(([group, values]) => `<details class="module-group"${group === "Root modules" ? " open" : ""}><summary>${escape(group)}<span class="count">${count(values.length, "module")}</span></summary>${moduleRows(values, prefix)}</details>`).join("");
  }

  async function renderLibrary(id, version) {
    const library = libraries.get(id);
    if (!library) throw new Error(`The library “${id}” is not in this source snapshot.`);
    const items = libraryModules(id);
    let overview = doc(library.doc);
    let root = modules.get(library.rootModule);
    if (root) root = await getModule(root.name);
    if (navigation !== version) return;
    if (root?.doc) overview = doc(root.doc);
    document.title = `${libraryName(library)} · NYLL`;
    app.innerHTML = `<header class="page-head"><span class="eyebrow">Library</span><h1 class="page-title">${escape(libraryName(library))}</h1><div class="page-actions"><span>${count(items.length, "module")}</span>${root ? routeLink(moduleHref(root.name), "Root module") : ""}${sourceAction(root ? sourceUrl(root) : "")}</div></header>
      ${overview ? `<section class="module-overview"><h2 class="section-label">Library documentation</h2><div class="documentation">${markdown(overview, sourceUrl(root) || base)}</div></section>` : ""}
      <section aria-labelledby="modules-heading"><div class="catalog-toolbar"><h2 id="modules-heading">Modules</h2><label><span class="sr-only">Filter modules in this library</span><input id="module-filter" type="search" placeholder="Filter modules…" spellcheck="false"></label></div><div id="module-list">${groupedModuleRows(items, library)}</div></section>`;
    document.getElementById("module-filter").addEventListener("input", (event) => { window.MathJax?.typesetClear?.([document.getElementById("module-list")]); document.getElementById("module-list").innerHTML = groupedModuleRows(items, library, event.target.value); void typesetMath(document.getElementById("module-list")); });
    void typesetMath(app);
  }

  function importDetails(label, values) {
    const names = Array.isArray(values) ? values : [];
    return `<details class="dependency-details"><summary>${label}<span>${number(names.length)}</span></summary>${names.length ? `<ul>${names.map((name) => `<li>${modules.has(name) ? routeLink(moduleHref(name), escape(name)) : escape(name)}</li>`).join("")}</ul>` : '<p class="muted">None.</p>'}</details>`;
  }

  function declarationHtml(declaration, module) {
    const name = declaration.fullName || declaration.name || declaration.id;
    const id = declaration.id || name;
    const short = shortName(name);
    const source = declaration.source || "";
    const statement = declaration.statement || `${declaration.kind} ${declaration.name}`;
    const details = source && !declaration.statementIncludesBody && source.trim() !== statement.trim();
    const url = declaration.sourceUrl || sourceUrl(module, declaration.line);
    const isProof = ["theorem", "lemma", "example"].includes(declaration.kind);
    return `<article class="declaration" data-declaration="${escape(id)}" id="declaration-${escape(id)}"><div class="declaration-heading"><div class="declaration-title"><span class="kind">${escape(declaration.kind || "declaration")}</span><h3>${routeLink(moduleHref(module.name, id), escape(short))}</h3>${declaration.hasSorry ? '<span class="unproved">Contains sorry</span>' : ""}</div>${sourceAction(url, `L${declaration.line || 1} ↗`, "source-link")}</div>${name !== short ? `<div class="qualified-name">${escape(name)}</div>` : ""}
      ${declaration.doc ? `<section class="declaration-doc"><span class="content-label">Documentation</span><div class="documentation">${markdown(declaration.doc, url)}</div></section>` : ""}
      ${declaration.context?.length ? `<details class="context-details" data-context-index="${escape(id)}"><summary>Source context <span>${count(declaration.context.length, "command")}</span></summary><div class="context-mount"></div></details>` : ""}
      <div class="formal-statement"><span class="content-label">Lean source · ${declaration.statementIncludesBody ? "full declaration" : "statement"}</span><pre class="statement${declaration.statementIncludesBody ? " source-complete" : ""}"><code>${leanCode(statement)}</code></pre></div>
      ${details ? `<details class="proof-details" data-source-index="${escape(id)}"><summary>${isProof ? "Proof" : "Implementation"} · Lean source</summary><div class="proof-mount"></div></details>` : ""}</article>`;
  }

  async function renderModule(name, version) {
    const module = await getModule(name);
    if (version !== navigation) return;
    const library = libraryOf(module);
    const declarations = module.declarations || [];
    const url = sourceUrl(module);
    const title = shortName(name);
    document.title = `${title} · ${libraryName(library)} · NYLL`;
    app.innerHTML = `<header class="page-head"><span class="eyebrow">Module</span><h1 class="page-title module-title">${escape(title)}.lean</h1><div class="qualified-module">${escape(name)}</div><div class="page-actions"><span>${count(declarations.length, "declaration")} indexed from source</span>${sourceAction(url)}</div></header>
      ${module.doc ? `<section class="module-overview"><h2 class="section-label">Module documentation</h2><div class="documentation">${markdown(module.doc, url)}</div></section>` : ""}
      <div class="dependencies">${importDetails("Imports", module.imports)}${importDetails("Imported by", module.importedBy)}</div>
      <section aria-labelledby="declarations-heading"><div class="catalog-toolbar"><h2 id="declarations-heading">Declarations</h2>${declarations.some((entry) => entry.source && !entry.statementIncludesBody && entry.source.trim() !== entry.statement?.trim()) ? '<button id="proof-toggle" class="small-button" type="button" aria-pressed="false">Expand all source</button>' : ""}</div>${declarations.length ? declarations.map((entry) => declarationHtml(entry, module)).join("") : '<p class="empty">This module has no indexed declarations. Its imports and full source are available here.</p>'}</section>
      ${module.source ? '<details class="source-details"><summary>Full module source</summary><div id="full-source"></div></details>' : ""}<p class="page-footer">Statements and documentation are read from the Lean source at the revision shown. Source entries are not a measure of mathematical completeness.</p>`;
    const byId = new Map(declarations.map((entry) => [entry.id || entry.fullName || entry.name, entry]));
    for (const detail of app.querySelectorAll(".context-details")) detail.addEventListener("toggle", () => {
      if (detail.open && !detail.querySelector(".context-mount").hasChildNodes()) {
        const entry = byId.get(detail.dataset.contextIndex);
        detail.querySelector(".context-mount").innerHTML = `<p class="context-note">Surrounding namespaces, section variables, and local commands at this declaration.</p><pre class="statement"><code>${leanCode((entry?.context || []).map((command) => command.source).join("\n"))}</code></pre>`;
      }
    });
    const details = [...app.querySelectorAll(".proof-details")];
    for (const detail of details) detail.addEventListener("toggle", () => {
      if (detail.open && !detail.querySelector(".proof-mount").hasChildNodes()) detail.querySelector(".proof-mount").innerHTML = `<pre class="statement"><code>${leanCode(byId.get(detail.dataset.sourceIndex)?.source || "")}</code></pre>`;
      updateProofToggle();
    });
    function updateProofToggle() {
      const button = document.getElementById("proof-toggle");
      if (!button) return;
      const allOpen = details.length > 0 && details.every((detail) => detail.open);
      button.textContent = allOpen ? "Collapse all source" : "Expand all source";
      button.setAttribute("aria-pressed", String(allOpen));
    }
    document.getElementById("proof-toggle")?.addEventListener("click", () => { const open = !details.every((detail) => detail.open); for (const detail of details) detail.open = open; updateProofToggle(); });
    app.querySelector(".source-details")?.addEventListener("toggle", (event) => { if (event.target.open && !document.getElementById("full-source").hasChildNodes()) document.getElementById("full-source").innerHTML = `<pre><code>${leanCode(module.source)}</code></pre>`; });
    void typesetMath(app);
  }

  function workerSearch(pattern, limit = 12, kind = "all") {
    if (!worker) {
      worker = new Worker(new URL("assets/search-worker.js", base));
      worker.onmessage = ({ data }) => {
        const pending = workerRequests.get(data.id);
        if (!pending) return;
        workerRequests.delete(data.id);
        if (data.error) pending.reject(new Error(data.error)); else pending.resolve(data);
      };
      worker.onerror = () => { for (const pending of workerRequests.values()) pending.reject(new Error("Search could not be loaded. Browse the library tree or try again.")); workerRequests.clear(); worker.terminate(); worker = null; };
      worker.postMessage({ type: "init", base: base.href, searchUrl: manifest.searchUrl, libraries: [...libraries.values()].map((library) => ({ type: "library", id: library.id, name: libraryName(library), library: library.id, doc: plainExcerpt(library.doc || library.summary) })), modules: [...modules.values()].map((module) => ({ type: "module", name: module.name, module: module.name, library: module.library, doc: plainExcerpt(module.doc || module.summary) })) });
    }
    const id = ++requestId;
    return new Promise((resolve, reject) => { workerRequests.set(id, { resolve, reject }); worker.postMessage({ type: "search", id, pattern, limit, kind }); });
  }

  function searchHref(item) {
    if (item.type === "library") return libraryHref(item.library || item.id);
    return moduleHref(item.module || item.name, item.type === "module" ? null : item.id || item.name);
  }

  async function renderSearch(pattern, version) {
    document.title = `Search: ${pattern} · NYLL`;
    const type = currentParams.get("type") || "all";
    app.innerHTML = `<header class="page-head"><span class="eyebrow">Search the library</span><h1 class="page-title">${escape(pattern || "Search")}</h1><p id="search-count" class="search-count" role="status">Loading the search index…</p></header><div class="catalog-toolbar"><h2>Results</h2><label><span class="sr-only">Result type</span><select id="search-type"><option value="all">All entries</option><option value="library">Libraries</option><option value="module">Modules</option><option value="declaration">Declarations</option></select></label></div><div id="search-results"></div><button id="load-more" class="small-button load-more" type="button" hidden>Show more results</button>`;
    const select = document.getElementById("search-type");
    select.value = ["all", "library", "module", "declaration"].includes(type) ? type : "all";
    select.addEventListener("change", () => navigate(href({ q: pattern, type: select.value === "all" ? null : select.value })));
    let limit = 60;
    async function showResults() {
      const result = await workerSearch(pattern, limit, select.value);
      if (version !== navigation) return;
      document.getElementById("search-count").textContent = `${count(result.total, "result")} for “${pattern}”`;
      document.getElementById("search-results").innerHTML = result.results.map((item) => `<article class="search-result"><h2>${routeLink(searchHref(item), escape(item.fullName || item.name))}</h2><div class="result-meta">${escape(item.type === "declaration" ? item.kind || "declaration" : item.type)} · ${escape(libraryName(libraries.get(item.library)))}${item.type === "declaration" ? ` · ${escape(item.module)}` : ""}</div>${item.doc ? `<p>${escape(plainExcerpt(item.doc))}</p>` : ""}</article>`).join("") || '<p class="empty">No matching entries. Try a shorter name or a module name.</p>';
      const more = document.getElementById("load-more");
      more.hidden = result.results.length >= result.total;
      more.disabled = false;
      announce.textContent = count(result.total, "search result");
    }
    document.getElementById("load-more").addEventListener("click", async (event) => { event.target.disabled = true; limit += 60; try { await showResults(); } catch (error) { document.getElementById("search-count").textContent = error.message; event.target.disabled = false; } });
    await showResults();
  }

  function makeTree(items, prefix) {
    const root = { children: new Map() };
    for (const module of items) {
      const rest = module.name.startsWith(`${prefix}.`) ? module.name.slice(prefix.length + 1) : module.name;
      let node = root;
      for (const part of rest.split(".")) { if (!node.children.has(part)) node.children.set(part, { name: part, children: new Map() }); node = node.children.get(part); }
      node.module = module;
    }
    return root;
  }

  function treeNodeHtml(node, active) {
    const current = node.module?.name === active;
    const file = node.module ? `<li>${routeLink(moduleHref(node.module.name), `${escape(node.name)}.lean`, `class="tree-module" title="${escape(node.module.name)}"${current ? ' aria-current="page"' : ""}`)}</li>` : "";
    if (!node.children.size) return file;
    const contains = (branch) => branch.module?.name === active || [...branch.children.values()].some(contains);
    return `<li><details${contains(node) ? " open" : ""}><summary>${escape(node.name)}</summary><ul>${file}${[...node.children.values()].map((child) => treeNodeHtml(child, active)).join("")}</ul></details></li>`;
  }

  function renderTree() {
    const active = currentParams.get("module") || "";
    const activeLibrary = currentParams.get("library") || modules.get(active)?.library;
    tree.innerHTML = `<ul class="tree"><li class="tree-root">${routeLink(href(), "All libraries", `${!activeLibrary && !currentParams.has("q") ? 'aria-current="page"' : ""}`)}</li>${[...libraries.values()].map((library) => `<li><details data-tree-library="${escape(library.id)}"${library.id === activeLibrary ? " open" : ""}><summary>${escape(libraryName(library))}</summary><ul class="library-tree-mount"></ul></details></li>`).join("")}</ul>`;
    for (const detail of tree.querySelectorAll("[data-tree-library]")) {
      const populate = () => {
        const mount = detail.querySelector(".library-tree-mount");
        if (!detail.open || mount.hasChildNodes()) return;
        const id = detail.dataset.treeLibrary;
        const library = libraries.get(id);
        const root = makeTree(libraryModules(id), `Nyll.${id}`);
        mount.innerHTML = `<li>${routeLink(libraryHref(id), "Library overview", `class="tree-overview"${id === activeLibrary && !active ? ' aria-current="page"' : ""}`)}</li>${[...root.children.values()].map((child) => treeNodeHtml(child, active)).join("")}`;
      };
      detail.addEventListener("toggle", populate);
      populate();
    }
  }

  function closeSuggestions() { clearTimeout(searchTimer); popup.hidden = true; search.setAttribute("aria-expanded", "false"); search.removeAttribute("aria-activedescendant"); suggestionIndex = -1; }

  async function updateSuggestions() {
    if (document.activeElement !== search) return;
    const pattern = search.value.trim();
    const version = ++suggestionVersion;
    if (pattern.length < 2) { closeSuggestions(); return; }
    popup.hidden = false;
    search.setAttribute("aria-expanded", "true");
    suggestions.innerHTML = '<div class="search-message" role="status">Searching…</div>';
    document.getElementById("search-all").href = href({ q: pattern });
    try {
      const result = await workerSearch(pattern);
      if (version !== suggestionVersion || document.activeElement !== search) return;
      suggestions.innerHTML = result.results.map((item, index) => `<a id="suggestion-${index}" class="suggestion" role="option" aria-selected="false" href="${escape(searchHref(item))}" data-route><span class="suggestion-name">${escape(item.fullName || item.name)}</span><span class="suggestion-meta">${escape(item.type === "declaration" ? item.kind || "declaration" : item.type)} · ${escape(libraryName(libraries.get(item.library)))}</span></a>`).join("") || '<div class="search-message" role="status">No matching entries.</div>';
      suggestionIndex = -1;
    } catch (error) {
      if (version === suggestionVersion) {
        suggestions.innerHTML = `<div class="search-message" role="status">${escape(error.message)}<p><button id="reload-search" class="small-button" type="button">Reload page</button></p></div>`;
        document.getElementById("reload-search").addEventListener("click", () => location.reload());
      }
    }
  }

  function setMenu(open) {
    sidebar.classList.toggle("is-open", open);
    backdrop.hidden = !open;
    menuToggle.setAttribute("aria-expanded", String(open));
    menuToggle.setAttribute("aria-label", open ? "Close module navigation" : "Open module navigation");
    if (open) document.getElementById("tree-close").focus();
  }

  async function render() {
    const version = ++navigation;
    window.MathJax?.typesetClear?.([app]);
    currentParams = new URLSearchParams(location.search);
    const query = currentParams.get("q");
    const module = currentParams.get("module");
    const library = currentParams.get("library");
    search.value = query || "";
    app.setAttribute("aria-busy", "true");
    renderTree();
    try {
      if (query !== null) await renderSearch(query, version);
      else if (module) await renderModule(module, version);
      else if (library) await renderLibrary(library, version);
      else renderHome();
      if (version !== navigation) return;
      const declaration = currentParams.get("decl");
      if (declaration) {
        const target = [...app.querySelectorAll("[data-declaration]")].find((element) => element.dataset.declaration === declaration);
        if (target) { target.classList.add("is-target"); requestAnimationFrame(() => target.scrollIntoView({ block: "start" })); }
      }
      announce.textContent = document.title;
    } catch (error) {
      if (version === navigation) {
        document.title = "Page unavailable · NYLL";
        app.innerHTML = `<section class="error-state"><span class="eyebrow">NYLL</span><h1>This page could not be loaded.</h1><p>${escape(error.message)}</p><p>${routeLink(href(), "Return to all libraries")} · ${sourceAction(manifest.source?.repo, "Browse on GitHub ↗")}</p><button id="retry-page" class="small-button" type="button">Reload page</button></section>`;
        document.getElementById("retry-page").addEventListener("click", () => location.reload());
      }
    } finally { if (version === navigation) app.setAttribute("aria-busy", "false"); }
  }

  function navigate(url) {
    if (!manifest) return;
    const next = new URL(url, base);
    if (next.origin !== location.origin || next.pathname !== base.pathname) return;
    history.pushState({}, "", next);
    closeSuggestions(); ++suggestionVersion;
    setMenu(false);
    window.scrollTo({ top: 0 });
    app.focus({ preventScroll: true });
    void render();
  }

  document.addEventListener("click", (event) => {
    const link = event.target.closest("a[data-route]");
    if (link && !event.ctrlKey && !event.metaKey && !event.shiftKey && !event.altKey && event.button === 0) { event.preventDefault(); navigate(link.href); }
    if (!event.target.closest(".search-form")) { closeSuggestions(); ++suggestionVersion; }
  });
  document.addEventListener("focusin", (event) => { if (!event.target.closest(".search-form")) { closeSuggestions(); ++suggestionVersion; } });
  search.addEventListener("input", () => { clearTimeout(searchTimer); ++suggestionVersion; searchTimer = setTimeout(updateSuggestions, 180); });
  search.addEventListener("focus", () => { if (search.value.trim().length >= 2) void updateSuggestions(); });
  search.addEventListener("keydown", (event) => {
    const entries = [...suggestions.querySelectorAll("[role=option]")];
    if (["ArrowDown", "ArrowUp"].includes(event.key) && !popup.hidden && entries.length) {
      event.preventDefault(); suggestionIndex = suggestionIndex < 0 ? (event.key === "ArrowDown" ? 0 : entries.length - 1) : (suggestionIndex + (event.key === "ArrowDown" ? 1 : -1) + entries.length) % entries.length;
      entries.forEach((entry, index) => entry.setAttribute("aria-selected", String(index === suggestionIndex)));
      search.setAttribute("aria-activedescendant", entries[suggestionIndex].id);
      entries[suggestionIndex].scrollIntoView({ block: "nearest" });
    } else if (event.key === "Enter" && !popup.hidden && suggestionIndex >= 0) { event.preventDefault(); navigate(entries[suggestionIndex].href); }
    else if (event.key === "Escape") { closeSuggestions(); ++suggestionVersion; }
  });
  document.querySelector(".search-form").addEventListener("submit", (event) => { event.preventDefault(); const query = search.value.trim(); if (query) navigate(href({ q: query })); });
  document.addEventListener("keydown", (event) => {
    if (event.key === "/" && !event.ctrlKey && !event.metaKey && !event.altKey && !event.target.matches("input,textarea,select,[contenteditable=true]")) { event.preventDefault(); search.focus(); }
    if (event.key === "Escape" && sidebar.classList.contains("is-open")) { setMenu(false); menuToggle.focus(); }
  });
  menuToggle.addEventListener("click", () => setMenu(!sidebar.classList.contains("is-open")));
  document.getElementById("tree-close").addEventListener("click", () => { setMenu(false); menuToggle.focus(); });
  backdrop.addEventListener("click", () => { setMenu(false); menuToggle.focus(); });
  window.addEventListener("popstate", () => { closeSuggestions(); setMenu(false); void render(); });

  fetch(new URL("data/manifest.json", base), { cache: "no-cache" }).then((response) => { if (!response.ok) throw new Error("The source catalog could not be loaded. Please try again shortly."); return response.json(); }).then((data) => {
    manifest = data;
    search.disabled = false;
    libraries = new Map((manifest.libraries || []).map((library) => [library.id, library]));
    modules = new Map((manifest.modules || []).map((module) => [module.name, module]));
    if (!libraries.size && !modules.size) throw new Error("The source catalog is empty.");
    const source = manifest.source || {};
    if (source.repo) document.getElementById("github-link").href = source.repo;
    const date = source.committedAt ? new Date(source.committedAt) : null;
    const dateText = date && !Number.isNaN(date.valueOf()) ? date.toLocaleDateString("en", { year: "numeric", month: "short", day: "numeric", timeZone: "UTC" }) : "";
    const revision = source.commitShort || source.commit?.slice(0, 8);
    document.getElementById("revision").innerHTML = `<p>Source revision ${revision ? `<a href="${escape(`${source.repo}/commit/${source.commit}`)}"><code>${escape(revision)}</code></a>` : "unavailable"}</p>${dateText ? `<p>${escape(dateText)} · updated from Git</p>` : ""}<p><a href="${escape(`${source.repo}/actions/workflows/libraries.yml`)}">Lean checks ↗</a></p>`;
    void render();
  }).catch((error) => { app.setAttribute("aria-busy", "false"); app.innerHTML = `<section class="error-state"><span class="eyebrow">NYLL</span><h1>The library browser is unavailable.</h1><p>${escape(error.message)}</p><p><a href="https://github.com/n-yamaguchi-0729/NYLL">Browse the source on GitHub ↗</a></p><button class="small-button" type="button" onclick="location.reload()">Try again</button></section>`; tree.innerHTML = '<p class="muted">Source catalog unavailable.</p>'; });
})();
