/* Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
 * Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
 * https://github.com/n-yamaguchi-0729
 */
(() => {
  "use strict";

  const base = new URL("../", document.currentScript.src);
  // Keep shared navigation anchored at the deployment root after SPA navigation.
  document.querySelector(".brand").href = base.href;
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

  const homeTitle = "NYLL — Lean 4 libraries for number theory and arithmetic geometry";
  const homeDescription = "Lean 4 libraries for number theory and arithmetic geometry. Explore mathematical statements, published Lean code, historical context, and references.";
  const encodeRoutePart = (value) => encodeURIComponent(String(value)).replace(/[!'()*]/g, (c) => "%" + c.charCodeAt(0).toString(16).toUpperCase());

  function readRoute(value) {
    const url = new URL(value, location.href);
    if (url.origin !== base.origin || !url.pathname.startsWith(base.pathname)) return null;
    const path = url.pathname.slice(base.pathname.length);
    const catalog = /^(?:browse|browse\/|browse\/index\.html)$/.test(path);
    const match = path.match(/^(modules|browse)\/([^/]+)(?:\/|\/index\.html)?$/);
    if (path !== "" && path !== "index.html" && !match && !catalog) return null;
    let id;
    try { id = match ? decodeURIComponent(match[2]) : ""; } catch { return null; }
    const query = url.searchParams;
    let route;
    if (query.has("q")) {
      const type = ["library", "module", "declaration"].includes(query.get("type")) ? query.get("type") : "";
      route = { kind: "search", query: query.get("q"), type };
    } else if (catalog) {
      route = { kind: "catalog" };
    } else if (match) {
      route = { kind: match[1] === "modules" ? "module" : "library", id };
    } else if (query.get("module")) {
      route = { kind: "module", id: query.get("module") };
    } else if (query.get("library")) {
      route = { kind: "library", id: query.get("library") };
    } else {
      route = { kind: "home" };
    }
    route.hash = url.hash;
    if (route.kind === "module") {
      let fragment = "";
      try { fragment = decodeURIComponent(url.hash.slice(1)); } catch { /* Keep an unrecognized fragment unchanged. */ }
      route.declaration = query.get("decl") || (fragment.startsWith("declaration-") ? fragment.slice(12) : "");
    }
    return route;
  }

  function routeHref(route) {
    const path = route.kind === "module" ? "modules/" + encodeRoutePart(route.id) + "/"
      : route.kind === "library" ? "browse/" + encodeRoutePart(route.id) + "/"
      : ["catalog", "search"].includes(route.kind) ? "browse/" : "";
    const url = new URL(path, base);
    if (route.kind === "search") {
      url.searchParams.set("q", route.query || "");
      if (route.type) url.searchParams.set("type", route.type);
    }
    url.hash = route.kind === "module" && route.declaration
      ? "declaration-" + encodeRoutePart(route.declaration) : route.hash || "";
    return url.pathname + url.search + url.hash;
  }

  function routeParams(route) {
    const params = new URLSearchParams();
    if (route.kind === "module") {
      params.set("module", route.id);
      if (route.declaration) params.set("decl", route.declaration);
    } else if (route.kind === "library") params.set("library", route.id);
    else if (route.kind === "catalog") params.set("catalog", "1");
    else if (route.kind === "search") {
      params.set("q", route.query);
      if (route.type) params.set("type", route.type);
    }
    return params;
  }

  function normalizeLocation() {
    const route = readRoute(location.href);
    if (!route) return null;
    const next = routeHref(route);
    if (next !== location.pathname + location.search + location.hash) history.replaceState(history.state, "", next);
    return route;
  }

  function href(values = {}) {
    const route = values.q !== null && values.q !== undefined ? { kind: "search", query: values.q, type: values.type }
      : values.module ? { kind: "module", id: values.module, declaration: values.decl }
      : values.library ? { kind: "library", id: values.library }
      : values.catalog ? { kind: "catalog" } : { kind: "home" };
    return routeHref(route);
  }
  const moduleHref = (name, declaration) => href({ module: name, decl: declaration });
  const libraryHref = (id) => href({ library: id });
  const routeLink = (url, label, attributes = "") => '<a href="' + escape(url) + '" data-route ' + attributes + ">" + label + "</a>";

  function metadataRoot() {
    const configured = document.body.dataset.siteRoot;
    if (configured) return new URL(configured, base);
    const canonical = document.querySelector('link[rel="canonical"]');
    if (!canonical) return new URL(base);
    const kind = document.body.dataset.staticPage;
    return new URL(["module", "library"].includes(kind) ? "../../" : kind === "catalog" ? "../" : "./", canonical.href);
  }
  const canonicalBase = metadataRoot();
  const initialRoute = readRoute(location.href);
  // Keep the landing page static. Legacy source links move to the browser;
  // the browser never repaints the library guides or adds its tree here.
  if (!sidebar) {
    if (initialRoute && initialRoute.kind !== "home") location.replace(routeHref(initialRoute));
    return;
  }
  document.querySelector(".search-form").action = new URL("browse/", base).href;
  let keepInitialContent = Boolean(app.children.length) && initialRoute !== null
    && (document.body.dataset.staticPage || "home") === initialRoute.kind
    && (["home", "catalog"].includes(initialRoute.kind) || document.body.dataset.staticId === initialRoute.id);

  function setMetadata(title, description, route = readRoute(location.href)) {
    document.title = title;
    const setMeta = (attribute, name, content) => {
      let element = document.querySelector("meta[" + attribute + '="' + name + '"]');
      if (!element) {
        element = document.createElement("meta");
        element.setAttribute(attribute, name);
        document.head.appendChild(element);
      }
      element.setAttribute("content", content);
    };
    setMeta("name", "description", description);
    setMeta("name", "robots", route?.kind === "search" ? "noindex,follow" : "index,follow");
    setMeta("property", "og:title", title);
    setMeta("property", "og:description", description);
    setMeta("name", "twitter:title", title);
    setMeta("name", "twitter:description", description);
    if (route) {
      const relative = routeHref(route).slice(base.pathname.length).split("#")[0];
      const canonicalUrl = new URL(relative, canonicalBase).href;
      let canonical = document.querySelector('link[rel="canonical"]');
      if (!canonical) {
        canonical = document.createElement("link");
        canonical.setAttribute("rel", "canonical");
        document.head.appendChild(canonical);
      }
      canonical.href = canonicalUrl;
      setMeta("property", "og:url", canonicalUrl);
    }
  }

  function updateRouteMetadata(route) {
    if (route.kind === "module") {
      const module = modules.get(route.id);
      const label = libraryName(libraryOf(module));
      setMetadata(route.id + " · NYLL",
        plainExcerpt(module?.doc || module?.summary, 160) || route.id + ": Lean source, declarations, and documentation in " + label + ".", route);
    } else if (route.kind === "library") {
      const library = libraries.get(route.id);
      const label = libraryName(library);
      setMetadata(label + " · NYLL", plainExcerpt(library?.doc || library?.summary, 160)
        || label + ": Lean source modules, mathematical statements, and documentation.", route);
    } else if (route.kind === "catalog") {
      setMetadata("All source code · NYLL", "Browse all NYLL source libraries, modules, and Lean declarations.", route);
    } else if (route.kind === "search") {
      setMetadata("Search: " + route.query + " · NYLL", "Search NYLL libraries, modules, and Lean declarations.", route);
    } else setMetadata(homeTitle, homeDescription, route);
  }

  function scrollToRouteTarget(route) {
    for (const element of app.querySelectorAll(".declaration.is-target")) element.classList.remove("is-target");
    let target;
    if (route.kind === "module" && route.declaration) {
      target = [...app.querySelectorAll("[data-declaration]")].find((element) => element.dataset.declaration === route.declaration);
      target?.classList.add("is-target");
    } else if (route.hash) {
      try { target = document.getElementById(decodeURIComponent(route.hash.slice(1))); } catch { /* Ignore malformed fragments. */ }
    }
    if (target && app.contains(target)) requestAnimationFrame(() => target.isConnected && target.scrollIntoView({ block: "start" }));
  }

  function showLoadFailure(error, preserve) {
    if (preserve) {
      if (!app.querySelector("[data-load-notice]")) app.insertAdjacentHTML("afterbegin",
        '<p class="context-note" data-load-notice role="status">Interactive browsing could not be loaded. The published page remains available below. Reload the page to try again.</p>');
      announce.textContent = error.message;
      return;
    }
    setMetadata("Page unavailable · NYLL", error.message);
    document.querySelector('meta[name="robots"]').setAttribute("content", "noindex,follow");
    app.innerHTML = '<section class="error-state"><span class="eyebrow">NYLL</span><h1>This page could not be loaded.</h1><p>' + escape(error.message)
      + "</p><p>" + routeLink(href(), "Return to all libraries") + " · " + sourceAction(manifest?.source?.repo || "https://github.com/n-yamaguchi-0729/NYLL", "Browse on GitHub ↗")
      + '</p><button id="retry-page" class="small-button" type="button">Reload page</button></section>';
    document.getElementById("retry-page").addEventListener("click", () => location.reload());
  }

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

  function renderCatalog() {
    const values = [...libraries.values()];
    app.innerHTML = `<header class="page-head"><h1 class="page-title">All source code</h1><p>The complete published NYLL collection, organized by source library.</p></header><section aria-labelledby="libraries-heading"><div class="catalog-intro"><h2 id="libraries-heading">Source libraries</h2><span class="count">${count(values.length, "library", "libraries")} · ${count(modules.size, "module")}</span></div>
      ${values.map((library, index) => {
        return `<article class="library-row"><span class="row-number" aria-hidden="true">${String(index + 1).padStart(2, "0")}</span><div><h3>${routeLink(libraryHref(library.id), escape(libraryName(library)))}</h3><div class="row-meta"><span>${count(library.moduleCount, "module")}</span><code>${escape(library.rootModule || `Nyll.${library.id}.All`)}</code></div></div>${routeLink(libraryHref(library.id), "↗", `class="row-arrow" aria-label="Browse ${escape(libraryName(library))}"`)}</article>`;
      }).join("")}</section>`;
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
    setMetadata(libraryName(library) + " · NYLL", plainExcerpt(overview, 160)
      || libraryName(library) + ": Lean source modules, mathematical statements, and documentation.");
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
    setMetadata(name + " · NYLL", plainExcerpt(module.doc || module.summary, 160)
      || name + ": Lean source, declarations, and documentation in " + libraryName(library) + ".");
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
    setMetadata("Search: " + pattern + " · NYLL", "Search NYLL libraries, modules, and Lean declarations.");
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
    tree.innerHTML = `<ul class="tree"><li class="tree-root">${routeLink(href({catalog: true}), "All source code", `${currentParams.has("catalog") ? 'aria-current="page"' : ""}`)}</li>${[...libraries.values()].map((library) => `<li><details data-tree-library="${escape(library.id)}"${library.id === activeLibrary ? " open" : ""}><summary>${escape(libraryName(library))}</summary><ul class="library-tree-mount"></ul></details></li>`).join("")}</ul>`;
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
    const route = normalizeLocation();
    if (!route) return;
    if (route.kind === "home") { location.replace(routeHref(route)); return; }
    window.MathJax?.typesetClear?.([app]);
    currentParams = routeParams(route);
    document.body.dataset.page = route.kind;
    const preserve = keepInitialContent && initialRoute.kind === route.kind && initialRoute.id === route.id;
    search.value = route.kind === "search" ? route.query : "";
    app.setAttribute("aria-busy", "true");
    updateRouteMetadata(route);
    renderTree();
    try {
      if (route.kind === "search") await renderSearch(route.query, version);
      else if (route.kind === "module") await renderModule(route.id, version);
      else if (route.kind === "library") await renderLibrary(route.id, version);
      else if (route.kind === "catalog") renderCatalog();
      if (version !== navigation) return;
      keepInitialContent = false;
      scrollToRouteTarget(route);
      announce.textContent = document.title;
    } catch (error) {
      if (version === navigation) showLoadFailure(error, preserve);
    } finally { if (version === navigation) app.setAttribute("aria-busy", "false"); }
  }

  function navigate(value) {
    if (!manifest) return false;
    const route = readRoute(new URL(value, location.href));
    if (!route || route.kind === "home") return false;
    history.pushState({}, "", routeHref(route));
    keepInitialContent = false;
    closeSuggestions(); ++suggestionVersion;
    setMenu(false);
    window.scrollTo({ top: 0 });
    app.focus({ preventScroll: true });
    void render();
    return true;
  }

  document.addEventListener("click", (event) => {
    const link = event.target.closest("a[data-route]");
    if (link && !event.ctrlKey && !event.metaKey && !event.shiftKey && !event.altKey && event.button === 0
      && (!link.target || link.target === "_self") && !link.hasAttribute("download") && navigate(link.href)) event.preventDefault();
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
  window.addEventListener("popstate", () => { closeSuggestions(); setMenu(false); if (manifest) void render(); });
  window.addEventListener("hashchange", () => {
    const route = readRoute(location.href);
    if (route && route.kind === "module" && route.id === currentParams.get("module")) {
      currentParams = routeParams(route);
      scrollToRouteTarget(route);
    }
  });

  const startingRoute = normalizeLocation();
  if (startingRoute?.kind === "search") updateRouteMetadata(startingRoute);

  fetch(new URL("data/manifest.json", base), { cache: "no-cache" }).then((response) => { if (!response.ok) throw new Error("The source catalog could not be loaded. Please try again shortly."); return response.json(); }).then((data) => {
    manifest = data;
    libraries = new Map((manifest.libraries || []).map((library) => [library.id, library]));
    modules = new Map((manifest.modules || []).map((module) => [module.name, module]));
    if (!libraries.size && !modules.size) throw new Error("The source catalog is empty.");
    search.disabled = false;
    const source = manifest.source || {};
    if (source.repo) document.getElementById("github-link").href = source.repo;
    const date = source.committedAt ? new Date(source.committedAt) : null;
    const dateText = date && !Number.isNaN(date.valueOf()) ? date.toLocaleDateString("en", { year: "numeric", month: "short", day: "numeric", timeZone: "UTC" }) : "";
    const revision = source.commitShort || source.commit?.slice(0, 8);
    document.getElementById("revision").innerHTML = `<p>Source revision ${revision ? `<a href="${escape(`${source.repo}/commit/${source.commit}`)}"><code>${escape(revision)}</code></a>` : "unavailable"}</p>${dateText ? `<p>${escape(dateText)} · updated from Git</p>` : ""}<p><a href="${escape(`${source.repo}/actions/workflows/libraries.yml`)}">Lean checks ↗</a></p>`;
    void render();
  }).catch((error) => {
    manifest = undefined;
    search.disabled = true;
    app.setAttribute("aria-busy", "false");
    showLoadFailure(error, keepInitialContent);
    if (!keepInitialContent) tree.innerHTML = '<p class="muted">Source catalog unavailable.</p>';
  });
})();
