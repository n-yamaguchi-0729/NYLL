/* Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
 * Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
 * https://github.com/n-yamaguchi-0729
 */
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const test = require("node:test");
const source = fs.readFileSync(path.join(__dirname, "../../site/assets/site.js"), "utf8");
// Exercise the actual URL/metadata helpers. Full UI behavior is checked in a browser.
const helpers = source.slice(source.indexOf("  const homeTitle ="), source.indexOf("  function updateRouteMetadata("));

function setup(url = "https://preview.test/NYLL/") {
  const location = new URL(url);
  const children = [];
  const document = {
    body: { dataset: { staticPage: "home", siteRoot: "https://n-yamaguchi-0729.github.io/NYLL/" } },
    head: { appendChild(element) { children.push(element); } },
    createElement(tag) { return { tag, attrs: {}, setAttribute(name, value) { this.attrs[name] = value; } }; },
    querySelector(selector) {
      if (selector === ".search-form") return {};
      const match = selector.match(/^(meta|link)\[(name|property|rel)="([^"]+)"\]$/);
      return match ? children.find((node) => node.tag === match[1] && node.attrs[match[2]] === match[3]) || null : null;
    }
  };
  const history = { state: {}, replaceState(_, __, value) { location.href = new URL(value, location).href; } };
  const context = { base: new URL("https://preview.test/NYLL/"), location, history, document,
    app: { children: [] }, sidebar: {}, URL, URLSearchParams, escape: String };
  vm.runInNewContext("(() => {" + helpers + "\nglobalThis.api = { readRoute, routeHref, href, moduleHref, libraryHref, normalizeLocation, setMetadata };})()", context);
  return { ...context, meta: (name) => document.querySelector('meta[name="' + name + '"]')?.attrs.content,
    canonical: () => document.querySelector('link[rel="canonical"]')?.href };
}

test("paths and declaration fragments use strict RFC3986 encoding", () => {
  const { api } = setup();
  assert.equal(api.moduleHref("Nyll.奇妙!x'()*", "d!'()*"), "/NYLL/modules/Nyll.%E5%A5%87%E5%A6%99%21x%27%28%29%2A/#declaration-d%21%27%28%29%2A");
  assert.equal(api.libraryHref("A'B"), "/NYLL/browse/A%27B/");
  const route = api.readRoute("https://preview.test" + api.moduleHref("Nyll.奇妙!x'()*", "d!'()*"));
  assert.equal(route.id, "Nyll.奇妙!x'()*");
  assert.equal(route.declaration, "d!'()*");
});

test("legacy module queries retain declaration targets after normalization", () => {
  const env = setup("https://preview.test/NYLL/?module=Nyll.Example.Basic&decl=a%27b");
  env.api.normalizeLocation();
  assert.equal(env.location.href, "https://preview.test/NYLL/modules/Nyll.Example.Basic/#declaration-a%27b");
  assert.equal(env.api.readRoute(env.location.href).declaration, "a'b");
});

test("legacy library and index paths use trailing-slash canonical routes", () => {
  const env = setup("https://preview.test/NYLL/?library=Example");
  env.api.normalizeLocation();
  assert.equal(env.location.pathname, "/NYLL/browse/Example/");
  for (const suffix of ["", "/", "/index.html"]) {
    const route = env.api.readRoute("https://preview.test/NYLL/modules/Nyll.Example.Basic" + suffix);
    assert.equal(env.api.routeHref(route), "/NYLL/modules/Nyll.Example.Basic/");
  }
});

test("foreign, guide, malformed, and out-of-base URLs are not SPA routes", () => {
  const { api } = setup();
  for (const url of ["https://foreign.test/NYLL/?module=X", "https://preview.test/NYLL/libraries/class-field-theory/",
    "https://preview.test/NYLL-elsewhere/?module=X", "https://preview.test/NYLL/modules/%ZZ/",
    "https://preview.test/NYLL/modules/X/extra/"]) assert.equal(api.readRoute(url), null, url);
});

test("the full source catalog has its own canonical route", () => {
  const env = setup();
  for (const suffix of ["browse", "browse/", "browse/index.html"]) {
    const route = env.api.readRoute("https://preview.test/NYLL/" + suffix);
    assert.equal(route.kind, "catalog");
    assert.equal(env.api.routeHref(route), "/NYLL/browse/");
  }
  assert.equal(env.api.href({catalog: true}), "/NYLL/browse/");
  env.location.href = "https://preview.test/NYLL/browse/";
  env.api.setMetadata("All source code · NYLL", "All source libraries.");
  assert.equal(env.canonical(), "https://n-yamaguchi-0729.github.io/NYLL/browse/");
  assert.equal(env.meta("robots"), "index,follow");
});

test("empty searches and filters survive normalization, including legacy query precedence", () => {
  const env = setup("https://preview.test/NYLL/?module=X&q=&type=declaration");
  env.api.normalizeLocation();
  assert.equal(env.location.href, "https://preview.test/NYLL/browse/?q=&type=declaration");
  assert.equal(env.api.href({ q: "", type: "module" }), "/NYLL/browse/?q=&type=module");
});

test("module metadata uses production canonical URL and strips declaration fragments", () => {
  const env = setup("https://preview.test/NYLL/modules/Nyll.Example.Basic/#declaration-target");
  env.api.setMetadata("Nyll.Example.Basic · NYLL", "Finite groups.");
  assert.equal(env.document.title, "Nyll.Example.Basic · NYLL");
  assert.equal(env.canonical(), "https://n-yamaguchi-0729.github.io/NYLL/modules/Nyll.Example.Basic/");
  assert.equal(env.meta("description"), "Finite groups.");
  assert.equal(env.meta("robots"), "index,follow");
});

test("home and library metadata clear search noindex and stale canonical URLs", () => {
  const env = setup("https://preview.test/NYLL/?q=group&type=module");
  env.api.setMetadata("Search: group · NYLL", "Search.");
  assert.equal(env.meta("robots"), "noindex,follow");
  assert.equal(env.canonical(), "https://n-yamaguchi-0729.github.io/NYLL/browse/?q=group&type=module");
  env.location.href = "https://preview.test/NYLL/";
  env.api.setMetadata("Home", "Home description.");
  assert.equal(env.meta("robots"), "index,follow");
  assert.equal(env.canonical(), "https://n-yamaguchi-0729.github.io/NYLL/");
  env.location.href = "https://preview.test/NYLL/browse/Example/";
  env.api.setMetadata("Example · NYLL", "Example description.");
  assert.equal(env.canonical(), "https://n-yamaguchi-0729.github.io/NYLL/browse/Example/");
  assert.equal(env.meta("robots"), "index,follow");
});

test("reading a restored module URL retains its declaration after history navigation", () => {
  const env = setup();
  env.location.href = "https://preview.test/NYLL/modules/Nyll.Example.Basic/#declaration-a%27b";
  const restored = env.api.normalizeLocation();
  assert.equal(restored.kind, "module");
  assert.equal(restored.id, "Nyll.Example.Basic");
  assert.equal(restored.declaration, "a'b");
});

test("landing page neither loads source data nor rewrites the guide catalog", () => {
  function landing(url) {
    let replaced = null;
    const location = new URL(url);
    location.replace = value => { replaced = value; };
    const app = { children: [{}] };
    const document = {
      currentScript: { src: "https://preview.test/NYLL/assets/site.js?v=current" },
      body: { dataset: { staticPage: "home", siteRoot: "https://preview.test/NYLL/" } },
      querySelector: selector => selector === ".brand" ? {} : null,
      getElementById: id => id === "main" ? app : null,
    };
    vm.runInNewContext(source, { document, location, URL, URLSearchParams });
    assert.deepEqual(app, { children: [{}] });
    return replaced;
  }
  assert.equal(landing("https://preview.test/NYLL/"), null);
  assert.equal(landing("https://preview.test/NYLL/?module=Nyll.Example.Basic&decl=x"), "/NYLL/modules/Nyll.Example.Basic/#declaration-x");
  assert.equal(landing("https://preview.test/NYLL/?q=group"), "/NYLL/browse/?q=group");
});
