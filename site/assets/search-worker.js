/* Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
 * Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
 * https://github.com/n-yamaguchi-0729
 */
"use strict";
let base;
let searchUrl;
let entries = [];
let dataPromise;

async function loadData() {
  const url = new URL(searchUrl || "data/search.json", base);
  if (!dataPromise) dataPromise = fetch(url).then((response) => {
    if (!response.ok) throw new Error(response.status === 404 ? "This search snapshot is no longer available. Reload the page to search the latest revision." : "The search index could not be loaded. Please reload the page.");
    return response.json();
  }).then((data) => {
    for (const entry of (Array.isArray(data) ? data : data.entries || [])) entries.push({ ...entry, type: entry.type || "declaration" });
    // Keep the large index and its search work away from the UI thread.
    for (const entry of entries) {
      entry.normalName = String(entry.fullName || entry.name || "").toLowerCase();
      entry.normalShort = entry.normalName.split(".").at(-1);
      entry.haystack = `${entry.normalName} ${entry.module || ""} ${entry.library || ""} ${entry.kind || ""} ${entry.doc || ""}`.toLowerCase();
    }
  }).catch((error) => { dataPromise = null; throw error; });
  return dataPromise;
}

function find(pattern, limit, kind) {
  const needle = pattern.trim().toLowerCase();
  const terms = needle.split(/\s+/).filter(Boolean);
  if (!terms.length) return { total: 0, results: [] };
  const matches = [];
  for (let index = 0; index < entries.length; index++) {
    const entry = entries[index];
    if (kind !== "all" && entry.type !== kind) continue;
    if (!terms.every((term) => entry.haystack.includes(term))) continue;
    let score = entry.type === "library" ? 4 : entry.type === "module" ? 2 : 0;
    if (entry.normalShort === needle) score += 160;
    else if (entry.normalName === needle) score += 150;
    else if (entry.normalShort.startsWith(needle)) score += 100;
    else if (entry.normalName.includes(needle)) score += 70;
    else if (entry.haystack.includes(needle)) score += 10;
    matches.push({ index, score });
  }
  matches.sort((left, right) => right.score - left.score || entries[left.index].normalName.localeCompare(entries[right.index].normalName));
  return { total: matches.length, results: matches.slice(0, limit).map(({ index }) => {
    const { normalName, normalShort, haystack, ...entry } = entries[index];
    return entry;
  }) };
}

self.onmessage = async ({ data }) => {
  if (data.type === "init") { base = data.base; searchUrl = data.searchUrl; entries = [...data.libraries, ...data.modules]; return; }
  if (data.type !== "search") return;
  try { await loadData(); self.postMessage({ id: data.id, ...find(data.pattern || "", Math.max(1, Math.min(Number(data.limit) || 12, 10000)), data.kind || "all") }); }
  catch (error) { self.postMessage({ id: data.id, error: error.message }); }
};
