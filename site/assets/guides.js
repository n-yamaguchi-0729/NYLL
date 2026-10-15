/* Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
 * Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
 * https://github.com/n-yamaguchi-0729
 */
(() => {
  "use strict";
  window.MathJax = {
    loader: { load: ["ui/safe"] },
    tex: {
      inlineMath: [["$", "$"], ["\\(", "\\)"]],
      displayMath: [["$$", "$$"], ["\\[", "\\]"]],
      processEscapes: true,
    },
    options: {
      skipHtmlTags: ["script", "noscript", "style", "textarea", "pre", "code"],
      safeOptions: {
        allow: { URLs: "safe", classes: "none", cssIDs: "none", styles: "none" },
        safeProtocols: { http: true, https: true, file: false, javascript: false, data: false },
      },
    },
  };
  const script = document.createElement("script");
  script.src = "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml.js";
  script.async = true;
  script.onerror = () => {
    const notice = document.createElement("p");
    notice.className = "math-notice";
    notice.textContent = "The equation renderer could not load. Mathematical notation is shown as TeX.";
    document.querySelector(".guide-hero").append(notice);
  };
  document.head.append(script);
})();
