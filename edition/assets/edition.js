document.querySelectorAll(".scope-toggle").forEach((button) => {
  button.addEventListener("click", () => {
    const formula = document.querySelector("[data-pm-formula]");
    const active = button.getAttribute("aria-pressed") !== "true";
    button.setAttribute("aria-pressed", String(active));
    button.textContent = active ? "Hide printed scope marks" : "Show printed scope marks";
    button.setAttribute("aria-label", active
      ? "Hide highlighted dots and colons in the printed formula"
      : "Highlight dots and colons in the printed formula");
    formula?.classList.toggle("scope-active", active);
  });
});
