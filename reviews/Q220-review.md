# Audit Q220 — PM I, ✱2·82–✱2·86 selected sequence

Verdict: **A FOR TARGET AND GENERATED CONTEXT — pending remote kernel CI**.
Source: first edition, vol. I,
p. 113, leaf 135; SHA-256
`0015ae56c8a9c1eedab541d07e06d683c499319b60fa021d088077535f93f2f0`.

The ASTs preserve PM's left-associated `p∨q∨r`. ✱2·82 and ✱2·83 retain the
printed simultaneous substitutions; ✱2·85 retains its numbered intermediate
lines and final use of ✱2·54; ✱2·86 is its displayed `∼p/p` instance. The
split word `Com`/`m.` in ✱2·85 is ordinary line breaking, not a misprint.
Confidence high.

The deterministic proof parser resolves independent per-target whitelists:
✱2·82={✱2·8, ✱2·81}; ✱2·83={earlier local ✱2·82};
✱2·85={Add, Syll, ✱2·55, earlier local ✱2·83, Comm, ✱2·54}; and
✱2·86={earlier local ✱2·85}, plus reviewed ✱1·11 where licensed. The generated
20.3 kB context contains only the external transitive implementation closure;
local targets occur only in order inside the request. Context CI is pending.

GitHub CI kernel-checked the generated standalone context and the full edition
at commit `67663311e24ddd1ca3bdb267d36436ae674ca3bf`, run
[`31446802971`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31446802971),
conclusion `success`. The single constrained request is eligible.
