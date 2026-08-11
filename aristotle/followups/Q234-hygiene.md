# Q234 hygiene retry

Reconstruct only the exact requested targets in the reviewed interface context.
Do not introduce any `axiom`, `sorry`, `admit`, `unsafe`, `Classical`, import,
local copy of a dependency, or helper declaration.  Dependencies are opaque
interfaces only; use exactly the prompt whitelist.  If the target cannot be
proved under that interface, report the exact missing interface rather than
adding an axiom or changing the target.
