# Q238 hygiene retry

Use only the reviewed opaque interface and exact whitelist.  No `Classical`
outside Main, and no `axiom`, `sorry`, `admit`, `unsafe`, import, helper,
local module, or dependency reconstruction.  If the exact target is blocked,
report its missing interface rather than altering it.
